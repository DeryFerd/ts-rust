//! Declared object-member construction for the canonical checker.
//!
//! This module owns the exact syntax-to-member-table boundary.  It deliberately
//! does not recurse through property annotations: [`super::type_nodes`] plans
//! and executes property, index, and signature annotations so one query
//! retains a single dependency graph and resolution stack. Call and construct
//! signatures retain authenticated generic parameters, overload order, and
//! supported rest parameters. Interfaces may also contain authenticated
//! properties, methods, and index signatures. Callable type literals may retain
//! ordinary properties, optional `any` parameters, implicit `any` returns, and
//! trailing implicit `any[]` rest parameters. Interface constructors may retain
//! implicit `any` returns, and construct signatures support trailing optional
//! `any` parameters.
//! Named interface and type-literal methods retain their own binder symbols,
//! authenticated method type parameters, annotated required or optional
//! parameters, and authenticated array, tuple, tuple-union, or inferred rest
//! parameters. Selected default-library `Math` methods also retain their
//! numeric rest parameters.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeData, NodeFlags, NodeList, NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolData, SymbolFlags,
    SymbolTableId, semantic::PreparedSymbolTable,
};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost, SignatureId, TypeId,
    array_types::CanonicalArrayTargets,
    bootstrap::UnionReduction,
    declared::{
        cached_ordinary_type_parameter_owner, preflight_node, preflight_type_parameter_symbol,
        type_list_key,
    },
    global_types::preflight_generic_global_type_target,
    instantiate::{InstantiationLimits, InstantiationSession},
    instantiated_members::{
        demand_instantiated_property_type, resolve_members_with_array_targets,
        validate_generic_interface_members,
    },
    interface_heritage::{
        DirectInterfaceBaseKind, DirectInterfaceHeritageError, DirectInterfaceHeritagePlan,
        plan_direct_interface_heritage,
    },
    links::{
        AliasTargetState, ResolvedSignatureState, SignatureLinks, TypeNodeLinks, ValueSymbolLinks,
    },
    reference_types::{
        validate_direct_generic_reference, validate_nongeneric_interface_argument_origin,
    },
    signatures::SignatureFlags,
    source_callables::implicit_any_array_type,
    source_namespaces::authenticated_merged_namespace_interface,
    store::SourceNodeParent,
    type_records::{
        ConstrainedTypeData, InterfaceTypeData, ObjectTypeData, StructuredTypeData, TypeCacheState,
        TypeData, TypeRecord,
    },
    types::{ObjectFlags, TypeFlags},
};

const NODE_FLAG_JSDOC: u32 = 1 << 22;
const NODE_FLAG_HAS_ERROR: u32 = 1 << 15;
const MAX_INTERFACE_PROPERTY_HERITAGE_DEPTH: usize = 16;

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

/// One unbound object spread and its position among source-owned properties.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlannedObjectSpread {
    pub declaration: NodeRef,
    pub expression: NodeRef,
    pub property_index: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ResolvedObjectProperty {
    name: String,
    type_: TypeId,
    readonly: bool,
    optional: bool,
}

/// One binder-owned shorthand assignment with an explicit default expression.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlannedObjectAssignmentShorthand {
    pub object: NodeRef,
    pub owner: SemanticSymbolId,
    pub declaration: NodeRef,
    pub symbol: SemanticSymbolId,
    pub name: NodeRef,
    pub initializer: NodeRef,
}

const fn source_property_check_flags(readonly: bool) -> CheckFlags {
    if readonly {
        CheckFlags::READONLY
    } else {
        CheckFlags::NONE
    }
}

fn valid_declared_property_check_flags(
    store: &CanonicalTypeMapperStore,
    property: &PlannedProperty,
) -> bool {
    store.symbol(property.symbol).is_some_and(|record| {
        if record.flags().intersects(SymbolFlags::ACCESSOR) {
            record.check_flags() == CheckFlags::NONE
        } else {
            record.check_flags() == source_property_check_flags(property.readonly)
        }
    })
}

fn expected_declared_property_links(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    property: &PlannedProperty,
    read_type: TypeId,
) -> Option<ValueSymbolLinks> {
    let write_type = match plan.accessor_write_type_node(property.symbol) {
        Some(annotation) => {
            let write_type = cached_planned_type_identity(store, annotation)?;
            (write_type != read_type).then_some(write_type)
        }
        None => None,
    };
    Some(ValueSymbolLinks {
        resolved_type: Some(read_type),
        write_type,
        ..ValueSymbolLinks::default()
    })
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
    value_type_parameter: Option<SemanticSymbolId>,
}

/// One annotated identifier parameter in an admitted declared signature.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlannedCallParameter {
    pub symbol: SemanticSymbolId,
    pub type_node: NodeRef,
    identity_node: NodeRef,
    null_literal_identity: bool,
    optional: bool,
    pub(super) implicit_any_rest: bool,
}

/// One binder-owned type parameter declared directly on a source signature.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PlannedInterfaceMethodTypeParameter {
    pub declaration: NodeRef,
    pub symbol: SemanticSymbolId,
    pub constraint: Option<NodeRef>,
    pub default_type: Option<NodeRef>,
}

/// One named method on an interface or type literal.
///
/// Overloads share the binder-owned method symbol but keep separate signature
/// declarations, type parameters, and value parameter lists.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PlannedInterfaceMethod {
    pub declaration: NodeRef,
    pub symbol: SemanticSymbolId,
    pub type_parameters: Vec<PlannedInterfaceMethodTypeParameter>,
    pub parameters: Vec<PlannedCallParameter>,
    pub return_type: NodeRef,
    pub flags: SignatureFlags,
    minimum_argument_count: usize,
}

/// One binder-owned getter or setter contributing to an interface property.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PlannedInterfaceAccessor {
    pub declaration: NodeRef,
    pub symbol: SemanticSymbolId,
    pub name_node: NodeRef,
    pub type_node: NodeRef,
    pub parameter: Option<PlannedCallParameter>,
}

/// One authenticated call or construct signature in source order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PlannedCallSignature {
    pub declaration: NodeRef,
    pub symbol: SemanticSymbolId,
    pub type_parameters: Vec<PlannedInterfaceMethodTypeParameter>,
    pub parameters: Vec<PlannedCallParameter>,
    pub return_type: NodeRef,
    return_identity_node: NodeRef,
    return_null_literal_identity: bool,
    flags: SignatureFlags,
    pub(super) implicit_any_return: bool,
}

impl PlannedCallSignature {
    const fn is_construct(&self) -> bool {
        self.flags.contains(SignatureFlags::CONSTRUCT)
    }

    const fn syntax_kind(&self) -> SyntaxKind {
        if self.is_construct() {
            SyntaxKind::ConstructSignature
        } else {
            SyntaxKind::CallSignature
        }
    }

    const fn internal_name(&self) -> InternalSymbolName {
        if self.is_construct() {
            InternalSymbolName::New
        } else {
            InternalSymbolName::Call
        }
    }

    pub(super) fn min_argument_count(&self) -> usize {
        let fixed = self.parameters.len().saturating_sub(usize::from(
            self.flags.contains(SignatureFlags::HAS_REST_PARAMETER),
        ));
        self.parameters
            .iter()
            .take(fixed)
            .position(|parameter| parameter.optional || parameter.implicit_any_rest)
            .unwrap_or(fixed)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ResolvedCallSignatureTypes {
    pub parameter_types: Vec<TypeId>,
    pub return_type: TypeId,
}

/// One source-only call-signature contribution to the initialized global Array.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct GlobalArrayCallAugmentationPlan {
    pub declaration: NodeRef,
    pub symbol: SemanticSymbolId,
    pub target: TypeId,
    pub signature: NodeRef,
    pub return_type: NodeRef,
    pub any_array_type: TypeId,
}

/// One source-owned property added to the initialized global `Array<T>`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct GlobalArrayPropertyAugmentationPlan {
    pub declaration: NodeRef,
    pub symbol: SemanticSymbolId,
    pub target: TypeId,
    pub property: PlannedProperty,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum GlobalArrayConcatOverloadKind {
    Arrays,
    ValuesOrArrays,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct GlobalArrayConcatOverloadPlan {
    declaration: NodeRef,
    parameter: SemanticSymbolId,
    parameter_annotation: NodeRef,
    return_annotation: NodeRef,
    kind: GlobalArrayConcatOverloadKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct GlobalArrayConcatPlan {
    owner: SemanticSymbolId,
    method: SemanticSymbolId,
    concat_array: SemanticSymbolId,
    target: TypeId,
    type_parameter: TypeId,
    overloads: Vec<GlobalArrayConcatOverloadPlan>,
}

/// Authenticated identity for a reopened namespace-owned generic interface.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct LazyMergedGenericInterfacePlan {
    pub symbol: SemanticSymbolId,
    pub namespace: SemanticSymbolId,
    pub type_parameter: SemanticSymbolId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PropertyObjectPlan {
    pub kind: PropertyObjectKind,
    pub node: NodeRef,
    pub const_context: bool,
    pub declarations: Vec<NodeRef>,
    pub symbol: SemanticSymbolId,
    pub members: Option<SymbolTableId>,
    pub properties: Vec<PlannedProperty>,
    pub methods: Vec<PlannedInterfaceMethod>,
    pub accessors: Vec<PlannedInterfaceAccessor>,
    pub spreads: Vec<PlannedObjectSpread>,
    pub indexes: Vec<PlannedIndexSignature>,
    pub call_signatures: Vec<PlannedCallSignature>,
    pub alias_symbol: Option<SemanticSymbolId>,
    pub heritage: Option<DirectInterfaceHeritagePlan>,
}

impl PropertyObjectPlan {
    pub(super) fn property_type_nodes(&self) -> impl Iterator<Item = NodeRef> + '_ {
        self.properties
            .iter()
            .filter(|property| {
                self.kind != PropertyObjectKind::Interface
                    || property.type_node != property.name_node
            })
            .map(|property| property.type_node)
    }

    pub(super) fn spread_expression_nodes(&self) -> impl ExactSizeIterator<Item = NodeRef> + '_ {
        self.spreads.iter().map(|spread| spread.expression)
    }

    pub(super) fn accessor_write_type_node(&self, symbol: SemanticSymbolId) -> Option<NodeRef> {
        self.accessors
            .iter()
            .find(|accessor| accessor.symbol == symbol && accessor.parameter.is_some())
            .map(|accessor| accessor.type_node)
    }

    pub(super) fn index_type_nodes(
        &self,
    ) -> impl ExactSizeIterator<Item = (NodeRef, NodeRef)> + '_ {
        self.indexes
            .iter()
            .map(|index| (index.key_type_node, index.value_type_node))
    }

    pub(super) fn call_type_nodes(&self) -> impl Iterator<Item = NodeRef> + '_ {
        self.call_signatures
            .iter()
            .flat_map(|signature| {
                signature
                    .type_parameters
                    .iter()
                    .flat_map(|parameter| [parameter.constraint, parameter.default_type])
                    .flatten()
                    .chain(
                        signature
                            .parameters
                            .iter()
                            .filter(|parameter| !parameter.implicit_any_rest)
                            .map(|parameter| parameter.type_node),
                    )
                    .chain((!signature.implicit_any_return).then_some(signature.return_type))
            })
            .chain(self.methods.iter().flat_map(|method| {
                method
                    .type_parameters
                    .iter()
                    .flat_map(|parameter| [parameter.constraint, parameter.default_type])
                    .flatten()
                    .chain(
                        method
                            .parameters
                            .iter()
                            .map(|parameter| parameter.type_node),
                    )
                    .chain(std::iter::once(method.return_type))
            }))
            .chain(self.accessors.iter().map(|accessor| accessor.type_node))
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
    let (owner_declaration, structured, members, exact_owner, inherited_base, own_signature_count) =
        match record.data() {
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
                    && record.object_flags()
                        == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
                    && owner_record.flags() == SymbolFlags::TYPE_LITERAL
                    && owner_record.check_flags() == CheckFlags::NONE
                    && owner_record.name() == InternalSymbolName::Type.as_ref()
                    && owner_record.value_declaration().is_none()
                    && owner_record.exports().is_none()
                    && owner_record.parent().is_none()
                    && owner_record.export_symbol().is_none()
                    && store.get_merged_symbol(owner) == Some(owner)
                    && matches!(
                        store.source_node_kind(*declaration),
                        Some(SyntaxKind::TypeLiteral | SyntaxKind::ConstructorType)
                    )
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
                    None,
                    object.structured.signatures.as_ref().map_or(0, Vec::len),
                )
            }
            TypeData::Interface(interface) => {
                let Some([declaration]) = owner_record.declarations() else {
                    return StoredDeclaredCallSetValidation::Malformed;
                };
                let inherited_base = match interface.resolved_base_types.as_deref() {
                    None => None,
                    Some([base]) if *base != type_ => Some(*base),
                    _ => return StoredDeclaredCallSetValidation::Malformed,
                };
                let declared_calls = interface.declared_call_signatures.as_deref();
                let declared_constructs = interface.declared_construct_signatures.as_deref();
                let own_signature_count = declared_calls.map_or(0, <[SignatureId]>::len)
                    + declared_constructs.map_or(0, <[SignatureId]>::len);
                let inherited_base_valid = inherited_base.is_none_or(|base| {
                    let Some(base_record) = store.type_payload(base) else {
                        return false;
                    };
                    let Some(base_owner) = base_record.symbol() else {
                        return false;
                    };
                    let Some(provenance) = store.direct_interface_heritage_provenance(type_) else {
                        return false;
                    };
                    let TypeData::Interface(base_interface) = base_record.data() else {
                        return false;
                    };
                    let Some(base_signatures) = base_interface
                        .reference
                        .object
                        .structured
                        .signatures
                        .as_deref()
                    else {
                        return false;
                    };
                    let Some(signatures) =
                        interface.reference.object.structured.signatures.as_deref()
                    else {
                        return false;
                    };
                    provenance.owner_symbol == owner
                        && provenance.base_symbol == base_owner
                        && provenance.base_type == base
                        && provenance.second_base.is_none()
                        && base_interface.resolved_base_types.is_none()
                        && declared_constructs.is_none()
                        && declared_calls.is_some_and(|calls| {
                            !calls.is_empty()
                                && signatures.len() == calls.len() + base_signatures.len()
                                && signatures.starts_with(calls)
                                && signatures[calls.len()..] == *base_signatures
                        })
                        && matches!(
                            validate_stored_declared_call_set(store, base),
                            StoredDeclaredCallSetValidation::Valid(_)
                        )
                });
                let exact = record.flags() == TypeFlags::OBJECT
                    && record.object_flags()
                        == ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
                    && record.alias().is_none()
                    && owner_record.flags() == SymbolFlags::INTERFACE
                    && owner_record.check_flags() == CheckFlags::NONE
                    && owner_record.name().as_utf8().is_some()
                    && owner_record.value_declaration().is_none()
                    && owner_record.members() == interface.declared_members
                    && owner_record.exports().is_none()
                    && owner_record.export_symbol().is_none()
                    && store.get_merged_symbol(owner) == Some(owner)
                    && store.source_node_kind(*declaration)
                        == Some(SyntaxKind::InterfaceDeclaration)
                    && store
                        .declared_type_links(owner)
                        .is_some_and(|links| links.declared_type == Some(type_))
                    && valid_thisless_interface_identity(interface)
                    && interface.base_types_resolved
                    && interface.resolved_base_constructor_type.is_none()
                    && inherited_base_valid
                    && interface.declared_members_resolved
                    && interface.declared_index_infos.as_deref()
                        == interface.reference.object.structured.index_infos.as_deref()
                    && match (declared_calls, declared_constructs) {
                        (Some(calls), None) => {
                            let signatures = interface
                                .reference
                                .object
                                .structured
                                .signatures
                                .as_deref()
                                .unwrap_or_default();
                            signatures.starts_with(calls)
                                && interface.reference.object.structured.call_signature_count
                                    == signatures.len()
                                && (inherited_base.is_some() || signatures == calls)
                        }
                        (None, Some(constructs)) => {
                            inherited_base.is_none()
                                && constructs
                                    == interface
                                        .reference
                                        .object
                                        .structured
                                        .signatures
                                        .as_deref()
                                        .unwrap_or_default()
                                && interface.reference.object.structured.call_signature_count == 0
                        }
                        (Some(calls), Some(constructs)) => {
                            let signatures = interface
                                .reference
                                .object
                                .structured
                                .signatures
                                .as_deref()
                                .unwrap_or_default();
                            inherited_base.is_none()
                                && !calls.is_empty()
                                && !constructs.is_empty()
                                && signatures.len() == calls.len() + constructs.len()
                                && signatures.starts_with(calls)
                                && signatures[calls.len()..] == *constructs
                                && interface.reference.object.structured.call_signature_count
                                    == calls.len()
                        }
                        _ => false,
                    };
                (
                    *declaration,
                    &interface.reference.object.structured,
                    owner_record.members(),
                    exact,
                    inherited_base,
                    own_signature_count,
                )
            }
            _ => return StoredDeclaredCallSetValidation::Malformed,
        };
    let Some(signatures) = structured.signatures.as_deref() else {
        return StoredDeclaredCallSetValidation::Malformed;
    };
    let call_signature_count = structured.call_signature_count;
    if !exact_owner
        || signatures.is_empty()
        || call_signature_count > signatures.len()
        || structured.constrained != ConstrainedTypeData::default()
        || inherited_base.is_none() && structured.members != members
        || inherited_base.is_some() && structured.members == members
        || inherited_base.is_some()
            && (structured.properties.is_some() || structured.index_infos.is_some())
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return StoredDeclaredCallSetValidation::Malformed;
    }
    let Some(members) = members.and_then(|members| store.symbol_table(members)) else {
        return StoredDeclaredCallSetValidation::Malformed;
    };
    let own_call_signature_count = if inherited_base.is_some() {
        own_signature_count
    } else {
        call_signature_count
    };
    let properties = structured.properties.as_deref().unwrap_or_default();
    if own_call_signature_count > call_signature_count
        || own_signature_count > signatures.len()
        || structured.properties.as_ref().is_some_and(Vec::is_empty)
        || !properties.is_empty()
            && (inherited_base.is_some()
                || match store.source_node_kind(owner_declaration) {
                    Some(SyntaxKind::InterfaceDeclaration) => false,
                    Some(SyntaxKind::TypeLiteral) => call_signature_count != signatures.len(),
                    _ => true,
                })
    {
        return StoredDeclaredCallSetValidation::Malformed;
    }
    let own_calls = &signatures[..own_call_signature_count];
    let own_constructs = &signatures[call_signature_count..];
    if own_signature_count != own_calls.len() + own_constructs.len() {
        return StoredDeclaredCallSetValidation::Malformed;
    }
    let family_count = usize::from(!own_calls.is_empty()) + usize::from(!own_constructs.is_empty());
    let Some(member_edges) = validate_declared_call_set_member_edges(
        store,
        type_,
        owner,
        owner_declaration,
        structured,
        family_count,
    ) else {
        return StoredDeclaredCallSetValidation::Malformed;
    };
    for (name, family_signatures) in [
        (InternalSymbolName::Call, own_calls),
        (InternalSymbolName::New, own_constructs),
    ] {
        let symbol = members.get(name.as_ref());
        if family_signatures.is_empty() {
            if symbol.is_some() {
                return StoredDeclaredCallSetValidation::Malformed;
            }
            continue;
        }
        let Some(symbol) = symbol else {
            return StoredDeclaredCallSetValidation::Malformed;
        };
        let Some(symbol_record) = store.symbol(symbol) else {
            return StoredDeclaredCallSetValidation::Malformed;
        };
        let declarations = family_signatures
            .iter()
            .filter_map(|signature| store.signature(*signature)?.declaration())
            .collect::<Vec<_>>();
        if declarations.len() != family_signatures.len()
            || symbol_record.flags() != SymbolFlags::SIGNATURE
            || symbol_record.check_flags() != CheckFlags::NONE
            || symbol_record.name() != name.as_ref()
            || symbol_record.declarations() != Some(declarations.as_slice())
            || symbol_record.value_declaration().is_some()
            || symbol_record.members().is_some()
            || symbol_record.exports().is_some()
            || if store.source_node_kind(owner_declaration) == Some(SyntaxKind::ConstructorType) {
                symbol_record.parent().is_some()
            } else {
                symbol_record.parent() != Some(owner)
            }
            || symbol_record.export_symbol().is_some()
            || store.get_merged_symbol(symbol) != Some(symbol)
        {
            return StoredDeclaredCallSetValidation::Malformed;
        }
        if inherited_base.is_some()
            && structured
                .members
                .and_then(|members| store.symbol_table(members))
                .is_none_or(|members| {
                    members.len() != 1 || members.get(name.as_ref()) != Some(symbol)
                })
        {
            return StoredDeclaredCallSetValidation::Malformed;
        }
    }

    let mut edges = Vec::new();
    let mut seen_signatures = HashSet::with_capacity(signatures.len());
    for (index, signature) in signatures.iter().copied().enumerate() {
        let Some(signature_record) = store.signature(signature) else {
            return StoredDeclaredCallSetValidation::Malformed;
        };
        let Some(declaration) = signature_record.declaration() else {
            return StoredDeclaredCallSetValidation::Malformed;
        };
        let construct = index >= call_signature_count;
        let Some(parameter_types) = store.callable_signature_parameter_types(signature) else {
            return StoredDeclaredCallSetValidation::Malformed;
        };
        let Some(return_type) = signature_record.resolved_return_type() else {
            return StoredDeclaredCallSetValidation::Malformed;
        };
        let return_annotation = store.function_signature_return_annotation(signature);
        let Ok(minimum) = usize::try_from(signature_record.min_argument_count()) else {
            return StoredDeclaredCallSetValidation::Malformed;
        };
        let has_rest = signature_record
            .flags()
            .contains(SignatureFlags::HAS_REST_PARAMETER);
        let Some(fixed_parameter_count) = signature_record
            .parameters()
            .len()
            .checked_sub(usize::from(has_rest))
        else {
            return StoredDeclaredCallSetValidation::Malformed;
        };
        let provider = if index < own_signature_count {
            type_
        } else {
            let Some(base) = inherited_base else {
                return StoredDeclaredCallSetValidation::Malformed;
            };
            base
        };
        let provider_declaration = if provider == type_ {
            owner_declaration
        } else {
            let Some([declaration]) = store
                .type_payload(provider)
                .and_then(TypeRecord::symbol)
                .and_then(|owner| store.symbol(owner))
                .and_then(ts_binder::semantic::Symbol::declarations)
            else {
                return StoredDeclaredCallSetValidation::Malformed;
            };
            *declaration
        };
        if !seen_signatures.insert(signature)
            || store.declared_call_set_type_for_signature(signature) != Some(provider)
            || if construct
                && store.source_node_kind(provider_declaration) == Some(SyntaxKind::ConstructorType)
            {
                declaration != provider_declaration
                    || store.source_node_kind(declaration) != Some(SyntaxKind::ConstructorType)
            } else {
                store.source_node_kind(declaration)
                    != Some(if construct {
                        SyntaxKind::ConstructSignature
                    } else {
                        SyntaxKind::CallSignature
                    })
                    || store.source_node_parent(declaration)
                        != Some(SourceNodeParent::Parent(provider_declaration))
            }
            || store.signature_links(declaration)
                != Some(&SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                })
            || signature_record.flags().contains(SignatureFlags::CONSTRUCT) != construct
            || signature_record.flags().bits()
                & !(SignatureFlags::HAS_LITERAL_TYPES
                    | SignatureFlags::HAS_REST_PARAMETER
                    | SignatureFlags::CONSTRUCT)
                    .bits()
                != 0
            || signature_record.resolved_min_argument_count() != -1
            || minimum > fixed_parameter_count
            || !construct
                && minimum != fixed_parameter_count
                && store.source_node_kind(provider_declaration) != Some(SyntaxKind::TypeLiteral)
            || !super::callable_sets::valid_declared_method_type_parameters(
                store,
                signature_record,
                declaration,
            )
            || signature_record.this_parameter().is_some()
            || signature_record.resolved_type_predicate().is_some()
            || signature_record.target().is_some()
            || signature_record.mapper().is_some()
            || signature_record.isolated_signature_type().is_some()
            || signature_record.composite().is_some()
            || store.signature_has_circular_return_type(signature)
            || !match return_annotation {
                Some((annotation, null_literal_identity)) => valid_signature_return_annotation(
                    store,
                    annotation,
                    null_literal_identity,
                    return_type,
                ),
                None => {
                    matches!(
                        (construct, store.source_node_kind(provider_declaration)),
                        (false, Some(SyntaxKind::TypeLiteral))
                            | (true, Some(SyntaxKind::InterfaceDeclaration))
                    ) && store.source_direct_type_annotation(declaration).is_none()
                        && store
                            .intrinsic_bootstrap()
                            .is_some_and(|bootstrap| return_type == bootstrap.any_type)
                }
            }
            || parameter_types.len() != signature_record.parameters().len()
        {
            return StoredDeclaredCallSetValidation::Malformed;
        }
        let mut seen_parameters = HashSet::with_capacity(parameter_types.len());
        for (parameter_index, (parameter, type_)) in signature_record
            .parameters()
            .iter()
            .copied()
            .zip(parameter_types)
            .enumerate()
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
                || declared_signature_parameter_is_implicit_any_rest(
                    store,
                    *parameter_declaration,
                    *type_,
                ) != (has_rest
                    && parameter_index == fixed_parameter_count
                    && store
                        .source_direct_type_annotation(*parameter_declaration)
                        .is_none())
                || declared_signature_parameter_is_optional(store, *parameter_declaration, *type_)
                    .is_none_or(|optional| {
                        optional
                            != ((construct
                                || store.source_node_kind(provider_declaration)
                                    == Some(SyntaxKind::TypeLiteral))
                                && parameter_index >= minimum
                                && parameter_index < fixed_parameter_count)
                    })
                || store
                    .source_direct_type_annotation(*parameter_declaration)
                    .is_some()
                    && declared_signature_parameter_is_rest(store, *parameter_declaration)
                        .is_none_or(|rest| {
                            rest != (has_rest && parameter_index == fixed_parameter_count)
                        })
            {
                return StoredDeclaredCallSetValidation::Malformed;
            }
            edges.push(*type_);
        }
        for parameter in signature_record.type_parameters() {
            let Some(TypeData::TypeParameter(data)) =
                store.type_payload(*parameter).map(TypeRecord::data)
            else {
                return StoredDeclaredCallSetValidation::Malformed;
            };
            edges.push(*parameter);
            edges.extend(data.constraint);
            edges.extend(data.resolved_default_type);
        }
        edges.push(return_type);
    }
    edges.extend(member_edges);
    StoredDeclaredCallSetValidation::Valid(edges)
}

fn validate_declared_call_set_member_edges(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    owner: SemanticSymbolId,
    owner_declaration: NodeRef,
    structured: &StructuredTypeData,
    signature_family_count: usize,
) -> Option<Vec<TypeId>> {
    let members = structured
        .members
        .and_then(|members| store.symbol_table(members))?;
    let properties = match structured.properties.as_deref() {
        None => &[][..],
        Some(properties) if !properties.is_empty() => properties,
        Some(_) => return None,
    };
    let indexes = match structured.index_infos.as_deref() {
        None => &[][..],
        Some(indexes) if !indexes.is_empty() => indexes,
        Some(_) => return None,
    };
    if !properties.is_empty()
        && !matches!(
            store.source_node_kind(owner_declaration),
            Some(SyntaxKind::InterfaceDeclaration | SyntaxKind::TypeLiteral)
        )
        || !indexes.is_empty()
            && store.source_node_kind(owner_declaration) != Some(SyntaxKind::InterfaceDeclaration)
        || members.len()
            != signature_family_count
                .checked_add(properties.len())?
                .checked_add(usize::from(!indexes.is_empty()))?
    {
        return None;
    }

    let mut edges = Vec::with_capacity(properties.len() + indexes.len() * 2);
    let mut seen_properties = HashSet::with_capacity(properties.len());
    let mut seen_declarations = HashSet::with_capacity(properties.len());
    let mut previous_declaration = None;
    for property in properties {
        let record = store.symbol(*property)?;
        let declarations = record.declarations()?;
        let declaration = *declarations.first()?;
        let method = record.flags() == SymbolFlags::METHOD;
        let accessor = record.flags().intersects(SymbolFlags::ACCESSOR);
        let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::ACCESSOR;
        if !seen_properties.insert(*property)
            || (method || accessor)
                && store.source_node_kind(owner_declaration)
                    != Some(SyntaxKind::InterfaceDeclaration)
            || !method
                && (!record.flags().contains(SymbolFlags::PROPERTY) && !accessor
                    || record.flags().without(allowed_flags) != SymbolFlags::NONE)
            || method && record.check_flags() != CheckFlags::NONE
            || !method && record.check_flags().bits() & !CheckFlags::READONLY.bits() != 0
            || accessor && record.check_flags() != CheckFlags::NONE
            || record.name().is_reserved_member_name()
            || record.name().is_private_identifier()
            || record.name().is_late_bound()
            || record.name().as_utf8().is_none()
            || record.value_declaration() != Some(declaration)
            || store.get_parent_of_symbol(*property) != Some(owner)
            || record.members().is_some()
            || record.exports().is_some()
            || record.export_symbol().is_some()
            || store.get_merged_symbol(*property) != Some(*property)
            || members.get(record.name()) != Some(*property)
            || previous_declaration.is_some_and(|previous| previous >= declaration)
            || !declarations.iter().all(|declaration| {
                store.source_node_parent(*declaration)
                    == Some(SourceNodeParent::Parent(owner_declaration))
                    && declaration.is_for(owner_declaration.arena, owner_declaration.file)
                    && *declaration < owner_declaration
                    && if method {
                        store.source_node_kind(*declaration) == Some(SyntaxKind::MethodSignature)
                    } else {
                        matches!(
                            store.source_node_kind(*declaration),
                            Some(
                                SyntaxKind::PropertyDeclaration
                                    | SyntaxKind::PropertySignature
                                    | SyntaxKind::GetAccessor
                                    | SyntaxKind::SetAccessor
                            )
                        )
                    }
                    && seen_declarations.insert(*declaration)
            })
        {
            return None;
        }
        let links = store.value_symbol_links(*property)?;
        let property_type = links.resolved_type?;
        if links
            != &(ValueSymbolLinks {
                resolved_type: Some(property_type),
                write_type: links.write_type,
                ..ValueSymbolLinks::default()
            })
            || links.write_type.is_some_and(|write_type| {
                !accessor
                    || !record.flags().contains(SymbolFlags::SET_ACCESSOR)
                    || write_type == property_type
                    || store.type_payload(write_type).is_none()
            })
            || store.type_payload(property_type).is_none()
            || !method
                && !accessor
                && store
                    .source_direct_type_annotation(declaration)
                    .is_none_or(|annotation| {
                        !store.source_direct_type_annotation_is_exact(annotation, property_type)
                    })
            || method
                && (store.authenticated_interface_method_owner(*property) != Some((owner, type_))
                    || !matches!(
                        super::callable_sets::validate_stored_declared_method_callable_set(
                            store,
                            property_type,
                        ),
                        Some(super::callable_sets::StoredCallableSetValidation::Valid {
                            projection,
                            ..
                        }) if projection.owner == property_type
                            && projection.call_signatures.iter().any(|callable| {
                                store
                                    .signature(callable.signature)
                                    .and_then(super::signatures::Signature::declaration)
                                    == Some(declaration)
                            })
                    ))
        {
            return None;
        }
        edges.push(property_type);
        edges.extend(links.write_type);
        previous_declaration = Some(declaration);
    }

    match (indexes, members.get(InternalSymbolName::Index.as_ref())) {
        ([], None) => {}
        (indexes, Some(symbol))
            if !indexes.is_empty()
                && super::structured_members::valid_index_symbol(
                    store,
                    owner,
                    &[owner_declaration],
                    symbol,
                    indexes,
                ) =>
        {
            for index in indexes {
                let info = store.index_info(*index)?;
                edges.push(info.key_type());
                edges.push(info.value_type());
            }
        }
        _ => return None,
    }

    if store.type_payload(type_).and_then(TypeRecord::symbol) != Some(owner) {
        return None;
    }
    Some(edges)
}

fn declared_signature_parameter_is_optional(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    type_: TypeId,
) -> Option<bool> {
    let Some(annotation) = store.source_direct_type_annotation(declaration) else {
        return declared_signature_parameter_is_implicit_any_rest(store, declaration, type_)
            .then_some(false);
    };
    let question_index = annotation.node.index().checked_sub(1)?;
    let question = NodeRef::new(
        declaration.arena,
        declaration.file,
        ts_ast::NodeId::new(u32::try_from(question_index).ok()?),
    );
    let optional = store.source_node_kind(question) == Some(SyntaxKind::QuestionToken)
        && store.source_node_parent(question) == Some(SourceNodeParent::Parent(declaration));
    if optional {
        let any = store.intrinsic_bootstrap()?.any_type;
        if store.source_node_kind(annotation) != Some(SyntaxKind::AnyKeyword) || type_ != any {
            return None;
        }
    }
    Some(optional)
}

pub(super) fn declared_signature_parameter_is_rest(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> Option<bool> {
    let annotation = store.source_direct_type_annotation(declaration)?;
    let name = (0..annotation.node.index()).rev().find_map(|index| {
        let node = NodeRef::new(
            declaration.arena,
            declaration.file,
            ts_ast::NodeId::new(u32::try_from(index).ok()?),
        );
        (store.source_node_kind(node) == Some(SyntaxKind::Identifier)
            && store.source_node_parent(node) == Some(SourceNodeParent::Parent(declaration)))
        .then_some(node)
    })?;
    let found = name
        .node
        .index()
        .checked_sub(1)
        .and_then(|index| u32::try_from(index).ok())
        .map(|index| {
            NodeRef::new(
                declaration.arena,
                declaration.file,
                ts_ast::NodeId::new(index),
            )
        })
        .is_some_and(|token| {
            store.source_node_kind(token) == Some(SyntaxKind::DotDotDotToken)
                && store.source_node_parent(token) == Some(SourceNodeParent::Parent(declaration))
        });
    if found
        && !matches!(
            store.source_node_kind(annotation),
            Some(
                SyntaxKind::ArrayType
                    | SyntaxKind::TupleType
                    | SyntaxKind::UnionType
                    | SyntaxKind::InferType
            )
        )
    {
        return None;
    }
    Some(found)
}

fn declared_signature_parameter_is_implicit_any_rest(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    type_: TypeId,
) -> bool {
    let Some(SourceNodeParent::Parent(signature)) = store.source_node_parent(declaration) else {
        return false;
    };
    let Some(SourceNodeParent::Parent(owner)) = store.source_node_parent(signature) else {
        return false;
    };
    if store.source_node_kind(declaration) != Some(SyntaxKind::Parameter)
        || store.source_node_kind(signature) != Some(SyntaxKind::CallSignature)
        || store.source_node_kind(owner) != Some(SyntaxKind::TypeLiteral)
        || store.source_direct_type_annotation(declaration).is_some()
        || implicit_any_array_type(store) != Some(type_)
    {
        return false;
    }
    (0..declaration.node.index()).any(|index| {
        let Ok(index) = u32::try_from(index) else {
            return false;
        };
        let token = NodeRef::new(
            declaration.arena,
            declaration.file,
            ts_ast::NodeId::new(index),
        );
        store.source_node_kind(token) == Some(SyntaxKind::DotDotDotToken)
            && store.source_node_parent(token) == Some(SourceNodeParent::Parent(declaration))
    })
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
        || symbol_record.export_symbol().is_some()
    {
        return Err(PropertyObjectError::InvalidObjectLiteral(node));
    }
    if let Some(exports) = symbol_record.exports() {
        return plan_javascript_expando_object_literal(store, host, node, symbol, exports);
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
    let mut plan = plan_members(
        store,
        host,
        PropertyObjectKind::ObjectLiteral,
        node,
        symbol,
        symbol_record.members(),
        &object.properties,
        &[],
        None,
        TypeLiteralMemberPolicy::General,
    )?;
    plan.const_context = object_literal_has_const_assertion(store, host, node)?;
    if plan.const_context {
        for property in &mut plan.properties {
            property.readonly = true;
        }
    }
    Ok(plan)
}

fn plan_javascript_expando_object_literal(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    owner: SemanticSymbolId,
    exports: SymbolTableId,
) -> Result<PropertyObjectPlan, PropertyObjectError> {
    let invalid = || PropertyObjectError::InvalidObjectLiteral(node);
    let (arena, bound) = host.source(node).ok_or_else(invalid)?;
    if bound
        .source_facts()
        .is_none_or(|facts| !facts.is_javascript_file() || facts.is_declaration_file())
        || bound.symbol(node) != Some(owner)
        || store
            .symbol(owner)
            .is_none_or(|symbol| symbol.members().is_some())
    {
        return Err(invalid());
    }
    let object = host.node(node).ok_or_else(invalid)?;
    let NodeData::ObjectLiteralExpression(object) = &object.data else {
        return Err(invalid());
    };
    if !object.properties.nodes.is_empty() {
        return Err(invalid());
    }
    let table = store.symbol_table(exports).ok_or_else(invalid)?;
    if table.is_empty() {
        return Err(invalid());
    }

    let mut properties = Vec::with_capacity(table.len());
    for (name, property) in table.iter() {
        let record = store.symbol(property).ok_or_else(invalid)?;
        let Some([declaration]) = record.declarations() else {
            return Err(invalid());
        };
        let declaration = *declaration;
        let statement = host
            .node(declaration)
            .and_then(|declaration| declaration.parent)
            .map(|statement| NodeRef::new(node.arena, node.file, statement))
            .ok_or_else(invalid)?;
        let assignment = super::assignment::plan_javascript_object_expando_assignment(
            arena, bound, store, statement,
        )
        .map_err(|_| invalid())?
        .ok_or_else(invalid)?;
        if assignment.expression != declaration
            || assignment.owner_symbol != owner
            || assignment.property_symbol != property
            || record.name() != name
        {
            return Err(invalid());
        }
        let name = name.as_utf8().ok_or_else(invalid)?.to_owned();
        properties.push(PlannedProperty {
            declaration,
            symbol: property,
            name_node: assignment.name,
            type_node: assignment.right,
            optional: false,
            readonly: false,
            name,
        });
    }
    properties.sort_by_key(|property| {
        host.node(property.declaration)
            .map(|declaration| declaration.range.start)
    });

    Ok(PropertyObjectPlan {
        kind: PropertyObjectKind::ObjectLiteral,
        node,
        const_context: false,
        declarations: vec![node],
        symbol: owner,
        members: Some(exports),
        properties,
        methods: Vec::new(),
        accessors: Vec::new(),
        spreads: Vec::new(),
        indexes: Vec::new(),
        call_signatures: Vec::new(),
        alias_symbol: None,
        heritage: None,
    })
}

/// Authenticates an object assignment pattern without treating it as a value literal.
#[allow(clippy::too_many_lines)] // Validates the complete binder-owned assignment pattern together.
pub(super) fn plan_object_assignment_shorthand(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<Option<PlannedObjectAssignmentShorthand>, PropertyObjectError> {
    let invalid = || PropertyObjectError::InvalidObjectLiteral(node);
    let record = preflight_node(store, host, node).map_err(|_| invalid())?;
    let NodeData::ObjectLiteralExpression(object) = &record.data else {
        return Ok(None);
    };
    let [property] = object.properties.nodes.as_slice() else {
        return Ok(None);
    };
    let declaration = NodeRef::new(node.arena, node.file, *property);
    let property_record = preflight_node(store, host, declaration).map_err(|_| invalid())?;
    let NodeData::ShorthandPropertyAssignment(property) = &property_record.data else {
        return Ok(None);
    };
    let (Some(equals), Some(initializer)) = (
        property.equals_token,
        property.object_assignment_initializer,
    ) else {
        return Ok(None);
    };
    let equals = NodeRef::new(node.arena, node.file, equals);
    let initializer = NodeRef::new(node.arena, node.file, initializer);
    let name = NodeRef::new(node.arena, node.file, property.name);
    let equals_record = preflight_node(store, host, equals).map_err(|_| invalid())?;
    let initializer_record = preflight_node(store, host, initializer).map_err(|_| invalid())?;
    let name_record = preflight_node(store, host, name).map_err(|_| invalid())?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invalid());
    };
    let owner = bound_symbol(store, host, node).ok_or_else(invalid)?;
    let owner_record = store.symbol(owner).ok_or_else(invalid)?;
    let symbol = bound_symbol(store, host, declaration).ok_or_else(invalid)?;
    let symbol_record = store.symbol(symbol).ok_or_else(invalid)?;
    let members = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
        .ok_or_else(invalid)?;
    if record.kind != SyntaxKind::ObjectLiteralExpression
        || record.flags.0 & NODE_FLAG_JSDOC != 0
        || object.symbol.is_some()
        || object.facts != 0
        || object.properties.range != record.range
        || object.properties.has_trailing_comma
        || owner_record.flags() != SymbolFlags::OBJECT_LITERAL
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name() != InternalSymbolName::Object.as_ref()
        || owner_record.declarations() != Some(&[node])
        || owner_record.value_declaration() != Some(node)
        || owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || property_record.kind != SyntaxKind::ShorthandPropertyAssignment
        || property_record.flags.0 != 0
        || property_record.parent != Some(node.node)
        || property.postfix_token.is_some()
        || property.modifiers.is_some()
        || property.type_.is_some()
        || property.symbol.is_some()
        || property.facts != 0
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || equals_record.kind != SyntaxKind::EqualsToken
        || equals_record.flags.0 != 0
        || equals_record.parent != Some(declaration.node)
        || !matches!(equals_record.data, NodeData::Token(_))
        || initializer_record.parent != Some(declaration.node)
        || name_record.range.end > equals_record.range.start
        || equals_record.range.end > initializer_record.range.start
        || initializer_record.range.end > property_record.range.end
        || symbol_record.flags() != SymbolFlags::PROPERTY
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || symbol_record.declarations() != Some(&[declaration])
        || symbol_record.value_declaration() != Some(declaration)
        || symbol_record.parent() != Some(owner)
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || members.len() != 1
        || members.get_source(&identifier.text) != Some(symbol)
        || store
            .value_symbol_links(symbol)
            .is_some_and(|links| links != &ValueSymbolLinks::default())
    {
        return Err(invalid());
    }

    Ok(Some(PlannedObjectAssignmentShorthand {
        object: node,
        owner,
        declaration,
        symbol,
        name,
        initializer,
    }))
}

fn object_literal_has_const_assertion(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<bool, PropertyObjectError> {
    let invalid = || PropertyObjectError::InvalidObjectLiteral(node);
    let mut operand = node;
    loop {
        let Some(parent) = preflight_node(store, host, operand)
            .map_err(|_| invalid())?
            .parent
        else {
            return Ok(false);
        };
        let parent = NodeRef::new(operand.arena, operand.file, parent);
        let record = preflight_node(store, host, parent).map_err(|_| invalid())?;
        let type_node = match (&record.data, record.kind) {
            (
                NodeData::ParenthesizedExpression(parenthesized),
                SyntaxKind::ParenthesizedExpression,
            ) if parenthesized.expression == operand.node => {
                operand = parent;
                continue;
            }
            (NodeData::PropertyAssignment(property), SyntaxKind::PropertyAssignment)
                if property.initializer == operand.node =>
            {
                let owner = record.parent.ok_or_else(invalid)?;
                let owner = NodeRef::new(parent.arena, parent.file, owner);
                let owner_record = preflight_node(store, host, owner).map_err(|_| invalid())?;
                let NodeData::ObjectLiteralExpression(object) = &owner_record.data else {
                    return Err(invalid());
                };
                if owner_record.kind != SyntaxKind::ObjectLiteralExpression
                    || !object.properties.nodes.contains(&parent.node)
                {
                    return Err(invalid());
                }
                operand = owner;
                continue;
            }
            (NodeData::AsExpression(assertion), SyntaxKind::AsExpression)
                if assertion.expression == operand.node =>
            {
                assertion.type_
            }
            (NodeData::TypeAssertion(assertion), SyntaxKind::TypeAssertionExpression)
                if assertion.expression == operand.node =>
            {
                assertion.type_
            }
            _ => return Ok(false),
        };
        let type_node = NodeRef::new(parent.arena, parent.file, type_node);
        let type_record = preflight_node(store, host, type_node).map_err(|_| invalid())?;
        if type_record.parent != Some(parent.node) {
            return Err(invalid());
        }
        let NodeData::TypeReferenceNode(reference) = &type_record.data else {
            return Ok(false);
        };
        if type_record.kind != SyntaxKind::TypeReference || reference.type_arguments.is_some() {
            return Ok(false);
        }
        let name = NodeRef::new(type_node.arena, type_node.file, reference.type_name);
        let name_record = preflight_node(store, host, name).map_err(|_| invalid())?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Ok(false);
        };
        return Ok(name_record.kind == SyntaxKind::Identifier
            && name_record.parent == Some(type_node.node)
            && identifier.text == "const");
    }
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
        &[],
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
    let merged_namespace_interface =
        authenticated_merged_namespace_interface(store, host, symbol).is_some();
    // `resolveDeclaredMembers` reads the merged symbol's member table
    // independently of its value side. A function-scoped value declaration
    // such as the standard library's `declare var Object` is therefore inert
    // for this property-only interface plan.
    let mut interface_declarations = Vec::new();
    let mut value_declarations = Vec::new();
    let mut namespace_declarations = Vec::new();
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
            (SyntaxKind::InterfaceDeclaration, NodeData::InterfaceDeclaration(_)) => {
                interface_declarations.push(*candidate);
            }
            (SyntaxKind::VariableDeclaration, NodeData::VariableDeclaration(_)) => {
                value_declarations.push(*candidate);
            }
            (SyntaxKind::ModuleDeclaration, NodeData::ModuleDeclaration(_))
                if merged_namespace_interface =>
            {
                namespace_declarations.push(*candidate);
            }
            _ => {
                return Err(PropertyObjectError::InvalidInterface {
                    declaration: *candidate,
                    symbol,
                });
            }
        }
    }
    let Some(&declaration) = interface_declarations.first() else {
        return Err(PropertyObjectError::InvalidInterfaceSymbol(symbol));
    };
    let expected_symbol_flags = SymbolFlags::INTERFACE
        | if value_declarations.is_empty() {
            SymbolFlags::NONE
        } else {
            SymbolFlags::FUNCTION_SCOPED_VARIABLE
        }
        | if namespace_declarations.is_empty() {
            SymbolFlags::NONE
        } else {
            SymbolFlags::NAMESPACE_MODULE
        };
    let valid_value_declaration = match symbol_record.value_declaration() {
        None => value_declarations.is_empty(),
        Some(value) => value_declarations.contains(&value),
    };
    if symbol_record.flags().without(SymbolFlags::TRANSIENT) != expected_symbol_flags
        || symbol_record.check_flags() != CheckFlags::NONE
        || !valid_value_declaration
        || merged_namespace_interface == namespace_declarations.is_empty()
        || merged_namespace_interface && !value_declarations.is_empty()
        || symbol_record.exports().is_some() != merged_namespace_interface
        || symbol_record.export_symbol().is_some()
    {
        return Err(PropertyObjectError::InvalidInterface {
            declaration,
            symbol,
        });
    }
    let mut additional_members = Vec::with_capacity(interface_declarations.len() - 1);
    let mut heritage = None;
    for (index, &candidate) in interface_declarations.iter().enumerate() {
        let invalid = || PropertyObjectError::InvalidInterface {
            declaration: candidate,
            symbol,
        };
        let record = preflight_node(store, host, candidate).map_err(|_| invalid())?;
        let NodeData::InterfaceDeclaration(interface) = &record.data else {
            return Err(invalid());
        };
        let name = NodeRef::new(candidate.arena, candidate.file, interface.name);
        let name_record = preflight_node(store, host, name).map_err(|_| invalid())?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(invalid());
        };
        let expected_parent = declared_type_declaration_parent(
            store,
            host,
            candidate,
            symbol,
            name,
            interface.modifiers.as_ref(),
        )
        .map_err(|()| invalid())?;
        if record.kind != SyntaxKind::InterfaceDeclaration
            || record.flags.0 != 0
            || !host.symbol_matches(store, candidate, symbol)
            || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
            || symbol_record.parent().is_some() != expected_parent.is_some()
            || store.get_parent_of_symbol(symbol) != expected_parent
            || name_record.kind != SyntaxKind::Identifier
            || name_record.parent != Some(candidate.node)
            || interface.flow_node.is_some()
            || interface.local_symbol.is_some()
            || interface.symbol.is_some()
            || interface.type_parameters.is_some()
            || interface.members.has_trailing_comma
            || interface.members.range.start < record.range.start
            || interface.members.range.end != record.range.end
        {
            return Err(invalid());
        }
        if let Some(clauses) = interface.heritage_clauses.as_ref() {
            let planned = plan_direct_interface_heritage(store, host, candidate, symbol, clauses)
                .map_err(|error| match error {
                DirectInterfaceHeritageError::Invalid => invalid(),
                DirectInterfaceHeritageError::Unsupported { node, kind } => {
                    PropertyObjectError::UnsupportedMember { node, kind }
                }
            })?;
            merge_interface_heritage(store, host, &mut heritage, planned, 2)?;
        }
        if index != 0 {
            additional_members.push((candidate, &interface.members));
        }
    }
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
    let mut plan = plan_members(
        store,
        host,
        PropertyObjectKind::Interface,
        declaration,
        symbol,
        symbol_record.members(),
        &interface.members,
        &additional_members,
        None,
        TypeLiteralMemberPolicy::General,
    )?;
    plan.heritage = heritage;
    if let Some(call) = plan.call_signatures.first()
        && !plan.properties.is_empty()
        && (!value_declarations.is_empty() || !namespace_declarations.is_empty())
    {
        return Err(PropertyObjectError::UnsupportedMember {
            node: call.declaration,
            kind: call.syntax_kind(),
        });
    }
    if let Some(method) = plan.methods.first()
        && (!value_declarations.is_empty()
            && !authenticated_global_math_random_interface(
                store,
                host,
                symbol,
                &value_declarations,
                &plan,
            )
            && !authenticated_global_builtin_interface(
                store,
                host,
                symbol,
                &value_declarations,
                &plan,
            )
            || symbol_record.name().as_utf8() == Some("IntrinsicElements")
                && store
                    .get_parent_of_symbol(symbol)
                    .and_then(|namespace| store.symbol(namespace))
                    .is_some_and(|namespace| namespace.name().as_utf8() == Some("JSX")))
    {
        return Err(PropertyObjectError::UnsupportedMember {
            node: method.declaration,
            kind: SyntaxKind::MethodSignature,
        });
    }
    if let Some(heritage) = plan.heritage.as_ref() {
        if heritage.bases.iter().any(|base| {
            matches!(
                base.kind,
                DirectInterfaceBaseKind::DefaultLibraryInterface
                    | DirectInterfaceBaseKind::DefaultLibraryArray
            )
        }) {
            if !matches!(
                heritage.bases.as_slice(),
                [base]
                    if base.kind == DirectInterfaceBaseKind::DefaultLibraryInterface
                        && base.type_arguments.is_empty()
                        || base.kind == DirectInterfaceBaseKind::DefaultLibraryArray
                            && base.type_arguments.len() == 1
            ) || !plan.properties.is_empty()
                || !plan.spreads.is_empty()
                || !plan.indexes.is_empty()
                || !plan.call_signatures.is_empty()
                || !value_declarations.is_empty()
                || plan.members.is_some()
                || plan.declarations.len() != 1
            {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: plan.node,
                    kind: SyntaxKind::InterfaceDeclaration,
                });
            }
            return Ok(plan);
        }
        if let Some(index) = plan.indexes.first() {
            return Err(PropertyObjectError::UnsupportedMember {
                node: index.declaration,
                kind: SyntaxKind::IndexSignature,
            });
        }
        if !matches!(heritage.bases.as_slice(), [_] | [_, _]) {
            return Err(PropertyObjectError::UnsupportedMember {
                node: heritage.clause,
                kind: SyntaxKind::HeritageClause,
            });
        }
        let mut base_plans = Vec::<PropertyObjectPlan>::with_capacity(heritage.bases.len());
        let mut effective_base_properties =
            Vec::<Vec<PlannedProperty>>::with_capacity(heritage.bases.len());
        for base in &heritage.bases {
            if !base.type_arguments.is_empty() {
                plan_generic_interface(store, host, base.symbol)?;
                if authenticated_react_portal_interface(store, host, &plan)? {
                    return Ok(plan);
                }
                return Err(PropertyObjectError::UnsupportedMember {
                    node: base.node,
                    kind: SyntaxKind::ExpressionWithTypeArguments,
                });
            }
            let base_plan = plan_interface(store, host, base.symbol)?;
            if let Some(index) = base_plan.indexes.first() {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: index.declaration,
                    kind: SyntaxKind::IndexSignature,
                });
            }
            if base_plan.heritage.is_some()
                && (!base_plan.call_signatures.is_empty() || !plan.call_signatures.is_empty())
            {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: base.node,
                    kind: SyntaxKind::ExpressionWithTypeArguments,
                });
            }
            if let Some(call) = base_plan.call_signatures.first()
                && (heritage.bases.len() != 1
                    || !base_plan.properties.is_empty()
                    || !plan.properties.is_empty()
                    || plan.call_signatures.is_empty()
                    || call.is_construct()
                    || plan
                        .call_signatures
                        .iter()
                        .any(PlannedCallSignature::is_construct))
            {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: call.declaration,
                    kind: call.syntax_kind(),
                });
            }
            let mut properties = Vec::new();
            collect_interface_property_heritage(
                store,
                host,
                &base_plan,
                &mut properties,
                &mut HashSet::from([symbol]),
                0,
            )?;
            for previous in &effective_base_properties {
                for property in &properties {
                    let Some(inherited) = previous
                        .iter()
                        .find(|inherited| inherited.name == property.name)
                    else {
                        continue;
                    };
                    let inherited_method = store
                        .symbol(inherited.symbol)
                        .is_some_and(|symbol| symbol.flags().contains(SymbolFlags::METHOD));
                    let property_method = store
                        .symbol(property.symbol)
                        .is_some_and(|symbol| symbol.flags().contains(SymbolFlags::METHOD));
                    let matching_annotations = if inherited_method || property_method {
                        inherited_method
                            && property_method
                            && matching_planned_interface_method_contract(
                                store, host, inherited, property,
                            )
                    } else {
                        equivalent_merged_property_annotations(
                            store,
                            host,
                            inherited.type_node,
                            property.type_node,
                        )
                    };
                    if inherited.optional != property.optional
                        || inherited.readonly != property.readonly
                        || !matching_annotations
                    {
                        return Err(PropertyObjectError::UnsupportedMember {
                            node: property.declaration,
                            kind: store
                                .source_node_kind(property.declaration)
                                .unwrap_or(SyntaxKind::PropertySignature),
                        });
                    }
                }
            }
            effective_base_properties.push(properties);
            base_plans.push(base_plan);
        }
        if let Some(call) = plan.call_signatures.first()
            && (base_plans.len() != 1
                || base_plans[0].call_signatures.is_empty()
                || !base_plans[0].properties.is_empty()
                || !plan.properties.is_empty()
                || call.is_construct()
                || base_plans[0]
                    .call_signatures
                    .iter()
                    .any(PlannedCallSignature::is_construct))
        {
            return Err(PropertyObjectError::UnsupportedMember {
                node: call.declaration,
                kind: call.syntax_kind(),
            });
        }
        if !value_declarations.is_empty() {
            return Err(PropertyObjectError::UnsupportedMember {
                node: heritage.clause,
                kind: SyntaxKind::HeritageClause,
            });
        }
        for base_properties in &effective_base_properties {
            for property in &plan.properties {
                let Some(base_property) = base_properties
                    .iter()
                    .find(|base| base.name == property.name)
                else {
                    continue;
                };
                let own_kind = store.source_node_kind(property.type_node);
                let base_kind = store.source_node_kind(base_property.type_node);
                let own_method = store
                    .symbol(property.symbol)
                    .is_some_and(|symbol| symbol.flags().contains(SymbolFlags::METHOD));
                let base_method = store
                    .symbol(base_property.symbol)
                    .is_some_and(|symbol| symbol.flags().contains(SymbolFlags::METHOD));
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
                let compatible = if own_method || base_method {
                    own_method
                        && base_method
                        && matching_planned_interface_method_contract(
                            store,
                            host,
                            property,
                            base_property,
                        )
                } else {
                    same_primitive
                        || own_kind == Some(SyntaxKind::AnyKeyword)
                            && base_kind != Some(SyntaxKind::NeverKeyword)
                };
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
    }
    if !value_declarations.is_empty() && !plan.call_signatures.is_empty() {
        return Err(PropertyObjectError::InvalidInterface {
            declaration,
            symbol,
        });
    }
    Ok(plan)
}

/// Proves the exact lazy `ReactPortal extends ReactElement<any>` declaration.
#[allow(clippy::too_many_lines)] // Portal, base, properties, and module ownership are one proof.
pub(super) fn authenticated_react_portal_interface(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &PropertyObjectPlan,
) -> Result<bool, PropertyObjectError> {
    let Some(heritage) = plan.heritage.as_ref() else {
        return Ok(false);
    };
    let [base] = heritage.bases.as_slice() else {
        return Ok(false);
    };
    let [key, children] = plan.properties.as_slice() else {
        return Ok(false);
    };
    let Some(owner) = store.symbol(plan.symbol) else {
        return Err(PropertyObjectError::InvalidInterfaceSymbol(plan.symbol));
    };
    let Some(namespace) = store.get_parent_of_symbol(plan.symbol) else {
        return Ok(false);
    };
    let Some(namespace_owner) = store.symbol(namespace) else {
        return Err(PropertyObjectError::InvalidInterfaceSymbol(namespace));
    };
    let Some(exports) = namespace_owner
        .exports()
        .and_then(|exports| store.symbol_table(exports))
    else {
        return Ok(false);
    };
    let Some(members) = plan.members.and_then(|members| store.symbol_table(members)) else {
        return Ok(false);
    };
    let Some(bound) = host.bound_file(plan.node) else {
        return Ok(false);
    };
    let Some(facts) = bound.source_facts() else {
        return Ok(false);
    };
    if plan.kind != PropertyObjectKind::Interface
        || plan.declarations.as_slice() != [plan.node]
        || plan.const_context
        || !plan.methods.is_empty()
        || !plan.accessors.is_empty()
        || !plan.spreads.is_empty()
        || !plan.indexes.is_empty()
        || !plan.call_signatures.is_empty()
        || plan.alias_symbol.is_some()
        || owner.flags() != SymbolFlags::INTERFACE
        || owner.check_flags() != CheckFlags::NONE
        || owner.name().as_utf8() != Some("ReactPortal")
        || owner.declarations() != Some(&[plan.node])
        || owner.value_declaration().is_some()
        || owner.members() != plan.members
        || owner.exports().is_some()
        || owner.export_symbol().is_some()
        || !host.symbol_matches(store, plan.node, plan.symbol)
        || !facts.is_declaration_file()
        || facts.is_default_library()
        || !namespace_owner.flags().intersects(SymbolFlags::NAMESPACE)
        || namespace_owner.check_flags() != CheckFlags::NONE
        || namespace_owner.name().as_utf8() != Some("React")
        || exports
            .get_source("ReactPortal")
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(plan.symbol)
        || base.kind != DirectInterfaceBaseKind::Interface
        || base.type_arguments.len() != 1
        || store
            .symbol(base.symbol)
            .and_then(|symbol| symbol.name().as_utf8())
            != Some("ReactElement")
        || store.get_parent_of_symbol(base.symbol) != Some(namespace)
        || exports
            .get_source("ReactElement")
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(base.symbol)
        || members.len() != 2
        || key.name != "key"
        || children.name != "children"
    {
        return Ok(false);
    }

    for property in [key, children] {
        let Some(record) = store.symbol(property.symbol) else {
            return Ok(false);
        };
        if property.optional
            || property.readonly
            || record.flags() != SymbolFlags::PROPERTY
            || record.check_flags() != CheckFlags::NONE
            || record.name().as_utf8() != Some(property.name.as_str())
            || record.declarations() != Some(&[property.declaration])
            || record.value_declaration() != Some(property.declaration)
            || record.members().is_some()
            || record.exports().is_some()
            || record.export_symbol().is_some()
            || store.get_parent_of_symbol(property.symbol) != Some(plan.symbol)
            || members.get(record.name()) != Some(property.symbol)
            || !host.symbol_matches(store, property.declaration, property.symbol)
        {
            return Ok(false);
        }
    }

    let argument = base.type_arguments[0];
    let Some(argument_record) = host.node(argument) else {
        return Ok(false);
    };
    if argument_record.kind != SyntaxKind::AnyKeyword
        || argument_record.flags.0 != 0
        || argument_record.parent != Some(base.node.node)
    {
        return Ok(false);
    }

    let generic = plan_generic_interface(store, host, base.symbol)?;
    let [element_type, element_props, element_key] = generic.properties.as_slice() else {
        return Ok(false);
    };
    if generic.heritage.is_some()
        || !generic.methods.is_empty()
        || !generic.accessors.is_empty()
        || !generic.spreads.is_empty()
        || !generic.indexes.is_empty()
        || !generic.call_signatures.is_empty()
        || element_type.name != "type"
        || element_props.name != "props"
        || element_key.name != "key"
        || !equivalent_merged_property_annotations(
            store,
            host,
            key.type_node,
            element_key.type_node,
        )
    {
        return Ok(false);
    }

    let Some(child_record) = host.node(children.type_node) else {
        return Ok(false);
    };
    let NodeData::TypeReferenceNode(child_reference) = &child_record.data else {
        return Ok(false);
    };
    let child_name = NodeRef::new(
        children.type_node.arena,
        children.type_node.file,
        child_reference.type_name,
    );
    let Some(child_name_record) = host.node(child_name) else {
        return Ok(false);
    };
    let NodeData::Identifier(identifier) = &child_name_record.data else {
        return Ok(false);
    };
    let Some(react_node) = exports
        .get_source("ReactNode")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(false);
    };
    let Some(alias) = store.symbol(react_node) else {
        return Ok(false);
    };
    let Ok(mut resolver) = host.name_resolver_host(store) else {
        return Ok(false);
    };
    if child_record.kind != SyntaxKind::TypeReference
        || child_record.flags.0 != 0
        || child_record.parent != Some(children.declaration.node)
        || child_reference.type_arguments.is_some()
        || child_name_record.kind != SyntaxKind::Identifier
        || child_name_record.flags.0 != 0
        || child_name_record.parent != Some(children.type_node.node)
        || identifier.flow_node.is_some()
        || identifier.text != "ReactNode"
        || alias.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::TYPE_ALIAS
        || alias.check_flags() != CheckFlags::NONE
        || store.get_parent_of_symbol(react_node) != Some(namespace)
        || resolver
            .resolve_entity_name(child_name, SymbolFlags::TYPE)
            .ok()
            .flatten()
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(react_node)
    {
        return Ok(false);
    }

    Ok(true)
}

fn authenticated_global_math_random_interface(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    value_declarations: &[NodeRef],
    plan: &PropertyObjectPlan,
) -> bool {
    let [declaration] = value_declarations else {
        return false;
    };
    let mut random_methods = plan.methods.iter().filter(|method| {
        store
            .symbol(method.symbol)
            .is_some_and(|method| method.name().as_utf8() == Some("random"))
    });
    let Some(method) = random_methods.next() else {
        return false;
    };
    if random_methods.next().is_some()
        || !authenticated_global_math_value_declaration(store, host, symbol, *declaration)
    {
        return false;
    }
    let Some(return_type) = host.node(method.return_type) else {
        return false;
    };
    let method_is_default_library = host
        .bound_file(method.declaration)
        .and_then(ts_binder::BoundFile::source_facts)
        .is_some_and(|facts| facts.is_declaration_file() && facts.is_default_library());

    method.type_parameters.is_empty()
        && method.parameters.is_empty()
        && method.flags == SignatureFlags::NONE
        && method.minimum_argument_count == 0
        && return_type.kind == SyntaxKind::NumberKeyword
        && return_type.flags.0 == 0
        && return_type.parent == Some(method.declaration.node)
        && method_is_default_library
        && plan.accessors.is_empty()
        && plan.spreads.is_empty()
        && plan.indexes.is_empty()
        && plan.call_signatures.is_empty()
        && plan.heritage.is_none()
}

fn authenticated_global_math_value_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
) -> bool {
    authenticated_global_builtin_value_declaration(store, host, symbol, declaration, "Math", "Math")
}

fn authenticated_global_builtin_value_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
    owner_name: &str,
    annotation_name: &str,
) -> bool {
    let Some(owner) = store.symbol(symbol) else {
        return false;
    };
    let allowed =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    let global = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source(owner_name))
        .and_then(|global| store.get_merged_symbol(global));
    let Some(bound) = host.bound_file(declaration) else {
        return false;
    };
    let Some(facts) = bound.source_facts() else {
        return false;
    };
    let Some(declaration_record) = host.node(declaration) else {
        return false;
    };
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return false;
    };
    let Some(annotation) = variable
        .type_
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
    else {
        return false;
    };
    let Some(annotation_record) = host.node(annotation) else {
        return false;
    };
    let NodeData::TypeReferenceNode(reference) = &annotation_record.data else {
        return false;
    };
    let name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
    let Some(name_record) = host.node(name) else {
        return false;
    };
    let NodeData::Identifier(identifier) = &name_record.data else {
        return false;
    };

    owner.name().as_utf8() == Some(owner_name)
        && owner
            .flags()
            .contains(SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE)
        && owner.flags().without(allowed) == SymbolFlags::NONE
        && owner.parent().is_none()
        && owner.value_declaration() == Some(declaration)
        && store.get_merged_symbol(symbol) == Some(symbol)
        && global == Some(symbol)
        && facts.is_declaration_file()
        && facts.is_default_library()
        && !facts.is_javascript_file()
        && !facts.is_external_or_common_js_module()
        && declaration_record.kind == SyntaxKind::VariableDeclaration
        && declaration_record.flags.0 == 0
        && variable.initializer.is_none()
        && variable.exclamation_token.is_none()
        && variable.local_symbol.is_none()
        && variable.symbol.is_none()
        && variable.facts == 0
        && host.symbol_matches(store, declaration, symbol)
        && annotation_record.kind == SyntaxKind::TypeReference
        && annotation_record.flags.0 == 0
        && annotation_record.parent == Some(declaration.node)
        && reference.type_arguments.is_none()
        && name_record.kind == SyntaxKind::Identifier
        && name_record.flags.0 == 0
        && name_record.parent == Some(annotation.node)
        && identifier.flow_node.is_none()
        && identifier.text == annotation_name
}

fn authenticated_global_builtin_interface(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    value_declarations: &[NodeRef],
    plan: &PropertyObjectPlan,
) -> bool {
    let [declaration] = value_declarations else {
        return false;
    };
    let Some(owner_name) = store
        .symbol(symbol)
        .and_then(|owner| owner.name().as_utf8())
    else {
        return false;
    };
    let (annotation_name, marker, parameter_count) = match owner_name {
        "Number" => ("NumberConstructor", "toFixed", 1),
        "String" => ("StringConstructor", "toLowerCase", 0),
        "Object" => ("ObjectConstructor", "toString", 0),
        "Symbol" => ("SymbolConstructor", "toString", 0),
        _ => return false,
    };
    if !authenticated_global_builtin_value_declaration(
        store,
        host,
        symbol,
        *declaration,
        owner_name,
        annotation_name,
    ) {
        return false;
    }
    let mut markers = plan.methods.iter().filter(|method| {
        store
            .symbol(method.symbol)
            .is_some_and(|method| method.name().as_utf8() == Some(marker))
    });
    let Some(method) = markers.next() else {
        return false;
    };
    if markers.next().is_some() {
        return false;
    }
    let Some(return_type) = host.node(method.return_type) else {
        return false;
    };

    method.type_parameters.is_empty()
        && method.parameters.len() == parameter_count
        && (owner_name != "Number"
            || method.parameters.first().is_some_and(|parameter| {
                store.source_node_kind(parameter.type_node) == Some(SyntaxKind::NumberKeyword)
            }))
        && method.flags == SignatureFlags::NONE
        && method.minimum_argument_count == 0
        && return_type.kind == SyntaxKind::StringKeyword
        && return_type.flags.0 == 0
        && return_type.parent == Some(method.declaration.node)
        && plan.methods.iter().all(|method| {
            method.type_parameters.is_empty()
                && host
                    .bound_file(method.declaration)
                    .and_then(ts_binder::BoundFile::source_facts)
                    .is_some_and(|facts| {
                        facts.is_declaration_file()
                            && facts.is_default_library()
                            && !facts.is_javascript_file()
                            && !facts.is_external_or_common_js_module()
                    })
        })
        && plan.indexes.iter().all(|index| {
            owner_name == "String"
                && index.readonly
                && store.source_node_kind(index.key_type_node) == Some(SyntaxKind::NumberKeyword)
                && store.source_node_kind(index.value_type_node) == Some(SyntaxKind::StringKeyword)
        })
        && plan.accessors.is_empty()
        && plan.spreads.is_empty()
        && plan.call_signatures.is_empty()
        && plan.heritage.is_none()
}

fn authenticated_default_library_builtin_symbol_tag(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    declaration: NodeRef,
) -> bool {
    let Ok(record) = preflight_node(store, host, declaration) else {
        return false;
    };
    let (name, type_node, postfix_token, ast_symbol, modifiers, valid_initializer) =
        match &record.data {
            NodeData::PropertyDeclaration(property)
                if record.kind == SyntaxKind::PropertyDeclaration =>
            {
                (
                    property.name,
                    property.type_,
                    property.postfix_token,
                    property.symbol,
                    property.modifiers.as_ref(),
                    property.initializer.is_none() && property.facts == 0,
                )
            }
            NodeData::PropertySignatureDeclaration(property)
                if record.kind == SyntaxKind::PropertySignature =>
            {
                (
                    property.name,
                    Some(property.type_),
                    property.postfix_token,
                    property.symbol,
                    property.modifiers.as_ref(),
                    missing_signature_initializer(store, host, declaration, property.initializer),
                )
            }
            _ => return false,
        };
    let Some(type_node) = type_node else {
        return false;
    };
    let name = NodeRef::new(declaration.arena, declaration.file, name);
    let Ok(name_record) = preflight_node(store, host, name) else {
        return false;
    };
    let NodeData::ComputedPropertyName(computed) = &name_record.data else {
        return false;
    };
    let expression = NodeRef::new(name.arena, name.file, computed.expression);
    let Ok(expression_record) = preflight_node(store, host, expression) else {
        return false;
    };
    let NodeData::PropertyAccessExpression(access) = &expression_record.data else {
        return false;
    };
    let object = NodeRef::new(expression.arena, expression.file, access.expression);
    let property_name = NodeRef::new(expression.arena, expression.file, access.name);
    let (Ok(object_record), Ok(property_name_record)) = (
        preflight_node(store, host, object),
        preflight_node(store, host, property_name),
    ) else {
        return false;
    };
    let (NodeData::Identifier(object_identifier), NodeData::Identifier(property_identifier)) =
        (&object_record.data, &property_name_record.data)
    else {
        return false;
    };
    let type_node = NodeRef::new(declaration.arena, declaration.file, type_node);
    let Ok(type_record) = preflight_node(store, host, type_node) else {
        return false;
    };
    let Some(bound) = host.bound_file(declaration) else {
        return false;
    };
    let Some(symbol) = bound
        .symbol(declaration)
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(symbol_record) = store.symbol(symbol) else {
        return false;
    };
    let Some(value_declaration) = store
        .symbol(owner)
        .and_then(ts_binder::semantic::Symbol::value_declaration)
    else {
        return false;
    };
    let Some(owner_name) = store.symbol(owner).and_then(|owner| owner.name().as_utf8()) else {
        return false;
    };
    let annotation_name = match owner_name {
        "Math" => "Math",
        "Symbol" => "SymbolConstructor",
        _ => return false,
    };

    bound.source_facts().is_some_and(|facts| {
        facts.is_declaration_file()
            && facts.is_default_library()
            && !facts.is_javascript_file()
            && !facts.is_external_or_common_js_module()
    }) && authenticated_global_builtin_value_declaration(
        store,
        host,
        owner,
        value_declaration,
        owner_name,
        annotation_name,
    ) && record.flags.0 == 0
        && postfix_token.is_none()
        && ast_symbol.is_none()
        && valid_initializer
        && preflight_readonly_modifier(store, host, declaration, modifiers) == Some(true)
        && name_record.kind == SyntaxKind::ComputedPropertyName
        && name_record.flags.0 == 0
        && name_record.parent == Some(declaration.node)
        && computed.facts == 0
        && expression_record.kind == SyntaxKind::PropertyAccessExpression
        && expression_record.flags.0 == 0
        && expression_record.parent == Some(name.node)
        && access.flow_node.is_none()
        && access.question_dot_token.is_none()
        && access.facts == 0
        && object_record.kind == SyntaxKind::Identifier
        && object_record.flags.0 == 0
        && object_record.parent == Some(expression.node)
        && object_identifier.flow_node.is_none()
        && object_identifier.text == "Symbol"
        && property_name_record.kind == SyntaxKind::Identifier
        && property_name_record.flags.0 == 0
        && property_name_record.parent == Some(expression.node)
        && property_identifier.flow_node.is_none()
        && property_identifier.text == "toStringTag"
        && type_record.kind == SyntaxKind::StringKeyword
        && type_record.flags.0 == 0
        && type_record.parent == Some(declaration.node)
        && symbol_record.flags() == SymbolFlags::PROPERTY
        && symbol_record.check_flags() == CheckFlags::NONE
        && symbol_record.name() == InternalSymbolName::Computed.as_ref()
        && symbol_record.declarations() == Some(&[declaration])
        && symbol_record.value_declaration() == Some(declaration)
        && symbol_record.members().is_none()
        && symbol_record.exports().is_none()
        && symbol_record.export_symbol().is_none()
        && symbol_record
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            == Some(owner)
        && store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| store.symbol_table(members))
            .is_some_and(|members| members.iter().all(|(_, member)| member != symbol))
}

fn authenticated_default_library_builtin_symbol_method(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    declaration: NodeRef,
) -> bool {
    let Some(owner_record) = store.symbol(owner) else {
        return false;
    };
    let Some(owner_name) = owner_record.name().as_utf8() else {
        return false;
    };
    let (annotation_name, member_name, parameter_count) = match owner_name {
        "Symbol" => ("SymbolConstructor", "toPrimitive", 1),
        "String" => ("StringConstructor", "iterator", 0),
        _ => return false,
    };
    let Some(value_declaration) = owner_record.value_declaration() else {
        return false;
    };
    if !authenticated_global_builtin_value_declaration(
        store,
        host,
        owner,
        value_declaration,
        owner_name,
        annotation_name,
    ) {
        return false;
    }
    let Ok(record) = preflight_node(store, host, declaration) else {
        return false;
    };
    let NodeData::MethodSignatureDeclaration(method) = &record.data else {
        return false;
    };
    let name = NodeRef::new(declaration.arena, declaration.file, method.name);
    let Ok(name_record) = preflight_node(store, host, name) else {
        return false;
    };
    let NodeData::ComputedPropertyName(computed) = &name_record.data else {
        return false;
    };
    let expression = NodeRef::new(name.arena, name.file, computed.expression);
    let Ok(expression_record) = preflight_node(store, host, expression) else {
        return false;
    };
    let NodeData::PropertyAccessExpression(access) = &expression_record.data else {
        return false;
    };
    let object = NodeRef::new(expression.arena, expression.file, access.expression);
    let member = NodeRef::new(expression.arena, expression.file, access.name);
    let (Ok(object_record), Ok(member_record)) = (
        preflight_node(store, host, object),
        preflight_node(store, host, member),
    ) else {
        return false;
    };
    let (NodeData::Identifier(object_identifier), NodeData::Identifier(member_identifier)) =
        (&object_record.data, &member_record.data)
    else {
        return false;
    };
    let Some(return_type) = method
        .type_
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
    else {
        return false;
    };
    let Ok(return_record) = preflight_node(store, host, return_type) else {
        return false;
    };
    let Some(bound) = host.bound_file(declaration) else {
        return false;
    };
    let Some(symbol) = bound
        .symbol(declaration)
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(symbol_record) = store.symbol(symbol) else {
        return false;
    };
    let locals = bound
        .locals(declaration)
        .and_then(|locals| store.symbol_table(locals));
    let valid_parameter = match (owner_name, method.parameters.nodes.as_slice()) {
        ("Symbol", [parameter]) => {
            let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
            let Ok((planned, rest, optional)) = plan_interface_method_parameter(
                store,
                host,
                declaration,
                parameter,
                &method.parameters,
                false,
            ) else {
                return false;
            };
            !rest
                && !optional
                && store.source_node_kind(planned.type_node) == Some(SyntaxKind::StringKeyword)
                && store
                    .symbol(planned.symbol)
                    .is_some_and(|parameter| parameter.name().as_utf8() == Some("hint"))
                && locals.is_some_and(|locals| {
                    locals.len() == 1 && locals.get_source("hint") == Some(planned.symbol)
                })
        }
        ("String", []) => locals.is_none_or(ts_binder::semantic::SymbolTable::is_empty),
        _ => false,
    };
    let valid_return = match (owner_name, &return_record.data) {
        ("Symbol", NodeData::KeywordTypeNode(_)) => return_record.kind == SyntaxKind::SymbolKeyword,
        ("String", NodeData::TypeReferenceNode(reference))
            if return_record.kind == SyntaxKind::TypeReference =>
        {
            let reference_name =
                NodeRef::new(return_type.arena, return_type.file, reference.type_name);
            let Ok(reference_name_record) = preflight_node(store, host, reference_name) else {
                return false;
            };
            let NodeData::Identifier(identifier) = &reference_name_record.data else {
                return false;
            };
            let Some(arguments) = reference.type_arguments.as_ref() else {
                return false;
            };
            let [argument] = arguments.nodes.as_slice() else {
                return false;
            };
            let argument = NodeRef::new(return_type.arena, return_type.file, *argument);
            let Ok(argument_record) = preflight_node(store, host, argument) else {
                return false;
            };
            reference_name_record.kind == SyntaxKind::Identifier
                && reference_name_record.flags.0 == 0
                && reference_name_record.parent == Some(return_type.node)
                && identifier.flow_node.is_none()
                && identifier.text == "StringIterator"
                && !arguments.has_trailing_comma
                && argument_record.kind == SyntaxKind::StringKeyword
                && argument_record.flags.0 == 0
                && argument_record.parent == Some(return_type.node)
        }
        _ => false,
    };

    bound.source_facts().is_some_and(|facts| {
        facts.is_declaration_file()
            && facts.is_default_library()
            && !facts.is_javascript_file()
            && !facts.is_external_or_common_js_module()
    }) && record.kind == SyntaxKind::MethodSignature
        && record.flags.0 == 0
        && method.full_signature.is_none()
        && method.next_container.is_none()
        && method.postfix_token.is_none()
        && method.symbol.is_none()
        && method.type_parameters.is_none()
        && method.modifiers.is_none()
        && !method.parameters.has_trailing_comma
        && method.parameters.nodes.len() == parameter_count
        && valid_parameter
        && valid_return
        && return_record.flags.0 == 0
        && return_record.parent == Some(declaration.node)
        && name_record.kind == SyntaxKind::ComputedPropertyName
        && name_record.flags.0 == 0
        && name_record.parent == Some(declaration.node)
        && computed.facts == 0
        && expression_record.kind == SyntaxKind::PropertyAccessExpression
        && expression_record.flags.0 == 0
        && expression_record.parent == Some(name.node)
        && access.flow_node.is_none()
        && access.question_dot_token.is_none()
        && access.facts == 0
        && object_record.kind == SyntaxKind::Identifier
        && object_record.flags.0 == 0
        && object_record.parent == Some(expression.node)
        && object_identifier.flow_node.is_none()
        && object_identifier.text == "Symbol"
        && member_record.kind == SyntaxKind::Identifier
        && member_record.flags.0 == 0
        && member_record.parent == Some(expression.node)
        && member_identifier.flow_node.is_none()
        && member_identifier.text == member_name
        && symbol_record.flags() == SymbolFlags::METHOD
        && symbol_record.check_flags() == CheckFlags::NONE
        && symbol_record.name() == InternalSymbolName::Computed.as_ref()
        && symbol_record.declarations() == Some(&[declaration])
        && symbol_record.value_declaration() == Some(declaration)
        && symbol_record.members().is_none()
        && symbol_record.exports().is_none()
        && symbol_record.export_symbol().is_none()
        && symbol_record
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            == Some(owner)
        && owner_record
            .members()
            .and_then(|members| store.symbol_table(members))
            .is_some_and(|members| members.iter().all(|(_, member)| member != symbol))
}

/// Combines reopened interface clauses without duplicating authenticated bases.
fn merge_interface_heritage(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    heritage: &mut Option<DirectInterfaceHeritagePlan>,
    planned: DirectInterfaceHeritagePlan,
    maximum_bases: usize,
) -> Result<(), PropertyObjectError> {
    let Some(existing) = heritage.as_mut() else {
        *heritage = Some(planned);
        return Ok(());
    };

    for base in planned.bases {
        if let Some(previous) = existing
            .bases
            .iter()
            .find(|previous| previous.symbol == base.symbol)
        {
            if previous.kind != base.kind
                || previous.type_arguments.len() != base.type_arguments.len()
                || previous
                    .type_arguments
                    .iter()
                    .zip(&base.type_arguments)
                    .any(|(previous, current)| {
                        !equivalent_merged_property_annotations(store, host, *previous, *current)
                    })
            {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: base.node,
                    kind: SyntaxKind::ExpressionWithTypeArguments,
                });
            }
            continue;
        }
        if existing.bases.len() >= maximum_bases {
            return Err(PropertyObjectError::UnsupportedMember {
                node: planned.clause,
                kind: SyntaxKind::HeritageClause,
            });
        }
        existing.bases.push(base);
    }
    Ok(())
}

fn matching_planned_interface_method_contract(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    first: &PlannedProperty,
    second: &PlannedProperty,
) -> bool {
    let Some(first_record) = store.symbol(first.symbol) else {
        return false;
    };
    let Some(second_record) = store.symbol(second.symbol) else {
        return false;
    };
    let Some(first_declarations) = first_record.declarations() else {
        return false;
    };
    let Some(second_declarations) = second_record.declarations() else {
        return false;
    };
    if first_record.flags() != SymbolFlags::METHOD
        || second_record.flags() != SymbolFlags::METHOD
        || first_declarations.len() != second_declarations.len()
    {
        return false;
    }

    first_declarations.iter().zip(second_declarations).all(
        |(first_declaration, second_declaration)| {
            let first_parent = match store.source_node_parent(*first_declaration) {
                Some(SourceNodeParent::Parent(parent)) => parent,
                Some(SourceNodeParent::Root) | None => return false,
            };
            let second_parent = match store.source_node_parent(*second_declaration) {
                Some(SourceNodeParent::Parent(parent)) => parent,
                Some(SourceNodeParent::Root) | None => return false,
            };
            let Some(first_owner) = store.get_parent_of_symbol(first.symbol) else {
                return false;
            };
            let Some(second_owner) = store.get_parent_of_symbol(second.symbol) else {
                return false;
            };
            let Ok(first_method) =
                plan_interface_method(store, host, first_parent, first_owner, *first_declaration)
            else {
                return false;
            };
            let Ok(second_method) = plan_interface_method(
                store,
                host,
                second_parent,
                second_owner,
                *second_declaration,
            ) else {
                return false;
            };
            first_method.flags == second_method.flags
                && first_method.type_parameters.len() == second_method.type_parameters.len()
                && first_method.parameters.len() == second_method.parameters.len()
                && equivalent_merged_property_annotations(
                    store,
                    host,
                    first_method.return_type,
                    second_method.return_type,
                )
                && first_method
                    .parameters
                    .iter()
                    .zip(&second_method.parameters)
                    .all(|(first_parameter, second_parameter)| {
                        equivalent_merged_property_annotations(
                            store,
                            host,
                            first_parameter.type_node,
                            second_parameter.type_node,
                        )
                    })
        },
    )
}

fn collect_interface_property_heritage(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &PropertyObjectPlan,
    properties: &mut Vec<PlannedProperty>,
    active: &mut HashSet<SemanticSymbolId>,
    depth: usize,
) -> Result<(), PropertyObjectError> {
    if depth >= MAX_INTERFACE_PROPERTY_HERITAGE_DEPTH || !active.insert(plan.symbol) {
        return Err(PropertyObjectError::UnsupportedMember {
            node: plan.node,
            kind: SyntaxKind::InterfaceDeclaration,
        });
    }

    for property in &plan.properties {
        if !properties
            .iter()
            .any(|inherited| inherited.name == property.name)
        {
            properties.push(property.clone());
        }
    }

    if let Some(heritage) = plan.heritage.as_ref() {
        if !matches!(heritage.bases.as_slice(), [_] | [_, _]) {
            return Err(PropertyObjectError::UnsupportedMember {
                node: heritage.clause,
                kind: SyntaxKind::HeritageClause,
            });
        }
        for base in &heritage.bases {
            let base_plan = plan_interface(store, host, base.symbol)?;
            if !base_plan.indexes.is_empty() || !base_plan.call_signatures.is_empty() {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: base.node,
                    kind: SyntaxKind::ExpressionWithTypeArguments,
                });
            }
            collect_interface_property_heritage(
                store,
                host,
                &base_plan,
                properties,
                active,
                depth + 1,
            )?;
        }
    }

    assert!(active.remove(&plan.symbol));
    Ok(())
}

/// Authenticates one source-only `interface Array<T> { (): any[] }` contribution.
///
/// Global initialization has already merged and created the generic Array
/// target. This proof inspects only the current declaration and existing
/// identities; it does not resolve unrelated library members or publish a
/// callable signature.
pub(super) fn plan_global_array_call_augmentation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<Option<GlobalArrayCallAugmentationPlan>, PropertyObjectError> {
    let canonical = store
        .get_merged_symbol(symbol)
        .ok_or(PropertyObjectError::InvalidInterfaceSymbol(symbol))?;
    let invalid = || PropertyObjectError::InvalidInterface {
        declaration,
        symbol: canonical,
    };
    let record = preflight_node(store, host, declaration).map_err(|_| invalid())?;
    let NodeData::InterfaceDeclaration(interface) = &record.data else {
        return Err(invalid());
    };
    let name = NodeRef::new(declaration.arena, declaration.file, interface.name);
    let name_record = preflight_node(store, host, name).map_err(|_| invalid())?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invalid());
    };
    if identifier.text != "Array" {
        return Ok(None);
    }
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    let global = store
        .symbol_table(bootstrap.globals)
        .and_then(|globals| globals.get_source("Array"))
        .and_then(|global| store.get_merged_symbol(global));
    if global != Some(canonical) {
        return Ok(None);
    }
    let bound = host.bound_file(declaration).ok_or_else(invalid)?;
    let facts = bound.source_facts().ok_or_else(invalid)?;
    if facts.is_default_library()
        || facts.is_declaration_file()
        || facts.is_javascript_file()
        || facts.is_external_or_common_js_module()
    {
        return Ok(None);
    }
    if interface.members.nodes.len() == 1
        && store.source_node_kind(NodeRef::new(
            declaration.arena,
            declaration.file,
            interface.members.nodes[0],
        )) != Some(SyntaxKind::CallSignature)
    {
        return Ok(None);
    }

    let owner = store.symbol(canonical).ok_or_else(invalid)?;
    let allowed_flags =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    let Some(owner_declarations) = owner.declarations() else {
        return Err(invalid());
    };
    let has_library_owner = owner_declarations.iter().any(|candidate| {
        candidate.file != declaration.file
            && host
                .bound_file(*candidate)
                .and_then(ts_binder::BoundFile::source_facts)
                .is_some_and(ts_binder::CanonicalSourceFileFacts::is_default_library)
    });
    if !has_library_owner {
        return Ok(None);
    }
    let Some(members) = owner
        .members()
        .and_then(|members| store.symbol_table(members))
    else {
        return Err(invalid());
    };
    let Some(parameters) = interface.type_parameters.as_ref() else {
        return Err(invalid());
    };
    let source = record
        .parent
        .map(|parent| NodeRef::new(declaration.arena, declaration.file, parent))
        .ok_or_else(invalid)?;
    let source_record = preflight_node(store, host, source).map_err(|_| invalid())?;
    let NodeData::SourceFile(source_data) = &source_record.data else {
        return Err(invalid());
    };
    if record.kind != SyntaxKind::InterfaceDeclaration
        || record.flags.0 != 0
        || !host.symbol_matches(store, declaration, canonical)
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || interface.flow_node.is_some()
        || interface.local_symbol.is_some()
        || interface.symbol.is_some()
        || interface.modifiers.is_some()
        || interface.heritage_clauses.is_some()
        || interface.members.has_trailing_comma
        || interface.members.nodes.len() != 1
        || parameters.has_trailing_comma
        || parameters.nodes.len() != 1
        || source_record.kind != SyntaxKind::SourceFile
        || source_record.parent.is_some()
        || bound.source_file() != source
        || source_data
            .statements
            .nodes
            .iter()
            .filter(|candidate| **candidate == declaration.node)
            .count()
            != 1
        || owner.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
        || owner.flags().without(allowed_flags) != SymbolFlags::NONE
        || owner.check_flags() != CheckFlags::NONE
        || owner.name().as_utf8() != Some("Array")
        || owner.parent().is_some()
        || owner.exports().is_some()
        || owner.export_symbol().is_some()
        || !owner_declarations.contains(&declaration)
    {
        return Err(invalid());
    }

    let target = store
        .declared_type_links(canonical)
        .and_then(|links| links.declared_type)
        .ok_or_else(invalid)?;
    let target_record = store.type_payload(target).ok_or_else(invalid)?;
    let TypeData::Interface(target_interface) = target_record.data() else {
        return Err(invalid());
    };
    let reference = validate_direct_generic_reference(store, target).map_err(|_| invalid())?;
    let [parameter_type] = reference.type_arguments.as_slice() else {
        return Err(invalid());
    };
    let shared_parameter =
        cached_ordinary_type_parameter_owner(store, *parameter_type).ok_or_else(invalid)?;
    if reference.target != target
        || target_record.flags() != TypeFlags::OBJECT
        || !target_record
            .object_flags()
            .contains(ObjectFlags::INTERFACE | ObjectFlags::REFERENCE)
        || target_record.symbol() != Some(canonical)
        || target_record.alias().is_some()
        || target_interface.outer_type_parameter_count != 0
        || target_interface.declared_members_resolved
        || target_interface.reference.object.structured != StructuredTypeData::default()
    {
        return Err(invalid());
    }

    let parameter = NodeRef::new(declaration.arena, declaration.file, parameters.nodes[0]);
    let parameter_record = preflight_node(store, host, parameter).map_err(|_| invalid())?;
    let NodeData::TypeParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Err(invalid());
    };
    let parameter_name = NodeRef::new(parameter.arena, parameter.file, parameter_data.name);
    let parameter_name_record =
        preflight_node(store, host, parameter_name).map_err(|_| invalid())?;
    let NodeData::Identifier(parameter_identifier) = &parameter_name_record.data else {
        return Err(invalid());
    };
    let parameter_symbol = bound
        .symbol(parameter)
        .and_then(|parameter| store.get_merged_symbol(parameter))
        .ok_or_else(invalid)?;
    let parameter_symbol_record = store.symbol(parameter_symbol).ok_or_else(invalid)?;
    if parameter_record.kind != SyntaxKind::TypeParameter
        || parameter_record.flags.0 != 0
        || parameter_record.parent != Some(declaration.node)
        || parameter_data.constraint.is_some()
        || parameter_data.default_type.is_some()
        || parameter_data.expression.is_some()
        || parameter_data.symbol.is_some()
        || parameter_data.modifiers.is_some()
        || parameter_name_record.kind != SyntaxKind::Identifier
        || parameter_name_record.flags.0 != 0
        || parameter_name_record.parent != Some(parameter.node)
        || parameter_identifier.flow_node.is_some()
        || parameter_identifier.text != "T"
        || parameter_symbol != shared_parameter
        || !host.symbol_matches(store, parameter, parameter_symbol)
        || !parameter_symbol_record
            .flags()
            .contains(SymbolFlags::TYPE_PARAMETER)
        || parameter_symbol_record
            .flags()
            .without(SymbolFlags::TYPE_PARAMETER | SymbolFlags::TRANSIENT)
            != SymbolFlags::NONE
        || parameter_symbol_record.check_flags() != CheckFlags::NONE
        || parameter_symbol_record.name().as_utf8() != Some("T")
        || parameter_symbol_record
            .declarations()
            .is_none_or(|declarations| !declarations.contains(&parameter))
        || parameter_symbol_record.value_declaration().is_some()
        || parameter_symbol_record.members().is_some()
        || parameter_symbol_record.exports().is_some()
        || parameter_symbol_record.export_symbol().is_some()
        || store.get_parent_of_symbol(parameter_symbol) != Some(canonical)
        || members
            .get_source("T")
            .and_then(|parameter| store.get_merged_symbol(parameter))
            != Some(parameter_symbol)
    {
        return Err(invalid());
    }

    let signature = NodeRef::new(
        declaration.arena,
        declaration.file,
        interface.members.nodes[0],
    );
    let signature_record = preflight_node(store, host, signature).map_err(|_| invalid())?;
    let NodeData::CallSignatureDeclaration(call) = &signature_record.data else {
        return Err(invalid());
    };
    let call_symbol = bound
        .symbol(signature)
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(invalid)?;
    let call_record = store.symbol(call_symbol).ok_or_else(invalid)?;
    if signature_record.kind != SyntaxKind::CallSignature
        || signature_record.flags.0 != 0
        || signature_record.parent != Some(declaration.node)
        || call.full_signature.is_some()
        || call.next_container.is_some()
        || call.symbol.is_some()
        || call.type_parameters.is_some()
        || call.parameters.has_trailing_comma
        || !call.parameters.nodes.is_empty()
        || call_record.flags() != SymbolFlags::SIGNATURE
        || call_record.check_flags() != CheckFlags::NONE
        || call_record.name() != InternalSymbolName::Call.as_ref()
        || call_record.declarations() != Some(&[signature])
        || call_record.value_declaration().is_some()
        || call_record.members().is_some()
        || call_record.exports().is_some()
        || call_record.export_symbol().is_some()
        || call_record
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(canonical)
        || members.get(InternalSymbolName::Call.as_ref()) != Some(call_symbol)
        || store
            .signature_links(signature)
            .is_some_and(|links| links != &SignatureLinks::default())
        || bound
            .locals(signature)
            .and_then(|locals| store.symbol_table(locals))
            .is_some_and(|locals| !locals.is_empty())
    {
        return Err(invalid());
    }

    let return_type = call
        .type_
        .map(|type_| NodeRef::new(signature.arena, signature.file, type_))
        .ok_or_else(invalid)?;
    let return_record = preflight_node(store, host, return_type).map_err(|_| invalid())?;
    let NodeData::ArrayTypeNode(array) = &return_record.data else {
        return Err(invalid());
    };
    let element = NodeRef::new(return_type.arena, return_type.file, array.element_type);
    let element_record = preflight_node(store, host, element).map_err(|_| invalid())?;
    let TypeCacheState::Allocated(instantiations) =
        &target_interface.reference.object.instantiations
    else {
        return Err(invalid());
    };
    let any_array_type = instantiations
        .get(&type_list_key(&[bootstrap.any_type]))
        .copied()
        .ok_or_else(invalid)?;
    let any_reference =
        validate_direct_generic_reference(store, any_array_type).map_err(|_| invalid())?;
    if return_record.kind != SyntaxKind::ArrayType
        || return_record.flags.0 != 0
        || return_record.parent != Some(signature.node)
        || return_record.range.start < call.parameters.range.end
        || return_record.range.end > signature_record.range.end
        || element_record.kind != SyntaxKind::AnyKeyword
        || !matches!(element_record.data, NodeData::KeywordTypeNode(_))
        || element_record.flags.0 != 0
        || element_record.parent != Some(return_type.node)
        || element_record.range.start != return_record.range.start
        || element_record.range.end > return_record.range.end
        || any_reference.target != target
        || any_reference.type_arguments.as_slice() != [bootstrap.any_type]
        || store.type_node_links(element).is_some_and(|links| {
            links.outer_type_parameters.is_some()
                || links
                    .resolved_type
                    .is_some_and(|type_| type_ != bootstrap.any_type)
        })
        || store.type_node_links(return_type).is_some_and(|links| {
            links.outer_type_parameters.is_some()
                || links
                    .resolved_type
                    .is_some_and(|type_| type_ != any_array_type)
        })
    {
        return Err(invalid());
    }

    Ok(Some(GlobalArrayCallAugmentationPlan {
        declaration,
        symbol: canonical,
        target,
        signature,
        return_type,
        any_array_type,
    }))
}

/// Authenticates a source property augmentation without resolving library members.
#[allow(clippy::too_many_lines)] // Declaration, merged parameter, and property form one proof.
pub(super) fn plan_global_array_property_augmentation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<Option<GlobalArrayPropertyAugmentationPlan>, PropertyObjectError> {
    let canonical = store
        .get_merged_symbol(symbol)
        .ok_or(PropertyObjectError::InvalidInterfaceSymbol(symbol))?;
    let invalid = || PropertyObjectError::InvalidInterface {
        declaration,
        symbol: canonical,
    };
    let record = preflight_node(store, host, declaration).map_err(|_| invalid())?;
    let NodeData::InterfaceDeclaration(interface) = &record.data else {
        return Err(invalid());
    };
    let name = NodeRef::new(declaration.arena, declaration.file, interface.name);
    let name_record = preflight_node(store, host, name).map_err(|_| invalid())?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invalid());
    };
    if identifier.text != "Array" {
        return Ok(None);
    }
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    let global = store
        .symbol_table(bootstrap.globals)
        .and_then(|globals| globals.get_source("Array"))
        .and_then(|owner| store.get_merged_symbol(owner));
    if global != Some(canonical) {
        return Ok(None);
    }
    let bound = host.bound_file(declaration).ok_or_else(invalid)?;
    let facts = bound.source_facts().ok_or_else(invalid)?;
    if facts.is_default_library()
        || facts.is_declaration_file()
        || facts.is_javascript_file()
        || facts.is_external_or_common_js_module()
    {
        return Ok(None);
    }
    let [member] = interface.members.nodes.as_slice() else {
        return Ok(None);
    };
    let member = NodeRef::new(declaration.arena, declaration.file, *member);
    let member_record = preflight_node(store, host, member).map_err(|_| invalid())?;
    let (property_name, annotation, optional, modifiers) = match &member_record.data {
        NodeData::PropertyDeclaration(property)
            if member_record.kind == SyntaxKind::PropertyDeclaration
                && property.initializer.is_none() =>
        {
            (
                property.name,
                property.type_.ok_or_else(invalid)?,
                property.postfix_token,
                property.modifiers.as_ref(),
            )
        }
        NodeData::PropertySignatureDeclaration(property)
            if member_record.kind == SyntaxKind::PropertySignature =>
        {
            (
                property.name,
                property.type_,
                property.postfix_token,
                property.modifiers.as_ref(),
            )
        }
        _ => return Ok(None),
    };

    let owner = store.symbol(canonical).ok_or_else(invalid)?;
    let allowed_flags =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    let declarations = owner.declarations().ok_or_else(invalid)?;
    let has_library_owner = declarations.iter().any(|candidate| {
        candidate.file != declaration.file
            && host
                .bound_file(*candidate)
                .and_then(ts_binder::BoundFile::source_facts)
                .is_some_and(ts_binder::CanonicalSourceFileFacts::is_default_library)
    });
    if !has_library_owner {
        return Ok(None);
    }
    let parameters = interface.type_parameters.as_ref().ok_or_else(invalid)?;
    let [parameter] = parameters.nodes.as_slice() else {
        return Err(invalid());
    };
    let members = owner.members().ok_or_else(invalid)?;
    let table = store.symbol_table(members).ok_or_else(invalid)?;
    if record.kind != SyntaxKind::InterfaceDeclaration
        || record.flags.0 != 0
        || !host.symbol_matches(store, declaration, canonical)
        || name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(declaration.node)
        || interface.flow_node.is_some()
        || interface.local_symbol.is_some()
        || interface.symbol.is_some()
        || interface.modifiers.is_some()
        || interface.heritage_clauses.is_some()
        || interface.members.has_trailing_comma
        || parameters.has_trailing_comma
        || owner.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
        || owner.flags().without(allowed_flags) != SymbolFlags::NONE
        || owner.check_flags() != CheckFlags::NONE
        || owner.name().as_utf8() != Some("Array")
        || owner.parent().is_some()
        || owner.exports().is_some()
        || owner.export_symbol().is_some()
        || !declarations.contains(&declaration)
    {
        return Err(invalid());
    }

    let target = store
        .declared_type_links(canonical)
        .and_then(|links| links.declared_type)
        .ok_or_else(invalid)?;
    let target_record = store.type_payload(target).ok_or_else(invalid)?;
    let TypeData::Interface(target_interface) = target_record.data() else {
        return Err(invalid());
    };
    let reference = validate_direct_generic_reference(store, target).map_err(|_| invalid())?;
    let [parameter_type] = reference.type_arguments.as_slice() else {
        return Err(invalid());
    };
    let parameter_symbol =
        cached_ordinary_type_parameter_owner(store, *parameter_type).ok_or_else(invalid)?;
    let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
    let parameter_record = preflight_node(store, host, parameter).map_err(|_| invalid())?;
    let NodeData::TypeParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Err(invalid());
    };
    let parameter_name = NodeRef::new(parameter.arena, parameter.file, parameter_data.name);
    let parameter_name_record =
        preflight_node(store, host, parameter_name).map_err(|_| invalid())?;
    let NodeData::Identifier(parameter_identifier) = &parameter_name_record.data else {
        return Err(invalid());
    };
    if reference.target != target
        || target_record.flags() != TypeFlags::OBJECT
        || !target_record
            .object_flags()
            .contains(ObjectFlags::INTERFACE | ObjectFlags::REFERENCE)
        || target_record.symbol() != Some(canonical)
        || target_record.alias().is_some()
        || target_interface.outer_type_parameter_count != 0
        || target_interface.declared_members_resolved
        || target_interface.reference.object.structured != StructuredTypeData::default()
        || parameter_record.kind != SyntaxKind::TypeParameter
        || parameter_record.parent != Some(declaration.node)
        || parameter_data.constraint.is_some()
        || parameter_data.default_type.is_some()
        || parameter_data.expression.is_some()
        || parameter_data.symbol.is_some()
        || parameter_data.modifiers.is_some()
        || parameter_name_record.kind != SyntaxKind::Identifier
        || parameter_name_record.parent != Some(parameter.node)
        || parameter_identifier.text != "T"
        || bound
            .symbol(parameter)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(parameter_symbol)
        || table
            .get_source("T")
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(parameter_symbol)
    {
        return Err(invalid());
    }

    let name_node = NodeRef::new(member.arena, member.file, property_name);
    let property_name_record = preflight_node(store, host, name_node).map_err(|_| invalid())?;
    let NodeData::Identifier(property_identifier) = &property_name_record.data else {
        return Err(invalid());
    };
    let annotation = NodeRef::new(member.arena, member.file, annotation);
    let annotation_record = preflight_node(store, host, annotation).map_err(|_| invalid())?;
    let property_symbol = bound
        .symbol(member)
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(invalid)?;
    let property_record = store.symbol(property_symbol).ok_or_else(invalid)?;
    let optional = optional.is_some();
    let expected_flags = SymbolFlags::PROPERTY
        | if optional {
            SymbolFlags::OPTIONAL
        } else {
            SymbolFlags::NONE
        };
    let readonly =
        preflight_readonly_modifier(store, host, member, modifiers).ok_or_else(invalid)?;
    if member_record.flags.0 != 0
        || member_record.parent != Some(declaration.node)
        || property_name_record.kind != SyntaxKind::Identifier
        || property_name_record.parent != Some(member.node)
        || property_identifier.flow_node.is_some()
        || property_identifier.text.is_empty()
        || annotation_record.parent != Some(member.node)
        || property_record.flags() != expected_flags
        || property_record.check_flags() != CheckFlags::NONE
            && property_record.check_flags() != source_property_check_flags(readonly)
        || property_record.name().as_utf8() != Some(property_identifier.text.as_str())
        || property_record.declarations() != Some(&[member])
        || property_record.value_declaration() != Some(member)
        || property_record.members().is_some()
        || property_record.exports().is_some()
        || property_record.export_symbol().is_some()
        || property_record
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(canonical)
        || table
            .get_source(&property_identifier.text)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(property_symbol)
        || store
            .value_symbol_links(property_symbol)
            .is_some_and(|links| {
                links
                    != &(ValueSymbolLinks {
                        resolved_type: links.resolved_type,
                        ..ValueSymbolLinks::default()
                    })
                    || links
                        .resolved_type
                        .is_some_and(|type_| store.type_payload(type_).is_none())
            })
    {
        return Err(invalid());
    }

    Ok(Some(GlobalArrayPropertyAugmentationPlan {
        declaration,
        symbol: canonical,
        target,
        property: PlannedProperty {
            declaration: member,
            symbol: property_symbol,
            name_node,
            type_node: annotation,
            optional,
            readonly,
            name: property_identifier.text.clone(),
        },
    }))
}

fn global_array_concat_type_parameter_reference(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    parameter_name: &str,
) -> bool {
    let Ok(record) = preflight_node(store, host, node) else {
        return false;
    };
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return false;
    };
    let name = NodeRef::new(node.arena, node.file, reference.type_name);
    let Ok(name_record) = preflight_node(store, host, name) else {
        return false;
    };
    let NodeData::Identifier(identifier) = &name_record.data else {
        return false;
    };
    record.kind == SyntaxKind::TypeReference
        && record.flags.0 == 0
        && reference.type_arguments.is_none()
        && name_record.kind == SyntaxKind::Identifier
        && name_record.flags.0 == 0
        && name_record.parent == Some(node.node)
        && identifier.flow_node.is_none()
        && identifier.text == parameter_name
}

fn global_array_concat_reference(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    parameter_name: &str,
) -> bool {
    let Ok(record) = preflight_node(store, host, node) else {
        return false;
    };
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return false;
    };
    let Some(arguments) = reference.type_arguments.as_ref() else {
        return false;
    };
    let [argument] = arguments.nodes.as_slice() else {
        return false;
    };
    let name = NodeRef::new(node.arena, node.file, reference.type_name);
    let Ok(name_record) = preflight_node(store, host, name) else {
        return false;
    };
    let NodeData::Identifier(identifier) = &name_record.data else {
        return false;
    };
    let argument = NodeRef::new(node.arena, node.file, *argument);
    let Ok(argument_record) = preflight_node(store, host, argument) else {
        return false;
    };
    record.kind == SyntaxKind::TypeReference
        && record.flags.0 == 0
        && !arguments.has_trailing_comma
        && name_record.kind == SyntaxKind::Identifier
        && name_record.flags.0 == 0
        && name_record.parent == Some(node.node)
        && identifier.flow_node.is_none()
        && identifier.text == "ConcatArray"
        && argument_record.parent == Some(node.node)
        && global_array_concat_type_parameter_reference(store, host, argument, parameter_name)
}

fn plan_global_array_concat_overload(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    method: SemanticSymbolId,
    declaration: NodeRef,
    parameter_name: &str,
) -> Result<GlobalArrayConcatOverloadPlan, PropertyObjectError> {
    let unsupported = || PropertyObjectError::UnsupportedMember {
        node: declaration,
        kind: SyntaxKind::MethodSignature,
    };
    let record = preflight_node(store, host, declaration).map_err(|_| unsupported())?;
    let NodeData::MethodSignatureDeclaration(signature) = &record.data else {
        return Err(unsupported());
    };
    let Some(SourceNodeParent::Parent(interface)) = store.source_node_parent(declaration) else {
        return Err(unsupported());
    };
    let bound = host.bound_file(declaration).ok_or_else(unsupported)?;
    if record.kind != SyntaxKind::MethodSignature
        || record.flags.0 & NODE_FLAG_HAS_ERROR != 0
        || signature.full_signature.is_some()
        || signature.next_container.is_some()
        || signature.postfix_token.is_some()
        || signature.symbol.is_some()
        || signature.type_parameters.is_some()
        || signature.modifiers.is_some()
        || signature.parameters.has_trailing_comma
        || store.source_node_kind(interface) != Some(SyntaxKind::InterfaceDeclaration)
        || !host.symbol_matches(store, interface, owner)
        || !host.symbol_matches(store, declaration, method)
        || bound.source_facts().is_none_or(|facts| {
            !facts.is_default_library()
                || !facts.is_declaration_file()
                || facts.is_javascript_file()
                || facts.is_external_or_common_js_module()
        })
    {
        return Err(unsupported());
    }
    let method_name = NodeRef::new(declaration.arena, declaration.file, signature.name);
    let method_name_record = preflight_node(store, host, method_name).map_err(|_| unsupported())?;
    let NodeData::Identifier(identifier) = &method_name_record.data else {
        return Err(unsupported());
    };
    if method_name_record.kind != SyntaxKind::Identifier
        || method_name_record.parent != Some(declaration.node)
        || identifier.text != "concat"
        || identifier.flow_node.is_some()
    {
        return Err(unsupported());
    }

    let return_annotation = signature
        .type_
        .map(|type_| NodeRef::new(declaration.arena, declaration.file, type_))
        .ok_or_else(unsupported)?;
    let return_record =
        preflight_node(store, host, return_annotation).map_err(|_| unsupported())?;
    let NodeData::ArrayTypeNode(return_array) = &return_record.data else {
        return Err(unsupported());
    };
    let return_element = NodeRef::new(
        return_annotation.arena,
        return_annotation.file,
        return_array.element_type,
    );
    let return_element_record =
        preflight_node(store, host, return_element).map_err(|_| unsupported())?;
    if return_record.kind != SyntaxKind::ArrayType
        || return_record.parent != Some(declaration.node)
        || return_element_record.parent != Some(return_annotation.node)
        || !global_array_concat_type_parameter_reference(
            store,
            host,
            return_element,
            parameter_name,
        )
    {
        return Err(unsupported());
    }

    let [parameter] = signature.parameters.nodes.as_slice() else {
        return Err(unsupported());
    };
    let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
    let parameter_record = preflight_node(store, host, parameter).map_err(|_| unsupported())?;
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Err(unsupported());
    };
    let rest = parameter_data
        .dot_dot_dot_token
        .map(|token| NodeRef::new(parameter.arena, parameter.file, token))
        .ok_or_else(unsupported)?;
    let rest_record = preflight_node(store, host, rest).map_err(|_| unsupported())?;
    let parameter_name_node = NodeRef::new(parameter.arena, parameter.file, parameter_data.name);
    let parameter_name_record =
        preflight_node(store, host, parameter_name_node).map_err(|_| unsupported())?;
    let NodeData::Identifier(parameter_identifier) = &parameter_name_record.data else {
        return Err(unsupported());
    };
    let parameter_annotation = parameter_data
        .type_
        .map(|type_| NodeRef::new(parameter.arena, parameter.file, type_))
        .ok_or_else(unsupported)?;
    let annotation_record =
        preflight_node(store, host, parameter_annotation).map_err(|_| unsupported())?;
    let NodeData::ArrayTypeNode(array) = &annotation_record.data else {
        return Err(unsupported());
    };
    if parameter_record.kind != SyntaxKind::Parameter
        || parameter_record.flags.0 != 0
        || parameter_record.parent != Some(declaration.node)
        || parameter_data.initializer.is_some()
        || parameter_data.question_token.is_some()
        || parameter_data.symbol.is_some()
        || parameter_data.modifiers.is_some()
        || parameter_data.facts != 0
        || rest_record.kind != SyntaxKind::DotDotDotToken
        || rest_record.parent != Some(parameter.node)
        || !matches!(rest_record.data, NodeData::Token(_))
        || parameter_name_record.kind != SyntaxKind::Identifier
        || parameter_name_record.parent != Some(parameter.node)
        || parameter_identifier.flow_node.is_some()
        || parameter_identifier.text.is_empty()
        || annotation_record.kind != SyntaxKind::ArrayType
        || annotation_record.parent != Some(parameter.node)
    {
        return Err(unsupported());
    }

    let element = NodeRef::new(
        parameter_annotation.arena,
        parameter_annotation.file,
        array.element_type,
    );
    let element_record = preflight_node(store, host, element).map_err(|_| unsupported())?;
    if element_record.parent != Some(parameter_annotation.node) {
        return Err(unsupported());
    }
    let kind = if global_array_concat_reference(store, host, element, parameter_name) {
        GlobalArrayConcatOverloadKind::Arrays
    } else {
        let NodeData::ParenthesizedTypeNode(parenthesized) = &element_record.data else {
            return Err(unsupported());
        };
        let union = NodeRef::new(element.arena, element.file, parenthesized.type_);
        let union_record = preflight_node(store, host, union).map_err(|_| unsupported())?;
        let NodeData::UnionTypeNode(union_data) = &union_record.data else {
            return Err(unsupported());
        };
        let [value, array] = union_data.types.nodes.as_slice() else {
            return Err(unsupported());
        };
        let value = NodeRef::new(union.arena, union.file, *value);
        let array = NodeRef::new(union.arena, union.file, *array);
        if element_record.kind != SyntaxKind::ParenthesizedType
            || union_record.kind != SyntaxKind::UnionType
            || union_record.parent != Some(element.node)
            || union_data.types.has_trailing_comma
            || store.source_node_parent(value) != Some(SourceNodeParent::Parent(union))
            || store.source_node_parent(array) != Some(SourceNodeParent::Parent(union))
            || !global_array_concat_type_parameter_reference(store, host, value, parameter_name)
            || !global_array_concat_reference(store, host, array, parameter_name)
        {
            return Err(unsupported());
        }
        GlobalArrayConcatOverloadKind::ValuesOrArrays
    };

    let raw_parameter = bound.symbol(parameter).ok_or_else(unsupported)?;
    let parameter_symbol = store
        .get_merged_symbol(raw_parameter)
        .ok_or_else(unsupported)?;
    let symbol_record = store.symbol(parameter_symbol).ok_or_else(unsupported)?;
    let locals = bound
        .locals(declaration)
        .and_then(|locals| store.symbol_table(locals))
        .ok_or_else(unsupported)?;
    if parameter_symbol != raw_parameter
        || symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name().as_utf8() != Some(parameter_identifier.text.as_str())
        || symbol_record.declarations() != Some(&[parameter])
        || symbol_record.value_declaration() != Some(parameter)
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent().is_some()
        || symbol_record.export_symbol().is_some()
        || locals.len() != 1
        || locals.get(symbol_record.name()) != Some(parameter_symbol)
    {
        return Err(unsupported());
    }

    Ok(GlobalArrayConcatOverloadPlan {
        declaration,
        parameter: parameter_symbol,
        parameter_annotation,
        return_annotation,
        kind,
    })
}

fn plan_global_array_concat_method(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    receiver: TypeId,
) -> Result<Option<GlobalArrayConcatPlan>, PropertyObjectError> {
    let Some(array_owner) = store
        .type_payload(global_types.array_type)
        .and_then(TypeRecord::symbol)
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(None);
    };
    let receiver_array = store
        .canonical_array_reference(global_types, receiver)
        .map_err(|_| PropertyObjectError::InvalidCachedInterface {
            symbol: array_owner,
            type_: global_types.array_type,
        })?;
    let Some(receiver_array) = receiver_array else {
        return Ok(None);
    };
    let (target, owner_name) = if receiver_array.readonly {
        (global_types.readonly_array_type, "ReadonlyArray")
    } else {
        (global_types.array_type, "Array")
    };
    let Some(owner) = store
        .type_payload(target)
        .and_then(TypeRecord::symbol)
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(None);
    };
    let invalid = || PropertyObjectError::InvalidCachedInterface {
        symbol: owner,
        type_: target,
    };
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    let globals = store.symbol_table(bootstrap.globals).ok_or_else(invalid)?;
    if globals
        .get_source(owner_name)
        .and_then(|symbol| store.get_merged_symbol(symbol))
        != Some(owner)
    {
        return Err(invalid());
    }
    let owner_record = store.symbol(owner).ok_or_else(invalid)?;
    let target_record = store.type_payload(target).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = target_record.data() else {
        return Err(invalid());
    };
    let Some([parameter]) = interface.reference.resolved_type_arguments.as_deref() else {
        return Err(invalid());
    };
    let type_parameter = *parameter;
    let parameter = cached_ordinary_type_parameter_owner(store, *parameter).ok_or_else(invalid)?;
    let parameter_record = store.symbol(parameter).ok_or_else(invalid)?;
    let parameter_name = parameter_record.name().as_utf8().ok_or_else(invalid)?;
    let allowed_flags =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    if owner_record.flags() & SymbolFlags::TYPE != SymbolFlags::INTERFACE
        || owner_record.flags().without(allowed_flags) != SymbolFlags::NONE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || target_record.flags() != TypeFlags::OBJECT
        || !target_record
            .object_flags()
            .contains(ObjectFlags::INTERFACE)
        || target_record.symbol() != Some(owner)
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(target)
        || store.get_parent_of_symbol(parameter) != Some(owner)
    {
        return Err(invalid());
    }

    let members = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
        .ok_or_else(invalid)?;
    let Some(method) = members
        .get_source("concat")
        .and_then(|method| store.get_merged_symbol(method))
    else {
        return Ok(None);
    };
    let method_record = store.symbol(method).ok_or_else(invalid)?;
    let declarations = method_record.declarations().ok_or_else(invalid)?;
    if method_record.flags() != SymbolFlags::METHOD
        || method_record.check_flags() != CheckFlags::NONE
        || method_record.name().as_utf8() != Some("concat")
        || method_record.value_declaration() != declarations.first().copied()
        || method_record.members().is_some()
        || method_record.exports().is_some()
        || method_record.export_symbol().is_some()
        || store.get_parent_of_symbol(method) != Some(owner)
    {
        return Err(invalid());
    }
    if declarations.len() != 2 {
        return Ok(None);
    }
    let Some(concat_array) = globals
        .get_source("ConcatArray")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return Ok(None);
    };
    let concat_owner = store.symbol(concat_array).ok_or_else(invalid)?;
    if !concat_owner.flags().contains(SymbolFlags::INTERFACE)
        || concat_owner.name().as_utf8() != Some("ConcatArray")
    {
        return Ok(None);
    }

    let mut overloads = Vec::new();
    overloads
        .try_reserve_exact(declarations.len())
        .map_err(|_| PropertyObjectError::Capacity(declarations[0]))?;
    for declaration in declarations {
        let overload = match plan_global_array_concat_overload(
            store,
            host,
            owner,
            method,
            *declaration,
            parameter_name,
        ) {
            Ok(overload) => overload,
            Err(PropertyObjectError::UnsupportedMember { .. }) => return Ok(None),
            Err(error) => return Err(error),
        };
        overloads.push(overload);
    }
    if !matches!(
        overloads.as_slice(),
        [
            GlobalArrayConcatOverloadPlan {
                kind: GlobalArrayConcatOverloadKind::Arrays,
                ..
            },
            GlobalArrayConcatOverloadPlan {
                kind: GlobalArrayConcatOverloadKind::ValuesOrArrays,
                ..
            }
        ]
    ) {
        return Ok(None);
    }

    Ok(Some(GlobalArrayConcatPlan {
        owner,
        method,
        concat_array,
        target,
        type_parameter,
        overloads,
    }))
}

fn is_global_concat_array_reference(
    store: &CanonicalTypeMapperStore,
    plan: &GlobalArrayConcatPlan,
    type_: TypeId,
) -> bool {
    let Ok(reference) = validate_direct_generic_reference(store, type_) else {
        return false;
    };
    reference.type_arguments.as_slice() == [plan.type_parameter]
        && store
            .type_payload(reference.target)
            .and_then(TypeRecord::symbol)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            == Some(plan.concat_array)
}

fn resolved_global_array_concat_method(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    plan: &GlobalArrayConcatPlan,
    return_type: TypeId,
) -> Option<TypeId> {
    let value = store.value_symbol_links(plan.method)?;
    let type_ = value.resolved_type?;
    let record = store.type_payload(type_)?;
    let TypeData::Object(object) = record.data() else {
        return None;
    };
    let signatures = object.structured.signatures.as_deref()?;
    if value
        != &(ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        })
        || record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.symbol() != Some(plan.method)
        || record.alias().is_some()
        || !valid_object_tail(object)
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.structured.members.is_some()
        || object.structured.properties.is_some()
        || object.structured.call_signature_count != signatures.len()
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || signatures.len() != plan.overloads.len()
    {
        return None;
    }

    for (overload, signature) in plan.overloads.iter().zip(signatures) {
        let signature = *signature;
        let callable = store.signature(signature)?;
        let [parameter] = callable.parameters() else {
            return None;
        };
        let links = store.value_symbol_links(*parameter)?;
        let parameter_type = links.resolved_type?;
        let parameter_array = store
            .canonical_array_reference(global_types, parameter_type)
            .ok()
            .flatten()?;
        if callable.flags() != SignatureFlags::HAS_REST_PARAMETER
            || callable.declaration() != Some(overload.declaration)
            || !callable.type_parameters().is_empty()
            || callable.this_parameter().is_some()
            || callable.min_argument_count() != 0
            || callable.resolved_min_argument_count() != -1
            || callable.resolved_return_type() != Some(return_type)
            || callable.resolved_type_predicate().is_some()
            || callable.target().is_some()
            || callable.mapper().is_some()
            || callable.isolated_signature_type().is_some()
            || callable.composite().is_some()
            || store.signature_has_circular_return_type(signature)
            || *parameter != overload.parameter
            || links
                != &(ValueSymbolLinks {
                    resolved_type: Some(parameter_type),
                    ..ValueSymbolLinks::default()
                })
            || parameter_array.readonly
            || parameter_array.array_literal
            || store.signature_links(overload.declaration)
                != Some(&SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                })
            || store.type_node_links(overload.parameter_annotation)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(parameter_type),
                    ..TypeNodeLinks::default()
                })
            || store.type_node_links(overload.return_annotation)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(return_type),
                    ..TypeNodeLinks::default()
                })
            || store.function_signature_return_annotation(signature)
                != Some((overload.return_annotation, false))
            || store.callable_signature_parameter_types(signature)
                != Some([parameter_type].as_slice())
        {
            return None;
        }
        let valid_element = match overload.kind {
            GlobalArrayConcatOverloadKind::Arrays => {
                is_global_concat_array_reference(store, plan, parameter_array.element_type)
            }
            GlobalArrayConcatOverloadKind::ValuesOrArrays => {
                let Some(TypeData::Union(union)) = store
                    .type_payload(parameter_array.element_type)
                    .map(TypeRecord::data)
                else {
                    return None;
                };
                union.union.types.len() == 2
                    && union.union.types.contains(&plan.type_parameter)
                    && union
                        .union
                        .types
                        .iter()
                        .copied()
                        .filter(|candidate| *candidate != plan.type_parameter)
                        .all(|candidate| is_global_concat_array_reference(store, plan, candidate))
            }
        };
        if !valid_element {
            return None;
        }
    }
    Some(type_)
}

fn materialize_global_concat_array_members(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    owner: SemanticSymbolId,
    target: TypeId,
) -> Result<(), PropertyObjectError> {
    let invalid = || PropertyObjectError::InvalidCachedInterface {
        symbol: owner,
        type_: target,
    };
    let raw_members = store
        .symbol(owner)
        .and_then(ts_binder::semantic::Symbol::members)
        .and_then(|members| store.symbol_table(members))
        .ok_or_else(invalid)?;
    if raw_members
        .get(InternalSymbolName::Index.as_ref())
        .is_none()
        || ["length", "join", "slice"]
            .iter()
            .any(|name| raw_members.get_source(name).is_none())
    {
        return Ok(());
    }
    let plan = plan_generic_interface(store, host, owner)?;
    let reference = validate_direct_generic_reference(store, target).map_err(|_| invalid())?;
    let [parameter] = reference.type_arguments.as_slice() else {
        return Err(invalid());
    };
    let parameter = *parameter;
    let [index] = plan.indexes.as_slice() else {
        return Err(invalid());
    };
    let [join, slice] = plan.methods.as_slice() else {
        return Err(invalid());
    };
    let (number, string) = {
        let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
        (bootstrap.number_type, bootstrap.string_type)
    };
    if plan.heritage.is_some()
        || plan.properties.len() != 3
        || plan.properties[0].name != "length"
        || !plan.properties[0].readonly
        || plan.properties[1].name != "join"
        || plan.properties[2].name != "slice"
        || !index.readonly
        || cached_planned_type_identity(store, index.key_type_node) != Some(number)
        || index.value_type_parameter.and_then(|symbol| {
            store
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
        }) != Some(parameter)
        || join.symbol != plan.properties[1].symbol
        || join.parameters.len() != 1
        || join.minimum_argument_count != 0
        || cached_planned_type_identity(store, join.parameters[0].type_node) != Some(string)
        || cached_planned_type_identity(store, join.return_type) != Some(string)
        || slice.symbol != plan.properties[2].symbol
        || slice.parameters.len() != 2
        || slice.minimum_argument_count != 0
        || slice.parameters.iter().any(|parameter| {
            cached_planned_type_identity(store, parameter.type_node) != Some(number)
        })
        || store.source_node_kind(slice.return_type) != Some(SyntaxKind::ArrayType)
    {
        return Err(invalid());
    }
    let array = store
        .create_canonical_array_type(global_types, parameter, false)
        .map_err(|_| invalid())?;
    let expected_links = TypeNodeLinks {
        resolved_type: Some(array),
        ..TypeNodeLinks::default()
    };
    if store
        .type_node_links(slice.return_type)
        .is_some_and(|links| links != &TypeNodeLinks::default() && links != &expected_links)
        || !store.try_reserve_type_node_links(usize::from(
            store.type_node_links(slice.return_type).is_none(),
        ))
    {
        return Err(invalid());
    }
    if store.type_node_links(slice.return_type) != Some(&expected_links)
        && !store.set_type_node_links(slice.return_type, expected_links)
    {
        return Err(invalid());
    }
    let bases_resolved = match store.type_payload(target).map(TypeRecord::data) {
        Some(TypeData::Interface(interface)) => interface.base_types_resolved,
        _ => return Err(invalid()),
    };
    if !bases_resolved && !store.publish_interface_no_base_resolution(target) {
        return Err(invalid());
    }
    publish_generic_interface_declared_members(store, &plan, target, &[number, string, array])?;
    Ok(())
}

/// Publishes the two authenticated default-library `Array.concat` overloads.
///
/// Mutable and readonly declarations retain their own canonical type
/// parameter. Both return mutable arrays; receiver specialization is separate.
pub(super) fn materialize_global_array_concat_method(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    receiver: TypeId,
) -> Result<Option<TypeId>, PropertyObjectError> {
    let Some(plan) = plan_global_array_concat_method(store, host, global_types, receiver)? else {
        return Ok(None);
    };
    let invalid = || PropertyObjectError::InvalidCachedInterface {
        symbol: plan.owner,
        type_: plan.target,
    };
    let return_type = if plan.target == global_types.array_type {
        plan.target
    } else {
        let Ok(return_type) =
            store.create_canonical_array_type(global_types, plan.type_parameter, false)
        else {
            return Ok(None);
        };
        return_type
    };
    if store
        .value_symbol_links(plan.method)
        .is_some_and(|links| links != &ValueSymbolLinks::default())
    {
        return resolved_global_array_concat_method(store, global_types, &plan, return_type)
            .map(Some)
            .ok_or_else(invalid);
    }
    if plan.overloads.iter().any(|overload| {
        store
            .signature_links(overload.declaration)
            .is_some_and(|links| links != &SignatureLinks::default())
            || store
                .value_symbol_links(overload.parameter)
                .is_some_and(|links| links != &ValueSymbolLinks::default())
    }) {
        return Err(invalid());
    }

    let Ok(concat_target) = store.get_declared_type_of_symbol(host, plan.concat_array) else {
        return Ok(None);
    };
    materialize_global_concat_array_members(
        store,
        host,
        global_types,
        plan.concat_array,
        concat_target,
    )?;
    let Ok(concat_instance) =
        store.create_direct_generic_reference_type(concat_target, &[plan.type_parameter])
    else {
        return Ok(None);
    };
    let Ok(first_parameter) =
        store.create_canonical_array_type(global_types, concat_instance, false)
    else {
        return Ok(None);
    };
    let Ok(union) = store.expression_union_type_with_global_types(
        global_types,
        &[plan.type_parameter, concat_instance],
        UnionReduction::Literal,
    ) else {
        return Ok(None);
    };
    let Ok(second_parameter) = store.create_canonical_array_type(global_types, union, false) else {
        return Ok(None);
    };
    let parameter_types = [first_parameter, second_parameter];
    for (overload, parameter_type) in plan.overloads.iter().zip(parameter_types) {
        for (annotation, type_) in [
            (overload.parameter_annotation, parameter_type),
            (overload.return_annotation, return_type),
        ] {
            if store.type_node_links(annotation).is_some_and(|links| {
                links != &TypeNodeLinks::default()
                    && links
                        != &(TypeNodeLinks {
                            resolved_type: Some(type_),
                            ..TypeNodeLinks::default()
                        })
            }) {
                return Err(invalid());
            }
        }
    }
    let mut signatures = Vec::new();
    let mut stored_signatures = Vec::new();
    let mut parameter_symbols = Vec::new();
    let mut prepared_parameter_types = Vec::new();
    let mut parameter_batches = Vec::new();
    signatures
        .try_reserve_exact(plan.overloads.len())
        .map_err(|_| PropertyObjectError::Capacity(plan.overloads[0].declaration))?;
    stored_signatures
        .try_reserve_exact(plan.overloads.len())
        .map_err(|_| PropertyObjectError::Capacity(plan.overloads[0].declaration))?;
    parameter_symbols
        .try_reserve_exact(plan.overloads.len())
        .map_err(|_| PropertyObjectError::Capacity(plan.overloads[0].declaration))?;
    prepared_parameter_types
        .try_reserve_exact(plan.overloads.len())
        .map_err(|_| PropertyObjectError::Capacity(plan.overloads[0].declaration))?;
    parameter_batches
        .try_reserve_exact(plan.overloads.len())
        .map_err(|_| PropertyObjectError::Capacity(plan.overloads[0].declaration))?;
    for (overload, parameter_type) in plan.overloads.iter().zip(parameter_types) {
        let mut symbols = Vec::new();
        let mut types = Vec::new();
        symbols
            .try_reserve_exact(1)
            .map_err(|_| PropertyObjectError::Capacity(overload.declaration))?;
        types
            .try_reserve_exact(1)
            .map_err(|_| PropertyObjectError::Capacity(overload.declaration))?;
        symbols.push(overload.parameter);
        types.push(parameter_type);
        parameter_symbols.push(symbols);
        prepared_parameter_types.push(types);
    }
    let missing_value_links = usize::from(store.value_symbol_links(plan.method).is_none())
        .checked_add(
            plan.overloads
                .iter()
                .filter(|overload| store.value_symbol_links(overload.parameter).is_none())
                .count(),
        )
        .ok_or(PropertyObjectError::Capacity(plan.overloads[0].declaration))?;
    let missing_signature_links = plan
        .overloads
        .iter()
        .filter(|overload| store.signature_links(overload.declaration).is_none())
        .count();
    let missing_type_node_links = plan
        .overloads
        .iter()
        .flat_map(|overload| [overload.parameter_annotation, overload.return_annotation])
        .filter(|annotation| store.type_node_links(*annotation).is_none())
        .count();
    if !store.try_reserve_types(1)
        || !store.try_reserve_signatures(plan.overloads.len())
        || !store.try_reserve_signature_links(missing_signature_links)
        || !store.try_reserve_value_symbol_links(missing_value_links)
        || !store.try_reserve_type_node_links(missing_type_node_links)
        || !store.try_reserve_function_signature_return_annotations(plan.overloads.len())
        || !store.try_reserve_callable_signature_parameter_types(plan.overloads.len())
    {
        return Err(PropertyObjectError::Capacity(plan.overloads[0].declaration));
    }

    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(plan.method))
        .expect("the Array.concat transaction reserved its callable object");
    for (((overload, parameter_type), symbols), prepared_types) in plan
        .overloads
        .iter()
        .zip(parameter_types)
        .zip(parameter_symbols)
        .zip(prepared_parameter_types)
    {
        let signature = store
            .alloc_signature(
                SignatureFlags::HAS_REST_PARAMETER,
                Some(overload.declaration),
                Vec::new(),
                None,
                symbols,
                Some(return_type),
                None,
                0,
            )
            .expect("the Array.concat transaction reserved both overload signatures");
        assert!(store.set_signature_links(
            overload.declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        ));
        assert!(store.set_type_node_links(
            overload.parameter_annotation,
            TypeNodeLinks {
                resolved_type: Some(parameter_type),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(store.set_type_node_links(
            overload.return_annotation,
            TypeNodeLinks {
                resolved_type: Some(return_type),
                ..TypeNodeLinks::default()
            },
        ));
        assert!(store.set_value_symbol_links(
            overload.parameter,
            ValueSymbolLinks {
                resolved_type: Some(parameter_type),
                ..ValueSymbolLinks::default()
            },
        ));
        parameter_batches.push((signature, prepared_types));
        signatures.push(signature);
        stored_signatures.push(signature);
    }
    assert!(store.set_value_symbol_links(
        plan.method,
        ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        },
    ));
    assert!(store.set_structured_type_members(
        type_,
        None,
        None,
        Some(stored_signatures),
        None,
        None,
    ));
    for (overload, signature) in plan.overloads.iter().zip(&signatures) {
        if !store.set_function_signature_return_annotation(
            *signature,
            overload.return_annotation,
            false,
        ) {
            return Err(PropertyObjectError::UnsupportedMember {
                node: overload.declaration,
                kind: SyntaxKind::MethodSignature,
            });
        }
    }
    if !store.set_callable_signature_parameter_types_batch(parameter_batches) {
        return Err(PropertyObjectError::UnsupportedMember {
            node: plan.overloads[0].declaration,
            kind: SyntaxKind::MethodSignature,
        });
    }
    Ok(Some(type_))
}

/// Plans the declared members of one source-owned generic interface.
///
/// The bound member table also contains the interface's type parameters. The
/// plan accepts merged declarations and canonical exported owners. Publication
/// creates a separate declared-property table instead of replacing the
/// binder-owned table.
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
    let Some(declarations) = symbol_record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
    else {
        return Err(PropertyObjectError::InvalidInterfaceSymbol(symbol));
    };
    let declaration = declarations[0];
    let invalid = || PropertyObjectError::InvalidInterface {
        declaration,
        symbol,
    };
    let raw_members = symbol_record.members().ok_or_else(invalid)?;
    let raw_table = store.symbol_table(raw_members).ok_or_else(invalid)?;
    if !symbol_record.flags().contains(SymbolFlags::INTERFACE)
        || symbol_record
            .flags()
            .without(SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT)
            != SymbolFlags::NONE
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.value_declaration().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.export_symbol().is_some()
    {
        return Err(invalid());
    }

    let mut seen_declarations = HashSet::with_capacity(declarations.len());
    let mut parameter_symbols = None;
    let mut first_members = None;
    let mut additional_members = Vec::with_capacity(declarations.len().saturating_sub(1));
    let mut heritage = None;
    for &candidate in declarations {
        let invalid_declaration = || PropertyObjectError::InvalidInterface {
            declaration: candidate,
            symbol,
        };
        if !seen_declarations.insert(candidate) {
            return Err(invalid_declaration());
        }
        let record = preflight_node(store, host, candidate).map_err(|_| invalid_declaration())?;
        let NodeData::InterfaceDeclaration(interface) = &record.data else {
            return Err(invalid_declaration());
        };
        let Some(parameters) = interface.type_parameters.as_ref() else {
            return Err(invalid_declaration());
        };
        let name = NodeRef::new(candidate.arena, candidate.file, interface.name);
        let name_record = preflight_node(store, host, name).map_err(|_| invalid_declaration())?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(invalid_declaration());
        };
        let expected_parent = declared_type_declaration_parent(
            store,
            host,
            candidate,
            symbol,
            name,
            interface.modifiers.as_ref(),
        )
        .map_err(|()| invalid_declaration())?;
        if record.kind != SyntaxKind::InterfaceDeclaration
            || record.flags.0 != 0
            || parameters.nodes.is_empty()
            || !host.symbol_matches(store, candidate, symbol)
            || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
            || symbol_record.parent().is_some() != expected_parent.is_some()
            || store.get_parent_of_symbol(symbol) != expected_parent
            || name_record.kind != SyntaxKind::Identifier
            || name_record.parent != Some(candidate.node)
            || interface.flow_node.is_some()
            || interface.local_symbol.is_some()
            || interface.symbol.is_some()
            || interface.members.has_trailing_comma
            || interface.members.range.start < record.range.start
            || interface.members.range.end != record.range.end
        {
            return Err(invalid_declaration());
        }
        if let Some(clauses) = interface.heritage_clauses.as_ref() {
            let planned = plan_direct_interface_heritage(store, host, candidate, symbol, clauses)
                .map_err(|error| match error {
                DirectInterfaceHeritageError::Invalid => invalid_declaration(),
                DirectInterfaceHeritageError::Unsupported { node, kind } => {
                    PropertyObjectError::UnsupportedMember { node, kind }
                }
            })?;
            if planned.bases.is_empty()
                || planned.bases.len() > 2
                || planned
                    .bases
                    .iter()
                    .any(|base| base.kind != DirectInterfaceBaseKind::Interface)
            {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: planned.clause,
                    kind: SyntaxKind::HeritageClause,
                });
            }
            merge_interface_heritage(store, host, &mut heritage, planned, 2)?;
        }

        let mut current_parameters = Vec::with_capacity(parameters.nodes.len());
        let mut unique_parameters = HashSet::with_capacity(parameters.nodes.len());
        for parameter in &parameters.nodes {
            let parameter = NodeRef::new(candidate.arena, candidate.file, *parameter);
            let parameter_record =
                preflight_node(store, host, parameter).map_err(|_| invalid_declaration())?;
            if parameter_record.kind != SyntaxKind::TypeParameter
                || parameter_record.parent != Some(candidate.node)
            {
                return Err(invalid_declaration());
            }
            let parameter_symbol =
                bound_symbol(store, host, parameter).ok_or_else(invalid_declaration)?;
            let parameter_symbol_record = store
                .symbol(parameter_symbol)
                .ok_or_else(invalid_declaration)?;
            if !parameter_symbol_record
                .flags()
                .contains(SymbolFlags::TYPE_PARAMETER)
                || parameter_symbol_record
                    .flags()
                    .without(SymbolFlags::TYPE_PARAMETER | SymbolFlags::TRANSIENT)
                    != SymbolFlags::NONE
                || parameter_symbol_record.check_flags() != CheckFlags::NONE
                || store.get_parent_of_symbol(parameter_symbol) != Some(symbol)
                || raw_table
                    .get(parameter_symbol_record.name())
                    .and_then(|parameter| store.get_merged_symbol(parameter))
                    != Some(parameter_symbol)
                || !unique_parameters.insert(parameter_symbol)
            {
                return Err(invalid_declaration());
            }
            current_parameters.push(parameter_symbol);
        }
        match parameter_symbols.as_ref() {
            Some(expected) if expected != &current_parameters => {
                return Err(invalid_declaration());
            }
            None => parameter_symbols = Some(current_parameters),
            Some(_) => {}
        }

        if candidate == declaration {
            first_members = Some(&interface.members);
        } else {
            additional_members.push((candidate, &interface.members));
        }
    }

    let mut plan = plan_members(
        store,
        host,
        PropertyObjectKind::Interface,
        declaration,
        symbol,
        Some(raw_members),
        first_members.ok_or_else(invalid)?,
        &additional_members,
        None,
        TypeLiteralMemberPolicy::GenericInterface,
    )?;
    plan.heritage = heritage;
    if let Some(call) = plan.call_signatures.first() {
        return Err(PropertyObjectError::UnsupportedMember {
            node: call.declaration,
            kind: call.syntax_kind(),
        });
    }
    if raw_table.len()
        != parameter_symbols.as_ref().map_or(0, Vec::len)
            + plan.properties.len()
            + usize::from(!plan.indexes.is_empty())
    {
        return Err(invalid());
    }
    Ok(plan)
}

/// Validates a reopened generic interface without reading its member annotations.
///
/// All declarations must belong to the same authenticated namespace, share one
/// binder-owned type parameter, and repeat the same optional generic base.
#[allow(clippy::too_many_lines)] // Declaration, parameter, and warm identity form one proof.
pub(super) fn plan_lazy_merged_generic_interface(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<LazyMergedGenericInterfacePlan, PropertyObjectError> {
    let symbol = store
        .get_merged_symbol(symbol)
        .ok_or(PropertyObjectError::InvalidInterfaceSymbol(symbol))?;
    let owner = store
        .symbol(symbol)
        .ok_or(PropertyObjectError::InvalidInterfaceSymbol(symbol))?;
    let declarations = owner
        .declarations()
        .filter(|declarations| declarations.len() >= 2)
        .ok_or(PropertyObjectError::InvalidInterfaceSymbol(symbol))?;
    let declaration = declarations[0];
    let invalid = || PropertyObjectError::InvalidInterface {
        declaration,
        symbol,
    };
    let namespace = store.get_parent_of_symbol(symbol).ok_or_else(invalid)?;
    let namespace_record = store.symbol(namespace).ok_or_else(invalid)?;
    let exports = namespace_record
        .exports()
        .and_then(|exports| store.symbol_table(exports))
        .ok_or_else(invalid)?;
    let members = owner
        .members()
        .and_then(|members| store.symbol_table(members))
        .ok_or_else(invalid)?;
    if !owner.flags().contains(SymbolFlags::INTERFACE)
        || owner
            .flags()
            .without(SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT)
            != SymbolFlags::NONE
        || owner.check_flags() != CheckFlags::NONE
        || owner.value_declaration().is_some()
        || owner.exports().is_some()
        || owner.export_symbol().is_some()
        || !namespace_record.flags().intersects(SymbolFlags::MODULE)
        || exports
            .get(owner.name())
            .and_then(|export| store.get_merged_symbol(export))
            != Some(symbol)
    {
        return Err(invalid());
    }

    let mut seen_declarations = HashSet::with_capacity(declarations.len());
    let mut parameter_declarations = Vec::with_capacity(declarations.len());
    let mut shared_parameter = None;
    let mut shared_base = None;
    for &candidate in declarations {
        let invalid_declaration = || PropertyObjectError::InvalidInterface {
            declaration: candidate,
            symbol,
        };
        let record = preflight_node(store, host, candidate).map_err(|_| invalid_declaration())?;
        let NodeData::InterfaceDeclaration(interface) = &record.data else {
            return Err(invalid_declaration());
        };
        let Some(parameters) = interface.type_parameters.as_ref() else {
            return Err(invalid_declaration());
        };
        let [parameter_id] = parameters.nodes.as_slice() else {
            return Err(invalid_declaration());
        };
        let name = NodeRef::new(candidate.arena, candidate.file, interface.name);
        let name_record = preflight_node(store, host, name).map_err(|_| invalid_declaration())?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(invalid_declaration());
        };
        let parent = declared_type_declaration_parent(
            store,
            host,
            candidate,
            symbol,
            name,
            interface.modifiers.as_ref(),
        )
        .map_err(|()| invalid_declaration())?;
        if !seen_declarations.insert(candidate)
            || record.kind != SyntaxKind::InterfaceDeclaration
            || record.flags.0 != 0
            || !host.symbol_matches(store, candidate, symbol)
            || parent != Some(namespace)
            || name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || name_record.parent != Some(candidate.node)
            || identifier.flow_node.is_some()
            || owner.name().as_utf8() != Some(identifier.text.as_str())
            || interface.flow_node.is_some()
            || interface.local_symbol.is_some()
            || interface.symbol.is_some()
            || parameters.has_trailing_comma
            || interface.members.has_trailing_comma
            || interface.members.range.start < record.range.start
            || interface.members.range.end != record.range.end
        {
            return Err(invalid_declaration());
        }

        let parameter = NodeRef::new(candidate.arena, candidate.file, *parameter_id);
        let parameter_record =
            preflight_node(store, host, parameter).map_err(|_| invalid_declaration())?;
        let NodeData::TypeParameterDeclaration(parameter_data) = &parameter_record.data else {
            return Err(invalid_declaration());
        };
        let parameter_name = NodeRef::new(parameter.arena, parameter.file, parameter_data.name);
        let parameter_name_record =
            preflight_node(store, host, parameter_name).map_err(|_| invalid_declaration())?;
        let NodeData::Identifier(parameter_identifier) = &parameter_name_record.data else {
            return Err(invalid_declaration());
        };
        let parameter_symbol =
            bound_symbol(store, host, parameter).ok_or_else(invalid_declaration)?;
        let parameter_owner = store
            .symbol(parameter_symbol)
            .ok_or_else(invalid_declaration)?;
        if parameter_record.kind != SyntaxKind::TypeParameter
            || parameter_record.flags.0 != 0
            || parameter_record.parent != Some(candidate.node)
            || parameter_data.constraint.is_some()
            || parameter_data.default_type.is_some()
            || parameter_data.expression.is_some()
            || parameter_data.modifiers.is_some()
            || parameter_data.symbol.is_some()
            || parameter_name_record.kind != SyntaxKind::Identifier
            || parameter_name_record.flags.0 != 0
            || parameter_name_record.parent != Some(parameter.node)
            || parameter_identifier.flow_node.is_some()
            || parameter_owner.name().as_utf8() != Some(parameter_identifier.text.as_str())
            || !parameter_owner
                .flags()
                .contains(SymbolFlags::TYPE_PARAMETER)
            || parameter_owner
                .flags()
                .without(SymbolFlags::TYPE_PARAMETER | SymbolFlags::TRANSIENT)
                != SymbolFlags::NONE
            || parameter_owner.check_flags() != CheckFlags::NONE
            || parameter_owner.value_declaration().is_some()
            || parameter_owner.members().is_some()
            || parameter_owner.exports().is_some()
            || parameter_owner.export_symbol().is_some()
            || store.get_parent_of_symbol(parameter_symbol) != Some(symbol)
            || members
                .get(parameter_owner.name())
                .and_then(|parameter| store.get_merged_symbol(parameter))
                != Some(parameter_symbol)
            || shared_parameter.is_some_and(|previous| previous != parameter_symbol)
        {
            return Err(invalid_declaration());
        }
        shared_parameter = Some(parameter_symbol);
        parameter_declarations.push(parameter);

        let base = interface
            .heritage_clauses
            .as_ref()
            .map(|clauses| {
                plan_lazy_merged_generic_interface_base(
                    store,
                    host,
                    candidate,
                    clauses,
                    namespace,
                    parameter_identifier.text.as_str(),
                )
            })
            .transpose()?;
        match shared_base {
            None => shared_base = Some(base),
            Some(previous) if previous != base => return Err(invalid_declaration()),
            Some(_) => {}
        }
    }

    let parameter = shared_parameter.ok_or_else(invalid)?;
    let parameter_owner = store.symbol(parameter).ok_or_else(invalid)?;
    if parameter_owner.declarations() != Some(parameter_declarations.as_slice()) {
        return Err(invalid());
    }
    if let Some(target) = store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
    {
        let record = store.type_payload(target).ok_or_else(invalid)?;
        let TypeData::Interface(interface) = record.data() else {
            return Err(invalid());
        };
        let reference = validate_direct_generic_reference(store, target).map_err(|_| invalid())?;
        let [argument] = reference.type_arguments.as_slice() else {
            return Err(invalid());
        };
        if record.flags() != TypeFlags::OBJECT
            || !record
                .object_flags()
                .contains(ObjectFlags::INTERFACE | ObjectFlags::REFERENCE)
            || record.symbol() != Some(symbol)
            || record.alias().is_some()
            || reference.target != target
            || cached_ordinary_type_parameter_owner(store, *argument) != Some(parameter)
            || interface.outer_type_parameter_count != 0
            || interface.declared_members_resolved
            || interface.reference.object.structured != StructuredTypeData::default()
        {
            return Err(invalid());
        }
    }

    Ok(LazyMergedGenericInterfacePlan {
        symbol,
        namespace,
        type_parameter: parameter,
    })
}

fn plan_lazy_merged_generic_interface_base(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    clauses: &NodeList,
    namespace: SemanticSymbolId,
    parameter_name: &str,
) -> Result<SemanticSymbolId, PropertyObjectError> {
    let invalid = || PropertyObjectError::UnsupportedMember {
        node: declaration,
        kind: SyntaxKind::InterfaceDeclaration,
    };
    let [clause_id] = clauses.nodes.as_slice() else {
        return Err(invalid());
    };
    let clause = NodeRef::new(declaration.arena, declaration.file, *clause_id);
    let clause_record = preflight_node(store, host, clause).map_err(|_| invalid())?;
    let NodeData::HeritageClause(heritage) = &clause_record.data else {
        return Err(invalid());
    };
    let [base_id] = heritage.types.nodes.as_slice() else {
        return Err(invalid());
    };
    if clauses.has_trailing_comma
        || clause_record.kind != SyntaxKind::HeritageClause
        || clause_record.flags.0 != 0
        || clause_record.parent != Some(declaration.node)
        || heritage.token != SyntaxKind::ExtendsKeyword
        || heritage.facts != 0
        || heritage.types.has_trailing_comma
    {
        return Err(invalid());
    }

    let base = NodeRef::new(declaration.arena, declaration.file, *base_id);
    let base_record = preflight_node(store, host, base).map_err(|_| invalid())?;
    let NodeData::ExpressionWithTypeArguments(expression) = &base_record.data else {
        return Err(invalid());
    };
    let Some(arguments) = expression.type_arguments.as_ref() else {
        return Err(invalid());
    };
    let [argument_id] = arguments.nodes.as_slice() else {
        return Err(invalid());
    };
    if base_record.kind != SyntaxKind::ExpressionWithTypeArguments
        || base_record.flags.0 != 0
        || base_record.parent != Some(clause.node)
        || expression.facts != 0
        || arguments.has_trailing_comma
    {
        return Err(invalid());
    }

    let base_name = NodeRef::new(base.arena, base.file, expression.expression);
    let base_name_record = preflight_node(store, host, base_name).map_err(|_| invalid())?;
    let NodeData::Identifier(base_identifier) = &base_name_record.data else {
        return Err(invalid());
    };
    let argument = NodeRef::new(base.arena, base.file, *argument_id);
    let argument_record = preflight_node(store, host, argument).map_err(|_| invalid())?;
    let NodeData::TypeReferenceNode(argument_reference) = &argument_record.data else {
        return Err(invalid());
    };
    let argument_name = NodeRef::new(argument.arena, argument.file, argument_reference.type_name);
    let argument_name_record = preflight_node(store, host, argument_name).map_err(|_| invalid())?;
    let NodeData::Identifier(argument_identifier) = &argument_name_record.data else {
        return Err(invalid());
    };
    let base_symbol = store
        .symbol(namespace)
        .and_then(ts_binder::semantic::Symbol::exports)
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get_source(&base_identifier.text))
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(invalid)?;
    let owner = store.symbol(base_symbol).ok_or_else(invalid)?;
    if base_name_record.kind != SyntaxKind::Identifier
        || base_name_record.flags.0 != 0
        || base_name_record.parent != Some(base.node)
        || base_identifier.flow_node.is_some()
        || argument_record.kind != SyntaxKind::TypeReference
        || argument_record.flags.0 != 0
        || argument_record.parent != Some(base.node)
        || argument_reference.type_arguments.is_some()
        || argument_name_record.kind != SyntaxKind::Identifier
        || argument_name_record.flags.0 != 0
        || argument_name_record.parent != Some(argument.node)
        || argument_identifier.flow_node.is_some()
        || argument_identifier.text != parameter_name
        || !owner.flags().contains(SymbolFlags::INTERFACE)
        || owner
            .flags()
            .without(SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT)
            != SymbolFlags::NONE
        || owner.check_flags() != CheckFlags::NONE
        || store.get_parent_of_symbol(base_symbol) != Some(namespace)
    {
        return Err(invalid());
    }
    Ok(base_symbol)
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
        let declarations = owner
            .declarations()
            .ok_or_else(invalid)?
            .iter()
            .copied()
            .filter(|candidate| {
                candidate.is_for(declaration.arena, declaration.file)
                    && bound.local_symbol(*candidate) == Some(local)
            })
            .collect::<Vec<_>>();
        if local == symbol
            || store.get_merged_symbol(local) != Some(local)
            || record.flags() != SymbolFlags::NONE
            || record.check_flags() != CheckFlags::NONE
            || record.name().as_utf8() != Some(name)
            || declarations.is_empty()
            || record.declarations() != Some(declarations.as_slice())
            || record.value_declaration().is_some()
            || record.members().is_some()
            || record.exports().is_some()
            || record.parent().is_some()
            || record
                .export_symbol()
                .and_then(|export| store.get_merged_symbol(export))
                != Some(symbol)
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

fn is_reparsed_javascript_typedef_property(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    literal: NodeRef,
    alias_symbol: Option<SemanticSymbolId>,
    property: NodeRef,
) -> bool {
    let Some(alias_symbol) = alias_symbol else {
        return false;
    };
    let Ok(literal_record) = preflight_node(store, host, literal) else {
        return false;
    };
    let Ok(property_record) = preflight_node(store, host, property) else {
        return false;
    };
    let Some(alias_node) = literal_record.parent else {
        return false;
    };
    let alias_node = NodeRef::new(literal.arena, literal.file, alias_node);
    let Ok(alias_record) = preflight_node(store, host, alias_node) else {
        return false;
    };
    let NodeData::TypeAliasDeclaration(alias) = &alias_record.data else {
        return false;
    };
    let Some(bound) = host.bound_file(alias_node) else {
        return false;
    };

    literal_record.kind == SyntaxKind::TypeLiteral
        && literal_record.flags == NodeFlags::REPARSED
        && property_record.kind == SyntaxKind::PropertyDeclaration
        && property_record.flags == NodeFlags::REPARSED
        && property_record.parent == Some(literal.node)
        && alias_record.kind == SyntaxKind::JsTypeAliasDeclaration
        && alias_record.flags == NodeFlags::REPARSED
        && alias_record.parent == Some(bound.source_file().node)
        && alias.type_ == literal.node
        && bound
            .source_facts()
            .is_some_and(ts_binder::CanonicalSourceFileFacts::is_javascript_file)
        && bound
            .symbol(alias_node)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            == Some(alias_symbol)
        && host.symbol_matches(store, alias_node, alias_symbol)
}

fn implicit_any_augmentation_interface_property(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    interface: NodeRef,
    property: NodeRef,
) -> bool {
    let Some(bound) = host.bound_file(interface) else {
        return false;
    };
    let Some(interface_record) = host.node(interface) else {
        return false;
    };
    let Some(body) = interface_record
        .parent
        .map(|node| NodeRef::new(interface.arena, interface.file, node))
    else {
        return false;
    };
    let Some(body_record) = host.node(body) else {
        return false;
    };
    let Some(namespace) = body_record
        .parent
        .map(|node| NodeRef::new(interface.arena, interface.file, node))
    else {
        return false;
    };
    let Some(namespace_record) = host.node(namespace) else {
        return false;
    };
    let NodeData::ModuleDeclaration(module) = &namespace_record.data else {
        return false;
    };
    let name = NodeRef::new(namespace.arena, namespace.file, module.name);
    let Some(property_record) = host.node(property) else {
        return false;
    };
    let NodeData::PropertyDeclaration(member) = &property_record.data else {
        return false;
    };
    let property_name = NodeRef::new(property.arena, property.file, member.name);

    interface_record.kind == SyntaxKind::InterfaceDeclaration
        && body_record.kind == SyntaxKind::ModuleBlock
        && body_record.parent == Some(namespace.node)
        && namespace_record.kind == SyntaxKind::ModuleDeclaration
        && bound
            .module_augmentations()
            .iter()
            .any(|augmentation| augmentation.name() == name)
        && property_record.kind == SyntaxKind::PropertyDeclaration
        && property_record.flags.0 == 0
        && property_record.parent == Some(interface.node)
        && member.type_.is_none()
        && member.initializer.is_none()
        && member.postfix_token.is_none()
        && member.modifiers.is_none()
        && member.symbol.is_none()
        && member.facts == 0
        && host.node(property_name).is_some_and(|name| {
            matches!(
                &name.data,
                NodeData::Identifier(identifier)
                    if name.kind == SyntaxKind::Identifier
                        && name.flags.0 == 0
                        && name.parent == Some(property.node)
                        && identifier.flow_node.is_none()
                        && !identifier.text.is_empty()
            )
        })
        && bound
            .symbol(interface)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            .is_some()
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
    additional_members: &[(NodeRef, &NodeList)],
    alias_symbol: Option<SemanticSymbolId>,
    policy: TypeLiteralMemberPolicy,
) -> Result<PropertyObjectPlan, PropertyObjectError> {
    let provisional = PropertyObjectPlan {
        kind,
        node,
        const_context: false,
        declarations: std::iter::once(node)
            .chain(
                additional_members
                    .iter()
                    .map(|(declaration, _)| *declaration),
            )
            .collect(),
        symbol,
        members,
        properties: Vec::new(),
        methods: Vec::new(),
        accessors: Vec::new(),
        spreads: Vec::new(),
        indexes: Vec::new(),
        call_signatures: Vec::new(),
        alias_symbol,
        heritage: None,
    };
    let member_count = additional_members
        .iter()
        .try_fold(member_nodes.nodes.len(), |count, (_, members)| {
            count.checked_add(members.nodes.len())
        })
        .ok_or(PropertyObjectError::Capacity(node))?;
    let direct_member_count = if kind == PropertyObjectKind::ObjectLiteral {
        member_nodes
            .nodes
            .iter()
            .filter(|member| {
                let member = NodeRef::new(node.arena, node.file, **member);
                store.source_node_kind(member) != Some(SyntaxKind::SpreadAssignment)
            })
            .count()
    } else {
        member_count
    };
    if kind != PropertyObjectKind::ObjectLiteral
        && (member_nodes.has_trailing_comma
            || additional_members
                .iter()
                .any(|(_, members)| members.has_trailing_comma))
        || policy != TypeLiteralMemberPolicy::GenericInterface
            && members.is_some() == (direct_member_count == 0)
        || policy == TypeLiteralMemberPolicy::GenericInterface && members.is_none()
    {
        return Err(invalid_plan(&provisional));
    }
    let table = members.and_then(|members| store.symbol_table(members));
    if members.is_some() != table.is_some() {
        return Err(invalid_plan(&provisional));
    }

    let mut seen_nodes = HashSet::new();
    let mut member_entries = Vec::with_capacity(member_count);
    for (owner, group) in
        std::iter::once((node, member_nodes)).chain(additional_members.iter().copied())
    {
        let owner_record =
            preflight_node(store, host, owner).map_err(|_| invalid_plan(&provisional))?;
        let mut previous_end = group.range.start;
        for member in &group.nodes {
            let member = NodeRef::new(owner.arena, owner.file, *member);
            let member_record =
                preflight_node(store, host, member).map_err(|_| invalid_plan(&provisional))?;
            if member_record.parent != Some(owner.node)
                || member_record.flags.0 & NODE_FLAG_JSDOC != 0
                || member_record.range.start < previous_end
                || member_record.range.start < group.range.start
                || member_record.range.end > group.range.end
                || member_record.range.start < owner_record.range.start
                || member_record.range.end > owner_record.range.end
                || !seen_nodes.insert(member)
            {
                return Err(invalid_plan(&provisional));
            }
            previous_end = member_record.range.end;
            member_entries.push((owner, member));
        }
    }
    let mut seen_symbols = HashSet::new();
    let mut seen_names = HashSet::new();
    let mut planned_symbol_declarations = HashMap::<SemanticSymbolId, Vec<NodeRef>>::new();
    let mut properties = Vec::with_capacity(member_count);
    let mut methods = Vec::new();
    let mut accessors = Vec::new();
    let mut spreads = Vec::new();
    let mut indexes = Vec::with_capacity(1);
    let mut call_signatures = Vec::with_capacity(member_count);
    for (member_owner, member) in member_entries {
        let member_record =
            preflight_node(store, host, member).map_err(|_| invalid_plan(&provisional))?;
        if kind == PropertyObjectKind::Interface
            && matches!(
                member_record.kind,
                SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature
            )
            && authenticated_default_library_builtin_symbol_tag(store, host, symbol, member)
        {
            continue;
        }
        if kind == PropertyObjectKind::Interface
            && member_record.kind == SyntaxKind::MethodSignature
            && matches!(
                &member_record.data,
                NodeData::MethodSignatureDeclaration(method)
                    if store.source_node_kind(NodeRef::new(
                        member.arena,
                        member.file,
                        method.name,
                    )) == Some(SyntaxKind::ComputedPropertyName)
            )
            && authenticated_default_library_builtin_symbol_method(store, host, symbol, member)
        {
            continue;
        }
        let admitted_kind = match kind {
            PropertyObjectKind::ObjectLiteral => matches!(
                member_record.kind,
                SyntaxKind::PropertyAssignment
                    | SyntaxKind::ShorthandPropertyAssignment
                    | SyntaxKind::SpreadAssignment
            ),
            PropertyObjectKind::TypeLiteral => matches!(
                member_record.kind,
                SyntaxKind::PropertyDeclaration
                    | SyntaxKind::PropertySignature
                    | SyntaxKind::MethodSignature
                    | SyntaxKind::IndexSignature
                    | SyntaxKind::CallSignature
                    | SyntaxKind::ConstructSignature
            ),
            PropertyObjectKind::Interface => matches!(
                member_record.kind,
                SyntaxKind::PropertyDeclaration
                    | SyntaxKind::PropertySignature
                    | SyntaxKind::MethodSignature
                    | SyntaxKind::GetAccessor
                    | SyntaxKind::SetAccessor
                    | SyntaxKind::IndexSignature
                    | SyntaxKind::CallSignature
                    | SyntaxKind::ConstructSignature
            ),
        };
        if !admitted_kind {
            return Err(PropertyObjectError::UnsupportedMember {
                node: member,
                kind: member_record.kind,
            });
        }
        if member_record.kind == SyntaxKind::SpreadAssignment {
            let NodeData::SpreadAssignment(spread) = &member_record.data else {
                return Err(invalid_plan(&provisional));
            };
            let expression = NodeRef::new(member.arena, member.file, spread.expression);
            let expression_record =
                preflight_node(store, host, expression).map_err(|_| invalid_plan(&provisional))?;
            if kind != PropertyObjectKind::ObjectLiteral
                || spread.symbol.is_some()
                || host
                    .bound_file(member)
                    .and_then(|bound| bound.symbol(member))
                    .is_some()
                || expression_record.parent != Some(member.node)
                || expression_record.range.start < member_record.range.start
                || expression_record.range.end > member_record.range.end
            {
                return Err(invalid_plan(&provisional));
            }
            spreads.push(PlannedObjectSpread {
                declaration: member,
                expression,
                property_index: properties.len(),
            });
            continue;
        }
        if matches!(
            member_record.kind,
            SyntaxKind::CallSignature | SyntaxKind::ConstructSignature
        ) {
            let signature = plan_call_signature(store, host, member_owner, symbol, member)?;
            call_signatures.push(signature);
            continue;
        }

        if member_record.kind == SyntaxKind::IndexSignature {
            let index = plan_index_signature(store, host, member_owner, symbol, member)?;
            if kind != PropertyObjectKind::Interface
                && policy == TypeLiteralMemberPolicy::General
                && !indexes.is_empty()
            {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: member,
                    kind: SyntaxKind::IndexSignature,
                });
            }
            indexes.push(index);
            continue;
        }

        if matches!(
            member_record.kind,
            SyntaxKind::GetAccessor | SyntaxKind::SetAccessor
        ) {
            if kind != PropertyObjectKind::Interface
                || policy == TypeLiteralMemberPolicy::GenericInterface
            {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: member,
                    kind: member_record.kind,
                });
            }
            let accessor = plan_interface_accessor(store, host, member_owner, symbol, member)?;
            let accessor_symbol = store
                .symbol(accessor.symbol)
                .ok_or_else(|| invalid_plan(&provisional))?;
            let property_name = accessor_symbol
                .name()
                .as_utf8()
                .ok_or_else(|| invalid_plan(&provisional))?
                .to_owned();
            if table.and_then(|table| table.get_source(&property_name)) != Some(accessor.symbol) {
                return Err(invalid_plan(&provisional));
            }
            planned_symbol_declarations
                .entry(accessor.symbol)
                .or_default()
                .push(member);
            let getter = member_record.kind == SyntaxKind::GetAccessor;
            if seen_symbols.insert(accessor.symbol) {
                if !seen_names.insert(property_name.clone()) {
                    return Err(invalid_plan(&provisional));
                }
                properties.push(PlannedProperty {
                    declaration: member,
                    symbol: accessor.symbol,
                    name_node: accessor.name_node,
                    type_node: accessor.type_node,
                    optional: accessor_symbol.flags().contains(SymbolFlags::OPTIONAL),
                    readonly: getter
                        && !accessor_symbol.flags().contains(SymbolFlags::SET_ACCESSOR)
                        && !accessor_symbol.flags().contains(SymbolFlags::PROPERTY),
                    name: property_name,
                });
            } else {
                let Some(property) = properties
                    .iter_mut()
                    .find(|property| property.symbol == accessor.symbol)
                else {
                    return Err(invalid_plan(&provisional));
                };
                if store
                    .symbol(property.symbol)
                    .is_some_and(|symbol| symbol.flags().contains(SymbolFlags::METHOD))
                {
                    return Err(invalid_plan(&provisional));
                }
                if getter {
                    let previous_getter =
                        accessors.iter().any(|previous: &PlannedInterfaceAccessor| {
                            previous.symbol == accessor.symbol && previous.parameter.is_none()
                        });
                    let previous_property = planned_symbol_declarations
                        .get(&accessor.symbol)
                        .is_some_and(|declarations| {
                            declarations.iter().any(|declaration| {
                                matches!(
                                    store.source_node_kind(*declaration),
                                    Some(
                                        SyntaxKind::PropertyDeclaration
                                            | SyntaxKind::PropertySignature
                                    )
                                )
                            })
                        });
                    if previous_getter
                        || previous_property
                            && !equivalent_merged_property_annotations(
                                store,
                                host,
                                property.type_node,
                                accessor.type_node,
                            )
                    {
                        return Err(PropertyObjectError::UnsupportedMember {
                            node: member,
                            kind: member_record.kind,
                        });
                    }
                    property.type_node = accessor.type_node;
                } else {
                    if accessors.iter().any(|previous: &PlannedInterfaceAccessor| {
                        previous.symbol == accessor.symbol && previous.parameter.is_some()
                    }) {
                        return Err(PropertyObjectError::UnsupportedMember {
                            node: member,
                            kind: member_record.kind,
                        });
                    }
                    property.readonly = false;
                }
            }
            accessors.push(accessor);
            continue;
        }

        if member_record.kind == SyntaxKind::MethodSignature {
            if kind == PropertyObjectKind::ObjectLiteral {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: member,
                    kind: SyntaxKind::MethodSignature,
                });
            }
            let method = plan_interface_method(store, host, member_owner, symbol, member)?;
            let method_record = store
                .symbol(method.symbol)
                .ok_or_else(|| invalid_plan(&provisional))?;
            let property_name = method_record
                .name()
                .as_utf8()
                .ok_or_else(|| invalid_plan(&provisional))?
                .to_owned();
            if table.and_then(|table| table.get_source(&property_name)) != Some(method.symbol) {
                return Err(invalid_plan(&provisional));
            }
            planned_symbol_declarations
                .entry(method.symbol)
                .or_default()
                .push(member);
            if seen_symbols.insert(method.symbol) {
                if !seen_names.insert(property_name.clone()) {
                    return Err(invalid_plan(&provisional));
                }
                let NodeData::MethodSignatureDeclaration(declaration) = &member_record.data else {
                    unreachable!("the interface method planner checked its declaration")
                };
                properties.push(PlannedProperty {
                    declaration: member,
                    symbol: method.symbol,
                    name_node: NodeRef::new(member.arena, member.file, declaration.name),
                    type_node: method.return_type,
                    optional: false,
                    readonly: false,
                    name: property_name,
                });
            } else if !properties.iter().any(|property| {
                property.symbol == method.symbol
                    && property.name == property_name
                    && !property.optional
                    && !property.readonly
                    && store.source_node_kind(property.declaration)
                        == Some(SyntaxKind::MethodSignature)
            }) {
                return Err(invalid_plan(&provisional));
            }
            methods.push(method);
            continue;
        }

        let (name_id, value_id, postfix_token, modifiers, signature_initializer, valid_payload) =
            match &member_record.data {
                NodeData::PropertyDeclaration(property)
                    if kind != PropertyObjectKind::ObjectLiteral =>
                {
                    let implicit_any = kind == PropertyObjectKind::Interface
                        && property.type_.is_none()
                        && implicit_any_augmentation_interface_property(
                            store,
                            host,
                            member_owner,
                            member,
                        );
                    (
                        property.name,
                        property
                            .type_
                            .or_else(|| implicit_any.then_some(property.name)),
                        property.postfix_token,
                        property.modifiers.as_ref(),
                        None,
                        property.initializer.is_none()
                            && (property.type_.is_some() || implicit_any)
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
            NodeData::StringLiteral(literal) if name_record.kind == SyntaxKind::StringLiteral => {
                literal.text.clone()
            }
            NodeData::NumericLiteral(literal) if name_record.kind == SyntaxKind::NumericLiteral => {
                literal.text.clone()
            }
            NodeData::NoSubstitutionTemplateLiteral(literal)
                if kind != PropertyObjectKind::TypeLiteral
                    && name_record.kind == SyntaxKind::NoSubstitutionTemplateLiteral =>
            {
                literal.text.clone()
            }
            NodeData::ComputedPropertyName(computed)
                if name_record.kind == SyntaxKind::ComputedPropertyName =>
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
        {
            return Err(invalid_plan(&provisional));
        }

        let type_node = NodeRef::new(member.arena, member.file, value_id.expect("checked above"));
        let type_record =
            preflight_node(store, host, type_node).map_err(|_| invalid_plan(&provisional))?;
        let reparsed_javascript_property = kind == PropertyObjectKind::TypeLiteral
            && is_reparsed_javascript_typedef_property(
                store,
                host,
                member_owner,
                alias_symbol,
                member,
            );
        let valid_value_range = if member_record.kind == SyntaxKind::ShorthandPropertyAssignment
            || kind == PropertyObjectKind::Interface && type_node == name
        {
            type_node == name && type_record.range == name_record.range
        } else if reparsed_javascript_property {
            type_record.range.start >= member_record.range.start
                && type_record.range.end <= name_record.range.start
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
            let valid_token_range = if reparsed_javascript_property {
                token_record.flags == NodeFlags::REPARSED
                    && token_record.range.start == name_record.range.end
                    && token_record.range.end == name_record.range.end
            } else {
                token_record.range.start >= name_record.range.end
                    && token_record.range.end <= type_record.range.start
            };
            if token_record.kind != SyntaxKind::QuestionToken
                || token_record.parent != Some(member.node)
                || !valid_token_range
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
            }
            | if kind == PropertyObjectKind::Interface {
                property_record.flags() & SymbolFlags::ACCESSOR
            } else {
                SymbolFlags::NONE
            };
        let expected_check_flags = source_property_check_flags(readonly);
        let symbol_declarations = property_record.declarations().unwrap_or_default();
        let declarations_valid = if kind == PropertyObjectKind::Interface {
            !symbol_declarations.is_empty() && symbol_declarations.contains(&member)
        } else {
            symbol_declarations == [member].as_slice()
        };
        if property_record.flags() != expected_flags
            || (property_record.check_flags() != CheckFlags::NONE
                && property_record.check_flags() != expected_check_flags)
            || property_record.name().as_utf8() != Some(property_name.as_str())
            || !declarations_valid
            || property_record.value_declaration() != symbol_declarations.first().copied()
            || property_record.members().is_some()
            || property_record.exports().is_some()
            || property_record.export_symbol().is_some()
            || property_record
                .parent()
                .and_then(|parent| store.get_merged_symbol(parent))
                != Some(symbol)
            || table.and_then(|table| table.get_source(&property_name)) != Some(property_symbol)
        {
            return Err(invalid_plan(&provisional));
        }
        planned_symbol_declarations
            .entry(property_symbol)
            .or_default()
            .push(member);
        if !seen_symbols.insert(property_symbol) {
            let Some(existing) = properties
                .iter_mut()
                .find(|planned| planned.symbol == property_symbol)
            else {
                return Err(invalid_plan(&provisional));
            };
            if property_record.flags().intersects(SymbolFlags::ACCESSOR) {
                let getter = accessors.iter().find(|accessor| {
                    accessor.symbol == property_symbol && accessor.parameter.is_none()
                });
                if kind != PropertyObjectKind::Interface
                    || existing.name != property_name
                    || existing.optional != optional
                    || getter.is_some_and(|accessor| {
                        !equivalent_merged_property_annotations(
                            store,
                            host,
                            accessor.type_node,
                            type_node,
                        )
                    })
                {
                    return Err(PropertyObjectError::UnsupportedMember {
                        node: member,
                        kind: member_record.kind,
                    });
                }
                if getter.is_none() {
                    existing.type_node = type_node;
                }
                existing.readonly =
                    readonly && !property_record.flags().contains(SymbolFlags::SET_ACCESSOR);
                continue;
            }
            if kind != PropertyObjectKind::Interface
                || existing.name != property_name
                || existing.optional != optional
                || existing.readonly != readonly
                || !equivalent_merged_property_annotations(
                    store,
                    host,
                    existing.type_node,
                    type_node,
                )
            {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: member,
                    kind: member_record.kind,
                });
            }
            continue;
        }
        if !seen_names.insert(property_name.clone()) {
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

    if planned_symbol_declarations
        .iter()
        .any(|(property, declarations)| {
            store
                .symbol(*property)
                .and_then(ts_binder::semantic::Symbol::declarations)
                != Some(declarations.as_slice())
        })
    {
        return Err(invalid_plan(&provisional));
    }

    let mut seen_index_kinds = HashSet::with_capacity(indexes.len());
    for index in &indexes {
        let Some(
            kind @ (SyntaxKind::StringKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::TemplateLiteralType),
        ) = store.source_node_kind(index.key_type_node)
        else {
            return Err(invalid_plan(&provisional));
        };
        if kind != SyntaxKind::TemplateLiteralType && !seen_index_kinds.insert(kind) {
            return Err(PropertyObjectError::UnsupportedMember {
                node: index.declaration,
                kind: SyntaxKind::IndexSignature,
            });
        }
    }

    let reserved_index_count = usize::from(!indexes.is_empty());
    let reserved_call_count = usize::from(
        call_signatures
            .iter()
            .any(|signature| !signature.is_construct()),
    ) + usize::from(
        call_signatures
            .iter()
            .any(PlannedCallSignature::is_construct),
    );
    if table.is_some_and(|table| {
        let parameter_count = if policy == TypeLiteralMemberPolicy::GenericInterface {
            table
                .iter()
                .filter(|(_, member)| {
                    store.symbol(*member).is_some_and(|record| {
                        record.flags().contains(SymbolFlags::TYPE_PARAMETER)
                            && record
                                .flags()
                                .without(SymbolFlags::TYPE_PARAMETER | SymbolFlags::TRANSIENT)
                                == SymbolFlags::NONE
                    })
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
            || [false, true].into_iter().any(|construct| {
                let name = if construct {
                    InternalSymbolName::New
                } else {
                    InternalSymbolName::Call
                };
                let expected = call_signatures
                    .iter()
                    .find(|signature| signature.is_construct() == construct)
                    .map(|signature| signature.symbol);
                table.get(name.as_ref()) != expected
            })
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
    if kind != PropertyObjectKind::Interface
        && policy == TypeLiteralMemberPolicy::General
        && !indexes.is_empty()
        && !properties.is_empty()
        && indexes.iter().any(|index| {
            store.source_node_kind(index.key_type_node) != Some(SyntaxKind::TemplateLiteralType)
        })
    {
        return Err(PropertyObjectError::UnsupportedMember {
            node: indexes[0].declaration,
            kind: SyntaxKind::IndexSignature,
        });
    }
    if !call_signatures.is_empty()
        && (kind != PropertyObjectKind::Interface && !indexes.is_empty()
            || !properties.is_empty()
                && match kind {
                    PropertyObjectKind::Interface => false,
                    PropertyObjectKind::TypeLiteral => {
                        policy == TypeLiteralMemberPolicy::GenericInterface
                            || !additional_members.is_empty()
                            || !methods.is_empty()
                            || !accessors.is_empty()
                            || call_signatures
                                .iter()
                                .any(PlannedCallSignature::is_construct)
                    }
                    PropertyObjectKind::ObjectLiteral => true,
                })
    {
        return Err(PropertyObjectError::UnsupportedMember {
            node: call_signatures[0].declaration,
            kind: call_signatures[0].syntax_kind(),
        });
    }
    for construct in [false, true] {
        let Some(first) = call_signatures
            .iter()
            .find(|signature| signature.is_construct() == construct)
        else {
            continue;
        };
        let declarations = call_signatures
            .iter()
            .filter(|signature| signature.is_construct() == construct)
            .map(|signature| signature.declaration)
            .collect::<Vec<_>>();
        let Some(record) = store.symbol(first.symbol) else {
            return Err(invalid_plan(&provisional));
        };
        if call_signatures
            .iter()
            .filter(|signature| signature.is_construct() == construct)
            .any(|signature| signature.symbol != first.symbol)
            || record.declarations() != Some(declarations.as_slice())
        {
            return Err(invalid_plan(&provisional));
        }
    }

    Ok(PropertyObjectPlan {
        properties,
        methods,
        accessors,
        spreads,
        indexes,
        call_signatures,
        ..provisional
    })
}

fn equivalent_merged_property_annotations(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    first: NodeRef,
    second: NodeRef,
) -> bool {
    let (Ok(first_record), Ok(second_record)) = (
        preflight_node(store, host, first),
        preflight_node(store, host, second),
    ) else {
        return false;
    };
    if first_record.kind != second_record.kind {
        return false;
    }
    if first_record.kind.is_keyword_type() {
        return true;
    }
    let Some((first_arena, _)) = host.source(first) else {
        return false;
    };
    let Some((second_arena, _)) = host.source(second) else {
        return false;
    };
    let Some(first_source) = first_arena.source_text() else {
        return false;
    };
    let Some(second_source) = second_arena.source_text() else {
        return false;
    };
    let first_text = first_source
        .get(first_record.range.start.get() as usize..first_record.range.end.get() as usize);
    let second_text = second_source
        .get(second_record.range.start.get() as usize..second_record.range.end.get() as usize);
    first_text.is_some() && first_text == second_text
}

fn plan_interface_accessor(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: NodeRef,
    owner_symbol: SemanticSymbolId,
    declaration: NodeRef,
) -> Result<PlannedInterfaceAccessor, PropertyObjectError> {
    let record = preflight_node(store, host, declaration).map_err(|_| {
        PropertyObjectError::InvalidInterface {
            declaration: owner,
            symbol: owner_symbol,
        }
    })?;
    let unsupported = || PropertyObjectError::UnsupportedMember {
        node: declaration,
        kind: record.kind,
    };
    let (name_id, parameters, annotation, getter, valid_payload) = match &record.data {
        NodeData::GetAccessorDeclaration(accessor) if record.kind == SyntaxKind::GetAccessor => (
            accessor.name,
            &accessor.parameters,
            accessor.type_,
            true,
            accessor.asterisk_token.is_none()
                && accessor.body.is_none()
                && accessor.end_flow_node.is_none()
                && accessor.flow_node.is_none()
                && accessor.full_signature.is_none()
                && accessor.next_container.is_none()
                && accessor.postfix_token.is_none()
                && accessor.symbol.is_none()
                && accessor.type_parameters.is_none()
                && accessor.facts == 0
                && accessor.modifiers.is_none(),
        ),
        NodeData::SetAccessorDeclaration(accessor) if record.kind == SyntaxKind::SetAccessor => (
            accessor.name,
            &accessor.parameters,
            accessor.type_,
            false,
            accessor.asterisk_token.is_none()
                && accessor.body.is_none()
                && accessor.end_flow_node.is_none()
                && accessor.flow_node.is_none()
                && accessor.full_signature.is_none()
                && accessor.next_container.is_none()
                && accessor.postfix_token.is_none()
                && accessor.symbol.is_none()
                && accessor.type_parameters.is_none()
                && accessor.facts == 0
                && accessor.modifiers.is_none(),
        ),
        _ => return Err(unsupported()),
    };
    if record.flags.0 != 0
        || record.parent != Some(owner.node)
        || !valid_payload
        || parameters.has_trailing_comma
        || parameters.range.start < record.range.start
        || parameters.range.end > record.range.end
        || getter && (!parameters.nodes.is_empty() || annotation.is_none())
        || !getter && (parameters.nodes.len() != 1 || annotation.is_some())
    {
        return Err(unsupported());
    }

    let name = NodeRef::new(declaration.arena, declaration.file, name_id);
    let name_record = preflight_node(store, host, name).map_err(|_| unsupported())?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported());
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || name_record.range.start < record.range.start
        || name_record.range.end > parameters.range.start
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(unsupported());
    }

    let bound = host.bound_file(declaration).ok_or_else(unsupported)?;
    let raw_symbol = bound.symbol(declaration).ok_or_else(unsupported)?;
    let symbol = store
        .get_merged_symbol(raw_symbol)
        .ok_or_else(unsupported)?;
    let accessor = store.symbol(symbol).ok_or_else(unsupported)?;
    let declarations = accessor.declarations().ok_or_else(unsupported)?;
    let expected_accessor = if getter {
        SymbolFlags::GET_ACCESSOR
    } else {
        SymbolFlags::SET_ACCESSOR
    };
    let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::ACCESSOR;
    if symbol != raw_symbol
        || !host.symbol_matches(store, declaration, symbol)
        || !accessor.flags().contains(expected_accessor)
        || accessor.flags().without(allowed_flags) != SymbolFlags::NONE
        || accessor.flags().contains(SymbolFlags::OPTIONAL)
            && !accessor.flags().contains(SymbolFlags::PROPERTY)
        || accessor.check_flags() != CheckFlags::NONE
        || accessor.name().as_utf8() != Some(identifier.text.as_str())
        || !declarations.contains(&declaration)
        || accessor.value_declaration() != declarations.first().copied()
        || accessor.members().is_some()
        || accessor.exports().is_some()
        || accessor.export_symbol().is_some()
        || accessor
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(owner_symbol)
    {
        return Err(unsupported());
    }

    let locals = bound
        .locals(declaration)
        .and_then(|locals| store.symbol_table(locals));
    let (type_node, parameter) = if getter {
        if locals.is_some_and(|locals| !locals.is_empty()) {
            return Err(unsupported());
        }
        let annotation = NodeRef::new(
            declaration.arena,
            declaration.file,
            annotation.expect("getter annotations were checked"),
        );
        let annotation_record =
            preflight_node(store, host, annotation).map_err(|_| unsupported())?;
        if annotation_record.flags.0 != 0
            || annotation_record.parent != Some(declaration.node)
            || annotation_record.range.start < parameters.range.end
            || annotation_record.range.end > record.range.end
        {
            return Err(unsupported());
        }
        (annotation, None)
    } else {
        let parameter = NodeRef::new(declaration.arena, declaration.file, parameters.nodes[0]);
        let parameter_record = preflight_node(store, host, parameter).map_err(|_| unsupported())?;
        let NodeData::ParameterDeclaration(data) = &parameter_record.data else {
            return Err(unsupported());
        };
        let parameter_name = NodeRef::new(parameter.arena, parameter.file, data.name);
        let parameter_name_record =
            preflight_node(store, host, parameter_name).map_err(|_| unsupported())?;
        let NodeData::Identifier(parameter_identifier) = &parameter_name_record.data else {
            return Err(unsupported());
        };
        let annotation = data
            .type_
            .map(|annotation| NodeRef::new(parameter.arena, parameter.file, annotation))
            .ok_or_else(unsupported)?;
        let annotation_record =
            preflight_node(store, host, annotation).map_err(|_| unsupported())?;
        let parameter_symbol = bound
            .symbol(parameter)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            .ok_or_else(unsupported)?;
        let parameter_owner = store.symbol(parameter_symbol).ok_or_else(unsupported)?;
        if parameter_record.kind != SyntaxKind::Parameter
            || parameter_record.flags.0 != 0
            || parameter_record.parent != Some(declaration.node)
            || parameter_record.range.start < parameters.range.start
            || parameter_record.range.end > parameters.range.end
            || data.dot_dot_dot_token.is_some()
            || data.initializer.is_some()
            || data.question_token.is_some()
            || data.symbol.is_some()
            || data.modifiers.is_some()
            || data.facts != 0
            || parameter_name_record.kind != SyntaxKind::Identifier
            || parameter_name_record.flags.0 != 0
            || parameter_name_record.parent != Some(parameter.node)
            || parameter_identifier.flow_node.is_some()
            || parameter_identifier.text.is_empty()
            || parameter_identifier.text == "this"
            || annotation_record.flags.0 != 0
            || annotation_record.parent != Some(parameter.node)
            || annotation_record.range.start < parameter_name_record.range.end
            || annotation_record.range.end > parameter_record.range.end
            || parameter_owner.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            || parameter_owner.check_flags() != CheckFlags::NONE
            || parameter_owner.name().as_utf8() != Some(parameter_identifier.text.as_str())
            || parameter_owner.declarations() != Some(&[parameter])
            || parameter_owner.value_declaration() != Some(parameter)
            || parameter_owner.members().is_some()
            || parameter_owner.exports().is_some()
            || parameter_owner.parent().is_some()
            || parameter_owner.export_symbol().is_some()
            || locals.is_none_or(|locals| {
                locals.len() != 1 || locals.get(parameter_owner.name()) != Some(parameter_symbol)
            })
            || store.get_merged_symbol(parameter_symbol) != Some(parameter_symbol)
        {
            return Err(unsupported());
        }
        (
            annotation,
            Some(PlannedCallParameter {
                symbol: parameter_symbol,
                type_node: annotation,
                identity_node: annotation,
                null_literal_identity: false,
                optional: false,
                implicit_any_rest: false,
            }),
        )
    };

    Ok(PlannedInterfaceAccessor {
        declaration,
        symbol,
        name_node: name,
        type_node,
        parameter,
    })
}

fn plan_interface_method(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: NodeRef,
    owner_symbol: SemanticSymbolId,
    declaration: NodeRef,
) -> Result<PlannedInterfaceMethod, PropertyObjectError> {
    let unsupported = || PropertyObjectError::UnsupportedMember {
        node: declaration,
        kind: SyntaxKind::MethodSignature,
    };
    let record = preflight_node(store, host, declaration).map_err(|_| unsupported())?;
    let NodeData::MethodSignatureDeclaration(method) = &record.data else {
        return Err(unsupported());
    };
    if record.kind != SyntaxKind::MethodSignature
        || record.flags.0 != 0
        || record.parent != Some(owner.node)
        || method.full_signature.is_some()
        || method.next_container.is_some()
        || method.postfix_token.is_some()
        || method.symbol.is_some()
        || method.modifiers.is_some()
        || method.parameters.has_trailing_comma
        || method.parameters.range.start < record.range.start
        || method.parameters.range.end > record.range.end
    {
        return Err(unsupported());
    }

    let name = NodeRef::new(declaration.arena, declaration.file, method.name);
    let name_record = preflight_node(store, host, name).map_err(|_| unsupported())?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported());
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || name_record.range.start < record.range.start
        || name_record.range.end > method.parameters.range.start
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(unsupported());
    }

    let return_type = method
        .type_
        .map(|type_| NodeRef::new(declaration.arena, declaration.file, type_))
        .ok_or_else(unsupported)?;
    let return_record = preflight_node(store, host, return_type).map_err(|_| unsupported())?;
    if return_record.flags.0 != 0
        || return_record.parent != Some(declaration.node)
        || return_record.range.start < method.parameters.range.end
        || return_record.range.end > record.range.end
    {
        return Err(unsupported());
    }

    let bound = host.bound_file(declaration).ok_or_else(unsupported)?;
    let raw_symbol = bound.symbol(declaration).ok_or_else(unsupported)?;
    let symbol = store
        .get_merged_symbol(raw_symbol)
        .ok_or_else(unsupported)?;
    let method_symbol = store.symbol(symbol).ok_or_else(unsupported)?;
    let declarations = method_symbol.declarations().ok_or_else(unsupported)?;
    if symbol != raw_symbol
        || !host.symbol_matches(store, declaration, symbol)
        || method_symbol.flags() != SymbolFlags::METHOD
        || method_symbol.check_flags() != CheckFlags::NONE
        || method_symbol.name().as_utf8() != Some(identifier.text.as_str())
        || !declarations.contains(&declaration)
        || method_symbol.value_declaration() != declarations.first().copied()
        || method_symbol.members().is_some()
        || method_symbol.exports().is_some()
        || method_symbol.export_symbol().is_some()
        || method_symbol
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(owner_symbol)
    {
        return Err(unsupported());
    }

    let locals = bound
        .locals(declaration)
        .and_then(|locals| store.symbol_table(locals));
    let type_parameters = plan_declared_signature_type_parameters(
        store,
        host,
        declaration,
        method.type_parameters.as_ref(),
        &method.parameters,
        locals,
        SyntaxKind::MethodSignature,
    )?;
    if method.parameters.nodes.is_empty() && type_parameters.is_empty() {
        if locals.is_some_and(|locals| !locals.is_empty()) {
            return Err(unsupported());
        }
    } else if locals.is_none() {
        return Err(unsupported());
    }
    let mut parameters = Vec::new();
    parameters
        .try_reserve_exact(method.parameters.nodes.len())
        .map_err(|_| PropertyObjectError::Capacity(declaration))?;
    let mut flags = SignatureFlags::NONE;
    let mut previous_end = method.parameters.range.start;
    let mut minimum_argument_count = 0usize;
    let mut optional_parameter_seen = false;
    let numeric_math_rest = matches!(identifier.text.as_str(), "max" | "min" | "hypot")
        && bound.source_facts().is_some_and(|facts| {
            facts.is_declaration_file()
                && facts.is_default_library()
                && !facts.is_javascript_file()
                && !facts.is_external_or_common_js_module()
        })
        && store
            .symbol(owner_symbol)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            .is_some_and(|declaration| {
                authenticated_global_math_value_declaration(store, host, owner_symbol, declaration)
            });
    for (index, parameter) in method.parameters.nodes.iter().copied().enumerate() {
        let parameter = NodeRef::new(declaration.arena, declaration.file, parameter);
        let parameter_record = preflight_node(store, host, parameter).map_err(|_| unsupported())?;
        if parameter_record.range.start < previous_end {
            return Err(unsupported());
        }
        previous_end = parameter_record.range.end;
        let (planned, rest, optional) = plan_interface_method_parameter(
            store,
            host,
            declaration,
            parameter,
            &method.parameters,
            numeric_math_rest,
        )?;
        if rest && (optional || index + 1 != method.parameters.nodes.len())
            || !rest && !optional && optional_parameter_seen
        {
            return Err(unsupported());
        }
        if rest {
            flags |= SignatureFlags::HAS_REST_PARAMETER;
        } else if optional {
            optional_parameter_seen = true;
        } else {
            minimum_argument_count += 1;
        }
        let symbol = store.symbol(planned.symbol).ok_or_else(unsupported)?;
        if locals.and_then(|locals| locals.get(symbol.name())) != Some(planned.symbol)
            || parameters
                .iter()
                .any(|parameter: &PlannedCallParameter| parameter.symbol == planned.symbol)
        {
            return Err(unsupported());
        }
        parameters.push(planned);
    }
    if locals.is_some_and(|locals| locals.len() != parameters.len() + type_parameters.len())
        || i32::try_from(parameters.len()).is_err()
    {
        return Err(unsupported());
    }

    Ok(PlannedInterfaceMethod {
        declaration,
        symbol,
        type_parameters,
        parameters,
        return_type,
        flags,
        minimum_argument_count,
    })
}

#[allow(clippy::too_many_lines)] // Binder, syntax, constraints, and defaults share one proof.
fn plan_declared_signature_type_parameters(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    parameters: Option<&NodeList>,
    value_parameters: &NodeList,
    locals: Option<&ts_binder::semantic::SymbolTable>,
    kind: SyntaxKind,
) -> Result<Vec<PlannedInterfaceMethodTypeParameter>, PropertyObjectError> {
    let unsupported = || PropertyObjectError::UnsupportedMember {
        node: declaration,
        kind,
    };
    let Some(parameters) = parameters else {
        return Ok(Vec::new());
    };
    let declaration_record = preflight_node(store, host, declaration).map_err(|_| unsupported())?;
    if parameters.nodes.is_empty()
        || parameters.has_trailing_comma
        || parameters.range.start < declaration_record.range.start
        || parameters.range.end > value_parameters.range.start
        || parameters.range.start >= parameters.range.end
        || locals.is_none()
    {
        return Err(unsupported());
    }

    let mut planned = Vec::with_capacity(parameters.nodes.len());
    let mut symbols = HashSet::with_capacity(parameters.nodes.len());
    let mut names = HashSet::with_capacity(parameters.nodes.len());
    let mut checked = HashSet::with_capacity(parameters.nodes.len());
    let mut previous_end = parameters.range.start;
    let mut default_seen = false;
    for parameter in &parameters.nodes {
        let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter);
        let record = preflight_node(store, host, parameter).map_err(|_| unsupported())?;
        let NodeData::TypeParameterDeclaration(data) = &record.data else {
            return Err(unsupported());
        };
        if record.kind != SyntaxKind::TypeParameter
            || record.flags.0 != 0
            || record.parent != Some(declaration.node)
            || record.range.start < previous_end
            || record.range.start < parameters.range.start
            || record.range.end > parameters.range.end
            || data.expression.is_some()
            || data.symbol.is_some()
            || data.modifiers.is_some()
        {
            return Err(unsupported());
        }

        let name = NodeRef::new(parameter.arena, parameter.file, data.name);
        let name_record = preflight_node(store, host, name).map_err(|_| unsupported())?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(unsupported());
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || name_record.parent != Some(parameter.node)
            || name_record.range.start < record.range.start
            || name_record.range.end > record.range.end
            || identifier.text.is_empty()
            || identifier.flow_node.is_some()
            || !names.insert(identifier.text.as_str())
        {
            return Err(unsupported());
        }

        let symbol = bound_symbol(store, host, parameter).ok_or_else(unsupported)?;
        preflight_type_parameter_symbol(store, host, symbol, &mut checked)
            .map_err(|_| unsupported())?;
        let symbol_record = store.symbol(symbol).ok_or_else(unsupported)?;
        if symbol_record.flags() != SymbolFlags::TYPE_PARAMETER
            || symbol_record.check_flags() != CheckFlags::NONE
            || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
            || symbol_record.declarations() != Some(&[parameter])
            || symbol_record.value_declaration().is_some()
            || symbol_record.members().is_some()
            || symbol_record.exports().is_some()
            || symbol_record.parent().is_some()
            || symbol_record.export_symbol().is_some()
            || locals.and_then(|locals| locals.get(symbol_record.name())) != Some(symbol)
            || !symbols.insert(symbol)
        {
            return Err(unsupported());
        }

        let constraint = data
            .constraint
            .map(|node| NodeRef::new(parameter.arena, parameter.file, node));
        let default_type = data
            .default_type
            .map(|node| NodeRef::new(parameter.arena, parameter.file, node));
        let mut previous_child_end = name_record.range.end;
        for annotation in [constraint, default_type].into_iter().flatten() {
            let annotation_record =
                preflight_node(store, host, annotation).map_err(|_| unsupported())?;
            if annotation_record.flags.0 != 0
                || annotation_record.parent != Some(parameter.node)
                || annotation_record.range.start < previous_child_end
                || annotation_record.range.end > record.range.end
            {
                return Err(unsupported());
            }
            previous_child_end = annotation_record.range.end;
        }
        if default_seen && default_type.is_none() {
            return Err(unsupported());
        }
        default_seen |= default_type.is_some();
        planned.push(PlannedInterfaceMethodTypeParameter {
            declaration: parameter,
            symbol,
            constraint,
            default_type,
        });
        previous_end = record.range.end;
    }
    Ok(planned)
}

/// Returns every overload when `node` is a generic interface method return.
///
/// Source checking resolves generic interface members through their property
/// annotations, so the first overload must also expose its sibling signatures.
pub(super) fn plan_enclosing_generic_interface_methods(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<Vec<PlannedInterfaceMethod>, PropertyObjectError> {
    let Ok(record) = preflight_node(store, host, node) else {
        return Ok(Vec::new());
    };
    let Some(parent) = record.parent else {
        return Ok(Vec::new());
    };
    let declaration = NodeRef::new(node.arena, node.file, parent);
    let Ok(method_record) = preflight_node(store, host, declaration) else {
        return Ok(Vec::new());
    };
    let NodeData::MethodSignatureDeclaration(method) = &method_record.data else {
        return Ok(Vec::new());
    };
    if method.type_ != Some(node.node) {
        return Ok(Vec::new());
    }
    let Some(owner) = method_record.parent else {
        return Ok(Vec::new());
    };
    let owner = NodeRef::new(node.arena, node.file, owner);
    let Ok(owner_record) = preflight_node(store, host, owner) else {
        return Ok(Vec::new());
    };
    let NodeData::InterfaceDeclaration(interface) = &owner_record.data else {
        return Ok(Vec::new());
    };
    if interface.type_parameters.is_none() {
        return Ok(Vec::new());
    }
    let Some(owner_symbol) = bound_symbol(store, host, owner) else {
        return Err(PropertyObjectError::UnsupportedMember {
            node: declaration,
            kind: SyntaxKind::MethodSignature,
        });
    };
    let method_symbol =
        bound_symbol(store, host, declaration).ok_or(PropertyObjectError::UnsupportedMember {
            node: declaration,
            kind: SyntaxKind::MethodSignature,
        })?;
    let plan = plan_generic_interface(store, host, owner_symbol)?;
    Ok(plan
        .methods
        .into_iter()
        .filter(|method| method.symbol == method_symbol)
        .collect())
}

fn valid_declared_rest_parameter_annotation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    numeric_math_rest: bool,
) -> bool {
    let Ok(record) = preflight_node(store, host, node) else {
        return false;
    };
    match &record.data {
        NodeData::ArrayTypeNode(array) if record.kind == SyntaxKind::ArrayType => {
            let element = NodeRef::new(node.arena, node.file, array.element_type);
            preflight_node(store, host, element).is_ok_and(|element| {
                (!numeric_math_rest || element.kind == SyntaxKind::NumberKeyword)
                    && element.flags.0 == 0
                    && element.parent == Some(node.node)
                    && element.range.start == record.range.start
                    && element.range.end <= record.range.end
            })
        }
        NodeData::TupleTypeNode(tuple)
            if !numeric_math_rest && record.kind == SyntaxKind::TupleType =>
        {
            tuple.elements.range == record.range
        }
        NodeData::UnionTypeNode(union)
            if !numeric_math_rest && record.kind == SyntaxKind::UnionType =>
        {
            if union.types.nodes.len() < 2
                || union.types.has_trailing_comma
                || union.types.range != record.range
            {
                return false;
            }

            let mut previous_end = record.range.start;
            union.types.nodes.iter().all(|constituent| {
                let constituent = NodeRef::new(node.arena, node.file, *constituent);
                let Ok(constituent_record) = preflight_node(store, host, constituent) else {
                    return false;
                };
                let NodeData::TupleTypeNode(tuple) = &constituent_record.data else {
                    return false;
                };
                if constituent_record.kind != SyntaxKind::TupleType
                    || constituent_record.flags.0 != 0
                    || constituent_record.parent != Some(node.node)
                    || constituent_record.range.start < previous_end
                    || constituent_record.range.start < record.range.start
                    || constituent_record.range.end > record.range.end
                    || tuple.elements.range != constituent_record.range
                {
                    return false;
                }
                previous_end = constituent_record.range.end;
                true
            })
        }
        NodeData::InferTypeNode(inferred)
            if !numeric_math_rest && record.kind == SyntaxKind::InferType =>
        {
            let parameter = NodeRef::new(node.arena, node.file, inferred.type_parameter);
            preflight_node(store, host, parameter).is_ok_and(|parameter| {
                parameter.kind == SyntaxKind::TypeParameter
                    && parameter.flags.0 == 0
                    && parameter.parent == Some(node.node)
            })
        }
        _ => false,
    }
}

fn plan_interface_method_parameter(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    method: NodeRef,
    declaration: NodeRef,
    parameter_nodes: &NodeList,
    numeric_math_rest: bool,
) -> Result<(PlannedCallParameter, bool, bool), PropertyObjectError> {
    let unsupported = || PropertyObjectError::UnsupportedMember {
        node: method,
        kind: SyntaxKind::MethodSignature,
    };
    let record = preflight_node(store, host, declaration).map_err(|_| unsupported())?;
    let NodeData::ParameterDeclaration(parameter) = &record.data else {
        return Err(unsupported());
    };
    if record.kind != SyntaxKind::Parameter
        || record.flags.0 != 0
        || record.parent != Some(method.node)
        || record.range.start < parameter_nodes.range.start
        || record.range.end > parameter_nodes.range.end
        || parameter.initializer.is_some()
        || parameter.symbol.is_some()
        || parameter.modifiers.is_some()
        || parameter.facts != 0
    {
        return Err(unsupported());
    }
    let rest = parameter
        .dot_dot_dot_token
        .map(|rest| NodeRef::new(declaration.arena, declaration.file, rest));
    let rest_end = if let Some(rest) = rest {
        let rest_record = preflight_node(store, host, rest).map_err(|_| unsupported())?;
        if rest_record.kind != SyntaxKind::DotDotDotToken
            || rest_record.flags.0 != 0
            || rest_record.parent != Some(declaration.node)
            || rest_record.range.start < record.range.start
            || !matches!(rest_record.data, NodeData::Token(_))
        {
            return Err(unsupported());
        }
        rest_record.range.end
    } else {
        record.range.start
    };

    let name = NodeRef::new(declaration.arena, declaration.file, parameter.name);
    let name_record = preflight_node(store, host, name).map_err(|_| unsupported())?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported());
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || name_record.range.start < rest_end
        || name_record.range.end > record.range.end
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || identifier.text == "this"
    {
        return Err(unsupported());
    }

    let type_node = parameter
        .type_
        .map(|type_| NodeRef::new(declaration.arena, declaration.file, type_))
        .ok_or_else(unsupported)?;
    let type_record = preflight_node(store, host, type_node).map_err(|_| unsupported())?;
    if type_record.flags.0 != 0
        || type_record.parent != Some(declaration.node)
        || type_record.range.start < name_record.range.end
        || type_record.range.end > record.range.end
    {
        return Err(unsupported());
    }
    let optional = if let Some(token) = parameter.question_token {
        let token = NodeRef::new(declaration.arena, declaration.file, token);
        let token_record = preflight_node(store, host, token).map_err(|_| unsupported())?;
        if token_record.kind != SyntaxKind::QuestionToken
            || token_record.flags.0 != 0
            || token_record.parent != Some(declaration.node)
            || token_record.range.start < name_record.range.end
            || token_record.range.end > type_record.range.start
            || !matches!(token_record.data, NodeData::Token(_))
        {
            return Err(unsupported());
        }
        true
    } else {
        false
    };
    if rest.is_some()
        && !valid_declared_rest_parameter_annotation(store, host, type_node, numeric_math_rest)
    {
        return Err(unsupported());
    }

    let bound = host.bound_file(declaration).ok_or_else(unsupported)?;
    let raw_symbol = bound.symbol(declaration).ok_or_else(unsupported)?;
    let symbol = store
        .get_merged_symbol(raw_symbol)
        .ok_or_else(unsupported)?;
    let symbol_record = store.symbol(symbol).ok_or_else(unsupported)?;
    if symbol != raw_symbol
        || symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || symbol_record.declarations() != Some(&[declaration])
        || symbol_record.value_declaration() != Some(declaration)
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent().is_some()
        || symbol_record.export_symbol().is_some()
    {
        return Err(unsupported());
    }

    let identity_node = peel_parenthesized_type(store, host, type_node)?;
    Ok((
        PlannedCallParameter {
            symbol,
            type_node,
            identity_node,
            null_literal_identity: is_null_literal_type(store, host, identity_node)?,
            optional,
            implicit_any_rest: false,
        },
        rest.is_some(),
        optional,
    ))
}

fn plan_call_signature(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: NodeRef,
    owner_symbol: SemanticSymbolId,
    declaration: NodeRef,
) -> Result<PlannedCallSignature, PropertyObjectError> {
    let syntax_kind = store
        .source_node_kind(declaration)
        .unwrap_or(SyntaxKind::CallSignature);
    let unsupported = || PropertyObjectError::UnsupportedMember {
        node: declaration,
        kind: syntax_kind,
    };
    let record = preflight_node(store, host, declaration).map_err(|_| unsupported())?;
    let (
        full_signature,
        next_container,
        signature_symbol,
        declared_type_parameters,
        parameter_nodes,
        type_,
    ) = match &record.data {
        NodeData::CallSignatureDeclaration(call) if record.kind == SyntaxKind::CallSignature => (
            call.full_signature,
            call.next_container,
            call.symbol,
            call.type_parameters.as_ref(),
            &call.parameters,
            call.type_,
        ),
        NodeData::ConstructSignatureDeclaration(construct)
            if record.kind == SyntaxKind::ConstructSignature =>
        {
            (
                construct.full_signature,
                construct.next_container,
                construct.symbol,
                construct.type_parameters.as_ref(),
                &construct.parameters,
                construct.type_,
            )
        }
        _ => return Err(unsupported()),
    };
    let is_construct = record.kind == SyntaxKind::ConstructSignature;
    let type_literal_call =
        !is_construct && store.source_node_kind(owner) == Some(SyntaxKind::TypeLiteral);
    if record.parent != Some(owner.node)
        || record.flags.0 != 0
        || full_signature.is_some()
        || next_container.is_some()
        || signature_symbol.is_some()
        || parameter_nodes.has_trailing_comma
        || parameter_nodes.range.start < record.range.start
        || parameter_nodes.range.end > record.range.end
    {
        return Err(unsupported());
    }
    let implicit_any_return = type_.is_none()
        && (type_literal_call
            || is_construct
                && store.source_node_kind(owner) == Some(SyntaxKind::InterfaceDeclaration));
    let return_type = match type_ {
        Some(return_id) => {
            let return_type = NodeRef::new(declaration.arena, declaration.file, return_id);
            let return_record =
                preflight_node(store, host, return_type).map_err(|_| unsupported())?;
            if return_record.parent != Some(declaration.node)
                || return_record.range.start < parameter_nodes.range.end
                || return_record.range.end > record.range.end
            {
                return Err(unsupported());
            }
            return_type
        }
        None if implicit_any_return => declaration,
        None => return Err(unsupported()),
    };

    let bound = host.bound_file(declaration).ok_or_else(unsupported)?;
    let raw_call_symbol = bound.symbol(declaration).ok_or_else(unsupported)?;
    let call_symbol = store
        .get_merged_symbol(raw_call_symbol)
        .ok_or_else(unsupported)?;
    let call_record = store.symbol(call_symbol).ok_or_else(unsupported)?;
    if call_symbol != raw_call_symbol
        || call_record.flags() != SymbolFlags::SIGNATURE
        || call_record.check_flags() != CheckFlags::NONE
        || call_record.name()
            != if is_construct {
                InternalSymbolName::New
            } else {
                InternalSymbolName::Call
            }
            .as_ref()
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
    let type_parameters = plan_declared_signature_type_parameters(
        store,
        host,
        declaration,
        declared_type_parameters,
        parameter_nodes,
        locals,
        syntax_kind,
    )?;
    if parameter_nodes.nodes.is_empty() && type_parameters.is_empty() {
        if locals.is_some_and(|locals| !locals.is_empty()) {
            return Err(unsupported());
        }
    } else if locals.is_none() {
        return Err(unsupported());
    }

    let mut parameters = Vec::with_capacity(parameter_nodes.nodes.len());
    let mut previous_end = parameter_nodes.range.start;
    let mut flags = if is_construct {
        SignatureFlags::CONSTRUCT
    } else {
        SignatureFlags::NONE
    };
    let mut optional_seen = false;
    for (index, parameter_id) in parameter_nodes.nodes.iter().enumerate() {
        let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter_id);
        let parameter_record = preflight_node(store, host, parameter).map_err(|_| unsupported())?;
        let NodeData::ParameterDeclaration(data) = &parameter_record.data else {
            return Err(unsupported());
        };
        if parameter_record.kind != SyntaxKind::Parameter
            || parameter_record.parent != Some(declaration.node)
            || parameter_record.flags.0 != 0
            || parameter_record.range.start < previous_end
            || parameter_record.range.start < parameter_nodes.range.start
            || parameter_record.range.end > parameter_nodes.range.end
            || data.initializer.is_some()
            || data.symbol.is_some()
            || data.facts != 0
            || data.modifiers.is_some()
        {
            return Err(unsupported());
        }
        previous_end = parameter_record.range.end;
        let rest = data
            .dot_dot_dot_token
            .map(|token| NodeRef::new(parameter.arena, parameter.file, token));
        let rest_end = if let Some(rest) = rest {
            let rest_record = preflight_node(store, host, rest).map_err(|_| unsupported())?;
            if rest_record.kind != SyntaxKind::DotDotDotToken
                || rest_record.flags.0 != 0
                || rest_record.parent != Some(parameter.node)
                || rest_record.range.start < parameter_record.range.start
                || !matches!(rest_record.data, NodeData::Token(_))
            {
                return Err(unsupported());
            }
            rest_record.range.end
        } else {
            parameter_record.range.start
        };
        let name = NodeRef::new(parameter.arena, parameter.file, data.name);
        let name_record = preflight_node(store, host, name).map_err(|_| unsupported())?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(unsupported());
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.parent != Some(parameter.node)
            || name_record.range.start < rest_end
            || name_record.range.end > parameter_record.range.end
            || identifier.text.is_empty()
            || identifier.text == "this"
        {
            return Err(unsupported());
        }
        let implicit_any_rest =
            type_literal_call && data.dot_dot_dot_token.is_some() && data.type_.is_none();
        let (type_node, type_start, literal_type) = match data.type_ {
            Some(type_id) => {
                let type_node = NodeRef::new(parameter.arena, parameter.file, type_id);
                let type_record =
                    preflight_node(store, host, type_node).map_err(|_| unsupported())?;
                if type_record.parent != Some(parameter.node)
                    || type_record.range.start < name_record.range.end
                    || type_record.range.end > parameter_record.range.end
                {
                    return Err(unsupported());
                }
                (
                    type_node,
                    type_record.range.start,
                    type_record.kind == SyntaxKind::LiteralType,
                )
            }
            None if implicit_any_rest => {
                let dependency = parameters
                    .last()
                    .map(|previous: &PlannedCallParameter| previous.type_node)
                    .or((!implicit_any_return).then_some(return_type))
                    .ok_or_else(unsupported)?;
                if implicit_any_array_type(store).is_none() {
                    return Err(unsupported());
                }
                (dependency, parameter_record.range.end, false)
            }
            None => return Err(unsupported()),
        };
        if let Some(token) = data.dot_dot_dot_token {
            let token = NodeRef::new(parameter.arena, parameter.file, token);
            let token_record = preflight_node(store, host, token).map_err(|_| unsupported())?;
            if index + 1 != parameter_nodes.nodes.len()
                || token_record.kind != SyntaxKind::DotDotDotToken
                || !matches!(token_record.data, NodeData::Token(_))
                || token_record.flags.0 != 0
                || token_record.parent != Some(parameter.node)
                || token_record.range.start < parameter_record.range.start
                || token_record.range.end > name_record.range.start
                || !implicit_any_rest
                    && !valid_declared_rest_parameter_annotation(store, host, type_node, false)
            {
                return Err(unsupported());
            }
            flags |= SignatureFlags::HAS_REST_PARAMETER;
        }
        let optional = if let Some(token) = data.question_token {
            let token = NodeRef::new(parameter.arena, parameter.file, token);
            let token_record = preflight_node(store, host, token).map_err(|_| unsupported())?;
            if !is_construct && !type_literal_call
                || rest.is_some()
                || token_record.kind != SyntaxKind::QuestionToken
                || !matches!(token_record.data, NodeData::Token(_))
                || token_record.flags.0 != 0
                || token_record.parent != Some(parameter.node)
                || token_record.range.start < name_record.range.end
                || token_record.range.end > type_start
                || preflight_node(store, host, type_node)
                    .map_err(|_| unsupported())?
                    .kind
                    != SyntaxKind::AnyKeyword
                || !matches!(
                    preflight_node(store, host, type_node)
                        .map_err(|_| unsupported())?
                        .data,
                    NodeData::KeywordTypeNode(_)
                )
            {
                return Err(unsupported());
            }
            true
        } else {
            false
        };
        if optional_seen && !optional && (rest.is_none() || implicit_any_rest)
            || implicit_any_rest && optional
        {
            return Err(unsupported());
        }
        optional_seen |= optional;
        if literal_type {
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
        let identity_node = if implicit_any_rest {
            name
        } else {
            peel_parenthesized_type(store, host, type_node)?
        };
        parameters.push(PlannedCallParameter {
            symbol: parameter_symbol,
            type_node,
            identity_node,
            null_literal_identity: !implicit_any_rest
                && is_null_literal_type(store, host, identity_node)?,
            optional,
            implicit_any_rest,
        });
    }
    if locals.is_some_and(|locals| locals.len() != parameters.len() + type_parameters.len()) {
        return Err(unsupported());
    }
    if i32::try_from(parameters.len()).is_err() {
        return Err(unsupported());
    }
    let return_identity_node = if implicit_any_return {
        declaration
    } else {
        peel_parenthesized_type(store, host, return_type)?
    };
    Ok(PlannedCallSignature {
        declaration,
        symbol: call_symbol,
        type_parameters,
        parameters,
        return_type,
        return_identity_node,
        return_null_literal_identity: !implicit_any_return
            && is_null_literal_type(store, host, return_identity_node)?,
        flags,
        implicit_any_return,
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
        SyntaxKind::StringKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::TemplateLiteralType
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
        || index_record
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(owner_symbol)
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

    let value_type_parameter = match &value_record.data {
        NodeData::TypeReferenceNode(reference) if reference.type_arguments.is_none() => {
            let name = NodeRef::new(
                value_type_node.arena,
                value_type_node.file,
                reference.type_name,
            );
            let name_record = preflight_node(store, host, name).map_err(|_| unsupported())?;
            if let NodeData::Identifier(identifier) = &name_record.data
                && name_record.kind == SyntaxKind::Identifier
                && name_record.flags.0 == 0
                && name_record.parent == Some(value_type_node.node)
                && identifier.flow_node.is_none()
            {
                store
                    .symbol(owner_symbol)
                    .and_then(ts_binder::semantic::Symbol::members)
                    .and_then(|members| store.symbol_table(members))
                    .and_then(|members| members.get_source(&identifier.text))
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    .filter(|symbol| {
                        store.symbol(*symbol).is_some_and(|record| {
                            record.flags().contains(SymbolFlags::TYPE_PARAMETER)
                                && record
                                    .flags()
                                    .without(SymbolFlags::TYPE_PARAMETER | SymbolFlags::TRANSIENT)
                                    == SymbolFlags::NONE
                                && store.get_parent_of_symbol(*symbol) == Some(owner_symbol)
                        })
                    })
            } else {
                None
            }
        }
        _ => None,
    };

    Ok(PlannedIndexSignature {
        declaration,
        symbol: index_symbol,
        key_type_node,
        value_type_node,
        readonly,
        value_type_parameter,
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
    if is_javascript_expando_object_plan(store, plan) {
        return javascript_expando_object_state(store, plan);
    }
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
    if !plan.spreads.is_empty()
        && store
            .intrinsic_bootstrap()
            .is_some_and(|bootstrap| type_ == bootstrap.any_type)
        && unresolved_property_links(store, plan)
    {
        return Ok(Some(PropertyObjectState::Resolved(type_)));
    }
    if store
        .type_payload(type_)
        .is_some_and(|record| record.symbol().is_none())
        && synthetic_object_literal_matches_plan(store, plan, type_)
    {
        return Ok(Some(PropertyObjectState::Resolved(type_)));
    }
    match validate_object_record(store, plan, type_) {
        Some(state @ PropertyObjectState::Resolved(_)) => Ok(Some(state)),
        _ => Err(invalid_cache(plan, type_)),
    }
}

pub(super) fn is_javascript_expando_object_plan(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
) -> bool {
    plan.kind == PropertyObjectKind::ObjectLiteral
        && plan.members.is_some()
        && store.symbol(plan.symbol).is_some_and(|owner| {
            owner.flags() == SymbolFlags::OBJECT_LITERAL
                && owner.members().is_none()
                && owner.exports() == plan.members
        })
}

fn javascript_expando_object_state(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
) -> Result<Option<PropertyObjectState>, PropertyObjectError> {
    let Some(links) = store.type_node_links(plan.node) else {
        return if plan.properties.iter().all(|property| {
            store
                .value_symbol_links(property.symbol)
                .is_none_or(|links| links == &ValueSymbolLinks::default())
        }) {
            Ok(None)
        } else {
            Err(PropertyObjectError::InvalidObjectLiteral(plan.node))
        };
    };
    let Some(type_) = links.resolved_type else {
        return Err(PropertyObjectError::InvalidObjectLiteral(plan.node));
    };
    if links.outer_type_parameters.is_some() {
        return Err(invalid_cache(plan, type_));
    }
    let record = store
        .type_payload(type_)
        .ok_or_else(|| invalid_cache(plan, type_))?;
    let TypeData::Object(object) = record.data() else {
        return Err(invalid_cache(plan, type_));
    };
    let properties = object.structured.properties.as_deref().unwrap_or_default();
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.symbol() != Some(plan.symbol)
        || record.alias().is_some()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
        || object.structured.members != plan.members
        || properties.len() != plan.properties.len()
        || object.structured.signatures.is_some()
        || object.structured.call_signature_count != 0
        || object.structured.index_infos.is_some()
        || plan
            .properties
            .iter()
            .zip(properties)
            .any(|(planned, actual)| {
                planned.symbol != *actual
                    || store
                        .value_symbol_links(planned.symbol)
                        .is_none_or(|links| {
                            links.resolved_type.is_none()
                                || links
                                    != &(ValueSymbolLinks {
                                        resolved_type: links.resolved_type,
                                        ..ValueSymbolLinks::default()
                                    })
                                || links
                                    .resolved_type
                                    .is_some_and(|type_| store.type_payload(type_).is_none())
                        })
            })
    {
        return Err(invalid_cache(plan, type_));
    }
    Ok(Some(PropertyObjectState::Resolved(type_)))
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
                valid_declared_property_check_flags(store, property)
                    && expected_declared_property_links(store, plan, property, *type_).as_ref()
                        == store.value_symbol_links(property.symbol)
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
        if store
            .symbol(property.symbol)
            .is_some_and(|symbol| symbol.flags().contains(SymbolFlags::METHOD))
        {
            assert_eq!(
                resolved_interface_method_value(store, plan, property.symbol),
                Some(*property_type),
                "the direct-interface plan validated its method callable"
            );
            continue;
        }
        let accessor = store
            .symbol(property.symbol)
            .is_some_and(|symbol| symbol.flags().intersects(SymbolFlags::ACCESSOR));
        if !accessor {
            assert!(
                store.set_source_property_readonly(property.symbol, property.readonly),
                "the direct-interface plan validated a bound source property"
            );
        }
        assert!(
            store.set_value_symbol_links(
                property.symbol,
                expected_declared_property_links(store, plan, property, *property_type)
                    .expect("the direct-interface plan validated its accessor write annotation"),
            )
        );
    }
    for accessor in &plan.accessors {
        if let Some(parameter) = accessor.parameter {
            let type_ = cached_planned_type_identity(store, parameter.type_node)
                .expect("the direct-interface plan resolved its setter annotation");
            assert!(store.set_value_symbol_links(
                parameter.symbol,
                ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                },
            ));
        }
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
    let owner = store.symbol(plan.symbol)?;
    let exact_declarations = owner
        .declarations()?
        .iter()
        .copied()
        .filter(|declaration| {
            store.source_node_kind(*declaration) == Some(SyntaxKind::InterfaceDeclaration)
        })
        .eq(plan.declarations.iter().copied());
    if record.flags() != TypeFlags::OBJECT
        || record.symbol() != Some(plan.symbol)
        || record.alias().is_some()
        || !exact_declarations
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
    let resolved_signatures = resolved_call_signature_ids(store, plan);
    let call_signature_count = plan
        .call_signatures
        .iter()
        .filter(|signature| !signature.is_construct())
        .count();
    let expected_calls = resolved_signatures
        .as_deref()
        .filter(|_| call_signature_count != 0)
        .map(|signatures| &signatures[..call_signature_count]);
    let expected_constructs = resolved_signatures
        .as_deref()
        .filter(|signatures| signatures.len() != call_signature_count)
        .map(|signatures| &signatures[call_signature_count..]);
    if record.object_flags() == ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
        && interface.base_types_resolved
        && interface.resolved_base_constructor_type.is_none()
        && interface.resolved_base_types.is_none()
        && interface.declared_members_resolved
        && interface.declared_members == plan.members
        && interface.declared_call_signatures.as_deref() == expected_calls
        && interface.declared_construct_signatures.as_deref() == expected_constructs
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
/// Namespace-owned interfaces additionally require their exact export edge.
pub(super) fn validate_resolved_declared_property_object(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> DeclaredPropertyObjectValidation {
    match validate_resolved_declared_property_object_detailed(store, type_) {
        DetailedDeclaredPropertyObjectValidation::Valid(proof) => {
            DeclaredPropertyObjectValidation::Valid(proof)
        }
        DetailedDeclaredPropertyObjectValidation::TraversableBoundary(
            DeclaredPropertyObjectProof::Interface,
        ) if authenticated_namespace_declared_property_interface(store, type_) => {
            DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::Interface)
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

fn authenticated_merged_react_declared_property_interface(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
) -> bool {
    let Some(interface) = store.symbol(owner) else {
        return false;
    };
    let Some(declarations) = interface
        .declarations()
        .filter(|declarations| declarations.len() > 1)
    else {
        return false;
    };
    let Some(namespace) = store.get_parent_of_symbol(owner) else {
        return false;
    };
    let Some(namespace_record) = store.symbol(namespace) else {
        return false;
    };
    let Some(namespace_declarations) = namespace_record.declarations() else {
        return false;
    };
    if interface.flags() != SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT
        || interface.check_flags() != CheckFlags::NONE
        || interface.value_declaration().is_some()
        || interface.exports().is_some()
        || interface.export_symbol().is_some()
        || interface
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(namespace)
        || store.get_merged_symbol(owner) != Some(owner)
        || namespace_record.name().as_utf8() != Some("React")
        || !namespace_record.flags().intersects(SymbolFlags::NAMESPACE)
        || namespace_record.check_flags() != CheckFlags::NONE
        || store.get_merged_symbol(namespace) != Some(namespace)
        || namespace_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(interface.name()))
            .and_then(|export| store.get_merged_symbol(export))
            != Some(owner)
    {
        return false;
    }

    let mut seen_declarations = HashSet::with_capacity(declarations.len());
    if !declarations.iter().all(|declaration| {
        let Some(SourceNodeParent::Parent(block)) = store.source_node_parent(*declaration) else {
            return false;
        };
        let Some(SourceNodeParent::Parent(module)) = store.source_node_parent(block) else {
            return false;
        };
        seen_declarations.insert(*declaration)
            && store.source_node_kind(*declaration) == Some(SyntaxKind::InterfaceDeclaration)
            && store.source_node_kind(block) == Some(SyntaxKind::ModuleBlock)
            && store.source_node_kind(module) == Some(SyntaxKind::ModuleDeclaration)
            && namespace_declarations.contains(&module)
    }) {
        return false;
    }

    interface.members().is_none_or(|members| {
        store.symbol_table(members).is_some_and(|members| {
            members.iter().all(|(name, member)| {
                store.symbol(member).is_some_and(|record| {
                    record.name() == name
                        && store.get_merged_symbol(member) == Some(member)
                        && store.get_parent_of_symbol(member) == Some(owner)
                        && record.declarations().is_some_and(|member_declarations| {
                            !member_declarations.is_empty()
                                && member_declarations.iter().all(|declaration| {
                                    matches!(
                                        store.source_node_parent(*declaration),
                                        Some(SourceNodeParent::Parent(parent))
                                            if declarations.contains(&parent)
                                    )
                                })
                        })
                })
            })
        })
    })
}

fn authenticated_namespace_declared_property_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> bool {
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    let Some(owner) = record.symbol() else {
        return false;
    };
    let Some(interface) = store.symbol(owner) else {
        return false;
    };
    let Some(namespace) = store.get_parent_of_symbol(owner) else {
        return false;
    };
    let Some(namespace_record) = store.symbol(namespace) else {
        return false;
    };
    let Some(namespace_declarations) = namespace_record.declarations() else {
        return false;
    };
    let Some(declarations) = interface.declarations() else {
        return false;
    };
    let TypeData::Interface(data) = record.data() else {
        return false;
    };

    record.object_flags() == ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
        && data.base_types_resolved
        && data.declared_members_resolved
        && data.resolved_base_types.is_none()
        && (interface.flags() == SymbolFlags::INTERFACE
            || authenticated_merged_react_declared_property_interface(store, owner))
        && namespace_record.flags().intersects(SymbolFlags::NAMESPACE)
        && namespace_record.check_flags() == CheckFlags::NONE
        && store.get_merged_symbol(namespace) == Some(namespace)
        && namespace_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(interface.name()))
            .and_then(|export| store.get_merged_symbol(export))
            == Some(owner)
        && declarations.iter().all(|declaration| {
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
}

fn validate_resolved_declared_property_object_detailed(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> DetailedDeclaredPropertyObjectValidation {
    use DetailedDeclaredPropertyObjectValidation::{
        Malformed, NotDeclared, TraversableBoundary, Valid,
    };

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
            if owner_record.flags() != SymbolFlags::INTERFACE
                && !authenticated_merged_react_declared_property_interface(store, owner)
            {
                return NotDeclared;
            }
            if valid_unresolved_jsx_element_interface(store, type_, record, interface)
                || valid_unresolved_react_node_array_interface(store, type_, record, interface)
                || valid_unresolved_react_portal_interface(store, type_, record, interface)
            {
                return TraversableBoundary(DeclaredPropertyObjectProof::Interface);
            }
            if record.object_flags() == ObjectFlags::INTERFACE | ObjectFlags::REFERENCE
                && matches!(
                    (
                        owner_record.name().as_utf8(),
                        store
                            .get_parent_of_symbol(owner)
                            .and_then(|namespace| store.symbol(namespace))
                            .and_then(|namespace| namespace.name().as_utf8()),
                    ),
                    (Some("Element"), Some("JSX"))
                        | (Some("ReactNodeArray" | "ReactPortal"), Some("React"))
                )
                && interface.base_types_resolved
                && interface.resolved_base_types.is_none()
                && store.direct_interface_heritage_provenance(type_).is_none()
                && validate_nongeneric_interface_argument_origin(store, type_).is_ok()
            {
                return Malformed;
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
                || interface.declared_call_signatures.is_some()
                || interface.declared_construct_signatures.is_some()
                || interface.declared_index_infos.is_some()
                || interface.reference.object.structured.signatures.is_some()
                || interface.reference.object.structured.call_signature_count != 0
                || interface.reference.object.structured.index_infos.is_some()
            {
                return NotDeclared;
            }
            if interface.resolved_base_types.is_some() {
                return match super::structured_members::validate_interface_heritage_members(
                    store, type_,
                ) {
                    super::structured_members::InterfaceHeritageMembersValidation::Valid => {
                        if owner_record.declarations().unwrap_or_default().iter().any(
                            |declaration| declaration_has_external_owner_shape(store, *declaration),
                        ) {
                            TraversableBoundary(DeclaredPropertyObjectProof::Interface)
                        } else if owner_record.parent().is_some()
                            || owner_record.exports().is_some()
                            || owner_record.export_symbol().is_some()
                        {
                            Malformed
                        } else {
                            Valid(DeclaredPropertyObjectProof::Interface)
                        }
                    }
                    super::structured_members::InterfaceHeritageMembersValidation::Malformed => {
                        Malformed
                    }
                    super::structured_members::InterfaceHeritageMembersValidation::NotHeritage => {
                        NotDeclared
                    }
                };
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

fn valid_unresolved_jsx_element_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    record: &TypeRecord,
    interface: &InterfaceTypeData,
) -> bool {
    let Some(owner) = record.symbol() else {
        return false;
    };
    let Some(owner_record) = store.symbol(owner) else {
        return false;
    };
    let Some([declaration]) = owner_record.declarations() else {
        return false;
    };
    let declaration = *declaration;
    let Some(namespace) = store.get_parent_of_symbol(owner) else {
        return false;
    };
    let Some(namespace_record) = store.symbol(namespace) else {
        return false;
    };
    let Some(SourceNodeParent::Parent(block)) = store.source_node_parent(declaration) else {
        return false;
    };
    let Some(SourceNodeParent::Parent(module)) = store.source_node_parent(block) else {
        return false;
    };
    let valid_interface_identity = match record.object_flags() {
        ObjectFlags::INTERFACE => valid_unresolved_interface_members(interface),
        flags if flags == ObjectFlags::INTERFACE | ObjectFlags::REFERENCE => {
            validate_nongeneric_interface_argument_origin(store, type_).is_ok()
                && interface.reference.object.structured == StructuredTypeData::default()
                && interface.resolved_base_constructor_type.is_none()
                && interface.resolved_base_types.is_none()
                && !interface.declared_members_resolved
                && interface.declared_members.is_none()
                && interface.declared_call_signatures.is_none()
                && interface.declared_construct_signatures.is_none()
                && interface.declared_index_infos.is_none()
        }
        _ => false,
    };
    if record.flags() != TypeFlags::OBJECT
        || !valid_interface_identity
        || record.alias().is_some()
        || interface.base_types_resolved
        || store.direct_interface_heritage_provenance(type_).is_some()
        || owner_record.flags() != SymbolFlags::INTERFACE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some("Element")
        || owner_record.value_declaration().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(type_)
        || store.source_node_kind(declaration) != Some(SyntaxKind::InterfaceDeclaration)
        || store.source_node_kind(block) != Some(SyntaxKind::ModuleBlock)
        || store.source_node_kind(module) != Some(SyntaxKind::ModuleDeclaration)
        || !namespace_record.flags().intersects(SymbolFlags::NAMESPACE)
        || namespace_record.check_flags() != CheckFlags::NONE
        || namespace_record.name().as_utf8() != Some("JSX")
        || store.get_merged_symbol(namespace) != Some(namespace)
        || namespace_record
            .declarations()
            .is_none_or(|declarations| !declarations.contains(&module))
        || namespace_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source("Element"))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(owner)
    {
        return false;
    }

    let has_own_properties = owner_record.members().is_some();
    if has_own_properties
        && classify_declared_owner_members(store, owner) != DeclaredOwnerMemberDomain::PropertyOnly
    {
        return false;
    }

    let mut heritage = None;
    let mut name_index = None;
    for index in (0..declaration.node.index()).rev() {
        let Ok(index) = u32::try_from(index) else {
            return false;
        };
        let node = NodeRef::new(
            declaration.arena,
            declaration.file,
            ts_ast::NodeId::new(index),
        );
        if store.source_node_parent(node) != Some(SourceNodeParent::Parent(declaration)) {
            continue;
        }
        match store.source_node_kind(node) {
            Some(SyntaxKind::HeritageClause) => {
                if heritage.replace(node).is_some() {
                    return false;
                }
            }
            Some(SyntaxKind::Identifier) => {
                name_index = Some(node.node.index());
                break;
            }
            Some(_) => {}
            None => return false,
        }
    }
    let Some(name_index) = name_index else {
        return false;
    };
    let Some(heritage) = heritage else {
        return true;
    };
    if has_own_properties {
        return false;
    }
    let mut bases = 0usize;
    for index in (name_index.saturating_add(1)..heritage.node.index()).rev() {
        let Ok(index) = u32::try_from(index) else {
            return false;
        };
        let node = NodeRef::new(heritage.arena, heritage.file, ts_ast::NodeId::new(index));
        if store.source_node_parent(node) != Some(SourceNodeParent::Parent(heritage)) {
            continue;
        }
        if store.source_node_kind(node) != Some(SyntaxKind::ExpressionWithTypeArguments) {
            continue;
        }
        bases += 1;
        if bases > 1 {
            return false;
        }
    }
    bases == 1
}

#[allow(clippy::too_many_lines)] // The lazy React shell and global Array share one provenance proof.
fn valid_unresolved_react_node_array_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    record: &TypeRecord,
    interface: &InterfaceTypeData,
) -> bool {
    let Some(owner) = record.symbol() else {
        return false;
    };
    let Some(owner_record) = store.symbol(owner) else {
        return false;
    };
    let Some([declaration]) = owner_record.declarations() else {
        return false;
    };
    let declaration = *declaration;
    let Some(namespace) = store.get_parent_of_symbol(owner) else {
        return false;
    };
    let Some(namespace_record) = store.symbol(namespace) else {
        return false;
    };
    let Some(exports) = namespace_record
        .exports()
        .and_then(|exports| store.symbol_table(exports))
    else {
        return false;
    };
    let Some(SourceNodeParent::Parent(block)) = store.source_node_parent(declaration) else {
        return false;
    };
    let Some(SourceNodeParent::Parent(module)) = store.source_node_parent(block) else {
        return false;
    };
    let Some(react_node) = exports
        .get_source("ReactNode")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(alias) = store.symbol(react_node) else {
        return false;
    };
    let Some([alias_declaration]) = alias.declarations() else {
        return false;
    };
    let valid_interface_identity = match record.object_flags() {
        ObjectFlags::INTERFACE => valid_unresolved_interface_members(interface),
        flags if flags == ObjectFlags::INTERFACE | ObjectFlags::REFERENCE => {
            validate_nongeneric_interface_argument_origin(store, type_).is_ok()
                && interface.reference.object.structured == StructuredTypeData::default()
                && interface.resolved_base_constructor_type.is_none()
                && interface.resolved_base_types.is_none()
                && !interface.declared_members_resolved
                && interface.declared_members.is_none()
                && interface.declared_call_signatures.is_none()
                && interface.declared_construct_signatures.is_none()
                && interface.declared_index_infos.is_none()
        }
        _ => false,
    };
    if record.flags() != TypeFlags::OBJECT
        || !valid_interface_identity
        || record.alias().is_some()
        || interface.base_types_resolved
        || store.direct_interface_heritage_provenance(type_).is_some()
        || owner_record.flags() != SymbolFlags::INTERFACE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some("ReactNodeArray")
        || owner_record.value_declaration().is_some()
        || owner_record.members().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(type_)
        || store.source_node_kind(declaration) != Some(SyntaxKind::InterfaceDeclaration)
        || store.source_node_kind(block) != Some(SyntaxKind::ModuleBlock)
        || store.source_node_kind(module) != Some(SyntaxKind::ModuleDeclaration)
        || !namespace_record.flags().intersects(SymbolFlags::NAMESPACE)
        || namespace_record.check_flags() != CheckFlags::NONE
        || namespace_record.name().as_utf8() != Some("React")
        || store.get_merged_symbol(namespace) != Some(namespace)
        || namespace_record
            .declarations()
            .is_none_or(|declarations| !declarations.contains(&module))
        || exports
            .get_source("ReactNodeArray")
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(owner)
        || alias.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::TYPE_ALIAS
        || alias.check_flags() != CheckFlags::NONE
        || store.get_parent_of_symbol(react_node) != Some(namespace)
        || store.source_node_kind(*alias_declaration) != Some(SyntaxKind::TypeAliasDeclaration)
        || store.source_node_parent(*alias_declaration) != Some(SourceNodeParent::Parent(block))
    {
        return false;
    }

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
    let Some(array_record) = store.symbol(array) else {
        return false;
    };
    let Some(target) = store
        .declared_type_links(array)
        .and_then(|links| links.declared_type)
    else {
        return false;
    };
    if array_record.flags().without(SymbolFlags::TRANSIENT)
        != SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || array_record.check_flags() != CheckFlags::NONE
        || array_record.name().as_utf8() != Some("Array")
        || array_record.parent().is_some()
        || array_record.exports().is_some()
        || array_record.export_symbol().is_some()
        || array_record.value_declaration().is_none_or(|value| {
            store.source_node_kind(value) != Some(SyntaxKind::VariableDeclaration)
        })
        || array_record.declarations().is_none_or(|declarations| {
            !declarations.iter().any(|candidate| {
                store.source_node_kind(*candidate) == Some(SyntaxKind::InterfaceDeclaration)
            })
        })
        || preflight_generic_global_type_target(store, target) != Ok(None)
        || store
            .type_payload(target)
            .and_then(TypeRecord::symbol)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(array)
    {
        return false;
    }

    let mut heritage = None;
    let mut name_index = None;
    for index in (0..declaration.node.index()).rev() {
        let Ok(index) = u32::try_from(index) else {
            return false;
        };
        let candidate = NodeRef::new(
            declaration.arena,
            declaration.file,
            ts_ast::NodeId::new(index),
        );
        if store.source_node_parent(candidate) != Some(SourceNodeParent::Parent(declaration)) {
            continue;
        }
        match store.source_node_kind(candidate) {
            Some(SyntaxKind::HeritageClause) => {
                if heritage.replace(candidate).is_some() {
                    return false;
                }
            }
            Some(SyntaxKind::Identifier) => {
                name_index = Some(candidate.node.index());
                break;
            }
            Some(_) => {}
            None => return false,
        }
    }
    let Some(heritage) = heritage else {
        return false;
    };
    let Some(name_index) = name_index else {
        return false;
    };
    let mut base = None;
    for index in (name_index.saturating_add(1)..heritage.node.index()).rev() {
        let Ok(index) = u32::try_from(index) else {
            return false;
        };
        let candidate = NodeRef::new(heritage.arena, heritage.file, ts_ast::NodeId::new(index));
        if store.source_node_parent(candidate) != Some(SourceNodeParent::Parent(heritage)) {
            continue;
        }
        if store.source_node_kind(candidate) != Some(SyntaxKind::ExpressionWithTypeArguments)
            || base.replace(candidate).is_some()
        {
            return false;
        }
    }
    let Some(base) = base else {
        return false;
    };
    let mut expression = None;
    let mut argument = None;
    for index in (name_index.saturating_add(1)..base.node.index()).rev() {
        let Ok(index) = u32::try_from(index) else {
            return false;
        };
        let candidate = NodeRef::new(base.arena, base.file, ts_ast::NodeId::new(index));
        if store.source_node_parent(candidate) != Some(SourceNodeParent::Parent(base)) {
            continue;
        }
        match store.source_node_kind(candidate) {
            Some(SyntaxKind::Identifier) if expression.replace(candidate).is_none() => {}
            Some(SyntaxKind::TypeReference) if argument.replace(candidate).is_none() => {}
            _ => return false,
        }
    }
    let Some(expression) = expression else {
        return false;
    };
    let Some(argument) = argument else {
        return false;
    };
    let mut argument_name = None;
    for index in (name_index.saturating_add(1)..argument.node.index()).rev() {
        let Ok(index) = u32::try_from(index) else {
            return false;
        };
        let candidate = NodeRef::new(argument.arena, argument.file, ts_ast::NodeId::new(index));
        if store.source_node_parent(candidate) != Some(SourceNodeParent::Parent(argument)) {
            continue;
        }
        if store.source_node_kind(candidate) != Some(SyntaxKind::Identifier)
            || argument_name.replace(candidate).is_some()
        {
            return false;
        }
    }
    let Some(argument_name) = argument_name else {
        return false;
    };
    [
        (base, array),
        (expression, array),
        (argument, react_node),
        (argument_name, react_node),
    ]
    .into_iter()
    .all(|(reference, expected)| {
        store.symbol_node_links(reference).is_none_or(|links| {
            links
                .resolved_symbol
                .is_none_or(|cached| store.get_merged_symbol(cached) == Some(expected))
        })
    })
}

#[allow(clippy::too_many_lines)] // The portal shell preserves exact React owner and generic-base edges.
fn valid_unresolved_react_portal_interface(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    record: &TypeRecord,
    interface: &InterfaceTypeData,
) -> bool {
    let Some(owner) = record.symbol() else {
        return false;
    };
    let Some(owner_record) = store.symbol(owner) else {
        return false;
    };
    let Some([declaration]) = owner_record.declarations() else {
        return false;
    };
    let declaration = *declaration;
    let Some(namespace) = store.get_parent_of_symbol(owner) else {
        return false;
    };
    let Some(namespace_record) = store.symbol(namespace) else {
        return false;
    };
    let Some(exports) = namespace_record
        .exports()
        .and_then(|exports| store.symbol_table(exports))
    else {
        return false;
    };
    let Some(members) = owner_record
        .members()
        .and_then(|members| store.symbol_table(members))
    else {
        return false;
    };
    let Some(SourceNodeParent::Parent(block)) = store.source_node_parent(declaration) else {
        return false;
    };
    let Some(SourceNodeParent::Parent(module)) = store.source_node_parent(block) else {
        return false;
    };
    let Some(element) = exports
        .get_source("ReactElement")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(element_record) = store.symbol(element) else {
        return false;
    };
    let Some(element_members) = element_record
        .members()
        .and_then(|members| store.symbol_table(members))
    else {
        return false;
    };
    let Some(react_node) = exports
        .get_source("ReactNode")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(alias) = store.symbol(react_node) else {
        return false;
    };
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::INTERFACE | ObjectFlags::REFERENCE
        || record.alias().is_some()
        || validate_nongeneric_interface_argument_origin(store, type_).is_err()
        || interface.reference.object.structured != StructuredTypeData::default()
        || interface.base_types_resolved
        || interface.resolved_base_constructor_type.is_some()
        || interface.resolved_base_types.is_some()
        || interface.declared_members_resolved
        || interface.declared_members.is_some()
        || interface.declared_call_signatures.is_some()
        || interface.declared_construct_signatures.is_some()
        || interface.declared_index_infos.is_some()
        || store.direct_interface_heritage_provenance(type_).is_some()
        || owner_record.flags() != SymbolFlags::INTERFACE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name().as_utf8() != Some("ReactPortal")
        || owner_record.value_declaration().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(type_)
        || store.source_node_kind(declaration) != Some(SyntaxKind::InterfaceDeclaration)
        || store.source_node_kind(block) != Some(SyntaxKind::ModuleBlock)
        || store.source_node_kind(module) != Some(SyntaxKind::ModuleDeclaration)
        || !namespace_record.flags().intersects(SymbolFlags::NAMESPACE)
        || namespace_record.check_flags() != CheckFlags::NONE
        || namespace_record.name().as_utf8() != Some("React")
        || namespace_record
            .declarations()
            .is_none_or(|declarations| !declarations.contains(&module))
        || exports
            .get_source("ReactPortal")
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(owner)
        || members.len() != 2
        || element_record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
        || element_record.check_flags() != CheckFlags::NONE
        || element_record.name().as_utf8() != Some("ReactElement")
        || store.get_parent_of_symbol(element) != Some(namespace)
        || element_members.len() != 4
        || alias.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::TYPE_ALIAS
        || alias.check_flags() != CheckFlags::NONE
        || store.get_parent_of_symbol(react_node) != Some(namespace)
    {
        return false;
    }

    for name in ["type", "props", "key"] {
        let Some(property) = element_members.get_source(name) else {
            return false;
        };
        let Some(property_record) = store.symbol(property) else {
            return false;
        };
        if property_record.flags() != SymbolFlags::PROPERTY
            || property_record.check_flags() != CheckFlags::NONE
            || store.get_parent_of_symbol(property) != Some(element)
        {
            return false;
        }
    }
    for name in ["key", "children"] {
        let Some(property) = members.get_source(name) else {
            return false;
        };
        let Some(property_record) = store.symbol(property) else {
            return false;
        };
        let Some([property_declaration]) = property_record.declarations() else {
            return false;
        };
        if property_record.flags() != SymbolFlags::PROPERTY
            || property_record.check_flags() != CheckFlags::NONE
            || property_record.name().as_utf8() != Some(name)
            || property_record.value_declaration() != Some(*property_declaration)
            || store.get_parent_of_symbol(property) != Some(owner)
            || store.source_node_parent(*property_declaration)
                != Some(SourceNodeParent::Parent(declaration))
            || store
                .value_symbol_links(property)
                .is_some_and(|links| links != &ValueSymbolLinks::default())
        {
            return false;
        }
        if name == "children" {
            let Some(annotation) = store.source_direct_type_annotation(*property_declaration)
            else {
                return false;
            };
            if store.source_node_kind(annotation) != Some(SyntaxKind::TypeReference)
                || store.symbol_node_links(annotation).is_some_and(|links| {
                    links
                        .resolved_symbol
                        .is_some_and(|symbol| store.get_merged_symbol(symbol) != Some(react_node))
                })
            {
                return false;
            }
        }
    }

    let mut heritage = None;
    let mut name_index = None;
    for index in (0..declaration.node.index()).rev() {
        let Ok(index) = u32::try_from(index) else {
            return false;
        };
        let candidate = NodeRef::new(
            declaration.arena,
            declaration.file,
            ts_ast::NodeId::new(index),
        );
        if store.source_node_parent(candidate) != Some(SourceNodeParent::Parent(declaration)) {
            continue;
        }
        match store.source_node_kind(candidate) {
            Some(SyntaxKind::HeritageClause) => {
                if heritage.replace(candidate).is_some() {
                    return false;
                }
            }
            Some(SyntaxKind::Identifier) => {
                name_index = Some(candidate.node.index());
                break;
            }
            Some(_) => {}
            None => return false,
        }
    }
    let (Some(heritage), Some(name_index)) = (heritage, name_index) else {
        return false;
    };
    let mut base = None;
    for index in (name_index.saturating_add(1)..heritage.node.index()).rev() {
        let Ok(index) = u32::try_from(index) else {
            return false;
        };
        let candidate = NodeRef::new(heritage.arena, heritage.file, ts_ast::NodeId::new(index));
        if store.source_node_parent(candidate) != Some(SourceNodeParent::Parent(heritage)) {
            continue;
        }
        if store.source_node_kind(candidate) != Some(SyntaxKind::ExpressionWithTypeArguments)
            || base.replace(candidate).is_some()
        {
            return false;
        }
    }
    let Some(base) = base else {
        return false;
    };
    let mut expression = None;
    let mut any = None;
    for index in (name_index.saturating_add(1)..base.node.index()).rev() {
        let Ok(index) = u32::try_from(index) else {
            return false;
        };
        let candidate = NodeRef::new(base.arena, base.file, ts_ast::NodeId::new(index));
        if store.source_node_parent(candidate) != Some(SourceNodeParent::Parent(base)) {
            continue;
        }
        match store.source_node_kind(candidate) {
            Some(SyntaxKind::Identifier) if expression.replace(candidate).is_none() => {}
            Some(SyntaxKind::AnyKeyword) if any.replace(candidate).is_none() => {}
            _ => return false,
        }
    }
    let Some(expression) = expression else {
        return false;
    };
    any.is_some()
        && [(base, element), (expression, element)]
            .into_iter()
            .all(|(reference, expected)| {
                store.symbol_node_links(reference).is_none_or(|links| {
                    links
                        .resolved_symbol
                        .is_none_or(|cached| store.get_merged_symbol(cached) == Some(expected))
                })
            })
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
    let Some(owner_record) = store.symbol(owner) else {
        return DeclaredOwnerMemberDomain::Malformed;
    };
    let Some(members) = owner_record.members() else {
        return DeclaredOwnerMemberDomain::PropertyOnly;
    };
    let Some(table) = store.symbol_table(members) else {
        return DeclaredOwnerMemberDomain::Malformed;
    };
    let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::ACCESSOR;
    let unsupported_flags = SymbolFlags::METHOD
        | SymbolFlags::SIGNATURE
        | SymbolFlags::ACCESSOR
        | SymbolFlags::CONSTRUCTOR;
    let mut domain = DeclaredOwnerMemberDomain::PropertyOnly;
    for (_, property) in table.iter() {
        let Some(property) = store.symbol(property) else {
            return DeclaredOwnerMemberDomain::Malformed;
        };
        if (property.flags().contains(SymbolFlags::PROPERTY)
            || property.flags().intersects(SymbolFlags::ACCESSOR))
            && property.flags().without(allowed_flags) == SymbolFlags::NONE
        {
            let declarations = property.declarations().unwrap_or_default();
            if property.flags().intersects(SymbolFlags::ACCESSOR) {
                let mut getters = 0usize;
                let mut setters = 0usize;
                let mut properties = 0usize;
                let mut unique = HashSet::with_capacity(declarations.len());
                if !owner_record.flags().contains(SymbolFlags::INTERFACE)
                    || declarations.is_empty()
                    || !declarations.iter().all(|declaration| {
                        if !unique.insert(*declaration) {
                            return false;
                        }
                        match store.source_node_kind(*declaration) {
                            Some(SyntaxKind::GetAccessor) => getters += 1,
                            Some(SyntaxKind::SetAccessor) => setters += 1,
                            Some(
                                SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature,
                            ) => {
                                properties += 1;
                            }
                            _ => return false,
                        }
                        true
                    })
                    || getters > 1
                    || setters > 1
                    || property.flags().contains(SymbolFlags::GET_ACCESSOR) != (getters == 1)
                    || property.flags().contains(SymbolFlags::SET_ACCESSOR) != (setters == 1)
                    || property.flags().contains(SymbolFlags::PROPERTY) != (properties != 0)
                    || property.flags().contains(SymbolFlags::OPTIONAL) && properties == 0
                {
                    return DeclaredOwnerMemberDomain::Malformed;
                }
                continue;
            }
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
                        if !owner_record.flags().contains(SymbolFlags::INTERFACE) {
                            return DeclaredOwnerMemberDomain::Malformed;
                        }
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
    use DetailedDeclaredPropertyObjectValidation::{Malformed, TraversableBoundary, Valid};

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
    Malformed,
}

fn validate_declared_property_owner(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    owner: SemanticSymbolId,
    members: Option<SymbolTableId>,
    proof: DeclaredPropertyObjectProof,
) -> DeclaredPropertyOwnerValidation {
    use DeclaredPropertyOwnerValidation::{Malformed, TraversableBoundary, Valid};

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
    if declarations.is_empty()
        || proof != DeclaredPropertyObjectProof::Interface && declarations.len() != 1
    {
        return Malformed;
    }
    let mut unique = HashSet::with_capacity(declarations.len());
    if !declarations.iter().all(|declaration| {
        unique.insert(*declaration) && store.source_node_kind(*declaration) == Some(expected_kind)
    }) {
        return Malformed;
    }
    let declaration = declarations[0];
    if store.get_merged_symbol(owner) != Some(owner)
        || owner_record.flags() != expected_flags
            && (proof != DeclaredPropertyObjectProof::Interface
                || !authenticated_merged_react_declared_property_interface(store, owner))
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
        && declarations
            .iter()
            .any(|declaration| declaration_has_external_owner_shape(store, *declaration))
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
    let valid_declaration = match store.source_node_kind(*declaration) {
        Some(SyntaxKind::TypeAliasDeclaration) => true,
        Some(SyntaxKind::JsTypeAliasDeclaration) => {
            authenticated_reparsed_js_type_alias(store, symbol, *declaration, type_)
        }
        _ => false,
    };
    let valid_core = symbol == expected_owner
        && alias_record.type_arguments().is_none()
        && store.get_merged_symbol(symbol) == Some(symbol)
        && symbol_record.flags() == SymbolFlags::TYPE_ALIAS
        && symbol_record.check_flags() == CheckFlags::NONE
        && symbol_record.value_declaration().is_none()
        && valid_declaration
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
    if declaration_has_external_owner_shape(store, *declaration)
        || store.source_node_kind(*declaration) == Some(SyntaxKind::JsTypeAliasDeclaration)
            && symbol_record.parent().is_some()
    {
        Unsupported
    } else if has_owner_relationship {
        Malformed
    } else {
        Valid
    }
}

fn authenticated_reparsed_js_type_alias(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
    type_: TypeId,
) -> bool {
    let Some(owner) = store.symbol(symbol) else {
        return false;
    };
    let Some(SourceNodeParent::Parent(source)) = store.source_node_parent(declaration) else {
        return false;
    };
    let valid_parent = match owner.parent() {
        None => true,
        Some(module) => store.symbol(module).is_some_and(|module_record| {
            store.get_merged_symbol(module) == Some(module)
                && module_record.flags() == SymbolFlags::VALUE_MODULE
                && module_record.check_flags() == CheckFlags::NONE
                && module_record.declarations() == Some(&[source])
                && module_record.value_declaration() == Some(source)
                && module_record.members().is_none()
                && module_record.parent().is_none()
                && module_record.export_symbol().is_none()
                && module_record
                    .exports()
                    .and_then(|exports| store.symbol_table(exports))
                    .and_then(|exports| exports.get(owner.name()))
                    == Some(symbol)
        }),
    };
    store.source_node_kind(declaration) == Some(SyntaxKind::JsTypeAliasDeclaration)
        && store.source_node_kind(source) == Some(SyntaxKind::SourceFile)
        && store.source_node_parent(source) == Some(SourceNodeParent::Root)
        && store.source_node_is_exported(declaration) != Some(true)
        && store.get_merged_symbol(symbol) == Some(symbol)
        && owner.flags() == SymbolFlags::TYPE_ALIAS
        && owner.check_flags() == CheckFlags::NONE
        && owner.declarations() == Some(&[declaration])
        && owner.value_declaration().is_none()
        && owner.members().is_none()
        && owner.exports().is_none()
        && valid_parent
        && owner.export_symbol().is_none()
        && store.type_alias_links(symbol).is_some_and(|links| {
            links.declared_type == Some(type_)
                && links.type_parameters.is_none()
                && links.instantiations.is_none()
                && !links.is_constructor_declared_property
        })
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
            SyntaxKind::TypeAliasDeclaration | SyntaxKind::JsTypeAliasDeclaration => {
                break Some(parent);
            }
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
                && (store.source_node_kind(alias_declaration)
                    != Some(SyntaxKind::JsTypeAliasDeclaration)
                    || authenticated_reparsed_js_type_alias(
                        store,
                        *owner,
                        alias_declaration,
                        type_,
                    ))
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
    let Some(owner_record) = store.symbol(owner) else {
        return false;
    };
    let owner_declarations = owner_record.declarations().unwrap_or_default();
    if !owner_declarations.contains(&owner_declaration) {
        return false;
    }
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
    let mut previous_position = None;
    for property in properties {
        if !seen_properties.insert(*property) {
            return false;
        }
        let Some(property_record) = store.symbol(*property) else {
            return false;
        };
        let declarations = property_record.declarations().unwrap_or_default();
        let Some(&declaration) = declarations.first() else {
            return false;
        };
        let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(declaration) else {
            return false;
        };
        let Some(owner_index) = owner_declarations
            .iter()
            .position(|candidate| *candidate == parent)
        else {
            return false;
        };
        let position = (owner_index, declaration);
        let accessor = property_record.flags().intersects(SymbolFlags::ACCESSOR);
        let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::ACCESSOR;
        if !property_record.flags().contains(SymbolFlags::PROPERTY) && !accessor
            || property_record.flags().without(allowed_flags) != SymbolFlags::NONE
            || property_record.check_flags().bits() & !CheckFlags::READONLY.bits() != 0
            || accessor && property_record.check_flags() != CheckFlags::NONE
            || accessor && !owner_record.flags().contains(SymbolFlags::INTERFACE)
            || property_record.name().is_reserved_member_name()
            || property_record.name().is_private_identifier()
            || property_record.name().is_late_bound()
            || property_record.name().as_utf8().is_none()
            || property_record.value_declaration() != Some(declaration)
            || store.get_parent_of_symbol(*property) != Some(owner)
            || property_record.members().is_some()
            || property_record.exports().is_some()
            || property_record.export_symbol().is_some()
            || store.get_merged_symbol(*property) != Some(*property)
            || previous_position.is_some_and(|previous| previous >= position)
            || table.and_then(|table| table.get(property_record.name())) != Some(*property)
        {
            return false;
        }
        if !declarations.iter().all(|declaration| {
            let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(*declaration)
            else {
                return false;
            };
            owner_declarations.contains(&parent)
                && declaration.is_for(parent.arena, parent.file)
                && *declaration < parent
                && matches!(
                    store.source_node_kind(*declaration),
                    Some(
                        SyntaxKind::PropertyDeclaration
                            | SyntaxKind::PropertySignature
                            | SyntaxKind::GetAccessor
                            | SyntaxKind::SetAccessor
                    )
                )
                && seen_declarations.insert(*declaration)
        }) {
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
                write_type: links.write_type,
                ..ValueSymbolLinks::default()
            })
            || links.write_type.is_some_and(|write_type| {
                !accessor
                    || !property_record.flags().contains(SymbolFlags::SET_ACCESSOR)
                    || write_type == property_type
                    || store.type_payload(write_type).is_none()
            })
            || store.type_payload(property_type).is_none()
        {
            return false;
        }
        previous_position = Some(position);
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
    let call_signature_count = plan
        .call_signatures
        .iter()
        .filter(|signature| !signature.is_construct())
        .count();
    valid_planned_call_signature_set(store, plan)
        && (plan.call_signatures.is_empty()
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
        && object.structured.call_signature_count == call_signature_count
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
    let mut seen = HashSet::with_capacity(indexes.len());
    indexes.iter().zip(&plan.indexes).all(|(id, planned)| {
        if !seen.insert(*id) {
            return false;
        }
        let Some(expected_key) = cached_planned_type_identity(store, planned.key_type_node) else {
            return false;
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

fn valid_signature_return_annotation(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    null_literal_identity: bool,
    type_: TypeId,
) -> bool {
    if let Some(cached) = cached_annotation_identity(store, node, null_literal_identity) {
        return cached == type_;
    }
    if null_literal_identity
        || store.source_node_kind(node) != Some(SyntaxKind::InferType)
        || store.type_node_links(node).is_some()
    {
        return false;
    }
    let Some(symbol) = cached_ordinary_type_parameter_owner(store, type_) else {
        return false;
    };
    let Some([declaration]) = store
        .symbol(symbol)
        .and_then(ts_binder::semantic::Symbol::declarations)
    else {
        return false;
    };
    store.source_node_kind(*declaration) == Some(SyntaxKind::TypeParameter)
        && store.source_node_parent(*declaration) == Some(SourceNodeParent::Parent(node))
}

fn valid_planned_signature_return(
    store: &CanonicalTypeMapperStore,
    signature: &PlannedCallSignature,
    type_: TypeId,
) -> bool {
    if signature.implicit_any_return {
        let valid_owner = match (
            store.source_node_kind(signature.declaration),
            store.source_node_parent(signature.declaration),
        ) {
            (Some(SyntaxKind::CallSignature), Some(SourceNodeParent::Parent(owner))) => {
                store.source_node_kind(owner) == Some(SyntaxKind::TypeLiteral)
            }
            (Some(SyntaxKind::ConstructSignature), Some(SourceNodeParent::Parent(owner))) => {
                store.source_node_kind(owner) == Some(SyntaxKind::InterfaceDeclaration)
            }
            _ => false,
        };
        signature.return_type == signature.declaration
            && signature.return_identity_node == signature.declaration
            && !signature.return_null_literal_identity
            && valid_owner
            && store
                .source_direct_type_annotation(signature.declaration)
                .is_none()
            && store
                .intrinsic_bootstrap()
                .is_some_and(|bootstrap| type_ == bootstrap.any_type)
    } else {
        valid_signature_return_annotation(
            store,
            signature.return_identity_node,
            signature.return_null_literal_identity,
            type_,
        )
    }
}

fn planned_call_parameter_type(
    store: &CanonicalTypeMapperStore,
    parameter: &PlannedCallParameter,
) -> Option<TypeId> {
    if parameter.implicit_any_rest {
        let declaration = store.symbol(parameter.symbol)?.value_declaration()?;
        let type_ = implicit_any_array_type(store)?;
        declared_signature_parameter_is_implicit_any_rest(store, declaration, type_)
            .then_some(type_)
    } else {
        cached_annotation_identity(
            store,
            parameter.identity_node,
            parameter.null_literal_identity,
        )
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
    if bound.flags() != SymbolFlags::PROPERTY
        || bound.check_flags() != CheckFlags::NONE
        || bound.name().as_utf8() != Some(property.name.as_str())
        || bound.declarations() != Some(&[property.declaration])
        || bound.value_declaration() != Some(property.declaration)
        || bound.members().is_some()
        || bound.exports().is_some()
        || bound.export_symbol().is_some()
        || store.get_merged_symbol(property.symbol) != Some(property.symbol)
        || cloned.flags() != (bound.flags() | SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT)
        || cloned.check_flags() != source_property_check_flags(property.readonly)
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
    (links == &expected && valid_object_literal_property_type(store, property, resolved_type))
        .then_some(resolved_type)
}

fn valid_object_literal_property_type(
    store: &CanonicalTypeMapperStore,
    property: &PlannedProperty,
    type_: TypeId,
) -> bool {
    store.type_payload(type_).is_some_and(|record| {
        !property.readonly
            || !matches!(record.data(), TypeData::Literal(literal) if literal.regular_type != type_)
    })
}

fn validated_synthetic_object_properties(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<Vec<ResolvedObjectProperty>> {
    let record = store.type_payload(type_)?;
    let TypeData::Object(object) = record.data() else {
        return None;
    };
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.symbol().is_some()
        || record.alias().is_some()
        || !valid_object_tail(object)
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.structured.signatures.is_some()
        || object.structured.call_signature_count != 0
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return None;
    }
    let members = object.structured.members?;
    let table = store.symbol_table(members)?;
    let properties = object.structured.properties.as_deref().unwrap_or_default();
    if table.len() != properties.len()
        || object.structured.properties.is_some() == properties.is_empty()
    {
        return None;
    }

    let mut seen = HashSet::with_capacity(properties.len());
    let mut resolved = Vec::with_capacity(properties.len());
    for symbol in properties {
        if !seen.insert(*symbol) {
            return None;
        }
        let property = store.symbol(*symbol)?;
        let links = store.value_symbol_links(*symbol)?;
        let type_ = links.resolved_type?;
        let name = property.name().as_utf8()?;
        let allowed_flags = SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL | SymbolFlags::TRANSIENT;
        if !property
            .flags()
            .contains(SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT)
            || property.flags().without(allowed_flags) != SymbolFlags::NONE
            || property.check_flags().bits() & !CheckFlags::READONLY.bits() != 0
            || property.name().is_reserved_member_name()
            || property.name().is_private_identifier()
            || property.name().is_late_bound()
            || property.declarations().is_some()
            || property.value_declaration().is_some()
            || property.parent().is_some()
            || property.members().is_some()
            || property.exports().is_some()
            || property.export_symbol().is_some()
            || store.get_merged_symbol(*symbol) != Some(*symbol)
            || store.type_payload(type_).is_none()
            || table.get(property.name()) != Some(*symbol)
            || links
                != &(ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
        {
            return None;
        }
        resolved.push(ResolvedObjectProperty {
            name: name.to_owned(),
            type_,
            readonly: property.check_flags().contains(CheckFlags::READONLY),
            optional: property.flags().contains(SymbolFlags::OPTIONAL),
        });
    }
    Some(resolved)
}

fn synthetic_object_literal_matches_plan(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    type_: TypeId,
) -> bool {
    if !unresolved_property_links(store, plan) {
        return false;
    }
    let Some(properties) = validated_synthetic_object_properties(store, type_) else {
        return false;
    };
    if !plan.spreads.is_empty() {
        return properties
            .iter()
            .all(|property| property.readonly == plan.const_context);
    }
    plan.const_context
        && properties.len() == plan.properties.len()
        && plan
            .properties
            .iter()
            .zip(properties)
            .all(|(planned, actual)| {
                planned.name == actual.name
                    && planned.readonly == actual.readonly
                    && planned.optional == actual.optional
                    && valid_object_literal_property_type(store, planned, actual.type_)
            })
}

fn unresolved_property_links(store: &CanonicalTypeMapperStore, plan: &PropertyObjectPlan) -> bool {
    plan.properties.iter().all(|property| {
        let Some(record) = store.symbol(property.symbol) else {
            return false;
        };
        if record.flags().contains(SymbolFlags::METHOD) {
            return match store.value_symbol_links(property.symbol) {
                Some(links) if links != &ValueSymbolLinks::default() => {
                    resolved_interface_method_value(store, plan, property.symbol).is_some()
                }
                _ => plan
                    .methods
                    .iter()
                    .filter(|method| method.symbol == property.symbol)
                    .all(|method| {
                        store
                            .signature_links(method.declaration)
                            .is_none_or(|links| links == &SignatureLinks::default())
                            && method.parameters.iter().all(|parameter| {
                                store
                                    .value_symbol_links(parameter.symbol)
                                    .is_none_or(|links| links == &ValueSymbolLinks::default())
                            })
                    }),
            };
        }
        if record.flags().intersects(SymbolFlags::ACCESSOR) {
            return record.check_flags() == CheckFlags::NONE
                && store
                    .value_symbol_links(property.symbol)
                    .is_none_or(|links| links == &ValueSymbolLinks::default())
                && plan
                    .accessors
                    .iter()
                    .filter(|accessor| accessor.symbol == property.symbol)
                    .filter_map(|accessor| accessor.parameter)
                    .all(|parameter| {
                        store
                            .value_symbol_links(parameter.symbol)
                            .is_none_or(|links| links == &ValueSymbolLinks::default())
                    });
        }
        let expected = source_property_check_flags(property.readonly);
        (record.check_flags() == CheckFlags::NONE || record.check_flags() == expected)
            && store
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
        let Some(record) = store.symbol(property.symbol) else {
            return false;
        };
        if record.flags().contains(SymbolFlags::METHOD) {
            return resolved_interface_method_value(store, plan, property.symbol).is_some();
        }
        valid_declared_property_check_flags(store, property)
            && store
                .value_symbol_links(property.symbol)
                .is_some_and(|links| {
                    links.resolved_type.is_some_and(|type_| {
                        store.type_payload(type_).is_some()
                            && expected_declared_property_links(store, plan, property, type_)
                                .as_ref()
                                == Some(links)
                    })
                })
            && plan
                .accessors
                .iter()
                .filter(|accessor| accessor.symbol == property.symbol)
                .filter_map(|accessor| accessor.parameter)
                .all(|parameter| {
                    cached_planned_type_identity(store, parameter.type_node).is_some_and(|type_| {
                        store.value_symbol_links(parameter.symbol)
                            == Some(&ValueSymbolLinks {
                                resolved_type: Some(type_),
                                ..ValueSymbolLinks::default()
                            })
                    })
                })
    }) && resolved_call_signature_ids(store, plan).is_some() != plan.call_signatures.is_empty()
}

fn valid_planned_call_signature_set(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
) -> bool {
    if plan.call_signatures.is_empty() {
        return plan.members.is_none_or(|members| {
            store.symbol_table(members).is_some_and(|members| {
                members.get(InternalSymbolName::Call.as_ref()).is_none()
                    && members.get(InternalSymbolName::New.as_ref()).is_none()
            })
        });
    }
    let Some(members) = plan.members.and_then(|members| store.symbol_table(members)) else {
        return false;
    };
    let family_count = usize::from(
        plan.call_signatures
            .iter()
            .any(|signature| !signature.is_construct()),
    ) + usize::from(
        plan.call_signatures
            .iter()
            .any(PlannedCallSignature::is_construct),
    );
    members.len()
        == family_count
            .saturating_add(plan.properties.len())
            .saturating_add(usize::from(!plan.indexes.is_empty()))
        && (plan.kind == PropertyObjectKind::Interface
            || plan.properties.is_empty()
            || plan.kind == PropertyObjectKind::TypeLiteral
                && plan.methods.is_empty()
                && plan.accessors.is_empty()
                && plan.indexes.is_empty()
                && !plan
                    .call_signatures
                    .iter()
                    .any(PlannedCallSignature::is_construct))
        && plan.properties.iter().all(|property| {
            members.get_source(&property.name) == Some(property.symbol)
                && store.symbol(property.symbol).is_some_and(|record| {
                    record.name().as_utf8() == Some(property.name.as_str())
                        && store.get_parent_of_symbol(property.symbol) == Some(plan.symbol)
                        && store.get_merged_symbol(property.symbol) == Some(property.symbol)
                })
        })
        && match plan.indexes.first() {
            Some(index) => members.get(InternalSymbolName::Index.as_ref()) == Some(index.symbol),
            None => members.get(InternalSymbolName::Index.as_ref()).is_none(),
        }
        && [false, true].into_iter().all(|construct| {
            let name = if construct {
                InternalSymbolName::New
            } else {
                InternalSymbolName::Call
            };
            let Some(first) = plan
                .call_signatures
                .iter()
                .find(|signature| signature.is_construct() == construct)
            else {
                return members.get(name.as_ref()).is_none();
            };
            let Some(record) = store.symbol(first.symbol) else {
                return false;
            };
            members.get(first.internal_name().as_ref()) == Some(first.symbol)
                && record.name() == first.internal_name().as_ref()
                && record.declarations().is_some_and(|declarations| {
                    declarations.iter().copied().eq(plan
                        .call_signatures
                        .iter()
                        .filter(|signature| signature.is_construct() == construct)
                        .map(|signature| signature.declaration))
                })
                && plan
                    .call_signatures
                    .iter()
                    .filter(|signature| signature.is_construct() == construct)
                    .all(|signature| {
                        signature.symbol == first.symbol
                            && store.source_node_kind(signature.declaration)
                                == Some(signature.syntax_kind())
                    })
        })
}

fn resolved_call_signature_ids(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
) -> Option<Vec<SignatureId>> {
    if plan.call_signatures.is_empty() || !valid_planned_call_signature_set(store, plan) {
        return None;
    }
    plan.call_signatures
        .iter()
        .filter(|planned| !planned.is_construct())
        .chain(
            plan.call_signatures
                .iter()
                .filter(|planned| planned.is_construct()),
        )
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
    let type_parameters = resolved_declared_signature_type_parameters(
        store,
        planned.declaration,
        &planned.type_parameters,
    )?;
    let minimum = i32::try_from(planned.min_argument_count()).ok()?;
    if record.flags() != planned.flags
        || record.min_argument_count() != minimum
        || record.resolved_min_argument_count() != -1
        || record.declaration() != Some(planned.declaration)
        || record.type_parameters() != type_parameters.as_slice()
        || record.this_parameter().is_some()
        || record.parameters() != parameter_symbols.as_slice()
        || record.resolved_type_predicate().is_some()
        || record.target().is_some()
        || record.mapper().is_some()
        || record.isolated_signature_type().is_some()
        || record.composite().is_some()
        || store.signature_has_circular_return_type(signature)
        || store.function_signature_return_annotation(signature)
            != (!planned.implicit_any_return).then_some((
                planned.return_identity_node,
                planned.return_null_literal_identity,
            ))
        || !valid_planned_signature_return(store, planned, return_type)
        || parameter_types.len() != planned.parameters.len()
    {
        return None;
    }
    let rest_index = planned
        .flags
        .contains(SignatureFlags::HAS_REST_PARAMETER)
        .then(|| planned.parameters.len().saturating_sub(1));
    for (index, (parameter, type_)) in planned.parameters.iter().zip(parameter_types).enumerate() {
        let declaration = store.symbol(parameter.symbol)?.value_declaration()?;
        let actual_rest = if parameter.implicit_any_rest {
            declared_signature_parameter_is_implicit_any_rest(store, declaration, *type_)
                .then_some(true)
        } else {
            declared_signature_parameter_is_rest(store, declaration)
        };
        if planned_call_parameter_type(store, parameter) != Some(*type_)
            || declared_signature_parameter_is_optional(store, declaration, *type_)
                != Some(parameter.optional)
            || actual_rest != Some(rest_index == Some(index))
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

fn resolved_interface_method_value(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    symbol: SemanticSymbolId,
) -> Option<TypeId> {
    let method_record = store.symbol(symbol)?;
    let declarations = method_record.declarations()?;
    let links = store.value_symbol_links(symbol)?;
    let type_ = links.resolved_type?;
    let record = store.type_payload(type_)?;
    let TypeData::Object(object) = record.data() else {
        return None;
    };
    let signatures = object.structured.signatures.as_deref()?;
    if method_record.flags() != SymbolFlags::METHOD
        || method_record.check_flags() != CheckFlags::NONE
        || declarations.is_empty()
        || method_record.value_declaration() != declarations.first().copied()
        || store.get_parent_of_symbol(symbol) != Some(plan.symbol)
        || links
            != &(ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
        || record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.symbol() != Some(symbol)
        || record.alias().is_some()
        || !valid_object_tail(object)
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.structured.members.is_some()
        || object.structured.properties.is_some()
        || object.structured.call_signature_count != signatures.len()
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || signatures.len() != declarations.len()
        || signatures.len()
            != plan
                .methods
                .iter()
                .filter(|method| method.symbol == symbol)
                .count()
    {
        return None;
    }

    for ((method, declaration), signature) in plan
        .methods
        .iter()
        .filter(|method| method.symbol == symbol)
        .zip(declarations)
        .zip(signatures)
    {
        let signature = *signature;
        let callable = store.signature(signature)?;
        let return_type = callable.resolved_return_type()?;
        let type_parameters = resolved_interface_method_type_parameters(store, method)?;
        if method.declaration != *declaration
            || callable.flags() != method.flags
            || callable.declaration() != Some(method.declaration)
            || callable.type_parameters() != type_parameters.as_slice()
            || callable.this_parameter().is_some()
            || callable.parameters().len() != method.parameters.len()
            || usize::try_from(callable.min_argument_count()).ok()
                != Some(method.minimum_argument_count)
            || callable.resolved_min_argument_count() != -1
            || callable.resolved_type_predicate().is_some()
            || callable.target().is_some()
            || callable.mapper().is_some()
            || callable.isolated_signature_type().is_some()
            || callable.composite().is_some()
            || store.signature_has_circular_return_type(signature)
            || cached_planned_type_identity(store, method.return_type) != Some(return_type)
            || store.signature_links(method.declaration)
                != Some(&SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                })
            || store
                .callable_signature_parameter_types(signature)
                .is_some_and(|cached| cached.len() != method.parameters.len())
        {
            return None;
        }

        for (index, (planned, parameter)) in method
            .parameters
            .iter()
            .zip(callable.parameters())
            .enumerate()
        {
            let links = store.value_symbol_links(*parameter)?;
            let parameter_type = links.resolved_type?;
            if planned.symbol != *parameter
                || cached_annotation_identity(
                    store,
                    planned.identity_node,
                    planned.null_literal_identity,
                ) != Some(parameter_type)
                || links
                    != &(ValueSymbolLinks {
                        resolved_type: Some(parameter_type),
                        ..ValueSymbolLinks::default()
                    })
                || store
                    .callable_signature_parameter_types(signature)
                    .is_some_and(|cached| cached[index] != parameter_type)
            {
                return None;
            }
        }
    }
    Some(type_)
}

fn resolved_interface_method_type_parameters(
    store: &CanonicalTypeMapperStore,
    method: &PlannedInterfaceMethod,
) -> Option<Vec<TypeId>> {
    resolved_declared_signature_type_parameters(store, method.declaration, &method.type_parameters)
}

fn resolved_declared_signature_type_parameters(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    parameters: &[PlannedInterfaceMethodTypeParameter],
) -> Option<Vec<TypeId>> {
    let mut resolved = Vec::with_capacity(parameters.len());
    let mut symbols = HashSet::with_capacity(parameters.len());
    for parameter in parameters {
        let type_ = store.declared_type_links(parameter.symbol)?.declared_type?;
        let record = store.type_payload(type_)?;
        let TypeData::TypeParameter(data) = record.data() else {
            return None;
        };
        let constraint = match parameter.constraint {
            Some(node) => Some(cached_planned_type_identity(store, node)?),
            None => None,
        };
        let default_type = match parameter.default_type {
            Some(node) => Some(cached_planned_type_identity(store, node)?),
            None => None,
        };
        if !symbols.insert(parameter.symbol)
            || cached_ordinary_type_parameter_owner(store, type_) != Some(parameter.symbol)
            || store.source_node_kind(parameter.declaration) != Some(SyntaxKind::TypeParameter)
            || store.source_node_parent(parameter.declaration)
                != Some(SourceNodeParent::Parent(declaration))
            || data.is_this_type
            || data.target.is_some()
            || data.mapper.is_some()
            || data.constraint != constraint
            || data.resolved_default_type != default_type
        {
            return None;
        }
        resolved.push(type_);
    }
    Some(resolved)
}

/// Publishes one callable object per binder-owned declared method symbol.
///
/// `resolved` and the returned values follow `plan.methods` in declaration
/// order. Overloads share one returned object and keep their signature order.
pub(super) fn publish_interface_method_values(
    store: &mut CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    resolved: &[ResolvedCallSignatureTypes],
) -> Result<Vec<TypeId>, PropertyObjectError> {
    struct PreparedMethodGroup {
        symbol: SemanticSymbolId,
        indexes: Vec<usize>,
        type_parameters: Vec<Vec<TypeId>>,
        parameter_symbols: Vec<Vec<SemanticSymbolId>>,
        parameter_types: Vec<Vec<TypeId>>,
        signatures: Vec<SignatureId>,
        warm: Option<TypeId>,
    }

    if plan.methods.is_empty() && resolved.is_empty() {
        return Ok(Vec::new());
    }
    let owner_type = match plan.kind {
        PropertyObjectKind::Interface => store
            .declared_type_links(plan.symbol)
            .and_then(|links| links.declared_type),
        PropertyObjectKind::TypeLiteral => store
            .type_node_links(plan.node)
            .and_then(|links| links.resolved_type),
        PropertyObjectKind::ObjectLiteral => None,
    }
    .ok_or_else(|| invalid_plan(plan))?;
    if resolved.len() != plan.methods.len() {
        return Err(invalid_cache(plan, owner_type));
    }

    let placeholder = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.error_type)
        .ok_or_else(|| invalid_cache(plan, owner_type))?;
    let mut published = Vec::new();
    let mut prepared = Vec::new();
    let mut method_groups = HashMap::new();
    published
        .try_reserve_exact(plan.methods.len())
        .map_err(|_| PropertyObjectError::Capacity(plan.node))?;
    prepared
        .try_reserve_exact(plan.methods.len())
        .map_err(|_| PropertyObjectError::Capacity(plan.node))?;
    method_groups
        .try_reserve(plan.methods.len())
        .map_err(|_| PropertyObjectError::Capacity(plan.node))?;
    for (index, (method, resolved_signature)) in plan.methods.iter().zip(resolved).enumerate() {
        if plan
            .properties
            .iter()
            .all(|property| property.symbol != method.symbol)
            || resolved_signature.parameter_types.len() != method.parameters.len()
            || cached_planned_type_identity(store, method.return_type)
                != Some(resolved_signature.return_type)
            || method
                .parameters
                .iter()
                .zip(&resolved_signature.parameter_types)
                .any(|(parameter, parameter_type)| {
                    cached_annotation_identity(
                        store,
                        parameter.identity_node,
                        parameter.null_literal_identity,
                    ) != Some(*parameter_type)
                })
        {
            return Err(invalid_cache(plan, owner_type));
        }
        let type_parameters = resolved_interface_method_type_parameters(store, method)
            .ok_or_else(|| invalid_cache(plan, owner_type))?;
        published.push(placeholder);
        let group_index = if let Some(group) = method_groups.get(&method.symbol).copied() {
            group
        } else {
            let group = prepared.len();
            method_groups.insert(method.symbol, group);
            prepared.push(PreparedMethodGroup {
                symbol: method.symbol,
                indexes: Vec::new(),
                type_parameters: Vec::new(),
                parameter_symbols: Vec::new(),
                parameter_types: Vec::new(),
                signatures: Vec::new(),
                warm: None,
            });
            group
        };
        let group = &mut prepared[group_index];
        group
            .indexes
            .try_reserve(1)
            .map_err(|_| PropertyObjectError::Capacity(plan.node))?;
        group
            .type_parameters
            .try_reserve(1)
            .map_err(|_| PropertyObjectError::Capacity(plan.node))?;
        group
            .parameter_symbols
            .try_reserve(1)
            .map_err(|_| PropertyObjectError::Capacity(plan.node))?;
        group
            .parameter_types
            .try_reserve(1)
            .map_err(|_| PropertyObjectError::Capacity(plan.node))?;
        let mut parameter_symbols = Vec::new();
        let mut parameter_types = Vec::new();
        parameter_symbols
            .try_reserve_exact(method.parameters.len())
            .map_err(|_| PropertyObjectError::Capacity(plan.node))?;
        parameter_types
            .try_reserve_exact(resolved_signature.parameter_types.len())
            .map_err(|_| PropertyObjectError::Capacity(plan.node))?;
        parameter_symbols.extend(method.parameters.iter().map(|parameter| parameter.symbol));
        parameter_types.extend_from_slice(&resolved_signature.parameter_types);
        group.indexes.push(index);
        group.type_parameters.push(type_parameters);
        group.parameter_symbols.push(parameter_symbols);
        group.parameter_types.push(parameter_types);
    }

    let mut cold_groups = 0usize;
    let mut cold_signatures = 0usize;
    let mut missing_value_links = 0usize;
    let mut missing_signature_links = 0usize;
    for group in &mut prepared {
        let Some(method_symbol) = store.symbol(group.symbol) else {
            return Err(invalid_cache(plan, owner_type));
        };
        let Some(declarations) = method_symbol.declarations() else {
            return Err(invalid_cache(plan, owner_type));
        };
        if declarations.len() != group.indexes.len()
            || declarations
                .iter()
                .zip(&group.indexes)
                .any(|(declaration, index)| *declaration != plan.methods[*index].declaration)
            || plan.properties.iter().all(|property| {
                property.symbol != group.symbol || property.declaration != declarations[0]
            })
        {
            return Err(invalid_cache(plan, owner_type));
        }

        let value = store.value_symbol_links(group.symbol);
        if value.is_some_and(|links| links != &ValueSymbolLinks::default()) {
            let Some(callable_type) = resolved_interface_method_value(store, plan, group.symbol)
            else {
                return Err(invalid_cache(plan, owner_type));
            };
            let signatures = store
                .type_payload(callable_type)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.signatures.as_deref())
                .ok_or_else(|| invalid_cache(plan, owner_type))?;
            for (index, signature) in group.indexes.iter().zip(signatures) {
                let method = &plan.methods[*index];
                let resolved_signature = &resolved[*index];
                if store
                    .signature(*signature)
                    .and_then(super::signatures::Signature::resolved_return_type)
                    != Some(resolved_signature.return_type)
                    || method
                        .parameters
                        .iter()
                        .zip(&resolved_signature.parameter_types)
                        .any(|(parameter, parameter_type)| {
                            store.value_symbol_links(parameter.symbol)
                                != Some(&ValueSymbolLinks {
                                    resolved_type: Some(*parameter_type),
                                    ..ValueSymbolLinks::default()
                                })
                        })
                {
                    return Err(invalid_cache(plan, owner_type));
                }
                published[*index] = callable_type;
            }
            group.warm = Some(callable_type);
            continue;
        }

        cold_groups = cold_groups
            .checked_add(1)
            .ok_or(PropertyObjectError::Capacity(plan.node))?;
        cold_signatures = cold_signatures
            .checked_add(group.indexes.len())
            .ok_or(PropertyObjectError::Capacity(plan.node))?;
        missing_value_links = missing_value_links
            .checked_add(usize::from(value.is_none()))
            .ok_or(PropertyObjectError::Capacity(plan.node))?;
        group
            .signatures
            .try_reserve_exact(group.indexes.len())
            .map_err(|_| PropertyObjectError::Capacity(plan.node))?;
        for index in &group.indexes {
            let method = &plan.methods[*index];
            if store
                .signature_links(method.declaration)
                .is_some_and(|links| links != &SignatureLinks::default())
                || method.parameters.iter().any(|parameter| {
                    store
                        .value_symbol_links(parameter.symbol)
                        .is_some_and(|links| links != &ValueSymbolLinks::default())
                })
            {
                return Err(invalid_cache(plan, owner_type));
            }
            missing_signature_links = missing_signature_links
                .checked_add(usize::from(
                    store.signature_links(method.declaration).is_none(),
                ))
                .ok_or(PropertyObjectError::Capacity(plan.node))?;
            missing_value_links = missing_value_links
                .checked_add(
                    method
                        .parameters
                        .iter()
                        .filter(|parameter| store.value_symbol_links(parameter.symbol).is_none())
                        .count(),
                )
                .ok_or(PropertyObjectError::Capacity(plan.node))?;
        }
    }

    let mut parameter_batches = Vec::new();
    parameter_batches
        .try_reserve_exact(cold_signatures)
        .map_err(|_| PropertyObjectError::Capacity(plan.node))?;
    if !store.try_reserve_types(cold_groups)
        || !store.try_reserve_signatures(cold_signatures)
        || !store.try_reserve_signature_links(missing_signature_links)
        || !store.try_reserve_value_symbol_links(missing_value_links)
        || !store.try_reserve_callable_signature_parameter_types(cold_signatures)
    {
        return Err(PropertyObjectError::Capacity(plan.node));
    }

    for mut group in prepared {
        if group.warm.is_some() {
            continue;
        }
        let callable_type = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(group.symbol))
            .expect("the interface method transaction reserved its callable object");
        for (((index, type_parameters), parameter_symbols), parameter_types) in group
            .indexes
            .iter()
            .zip(group.type_parameters)
            .zip(group.parameter_symbols)
            .zip(group.parameter_types)
        {
            let method = &plan.methods[*index];
            let resolved_signature = &resolved[*index];
            let minimum = i32::try_from(method.minimum_argument_count)
                .expect("the interface method plan checked its parameter count");
            let signature = store
                .alloc_signature(
                    method.flags,
                    Some(method.declaration),
                    type_parameters,
                    None,
                    parameter_symbols,
                    Some(resolved_signature.return_type),
                    None,
                    minimum,
                )
                .expect("the interface method transaction reserved its signature");
            group.signatures.push(signature);
            assert!(store.set_signature_links(
                method.declaration,
                SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                },
            ));
            for (parameter, parameter_type) in method
                .parameters
                .iter()
                .zip(&resolved_signature.parameter_types)
            {
                assert!(store.set_value_symbol_links(
                    parameter.symbol,
                    ValueSymbolLinks {
                        resolved_type: Some(*parameter_type),
                        ..ValueSymbolLinks::default()
                    },
                ));
            }
            parameter_batches.push((signature, parameter_types));
            published[*index] = callable_type;
        }
        assert!(store.set_value_symbol_links(
            group.symbol,
            ValueSymbolLinks {
                resolved_type: Some(callable_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(store.set_structured_type_members(
            callable_type,
            None,
            None,
            Some(group.signatures),
            None,
            None,
        ));
    }
    if !parameter_batches.is_empty()
        && !store.set_callable_signature_parameter_types_batch(parameter_batches)
    {
        return Err(PropertyObjectError::UnsupportedMember {
            node: plan
                .methods
                .first()
                .map_or(plan.node, |method| method.declaration),
            kind: SyntaxKind::MethodSignature,
        });
    }
    Ok(published)
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
                TypeData::Object(_) if record.symbol().is_none() => {
                    validated_synthetic_object_properties(store, record.id()).and_then(
                        |properties| {
                            (properties.len() == plan.properties.len()
                                && properties.iter().zip(&plan.properties).all(
                                    |(actual, planned)| {
                                        actual.name == planned.name
                                            && actual.readonly == planned.readonly
                                    },
                                ))
                            .then(|| {
                                properties
                                    .into_iter()
                                    .map(|property| property.type_)
                                    .collect()
                            })
                        },
                    )
                }
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
                    valid_declared_property_check_flags(store, property)
                        && expected_declared_property_links(store, plan, property, *type_).as_ref()
                            == store.value_symbol_links(property.symbol)
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
    let valid_calls = valid_planned_call_signature_set(store, plan)
        && call_types.len() == plan.call_signatures.len()
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
    if !valid_planned_call_signature_set(store, plan) {
        return Err(invalid_cache(plan, type_));
    }
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
        || plan
            .properties
            .iter()
            .zip(property_types)
            .any(|(property, property_type)| {
                expected_declared_property_links(store, plan, property, *property_type).is_none()
                    || store
                        .symbol(property.symbol)
                        .is_some_and(|symbol| symbol.flags().contains(SymbolFlags::METHOD))
                        && resolved_interface_method_value(store, plan, property.symbol)
                            != Some(*property_type)
            })
        || plan.accessors.iter().any(|accessor| {
            cached_planned_type_identity(store, accessor.type_node).is_none()
                || accessor.parameter.is_some_and(|parameter| {
                    store
                        .value_symbol_links(parameter.symbol)
                        .is_some_and(|links| links != &ValueSymbolLinks::default())
                })
        })
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

    let mut seen_keys = HashSet::with_capacity(index_types.len());
    let valid_indexes = plan
        .indexes
        .iter()
        .zip(index_types)
        .all(|(planned, (key_type, _))| {
            cached_planned_type_identity(store, planned.key_type_node) == Some(*key_type)
                && seen_keys.insert(*key_type)
        });
    if !valid_indexes {
        return Err(invalid_cache(plan, type_));
    }
    let call_type_parameters = plan
        .call_signatures
        .iter()
        .map(|signature| {
            resolved_declared_signature_type_parameters(
                store,
                signature.declaration,
                &signature.type_parameters,
            )
        })
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| invalid_cache(plan, type_))?;
    let missing_accessor_links = plan
        .accessors
        .iter()
        .filter_map(|accessor| accessor.parameter)
        .filter(|parameter| store.value_symbol_links(parameter.symbol).is_none())
        .count();
    let annotated_signature_count = plan
        .call_signatures
        .iter()
        .filter(|signature| !signature.implicit_any_return)
        .count();
    if !store.try_reserve_index_infos(plan.indexes.len())
        || !store.try_reserve_signatures(plan.call_signatures.len())
        || !store.try_reserve_value_symbol_links(missing_accessor_links)
        || !store.try_reserve_function_signature_return_annotations(annotated_signature_count)
        || !store.try_reserve_callable_signature_parameter_types(plan.call_signatures.len())
        || !store.try_reserve_declared_call_set_provenance(
            usize::from(!plan.call_signatures.is_empty()),
            plan.call_signatures.len(),
        )
    {
        return Err(PropertyObjectError::Capacity(plan.node));
    }

    for (planned, resolved) in plan.call_signatures.iter().zip(call_types) {
        if !valid_planned_signature_return(store, planned, resolved.return_type)
            || planned
                .parameters
                .iter()
                .zip(&resolved.parameter_types)
                .any(|(parameter, type_)| {
                    planned_call_parameter_type(store, parameter) != Some(*type_)
                        || store
                            .symbol(parameter.symbol)
                            .and_then(ts_binder::semantic::Symbol::value_declaration)
                            .and_then(|declaration| {
                                declared_signature_parameter_is_optional(store, declaration, *type_)
                            })
                            != Some(parameter.optional)
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
        .zip(call_type_parameters)
        .map(|((planned, resolved), type_parameters)| {
            store
                .alloc_signature(
                    planned.flags,
                    Some(planned.declaration),
                    type_parameters,
                    None,
                    planned
                        .parameters
                        .iter()
                        .map(|parameter| parameter.symbol)
                        .collect(),
                    Some(resolved.return_type),
                    None,
                    i32::try_from(planned.min_argument_count())
                        .expect("the call-signature plan validated its minimum arity"),
                )
                .expect("the declared-call plan and reservation validated every identity")
        })
        .collect::<Vec<_>>();
    if !signatures.is_empty() {
        assert!(store.set_declared_call_set_provenance(type_, &signatures));
    }
    for (planned, signature) in plan.call_signatures.iter().zip(&signatures) {
        if !planned.implicit_any_return {
            assert!(store.set_function_signature_return_annotation(
                *signature,
                planned.return_identity_node,
                planned.return_null_literal_identity,
            ));
        }
        assert!(store.set_signature_links(
            planned.declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(*signature),
                ..SignatureLinks::default()
            },
        ));
    }
    let calls = plan
        .call_signatures
        .iter()
        .zip(&signatures)
        .filter_map(|(planned, signature)| (!planned.is_construct()).then_some(*signature))
        .collect::<Vec<_>>();
    let constructs = plan
        .call_signatures
        .iter()
        .zip(&signatures)
        .filter_map(|(planned, signature)| planned.is_construct().then_some(*signature))
        .collect::<Vec<_>>();
    let published_calls = (!calls.is_empty()).then_some(calls);
    let published_constructs = (!constructs.is_empty()).then_some(constructs);

    // All fallible checks precede publication.  The store setters below can
    // only reject foreign identities, all of which were validated above.
    for (property, property_type) in plan.properties.iter().zip(property_types) {
        if store
            .symbol(property.symbol)
            .is_some_and(|symbol| symbol.flags().contains(SymbolFlags::METHOD))
        {
            assert_eq!(
                resolved_interface_method_value(store, plan, property.symbol),
                Some(*property_type),
                "the declared-member plan validated its method callable"
            );
            continue;
        }
        if !store
            .symbol(property.symbol)
            .is_some_and(|symbol| symbol.flags().intersects(SymbolFlags::ACCESSOR))
        {
            assert!(
                store.set_source_property_readonly(property.symbol, property.readonly),
                "the declared-member plan validated a bound source property"
            );
        }
        let links = expected_declared_property_links(store, plan, property, *property_type)
            .expect("the declared-member plan validated its accessor write annotation");
        assert!(store.set_value_symbol_links(property.symbol, links));
    }
    for accessor in &plan.accessors {
        if let Some(parameter) = accessor.parameter {
            let type_ = cached_planned_type_identity(store, parameter.type_node)
                .expect("the declared-member plan resolved its setter annotation");
            assert!(store.set_value_symbol_links(
                parameter.symbol,
                ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                },
            ));
        }
    }
    match plan.kind {
        PropertyObjectKind::TypeLiteral => {
            assert!(store.set_structured_type_members(
                type_,
                plan.members,
                plan.expected_properties(),
                published_calls.clone(),
                published_constructs.clone(),
                published_index_infos,
            ));
        }
        PropertyObjectKind::Interface => {
            assert!(store.set_interface_declared_members(
                type_,
                true,
                plan.members,
                published_calls.clone(),
                published_constructs.clone(),
                published_index_infos.clone(),
            ));
            assert!(store.set_interface_base_resolution(type_, true, None, None));
            assert!(store.set_structured_type_members(
                type_,
                plan.members,
                plan.expected_properties(),
                published_calls,
                published_constructs,
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

/// Publishes a generic interface's declared properties, methods, and indexes
/// without resolving its lazy instantiated member table.
///
/// The caller must resolve the interface's direct bases first. The publisher
/// checks the full binder-owned target and every planned member before it
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
        || plan.alias_symbol.is_some()
        || !plan.call_signatures.is_empty()
        || plan.properties.len() != property_types.len()
        || property_types
            .iter()
            .any(|type_| store.type_payload(*type_).is_none())
    {
        return Err(invalid());
    }
    let index_types = generic_index_types(store, plan, target).ok_or_else(invalid)?;
    let method_types =
        generic_method_signature_types(store, plan, property_types).ok_or_else(invalid)?;

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
                    let method = store
                        .symbol(property.symbol)
                        .is_some_and(|record| record.flags().contains(SymbolFlags::METHOD));
                    let expected_type = if method {
                        resolved_interface_method_value(store, plan, property.symbol)
                    } else {
                        Some(*property_type)
                    };
                    declared_members
                        .and_then(|members| store.symbol_table(members))
                        .and_then(|members| members.get_source(&property.name))
                        == Some(property.symbol)
                        && expected_type.is_some_and(|type_| {
                            store.value_symbol_links(property.symbol)
                                == Some(&ValueSymbolLinks {
                                    resolved_type: Some(type_),
                                    ..ValueSymbolLinks::default()
                                })
                        })
                        && store.symbol(property.symbol).is_some_and(|record| {
                            record.check_flags()
                                == if method {
                                    CheckFlags::NONE
                                } else {
                                    source_property_check_flags(property.readonly)
                                }
                        })
                })
            || interface
                .declared_index_infos
                .as_deref()
                .unwrap_or_default()
                .iter()
                .zip(&index_types)
                .any(|(index, (key, value))| {
                    store
                        .index_info(*index)
                        .is_none_or(|info| info.key_type() != *key || info.value_type() != *value)
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
        .filter(|property| {
            !store
                .symbol(property.symbol)
                .is_some_and(|record| record.flags().contains(SymbolFlags::METHOD))
                && store.value_symbol_links(property.symbol).is_none()
        })
        .count();
    if !store.try_reserve_checker_symbol_allocations(0, usize::from(prepared.is_some()))
        || !store.try_reserve_value_symbol_links(missing_links)
        || !store.try_reserve_index_infos(index_types.len())
    {
        return Err(PropertyObjectError::Capacity(plan.node));
    }
    let method_values = publish_interface_method_values(store, plan, &method_types)?;
    let declared_members = prepared.map(|table| store.alloc_prepared_symbol_table(table));
    let index_infos = plan
        .indexes
        .iter()
        .zip(&index_types)
        .map(|(planned, (key_type, value_type))| {
            store
                .alloc_index_info(
                    *key_type,
                    *value_type,
                    planned.readonly,
                    Some(planned.declaration),
                    Vec::new(),
                )
                .expect("the generic index plan and reservation validated every identity")
        })
        .collect::<Vec<_>>();
    for (property, property_type) in plan.properties.iter().zip(property_types) {
        if store
            .symbol(property.symbol)
            .is_some_and(|record| record.flags().contains(SymbolFlags::METHOD))
        {
            let method = plan
                .methods
                .iter()
                .position(|method| method.symbol == property.symbol)
                .expect("the generic method plan retained its declared property");
            assert_eq!(
                store
                    .value_symbol_links(property.symbol)
                    .and_then(|links| links.resolved_type),
                Some(method_values[method]),
            );
        } else {
            assert!(store.set_source_property_readonly(property.symbol, property.readonly));
            assert!(store.set_value_symbol_links(
                property.symbol,
                ValueSymbolLinks {
                    resolved_type: Some(*property_type),
                    ..ValueSymbolLinks::default()
                },
            ));
        }
        assert_eq!(
            store.insert_symbol(
                declared_members.expect("a generic property owns a declared member table"),
                EscapedName::source(&property.name),
                property.symbol,
            ),
            Some(None)
        );
    }
    assert!(store.set_interface_declared_members(
        target,
        true,
        declared_members,
        None,
        None,
        (!index_infos.is_empty()).then_some(index_infos),
    ));
    Ok(target)
}

fn generic_index_types(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    target: TypeId,
) -> Option<Vec<(TypeId, TypeId)>> {
    let reference = validate_direct_generic_reference(store, target).ok()?;
    let mut keys = HashSet::with_capacity(plan.indexes.len());
    let mut indexes = Vec::with_capacity(plan.indexes.len());
    for index in &plan.indexes {
        let key_type = cached_planned_type_identity(store, index.key_type_node)?;
        let value_type =
            cached_planned_type_identity(store, index.value_type_node).or_else(|| {
                index.value_type_parameter.and_then(|parameter| {
                    let type_ = store.declared_type_links(parameter)?.declared_type?;
                    (reference.type_arguments.contains(&type_)
                        && cached_ordinary_type_parameter_owner(store, type_) == Some(parameter))
                    .then_some(type_)
                })
            })?;
        if !keys.insert(key_type)
            || store.type_payload(key_type).is_none()
            || store.type_payload(value_type).is_none()
        {
            return None;
        }
        indexes.push((key_type, value_type));
    }
    Some(indexes)
}

fn generic_method_signature_types(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    property_types: &[TypeId],
) -> Option<Vec<ResolvedCallSignatureTypes>> {
    let mut signatures = Vec::with_capacity(plan.methods.len());
    for method in &plan.methods {
        let property = plan
            .properties
            .iter()
            .position(|property| property.symbol == method.symbol)?;
        let return_type =
            cached_planned_type_identity(store, method.return_type).or_else(|| {
                (plan.properties[property].declaration == method.declaration)
                    .then_some(property_types[property])
            })?;
        if plan.properties[property].declaration == method.declaration
            && property_types[property] != return_type
        {
            return None;
        }
        let parameter_types = method
            .parameters
            .iter()
            .map(|parameter| {
                cached_annotation_identity(
                    store,
                    parameter.identity_node,
                    parameter.null_literal_identity,
                )
            })
            .collect::<Option<Vec<_>>>()?;
        signatures.push(ResolvedCallSignatureTypes {
            parameter_types,
            return_type,
        });
    }
    Some(signatures)
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
    let Some(owner_declarations) = owner
        .declarations()
        .filter(|declarations| !declarations.is_empty())
    else {
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
        || !owner.flags().contains(SymbolFlags::INTERFACE)
        || owner
            .flags()
            .without(SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT)
            != SymbolFlags::NONE
        || owner.check_flags() != CheckFlags::NONE
        || owner_declarations != plan.declarations.as_slice()
        || plan.declarations.first().copied() != Some(plan.node)
        || owner.value_declaration().is_some()
        || owner.members() != Some(raw_members)
        || owner.exports().is_some()
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
        || interface.declared_call_signatures.is_some()
        || interface.declared_construct_signatures.is_some()
        || if interface.declared_members_resolved {
            !valid_declared_index_infos(store, interface.declared_index_infos.as_deref(), plan)
        } else {
            interface.declared_index_infos.is_some()
        }
        || raw_table.len()
            != reference.type_arguments.len()
                + plan.properties.len()
                + usize::from(!plan.indexes.is_empty())
    {
        return false;
    }
    match (
        plan.heritage.as_ref(),
        interface.resolved_base_types.as_deref(),
    ) {
        (None, None) => {}
        (Some(heritage), Some(bases)) => {
            if heritage.bases.is_empty()
                || heritage.bases.len() > 2
                || heritage.bases.len() != bases.len()
            {
                return false;
            }
            for (planned, base) in heritage.bases.iter().zip(bases) {
                if planned.kind != DirectInterfaceBaseKind::Interface {
                    return false;
                }
                if planned.type_arguments.is_empty() {
                    if !matches!(
                        validate_resolved_declared_property_object(store, *base),
                        DeclaredPropertyObjectValidation::Valid(
                            DeclaredPropertyObjectProof::Interface,
                        )
                    ) || store
                        .type_payload(*base)
                        .and_then(TypeRecord::symbol)
                        .and_then(|symbol| store.get_merged_symbol(symbol))
                        != Some(planned.symbol)
                    {
                        return false;
                    }
                    continue;
                }

                let Ok(base_reference) = validate_direct_generic_reference(store, *base) else {
                    return false;
                };
                let arguments_match = if base_reference.type_arguments == reference.type_arguments {
                    true
                } else {
                    let mut previous_position = None;
                    planned.type_arguments.len() == base_reference.type_arguments.len()
                        && planned
                            .type_arguments
                            .iter()
                            .zip(&base_reference.type_arguments)
                            .all(|(annotation, argument)| {
                                if cached_planned_type_identity(store, *annotation)
                                    != Some(*argument)
                                {
                                    return false;
                                }
                                let Some(position) = reference
                                    .type_arguments
                                    .iter()
                                    .position(|parameter| parameter == argument)
                                else {
                                    return true;
                                };
                                if previous_position.is_some_and(|previous| position <= previous) {
                                    return false;
                                }
                                previous_position = Some(position);
                                cached_ordinary_type_parameter_owner(store, *argument)
                                    .and_then(|parameter| store.get_parent_of_symbol(parameter))
                                    == Some(plan.symbol)
                            })
                };
                if !arguments_match
                    || store
                        .type_payload(base_reference.target)
                        .and_then(TypeRecord::symbol)
                        .and_then(|symbol| store.get_merged_symbol(symbol))
                        != Some(planned.symbol)
                {
                    return false;
                }
            }
        }
        _ => return false,
    }

    let parent = store.get_parent_of_symbol(plan.symbol);
    if owner.parent().is_some() != parent.is_some()
        || parent.is_some_and(|parent| {
            store
                .symbol(parent)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| store.symbol_table(exports))
                .and_then(|exports| exports.get(owner.name()))
                .and_then(|symbol| store.get_merged_symbol(symbol))
                != Some(plan.symbol)
        })
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
        if store.get_parent_of_symbol(symbol) != Some(plan.symbol)
            || raw_table
                .get(record.name())
                .and_then(|parameter| store.get_merged_symbol(parameter))
                != Some(symbol)
            || !symbols.insert(symbol)
        {
            return false;
        }
    }
    let mut names = HashSet::with_capacity(plan.properties.len());
    let mut declarations = HashSet::with_capacity(plan.properties.len());
    let mut previous_position = None;
    for property in &plan.properties {
        let Some(record) = store.symbol(property.symbol) else {
            return false;
        };
        let Some(property_declarations) = record
            .declarations()
            .filter(|declarations| !declarations.is_empty())
        else {
            return false;
        };
        let Some(SourceNodeParent::Parent(property_owner)) =
            store.source_node_parent(property.declaration)
        else {
            return false;
        };
        let Some(owner_index) = owner_declarations
            .iter()
            .position(|declaration| *declaration == property_owner)
        else {
            return false;
        };
        let position = (owner_index, property.declaration);
        let method = record.flags().contains(SymbolFlags::METHOD);
        let expected_flags = if method {
            SymbolFlags::METHOD
        } else {
            SymbolFlags::PROPERTY
                | if property.optional {
                    SymbolFlags::OPTIONAL
                } else {
                    SymbolFlags::NONE
                }
        };
        let expected_checks = source_property_check_flags(property.readonly);
        if record.flags() != expected_flags
            || record.check_flags() != CheckFlags::NONE && record.check_flags() != expected_checks
            || method && (property.optional || property.readonly)
            || method
                != plan
                    .methods
                    .iter()
                    .any(|planned| planned.symbol == property.symbol)
            || record.name().as_utf8() != Some(property.name.as_str())
            || property_declarations.first().copied() != Some(property.declaration)
            || record.value_declaration() != Some(property.declaration)
            || store.get_parent_of_symbol(property.symbol) != Some(plan.symbol)
            || record.members().is_some()
            || record.exports().is_some()
            || record.export_symbol().is_some()
            || store.get_merged_symbol(property.symbol) != Some(property.symbol)
            || raw_table
                .get(record.name())
                .and_then(|symbol| store.get_merged_symbol(symbol))
                != Some(property.symbol)
            || previous_position.is_some_and(|previous| previous >= position)
            || store.source_node_parent(property.name_node)
                != Some(SourceNodeParent::Parent(property.declaration))
            || store.source_node_parent(property.type_node)
                != Some(SourceNodeParent::Parent(property.declaration))
            || !symbols.insert(property.symbol)
            || !names.insert(property.name.as_str())
        {
            return false;
        }
        if !property_declarations.iter().all(|declaration| {
            let Some(SourceNodeParent::Parent(owner)) = store.source_node_parent(*declaration)
            else {
                return false;
            };
            owner_declarations.contains(&owner)
                && declaration.is_for(owner.arena, owner.file)
                && if method {
                    store.source_node_kind(*declaration) == Some(SyntaxKind::MethodSignature)
                } else {
                    matches!(
                        store.source_node_kind(*declaration),
                        Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
                    )
                }
                && declarations.insert(*declaration)
        }) {
            return false;
        }
        previous_position = Some(position);
    }
    if let Some(first) = plan.indexes.first() {
        let Some(index_record) = store.symbol(first.symbol) else {
            return false;
        };
        let expected_declarations = plan
            .indexes
            .iter()
            .map(|index| index.declaration)
            .collect::<Vec<_>>();
        if index_record.flags() != SymbolFlags::SIGNATURE
            || index_record.check_flags() != CheckFlags::NONE
            || index_record.name() != InternalSymbolName::Index.as_ref()
            || index_record.declarations() != Some(expected_declarations.as_slice())
            || index_record.value_declaration().is_some()
            || index_record.members().is_some()
            || index_record.exports().is_some()
            || index_record.export_symbol().is_some()
            || store.get_parent_of_symbol(first.symbol) != Some(plan.symbol)
            || raw_table.get(InternalSymbolName::Index.as_ref()) != Some(first.symbol)
            || plan.indexes.iter().any(|index| {
                index.symbol != first.symbol
                    || store.source_node_kind(index.declaration) != Some(SyntaxKind::IndexSignature)
                    || !matches!(
                        store.source_node_parent(index.declaration),
                        Some(SourceNodeParent::Parent(owner))
                            if owner_declarations.contains(&owner)
                    )
            })
            || !symbols.insert(first.symbol)
        {
            return false;
        }
    }
    raw_table.iter().all(|(name, symbol)| {
        store
            .get_merged_symbol(symbol)
            .is_some_and(|symbol| symbols.contains(&symbol))
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

fn valid_generic_structured_property(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    interface: &InterfaceTypeData,
    planned: &PlannedProperty,
    actual: SemanticSymbolId,
) -> bool {
    if actual == planned.symbol {
        return true;
    }
    let Some(declared) = store.symbol(planned.symbol) else {
        return false;
    };
    let Some(property) = store.symbol(actual) else {
        return false;
    };
    let Some(links) = store.value_symbol_links(actual) else {
        return false;
    };
    let Some(mapper) = links.mapper else {
        return false;
    };
    let Some(parameters) = interface.reference.resolved_type_arguments.as_deref() else {
        return false;
    };
    let Some(this_type) = interface.this_type else {
        return false;
    };
    let mapper_sources = parameters
        .iter()
        .copied()
        .chain(std::iter::once(this_type))
        .collect::<Vec<_>>();
    let mapper_targets = parameters
        .iter()
        .copied()
        .chain(std::iter::once(target))
        .collect::<Vec<_>>();
    let checks = CheckFlags::INSTANTIATED
        | (declared.check_flags()
            & (CheckFlags::READONLY
                | CheckFlags::LATE
                | CheckFlags::OPTIONAL_PARAMETER
                | CheckFlags::REST_PARAMETER));

    property.flags() == declared.flags() | SymbolFlags::TRANSIENT
        && property.check_flags() == checks
        && property.name() == declared.name()
        && property.declarations() == declared.declarations()
        && property.value_declaration() == declared.value_declaration()
        && property.parent() == declared.parent()
        && property.members().is_none()
        && property.exports().is_none()
        && property.export_symbol().is_none()
        && store.get_merged_symbol(actual) == Some(actual)
        && store.type_mapper_has_exact_endpoints(mapper, &mapper_sources, &mapper_targets)
            == Some(true)
        && links
            == &(ValueSymbolLinks {
                resolved_type: links.resolved_type,
                target: Some(planned.symbol),
                mapper: Some(mapper),
                name_type: store
                    .value_symbol_links(planned.symbol)
                    .and_then(|declared| declared.name_type),
                ..ValueSymbolLinks::default()
            })
        && links
            .resolved_type
            .is_none_or(|type_| store.type_payload(type_).is_some())
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
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return false;
    }
    let properties = structured.properties.as_deref().unwrap_or_default();
    if properties.len() < plan.properties.len() {
        return false;
    }
    let mut expected = Vec::with_capacity(properties.len());
    for (actual, planned) in properties.iter().zip(&plan.properties) {
        if !valid_generic_structured_property(store, target, interface, planned, *actual) {
            return false;
        }
        expected.push(*actual);
    }
    let mut names = plan
        .properties
        .iter()
        .map(|property| EscapedName::source(&property.name))
        .collect::<HashSet<_>>();
    let mut expected_indexes = interface
        .declared_index_infos
        .as_deref()
        .unwrap_or_default()
        .to_vec();
    let Some(mut index_keys) = expected_indexes
        .iter()
        .map(|index| {
            store
                .index_info(*index)
                .map(super::signatures::IndexInfo::key_type)
        })
        .collect::<Option<HashSet<_>>>()
    else {
        return false;
    };
    if let Some(heritage) = plan.heritage.as_ref() {
        let Some(bases) = interface.resolved_base_types.as_deref() else {
            return false;
        };
        if bases.len() != heritage.bases.len() {
            return false;
        }
        for (planned, base) in heritage.bases.iter().zip(bases) {
            let Some(record) = store.type_payload(*base) else {
                return false;
            };
            let owner = if planned.type_arguments.is_empty() {
                if !matches!(
                    validate_resolved_declared_property_object(store, *base),
                    DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::Interface,)
                ) {
                    return false;
                }
                record.symbol()
            } else {
                let Ok(reference) = validate_direct_generic_reference(store, *base) else {
                    return false;
                };
                store
                    .type_payload(reference.target)
                    .and_then(TypeRecord::symbol)
            };
            if owner.and_then(|symbol| store.get_merged_symbol(symbol)) != Some(planned.symbol)
                || !record
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED)
            {
                return false;
            }
            let Some(base_members) = record.data().structured() else {
                return false;
            };
            for property in base_members.properties.as_deref().unwrap_or_default() {
                let Some(property_record) = store.symbol(*property) else {
                    return false;
                };
                if names.insert(property_record.name().to_owned()) {
                    expected.push(*property);
                }
            }
            for index in base_members.index_infos.as_deref().unwrap_or_default() {
                let Some(info) = store.index_info(*index) else {
                    return false;
                };
                if index_keys.insert(info.key_type()) {
                    expected_indexes.push(*index);
                }
            }
        }
    }
    if properties != expected.as_slice()
        || properties.is_empty() != structured.properties.is_none()
        || structured.index_infos.as_deref()
            != (!expected_indexes.is_empty()).then_some(expected_indexes.as_slice())
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
                && properties.iter().all(|property| {
                    store
                        .symbol(*property)
                        .is_some_and(|record| table.get(record.name()) == Some(*property))
                })
        })
}

fn valid_object_literal_owner(store: &CanonicalTypeMapperStore, plan: &PropertyObjectPlan) -> bool {
    let Some(owner) = store.symbol(plan.symbol) else {
        return false;
    };
    store.get_merged_symbol(plan.symbol) == Some(plan.symbol)
        && owner.flags() == SymbolFlags::OBJECT_LITERAL
        && owner.check_flags() == CheckFlags::NONE
        && owner.name() == InternalSymbolName::Object.as_ref()
        && owner.declarations() == Some(&[plan.node])
        && owner.value_declaration() == Some(plan.node)
        && owner.members() == plan.members
        && owner.parent().is_none()
        && owner.exports().is_none()
        && owner.export_symbol().is_none()
}

fn valid_bound_object_literal_property(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    property: &PlannedProperty,
) -> bool {
    let Some(bound) = store.symbol(property.symbol) else {
        return false;
    };
    store.get_merged_symbol(property.symbol) == Some(property.symbol)
        && bound.flags() == SymbolFlags::PROPERTY
        && bound.check_flags() == CheckFlags::NONE
        && bound.name().as_utf8() == Some(property.name.as_str())
        && bound.declarations() == Some(&[property.declaration])
        && bound.value_declaration() == Some(property.declaration)
        && bound.members().is_none()
        && bound.exports().is_none()
        && bound.parent() == Some(plan.symbol)
        && bound.export_symbol().is_none()
        && store.source_node_parent(property.declaration)
            == Some(SourceNodeParent::Parent(plan.node))
        && store.source_node_parent(property.name_node)
            == Some(SourceNodeParent::Parent(property.declaration))
        && store.source_node_parent(property.type_node)
            == Some(SourceNodeParent::Parent(property.declaration))
        && plan
            .members
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source(&property.name))
            == Some(property.symbol)
}

fn inherited_const_object_literal(store: &CanonicalTypeMapperStore, node: NodeRef) -> bool {
    let mut current = node;
    while let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(current) {
        match store.source_node_kind(parent) {
            Some(SyntaxKind::ParenthesizedExpression) => current = parent,
            Some(SyntaxKind::PropertyAssignment) => return true,
            _ => return false,
        }
    }
    false
}

fn uses_synthetic_const_object(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    property_types: &[TypeId],
) -> bool {
    plan.const_context
        && (inherited_const_object_literal(store, plan.node)
            || property_types.iter().any(|type_| {
                !matches!(
                    store.type_payload(*type_).map(TypeRecord::data),
                    Some(TypeData::Literal(_))
                )
            }))
}

fn publish_synthetic_object_literal(
    store: &mut CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    properties: &[ResolvedObjectProperty],
) -> Result<TypeId, PropertyObjectError> {
    if properties.iter().any(|property| {
        let name = EscapedName::source(&property.name);
        name.as_ref().is_reserved_member_name()
            || name.as_ref().is_private_identifier()
            || name.as_ref().is_late_bound()
            || store.type_payload(property.type_).is_none()
    }) {
        return Err(PropertyObjectError::InvalidObjectLiteral(plan.node));
    }
    let prepared_members = PreparedSymbolTable::new(properties.len())
        .ok_or(PropertyObjectError::Capacity(plan.node))?;
    let mut symbols = Vec::new();
    symbols
        .try_reserve_exact(properties.len())
        .map_err(|_| PropertyObjectError::Capacity(plan.node))?;
    if !store.try_reserve_types(1)
        || !store.try_reserve_checker_symbol_allocations(properties.len(), 1)
        || !store.try_reserve_value_symbol_links(properties.len())
        || !store
            .try_reserve_type_node_links(usize::from(store.type_node_links(plan.node).is_none()))
    {
        return Err(PropertyObjectError::Capacity(plan.node));
    }

    let members = store.alloc_prepared_symbol_table(prepared_members);
    for property in properties {
        let flags = SymbolFlags::PROPERTY
            | if property.optional {
                SymbolFlags::OPTIONAL
            } else {
                SymbolFlags::NONE
            };
        let symbol = store.alloc_transient_symbol(
            flags,
            EscapedName::source(&property.name),
            source_property_check_flags(property.readonly),
        );
        assert!(store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(property.type_),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            store.insert_symbol(members, EscapedName::source(&property.name), symbol),
            Some(None)
        );
        symbols.push(symbol);
    }
    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
        .expect("the synthetic object has no source-owned symbol");
    assert!(store.set_structured_type_members(
        type_,
        Some(members),
        (!symbols.is_empty()).then_some(symbols),
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

pub(super) fn publish_object_literal(
    store: &mut CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    property_types: &[TypeId],
) -> Result<TypeId, PropertyObjectError> {
    debug_assert_eq!(plan.kind, PropertyObjectKind::ObjectLiteral);
    if is_javascript_expando_object_plan(store, plan) {
        return publish_javascript_expando_object_literal(store, plan, property_types);
    }
    if !plan.spreads.is_empty() {
        return Err(PropertyObjectError::InvalidObjectLiteral(plan.node));
    }
    if let Some(state) = object_literal_state(store, plan)? {
        validate_resolved_property_types(store, plan, property_types)?;
        return Ok(state.type_id());
    }
    if property_types.len() != plan.properties.len()
        || plan
            .properties
            .iter()
            .zip(property_types)
            .any(|(property, type_)| !valid_object_literal_property_type(store, property, *type_))
        || plan.properties.first().is_some_and(|first| {
            plan.properties
                .iter()
                .any(|property| property.readonly != first.readonly)
        })
        || !unresolved_property_links(store, plan)
    {
        return Err(PropertyObjectError::InvalidObjectLiteral(plan.node));
    }
    if !valid_object_literal_owner(store, plan) {
        return Err(PropertyObjectError::InvalidObjectLiteral(plan.node));
    }
    let object_flags = expected_object_literal_flags(store, property_types)
        .ok_or(PropertyObjectError::InvalidObjectLiteral(plan.node))?;
    let cloned_symbol_data = plan
        .properties
        .iter()
        .map(|property| {
            let bound = store.symbol(property.symbol)?;
            if !valid_bound_object_literal_property(store, plan, property) {
                return None;
            }
            let mut data = SymbolData::new(
                bound.flags() | SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
                bound.name().to_owned(),
            );
            data.check_flags = source_property_check_flags(property.readonly);
            data.declarations = bound.declarations().map(<[NodeRef]>::to_vec);
            data.value_declaration = bound.value_declaration();
            data.parent = bound.parent();
            Some(data)
        })
        .collect::<Option<Vec<_>>>()
        .ok_or(PropertyObjectError::InvalidObjectLiteral(plan.node))?;
    if uses_synthetic_const_object(store, plan, property_types) {
        let properties = plan
            .properties
            .iter()
            .zip(property_types)
            .map(|(property, type_)| ResolvedObjectProperty {
                name: property.name.clone(),
                type_: *type_,
                readonly: property.readonly,
                optional: property.optional,
            })
            .collect::<Vec<_>>();
        return publish_synthetic_object_literal(store, plan, &properties);
    }
    let prepared_members = PreparedSymbolTable::new(plan.properties.len())
        .ok_or(PropertyObjectError::Capacity(plan.node))?;
    let mut cloned_properties = Vec::new();
    cloned_properties
        .try_reserve_exact(plan.properties.len())
        .map_err(|_| PropertyObjectError::Capacity(plan.node))?;
    if !store.try_reserve_types(1)
        || !store.try_reserve_checker_symbol_allocations(plan.properties.len(), 1)
        || !store.try_reserve_value_symbol_links(plan.properties.len())
        || !store
            .try_reserve_type_node_links(usize::from(store.type_node_links(plan.node).is_none()))
    {
        return Err(PropertyObjectError::Capacity(plan.node));
    }

    let members = store.alloc_prepared_symbol_table(prepared_members);
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

fn publish_javascript_expando_object_literal(
    store: &mut CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    property_types: &[TypeId],
) -> Result<TypeId, PropertyObjectError> {
    if property_types.len() != plan.properties.len()
        || !plan.spreads.is_empty()
        || property_types
            .iter()
            .any(|type_| store.type_payload(*type_).is_none())
    {
        return Err(PropertyObjectError::InvalidObjectLiteral(plan.node));
    }
    if let Some(state) = javascript_expando_object_state(store, plan)? {
        if plan
            .properties
            .iter()
            .zip(property_types)
            .any(|(property, expected)| {
                store
                    .value_symbol_links(property.symbol)
                    .and_then(|links| links.resolved_type)
                    != Some(*expected)
            })
        {
            return Err(invalid_cache(plan, state.type_id()));
        }
        return Ok(state.type_id());
    }
    if !store.try_reserve_types(1)
        || !store.try_reserve_value_symbol_links(plan.properties.len())
        || !store.try_reserve_type_node_links(1)
    {
        return Err(PropertyObjectError::Capacity(plan.node));
    }
    for (property, type_) in plan.properties.iter().zip(property_types) {
        if !store.set_value_symbol_links(
            property.symbol,
            ValueSymbolLinks {
                resolved_type: Some(*type_),
                ..ValueSymbolLinks::default()
            },
        ) {
            return Err(PropertyObjectError::InvalidObjectLiteral(plan.node));
        }
    }
    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(plan.symbol))
        .ok_or(PropertyObjectError::InvalidObjectLiteral(plan.node))?;
    let properties = plan
        .properties
        .iter()
        .map(|property| property.symbol)
        .collect::<Vec<_>>();
    if !store.set_structured_type_members(type_, plan.members, Some(properties), None, None, None)
        || !store.set_type_node_links(
            plan.node,
            TypeNodeLinks {
                resolved_type: Some(type_),
                ..TypeNodeLinks::default()
            },
        )
    {
        return Err(PropertyObjectError::InvalidObjectLiteral(plan.node));
    }
    Ok(type_)
}

enum SpreadDonorValidation {
    Valid(Vec<ResolvedObjectProperty>),
    Unsupported,
    Malformed,
}

fn projected_spread_donor_properties(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<Vec<ResolvedObjectProperty>> {
    let record = store.type_payload(type_)?;
    let structured = record.data().structured()?;
    let properties = structured.properties.as_deref().unwrap_or_default();
    let indexes = structured.index_infos.as_deref().unwrap_or_default();
    if structured.properties.is_some() == properties.is_empty() {
        return None;
    }
    let table = match structured.members {
        Some(members) => Some(store.symbol_table(members)?),
        None if properties.is_empty() => None,
        None => return None,
    };
    if table.is_some_and(|table| {
        table.len() != properties.len() + usize::from(!indexes.is_empty())
            || !indexes.is_empty() && table.get(InternalSymbolName::Index.as_ref()).is_none()
    }) {
        return None;
    }
    let mut seen = HashSet::with_capacity(properties.len());
    let mut result = Vec::with_capacity(properties.len());
    for symbol in properties {
        if !seen.insert(*symbol) {
            return None;
        }
        let property = store.symbol(*symbol)?;
        let name = property.name().as_utf8()?;
        let type_ = store.value_symbol_links(*symbol)?.resolved_type?;
        let method = property.flags().contains(SymbolFlags::METHOD);
        if !property.flags().contains(SymbolFlags::PROPERTY) && !method
            || property.check_flags().bits() & !CheckFlags::READONLY.bits() != 0
            || property.name().is_reserved_member_name()
            || property.name().is_private_identifier()
            || property.name().is_late_bound()
            || store.get_merged_symbol(*symbol) != Some(*symbol)
            || store.type_payload(type_).is_none()
            || table.and_then(|table| table.get(property.name())) != Some(*symbol)
            || method
                && super::structured_members::valid_interface_method_value(store, *symbol, type_)
                    .is_none()
        {
            return None;
        }
        result.push(ResolvedObjectProperty {
            name: name.to_owned(),
            type_,
            readonly: property.check_flags().contains(CheckFlags::READONLY),
            optional: property.flags().contains(SymbolFlags::OPTIONAL),
        });
    }
    Some(result)
}

#[allow(clippy::too_many_lines)] // Interface ownership, methods, and indexes share one proof.
fn validated_indexed_or_method_interface_spread_donor(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<Vec<ResolvedObjectProperty>> {
    let record = store.type_payload(type_)?;
    let TypeData::Interface(interface) = record.data() else {
        return None;
    };
    let owner = record.symbol()?;
    let owner_record = store.symbol(owner)?;
    let declarations = owner_record.declarations()?;
    let structured = &interface.reference.object.structured;
    let indexes = structured.index_infos.as_deref().unwrap_or_default();
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
        || record.alias().is_some()
        || owner_record.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.value_declaration().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || declarations.is_empty()
        || declarations.iter().any(|declaration| {
            store.source_node_kind(*declaration) != Some(SyntaxKind::InterfaceDeclaration)
        })
        || store.get_merged_symbol(owner) != Some(owner)
        || store
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            != Some(type_)
        || !valid_thisless_interface_identity(interface)
        || !interface.base_types_resolved
        || !interface.declared_members_resolved
        || interface.resolved_base_constructor_type.is_some()
        || interface.declared_call_signatures.is_some()
        || interface.declared_construct_signatures.is_some()
        || interface.declared_members != owner_record.members()
        || structured.constrained != ConstrainedTypeData::default()
        || structured.signatures.is_some()
        || structured.call_signature_count != 0
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || interface.resolved_base_types.is_some()
            && super::structured_members::validate_interface_heritage_members(store, type_)
                != super::structured_members::InterfaceHeritageMembersValidation::Valid
        || interface.resolved_base_types.is_none()
            && interface.declared_index_infos.as_deref() != structured.index_infos.as_deref()
    {
        return None;
    }

    let members = structured.members?;
    let table = store.symbol_table(members)?;
    if !indexes.is_empty() {
        let index_symbol = table.get(InternalSymbolName::Index.as_ref())?;
        let index = store.symbol(index_symbol)?;
        if index.flags() != SymbolFlags::SIGNATURE
            || index.check_flags() != CheckFlags::NONE
            || index.name() != InternalSymbolName::Index.as_ref()
            || index.value_declaration().is_some()
            || index.members().is_some()
            || index.exports().is_some()
            || index.export_symbol().is_some()
            || store.get_parent_of_symbol(index_symbol) != Some(owner)
            || store.get_merged_symbol(index_symbol) != Some(index_symbol)
        {
            return None;
        }
        let mut seen = HashSet::with_capacity(indexes.len());
        for id in indexes {
            let info = store.index_info(*id)?;
            let declaration = info.declaration()?;
            let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(declaration)
            else {
                return None;
            };
            if !seen.insert(*id)
                || store.type_payload(info.key_type()).is_none()
                || store.type_payload(info.value_type()).is_none()
                || info.index_symbol().is_some()
                || !info.components().is_empty()
                || store.source_node_kind(declaration) != Some(SyntaxKind::IndexSignature)
                || !declarations.contains(&parent)
                || index
                    .declarations()
                    .is_none_or(|declarations| !declarations.contains(&declaration))
            {
                return None;
            }
        }
    }

    for property in structured.properties.as_deref().unwrap_or_default() {
        let symbol = store.symbol(*property)?;
        let links = store.value_symbol_links(*property)?;
        let property_type = links.resolved_type?;
        if symbol.parent() != Some(owner) && interface.resolved_base_types.is_none()
            || links
                != &(ValueSymbolLinks {
                    resolved_type: Some(property_type),
                    ..ValueSymbolLinks::default()
                })
            || symbol.flags().contains(SymbolFlags::METHOD)
                && super::structured_members::valid_interface_method_value(
                    store,
                    *property,
                    property_type,
                )
                .is_none()
        {
            return None;
        }
    }
    projected_spread_donor_properties(store, type_)
}

fn validated_source_object_spread_donor(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<Vec<ResolvedObjectProperty>> {
    let record = store.type_payload(type_)?;
    let TypeData::Object(object) = record.data() else {
        return None;
    };
    let owner = record.symbol()?;
    let owner_record = store.symbol(owner)?;
    let [declaration] = owner_record.declarations()? else {
        return None;
    };
    if record.flags() != TypeFlags::OBJECT
        || record.alias().is_some()
        || !valid_object_tail(object)
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.structured.signatures.is_some()
        || object.structured.call_signature_count != 0
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || owner_record.flags() != SymbolFlags::OBJECT_LITERAL
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name() != InternalSymbolName::Object.as_ref()
        || owner_record.value_declaration() != Some(*declaration)
        || owner_record.parent().is_some()
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || store.source_node_kind(*declaration) != Some(SyntaxKind::ObjectLiteralExpression)
        || store
            .type_node_links(*declaration)
            .and_then(|links| links.resolved_type)
            != Some(type_)
    {
        return None;
    }
    let members = object.structured.members?;
    if Some(members) == owner_record.members() {
        return None;
    }
    let table = store.symbol_table(members)?;
    let properties = object.structured.properties.as_deref().unwrap_or_default();
    if table.len() != properties.len()
        || object.structured.properties.is_some() == properties.is_empty()
        || owner_record.members().is_some() == properties.is_empty()
    {
        return None;
    }
    let raw_table = match owner_record.members() {
        Some(members) => Some(store.symbol_table(members)?),
        None => None,
    };
    if raw_table.is_some_and(|table| table.len() != properties.len()) {
        return None;
    }
    let mut seen = HashSet::with_capacity(properties.len());
    let mut seen_raw = HashSet::with_capacity(properties.len());
    let mut result = Vec::with_capacity(properties.len());
    for symbol in properties {
        if !seen.insert(*symbol) {
            return None;
        }
        let property = store.symbol(*symbol)?;
        let links = store.value_symbol_links(*symbol)?;
        let property_type = links.resolved_type?;
        let raw = links.target?;
        let raw_record = store.symbol(raw)?;
        let name = property.name().as_utf8()?;
        if !seen_raw.insert(raw)
            || property.flags() != SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
            || property.check_flags().bits() & !CheckFlags::READONLY.bits() != 0
            || property.name().is_reserved_member_name()
            || property.name().is_private_identifier()
            || property.name().is_late_bound()
            || property.parent() != Some(owner)
            || property.members().is_some()
            || property.exports().is_some()
            || property.export_symbol().is_some()
            || store.get_merged_symbol(*symbol) != Some(*symbol)
            || raw_record.flags() != SymbolFlags::PROPERTY
            || raw_record.check_flags() != CheckFlags::NONE
            || raw_record.name() != property.name()
            || raw_record.declarations() != property.declarations()
            || raw_record.value_declaration() != property.value_declaration()
            || raw_record.parent() != Some(owner)
            || raw_record.members().is_some()
            || raw_record.exports().is_some()
            || raw_record.export_symbol().is_some()
            || store.get_merged_symbol(raw) != Some(raw)
            || store
                .value_symbol_links(raw)
                .is_some_and(|links| links != &ValueSymbolLinks::default())
            || store.type_payload(property_type).is_none()
            || table.get(property.name()) != Some(*symbol)
            || raw_table.and_then(|table| table.get(raw_record.name())) != Some(raw)
            || links
                != &(ValueSymbolLinks {
                    resolved_type: Some(property_type),
                    target: Some(raw),
                    ..ValueSymbolLinks::default()
                })
        {
            return None;
        }
        let [property_declaration] = property.declarations()? else {
            return None;
        };
        if property.value_declaration() != Some(*property_declaration)
            || !matches!(
                store.source_node_kind(*property_declaration),
                Some(SyntaxKind::PropertyAssignment | SyntaxKind::ShorthandPropertyAssignment)
            )
            || store.source_node_parent(*property_declaration)
                != Some(SourceNodeParent::Parent(*declaration))
            || property.check_flags().contains(CheckFlags::READONLY)
                && !matches!(
                    store.type_payload(property_type).map(TypeRecord::data),
                    Some(TypeData::Literal(literal)) if literal.regular_type == property_type
                )
        {
            return None;
        }
        result.push(ResolvedObjectProperty {
            name: name.to_owned(),
            type_: property_type,
            readonly: property.check_flags().contains(CheckFlags::READONLY),
            optional: false,
        });
    }
    let property_types = result
        .iter()
        .map(|property| property.type_)
        .collect::<Vec<_>>();
    (record.object_flags()
        == expected_object_literal_flags(store, &property_types)? | ObjectFlags::MEMBERS_RESOLVED)
        .then_some(result)
}

#[allow(clippy::too_many_lines)] // Authenticate the cached object and all assignment-owned members.
fn validated_javascript_expando_spread_donor(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<Vec<ResolvedObjectProperty>> {
    let record = store.type_payload(type_)?;
    let TypeData::Object(object) = record.data() else {
        return None;
    };
    let owner = record.symbol()?;
    let owner_record = store.symbol(owner)?;
    let [declaration] = owner_record.declarations()? else {
        return None;
    };
    let exports = owner_record.exports()?;
    let Some(SourceNodeParent::Parent(variable)) = store.source_node_parent(*declaration) else {
        return None;
    };
    let Some(SourceNodeParent::Parent(list)) = store.source_node_parent(variable) else {
        return None;
    };
    let Some(SourceNodeParent::Parent(statement)) = store.source_node_parent(list) else {
        return None;
    };
    let Some(SourceNodeParent::Parent(source)) = store.source_node_parent(statement) else {
        return None;
    };
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.alias().is_some()
        || !valid_object_tail(object)
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.structured.members != Some(exports)
        || object.structured.signatures.is_some()
        || object.structured.call_signature_count != 0
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || owner_record.flags() != SymbolFlags::OBJECT_LITERAL
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.name() != InternalSymbolName::Object.as_ref()
        || owner_record.value_declaration() != Some(*declaration)
        || owner_record.members().is_some()
        || owner_record.parent().is_some()
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || store.source_node_kind(*declaration) != Some(SyntaxKind::ObjectLiteralExpression)
        || store.source_node_kind(variable) != Some(SyntaxKind::VariableDeclaration)
        || store.source_node_kind(list) != Some(SyntaxKind::VariableDeclarationList)
        || store.source_node_kind(statement) != Some(SyntaxKind::VariableStatement)
        || store.source_node_kind(source) != Some(SyntaxKind::SourceFile)
        || store.type_node_links(*declaration)
            != Some(&TypeNodeLinks {
                resolved_type: Some(type_),
                ..TypeNodeLinks::default()
            })
    {
        return None;
    }

    let table = store.symbol_table(exports)?;
    let properties = object.structured.properties.as_deref()?;
    if properties.is_empty() || table.len() != properties.len() {
        return None;
    }

    let mut seen = HashSet::with_capacity(properties.len());
    let mut result = Vec::with_capacity(properties.len());
    for symbol in properties {
        if !seen.insert(*symbol) {
            return None;
        }
        let property = store.symbol(*symbol)?;
        let [assignment] = property.declarations()? else {
            return None;
        };
        let Some(SourceNodeParent::Parent(assignment_statement)) =
            store.source_node_parent(*assignment)
        else {
            return None;
        };
        let links = store.value_symbol_links(*symbol)?;
        let property_type = links.resolved_type?;
        let name = property.name().as_utf8()?;
        if property.flags() != SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT
            || property.check_flags() != CheckFlags::NONE
            || property.name().is_reserved_member_name()
            || property.name().is_private_identifier()
            || property.name().is_late_bound()
            || property.value_declaration() != Some(*assignment)
            || property.parent() != Some(owner)
            || property.members().is_some()
            || property.exports().is_some()
            || property.export_symbol().is_some()
            || store.get_merged_symbol(*symbol) != Some(*symbol)
            || !assignment.is_for(declaration.arena, declaration.file)
            || store.source_node_kind(*assignment) != Some(SyntaxKind::BinaryExpression)
            || store.source_node_kind(assignment_statement) != Some(SyntaxKind::ExpressionStatement)
            || store.source_node_parent(assignment_statement)
                != Some(SourceNodeParent::Parent(source))
            || store.type_payload(property_type).is_none()
            || table.get(property.name()) != Some(*symbol)
            || links
                != &(ValueSymbolLinks {
                    resolved_type: Some(property_type),
                    ..ValueSymbolLinks::default()
                })
        {
            return None;
        }
        result.push(ResolvedObjectProperty {
            name: name.to_owned(),
            type_: property_type,
            readonly: false,
            optional: false,
        });
    }
    Some(result)
}

fn validated_module_namespace_spread_donor(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<Vec<ResolvedObjectProperty>> {
    let record = store.type_payload(type_)?;
    let TypeData::Object(object) = record.data() else {
        return None;
    };
    let owner = record.symbol()?;
    let owner_record = store.symbol(owner)?;
    let [declaration] = owner_record.declarations()? else {
        return None;
    };
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.alias().is_some()
        || !valid_object_tail(object)
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.structured.signatures.is_some()
        || object.structured.call_signature_count != 0
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || owner_record.flags() != SymbolFlags::VALUE_MODULE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.value_declaration() != Some(*declaration)
        || owner_record.members().is_some()
        || owner_record.parent().is_some()
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || store.source_node_kind(*declaration) != Some(SyntaxKind::SourceFile)
        || store.source_node_parent(*declaration) != Some(SourceNodeParent::Root)
    {
        return None;
    }
    let exports = store
        .module_symbol_links(owner)
        .and_then(|links| links.resolved_exports)
        .or_else(|| owner_record.exports())?;
    let export_table = store.symbol_table(exports)?;
    let properties = object.structured.properties.as_deref().unwrap_or_default();
    if object.structured.properties.is_some() == properties.is_empty() {
        return None;
    }
    let table = match object.structured.members {
        Some(members) if !properties.is_empty() => Some(store.symbol_table(members)?),
        None if properties.is_empty() => None,
        _ => return None,
    };
    if table.is_some_and(|table| table.len() != properties.len()) {
        return None;
    }

    let mut seen = HashSet::with_capacity(properties.len());
    let mut result = Vec::with_capacity(properties.len());
    for symbol in properties {
        if !seen.insert(*symbol) {
            return None;
        }
        let property = store.symbol(*symbol)?;
        let links = store.value_symbol_links(*symbol)?;
        let property_type = links.resolved_type?;
        let exported = links.target?;
        let exported_record = store.symbol(exported)?;
        let name = property.name().as_utf8()?;
        if property.flags() != SymbolFlags::PROPERTY
            || property.check_flags() != CheckFlags::NONE
            || property.name().is_reserved_member_name()
            || property.name().is_private_identifier()
            || property.name().is_late_bound()
            || property.declarations().is_some()
            || property.value_declaration().is_some()
            || property.members().is_some()
            || property.exports().is_some()
            || property.parent().is_some()
            || property.export_symbol().is_some()
            || store.get_merged_symbol(*symbol) != Some(*symbol)
            || store.get_merged_symbol(exported) != Some(exported)
            || store.type_payload(property_type).is_none()
            || table.and_then(|table| table.get(property.name())) != Some(*symbol)
            || export_table.get(property.name()) != Some(exported)
            || links
                != &(ValueSymbolLinks {
                    resolved_type: Some(property_type),
                    target: Some(exported),
                    ..ValueSymbolLinks::default()
                })
        {
            return None;
        }
        let value = if exported_record.flags() == SymbolFlags::ALIAS {
            let alias = store.alias_symbol_links(exported)?;
            let AliasTargetState::Resolved(value) = alias.alias_target else {
                return None;
            };
            if alias.type_only_declaration.is_some() {
                return None;
            }
            value
        } else {
            exported
        };
        if store.get_merged_symbol(value) != Some(value)
            || store
                .symbol(value)
                .is_none_or(|value| !value.flags().intersects(SymbolFlags::VALUE))
            || [exported, value].into_iter().any(|target| {
                store
                    .value_symbol_links(target)
                    .and_then(|links| links.resolved_type)
                    .is_some_and(|cached| cached != property_type)
                    || store
                        .source_callable_type_for_owner(target)
                        .is_some_and(|cached| cached != property_type)
            })
        {
            return None;
        }
        result.push(ResolvedObjectProperty {
            name: name.to_owned(),
            type_: property_type,
            readonly: false,
            optional: false,
        });
    }
    Some(result)
}

fn validated_generic_interface_spread_donor(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    type_: TypeId,
) -> Option<Vec<ResolvedObjectProperty>> {
    validate_direct_generic_reference(store, type_).ok()?;
    let array_targets = global_types.map(CanonicalArrayTargets::from_global_types);
    let members = resolve_members_with_array_targets(store, type_, array_targets).ok()?;
    let mut session = InstantiationSession::new(InstantiationLimits::default());
    let mut result = Vec::with_capacity(members.properties().len());

    for symbol in members.properties() {
        let property = store.symbol(*symbol)?;
        let name = property.name().as_utf8()?.to_owned();
        let readonly = property.check_flags().contains(CheckFlags::READONLY);
        if !property.flags().contains(SymbolFlags::PROPERTY)
            || property.flags().contains(SymbolFlags::OPTIONAL)
            || property.check_flags().bits()
                & !(CheckFlags::INSTANTIATED | CheckFlags::READONLY).bits()
                != 0
            || property.name().is_reserved_member_name()
            || property.name().is_private_identifier()
            || property.name().is_late_bound()
            || store.get_merged_symbol(*symbol) != Some(*symbol)
        {
            return None;
        }
        let property_type =
            demand_instantiated_property_type(store, type_, *symbol, array_targets, &mut session)
                .ok()?;
        result.push(ResolvedObjectProperty {
            name,
            type_: property_type,
            readonly,
            optional: false,
        });
    }

    (validate_generic_interface_members(store, type_, array_targets)
        .ok()?
        .as_ref()
        == Some(&members))
    .then_some(result)
}

fn spread_union_property_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    types: &[TypeId],
) -> Option<TypeId> {
    let [first, rest @ ..] = types else {
        return None;
    };
    if rest.iter().all(|type_| type_ == first) {
        return Some(*first);
    }
    if let Some(global_types) = global_types {
        return store
            .expression_union_type_with_global_types(global_types, types, UnionReduction::Literal)
            .ok();
    }
    super::instantiate::canonical_anonymous_union(store, types).ok()
}

fn spread_union_empty_constituent(store: &CanonicalTypeMapperStore, type_: TypeId) -> bool {
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return false;
    };
    record
        .flags()
        .intersects(TypeFlags::NULLABLE | TypeFlags::NEVER)
        || type_ == bootstrap.false_type
        || type_ == bootstrap.regular_false_type
}

fn validate_union_spread_donor(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    type_: TypeId,
) -> SpreadDonorValidation {
    let valid_union = global_types.map_or_else(
        || store.validate_union_constituent(type_),
        |global_types| store.validate_union_constituent_with_global_types(global_types, type_),
    );
    if valid_union.is_err() {
        return SpreadDonorValidation::Malformed;
    }
    let Some(TypeData::Union(union)) = store.type_payload(type_).map(TypeRecord::data) else {
        return SpreadDonorValidation::Malformed;
    };
    let constituents = union.union.types.clone();
    let mut entries = Vec::<(ResolvedObjectProperty, Vec<TypeId>, usize)>::new();
    let mut positions = HashMap::<String, usize>::new();
    let mut object_constituents = 0usize;
    for constituent in constituents.iter().copied() {
        if spread_union_empty_constituent(store, constituent) {
            continue;
        }
        let properties = match validate_spread_donor(store, global_types, constituent) {
            SpreadDonorValidation::Valid(properties) => properties,
            SpreadDonorValidation::Unsupported => return SpreadDonorValidation::Unsupported,
            SpreadDonorValidation::Malformed => return SpreadDonorValidation::Malformed,
        };
        object_constituents += 1;
        for property in properties {
            if let Some(index) = positions.get(&property.name).copied() {
                let (existing, property_types, present) = &mut entries[index];
                if !property_types.contains(&property.type_) {
                    property_types.push(property.type_);
                }
                existing.readonly &= property.readonly;
                existing.optional |= property.optional;
                *present += 1;
            } else {
                positions.insert(property.name.clone(), entries.len());
                let type_ = property.type_;
                entries.push((property, vec![type_], 1));
            }
        }
    }
    if object_constituents == 0 {
        return SpreadDonorValidation::Unsupported;
    }
    let mut properties = Vec::with_capacity(entries.len());
    for (mut property, property_types, present) in entries {
        let Some(type_) = spread_union_property_type(store, global_types, &property_types) else {
            return SpreadDonorValidation::Malformed;
        };
        property.type_ = type_;
        property.optional |= present != constituents.len();
        properties.push(property);
    }
    SpreadDonorValidation::Valid(properties)
}

fn validate_spread_donor(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    type_: TypeId,
) -> SpreadDonorValidation {
    let Some(record) = store.type_payload(type_) else {
        return SpreadDonorValidation::Malformed;
    };
    let flags = record.flags();
    let interface = matches!(record.data(), TypeData::Interface(_));
    let symbol = record.symbol();
    if flags.intersects(TypeFlags::UNION) {
        return validate_union_spread_donor(store, global_types, type_);
    }
    if flags != TypeFlags::OBJECT {
        return SpreadDonorValidation::Unsupported;
    }
    match validate_resolved_declared_property_object(store, type_) {
        DeclaredPropertyObjectValidation::Valid(_) => {
            return projected_spread_donor_properties(store, type_).map_or(
                SpreadDonorValidation::Malformed,
                SpreadDonorValidation::Valid,
            );
        }
        DeclaredPropertyObjectValidation::Malformed => return SpreadDonorValidation::Malformed,
        DeclaredPropertyObjectValidation::NotDeclared => {}
    }
    if interface {
        return validated_indexed_or_method_interface_spread_donor(store, type_).map_or(
            SpreadDonorValidation::Malformed,
            SpreadDonorValidation::Valid,
        );
    }
    let derived = global_types.map_or_else(
        || store.validate_derived_object_literal_for_relation(type_),
        |global_types| store.validate_derived_object_literal_with_global_types(type_, global_types),
    );
    match derived {
        super::derived_types::DerivedObjectLiteralValidation::Valid { .. } => {
            return projected_spread_donor_properties(store, type_).map_or(
                SpreadDonorValidation::Malformed,
                SpreadDonorValidation::Valid,
            );
        }
        super::derived_types::DerivedObjectLiteralValidation::Invalid => {
            return SpreadDonorValidation::Malformed;
        }
        super::derived_types::DerivedObjectLiteralValidation::NotDerived => {}
    }
    if symbol.is_none() {
        return validated_synthetic_object_properties(store, type_).map_or(
            SpreadDonorValidation::Malformed,
            SpreadDonorValidation::Valid,
        );
    }
    if let Some(owner) = symbol.and_then(|symbol| store.symbol(symbol))
        && owner.flags() == SymbolFlags::OBJECT_LITERAL
    {
        let properties = if owner.exports().is_some() {
            validated_javascript_expando_spread_donor(store, type_)
        } else {
            validated_source_object_spread_donor(store, type_)
        };
        return properties.map_or(
            SpreadDonorValidation::Malformed,
            SpreadDonorValidation::Valid,
        );
    }
    if record
        .symbol()
        .and_then(|symbol| store.symbol(symbol))
        .is_some_and(|symbol| symbol.flags() == SymbolFlags::VALUE_MODULE)
    {
        return validated_module_namespace_spread_donor(store, type_).map_or(
            SpreadDonorValidation::Malformed,
            SpreadDonorValidation::Valid,
        );
    }
    if record.object_flags().intersects(ObjectFlags::REFERENCE)
        && record
            .symbol()
            .and_then(|symbol| store.symbol(symbol))
            .is_some_and(|symbol| symbol.flags().contains(SymbolFlags::INTERFACE))
    {
        return validated_generic_interface_spread_donor(store, global_types, type_).map_or(
            SpreadDonorValidation::Malformed,
            SpreadDonorValidation::Valid,
        );
    }
    SpreadDonorValidation::Unsupported
}

fn merge_spread_property(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    node: NodeRef,
    properties: &mut Vec<ResolvedObjectProperty>,
    positions: &mut HashMap<String, usize>,
    property: ResolvedObjectProperty,
) -> Result<(), PropertyObjectError> {
    if let Some(index) = positions.get(&property.name).copied() {
        if property.optional {
            let previous = &properties[index];
            let type_ =
                spread_union_property_type(store, global_types, &[previous.type_, property.type_])
                    .ok_or(PropertyObjectError::InvalidObjectLiteral(node))?;
            properties[index] = ResolvedObjectProperty {
                type_,
                optional: previous.optional,
                ..property
            };
        } else {
            properties[index] = property;
        }
    } else {
        positions.insert(property.name.clone(), properties.len());
        properties.push(property);
    }
    Ok(())
}

fn jsdoc_generic_arrow_spread_donor(
    store: &CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    type_: TypeId,
) -> bool {
    if !plan.properties.is_empty() || plan.spreads.len() != 1 {
        return false;
    }
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return false;
    };
    let generic = match store.type_payload(type_).map(TypeRecord::data) {
        Some(TypeData::TypeParameter(_)) => type_,
        Some(TypeData::Union(union)) if union.union.types.len() == 2 => {
            let Some(generic) = union
                .union
                .types
                .iter()
                .copied()
                .find(|candidate| *candidate != bootstrap.undefined_type)
            else {
                return false;
            };
            if !union.union.types.contains(&bootstrap.undefined_type)
                || !matches!(
                    store.type_payload(generic).map(TypeRecord::data),
                    Some(TypeData::TypeParameter(_))
                )
            {
                return false;
            }
            generic
        }
        _ => return false,
    };
    let Some(symbol) = cached_ordinary_type_parameter_owner(store, generic) else {
        return false;
    };
    let Some([declaration]) = store
        .symbol(symbol)
        .and_then(|symbol| symbol.declarations())
    else {
        return false;
    };
    let Some(SourceNodeParent::Parent(arrow)) = store.source_node_parent(*declaration) else {
        return false;
    };
    if store.source_node_kind(*declaration) != Some(SyntaxKind::TypeParameter)
        || store.source_node_kind(arrow) != Some(SyntaxKind::ArrowFunction)
    {
        return false;
    }
    let mut current = plan.node;
    let mut parenthesized = false;
    loop {
        let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(current) else {
            return false;
        };
        if parent == arrow {
            break;
        }
        if store.source_node_kind(parent) != Some(SyntaxKind::ParenthesizedExpression) {
            return false;
        }
        parenthesized = true;
        current = parent;
    }
    let Some(callable) = store.source_callable_type_for_declaration(arrow) else {
        return false;
    };
    let Some(signature) = store
        .source_callable_provenance(callable)
        .and_then(|provenance| store.signature(provenance.signature))
    else {
        return false;
    };
    parenthesized
        && signature.type_parameters().contains(&generic)
        && signature.parameters().iter().any(|parameter| {
            store
                .value_symbol_links(*parameter)
                .and_then(|links| links.resolved_type)
                == Some(type_)
        })
}

/// Publishes authenticated concrete or union spreads, with canonical `any` absorption.
pub(super) fn publish_object_literal_with_spreads(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    plan: &PropertyObjectPlan,
    property_types: &[TypeId],
    spread_types: &[TypeId],
) -> Result<TypeId, PropertyObjectError> {
    if plan.kind != PropertyObjectKind::ObjectLiteral
        || plan.spreads.is_empty()
        || plan.spreads.len() != spread_types.len()
        || plan.properties.len() != property_types.len()
        || plan
            .properties
            .iter()
            .zip(property_types)
            .any(|(property, type_)| {
                property.readonly != plan.const_context
                    || !valid_bound_object_literal_property(store, plan, property)
                    || !valid_object_literal_property_type(store, property, *type_)
            })
        || !valid_object_literal_owner(store, plan)
        || !unresolved_property_links(store, plan)
    {
        return Err(PropertyObjectError::InvalidObjectLiteral(plan.node));
    }
    let any = store
        .intrinsic_bootstrap()
        .ok_or(PropertyObjectError::InvalidObjectLiteral(plan.node))?
        .any_type;
    let mut donors = Vec::with_capacity(spread_types.len());
    let mut absorbs_any = false;
    for (spread, type_) in plan.spreads.iter().zip(spread_types) {
        if *type_ == any {
            donors.push(None);
            absorbs_any = true;
            continue;
        }
        if jsdoc_generic_arrow_spread_donor(store, plan, *type_) {
            donors.push(Some(Vec::new()));
            continue;
        }
        match validate_spread_donor(store, global_types, *type_) {
            SpreadDonorValidation::Valid(properties) => donors.push(Some(properties)),
            SpreadDonorValidation::Unsupported => {
                return Err(PropertyObjectError::UnsupportedMember {
                    node: spread.declaration,
                    kind: SyntaxKind::SpreadAssignment,
                });
            }
            SpreadDonorValidation::Malformed => {
                return Err(PropertyObjectError::InvalidObjectLiteral(plan.node));
            }
        }
    }
    if let Some(state) = object_literal_state(store, plan)? {
        if absorbs_any {
            return if state.type_id() == any {
                Ok(any)
            } else {
                Err(invalid_cache(plan, state.type_id()))
            };
        }
        if state.type_id() == any {
            return Err(invalid_cache(plan, any));
        }
    }

    if absorbs_any {
        if !store
            .try_reserve_type_node_links(usize::from(store.type_node_links(plan.node).is_none()))
        {
            return Err(PropertyObjectError::Capacity(plan.node));
        }
        let mut links = store
            .type_node_links(plan.node)
            .cloned()
            .unwrap_or_default();
        links.resolved_type = Some(any);
        assert!(store.set_type_node_links(plan.node, links));
        return Ok(any);
    }

    let mut merged = Vec::new();
    let mut positions = HashMap::new();
    let mut spread_index = 0;
    for (index, (property, type_)) in plan.properties.iter().zip(property_types).enumerate() {
        while plan
            .spreads
            .get(spread_index)
            .is_some_and(|spread| spread.property_index == index)
        {
            let donor = donors[spread_index]
                .as_ref()
                .expect("canonical any was handled before concrete spread publication");
            for property in donor {
                merge_spread_property(
                    store,
                    global_types,
                    plan.node,
                    &mut merged,
                    &mut positions,
                    ResolvedObjectProperty {
                        name: property.name.clone(),
                        type_: property.type_,
                        readonly: plan.const_context,
                        optional: property.optional,
                    },
                )?;
            }
            spread_index += 1;
        }
        merge_spread_property(
            store,
            global_types,
            plan.node,
            &mut merged,
            &mut positions,
            ResolvedObjectProperty {
                name: property.name.clone(),
                type_: *type_,
                readonly: property.readonly,
                optional: property.optional,
            },
        )?;
    }
    while let Some(spread) = plan.spreads.get(spread_index) {
        if spread.property_index != plan.properties.len() {
            return Err(PropertyObjectError::InvalidObjectLiteral(plan.node));
        }
        let donor = donors[spread_index]
            .as_ref()
            .expect("canonical any was handled before concrete spread publication");
        for property in donor {
            merge_spread_property(
                store,
                global_types,
                plan.node,
                &mut merged,
                &mut positions,
                ResolvedObjectProperty {
                    name: property.name.clone(),
                    type_: property.type_,
                    readonly: plan.const_context,
                    optional: property.optional,
                },
            )?;
        }
        spread_index += 1;
    }

    if let Some(state) = object_literal_state(store, plan)? {
        return if validated_synthetic_object_properties(store, state.type_id())
            .is_some_and(|actual| actual == merged)
        {
            Ok(state.type_id())
        } else {
            Err(invalid_cache(plan, state.type_id()))
        };
    }
    publish_synthetic_object_literal(store, plan, &merged)
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
        CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalGlobalTypes,
        IntrinsicBootstrapOptions, declared::get_declared_class_interface_or_type_parameter,
        global_types::initialize_global_library_types, links::TypeNodeLinks,
        production::GlobalMergeCompletion, type_nodes::CanonicalTypeQuery,
    };

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        bound: BoundFile,
        store: CanonicalTypeMapperStore,
        symbol: SemanticSymbolId,
    }

    struct GlobalArrayAugmentationFixture {
        library: ParseResult,
        source: ParseResult,
        library_bound: BoundFile,
        source_bound: BoundFile,
        store: CanonicalTypeMapperStore,
        global_types: CanonicalGlobalTypes,
        declaration: NodeRef,
        symbol: SemanticSymbolId,
    }

    fn global_array_augmentation_fixture(
        source_text: &str,
        file: u32,
    ) -> GlobalArrayAugmentationFixture {
        let library = parse_source_file(concat!(
            "interface IArguments {} ",
            "interface Array<T> {} declare var Array: any; ",
            "interface Object {} interface Function {} ",
            "interface String {} interface Number {} interface Boolean {} ",
            "interface RegExp {} interface ReadonlyArray<T> {} interface ThisType<T> {}",
        ));
        let source = parse_source_file(source_text);
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let library_file = FileId::new(file);
        let source_file = FileId::new(file + 1);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, is_default_library) in [
            (&library, library_file, true),
            (&source, source_file, false),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!("\"/array-augmentation-{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        is_default_library,
                        is_default_library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }

        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let library_bound = files.remove(&library_file).unwrap();
        let source_bound = files.remove(&source_file).unwrap();
        let declaration = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::InterfaceDeclaration).then_some(NodeRef::new(
                    source.arena.id(),
                    source_file,
                    node,
                ))
            })
            .expect("the source contains one array augmentation");
        let symbol = source_bound.symbol(declaration).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        for (parsed, file) in [(&library, library_file), (&source, source_file)] {
            assert!(
                store
                    .register_source_file(&parsed.arena, parsed.source_file, file)
                    .is_some()
            );
        }
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        let library_symbols = store
            .symbol_table(library_bound.locals(library_bound.source_file()).unwrap())
            .unwrap()
            .iter()
            .map(|(_, symbol)| symbol)
            .collect::<Vec<_>>();
        for symbol in library_symbols {
            store.merge_global_symbol(globals, symbol).unwrap();
        }
        store.merge_global_symbol(globals, symbol).unwrap();
        let global_types = {
            let host = DeclaredTypeHost::new_after_global_merge(
                [
                    (&library.arena, &library_bound),
                    (&source.arena, &source_bound),
                ],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            initialize_global_library_types(&mut store, &host, globals, false).unwrap()
        };

        GlobalArrayAugmentationFixture {
            library,
            source,
            library_bound,
            source_bound,
            store,
            global_types,
            declaration,
            symbol,
        }
    }

    fn fixture() -> Fixture {
        interface_fixture(
            "interface Box<T> { value: T; readonly label: string }",
            3_701,
        )
    }

    fn interface_fixture(source: &str, file: u32) -> Fixture {
        interface_fixture_with_module_state(source, file, CanonicalModuleState::Script)
    }

    fn interface_fixture_with_module_state(
        source: &str,
        file: u32,
        module_state: CanonicalModuleState,
    ) -> Fixture {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(file);
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
                    module_state,
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
        if module_state == CanonicalModuleState::Script {
            let globals = store.intrinsic_bootstrap().unwrap().globals;
            let global = store.get_parent_of_symbol(symbol).unwrap_or(symbol);
            store.merge_global_symbol(globals, global).unwrap();
        }
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

    fn object_initializer(fixture: &Fixture, expected: &str) -> NodeRef {
        let initializer = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &fixture.parsed.arena.get(variable.name)?.data
                else {
                    return None;
                };
                (name.text == expected)
                    .then_some(variable.initializer)
                    .flatten()
            })
            .unwrap_or_else(|| panic!("missing object initializer {expected}"));
        let mut node = NodeRef::new(fixture.parsed.arena.id(), fixture.file, initializer);
        loop {
            let record = fixture.parsed.arena.get(node.node).unwrap();
            node = match &record.data {
                NodeData::AsExpression(assertion) => {
                    NodeRef::new(node.arena, node.file, assertion.expression)
                }
                NodeData::ParenthesizedExpression(parenthesized) => {
                    NodeRef::new(node.arena, node.file, parenthesized.expression)
                }
                NodeData::ObjectLiteralExpression(_) => return node,
                _ => panic!("initializer {expected} does not contain an object literal"),
            };
        }
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
    fn global_array_property_augmentation_preserves_the_lazy_library_target() {
        let fixture = global_array_augmentation_fixture(
            "interface Array<T> { split: (parts: number) => T[][]; }",
            3_729,
        );
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&fixture.library.arena, &fixture.library_bound),
                (&fixture.source.arena, &fixture.source_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let plan = plan_global_array_property_augmentation(
            &fixture.store,
            &host,
            fixture.declaration,
            fixture.symbol,
        )
        .unwrap()
        .expect("the source property must augment the initialized Array target");

        assert_eq!(plan.target, fixture.global_types.array_type);
        assert_eq!(plan.property.name, "split");
        assert_eq!(
            fixture.store.source_node_kind(plan.property.type_node),
            Some(SyntaxKind::FunctionType),
        );
        assert!(
            fixture
                .store
                .value_symbol_links(plan.property.symbol)
                .is_none()
        );
        let TypeData::Interface(target) = fixture.store.type_payload(plan.target).unwrap().data()
        else {
            panic!("Array must retain its generic interface target")
        };
        assert!(!target.declared_members_resolved);
        assert_eq!(
            target.reference.object.structured,
            StructuredTypeData::default()
        );
        assert_eq!(
            plan_global_array_call_augmentation(
                &fixture.store,
                &host,
                fixture.declaration,
                fixture.symbol,
            ),
            Ok(None),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn global_array_call_augmentation_reuses_initialized_target_without_expanding_members() {
        let mut fixture =
            global_array_augmentation_fixture("interface Array<T> { (): any[]; }", 3_731);
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&fixture.library.arena, &fixture.library_bound),
                (&fixture.source.arena, &fixture.source_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        let plan = plan_global_array_call_augmentation(
            &fixture.store,
            &host,
            fixture.declaration,
            fixture.symbol,
        )
        .unwrap()
        .expect("a default-library Array augmentation must be authenticated");
        assert_eq!(plan.declaration, fixture.declaration);
        assert_eq!(
            plan.symbol,
            fixture.store.get_merged_symbol(fixture.symbol).unwrap()
        );
        assert_eq!(plan.target, fixture.global_types.array_type);
        assert_eq!(plan.any_array_type, fixture.global_types.any_array_type);
        assert_eq!(
            fixture.store.source_node_kind(plan.signature),
            Some(SyntaxKind::CallSignature),
        );
        assert_eq!(
            fixture.store.source_node_kind(plan.return_type),
            Some(SyntaxKind::ArrayType),
        );
        assert!(fixture.store.signature_links(plan.signature).is_none());
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
        let TypeData::Interface(target) = fixture.store.type_payload(plan.target).unwrap().data()
        else {
            panic!("Array must retain its initialized generic interface target")
        };
        assert!(!target.declared_members_resolved);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            CanonicalTypeQuery::new_with_global_types(
                &mut fixture.store,
                &host,
                &fixture.global_types,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_type_from_type_node(plan.return_type),
            Ok(plan.any_array_type),
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            plan_global_array_call_augmentation(
                &fixture.store,
                &host,
                fixture.declaration,
                fixture.symbol,
            ),
            Ok(Some(plan)),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn ordinary_source_array_interfaces_are_not_global_call_augmentations() {
        for (offset, source) in [
            "interface Array<T> {}",
            "interface Array<T> { value: T }",
            "interface Array<T> { (): any[] }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = interface_fixture(source, 3_755 + u32::try_from(offset).unwrap());
            let host = host(&fixture.parsed, &fixture.bound);
            let declaration = fixture
                .store
                .symbol(fixture.symbol)
                .and_then(ts_binder::semantic::Symbol::declarations)
                .and_then(|declarations| declarations.first())
                .copied()
                .unwrap();
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(
                plan_global_array_call_augmentation(
                    &fixture.store,
                    &host,
                    declaration,
                    fixture.symbol,
                ),
                Ok(None),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn global_array_call_augmentation_rejects_invalid_shapes_and_poisoned_caches() {
        for (offset, source) in [
            "interface Array<T> { (value: any): any[]; }",
            "interface Array<T> { (): number[]; }",
            "interface Array<T> { (): any[]; marker: any; }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = global_array_augmentation_fixture(
                source,
                3_740 + u32::try_from(offset).unwrap() * 2,
            );
            let host = DeclaredTypeHost::new_after_global_merge(
                [
                    (&fixture.library.arena, &fixture.library_bound),
                    (&fixture.source.arena, &fixture.source_bound),
                ],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert!(matches!(
                plan_global_array_call_augmentation(
                    &fixture.store,
                    &host,
                    fixture.declaration,
                    fixture.symbol,
                ),
                Err(PropertyObjectError::InvalidInterface { .. })
            ));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }

        let mut fixture =
            global_array_augmentation_fixture("interface Array<T> { (): any[]; }", 3_750);
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&fixture.library.arena, &fixture.library_bound),
                (&fixture.source.arena, &fixture.source_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_global_array_call_augmentation(
            &fixture.store,
            &host,
            fixture.declaration,
            fixture.symbol,
        )
        .unwrap()
        .unwrap();
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(fixture.store.set_type_node_links(
            plan.return_type,
            TypeNodeLinks {
                resolved_type: Some(string),
                ..TypeNodeLinks::default()
            },
        ));
        let poisoned = fixture.store.checker_link_allocated_lengths();
        assert_eq!(
            plan_global_array_call_augmentation(
                &fixture.store,
                &host,
                fixture.declaration,
                fixture.symbol,
            ),
            Err(PropertyObjectError::InvalidInterface {
                declaration: fixture.declaration,
                symbol: plan.symbol,
            }),
        );
        assert_eq!(fixture.store.checker_link_allocated_lengths(), poisoned);
        assert!(
            fixture
                .store
                .set_type_node_links(plan.return_type, TypeNodeLinks::default(),)
        );
        assert_eq!(
            plan_global_array_call_augmentation(
                &fixture.store,
                &host,
                fixture.declaration,
                fixture.symbol,
            ),
            Ok(Some(plan)),
        );
    }

    #[test]
    fn object_spreads_preserve_unbound_operands_and_direct_property_positions() {
        let (fixture, object) = object_fixture(concat!(
            "declare const source: any; ",
            "const value = { ...source, first: 1, ...source, last: 2 };",
        ));
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_object_literal(&fixture.store, &host, object).unwrap();

        assert_eq!(
            plan.properties
                .iter()
                .map(|property| property.name.as_str())
                .collect::<Vec<_>>(),
            ["first", "last"],
        );
        assert_eq!(
            plan.spreads
                .iter()
                .map(|spread| spread.property_index)
                .collect::<Vec<_>>(),
            [0, 1],
        );
        assert_eq!(
            plan.spread_expression_nodes().collect::<Vec<_>>(),
            plan.spreads
                .iter()
                .map(|spread| spread.expression)
                .collect::<Vec<_>>(),
        );
        for spread in &plan.spreads {
            assert_eq!(fixture.bound.symbol(spread.declaration), None);
            assert_eq!(
                fixture.store.source_node_parent(spread.expression),
                Some(SourceNodeParent::Parent(spread.declaration)),
            );
        }
    }

    #[test]
    fn object_spreads_absorb_canonical_any_without_allocating_member_symbols() {
        let (mut fixture, object) = object_fixture(concat!(
            "declare const source: any; ",
            "const value = { first: 1, ...source, last: 2 };",
        ));
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_object_literal(&fixture.store, &host, object).unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let any = bootstrap.any_type;
        let number = bootstrap.number_type;
        let before = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.symbol_store().symbol_table_len(),
        );

        assert_eq!(
            publish_object_literal(&mut fixture.store, &plan, &[number, number]),
            Err(PropertyObjectError::InvalidObjectLiteral(object)),
        );
        assert_eq!(
            publish_object_literal_with_spreads(
                &mut fixture.store,
                None,
                &plan,
                &[number, number],
                &[any],
            ),
            Ok(any),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.symbol_store().symbol_table_len(),
            ),
            before,
        );
        assert_eq!(
            object_literal_state(&fixture.store, &plan),
            Ok(Some(PropertyObjectState::Resolved(any))),
        );
        assert!(plan.properties.iter().all(|property| {
            fixture
                .store
                .value_symbol_links(property.symbol)
                .is_none_or(|links| links == &ValueSymbolLinks::default())
        }));
        let warm = fixture.store.checker_link_allocated_lengths();
        assert_eq!(
            publish_object_literal_with_spreads(
                &mut fixture.store,
                None,
                &plan,
                &[number, number],
                &[any],
            ),
            Ok(any),
        );
        assert_eq!(fixture.store.checker_link_allocated_lengths(), warm);
    }

    #[test]
    fn concrete_object_spreads_merge_in_source_order_and_replay_exactly() {
        let (mut fixture, _) = object_fixture(concat!(
            "const first = { shared: 'left', first: 1 }; ",
            "const second = { shared: true, second: 2 }; ",
            "const value = { start: 0, ...first, shared: 3, ...second, last: 4 } as const;",
        ));
        let host = host(&fixture.parsed, &fixture.bound);
        let first = object_initializer(&fixture, "first");
        let second = object_initializer(&fixture, "second");
        let receiver = object_initializer(&fixture, "value");
        let first_plan = plan_object_literal(&fixture.store, &host, first).unwrap();
        let second_plan = plan_object_literal(&fixture.store, &host, second).unwrap();
        let receiver_plan = plan_object_literal(&fixture.store, &host, receiver).unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let boolean = bootstrap.boolean_type;
        let zero = fixture
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(0.0))
            .unwrap();
        let three = fixture
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(3.0))
            .unwrap();
        let four = fixture
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(4.0))
            .unwrap();
        let nine = fixture
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(9.0))
            .unwrap();
        let first_type =
            publish_object_literal(&mut fixture.store, &first_plan, &[string, number]).unwrap();
        let second_type =
            publish_object_literal(&mut fixture.store, &second_plan, &[boolean, number]).unwrap();

        let result = publish_object_literal_with_spreads(
            &mut fixture.store,
            None,
            &receiver_plan,
            &[zero, three, four],
            &[first_type, second_type],
        )
        .unwrap();
        assert_eq!(
            validated_synthetic_object_properties(&fixture.store, result),
            Some(vec![
                ResolvedObjectProperty {
                    name: "start".to_owned(),
                    type_: zero,
                    readonly: true,
                    optional: false,
                },
                ResolvedObjectProperty {
                    name: "shared".to_owned(),
                    type_: boolean,
                    readonly: true,
                    optional: false,
                },
                ResolvedObjectProperty {
                    name: "first".to_owned(),
                    type_: number,
                    readonly: true,
                    optional: false,
                },
                ResolvedObjectProperty {
                    name: "second".to_owned(),
                    type_: number,
                    readonly: true,
                    optional: false,
                },
                ResolvedObjectProperty {
                    name: "last".to_owned(),
                    type_: four,
                    readonly: true,
                    optional: false,
                },
            ]),
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            publish_object_literal_with_spreads(
                &mut fixture.store,
                None,
                &receiver_plan,
                &[zero, three, four],
                &[first_type, second_type],
            ),
            Ok(result),
        );
        assert_eq!(
            publish_object_literal_with_spreads(
                &mut fixture.store,
                None,
                &receiver_plan,
                &[zero, three, nine],
                &[first_type, second_type],
            ),
            Err(PropertyObjectError::InvalidCachedTypeLiteral {
                node: receiver,
                type_: result,
            }),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep optional union publication, replay, and cache poison together.
    fn union_spread_donors_preserve_optional_members_and_overwrite_order() {
        let (mut fixture, _) = object_fixture(concat!(
            "const first = { shared: 1, left: 'left' }; ",
            "const second = { shared: 'right', right: true }; ",
            "const result = { ...first } as const;",
        ));
        let host = host(&fixture.parsed, &fixture.bound);
        let first = object_initializer(&fixture, "first");
        let second = object_initializer(&fixture, "second");
        let receiver = object_initializer(&fixture, "result");
        let first_plan = plan_object_literal(&fixture.store, &host, first).unwrap();
        let second_plan = plan_object_literal(&fixture.store, &host, second).unwrap();
        let receiver_plan = plan_object_literal(&fixture.store, &host, receiver).unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let boolean = bootstrap.boolean_type;
        let first_type =
            publish_object_literal(&mut fixture.store, &first_plan, &[number, string]).unwrap();
        let second_type =
            publish_object_literal(&mut fixture.store, &second_plan, &[string, boolean]).unwrap();
        let donor = fixture
            .store
            .expression_union_type(&[first_type, second_type], UnionReduction::Literal)
            .unwrap();

        let result = publish_object_literal_with_spreads(
            &mut fixture.store,
            None,
            &receiver_plan,
            &[],
            &[donor],
        )
        .unwrap();
        let shared = fixture
            .store
            .expression_union_type(&[number, string], UnionReduction::Literal)
            .unwrap();
        assert_eq!(
            validated_synthetic_object_properties(&fixture.store, result),
            Some(vec![
                ResolvedObjectProperty {
                    name: "shared".to_owned(),
                    type_: shared,
                    readonly: true,
                    optional: false,
                },
                ResolvedObjectProperty {
                    name: "left".to_owned(),
                    type_: string,
                    readonly: true,
                    optional: true,
                },
                ResolvedObjectProperty {
                    name: "right".to_owned(),
                    type_: boolean,
                    readonly: true,
                    optional: true,
                },
            ]),
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            publish_object_literal_with_spreads(
                &mut fixture.store,
                None,
                &receiver_plan,
                &[],
                &[donor],
            ),
            Ok(result),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );

        let optional = fixture
            .store
            .type_payload(result)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.members)
            .and_then(|members| fixture.store.symbol_table(members))
            .and_then(|members| members.get_source("left"))
            .unwrap();
        assert!(fixture.store.set_symbol_flags(
            optional,
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
            CheckFlags::READONLY,
        ));
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            publish_object_literal_with_spreads(
                &mut fixture.store,
                None,
                &receiver_plan,
                &[],
                &[donor],
            ),
            Err(PropertyObjectError::InvalidCachedTypeLiteral {
                node: receiver,
                type_: result,
            }),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            poisoned,
        );
        assert!(fixture.store.set_symbol_flags(
            optional,
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT | SymbolFlags::OPTIONAL,
            CheckFlags::READONLY,
        ));
        assert_eq!(
            publish_object_literal_with_spreads(
                &mut fixture.store,
                None,
                &receiver_plan,
                &[],
                &[donor],
            ),
            Ok(result),
        );
    }

    #[test]
    fn optional_spread_overwrites_keep_prior_required_values() {
        let (mut fixture, _) = object_fixture(concat!(
            "const first = { value: 1 }; ",
            "const second = { value: 'ready' }; ",
            "const result = { ...first, ...second } as const;",
        ));
        let host = host(&fixture.parsed, &fixture.bound);
        let first = object_initializer(&fixture, "first");
        let second = object_initializer(&fixture, "second");
        let receiver = object_initializer(&fixture, "result");
        let first_plan = plan_object_literal(&fixture.store, &host, first).unwrap();
        let second_plan = plan_object_literal(&fixture.store, &host, second).unwrap();
        let receiver_plan = plan_object_literal(&fixture.store, &host, receiver).unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let false_type = bootstrap.false_type;
        let first_type =
            publish_object_literal(&mut fixture.store, &first_plan, &[number]).unwrap();
        let second_type =
            publish_object_literal(&mut fixture.store, &second_plan, &[string]).unwrap();
        let optional = fixture
            .store
            .expression_union_type(&[false_type, second_type], UnionReduction::Literal)
            .unwrap();

        let result = publish_object_literal_with_spreads(
            &mut fixture.store,
            None,
            &receiver_plan,
            &[],
            &[first_type, optional],
        )
        .unwrap();
        let combined = fixture
            .store
            .expression_union_type(&[number, string], UnionReduction::Literal)
            .unwrap();
        assert_eq!(
            validated_synthetic_object_properties(&fixture.store, result),
            Some(vec![ResolvedObjectProperty {
                name: "value".to_owned(),
                type_: combined,
                readonly: true,
                optional: false,
            }]),
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // The interface proof includes method, index, and poisoned links.
    fn interface_spreads_preserve_methods_static_fields_and_indexed_members() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Shape { [key: string]: any; value: number; run(): number; } ",
                "declare const input: Shape; ",
                "const copied = { ...input, ['indexed']: 1 };",
            ),
            3_899,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let receiver = object_initializer(&fixture, "copied");
        let plan = plan_object_literal(&fixture.store, &host, receiver).unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let donor = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let method = fixture
            .store
            .symbol(fixture.symbol)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| fixture.store.symbol_table(members))
            .and_then(|members| members.get_source("run"))
            .unwrap();
        let callable = fixture
            .store
            .value_symbol_links(method)
            .and_then(|links| links.resolved_type)
            .unwrap();

        let result = publish_object_literal_with_spreads(
            &mut fixture.store,
            None,
            &plan,
            &[number],
            &[donor],
        )
        .unwrap();
        assert_eq!(
            validated_synthetic_object_properties(&fixture.store, result),
            Some(vec![
                ResolvedObjectProperty {
                    name: "value".to_owned(),
                    type_: number,
                    readonly: false,
                    optional: false,
                },
                ResolvedObjectProperty {
                    name: "run".to_owned(),
                    type_: callable,
                    readonly: false,
                    optional: false,
                },
                ResolvedObjectProperty {
                    name: "indexed".to_owned(),
                    type_: number,
                    readonly: false,
                    optional: false,
                },
            ]),
        );
        assert!(diagnostics.is_empty());

        let expected = fixture.store.value_symbol_links(method).unwrap().clone();
        let mut poisoned = expected.clone();
        poisoned.write_type = Some(number);
        assert!(fixture.store.set_value_symbol_links(method, poisoned));
        let before = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            publish_object_literal_with_spreads(
                &mut fixture.store,
                None,
                &plan,
                &[number],
                &[donor],
            ),
            Err(PropertyObjectError::InvalidObjectLiteral(receiver)),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
        assert!(fixture.store.set_value_symbol_links(method, expected));
        assert_eq!(
            publish_object_literal_with_spreads(
                &mut fixture.store,
                None,
                &plan,
                &[number],
                &[donor],
            ),
            Ok(result),
        );
    }

    #[test]
    fn concrete_donors_and_any_still_absorb_without_allocating_receiver_members() {
        let (mut fixture, _) = object_fixture(concat!(
            "declare const unknown: any; ",
            "const donor = { value: 1 }; ",
            "const result = { ...donor, ...unknown };",
        ));
        let host = host(&fixture.parsed, &fixture.bound);
        let donor = object_initializer(&fixture, "donor");
        let receiver = object_initializer(&fixture, "result");
        let donor_plan = plan_object_literal(&fixture.store, &host, donor).unwrap();
        let receiver_plan = plan_object_literal(&fixture.store, &host, receiver).unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let any = bootstrap.any_type;
        let number = bootstrap.number_type;
        let donor_type =
            publish_object_literal(&mut fixture.store, &donor_plan, &[number]).unwrap();
        let before = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.symbol_store().symbol_table_len(),
        );

        assert_eq!(
            publish_object_literal_with_spreads(
                &mut fixture.store,
                None,
                &receiver_plan,
                &[],
                &[donor_type, any],
            ),
            Ok(any),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.symbol_store().symbol_table_len(),
            ),
            before,
        );
    }

    #[test]
    fn malformed_concrete_spread_donors_fail_before_receiver_publication() {
        let (mut fixture, _) = object_fixture(concat!(
            "const donor = { value: 1 }; ",
            "const result = { ...donor };",
        ));
        let host = host(&fixture.parsed, &fixture.bound);
        let donor = object_initializer(&fixture, "donor");
        let receiver = object_initializer(&fixture, "result");
        let donor_plan = plan_object_literal(&fixture.store, &host, donor).unwrap();
        let receiver_plan = plan_object_literal(&fixture.store, &host, receiver).unwrap();
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let donor_type =
            publish_object_literal(&mut fixture.store, &donor_plan, &[number]).unwrap();
        let property = fixture
            .store
            .type_payload(donor_type)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.properties.as_deref())
            .and_then(|properties| properties.first())
            .copied()
            .unwrap();
        assert!(fixture.store.set_symbol_flags(
            property,
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
            CheckFlags::READONLY,
        ));
        let before = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            publish_object_literal_with_spreads(
                &mut fixture.store,
                None,
                &receiver_plan,
                &[],
                &[donor_type],
            ),
            Err(PropertyObjectError::InvalidObjectLiteral(receiver)),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
        assert!(fixture.store.type_node_links(receiver).is_none());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One fixture verifies poisoned donor and receiver caches.
    fn synthetic_spreads_reject_poisoned_donor_and_receiver_caches() {
        let (mut fixture, _) = object_fixture(concat!(
            "const donor = { nested: { value: 1 } } as const; ",
            "const result = { ...donor };",
        ));
        let host = host(&fixture.parsed, &fixture.bound);
        let donor = object_initializer(&fixture, "donor");
        let receiver = object_initializer(&fixture, "result");
        let donor_plan = plan_object_literal(&fixture.store, &host, donor).unwrap();
        let nested = donor_plan.properties[0].type_node;
        let nested_plan = plan_object_literal(&fixture.store, &host, nested).unwrap();
        let receiver_plan = plan_object_literal(&fixture.store, &host, receiver).unwrap();
        let one = fixture
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(1.0))
            .unwrap();
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let nested_type = publish_object_literal(&mut fixture.store, &nested_plan, &[one]).unwrap();
        let donor_type =
            publish_object_literal(&mut fixture.store, &donor_plan, &[nested_type]).unwrap();
        let donor_property = fixture
            .store
            .type_payload(donor_type)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.properties.as_deref())
            .and_then(|properties| properties.first())
            .copied()
            .unwrap();
        let donor_links = fixture
            .store
            .value_symbol_links(donor_property)
            .unwrap()
            .clone();
        let mut poisoned_donor = donor_links.clone();
        poisoned_donor.write_type = Some(number);
        assert!(
            fixture
                .store
                .set_value_symbol_links(donor_property, poisoned_donor)
        );
        let state = |store: &CanonicalTypeMapperStore| {
            (
                store.type_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
            )
        };
        let poisoned = state(&fixture.store);
        assert_eq!(
            publish_object_literal_with_spreads(
                &mut fixture.store,
                None,
                &receiver_plan,
                &[],
                &[donor_type],
            ),
            Err(PropertyObjectError::InvalidObjectLiteral(receiver)),
        );
        assert_eq!(state(&fixture.store), poisoned);
        assert!(fixture.store.type_node_links(receiver).is_none());
        assert!(
            fixture
                .store
                .set_value_symbol_links(donor_property, donor_links)
        );

        let receiver_type = publish_object_literal_with_spreads(
            &mut fixture.store,
            None,
            &receiver_plan,
            &[],
            &[donor_type],
        )
        .unwrap();
        let receiver_property = fixture
            .store
            .type_payload(receiver_type)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.properties.as_deref())
            .and_then(|properties| properties.first())
            .copied()
            .unwrap();
        let receiver_links = fixture
            .store
            .value_symbol_links(receiver_property)
            .unwrap()
            .clone();
        let mut poisoned_receiver = receiver_links.clone();
        poisoned_receiver.target = Some(donor_plan.properties[0].symbol);
        assert!(
            fixture
                .store
                .set_value_symbol_links(receiver_property, poisoned_receiver)
        );
        let poisoned = state(&fixture.store);
        assert_eq!(
            publish_object_literal_with_spreads(
                &mut fixture.store,
                None,
                &receiver_plan,
                &[],
                &[donor_type],
            ),
            Err(PropertyObjectError::InvalidCachedTypeLiteral {
                node: receiver,
                type_: receiver_type,
            }),
        );
        assert_eq!(state(&fixture.store), poisoned);
        assert!(
            fixture
                .store
                .set_value_symbol_links(receiver_property, receiver_links)
        );

        let warm = state(&fixture.store);
        assert_eq!(
            publish_object_literal_with_spreads(
                &mut fixture.store,
                None,
                &receiver_plan,
                &[],
                &[donor_type],
            ),
            Ok(receiver_type),
        );
        assert_eq!(state(&fixture.store), warm);
    }

    #[test]
    fn unsupported_spread_donors_fail_before_publishing_partial_caches() {
        let (mut fixture, object) = object_fixture(concat!(
            "declare const source: any; ",
            "const value = { ...source };",
        ));
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_object_literal(&fixture.store, &host, object).unwrap();
        let unknown = fixture.store.intrinsic_bootstrap().unwrap().unknown_type;
        let before = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            publish_object_literal_with_spreads(&mut fixture.store, None, &plan, &[], &[unknown]),
            Err(PropertyObjectError::UnsupportedMember {
                node: plan.spreads[0].declaration,
                kind: SyntaxKind::SpreadAssignment,
            }),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
        assert!(fixture.store.type_node_links(object).is_none());
    }

    #[test]
    fn shorthand_assignment_defaults_preserve_binder_owned_pattern_symbols() {
        let (fixture, object) = object_fixture(concat!(
            "function assign(source: any) { let value; ",
            "({ value = (left: any, right: any) => left + right } = source); }",
        ));
        let host = host(&fixture.parsed, &fixture.bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let planned = plan_object_assignment_shorthand(&fixture.store, &host, object)
            .unwrap()
            .unwrap();

        assert_eq!(planned.owner, fixture.symbol);
        assert_eq!(
            fixture.bound.symbol(planned.declaration),
            Some(planned.symbol)
        );
        assert_eq!(
            fixture.store.source_node_kind(planned.declaration),
            Some(SyntaxKind::ShorthandPropertyAssignment),
        );
        assert_eq!(
            fixture.store.source_node_kind(planned.initializer),
            Some(SyntaxKind::ArrowFunction),
        );
        assert!(fixture.store.value_symbol_links(planned.symbol).is_none());
        assert!(fixture.store.type_node_links(object).is_none());
        assert_eq!(
            plan_object_assignment_shorthand(&fixture.store, &host, object),
            Ok(Some(planned)),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
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
    fn nested_const_objects_inherit_readonly_context_and_replay_synthetic_members() {
        let (mut fixture, _) =
            object_fixture("const value = ({ item: ({ nested: 1 }) }) as const;");
        let host = host(&fixture.parsed, &fixture.bound);
        let outer = object_initializer(&fixture, "value");
        let outer_plan = plan_object_literal(&fixture.store, &host, outer).unwrap();
        let parenthesized = outer_plan.properties[0].type_node;
        let NodeData::ParenthesizedExpression(parenthesized) =
            &fixture.parsed.arena.get(parenthesized.node).unwrap().data
        else {
            panic!("the nested object must retain its parenthesized initializer")
        };
        let inner = NodeRef::new(outer.arena, outer.file, parenthesized.expression);
        let inner_plan = plan_object_literal(&fixture.store, &host, inner).unwrap();
        assert!(outer_plan.const_context);
        assert!(inner_plan.const_context);
        assert!(
            outer_plan
                .properties
                .iter()
                .all(|property| property.readonly)
        );
        assert!(
            inner_plan
                .properties
                .iter()
                .all(|property| property.readonly)
        );
        let one = fixture
            .store
            .regular_number_literal_type(ts_jsnum::Number::new(1.0))
            .unwrap();

        let inner_type = publish_object_literal(&mut fixture.store, &inner_plan, &[one]).unwrap();
        let outer_type =
            publish_object_literal(&mut fixture.store, &outer_plan, &[inner_type]).unwrap();
        assert_eq!(
            validated_synthetic_object_properties(&fixture.store, inner_type),
            Some(vec![ResolvedObjectProperty {
                name: "nested".to_owned(),
                type_: one,
                readonly: true,
                optional: false,
            }]),
        );
        assert_eq!(
            validated_synthetic_object_properties(&fixture.store, outer_type),
            Some(vec![ResolvedObjectProperty {
                name: "item".to_owned(),
                type_: inner_type,
                readonly: true,
                optional: false,
            }]),
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            publish_object_literal(&mut fixture.store, &inner_plan, &[one]),
            Ok(inner_type),
        );
        assert_eq!(
            publish_object_literal(&mut fixture.store, &outer_plan, &[inner_type]),
            Ok(outer_type),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn const_object_literals_publish_readonly_keyword_properties_and_regular_literals() {
        let (mut fixture, object) = object_fixture(concat!(
            "const value = ({ ",
            "new: 'new', delete: 'delete', break: 'break', continue: 'continue', ",
            "count: 1, enabled: true, total: 2n ",
            "}) as const;",
        ));
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_object_literal(&fixture.store, &host, object).unwrap();
        assert_eq!(
            plan.properties
                .iter()
                .map(|property| property.name.as_str())
                .collect::<Vec<_>>(),
            [
                "new", "delete", "break", "continue", "count", "enabled", "total"
            ],
        );
        assert!(plan.properties.iter().all(|property| property.readonly));
        assert!(plan.properties.iter().all(|property| {
            fixture.store.symbol(property.symbol).unwrap().check_flags() == CheckFlags::NONE
        }));

        let mut property_types = ["new", "delete", "break", "continue"]
            .into_iter()
            .map(|value| {
                fixture
                    .store
                    .regular_string_literal_type(value.into())
                    .unwrap()
            })
            .collect::<Vec<_>>();
        property_types.push(
            fixture
                .store
                .regular_number_literal_type(ts_jsnum::Number::new(1.0))
                .unwrap(),
        );
        property_types.push(
            fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .regular_true_type,
        );
        property_types.push(
            fixture
                .store
                .regular_bigint_literal_type(ts_jsnum::PseudoBigInt::parse_valid("2n"))
                .unwrap(),
        );

        let type_ = publish_object_literal(&mut fixture.store, &plan, &property_types).unwrap();
        let TypeData::Object(record) = fixture.store.type_payload(type_).unwrap().data() else {
            panic!("a const assertion must preserve its object-literal type")
        };
        let properties = record.structured.properties.as_deref().unwrap();
        assert_eq!(properties.len(), plan.properties.len());
        for ((symbol, planned), expected) in
            properties.iter().zip(&plan.properties).zip(&property_types)
        {
            let property = fixture.store.symbol(*symbol).unwrap();
            assert_eq!(
                property.flags(),
                SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
            );
            assert_eq!(property.check_flags(), CheckFlags::READONLY);
            assert_eq!(property.name().as_utf8(), Some(planned.name.as_str()));
            assert_eq!(property.declarations(), Some(&[planned.declaration][..]));
            assert_eq!(
                fixture.store.value_symbol_links(*symbol),
                Some(&ValueSymbolLinks {
                    resolved_type: Some(*expected),
                    target: Some(planned.symbol),
                    ..ValueSymbolLinks::default()
                }),
            );
        }

        let warm = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            publish_object_literal(&mut fixture.store, &plan, &property_types),
            Ok(type_),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn const_object_publication_rejects_invalid_literals_and_poisoned_symbols_atomically() {
        let (mut fixture, object) = object_fixture("const value = { new: 'new' } as const;");
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_object_literal(&fixture.store, &host, object).unwrap();
        let regular = fixture
            .store
            .regular_string_literal_type("new".into())
            .unwrap();
        let fresh = fixture.store.fresh_type_of_literal_type(regular).unwrap();
        let state = |store: &CanonicalTypeMapperStore| {
            (
                store.type_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
            )
        };
        let before = state(&fixture.store);
        assert_eq!(
            publish_object_literal(&mut fixture.store, &plan, &[fresh]),
            Err(PropertyObjectError::InvalidObjectLiteral(object)),
        );
        assert_eq!(state(&fixture.store), before);

        assert!(fixture.store.set_symbol_flags(
            plan.properties[0].symbol,
            SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL,
            CheckFlags::NONE,
        ));
        let poisoned = state(&fixture.store);
        assert_eq!(
            publish_object_literal(&mut fixture.store, &plan, &[regular]),
            Err(PropertyObjectError::InvalidObjectLiteral(object)),
        );
        assert_eq!(state(&fixture.store), poisoned);
        assert!(fixture.store.set_symbol_flags(
            plan.properties[0].symbol,
            SymbolFlags::PROPERTY,
            CheckFlags::NONE,
        ));

        let type_ = publish_object_literal(&mut fixture.store, &plan, &[regular]).unwrap();
        let property = fixture
            .store
            .type_payload(type_)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.properties.as_ref())
            .and_then(|properties| properties.first())
            .copied()
            .unwrap();
        assert!(fixture.store.set_symbol_flags(
            property,
            SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
            CheckFlags::NONE,
        ));
        let poisoned = state(&fixture.store);
        assert_eq!(
            publish_object_literal(&mut fixture.store, &plan, &[regular]),
            Err(PropertyObjectError::InvalidCachedTypeLiteral {
                node: object,
                type_,
            }),
        );
        assert_eq!(state(&fixture.store), poisoned);
    }

    #[test]
    fn type_literals_plan_literal_property_names_and_preserve_bound_symbols() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Owner {} ",
                "type Shape = { ",
                "'quoted': string; ",
                "7: number; ",
                "['computed']: boolean; ",
                "[8]: bigint; ",
                "[`template`]: symbol; ",
                "['i\\u0307spanyol']: string ",
                "};",
            ),
            3_709,
        );
        let literal = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeLiteral).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .expect("the fixture contains a type literal");
        let alias = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeAliasDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .and_then(|declaration| fixture.bound.symbol(declaration))
            .expect("the fixture contains a bound type alias");
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_type_literal(&fixture.store, &host, literal, Some(alias)).unwrap();

        assert_eq!(
            plan.properties
                .iter()
                .map(|property| property.name.as_str())
                .collect::<Vec<_>>(),
            [
                "quoted",
                "7",
                "computed",
                "8",
                "template",
                "i\u{307}spanyol"
            ],
        );
        for property in &plan.properties {
            assert_eq!(
                fixture.bound.symbol(property.declaration),
                Some(property.symbol)
            );
        }

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(alias)
        .unwrap();
        let TypeData::Object(object) = fixture.store.type_payload(type_).unwrap().data() else {
            panic!("the alias must publish one anonymous type literal")
        };
        assert_eq!(
            object.structured.properties.as_deref(),
            Some(plan.property_symbols().as_slice()),
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(alias),
            Ok(type_),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_interface_call_overloads_publish_authenticated_signature_parameters() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Callable { ",
                "<Value extends string = string>(value: Value): Value; ",
                "<Other>(value: Other): Other; ",
                "}",
            ),
            3_910,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let [first, second] = plan.call_signatures.as_slice() else {
            panic!("the callable interface must preserve both generic declaration overloads")
        };
        assert_eq!(first.symbol, second.symbol);
        assert_eq!(first.type_parameters.len(), 1);
        assert_eq!(second.type_parameters.len(), 1);
        assert!(first.type_parameters[0].constraint.is_some());
        assert!(first.type_parameters[0].default_type.is_some());

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();

        let TypeData::Interface(interface) = fixture.store.type_payload(type_).unwrap().data()
        else {
            panic!("generic call overloads must retain their interface owner")
        };
        let signatures = interface.declared_call_signatures.as_deref().unwrap();
        assert_eq!(signatures.len(), 2);
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        for (signature, planned) in signatures.iter().zip(&plan.call_signatures) {
            let record = fixture.store.signature(*signature).unwrap();
            let [parameter] = record.type_parameters() else {
                panic!("each source overload must retain one distinct binder-owned type parameter")
            };
            assert_eq!(
                cached_ordinary_type_parameter_owner(&fixture.store, *parameter),
                Some(planned.type_parameters[0].symbol),
            );
            assert_eq!(
                record.parameters(),
                [planned.parameters[0].symbol].as_slice()
            );
            assert_eq!(record.resolved_return_type(), Some(*parameter));
            assert_eq!(
                fixture.store.callable_signature_parameter_types(*signature),
                Some([*parameter].as_slice()),
            );
        }
        let TypeData::TypeParameter(defaulted) = fixture
            .store
            .type_payload(
                fixture
                    .store
                    .signature(signatures[0])
                    .unwrap()
                    .type_parameters()[0],
            )
            .unwrap()
            .data()
        else {
            panic!("the first overload must retain its constrained default")
        };
        assert_eq!(defaulted.constraint, Some(string));
        assert_eq!(defaulted.resolved_default_type, Some(string));
        assert!(matches!(
            validate_stored_declared_call_set(&fixture.store, type_),
            StoredDeclaredCallSetValidation::Valid(_)
        ));

        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(fixture.symbol),
            Ok(type_),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_construct_signatures_publish_original_type_parameter_identity() {
        let mut fixture = interface_fixture(
            "interface Constructor { new<Value>(value: Value): Value; }",
            3_911,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let [planned] = plan.call_signatures.as_slice() else {
            panic!("the constructor interface must retain one generic declaration")
        };
        assert!(planned.is_construct());
        assert_eq!(planned.type_parameters.len(), 1);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();

        let TypeData::Interface(interface) = fixture.store.type_payload(type_).unwrap().data()
        else {
            panic!("the constructor must retain its interface owner")
        };
        let [signature] = interface.declared_construct_signatures.as_deref().unwrap() else {
            panic!("the constructor owner must publish exactly one signature")
        };
        let record = fixture.store.signature(*signature).unwrap();
        let [parameter] = record.type_parameters() else {
            panic!("the construct signature must retain its source type parameter")
        };
        assert_eq!(
            cached_ordinary_type_parameter_owner(&fixture.store, *parameter),
            Some(planned.type_parameters[0].symbol),
        );
        assert_eq!(record.resolved_return_type(), Some(*parameter));
        assert!(matches!(
            validate_stored_declared_call_set(&fixture.store, type_),
            StoredDeclaredCallSetValidation::Valid(_)
        ));
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_type_literal_call_signatures_preserve_union_identity_and_replay_warm() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Owner {} ",
                "type Callback = { <Value>(value: Value | string): Value | string };",
            ),
            3_913,
        );
        let literal = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeLiteral).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let alias = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeAliasDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .and_then(|declaration| fixture.bound.symbol(declaration))
            .unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_type_literal(&fixture.store, &host, literal, Some(alias)).unwrap();
        let [planned] = plan.call_signatures.as_slice() else {
            panic!("the callback literal must retain one generic call signature")
        };
        assert_eq!(planned.type_parameters.len(), 1);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(alias)
        .unwrap();
        let TypeData::Object(object) = fixture.store.type_payload(type_).unwrap().data() else {
            panic!("the callback alias must retain its anonymous type literal")
        };
        assert_eq!(object.structured.call_signature_count, 1);
        let [signature] = object.structured.signatures.as_deref().unwrap() else {
            panic!("the callback literal must publish exactly one source signature")
        };
        let signature = *signature;
        let record = fixture.store.signature(signature).unwrap();
        let [parameter] = record.type_parameters() else {
            panic!("the callback signature must retain its binder-owned type parameter")
        };
        let parameter = *parameter;
        let union = record.resolved_return_type().unwrap();
        let TypeData::Union(data) = fixture.store.type_payload(union).unwrap().data() else {
            panic!("the callback signature must retain its generic union")
        };
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(data.union.types.len(), 2);
        assert!(data.union.types.contains(&parameter));
        assert!(data.union.types.contains(&string));
        assert_eq!(
            cached_ordinary_type_parameter_owner(&fixture.store, parameter),
            Some(planned.type_parameters[0].symbol),
        );
        assert_eq!(
            record.parameters(),
            [planned.parameters[0].symbol].as_slice()
        );
        assert_eq!(
            fixture.store.callable_signature_parameter_types(signature),
            Some([union].as_slice()),
        );
        assert_eq!(
            fixture
                .store
                .type_node_links(planned.parameters[0].type_node)
                .and_then(|links| links.resolved_type),
            Some(union),
        );
        assert!(matches!(
            validate_stored_declared_call_set(&fixture.store, type_),
            StoredDeclaredCallSetValidation::Valid(_)
        ));
        assert!(matches!(
            crate::semantic::callable_sets::validate_stored_callable_set(&fixture.store, type_),
            crate::semantic::callable_sets::StoredCallableSetValidation::Valid { .. }
        ));

        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .union_cache_len(),
        );
        assert_eq!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(alias),
            Ok(type_),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture
                    .store
                    .intrinsic_bootstrap()
                    .unwrap()
                    .union_cache_len(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn declared_call_signature_rest_tuples_preserve_source_arity_and_callable_identity() {
        let mut fixture = interface_fixture(
            "interface Callable { (value: string, ...rest: [extra: number]): void; }",
            3_912,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let [planned] = plan.call_signatures.as_slice() else {
            panic!("the callable interface must retain its rest declaration")
        };
        assert_eq!(planned.flags, SignatureFlags::HAS_REST_PARAMETER);
        assert_eq!(planned.min_argument_count(), 1);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();

        let TypeData::Interface(interface) = fixture.store.type_payload(type_).unwrap().data()
        else {
            panic!("the rest callable must retain its interface owner")
        };
        let [signature] = interface.declared_call_signatures.as_deref().unwrap() else {
            panic!("the rest callable must publish exactly one signature")
        };
        let record = fixture.store.signature(*signature).unwrap();
        assert!(record.flags().contains(SignatureFlags::HAS_REST_PARAMETER));
        assert_eq!(record.min_argument_count(), 1);
        assert!(matches!(
            validate_stored_declared_call_set(&fixture.store, type_),
            StoredDeclaredCallSetValidation::Valid(_)
        ));
        let crate::semantic::callable_sets::StoredCallableSetValidation::Valid {
            projection, ..
        } = crate::semantic::callable_sets::validate_stored_callable_set(&fixture.store, type_)
        else {
            panic!("the rest signature must remain authenticated as a callable set")
        };
        let [callable] = projection.call_signatures.as_ref() else {
            panic!("the callable projection must retain one source signature")
        };
        assert_eq!(callable.parameters.len(), 1);
        assert!(callable.rest_parameter.is_some());
        assert_eq!(callable.min_argument_count, 1);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn type_literal_construct_signatures_publish_authenticated_cold_and_warm_members() {
        let mut fixture = interface_fixture(
            "interface Owner {} type Constructor = { new(value: number): string };",
            3_713,
        );
        let literal = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeLiteral).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .expect("the fixture contains a constructor type literal");
        let alias = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeAliasDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .and_then(|declaration| fixture.bound.symbol(declaration))
            .expect("the fixture contains a bound constructor alias");
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_type_literal(&fixture.store, &host, literal, Some(alias)).unwrap();
        let [planned] = plan.call_signatures.as_slice() else {
            panic!("the type literal must retain one declared construct signature")
        };
        assert!(planned.is_construct());
        assert_eq!(planned.parameters.len(), 1);
        assert_eq!(
            fixture.store.symbol(planned.symbol).unwrap().name(),
            InternalSymbolName::New.as_ref(),
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(alias)
        .unwrap();
        let TypeData::Object(object) = fixture.store.type_payload(type_).unwrap().data() else {
            panic!("a constructor type literal must retain its anonymous object")
        };
        assert_eq!(object.structured.call_signature_count, 0);
        let [signature] = object.structured.signatures.as_deref().unwrap() else {
            panic!("the structured object must publish one construct signature")
        };
        let signature = *signature;
        let record = fixture.store.signature(signature).unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        assert!(record.flags().contains(SignatureFlags::CONSTRUCT));
        assert_eq!(record.declaration(), Some(planned.declaration));
        assert_eq!(record.resolved_return_type(), Some(bootstrap.string_type));
        assert_eq!(
            fixture.store.callable_signature_parameter_types(signature),
            Some([bootstrap.number_type].as_slice()),
        );
        assert!(matches!(
            validate_stored_declared_call_set(&fixture.store, type_),
            StoredDeclaredCallSetValidation::Valid(_)
        ));

        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(alias),
            Ok(type_),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn interface_construct_overloads_publish_authenticated_cold_and_warm_members() {
        let mut fixture = interface_fixture(
            "interface Constructor { new(value: number): string; new(value: string): number }",
            3_715,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        assert_eq!(plan.call_signatures.len(), 2);
        assert!(
            plan.call_signatures
                .iter()
                .all(PlannedCallSignature::is_construct)
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let TypeData::Interface(interface) = fixture.store.type_payload(type_).unwrap().data()
        else {
            panic!("constructor overloads must publish one interface")
        };
        assert!(interface.declared_call_signatures.is_none());
        let signatures = interface
            .declared_construct_signatures
            .as_deref()
            .expect("constructor overloads must publish construct signatures");
        assert_eq!(
            interface.reference.object.structured.signatures.as_deref(),
            Some(signatures),
        );
        assert_eq!(
            interface.reference.object.structured.call_signature_count,
            0
        );

        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        for ((signature, planned), (parameter_type, return_type)) in signatures
            .iter()
            .zip(&plan.call_signatures)
            .zip([(number, string), (string, number)])
        {
            let record = fixture.store.signature(*signature).unwrap();
            assert!(record.flags().contains(SignatureFlags::CONSTRUCT));
            assert_eq!(record.declaration(), Some(planned.declaration));
            assert_eq!(record.resolved_return_type(), Some(return_type));
            assert_eq!(
                fixture.store.callable_signature_parameter_types(*signature),
                Some([parameter_type].as_slice()),
            );
        }
        assert_eq!(
            validate_stored_declared_call_set(&fixture.store, type_),
            StoredDeclaredCallSetValidation::Valid(vec![number, string, string, number]),
        );

        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(fixture.symbol),
            Ok(type_),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn interface_call_overloads_and_properties_preserve_identity_cold_and_warm() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Callable { ",
                "(value: string): void; ",
                "readonly field: boolean; ",
                "(value: number): void; ",
                "}",
            ),
            3_796,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let [first, second] = plan.call_signatures.as_slice() else {
            panic!("the interface must retain both call overloads")
        };
        let [property] = plan.properties.as_slice() else {
            panic!("the interface must retain its ordinary property")
        };
        assert!(property.readonly);
        assert_eq!(first.symbol, second.symbol);
        assert_eq!(
            fixture
                .store
                .symbol(first.symbol)
                .and_then(ts_binder::semantic::Symbol::declarations),
            Some([first.declaration, second.declaration].as_slice()),
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let TypeData::Interface(interface) = fixture.store.type_payload(type_).unwrap().data()
        else {
            panic!("mixed call overloads must retain their interface identity")
        };
        let signatures = interface.declared_call_signatures.as_deref().unwrap();
        assert_eq!(signatures.len(), 2);
        for (signature, planned) in signatures.iter().zip(&plan.call_signatures) {
            assert_eq!(
                fixture.store.signature(*signature).unwrap().declaration(),
                Some(planned.declaration),
            );
        }
        assert_eq!(
            interface.reference.object.structured.properties.as_deref(),
            Some([property.symbol].as_slice()),
        );
        assert_eq!(
            fixture.store.symbol(property.symbol).unwrap().check_flags(),
            CheckFlags::READONLY,
        );
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        assert_eq!(
            validate_stored_declared_call_set(&fixture.store, type_),
            StoredDeclaredCallSetValidation::Valid(vec![
                bootstrap.string_type,
                bootstrap.void_type,
                bootstrap.number_type,
                bootstrap.void_type,
                bootstrap.boolean_type,
            ]),
        );

        let state = |store: &CanonicalTypeMapperStore| {
            (
                store.type_len(),
                store.signature_len(),
                store.checker_link_allocated_lengths(),
            )
        };
        let warm = state(&fixture.store);
        assert_eq!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(fixture.symbol),
            Ok(type_),
        );
        assert_eq!(state(&fixture.store), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn mixed_interface_call_sets_reject_poisoned_property_links() {
        let mut fixture = interface_fixture(
            "interface Callable { (value: string): void; field: boolean; }",
            3_797,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let property = plan.properties[0].symbol;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let original = fixture.store.value_symbol_links(property).cloned().unwrap();
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(fixture.store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                write_type: Some(number),
                ..original.clone()
            },
        ));

        assert_eq!(
            validate_stored_declared_call_set(&fixture.store, type_),
            StoredDeclaredCallSetValidation::Malformed,
        );

        assert!(fixture.store.set_value_symbol_links(property, original));
        assert!(matches!(
            validate_stored_declared_call_set(&fixture.store, type_),
            StoredDeclaredCallSetValidation::Valid(_)
        ));
    }

    #[test]
    fn mixed_constructor_method_and_index_interfaces_preserve_authenticated_plans() {
        for (source, properties, methods, indexes, construct, file) in [
            (
                "interface Invalid { new(value: number): string; field: boolean; }",
                1,
                0,
                0,
                true,
                3_798,
            ),
            (
                "interface Invalid { (value: number): string; method(): void; }",
                1,
                1,
                0,
                false,
                3_799,
            ),
            (
                "interface Invalid { (value: number): string; [key: string]: boolean; }",
                0,
                0,
                1,
                false,
                3_800,
            ),
        ] {
            let fixture = interface_fixture(source, file);
            let host = host(&fixture.parsed, &fixture.bound);
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
            assert_eq!(plan.properties.len(), properties);
            assert_eq!(plan.methods.len(), methods);
            assert_eq!(plan.indexes.len(), indexes);
            let [signature] = plan.call_signatures.as_slice() else {
                panic!("each mixed interface must retain one binder-owned signature")
            };
            assert_eq!(signature.is_construct(), construct);
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn optional_interface_construct_parameters_preserve_source_arity_and_warm_identity() {
        let mut fixture =
            interface_fixture("interface Constructor { new(value?: any): string; }", 3_781);
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let [planned] = plan.call_signatures.as_slice() else {
            panic!("the constructor interface must retain its binder-owned signature")
        };
        let [parameter] = planned.parameters.as_slice() else {
            panic!("the constructor signature must retain its optional parameter")
        };
        assert!(planned.is_construct());
        assert!(parameter.optional);
        assert_eq!(planned.min_argument_count(), 0);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let TypeData::Interface(interface) = fixture.store.type_payload(type_).unwrap().data()
        else {
            panic!("the constructor interface must retain its declared identity")
        };
        let [signature] = interface.declared_construct_signatures.as_deref().unwrap() else {
            panic!("the interface must publish one real construct signature")
        };
        let signature = *signature;
        let record = fixture.store.signature(signature).unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        assert_eq!(record.declaration(), Some(planned.declaration));
        assert_eq!(record.parameters(), [parameter.symbol].as_slice());
        assert_eq!(record.min_argument_count(), 0);
        assert_eq!(record.resolved_return_type(), Some(bootstrap.string_type));
        assert_eq!(
            fixture.store.callable_signature_parameter_types(signature),
            Some([bootstrap.any_type].as_slice()),
        );
        assert_eq!(
            validate_stored_declared_call_set(&fixture.store, type_),
            StoredDeclaredCallSetValidation::Valid(vec![bootstrap.any_type, bootstrap.string_type]),
        );

        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(fixture.symbol),
            Ok(type_),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn callable_interfaces_publish_named_members_indexes_and_implicit_constructors() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Mixed { ",
                "value: number; ",
                "callback: (input: number) => string; ",
                "[key: string]: any; ",
                "new(input: number); ",
                "[key: number]: number; ",
                "(input: number): string; ",
                "run(input: string): number; ",
                "}",
            ),
            3_910,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        assert_eq!(
            plan.properties
                .iter()
                .map(|property| property.name.as_str())
                .collect::<Vec<_>>(),
            ["value", "callback", "run"],
        );
        assert_eq!(plan.indexes.len(), 2);
        let [construct, call] = plan.call_signatures.as_slice() else {
            panic!("the callable interface retains both signature families")
        };
        assert!(construct.is_construct());
        assert!(construct.implicit_any_return);
        assert!(!call.is_construct());
        assert!(!call.implicit_any_return);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();

        let TypeData::Interface(interface) = fixture.store.type_payload(type_).unwrap().data()
        else {
            panic!("the mixed surface retains its interface identity")
        };
        assert_eq!(
            interface.reference.object.structured.properties.as_deref(),
            Some(plan.property_symbols().as_slice()),
        );
        assert_eq!(
            interface.declared_index_infos.as_ref().map(Vec::len),
            Some(2)
        );
        assert_eq!(
            interface.reference.object.structured.call_signature_count,
            1,
        );
        let [call_signature] = interface.declared_call_signatures.as_deref().unwrap() else {
            panic!("the interface retains one declared call signature")
        };
        let [construct_signature] = interface.declared_construct_signatures.as_deref().unwrap()
        else {
            panic!("the interface retains one declared construct signature")
        };
        let (call_signature, construct_signature) = (*call_signature, *construct_signature);
        assert_eq!(
            interface.reference.object.structured.signatures.as_deref(),
            Some([call_signature, construct_signature].as_slice()),
        );
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        assert_eq!(
            fixture
                .store
                .signature(construct_signature)
                .and_then(super::super::signatures::Signature::resolved_return_type),
            Some(bootstrap.any_type),
        );
        assert!(
            fixture
                .store
                .function_signature_return_annotation(construct_signature)
                .is_none()
        );
        assert_eq!(
            fixture
                .store
                .callable_signature_parameter_types(construct_signature),
            Some([bootstrap.number_type].as_slice()),
        );
        assert!(matches!(
            validate_stored_declared_call_set(&fixture.store, type_),
            StoredDeclaredCallSetValidation::Valid(_)
        ));
        let crate::semantic::callable_sets::StoredCallableSetValidation::Valid {
            projection, ..
        } = crate::semantic::callable_sets::validate_stored_callable_set(&fixture.store, type_)
        else {
            panic!("named and indexed callable members retain authenticated provenance")
        };
        assert_eq!(projection.call_signatures.len(), 1);
        assert_eq!(projection.call_signatures[0].signature, call_signature);
        assert_eq!(
            projection.construct_signatures.as_ref(),
            &[construct_signature]
        );

        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.index_info_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(fixture.symbol),
            Ok(type_),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.index_info_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn callable_interface_surfaces_reject_poisoned_property_and_index_caches() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Mixed { ",
                "first: number; ",
                "second: string; ",
                "[key: string]: any; ",
                "[key: number]: number; ",
                "new(input: number); ",
                "(input: number): string; ",
                "}",
            ),
            3_911,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let (properties, calls, constructs, indexes) = {
            let TypeData::Interface(interface) = fixture.store.type_payload(type_).unwrap().data()
            else {
                panic!("the poisoned surface retains its interface identity")
            };
            (
                interface
                    .reference
                    .object
                    .structured
                    .properties
                    .clone()
                    .unwrap(),
                interface.declared_call_signatures.clone().unwrap(),
                interface.declared_construct_signatures.clone().unwrap(),
                interface.declared_index_infos.clone().unwrap(),
            )
        };

        for corruption in 0..3 {
            let mut poisoned_properties = properties.clone();
            let mut poisoned_indexes = Some(indexes.clone());
            match corruption {
                0 => poisoned_properties.swap(0, 1),
                1 => poisoned_indexes = None,
                2 => poisoned_indexes.as_mut().unwrap().swap(0, 1),
                _ => unreachable!("the property/index corruption cases are bounded"),
            }
            assert!(fixture.store.set_structured_type_members(
                type_,
                plan.members,
                Some(poisoned_properties),
                Some(calls.clone()),
                Some(constructs.clone()),
                poisoned_indexes,
            ));
            assert_eq!(
                validate_stored_declared_call_set(&fixture.store, type_),
                StoredDeclaredCallSetValidation::Malformed,
            );
            assert_eq!(
                interface_state(&fixture.store, &plan, type_),
                Err(PropertyObjectError::InvalidCachedInterface {
                    symbol: fixture.symbol,
                    type_,
                }),
            );
            assert!(fixture.store.set_structured_type_members(
                type_,
                plan.members,
                Some(properties.clone()),
                Some(calls.clone()),
                Some(constructs.clone()),
                Some(indexes.clone()),
            ));
            assert!(matches!(
                validate_stored_declared_call_set(&fixture.store, type_),
                StoredDeclaredCallSetValidation::Valid(_)
            ));
        }

        let property = properties[0];
        let original = fixture.store.value_symbol_links(property).unwrap().clone();
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(fixture.store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            validate_stored_declared_call_set(&fixture.store, type_),
            StoredDeclaredCallSetValidation::Malformed,
        );
        let mut failed_diagnostics = CanonicalCheckerDiagnostics::default();
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.index_info_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions {
                    no_implicit_any: true,
                    ..CanonicalCheckerOptions::default()
                },
                &mut failed_diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(fixture.symbol)
            .is_err()
        );
        assert!(failed_diagnostics.is_empty());
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.index_info_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            poisoned,
        );
        assert!(fixture.store.set_value_symbol_links(property, original));
        assert_eq!(
            interface_state(&fixture.store, &plan, type_),
            Ok(PropertyObjectState::Resolved(type_)),
        );
    }

    #[test]
    fn callable_type_literals_with_named_or_indexed_members_remain_unsupported() {
        for (source, file) in [
            (
                concat!(
                    "interface Owner {} type Mixed = { ",
                    "value: number; ",
                    "(input: number): string; ",
                    "new(input: number): number; ",
                    "};",
                ),
                3_912,
            ),
            (
                concat!(
                    "interface Owner {} type Mixed = { ",
                    "[key: string]: any; ",
                    "(input: number): string; ",
                    "new(input: number): number; ",
                    "};",
                ),
                3_913,
            ),
        ] {
            let fixture = interface_fixture(source, file);
            let host = host(&fixture.parsed, &fixture.bound);
            let literal = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::TypeLiteral).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .unwrap();
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert!(matches!(
                plan_type_literal(&fixture.store, &host, literal, None),
                Err(PropertyObjectError::UnsupportedMember {
                    kind: SyntaxKind::CallSignature,
                    ..
                })
            ));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn unsupported_optional_signature_parameters_do_not_publish_checker_state() {
        for (source, expected_kind, file) in [
            (
                "interface Constructor { new(value?: string): number; }",
                SyntaxKind::ConstructSignature,
                3_782,
            ),
            (
                "interface Callable { (value?: any): string; }",
                SyntaxKind::CallSignature,
                3_783,
            ),
            (
                concat!(
                    "interface Constructor { ",
                    "new(value?: any): string; ",
                    "<T>(value?: T): value is T; ",
                    "}",
                ),
                SyntaxKind::CallSignature,
                3_791,
            ),
        ] {
            let fixture = interface_fixture(source, file);
            let host = host(&fixture.parsed, &fixture.bound);
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert!(matches!(
                plan_interface(&fixture.store, &host, fixture.symbol),
                Err(PropertyObjectError::UnsupportedMember { kind, .. }) if kind == expected_kind
            ));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn forged_optional_constructor_parameter_plans_fail_before_publication() {
        let mut fixture =
            interface_fixture("interface Constructor { new(value?: any): string; }", 3_790);
        let host = host(&fixture.parsed, &fixture.bound);
        let mut plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
        let type_ = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            fixture.symbol,
            flags,
        )
        .unwrap()
        .unwrap();
        let state = interface_state(&fixture.store, &plan, type_).unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let resolved = [ResolvedCallSignatureTypes {
            parameter_types: vec![bootstrap.any_type],
            return_type: bootstrap.string_type,
        }];
        plan.call_signatures[0].parameters[0].optional = false;
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            publish_declared_members(&mut fixture.store, &plan, state, &[], &[], &resolved),
            Err(PropertyObjectError::InvalidCachedInterface {
                symbol: fixture.symbol,
                type_,
            }),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn inherited_interface_call_signatures_keep_their_declared_owner_and_order() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Base { (): string } ",
                "interface Derived extends Base { (key: string): string }",
            ),
            3_721,
        );
        let derived_declaration = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::InterfaceDeclaration(interface) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &fixture.parsed.arena.get(interface.name)?.data
                else {
                    return None;
                };
                (name.text == "Derived").then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .expect("the fixture contains its derived interface");
        let derived_symbol = fixture
            .bound
            .symbol(derived_declaration)
            .expect("the derived interface has one binder-owned symbol");
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        fixture
            .store
            .merge_global_symbol(globals, derived_symbol)
            .unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let base_plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let derived_plan = plan_interface(&fixture.store, &host, derived_symbol).unwrap();
        assert_eq!(base_plan.call_signatures.len(), 1);
        assert_eq!(derived_plan.call_signatures.len(), 1);
        assert_ne!(
            base_plan.call_signatures[0].symbol,
            derived_plan.call_signatures[0].symbol,
        );
        assert_eq!(
            fixture
                .store
                .symbol(derived_plan.call_signatures[0].symbol)
                .and_then(ts_binder::semantic::Symbol::declarations),
            Some([derived_plan.call_signatures[0].declaration].as_slice()),
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let derived_type = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(derived_symbol)
        .unwrap();
        let base_type = fixture
            .store
            .declared_type_links(fixture.symbol)
            .and_then(|links| links.declared_type)
            .expect("the direct base is resolved before derived publication");
        let (members, declared_members, own_signature, inherited_signature) = {
            let TypeData::Interface(interface) =
                fixture.store.type_payload(derived_type).unwrap().data()
            else {
                panic!("callable heritage must preserve the interface payload")
            };
            let [own] = interface.declared_call_signatures.as_deref().unwrap() else {
                panic!("only the derived call signature belongs to declared members")
            };
            let [first, inherited] = interface
                .reference
                .object
                .structured
                .signatures
                .as_deref()
                .unwrap()
            else {
                panic!("the resolved interface must retain own and inherited signatures")
            };
            assert_eq!(*first, *own);
            assert_eq!(
                interface.reference.object.structured.call_signature_count,
                2
            );
            (
                interface.reference.object.structured.members,
                interface.declared_members,
                *own,
                *inherited,
            )
        };
        assert_ne!(members, declared_members);
        assert_eq!(
            fixture
                .store
                .declared_call_set_type_for_signature(own_signature),
            Some(derived_type),
        );
        assert_eq!(
            fixture
                .store
                .declared_call_set_type_for_signature(inherited_signature),
            Some(base_type),
        );
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            validate_stored_declared_call_set(&fixture.store, derived_type),
            StoredDeclaredCallSetValidation::Valid(vec![string, string, string]),
        );

        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_store().symbol_table_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(derived_symbol),
            Ok(derived_type),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_store().symbol_table_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );

        assert!(fixture.store.set_structured_type_members(
            derived_type,
            members,
            None,
            Some(vec![inherited_signature, own_signature]),
            None,
            None,
        ));
        assert_eq!(
            validate_stored_declared_call_set(&fixture.store, derived_type),
            StoredDeclaredCallSetValidation::Malformed,
        );
        assert!(fixture.store.set_structured_type_members(
            derived_type,
            members,
            None,
            Some(vec![own_signature, inherited_signature]),
            None,
            None,
        ));
        assert!(fixture.store.set_structured_type_members(
            derived_type,
            declared_members,
            None,
            Some(vec![own_signature, inherited_signature]),
            None,
            None,
        ));
        assert_eq!(
            validate_stored_declared_call_set(&fixture.store, derived_type),
            StoredDeclaredCallSetValidation::Malformed,
        );
        assert!(fixture.store.set_structured_type_members(
            derived_type,
            members,
            None,
            Some(vec![own_signature, inherited_signature]),
            None,
            None,
        ));
        assert_eq!(
            validate_stored_declared_call_set(&fixture.store, derived_type),
            StoredDeclaredCallSetValidation::Valid(vec![string, string, string]),
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn interface_accessors_and_properties_share_one_binder_symbol_in_both_merge_orders() {
        for (index, source) in [
            concat!(
                "interface Shape { get value(): string; set value(next: string); } ",
                "interface Shape { value: string; }",
            ),
            concat!(
                "interface Shape { value: string; } ",
                "interface Shape { get value(): string; set value(next: string); }",
            ),
            concat!(
                "interface Shape { set value(next: string); get value(): string; } ",
                "interface Shape { value: string; }",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = interface_fixture(source, 3_860 + u32::try_from(index).unwrap());
            let host = host(&fixture.parsed, &fixture.bound);
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();

            let [property] = plan.properties.as_slice() else {
                panic!("merged accessor declarations retain exactly one property")
            };
            assert_eq!(property.name, "value");
            assert!(!property.optional);
            assert!(!property.readonly);
            assert!(plan.accessor_write_type_node(property.symbol).is_some());
            let [first, second] = plan.accessors.as_slice() else {
                panic!("both accessor declarations must remain in source order")
            };
            let (getter, setter) = if first.parameter.is_none() {
                (first, second)
            } else {
                (second, first)
            };
            assert_eq!(getter.symbol, property.symbol);
            assert_eq!(setter.symbol, property.symbol);
            assert!(getter.parameter.is_none());
            assert!(setter.parameter.is_some());
            assert_eq!(
                fixture.store.symbol(property.symbol).unwrap().flags(),
                SymbolFlags::PROPERTY | SymbolFlags::GET_ACCESSOR | SymbolFlags::SET_ACCESSOR,
            );
            let expected_declarations =
                plan.declarations
                    .iter()
                    .flat_map(|declaration| {
                        let NodeData::InterfaceDeclaration(interface) =
                            &fixture.parsed.arena.get(declaration.node).unwrap().data
                        else {
                            panic!("merged owners must remain interface declarations")
                        };
                        interface.members.nodes.iter().map(move |node| {
                            NodeRef::new(declaration.arena, declaration.file, *node)
                        })
                    })
                    .collect::<Vec<_>>();
            assert_eq!(
                fixture
                    .store
                    .symbol(property.symbol)
                    .unwrap()
                    .declarations(),
                Some(expected_declarations.as_slice()),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn interface_getters_and_setters_preserve_direction_and_parameter_symbols() {
        let fixture = interface_fixture(
            concat!(
                "interface Shape { ",
                "get read(): string; ",
                "set write(value: number); ",
                "get separate(): string; ",
                "set separate(value: string | number); ",
                "}",
            ),
            3_862,
        );
        let host = host(&fixture.parsed, &fixture.bound);

        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();

        assert_eq!(
            plan.properties
                .iter()
                .map(|property| property.name.as_str())
                .collect::<Vec<_>>(),
            ["read", "write", "separate"],
        );
        assert!(plan.properties[0].readonly);
        assert!(
            plan.accessor_write_type_node(plan.properties[0].symbol)
                .is_none()
        );
        assert!(!plan.properties[1].readonly);
        assert_eq!(
            plan.accessor_write_type_node(plan.properties[1].symbol),
            Some(plan.properties[1].type_node),
        );
        assert!(!plan.properties[2].readonly);
        assert_eq!(
            fixture.store.source_node_kind(
                plan.accessor_write_type_node(plan.properties[2].symbol)
                    .unwrap(),
            ),
            Some(SyntaxKind::UnionType),
        );
        let setter = plan
            .accessors
            .iter()
            .find(|accessor| {
                accessor.symbol == plan.properties[2].symbol && accessor.parameter.is_some()
            })
            .unwrap();
        let parameter = setter.parameter.unwrap();
        assert_eq!(
            fixture
                .store
                .symbol(parameter.symbol)
                .and_then(|symbol| symbol.name().as_utf8()),
            Some("value"),
        );
        assert_eq!(
            parameter.type_node,
            plan.accessor_write_type_node(plan.properties[2].symbol)
                .unwrap()
        );
    }

    #[test]
    fn merged_optional_accessor_properties_preserve_the_optional_binder_flag() {
        let fixture = interface_fixture(
            concat!(
                "interface Shape { get value(): string; set value(next: string); } ",
                "interface Shape { value?: string; }",
            ),
            3_863,
        );
        let host = host(&fixture.parsed, &fixture.bound);

        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();

        let [property] = plan.properties.as_slice() else {
            panic!("one optional property merges with its accessor pair")
        };
        assert!(property.optional);
        assert_eq!(
            fixture.store.symbol(property.symbol).unwrap().flags(),
            SymbolFlags::PROPERTY
                | SymbolFlags::OPTIONAL
                | SymbolFlags::GET_ACCESSOR
                | SymbolFlags::SET_ACCESSOR,
        );
    }

    #[test]
    fn duplicate_interface_accessors_keep_binder_diagnostics_and_fail_before_publication() {
        for (index, source) in [
            "interface Shape { get value(): string; get value(): string; }",
            "interface Shape { set value(left: string); set value(right: string); }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = interface_fixture(source, 3_864 + u32::try_from(index).unwrap());
            let host = host(&fixture.parsed, &fixture.bound);
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture.bound.diagnostics().len(),
            );

            assert!(plan_interface(&fixture.store, &host, fixture.symbol).is_err());
            assert!(!fixture.bound.diagnostics().is_empty());
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                    fixture.bound.diagnostics().len(),
                ),
                before,
            );
        }
    }

    #[test]
    fn interface_methods_keep_binder_symbols_and_parameter_annotations_in_source_order() {
        let fixture = interface_fixture(
            concat!(
                "interface Shape { ",
                "first: string; ",
                "reset(): void; ",
                "run(...args: any[]): void; ",
                "last: number ",
                "}",
            ),
            3_765,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();

        assert_eq!(
            plan.properties
                .iter()
                .map(|property| property.name.as_str())
                .collect::<Vec<_>>(),
            ["first", "reset", "run", "last"],
        );
        let [reset, run] = plan.methods.as_slice() else {
            panic!("the interface must retain both named method signatures")
        };
        assert_eq!(reset.symbol, plan.properties[1].symbol);
        assert_eq!(reset.flags, SignatureFlags::NONE);
        assert!(reset.parameters.is_empty());
        assert_eq!(run.symbol, plan.properties[2].symbol);
        assert_eq!(run.flags, SignatureFlags::HAS_REST_PARAMETER);
        let [parameter] = run.parameters.as_slice() else {
            panic!("the rest method must retain its one binder-owned parameter")
        };
        assert_eq!(
            fixture.store.source_node_kind(parameter.type_node),
            Some(SyntaxKind::ArrayType),
        );
        assert_eq!(
            fixture
                .store
                .symbol(parameter.symbol)
                .and_then(|symbol| symbol.name().as_utf8()),
            Some("args"),
        );
        assert_eq!(
            plan.call_type_nodes()
                .filter_map(|node| fixture.store.source_node_kind(node))
                .collect::<Vec<_>>(),
            [
                SyntaxKind::VoidKeyword,
                SyntaxKind::ArrayType,
                SyntaxKind::VoidKeyword,
            ],
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn generic_interface_method_plans_preserve_local_type_parameters_and_typed_rest_arrays() {
        let fixture = interface_fixture(
            concat!(
                "interface Shape { ",
                "map<Value extends string = string>(value: Value): Value; ",
                "map<Other>(...values: Other[]): Other; ",
                "}",
            ),
            3_890,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();

        let [first, second] = plan.methods.as_slice() else {
            panic!("the generic method symbol must preserve both declaration overloads")
        };
        assert_eq!(first.symbol, second.symbol);
        let [value] = first.type_parameters.as_slice() else {
            panic!("the first overload must retain its binder-owned type parameter")
        };
        assert!(value.constraint.is_some());
        assert!(value.default_type.is_some());
        assert_eq!(
            fixture.store.symbol(value.symbol).unwrap().name().as_utf8(),
            Some("Value"),
        );
        let [other] = second.type_parameters.as_slice() else {
            panic!("the rest overload must retain an independent type parameter")
        };
        assert_ne!(value.symbol, other.symbol);
        assert_eq!(second.flags, SignatureFlags::HAS_REST_PARAMETER);
        assert_eq!(
            fixture
                .store
                .source_node_kind(second.parameters[0].type_node),
            Some(SyntaxKind::ArrayType),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn generic_interface_methods_preserve_optional_annotation_identity_and_tuple_rest() {
        let fixture = interface_fixture(
            concat!(
                "interface Contract<Value> { ",
                "then(filter: null): Value; ",
                "then(filter?: ((null))): Value; ",
                "spread(...values: [value: Value]): Value; ",
                "}",
            ),
            3_898,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();

        let [required, optional, spread] = plan.methods.as_slice() else {
            panic!("the generic interface retains two overloads and its tuple-rest method")
        };
        assert_eq!(required.symbol, optional.symbol);
        assert!(required.parameters[0].null_literal_identity);
        assert!(!required.parameters[0].optional);
        assert_eq!(required.minimum_argument_count, 1);
        assert!(optional.parameters[0].null_literal_identity);
        assert!(optional.parameters[0].optional);
        assert_eq!(optional.minimum_argument_count, 0);
        assert_eq!(
            fixture
                .store
                .source_node_kind(optional.parameters[0].type_node),
            Some(SyntaxKind::ParenthesizedType),
        );
        assert_eq!(
            fixture
                .store
                .source_node_kind(optional.parameters[0].identity_node),
            Some(SyntaxKind::LiteralType),
        );
        assert_eq!(spread.flags, SignatureFlags::HAS_REST_PARAMETER);
        assert_eq!(
            fixture
                .store
                .source_node_kind(spread.parameters[0].type_node),
            Some(SyntaxKind::TupleType),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn interface_methods_accept_the_exact_class_implementation_tuple_union_rest_shape() {
        let fixture = interface_fixture(
            concat!(
                "declare class MySettable implements Settable { ",
                "set(option: Record<string, unknown>): void; ",
                "set(name: string, value: unknown): void; ",
                "} ",
                "interface Settable { ",
                "set(...args: ",
                "[option: Record<string, unknown>] | ",
                "[name: string, value: unknown] | ",
                "[name: string]): void; ",
                "}",
            ),
            3_903,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();

        let [method] = plan.methods.as_slice() else {
            panic!("the implemented interface retains one binder-owned set method")
        };
        let [rest] = method.parameters.as_slice() else {
            panic!("the set method retains one union-of-tuples rest parameter")
        };
        let NodeData::UnionTypeNode(union) =
            &fixture.parsed.arena.get(rest.type_node.node).unwrap().data
        else {
            panic!("the rest annotation retains its exact union syntax")
        };
        assert_eq!(method.flags, SignatureFlags::HAS_REST_PARAMETER);
        assert_eq!(method.minimum_argument_count, 0);
        assert_eq!(union.types.nodes.len(), 3);
        assert_eq!(
            union
                .types
                .nodes
                .iter()
                .map(|node| {
                    let NodeData::TupleTypeNode(tuple) =
                        &fixture.parsed.arena.get(*node).unwrap().data
                    else {
                        panic!("each union constituent must remain a tuple")
                    };
                    tuple.elements.nodes.len()
                })
                .collect::<Vec<_>>(),
            [1, 2, 1],
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One source proves tuple-union identity, warm replay, and poison.
    fn tuple_union_method_rest_parameters_publish_authenticated_cold_and_warm() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Settable { ",
                "set(...args: ",
                "[option: Options] | ",
                "[name: string, value: unknown] | ",
                "[name: string]): void; ",
                "} ",
                "interface Options { value: unknown; }",
            ),
            3_904,
        );
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        let options = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Options"))
            .unwrap();
        fixture.store.merge_global_symbol(globals, options).unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let [method] = plan.methods.as_slice() else {
            panic!("the tuple-union interface retains one method")
        };
        let [parameter] = method.parameters.as_slice() else {
            panic!("the method retains its one binder-owned rest parameter")
        };
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let owner = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let callable = fixture
            .store
            .value_symbol_links(method.symbol)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let crate::semantic::callable_sets::StoredCallableSetValidation::Valid {
            projection, ..
        } = crate::semantic::callable_sets::validate_stored_callable_set(&fixture.store, callable)
        else {
            panic!("the tuple-union method retains authenticated callable provenance")
        };
        let [projected] = projection.call_signatures.as_ref() else {
            panic!("the tuple-union method publishes exactly one source signature")
        };
        let signature = projected.signature;
        let rest = projected
            .rest_parameter
            .expect("the tuple union remains the method rest parameter");
        assert!(projected.parameters.is_empty());
        assert_eq!(projected.min_argument_count, 0);
        assert_eq!(
            fixture.store.callable_signature_parameter_types(signature),
            Some([rest].as_slice()),
        );
        assert_eq!(
            fixture
                .store
                .type_node_links(parameter.type_node)
                .and_then(|links| links.resolved_type),
            Some(rest),
        );
        assert_eq!(
            fixture.store.interface_method_linked_type(signature),
            Some(callable),
        );
        let TypeData::Union(union) = fixture.store.type_payload(rest).unwrap().data() else {
            panic!("the rest parameter must preserve its tuple-union type")
        };
        assert_eq!(union.union.types.len(), 3);
        let mut lengths = union
            .union
            .types
            .iter()
            .map(|tuple| {
                let shape = fixture
                    .store
                    .canonical_tuple_shape(*tuple)
                    .unwrap()
                    .expect("each rest-union constituent retains its canonical tuple identity");
                assert!(
                    shape
                        .element_infos()
                        .iter()
                        .all(|element| element.labeled_declaration().is_some())
                );
                shape.element_types().len()
            })
            .collect::<Vec<_>>();
        lengths.sort_unstable();
        assert_eq!(lengths, [1, 1, 2]);

        let void = fixture.store.intrinsic_bootstrap().unwrap().void_type;
        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .union_cache_len(),
        );
        for _ in 0..2 {
            assert_eq!(
                CanonicalTypeQuery::new(
                    &mut fixture.store,
                    &host,
                    CanonicalCheckerOptions::default(),
                    &mut diagnostics,
                )
                .unwrap()
                .get_declared_type_of_symbol(fixture.symbol),
                Ok(owner),
            );
            assert_eq!(
                CanonicalTypeQuery::new(
                    &mut fixture.store,
                    &host,
                    CanonicalCheckerOptions::default(),
                    &mut diagnostics,
                )
                .unwrap()
                .get_return_type_of_signature(signature),
                Ok(void),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                    fixture
                        .store
                        .intrinsic_bootstrap()
                        .unwrap()
                        .union_cache_len(),
                ),
                warm,
            );
        }

        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(fixture.store.set_value_symbol_links(
            parameter.symbol,
            ValueSymbolLinks {
                resolved_type: Some(number),
                ..ValueSymbolLinks::default()
            },
        ));
        assert!(matches!(
            crate::semantic::callable_sets::validate_stored_callable_set(&fixture.store, callable),
            crate::semantic::callable_sets::StoredCallableSetValidation::Malformed { .. }
        ));
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .union_cache_len(),
        );
        assert!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_return_type_of_signature(signature)
            .is_err()
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture
                    .store
                    .intrinsic_bootstrap()
                    .unwrap()
                    .union_cache_len(),
            ),
            poisoned,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn conditional_type_literal_methods_preserve_authenticated_inferred_rest_parameters() {
        let fixture = interface_fixture(
            concat!(
                "interface Owner {} ",
                "type Unwrap<Value> = Value extends { ",
                "then(value: infer Result, ...args: infer Rest): any; ",
                "} ? Result : never;",
            ),
            3_901,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let literal = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeLiteral).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let plan = plan_type_literal(&fixture.store, &host, literal, None).unwrap();

        let [method] = plan.methods.as_slice() else {
            panic!("the conditional thenable retains its binder-owned method")
        };
        let [value, rest] = method.parameters.as_slice() else {
            panic!("the thenable retains its inferred value and rest parameters")
        };
        assert_eq!(method.flags, SignatureFlags::HAS_REST_PARAMETER);
        assert_eq!(method.minimum_argument_count, 1);
        assert_eq!(
            fixture.store.source_node_kind(value.type_node),
            Some(SyntaxKind::InferType),
        );
        assert_eq!(
            fixture.store.source_node_kind(rest.type_node),
            Some(SyntaxKind::InferType),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn generic_interface_methods_reject_invalid_rest_annotations_before_publication() {
        for (index, source) in [
            "interface Contract<Value> { spread(...values: string): Value; }",
            "interface Contract<Value> { spread(...values: [value: Value] | string): Value; }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = interface_fixture(source, 3_899 + u32::try_from(index).unwrap());
            let host = host(&fixture.parsed, &fixture.bound);
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert!(matches!(
                plan_generic_interface(&fixture.store, &host, fixture.symbol),
                Err(PropertyObjectError::UnsupportedMember {
                    kind: SyntaxKind::MethodSignature,
                    ..
                })
            ));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn optional_generic_methods_publish_exact_signatures_and_replay_warm() {
        let mut fixture = interface_fixture(
            "interface Contract<Value> { select(value?: Value): Value; }",
            3_902,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let [method] = plan.methods.as_slice() else {
            panic!("the generic interface retains one optional method")
        };
        let [parameter] = method.parameters.as_slice() else {
            panic!("the optional method retains its binder-owned parameter")
        };
        assert!(parameter.optional);
        assert_eq!(method.minimum_argument_count, 0);
        assert_eq!(
            fixture.store.source_node_kind(parameter.type_node),
            Some(SyntaxKind::TypeReference),
        );
        assert_eq!(
            fixture.store.source_node_kind(parameter.identity_node),
            Some(SyntaxKind::TypeReference),
        );

        let flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
        let target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            fixture.symbol,
            flags,
        )
        .unwrap()
        .unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let value = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_type_from_type_node(method.return_type)
        .unwrap();
        assert!(fixture.store.publish_interface_no_base_resolution(target));
        assert_eq!(
            publish_generic_interface_declared_members(&mut fixture.store, &plan, target, &[value]),
            Ok(target),
        );

        let callable = fixture
            .store
            .value_symbol_links(method.symbol)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let crate::semantic::callable_sets::StoredCallableSetValidation::Valid {
            projection, ..
        } = crate::semantic::callable_sets::validate_stored_callable_set(&fixture.store, callable)
        else {
            panic!("the optional generic method retains authenticated callable provenance")
        };
        let [projected] = projection.call_signatures.as_ref() else {
            panic!("the optional generic method publishes exactly one signature")
        };
        let signature = projected.signature;
        assert_eq!(projected.parameters, [value]);
        assert_eq!(projected.min_argument_count, 0);
        assert_eq!(projected.return_type, Some(value));
        assert_eq!(
            fixture.store.callable_signature_parameter_types(signature),
            Some([value].as_slice()),
        );

        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        for _ in 0..2 {
            assert_eq!(
                publish_generic_interface_declared_members(
                    &mut fixture.store,
                    &plan,
                    target,
                    &[value],
                ),
                Ok(target),
            );
            assert_eq!(
                CanonicalTypeQuery::new(
                    &mut fixture.store,
                    &host,
                    CanonicalCheckerOptions::default(),
                    &mut diagnostics,
                )
                .unwrap()
                .get_return_type_of_signature(signature),
                Ok(value),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_interface_methods_accept_recursive_mapped_array_rest_annotations() {
        let fixture = interface_fixture(
            concat!(
                "type PartialDeep<T> = { [K in keyof T]?: PartialDeep<T[K]> }; ",
                "type Many<T> = T | readonly T[]; ",
                "interface Collection<T> { ",
                "sortBy(...iteratees: Many<PartialDeep<T>>[]): Collection<T>; ",
                "}",
            ),
            3_891,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();

        let [method] = plan.methods.as_slice() else {
            panic!("the collection interface must retain its sort method")
        };
        assert_eq!(method.flags, SignatureFlags::HAS_REST_PARAMETER);
        let [rest] = method.parameters.as_slice() else {
            panic!("the sort method must retain its mapped-array rest parameter")
        };
        let NodeData::ArrayTypeNode(array) =
            &fixture.parsed.arena.get(rest.type_node.node).unwrap().data
        else {
            panic!("the rest annotation must retain its original array syntax")
        };
        let element = NodeRef::new(
            rest.type_node.arena,
            rest.type_node.file,
            array.element_type,
        );
        assert_eq!(
            fixture.store.source_node_kind(element),
            Some(SyntaxKind::TypeReference),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One fixture proves accessor and generic-method cache identity.
    fn generic_method_signatures_publish_authenticated_type_parameters_cold_and_warm() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Shape { ",
                "get current(): string; set current(value: string); ",
                "map<Value extends string = string>(value: Value): Value; ",
                "}",
            ),
            3_892,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        assert_eq!(plan.accessors.len(), 2);
        let method = &plan.methods[0];
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let owner = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let callable = fixture
            .store
            .value_symbol_links(method.symbol)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let [signature] = fixture
            .store
            .type_payload(callable)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .unwrap()
        else {
            panic!("the generic method must publish exactly one signature")
        };
        let signature = *signature;
        let [parameter] = fixture
            .store
            .signature(signature)
            .unwrap()
            .type_parameters()
        else {
            panic!("the method signature must preserve its original generic parameter")
        };
        let parameter = *parameter;
        assert_eq!(
            cached_ordinary_type_parameter_owner(&fixture.store, parameter),
            Some(method.type_parameters[0].symbol),
        );
        let TypeData::TypeParameter(data) = fixture.store.type_payload(parameter).unwrap().data()
        else {
            panic!("the generic signature parameter must retain a type-parameter payload")
        };
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(data.constraint, Some(string));
        assert_eq!(data.resolved_default_type, Some(string));
        assert_eq!(
            fixture
                .store
                .value_symbol_links(plan.properties[0].symbol)
                .and_then(|links| links.resolved_type),
            Some(string),
        );
        assert_eq!(
            fixture.store.callable_signature_parameter_types(signature),
            Some([parameter].as_slice()),
        );
        assert_eq!(
            fixture.store.interface_method_linked_type(signature),
            Some(callable)
        );
        assert_eq!(
            crate::semantic::structured_members::valid_interface_method_value(
                &fixture.store,
                method.symbol,
                callable,
            ),
            Some(signature),
        );
        let crate::semantic::callable_sets::StoredCallableSetValidation::Valid {
            projection, ..
        } = crate::semantic::callable_sets::validate_stored_callable_set(&fixture.store, callable)
        else {
            panic!("the generic method must retain authenticated callable provenance")
        };
        assert!(projection.call_signatures[0].strict_variance_exempt);
        assert_eq!(projection.call_signatures[0].parameters, vec![parameter]);

        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(fixture.symbol),
            Ok(owner),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Cold and warm union identities share one declared signature.
    fn generic_method_unions_preserve_parameter_identity_and_replay_warm() {
        let mut fixture = interface_fixture(
            "interface Shape { map<Value>(value: Value | string): Value | string; }",
            3_895,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let method = &plan.methods[0];
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let owner = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let callable = fixture
            .store
            .value_symbol_links(method.symbol)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let [signature] = fixture
            .store
            .type_payload(callable)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .unwrap()
        else {
            panic!("the union method must retain its original generic signature")
        };
        let signature = *signature;
        let record = fixture.store.signature(signature).unwrap();
        let [parameter] = record.type_parameters() else {
            panic!("the union method must retain its binder-owned type parameter")
        };
        let parameter = *parameter;
        let union = record.resolved_return_type().unwrap();
        let TypeData::Union(data) = fixture.store.type_payload(union).unwrap().data() else {
            panic!("the method must retain its parameter-or-string union")
        };
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(data.union.types.len(), 2);
        assert!(data.union.types.contains(&parameter));
        assert!(data.union.types.contains(&string));
        assert_eq!(
            cached_ordinary_type_parameter_owner(&fixture.store, parameter),
            Some(method.type_parameters[0].symbol),
        );
        assert_eq!(
            fixture.store.callable_signature_parameter_types(signature),
            Some([union].as_slice()),
        );
        assert_eq!(
            fixture
                .store
                .type_node_links(method.parameters[0].type_node)
                .and_then(|links| links.resolved_type),
            Some(union),
        );
        assert_eq!(
            fixture
                .store
                .type_node_links(method.return_type)
                .and_then(|links| links.resolved_type),
            Some(union),
        );
        assert!(matches!(
            crate::semantic::callable_sets::validate_stored_callable_set(&fixture.store, callable,),
            crate::semantic::callable_sets::StoredCallableSetValidation::Valid { .. }
        ));

        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .union_cache_len(),
        );
        assert_eq!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(fixture.symbol),
            Ok(owner),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture
                    .store
                    .intrinsic_bootstrap()
                    .unwrap()
                    .union_cache_len(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn inherited_generic_methods_compare_their_type_parameters_by_position() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Base { map<Value>(value: Value): Value } ",
                "interface Derived extends Base { map<Value>(value: Value): Value }",
            ),
            3_894,
        );
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        let derived = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Derived"))
            .unwrap();
        fixture.store.merge_global_symbol(globals, derived).unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(derived)
        .unwrap();

        let TypeData::Interface(interface) = fixture.store.type_payload(type_).unwrap().data()
        else {
            panic!("generic method inheritance must retain its interface payload")
        };
        assert_eq!(
            interface
                .reference
                .object
                .structured
                .properties
                .as_ref()
                .map(Vec::len),
            Some(1),
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn interface_method_overloads_share_one_property_and_keep_each_signature() {
        let fixture = interface_fixture(
            "interface Shape { run(value: string): number; run(...args: any[]): void }",
            3_766,
        );
        let host = host(&fixture.parsed, &fixture.bound);

        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();

        assert_eq!(plan.properties.len(), 1);
        let [first, second] = plan.methods.as_slice() else {
            panic!("the method symbol must retain both overload declarations")
        };
        assert_eq!(first.symbol, second.symbol);
        assert_eq!(first.symbol, plan.properties[0].symbol);
        assert_ne!(first.declaration, second.declaration);
        assert_eq!(first.flags, SignatureFlags::NONE);
        assert_eq!(first.parameters.len(), 1);
        assert_eq!(second.flags, SignatureFlags::HAS_REST_PARAMETER);
        assert_eq!(
            fixture
                .store
                .symbol(first.symbol)
                .and_then(ts_binder::semantic::Symbol::declarations),
            Some([first.declaration, second.declaration].as_slice()),
        );
    }

    #[test]
    fn interface_method_overloads_publish_one_callable_and_replay_warm() {
        let mut fixture = global_array_augmentation_fixture(
            concat!(
                "interface Array<T> { (): any[]; } ",
                "interface Contract { ",
                "run(value: string): number; ",
                "run(...args: any[]): void; ",
                "}",
            ),
            3_776,
        );
        let locals = fixture
            .source_bound
            .locals(fixture.source_bound.source_file())
            .unwrap();
        let contract = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Contract"))
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        fixture
            .store
            .merge_global_symbol(globals, contract)
            .unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&fixture.library.arena, &fixture.library_bound),
                (&fixture.source.arena, &fixture.source_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_interface(&fixture.store, &host, contract).unwrap();
        let flags = fixture.store.symbol(contract).unwrap().flags();
        let owner_type = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            contract,
            flags,
        )
        .unwrap()
        .unwrap();
        let (any, string, number, void) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.any_type,
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.void_type,
            )
        };
        let any_array = fixture.global_types.any_array_type;
        let mut resolved = Vec::new();
        for method in &plan.methods {
            let return_type = match fixture.store.source_node_kind(method.return_type) {
                Some(SyntaxKind::NumberKeyword) => number,
                Some(SyntaxKind::VoidKeyword) => void,
                _ => panic!("the method fixture has numeric and void returns"),
            };
            assert!(fixture.store.set_type_node_links(
                method.return_type,
                TypeNodeLinks {
                    resolved_type: Some(return_type),
                    ..TypeNodeLinks::default()
                },
            ));
            let mut parameter_types = Vec::new();
            for parameter in &method.parameters {
                let parameter_type = match fixture.store.source_node_kind(parameter.type_node) {
                    Some(SyntaxKind::StringKeyword) => string,
                    Some(SyntaxKind::ArrayType) => {
                        let NodeData::ArrayTypeNode(array) = &fixture
                            .source
                            .arena
                            .get(parameter.type_node.node)
                            .unwrap()
                            .data
                        else {
                            unreachable!("the rest annotation is an array type")
                        };
                        let element = NodeRef::new(
                            parameter.type_node.arena,
                            parameter.type_node.file,
                            array.element_type,
                        );
                        assert!(fixture.store.set_type_node_links(
                            element,
                            TypeNodeLinks {
                                resolved_type: Some(any),
                                ..TypeNodeLinks::default()
                            },
                        ));
                        any_array
                    }
                    _ => panic!("the method fixture has string and any-array parameters"),
                };
                assert!(fixture.store.set_type_node_links(
                    parameter.type_node,
                    TypeNodeLinks {
                        resolved_type: Some(parameter_type),
                        ..TypeNodeLinks::default()
                    },
                ));
                parameter_types.push(parameter_type);
            }
            resolved.push(ResolvedCallSignatureTypes {
                parameter_types,
                return_type,
            });
        }

        let method_types =
            publish_interface_method_values(&mut fixture.store, &plan, &resolved).unwrap();

        assert_eq!(method_types.len(), 2);
        assert_eq!(method_types[0], method_types[1]);
        let method_type = method_types[0];
        let method_record = fixture.store.type_payload(method_type).unwrap();
        let signatures = method_record
            .data()
            .structured()
            .and_then(|structured| structured.signatures.as_deref())
            .unwrap();
        assert_eq!(signatures.len(), 2);
        assert_eq!(
            fixture.store.signature(signatures[0]).unwrap().flags(),
            SignatureFlags::NONE,
        );
        assert_eq!(
            fixture
                .store
                .signature(signatures[0])
                .unwrap()
                .min_argument_count(),
            1,
        );
        assert_eq!(
            fixture.store.signature(signatures[1]).unwrap().flags(),
            SignatureFlags::HAS_REST_PARAMETER,
        );
        assert_eq!(
            fixture
                .store
                .signature(signatures[1])
                .unwrap()
                .min_argument_count(),
            0,
        );
        assert!(matches!(
            crate::semantic::callable_sets::validate_stored_callable_set(
                &fixture.store,
                method_type,
            ),
            crate::semantic::callable_sets::StoredCallableSetValidation::Valid { .. }
        ));

        let state = interface_state(&fixture.store, &plan, owner_type).unwrap();
        assert_eq!(state, PropertyObjectState::Shell(owner_type));
        assert_eq!(
            publish_declared_members(&mut fixture.store, &plan, state, &[method_type], &[], &[],),
            Ok(owner_type),
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            publish_interface_method_values(&mut fixture.store, &plan, &resolved),
            Ok(method_types),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Prove both library overloads and every lazy owner boundary.
    fn default_library_array_concat_publishes_only_generic_declaration_overloads() {
        let library = parse_source_file(concat!(
            "interface IArguments {} ",
            "interface Array<T> { ",
            "concat(...items: ConcatArray<T>[]): T[]; ",
            "concat(...items: (T | ConcatArray<T>)[]): T[]; ",
            "untouched(): void; ",
            "} declare var Array: any; ",
            "interface ConcatArray<T> { ",
            "readonly length: number; readonly [index: number]: T; ",
            "join(separator?: string): string; ",
            "slice(start?: number, end?: number): T[]; ",
            "} ",
            "interface Object {} interface Function {} ",
            "interface String {} interface Number {} interface Boolean {} ",
            "interface RegExp {} interface ReadonlyArray<T> {} interface ThisType<T> {}",
        ));
        let source = parse_source_file("type Pair = [number, number];");
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let library_file = FileId::new(3_780);
        let source_file = FileId::new(3_781);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, default_library) in [
            (&library, library_file, true),
            (&source, source_file, false),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!("\"/array-concat-{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        default_library,
                        default_library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let library_bound = files.remove(&library_file).unwrap();
        let source_bound = files.remove(&source_file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        for (parsed, file) in [(&library, library_file), (&source, source_file)] {
            assert!(
                store
                    .register_source_file(&parsed.arena, parsed.source_file, file)
                    .is_some()
            );
        }
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        let library_symbols = store
            .symbol_table(library_bound.locals(library_bound.source_file()).unwrap())
            .unwrap()
            .iter()
            .map(|(_, symbol)| symbol)
            .collect::<Vec<_>>();
        for symbol in library_symbols {
            store.merge_global_symbol(globals, symbol).unwrap();
        }
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, &library_bound),
                (&source.arena, &source_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let global_types =
            initialize_global_library_types(&mut store, &host, globals, false).unwrap();
        let pair = store
            .symbol_table(source_bound.locals(source_bound.source_file()).unwrap())
            .and_then(|locals| locals.get_source("Pair"))
            .unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let pair = CanonicalTypeQuery::new_with_global_types(
            &mut store,
            &host,
            &global_types,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(pair)
        .unwrap();
        let receiver = store
            .create_canonical_array_type(&global_types, pair, false)
            .unwrap();
        let type_parameter = match store.type_payload(global_types.array_type).unwrap().data() {
            TypeData::Interface(interface) => interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .unwrap()[0],
            _ => panic!("the global Array target must retain one generic parameter"),
        };
        let owner = store
            .type_payload(global_types.array_type)
            .and_then(TypeRecord::symbol)
            .and_then(|owner| store.get_merged_symbol(owner))
            .unwrap();
        let members = store.symbol(owner).unwrap().members().unwrap();
        let method = store
            .symbol_table(members)
            .and_then(|members| members.get_source("concat"))
            .unwrap();
        let untouched = store
            .symbol_table(members)
            .and_then(|members| members.get_source("untouched"))
            .unwrap();
        assert!(store.value_symbol_links(method).is_none());
        assert!(store.value_symbol_links(untouched).is_none());

        let method_type =
            materialize_global_array_concat_method(&mut store, &host, &global_types, receiver)
                .unwrap()
                .unwrap();

        let object = store.type_payload(method_type).unwrap();
        let signatures = object
            .data()
            .structured()
            .and_then(|structured| structured.signatures.as_deref())
            .unwrap();
        assert_eq!(signatures.len(), 2);
        let mut parameter_types = Vec::new();
        for signature in signatures {
            let record = store.signature(*signature).unwrap();
            assert_eq!(record.flags(), SignatureFlags::HAS_REST_PARAMETER);
            assert_eq!(record.min_argument_count(), 0);
            assert_eq!(record.resolved_return_type(), Some(global_types.array_type));
            let [parameter] = record.parameters() else {
                panic!("each Array.concat overload has one rest parameter")
            };
            let parameter_type = store
                .value_symbol_links(*parameter)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let parameter_declaration = store
                .symbol(*parameter)
                .unwrap()
                .value_declaration()
                .unwrap();
            let parameter_annotation = store
                .source_direct_type_annotation(parameter_declaration)
                .unwrap();
            let return_annotation = store
                .source_direct_type_annotation(record.declaration().unwrap())
                .unwrap();
            assert_eq!(
                store
                    .type_node_links(parameter_annotation)
                    .and_then(|links| links.resolved_type),
                Some(parameter_type),
            );
            assert_eq!(
                store
                    .type_node_links(return_annotation)
                    .and_then(|links| links.resolved_type),
                Some(global_types.array_type),
            );
            assert_eq!(
                store.function_signature_return_annotation(*signature),
                Some((return_annotation, false)),
            );
            assert_eq!(
                store.callable_signature_parameter_types(*signature),
                Some([parameter_type].as_slice()),
            );
            parameter_types.push(parameter_type);
        }
        let first = store
            .canonical_array_reference(&global_types, parameter_types[0])
            .unwrap()
            .unwrap();
        let concat = validate_direct_generic_reference(&store, first.element_type).unwrap();
        assert_eq!(concat.type_arguments.as_slice(), &[type_parameter]);
        assert_ne!(type_parameter, pair);
        let (concat_parameter, concat_index, source_join, source_slice) = {
            let TypeData::Interface(interface) = store.type_payload(concat.target).unwrap().data()
            else {
                panic!("ConcatArray must retain its generic interface target")
            };
            assert!(interface.declared_members_resolved);
            let [index] = interface.declared_index_infos.as_deref().unwrap() else {
                panic!("ConcatArray must publish its numeric index signature")
            };
            let members = store
                .symbol_table(interface.declared_members.unwrap())
                .unwrap();
            assert_eq!(members.len(), 3);
            assert!(members.get(InternalSymbolName::Index.as_ref()).is_none());
            (
                interface
                    .reference
                    .resolved_type_arguments
                    .as_ref()
                    .unwrap()[0],
                *index,
                members.get_source("join").unwrap(),
                members.get_source("slice").unwrap(),
            )
        };
        let declared_index = store.index_info(concat_index).unwrap();
        assert_eq!(
            declared_index.key_type(),
            store.intrinsic_bootstrap().unwrap().number_type,
        );
        assert_eq!(declared_index.value_type(), concat_parameter);
        assert!(declared_index.is_readonly());
        for method in [source_join, source_slice] {
            let callable = store
                .value_symbol_links(method)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let [signature] = store
                .type_payload(callable)
                .and_then(|record| record.data().structured())
                .and_then(|structured| structured.signatures.as_deref())
                .unwrap()
            else {
                panic!("ConcatArray methods must retain one source signature")
            };
            assert_eq!(store.signature(*signature).unwrap().min_argument_count(), 0);
        }
        let second = store
            .canonical_array_reference(&global_types, parameter_types[1])
            .unwrap()
            .unwrap();
        let TypeData::Union(union) = store.type_payload(second.element_type).unwrap().data() else {
            panic!("the second overload retains the element-or-ConcatArray union")
        };
        assert!(union.union.types.contains(&type_parameter));
        assert!(union.union.types.contains(&first.element_type));
        assert!(store.value_symbol_links(untouched).is_none());
        let TypeData::Interface(array) =
            store.type_payload(global_types.array_type).unwrap().data()
        else {
            panic!("the array target remains an interface")
        };
        assert!(!array.declared_members_resolved);
        assert!(matches!(
            crate::semantic::callable_sets::validate_stored_callable_set(&store, method_type),
            crate::semantic::callable_sets::StoredCallableSetValidation::Valid { .. }
        ));

        let concat_pair = store
            .create_direct_generic_reference_type(concat.target, &[pair])
            .unwrap();
        let array_target = super::super::instantiated_members::GenericInterfaceArrayTarget::new(
            global_types.array_type,
        );
        let concat_members = store
            .resolve_generic_interface_members(concat_pair, Some(array_target))
            .unwrap();
        let [length, join, slice] = concat_members.properties() else {
            panic!("ConcatArray must preserve length, join, and slice in source order")
        };
        assert_eq!(
            store.symbol(*length).unwrap().name().as_utf8(),
            Some("length")
        );
        assert_eq!(*join, source_join);
        assert_ne!(*slice, source_slice);
        let [instantiated_index] = store
            .type_payload(concat_pair)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.index_infos.as_deref())
            .unwrap()
        else {
            panic!("ConcatArray<Pair> must publish its numeric index")
        };
        assert_eq!(
            store.index_info(*instantiated_index).unwrap().value_type(),
            pair
        );
        let specialized_slice = store
            .resolve_generic_interface_property(concat_pair, "slice", Some(array_target))
            .unwrap()
            .unwrap()
            .type_id();
        let [slice_signature] = store
            .type_payload(specialized_slice)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .unwrap()
        else {
            panic!("the instantiated slice must retain its source signature")
        };
        let slice_return = store
            .signature(*slice_signature)
            .and_then(super::super::signatures::Signature::resolved_return_type)
            .unwrap();
        assert_eq!(
            store
                .canonical_array_reference(&global_types, slice_return)
                .unwrap()
                .unwrap()
                .element_type,
            pair,
        );

        let warm = (
            store.type_len(),
            store.signature_len(),
            store.symbol_len(),
            store.index_info_len(),
            store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            materialize_global_array_concat_method(&mut store, &host, &global_types, receiver),
            Ok(Some(method_type)),
        );
        assert_eq!(
            (
                store.type_len(),
                store.signature_len(),
                store.symbol_len(),
                store.index_info_len(),
                store.checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn merged_interface_methods_stay_unsupported_outside_default_library_math_random() {
        for (index, source) in [
            "interface Shared { random(): number } declare var Shared: Shared;",
            "interface Shared { max(...values: number[]): number } declare var Shared: Shared;",
            "interface Math { random(): number } declare var Math: Math;",
            "interface Math { random(value: number): number } declare var Math: Math;",
            concat!(
                "interface Number { toFixed(fractionDigits?: number): string } ",
                "interface NumberConstructor {} declare var Number: NumberConstructor;",
            ),
            concat!(
                "interface String { toLowerCase(): string } ",
                "interface StringConstructor {} declare var String: StringConstructor;",
            ),
            concat!(
                "interface Object { toString(): string } ",
                "interface ObjectConstructor {} declare var Object: ObjectConstructor;",
            ),
            concat!(
                "interface Symbol { toString(): string; ",
                "[Symbol.toPrimitive](hint: string): symbol } ",
                "interface SymbolConstructor {} declare var Symbol: SymbolConstructor;",
            ),
            concat!(
                "interface Math { max(...values: number[]): number; random(): number } ",
                "declare var Math: Math;",
            ),
            concat!(
                "interface Math { hypot(...values: number[]): number; random(): number } ",
                "declare var Math: Math;",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = interface_fixture(source, 3_795 + u32::try_from(index).unwrap());
            let host = host(&fixture.parsed, &fixture.bound);
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert!(matches!(
                plan_interface(&fixture.store, &host, fixture.symbol),
                Err(PropertyObjectError::UnsupportedMember {
                    kind: SyntaxKind::MethodSignature,
                    ..
                })
            ));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn computed_symbol_tags_stay_unsupported_outside_default_library_math() {
        for (index, source) in [
            "interface Shared { value: string; readonly [Symbol.toStringTag]: string }",
            concat!(
                "interface Math { random(): number; readonly [Symbol.toStringTag]: string } ",
                "declare var Math: Math;",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = interface_fixture(source, 3_803 + u32::try_from(index).unwrap());
            let host = host(&fixture.parsed, &fixture.bound);
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert!(matches!(
                plan_interface(&fixture.store, &host, fixture.symbol),
                Err(PropertyObjectError::UnsupportedMember {
                    kind: SyntaxKind::ComputedPropertyName,
                    ..
                })
            ));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn poisoned_interface_method_parameter_values_reject_before_publication() {
        let mut fixture =
            interface_fixture("interface Shape { run(value: string): number }", 3_779);
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
        let owner_type = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            fixture.symbol,
            flags,
        )
        .unwrap()
        .unwrap();
        let (string, number) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let method = &plan.methods[0];
        let parameter = method.parameters[0];
        for (node, type_) in [(parameter.type_node, string), (method.return_type, number)] {
            assert!(fixture.store.set_type_node_links(
                node,
                TypeNodeLinks {
                    resolved_type: Some(type_),
                    ..TypeNodeLinks::default()
                },
            ));
        }
        assert!(fixture.store.set_value_symbol_links(
            parameter.symbol,
            ValueSymbolLinks {
                resolved_type: Some(number),
                ..ValueSymbolLinks::default()
            },
        ));
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            publish_interface_method_values(
                &mut fixture.store,
                &plan,
                &[ResolvedCallSignatureTypes {
                    parameter_types: vec![string],
                    return_type: number,
                }],
            ),
            Err(PropertyObjectError::InvalidCachedInterface {
                symbol: fixture.symbol,
                type_: owner_type,
            }),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn forward_interface_method_bases_preserve_matching_rest_contracts() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Derived extends Base { run(...args: any[]): void } ",
                "interface Base { run(...values: any[]): void }",
            ),
            3_767,
        );
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        let base = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Base"))
            .unwrap();
        fixture.store.merge_global_symbol(globals, base).unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();

        assert_eq!(plan.methods.len(), 1);
        assert_eq!(plan.methods[0].flags, SignatureFlags::HAS_REST_PARAMETER);
        assert!(plan.heritage.is_some());
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn unsupported_interface_method_shapes_do_not_publish_semantic_state() {
        for (index, source) in [
            "interface Shape { run(...args: number): void }",
            "interface Shape { run?(...args: any[]): void }",
            "interface Shape { run(...args: any[]) }",
        ]
        .into_iter()
        .enumerate()
        {
            let fixture = interface_fixture(source, 3_770 + u32::try_from(index).unwrap());
            let host = host(&fixture.parsed, &fixture.bound);
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert!(matches!(
                plan_interface(&fixture.store, &host, fixture.symbol),
                Err(PropertyObjectError::UnsupportedMember {
                    kind: SyntaxKind::MethodSignature,
                    ..
                })
            ));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn unresolved_jsx_element_shells_have_an_empty_authenticated_type_graph() {
        for (index, source) in [
            "declare namespace JSX { interface Element {} }",
            "declare namespace JSX { interface Element extends Base {} } interface Base {}",
        ]
        .into_iter()
        .enumerate()
        {
            let mut fixture = interface_fixture(source, 3_775 + u32::try_from(index).unwrap());
            let host = host(&fixture.parsed, &fixture.bound);
            let flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
            let type_ = get_declared_class_interface_or_type_parameter(
                &mut fixture.store,
                &host,
                fixture.symbol,
                flags,
            )
            .unwrap()
            .unwrap();

            assert_eq!(
                validate_resolved_declared_property_object(&fixture.store, type_),
                DeclaredPropertyObjectValidation::NotDeclared,
            );
            assert!(matches!(
                validate_resolved_declared_property_type_graph(&fixture.store, type_),
                DeclaredPropertyTypeGraphValidation::Traversable(property_types)
                    if property_types.is_empty()
            ));

            assert!(
                fixture
                    .store
                    .set_interface_base_resolution(type_, true, None, None)
            );
            assert!(matches!(
                validate_resolved_declared_property_type_graph(&fixture.store, type_),
                DeclaredPropertyTypeGraphValidation::Malformed
            ));
        }
    }

    #[test]
    fn transitive_interface_property_plans_keep_declaration_ownership() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Base { inherited: string } ",
                "interface Middle extends Base { middle: number } ",
                "interface Derived extends Middle { own: boolean }",
            ),
            3_722,
        );
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let middle = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Middle"))
            .unwrap();
        let derived = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Derived"))
            .unwrap();
        fixture.store.merge_global_symbol(globals, middle).unwrap();
        fixture.store.merge_global_symbol(globals, derived).unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let plan = plan_interface(&fixture.store, &host, derived).unwrap();

        assert_eq!(plan.properties.len(), 1);
        assert_eq!(plan.properties[0].name, "own");
        assert_eq!(
            plan.heritage
                .as_ref()
                .and_then(|heritage| heritage.bases.first())
                .map(|base| base.symbol),
            Some(middle),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
        assert_eq!(plan_interface(&fixture.store, &host, derived), Ok(plan));
    }

    #[test]
    fn transitive_interface_property_conflicts_fail_before_publication() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Base { value: string } ",
                "interface Middle extends Base {} ",
                "interface Derived extends Middle { value: number }",
            ),
            3_723,
        );
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        for name in ["Middle", "Derived"] {
            let symbol = fixture
                .store
                .symbol_table(locals)
                .and_then(|locals| locals.get_source(name))
                .unwrap();
            fixture.store.merge_global_symbol(globals, symbol).unwrap();
        }
        let derived = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Derived"))
            .unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert!(matches!(
            plan_interface(&fixture.store, &host, derived),
            Err(PropertyObjectError::UnsupportedMember {
                kind: SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature,
                ..
            })
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn mixed_call_and_construct_signatures_publish_partitioned_cold_and_warm_members() {
        for (source, type_literal, construct_first, file) in [
            (
                concat!(
                    "interface Mixed { ",
                    "(value: number): string; ",
                    "new(value: string): number; ",
                    "(value: string): number; ",
                    "new(value: number): string ",
                    "}",
                ),
                false,
                false,
                3_716,
            ),
            (
                concat!(
                    "interface Mixed { ",
                    "new(value: string): number; ",
                    "(value: number): string; ",
                    "new(value: number): string; ",
                    "(value: string): number ",
                    "}",
                ),
                false,
                true,
                3_717,
            ),
            (
                concat!(
                    "interface Owner {} type Mixed = { ",
                    "(value: number): string; ",
                    "new(value: string): number; ",
                    "(value: string): number; ",
                    "new(value: number): string ",
                    "};",
                ),
                true,
                false,
                3_718,
            ),
            (
                concat!(
                    "interface Owner {} type Mixed = { ",
                    "new(value: string): number; ",
                    "(value: number): string; ",
                    "new(value: number): string; ",
                    "(value: string): number ",
                    "};",
                ),
                true,
                true,
                3_719,
            ),
        ] {
            let mut fixture = interface_fixture(source, file);
            let host = host(&fixture.parsed, &fixture.bound);
            let before = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            let (plan, owner) = if type_literal {
                let literal = fixture
                    .parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        (record.kind == SyntaxKind::TypeLiteral).then_some(NodeRef::new(
                            fixture.parsed.arena.id(),
                            fixture.file,
                            node,
                        ))
                    })
                    .expect("the fixture contains a mixed type literal");
                let alias =
                    fixture
                        .parsed
                        .arena
                        .iter()
                        .find_map(|(node, record)| {
                            (record.kind == SyntaxKind::TypeAliasDeclaration).then_some(
                                NodeRef::new(fixture.parsed.arena.id(), fixture.file, node),
                            )
                        })
                        .and_then(|declaration| fixture.bound.symbol(declaration))
                        .expect("the fixture contains a bound mixed alias");
                (
                    plan_type_literal(&fixture.store, &host, literal, Some(alias)).unwrap(),
                    alias,
                )
            } else {
                (
                    plan_interface(&fixture.store, &host, fixture.symbol).unwrap(),
                    fixture.symbol,
                )
            };
            assert_eq!(
                plan.call_signatures
                    .iter()
                    .map(PlannedCallSignature::is_construct)
                    .collect::<Vec<_>>(),
                if construct_first {
                    vec![true, false, true, false]
                } else {
                    vec![false, true, false, true]
                },
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );

            let members = fixture.store.symbol_table(plan.members.unwrap()).unwrap();
            for construct in [false, true] {
                let expected = plan
                    .call_signatures
                    .iter()
                    .filter(|signature| signature.is_construct() == construct)
                    .collect::<Vec<_>>();
                let name = if construct {
                    InternalSymbolName::New
                } else {
                    InternalSymbolName::Call
                };
                let symbol = members.get(name.as_ref()).unwrap();
                let declarations = expected
                    .iter()
                    .map(|signature| signature.declaration)
                    .collect::<Vec<_>>();
                assert!(expected.iter().all(|signature| signature.symbol == symbol));
                assert_eq!(
                    fixture.store.symbol(symbol).unwrap().declarations(),
                    Some(declarations.as_slice()),
                );
            }

            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let type_ = CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(owner)
            .unwrap();
            let structured = match fixture.store.type_payload(type_).unwrap().data() {
                TypeData::Interface(interface) => {
                    assert_eq!(
                        interface.declared_call_signatures.as_ref().map(Vec::len),
                        Some(2),
                    );
                    assert_eq!(
                        interface
                            .declared_construct_signatures
                            .as_ref()
                            .map(Vec::len),
                        Some(2),
                    );
                    &interface.reference.object.structured
                }
                TypeData::Object(object) => &object.structured,
                _ => panic!("mixed signatures must retain their declared object identity"),
            };
            assert_eq!(structured.call_signature_count, 2);
            let [first_call, second_call, first_construct, second_construct] =
                structured.signatures.as_deref().unwrap()
            else {
                panic!("mixed signatures must publish calls before constructors")
            };
            let signatures = [
                *first_call,
                *second_call,
                *first_construct,
                *second_construct,
            ];
            if let TypeData::Interface(interface) =
                fixture.store.type_payload(type_).unwrap().data()
            {
                assert_eq!(
                    interface.declared_call_signatures.as_deref(),
                    Some(&signatures[..2]),
                );
                assert_eq!(
                    interface.declared_construct_signatures.as_deref(),
                    Some(&signatures[2..]),
                );
            }

            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            let number = bootstrap.number_type;
            let string = bootstrap.string_type;
            let expected = [
                (false, number, string),
                (false, string, number),
                (true, string, number),
                (true, number, string),
            ];
            for (signature, (construct, parameter_type, return_type)) in
                signatures.iter().zip(expected)
            {
                let record = fixture.store.signature(*signature).unwrap();
                assert_eq!(
                    record.flags().contains(SignatureFlags::CONSTRUCT),
                    construct,
                );
                assert_eq!(record.resolved_return_type(), Some(return_type));
                assert_eq!(
                    fixture.store.callable_signature_parameter_types(*signature),
                    Some([parameter_type].as_slice()),
                );
            }
            assert_eq!(
                validate_stored_declared_call_set(&fixture.store, type_),
                StoredDeclaredCallSetValidation::Valid(vec![
                    number, string, string, number, string, number, number, string,
                ]),
            );
            let crate::semantic::callable_sets::StoredCallableSetValidation::Valid {
                projection,
                ..
            } = crate::semantic::callable_sets::validate_stored_callable_set(&fixture.store, type_)
            else {
                panic!("mixed signatures must authenticate both callable families")
            };
            assert_eq!(
                projection
                    .call_signatures
                    .iter()
                    .map(|callable| callable.signature)
                    .collect::<Vec<_>>()
                    .as_slice(),
                &signatures[..2],
            );
            assert_eq!(projection.construct_signatures.as_ref(), &signatures[2..]);

            let warm = (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(
                CanonicalTypeQuery::new(
                    &mut fixture.store,
                    &host,
                    CanonicalCheckerOptions::default(),
                    &mut diagnostics,
                )
                .unwrap()
                .get_declared_type_of_symbol(owner),
                Ok(type_),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.signature_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
            assert!(diagnostics.is_empty(), "{source}");
        }
    }

    #[test]
    fn mixed_signature_cache_rejects_swapped_call_and_construct_families() {
        let mut fixture = interface_fixture(
            "interface Mixed { new(value: string): number; (value: number): string }",
            3_898,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let [call, construct] = fixture
            .store
            .type_payload(type_)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_deref()
            .unwrap()
        else {
            panic!("the interface must publish one call and one constructor")
        };
        let (call, construct) = (*call, *construct);

        assert!(fixture.store.set_structured_type_members(
            type_,
            plan.members,
            None,
            Some(vec![construct]),
            Some(vec![call]),
            None,
        ));
        assert_eq!(
            validate_stored_declared_call_set(&fixture.store, type_),
            StoredDeclaredCallSetValidation::Malformed,
        );
        assert_eq!(
            interface_state(&fixture.store, &plan, type_),
            Err(PropertyObjectError::InvalidCachedInterface {
                symbol: fixture.symbol,
                type_,
            }),
        );
    }

    #[test]
    fn forged_mixed_signature_ownership_fails_before_publication() {
        let mut fixture = interface_fixture(
            "interface Mixed { (value: number): string; new(value: string): number }",
            3_899,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let mut plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
        let type_ = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            fixture.symbol,
            flags,
        )
        .unwrap()
        .unwrap();
        let state = interface_state(&fixture.store, &plan, type_).unwrap();
        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let resolved = [
            ResolvedCallSignatureTypes {
                parameter_types: vec![bootstrap.number_type],
                return_type: bootstrap.string_type,
            },
            ResolvedCallSignatureTypes {
                parameter_types: vec![bootstrap.string_type],
                return_type: bootstrap.number_type,
            },
        ];
        plan.call_signatures[1].symbol = plan.call_signatures[0].symbol;
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            publish_declared_members(&mut fixture.store, &plan, state, &[], &[], &resolved),
            Err(PropertyObjectError::InvalidCachedInterface {
                symbol: fixture.symbol,
                type_,
            }),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn invalid_construct_publication_plans_are_rejected_atomically() {
        let mut fixture = interface_fixture(
            "interface Constructor { new(value: number): string; new(value: string): number }",
            3_720,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
        let type_ = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            fixture.symbol,
            flags,
        )
        .unwrap()
        .unwrap();
        let state = interface_state(&fixture.store, &plan, type_).unwrap();
        assert_eq!(state, PropertyObjectState::Shell(type_));

        let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
        let resolved = [
            ResolvedCallSignatureTypes {
                parameter_types: vec![bootstrap.number_type],
                return_type: bootstrap.string_type,
            },
            ResolvedCallSignatureTypes {
                parameter_types: vec![bootstrap.string_type],
                return_type: bootstrap.number_type,
            },
        ];
        let mut mixed_plan = plan.clone();
        mixed_plan.call_signatures[1].flags = SignatureFlags::NONE;
        let mut missing_plan = plan.clone();
        missing_plan.call_signatures.clear();

        let snapshot = |store: &CanonicalTypeMapperStore| {
            let record = store.type_payload(type_).unwrap();
            let TypeData::Interface(interface) = record.data() else {
                panic!("constructor publication must preserve its interface shell")
            };
            (
                record.object_flags(),
                interface.clone(),
                store.signature_len(),
                store.checker_link_allocated_lengths(),
                plan.call_signatures
                    .iter()
                    .map(|signature| {
                        (
                            store.signature_links(signature.declaration).cloned(),
                            signature
                                .parameters
                                .iter()
                                .map(|parameter| {
                                    store.value_symbol_links(parameter.symbol).cloned()
                                })
                                .collect::<Vec<_>>(),
                        )
                    })
                    .collect::<Vec<_>>(),
            )
        };
        for (invalid_plan, call_types) in [
            (&mixed_plan, resolved.as_slice()),
            (&missing_plan, &[] as &[ResolvedCallSignatureTypes]),
        ] {
            let before = snapshot(&fixture.store);
            assert_eq!(
                publish_declared_members(
                    &mut fixture.store,
                    invalid_plan,
                    state,
                    &[],
                    &[],
                    call_types,
                ),
                Err(PropertyObjectError::InvalidCachedInterface {
                    symbol: fixture.symbol,
                    type_,
                }),
            );
            assert_eq!(snapshot(&fixture.store), before);
        }
    }

    #[test]
    fn conditional_constructor_return_inference_retains_its_declared_signature() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Owner {} ",
                "type ExtractReturn<T> = T extends { new(): infer R } ? R : never;",
            ),
            3_714,
        );
        let alias = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeAliasDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .and_then(|declaration| fixture.bound.symbol(declaration))
            .expect("the fixture contains the conditional alias");
        let host = host(&fixture.parsed, &fixture.bound);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let conditional_type = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(alias)
        .unwrap();
        let TypeData::Conditional(conditional) =
            fixture.store.type_payload(conditional_type).unwrap().data()
        else {
            panic!("a generic constructor inference alias must retain its conditional type")
        };
        let root = fixture.store.conditional_root(conditional.root).unwrap();
        let [inferred] = root.infer_type_parameters().unwrap() else {
            panic!("the constructor return must own one infer parameter")
        };
        let inferred = *inferred;
        let extends_type = root.extends_type();
        let TypeData::Object(object) = fixture.store.type_payload(extends_type).unwrap().data()
        else {
            panic!("the conditional extends operand must remain a constructor object")
        };
        assert_eq!(object.structured.call_signature_count, 0);
        let [signature] = object.structured.signatures.as_deref().unwrap() else {
            panic!("the constructor object must expose one construct signature")
        };
        let signature = fixture.store.signature(*signature).unwrap();
        assert!(signature.flags().contains(SignatureFlags::CONSTRUCT));
        assert_eq!(signature.resolved_return_type(), Some(inferred));
        assert_eq!(
            validate_stored_declared_call_set(&fixture.store, extends_type),
            StoredDeclaredCallSetValidation::Valid(vec![inferred]),
        );

        let warm = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(alias),
            Ok(conditional_type),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
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
    fn merged_interface_properties_publish_once_in_declaration_order() {
        let mut fixture = interface_fixture(
            "interface Item { first: string; shared: number } \
             interface Item { shared: number; second: boolean }",
            3_706,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        assert_eq!(plan.declarations.len(), 2);
        assert_eq!(
            plan.properties
                .iter()
                .map(|property| property.name.as_str())
                .collect::<Vec<_>>(),
            ["first", "shared", "second"]
        );
        assert_eq!(
            fixture
                .store
                .symbol(plan.properties[1].symbol)
                .and_then(ts_binder::semantic::Symbol::declarations)
                .map(<[NodeRef]>::len),
            Some(2)
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        assert_eq!(
            validate_resolved_declared_property_object(&fixture.store, type_),
            DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::Interface)
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(fixture.symbol),
            Ok(type_)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn reopened_interfaces_merge_repeated_bases_after_their_own_properties() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Derived extends Base { first: string } ",
                "interface Derived extends Base { second: number } ",
                "interface Base { inherited: boolean }",
            ),
            3_792,
        );
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        let base = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Base"))
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        fixture.store.merge_global_symbol(globals, base).unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let heritage = plan.heritage.as_ref().unwrap();

        assert_eq!(plan.declarations.len(), 2);
        assert_eq!(heritage.bases.len(), 1);
        assert_eq!(heritage.bases[0].symbol, base);
        assert_eq!(
            plan.properties
                .iter()
                .map(|property| property.name.as_str())
                .collect::<Vec<_>>(),
            ["first", "second"],
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let TypeData::Interface(interface) = fixture.store.type_payload(type_).unwrap().data()
        else {
            panic!("the reopened declaration must retain its interface identity")
        };
        let properties = interface
            .reference
            .object
            .structured
            .properties
            .as_deref()
            .unwrap();
        assert_eq!(
            properties
                .iter()
                .map(|property| fixture.store.symbol(*property).unwrap().name().as_utf8())
                .collect::<Vec<_>>(),
            [Some("first"), Some("second"), Some("inherited")],
        );
        assert_eq!(
            fixture.store.get_parent_of_symbol(properties[2]),
            Some(base),
        );

        let warm = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(fixture.symbol),
            Ok(type_),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn reopened_interface_diamonds_keep_unique_inherited_symbols_in_source_order() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Derived extends Left { own: string } ",
                "interface Derived extends Right { extra: number } ",
                "interface Left extends Root { left: string } ",
                "interface Right extends Root { right: boolean } ",
                "interface Root { shared: string }",
            ),
            3_794,
        );
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        for name in ["Left", "Right", "Root"] {
            let base = fixture
                .store
                .symbol_table(locals)
                .and_then(|locals| locals.get_source(name))
                .unwrap();
            fixture.store.merge_global_symbol(globals, base).unwrap();
        }
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        assert_eq!(plan.heritage.as_ref().unwrap().bases.len(), 2);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let properties = fixture
            .store
            .type_payload(type_)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.properties.as_deref())
            .unwrap();
        assert_eq!(
            properties
                .iter()
                .map(|property| fixture.store.symbol(*property).unwrap().name().as_utf8())
                .collect::<Vec<_>>(),
            [
                Some("own"),
                Some("extra"),
                Some("left"),
                Some("shared"),
                Some("right"),
            ],
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn merged_generic_interfaces_publish_once_and_preserve_declaration_order() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Box<T> { first: T; shared: string } ",
                "interface Box<T> { shared: string; second: T }",
            ),
            3_710,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();
        assert_eq!(plan.declarations.len(), 2);
        assert_eq!(
            plan.properties
                .iter()
                .map(|property| property.name.as_str())
                .collect::<Vec<_>>(),
            ["first", "shared", "second"],
        );
        assert_eq!(
            fixture
                .store
                .symbol(plan.properties[1].symbol)
                .and_then(ts_binder::semantic::Symbol::declarations)
                .map(<[NodeRef]>::len),
            Some(2),
        );

        let flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
        let target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            fixture.symbol,
            flags,
        )
        .unwrap()
        .unwrap();
        let parameter = match fixture.store.type_payload(target).unwrap().data() {
            TypeData::Interface(interface) => interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .unwrap()[0],
            _ => panic!("merged declarations must produce one generic interface target"),
        };
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let property_types = [parameter, string, parameter];
        assert!(fixture.store.publish_interface_no_base_resolution(target));

        let mut invalid_plan = plan.clone();
        invalid_plan.declarations.reverse();
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
            }),
        );
        assert_eq!(state(&fixture.store, &plan, target), before);

        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &property_types,
            ),
            Ok(target),
        );
        let warm = state(&fixture.store, &plan, target);
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &property_types,
            ),
            Ok(target),
        );
        assert_eq!(state(&fixture.store, &plan, target), warm);

        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let reference = fixture
            .store
            .create_direct_generic_reference_type(target, &[number])
            .unwrap();
        for (name, expected) in [("first", number), ("shared", string), ("second", number)] {
            let property = fixture
                .store
                .resolve_generic_interface_property(reference, name, None)
                .unwrap()
                .unwrap();
            assert_eq!(property.type_id(), expected);
        }
    }

    #[test]
    fn reopened_generic_indexes_keep_one_binder_symbol_and_substitute_values() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Dictionary<T> { readonly [index: number]: T; fixed: T } ",
                "interface Dictionary<T> { [name: string]: T }",
            ),
            3_782,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let [numeric, text] = plan.indexes.as_slice() else {
            panic!("reopened generic declarations must preserve both index signatures")
        };
        assert_eq!(numeric.symbol, text.symbol);
        assert_eq!(
            fixture
                .store
                .symbol(numeric.symbol)
                .and_then(ts_binder::semantic::Symbol::declarations),
            Some([numeric.declaration, text.declaration].as_slice()),
        );
        assert!(numeric.readonly);
        assert!(!text.readonly);

        let flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
        let target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            fixture.symbol,
            flags,
        )
        .unwrap()
        .unwrap();
        let parameter = match fixture.store.type_payload(target).unwrap().data() {
            TypeData::Interface(interface) => interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .unwrap()[0],
            _ => panic!("Dictionary must retain its generic target"),
        };
        assert!(fixture.store.publish_interface_no_base_resolution(target));
        let before = (
            state(&fixture.store, &plan, target),
            fixture.store.index_info_len(),
        );
        assert!(fixture.store.set_symbol_flags(
            numeric.symbol,
            SymbolFlags::PROPERTY,
            CheckFlags::NONE,
        ));
        assert!(matches!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter],
            ),
            Err(PropertyObjectError::InvalidCachedInterface { .. }),
        ));
        assert_eq!(fixture.store.index_info_len(), before.1);
        assert!(fixture.store.set_symbol_flags(
            numeric.symbol,
            SymbolFlags::SIGNATURE,
            CheckFlags::NONE,
        ));
        assert_eq!(state(&fixture.store, &plan, target), before.0);

        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter],
            ),
            Ok(target),
        );
        let (declared_members, declared_indexes) =
            match fixture.store.type_payload(target).unwrap().data() {
                TypeData::Interface(interface) => (
                    interface.declared_members.unwrap(),
                    interface.declared_index_infos.as_ref().unwrap().clone(),
                ),
                _ => panic!("Dictionary must retain its published interface target"),
            };
        assert_eq!(
            fixture
                .store
                .symbol_table(declared_members)
                .and_then(|members| members.get(InternalSymbolName::Index.as_ref())),
            None,
        );
        for (index, planned) in declared_indexes.iter().zip(&plan.indexes) {
            let info = fixture.store.index_info(*index).unwrap();
            assert_eq!(info.value_type(), parameter);
            assert_eq!(info.declaration(), Some(planned.declaration));
            assert_eq!(info.is_readonly(), planned.readonly);
        }

        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let reference = fixture
            .store
            .create_direct_generic_reference_type(target, &[string])
            .unwrap();
        let members = fixture
            .store
            .resolve_generic_interface_members(reference, None)
            .unwrap();
        assert_eq!(members.properties().len(), 1);
        let indexes = fixture
            .store
            .type_payload(reference)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.index_infos.as_deref())
            .unwrap();
        assert_eq!(indexes.len(), 2);
        for (index, planned) in indexes.iter().zip(&plan.indexes) {
            let info = fixture.store.index_info(*index).unwrap();
            assert_eq!(info.value_type(), string);
            assert_eq!(info.declaration(), Some(planned.declaration));
            assert_eq!(info.is_readonly(), planned.readonly);
        }
        let warm = (
            fixture.store.mapper_len(),
            fixture.store.symbol_len(),
            fixture.store.index_info_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            fixture
                .store
                .resolve_generic_interface_members(reference, None),
            Ok(members),
        );
        assert_eq!(
            (
                fixture.store.mapper_len(),
                fixture.store.symbol_len(),
                fixture.store.index_info_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn generic_react_style_interfaces_keep_methods_bases_and_string_indexes() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Mixin<P, S> {} ",
                "interface ComponentSpec<P, S> extends Mixin<P, S> { ",
                "render(): P; [propertyName: string]: any; ",
                "}",
            ),
            3_783,
        );
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        let component = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("ComponentSpec"))
            .unwrap();
        fixture
            .store
            .merge_global_symbol(globals, component)
            .unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let base_plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let base_flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
        let base = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            fixture.symbol,
            base_flags,
        )
        .unwrap()
        .unwrap();
        assert!(fixture.store.publish_interface_no_base_resolution(base));
        assert_eq!(
            publish_generic_interface_declared_members(&mut fixture.store, &base_plan, base, &[]),
            Ok(base),
        );

        let plan = plan_generic_interface(&fixture.store, &host, component).unwrap();
        assert_eq!(plan.methods.len(), 1);
        assert_eq!(plan.indexes.len(), 1);
        let component_flags = fixture.store.symbol(component).unwrap().flags();
        let target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            component,
            component_flags,
        )
        .unwrap()
        .unwrap();
        let parameters = match fixture.store.type_payload(target).unwrap().data() {
            TypeData::Interface(interface) => interface
                .reference
                .resolved_type_arguments
                .as_ref()
                .unwrap()
                .clone(),
            _ => panic!("ComponentSpec must retain its two generic parameters"),
        };
        let base_reference = fixture
            .store
            .create_direct_generic_reference_type(base, &parameters)
            .unwrap();
        assert!(fixture.store.set_interface_base_resolution(
            target,
            true,
            None,
            Some(vec![base_reference]),
        ));
        assert!(fixture.store.set_type_node_links(
            plan.methods[0].return_type,
            TypeNodeLinks {
                resolved_type: Some(parameters[0]),
                ..TypeNodeLinks::default()
            },
        ));
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameters[0]],
            ),
            Ok(target),
        );
        let declared_index = match fixture.store.type_payload(target).unwrap().data() {
            TypeData::Interface(interface) => interface.declared_index_infos.as_ref().unwrap()[0],
            _ => panic!("ComponentSpec must retain its declared index"),
        };
        let (string, number, any) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.any_type,
            )
        };
        let index = fixture.store.index_info(declared_index).unwrap();
        assert_eq!(index.key_type(), string);
        assert_eq!(index.value_type(), any);

        let reference = fixture
            .store
            .create_direct_generic_reference_type(target, &[string, number])
            .unwrap();
        let members = fixture
            .store
            .resolve_generic_interface_members(reference, None)
            .unwrap();
        assert_eq!(members.properties().len(), 1);
        let [index] = fixture
            .store
            .type_payload(reference)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.index_infos.as_deref())
            .unwrap()
        else {
            panic!("the string index must survive generic inheritance")
        };
        assert_eq!(*index, declared_index);
        let render = fixture
            .store
            .resolve_generic_interface_property(reference, "render", None)
            .unwrap()
            .unwrap()
            .type_id();
        let [signature] = fixture
            .store
            .type_payload(render)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .unwrap()
        else {
            panic!("render must retain its instantiated source signature")
        };
        assert_eq!(
            fixture
                .store
                .signature(*signature)
                .and_then(super::super::signatures::Signature::resolved_return_type),
            Some(string),
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Verify overloads, indexes, defaults, and fresh parameters together.
    fn generic_method_overloads_and_indexes_instantiate_with_fresh_signature_parameters() {
        let mut fixture = global_array_augmentation_fixture(
            concat!(
                "interface Array<T> { (): any[]; } ",
                "interface Contract<Outer> { ",
                "map<Value extends Outer = never>(value: Value): Outer; ",
                "map<Value>(...values: Value[]): Outer; ",
                "readonly [index: number]: Outer; ",
                "}",
            ),
            3_893,
        );
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let locals = fixture
            .source_bound
            .locals(fixture.source_bound.source_file())
            .unwrap();
        let contract = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Contract"))
            .unwrap();
        fixture
            .store
            .merge_global_symbol(globals, contract)
            .unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&fixture.library.arena, &fixture.library_bound),
                (&fixture.source.arena, &fixture.source_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let plan = plan_generic_interface(&fixture.store, &host, contract).unwrap();
        let [first, second] = plan.methods.as_slice() else {
            panic!("the generic method must retain both overload declarations")
        };
        assert_eq!(plan.indexes.len(), 1);
        let flags = fixture.store.symbol(contract).unwrap().flags();
        let target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            contract,
            flags,
        )
        .unwrap()
        .unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let outer = CanonicalTypeQuery::new_with_global_types(
            &mut fixture.store,
            &host,
            &fixture.global_types,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_type_from_type_node(first.return_type)
        .unwrap();
        assert!(fixture.store.publish_interface_no_base_resolution(target));
        assert_eq!(
            publish_generic_interface_declared_members(&mut fixture.store, &plan, target, &[outer],),
            Ok(target),
        );

        let declared_callable = fixture
            .store
            .value_symbol_links(first.symbol)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let original_signatures = fixture
            .store
            .type_payload(declared_callable)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .unwrap()
            .to_vec();
        assert_eq!(original_signatures.len(), 2);
        for (signature, method) in original_signatures.iter().zip([first, second]) {
            let record = fixture.store.signature(*signature).unwrap();
            let [parameter] = record.type_parameters() else {
                panic!("each declaration overload must retain its own type parameter")
            };
            assert_eq!(
                cached_ordinary_type_parameter_owner(&fixture.store, *parameter),
                Some(method.type_parameters[0].symbol),
            );
            assert!(
                fixture
                    .store
                    .callable_signature_parameter_types(*signature)
                    .is_some()
            );
            assert_eq!(
                fixture.store.interface_method_linked_type(*signature),
                Some(declared_callable)
            );
        }

        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let reference = fixture
            .store
            .create_direct_generic_reference_type(target, &[string])
            .unwrap();
        let array_target = crate::semantic::instantiated_members::GenericInterfaceArrayTarget::new(
            fixture.global_types.array_type,
        );
        let members = fixture
            .store
            .resolve_generic_interface_members(reference, Some(array_target))
            .unwrap();
        assert_eq!(members.properties().len(), 1);
        let [index] = fixture
            .store
            .type_payload(reference)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.index_infos.as_deref())
            .unwrap()
        else {
            panic!("the numeric index must survive receiver specialization")
        };
        assert_eq!(
            fixture.store.index_info(*index).unwrap().value_type(),
            string
        );

        let instantiated = fixture
            .store
            .resolve_generic_interface_property(reference, "map", Some(array_target))
            .unwrap()
            .unwrap()
            .type_id();
        let TypeData::Object(object) = fixture.store.type_payload(instantiated).unwrap().data()
        else {
            panic!("an instantiated generic method must retain its callable object")
        };
        let owner_mapper = object.mapper.unwrap();
        let signatures = object.structured.signatures.as_deref().unwrap();
        assert_eq!(signatures.len(), 2);
        for (signature, original) in signatures.iter().zip(&original_signatures) {
            let record = fixture.store.signature(*signature).unwrap();
            let source = fixture.store.signature(*original).unwrap();
            let [fresh] = record.type_parameters() else {
                panic!("each receiver signature must own a fresh method type parameter")
            };
            let [original_parameter] = source.type_parameters() else {
                panic!("each original signature must retain one method type parameter")
            };
            assert_ne!(fresh, original_parameter);
            assert_eq!(record.target(), Some(*original));
            assert_ne!(record.mapper(), Some(owner_mapper));
            assert_eq!(record.resolved_return_type(), Some(string));
            let TypeData::TypeParameter(data) = fixture.store.type_payload(*fresh).unwrap().data()
            else {
                panic!("fresh method parameters must retain their source parameter")
            };
            assert_eq!(data.target, Some(*original_parameter));
            assert_eq!(data.mapper, record.mapper());
        }
        let defaulted = fixture
            .store
            .signature(signatures[0])
            .unwrap()
            .type_parameters()[0];
        let TypeData::TypeParameter(defaulted) =
            fixture.store.type_payload(defaulted).unwrap().data()
        else {
            panic!("the first receiver overload must preserve its default")
        };
        assert_eq!(
            defaulted.resolved_default_type,
            Some(fixture.store.intrinsic_bootstrap().unwrap().never_type),
        );
        assert_eq!(defaulted.constraint, Some(string));
        let rest = fixture.store.signature(signatures[1]).unwrap();
        assert_eq!(rest.flags(), SignatureFlags::HAS_REST_PARAMETER);
        let rest_type = fixture
            .store
            .value_symbol_links(rest.parameters()[0])
            .and_then(|links| links.resolved_type)
            .unwrap();
        let array = fixture
            .store
            .canonical_array_reference(&fixture.global_types, rest_type)
            .unwrap()
            .unwrap();
        assert_eq!(array.element_type, rest.type_parameters()[0]);
        assert!(matches!(
            crate::semantic::callable_sets::validate_stored_callable_set(
                &fixture.store,
                instantiated,
            ),
            crate::semantic::callable_sets::StoredCallableSetValidation::Valid { .. }
        ));

        let warm = (
            fixture.store.type_len(),
            fixture.store.mapper_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_len(),
            fixture.store.index_info_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            fixture
                .store
                .resolve_generic_interface_property(reference, "map", Some(array_target))
                .unwrap()
                .unwrap()
                .type_id(),
            instantiated,
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_len(),
                fixture.store.index_info_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Cold, warm, and poisoned union ownership share one receiver.
    fn instantiated_generic_method_unions_authenticate_fresh_type_parameters() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Contract<Outer> { ",
                "map<Value>(value: Value | Outer): Value | Outer; ",
                "}",
            ),
            3_896,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let method = &plan.methods[0];
        let flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
        let target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            fixture.symbol,
            flags,
        )
        .unwrap()
        .unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let declared_union = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_type_from_type_node(method.return_type)
        .unwrap();
        assert!(fixture.store.publish_interface_no_base_resolution(target));
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[declared_union],
            ),
            Ok(target),
        );

        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let receiver = fixture
            .store
            .create_direct_generic_reference_type(target, &[string])
            .unwrap();
        let callable = fixture
            .store
            .resolve_generic_interface_property(receiver, "map", None)
            .unwrap()
            .unwrap()
            .type_id();
        let [signature] = fixture
            .store
            .type_payload(callable)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .unwrap()
        else {
            panic!("the specialized method must retain one fresh generic signature")
        };
        let signature = *signature;
        let record = fixture.store.signature(signature).unwrap();
        let [fresh] = record.type_parameters() else {
            panic!("the specialized union must retain its fresh method parameter")
        };
        let fresh = *fresh;
        let union = record.resolved_return_type().unwrap();
        let TypeData::Union(data) = fixture.store.type_payload(union).unwrap().data() else {
            panic!("receiver specialization must preserve the method parameter union")
        };
        assert_eq!(data.union.types.len(), 2);
        assert!(data.union.types.contains(&fresh));
        assert!(data.union.types.contains(&string));
        let value = record.parameters()[0];
        assert_eq!(
            fixture
                .store
                .value_symbol_links(value)
                .and_then(|links| links.resolved_type),
            Some(union),
        );
        assert_eq!(fixture.store.validate_union_constituent(fresh), Ok(()));
        assert!(matches!(
            crate::semantic::callable_sets::validate_stored_callable_set(&fixture.store, callable,),
            crate::semantic::callable_sets::StoredCallableSetValidation::Valid { .. }
        ));

        let TypeData::TypeParameter(parameter) = fixture.store.type_payload(fresh).unwrap().data()
        else {
            panic!("the specialized signature must retain its fresh parameter metadata")
        };
        let (constraint, original, mapper, default_type) = (
            parameter.constraint,
            parameter.target,
            parameter.mapper,
            parameter.resolved_default_type,
        );
        assert!(fixture.store.set_type_parameter_resolution(
            fresh,
            constraint,
            original,
            None,
            default_type,
        ));
        assert_eq!(
            fixture.store.validate_union_constituent(fresh),
            Err(
                crate::semantic::bootstrap::LiteralTypeCacheError::UnsupportedUnionConstituent(
                    fresh,
                )
            ),
        );
        assert!(fixture.store.set_type_parameter_resolution(
            fresh,
            constraint,
            original,
            mapper,
            default_type,
        ));
        assert_eq!(fixture.store.validate_union_constituent(fresh), Ok(()));

        let warm = (
            fixture.store.type_len(),
            fixture.store.mapper_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
            fixture
                .store
                .intrinsic_bootstrap()
                .unwrap()
                .union_cache_len(),
        );
        assert_eq!(
            fixture
                .store
                .resolve_generic_interface_property(receiver, "map", None)
                .unwrap()
                .unwrap()
                .type_id(),
            callable,
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
                fixture
                    .store
                    .intrinsic_bootstrap()
                    .unwrap()
                    .union_cache_len(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_interface_heritage_preserves_transformed_base_arguments_and_members() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Base<First, Second> { first: First; second: Second; } ",
                "interface Derived<Value> extends Base<Value, string> { own: Value; }",
            ),
            3_900,
        );
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        let derived = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Derived"))
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        fixture.store.merge_global_symbol(globals, derived).unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let base_plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let base_flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
        let base = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            fixture.symbol,
            base_flags,
        )
        .unwrap()
        .unwrap();
        let base_arguments = validate_direct_generic_reference(&fixture.store, base)
            .unwrap()
            .type_arguments;
        assert!(fixture.store.publish_interface_no_base_resolution(base));
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &base_plan,
                base,
                &base_arguments,
            ),
            Ok(base),
        );

        let plan = plan_generic_interface(&fixture.store, &host, derived).unwrap();
        let flags = fixture.store.symbol(derived).unwrap().flags();
        let target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            derived,
            flags,
        )
        .unwrap()
        .unwrap();
        let value = validate_direct_generic_reference(&fixture.store, target)
            .unwrap()
            .type_arguments[0];
        let heritage = plan.heritage.as_ref().unwrap();
        let [base_plan] = heritage.bases.as_slice() else {
            panic!("the derived interface must retain one transformed generic base")
        };
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let arguments = base_plan
            .type_arguments
            .iter()
            .map(|annotation| {
                CanonicalTypeQuery::new(
                    &mut fixture.store,
                    &host,
                    CanonicalCheckerOptions::default(),
                    &mut diagnostics,
                )
                .unwrap()
                .get_type_from_type_node(*annotation)
                .unwrap()
            })
            .collect::<Vec<_>>();
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(arguments, [value, string]);
        let inherited = fixture
            .store
            .create_direct_generic_reference_type(base, &arguments)
            .unwrap();
        assert!(fixture.store.set_interface_base_resolution(
            target,
            true,
            None,
            Some(vec![inherited]),
        ));

        assert_eq!(
            publish_generic_interface_declared_members(&mut fixture.store, &plan, target, &[value],),
            Ok(target),
        );
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let receiver = fixture
            .store
            .create_direct_generic_reference_type(target, &[number])
            .unwrap();
        assert_eq!(
            fixture
                .store
                .resolve_generic_interface_property(receiver, "first", None)
                .unwrap()
                .unwrap()
                .type_id(),
            number,
        );
        assert_eq!(
            fixture
                .store
                .resolve_generic_interface_property(receiver, "second", None)
                .unwrap()
                .unwrap()
                .type_id(),
            string,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One namespace proves inherited ordering, warm identity, and cache poison.
    fn generic_react_class_attributes_inherit_authenticated_nongeneric_members() {
        let mut fixture = interface_fixture(
            concat!(
                "declare namespace React { ",
                "interface ClassAttributes<T> extends Attributes { ref: T; } ",
                "interface Attributes { key: string; } ",
                "}",
            ),
            3_914,
        );
        let namespace = fixture.store.get_parent_of_symbol(fixture.symbol).unwrap();
        let attributes = fixture
            .store
            .symbol(namespace)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| fixture.store.symbol_table(exports))
            .and_then(|exports| exports.get_source("Attributes"))
            .unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let [base] = plan.heritage.as_ref().unwrap().bases.as_slice() else {
            panic!("ClassAttributes must retain its one nongeneric Attributes base")
        };
        assert_eq!(base.symbol, attributes);
        assert!(base.type_arguments.is_empty());
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let base_type = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(attributes)
        .unwrap();
        assert_eq!(
            validate_resolved_declared_property_object(&fixture.store, base_type),
            DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::Interface),
        );
        let flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
        let target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            fixture.symbol,
            flags,
        )
        .unwrap()
        .unwrap();
        let parameter = validate_direct_generic_reference(&fixture.store, target)
            .unwrap()
            .type_arguments[0];
        assert!(fixture.store.set_interface_base_resolution(
            target,
            true,
            None,
            Some(vec![base_type]),
        ));
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter],
            ),
            Ok(target),
        );

        let (string, number) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let receiver = fixture
            .store
            .create_direct_generic_reference_type(target, &[number])
            .unwrap();
        let members = fixture
            .store
            .resolve_generic_interface_members(receiver, None)
            .unwrap();
        assert_eq!(
            members
                .properties()
                .iter()
                .map(|property| fixture.store.symbol(*property).unwrap().name().as_utf8())
                .collect::<Vec<_>>(),
            [Some("ref"), Some("key")],
        );
        for (name, expected) in [("ref", number), ("key", string)] {
            assert_eq!(
                fixture
                    .store
                    .resolve_generic_interface_property(receiver, name, None)
                    .unwrap()
                    .unwrap()
                    .type_id(),
                expected,
            );
        }

        let warm = state(&fixture.store, &plan, target);
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter],
            ),
            Ok(target),
        );
        assert_eq!(state(&fixture.store, &plan, target), warm);

        let exports = fixture.store.symbol(namespace).unwrap().exports().unwrap();
        assert_eq!(
            fixture
                .store
                .insert_symbol(exports, EscapedName::source("Attributes"), fixture.symbol,),
            Some(Some(attributes)),
        );
        assert_eq!(
            validate_resolved_declared_property_object(&fixture.store, base_type),
            DeclaredPropertyObjectValidation::NotDeclared,
        );
        let poisoned = state(&fixture.store, &plan, target);
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter],
            ),
            Err(PropertyObjectError::InvalidCachedInterface {
                symbol: fixture.symbol,
                type_: target,
            }),
        );
        assert_eq!(state(&fixture.store, &plan, target), poisoned);
        assert_eq!(
            fixture
                .store
                .insert_symbol(exports, EscapedName::source("Attributes"), attributes),
            Some(Some(fixture.symbol)),
        );
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter],
            ),
            Ok(target),
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Merged React ownership, inherited members, replay, and export poison share one proof.
    fn generic_react_class_attributes_accept_authenticated_transient_merged_bases() {
        let mut fixture = interface_fixture(
            concat!(
                "declare namespace React { ",
                "interface ClassAttributes<T> extends Attributes { ref: T; } ",
                "interface Attributes { key: string; } ",
                "interface Attributes { role: string; } ",
                "}",
            ),
            3_917,
        );
        let namespace = fixture.store.get_parent_of_symbol(fixture.symbol).unwrap();
        let exports = fixture.store.symbol(namespace).unwrap().exports().unwrap();
        let attributes = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("Attributes"))
            .unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let base = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(attributes)
        .unwrap();
        assert_eq!(
            fixture
                .store
                .symbol(attributes)
                .and_then(ts_binder::semantic::Symbol::declarations)
                .map(<[NodeRef]>::len),
            Some(2),
        );
        assert!(fixture.store.set_symbol_flags(
            attributes,
            SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT,
            CheckFlags::NONE,
        ));
        assert!(authenticated_merged_react_declared_property_interface(
            &fixture.store,
            attributes,
        ));
        assert_eq!(
            validate_resolved_declared_property_object(&fixture.store, base),
            DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::Interface),
        );

        let flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
        let target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            fixture.symbol,
            flags,
        )
        .unwrap()
        .unwrap();
        let parameter = validate_direct_generic_reference(&fixture.store, target)
            .unwrap()
            .type_arguments[0];
        assert!(
            fixture
                .store
                .set_interface_base_resolution(target, true, None, Some(vec![base]),)
        );
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter],
            ),
            Ok(target),
        );
        let warm = state(&fixture.store, &plan, target);
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter],
            ),
            Ok(target),
        );
        assert_eq!(state(&fixture.store, &plan, target), warm);

        assert_eq!(
            fixture
                .store
                .insert_symbol(exports, EscapedName::source("Attributes"), fixture.symbol,),
            Some(Some(attributes)),
        );
        assert!(!authenticated_merged_react_declared_property_interface(
            &fixture.store,
            attributes,
        ));
        assert_eq!(
            validate_resolved_declared_property_object(&fixture.store, base),
            DeclaredPropertyObjectValidation::NotDeclared,
        );
        let poisoned = state(&fixture.store, &plan, target);
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter],
            ),
            Err(PropertyObjectError::InvalidCachedInterface {
                symbol: fixture.symbol,
                type_: target,
            }),
        );
        assert_eq!(state(&fixture.store, &plan, target), poisoned);
        assert_eq!(
            fixture
                .store
                .insert_symbol(exports, EscapedName::source("Attributes"), attributes),
            Some(Some(fixture.symbol)),
        );
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter],
            ),
            Ok(target),
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn transient_declared_property_interfaces_require_merged_react_namespace_ownership() {
        for (source, file) in [
            (
                "declare namespace React { interface Attributes { key: string; } }",
                3_918,
            ),
            (
                concat!(
                    "declare namespace Other { ",
                    "interface Attributes { key: string; } ",
                    "interface Attributes { role: string; } ",
                    "}",
                ),
                3_919,
            ),
            (
                concat!(
                    "interface Attributes { key: string; } ",
                    "interface Attributes { role: string; }",
                ),
                3_920,
            ),
        ] {
            let mut fixture = interface_fixture(source, file);
            let host = host(&fixture.parsed, &fixture.bound);
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let target = CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalCheckerOptions::default(),
                &mut diagnostics,
            )
            .unwrap()
            .get_declared_type_of_symbol(fixture.symbol)
            .unwrap();
            assert!(fixture.store.set_symbol_flags(
                fixture.symbol,
                SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT,
                CheckFlags::NONE,
            ));
            let before = (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            assert!(!authenticated_merged_react_declared_property_interface(
                &fixture.store,
                fixture.symbol,
            ));
            assert_eq!(
                validate_resolved_declared_property_object(&fixture.store, target),
                DeclaredPropertyObjectValidation::NotDeclared,
                "{source}",
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.symbol_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
                "{source}",
            );
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Mixed React bases share ordered publication, replay, and cache poison.
    fn generic_react_html_attributes_preserve_mixed_base_order_and_cache_identity() {
        let mut fixture = interface_fixture(
            concat!(
                "declare namespace React { ",
                "interface HTMLAttributes<T> extends AriaAttributes, DOMAttributes<T> ",
                "{ id: T; } ",
                "interface HTMLAttributes<T> { title: boolean; } ",
                "interface AriaAttributes { label: string; shared: string; } ",
                "interface DOMAttributes<T> { target: T; shared: string; } ",
                "}",
            ),
            3_915,
        );
        let namespace = fixture.store.get_parent_of_symbol(fixture.symbol).unwrap();
        let exports = fixture.store.symbol(namespace).unwrap().exports().unwrap();
        let aria = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("AriaAttributes"))
            .unwrap();
        let dom = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("DOMAttributes"))
            .unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();
        assert_eq!(plan.declarations.len(), 2);
        assert_eq!(
            plan.properties
                .iter()
                .map(|property| property.name.as_str())
                .collect::<Vec<_>>(),
            ["id", "title"],
        );
        assert_eq!(
            plan.heritage
                .as_ref()
                .unwrap()
                .bases
                .iter()
                .map(|base| (base.symbol, base.type_arguments.len()))
                .collect::<Vec<_>>(),
            [(aria, 0), (dom, 1)],
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let aria_type = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(aria)
        .unwrap();
        let dom_plan = plan_generic_interface(&fixture.store, &host, dom).unwrap();
        let dom_flags = fixture.store.symbol(dom).unwrap().flags();
        let dom_target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            dom,
            dom_flags,
        )
        .unwrap()
        .unwrap();
        let dom_parameter = validate_direct_generic_reference(&fixture.store, dom_target)
            .unwrap()
            .type_arguments[0];
        let (string, number, boolean) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
            )
        };
        assert!(
            fixture
                .store
                .publish_interface_no_base_resolution(dom_target)
        );
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &dom_plan,
                dom_target,
                &[dom_parameter, string],
            ),
            Ok(dom_target),
        );

        let flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
        let target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            fixture.symbol,
            flags,
        )
        .unwrap()
        .unwrap();
        let parameter = validate_direct_generic_reference(&fixture.store, target)
            .unwrap()
            .type_arguments[0];
        let dom_reference = fixture
            .store
            .create_direct_generic_reference_type(dom_target, &[parameter])
            .unwrap();
        assert!(fixture.store.set_interface_base_resolution(
            target,
            true,
            None,
            Some(vec![dom_reference, aria_type]),
        ));
        let poisoned = state(&fixture.store, &plan, target);
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter, boolean],
            ),
            Err(PropertyObjectError::InvalidCachedInterface {
                symbol: fixture.symbol,
                type_: target,
            }),
        );
        assert_eq!(state(&fixture.store, &plan, target), poisoned);

        assert!(fixture.store.set_interface_base_resolution(
            target,
            true,
            None,
            Some(vec![aria_type, dom_reference]),
        ));
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter, boolean],
            ),
            Ok(target),
        );
        let receiver = fixture
            .store
            .create_direct_generic_reference_type(target, &[number])
            .unwrap();
        let members = fixture
            .store
            .resolve_generic_interface_members(receiver, None)
            .unwrap();
        assert_eq!(
            members
                .properties()
                .iter()
                .map(|property| fixture.store.symbol(*property).unwrap().name().as_utf8())
                .collect::<Vec<_>>(),
            [
                Some("id"),
                Some("title"),
                Some("label"),
                Some("shared"),
                Some("target"),
            ],
        );
        assert_eq!(
            fixture.store.get_parent_of_symbol(members.properties()[3]),
            Some(aria),
        );
        for (name, expected) in [
            ("id", number),
            ("title", boolean),
            ("label", string),
            ("shared", string),
            ("target", number),
        ] {
            assert_eq!(
                fixture
                    .store
                    .resolve_generic_interface_property(receiver, name, None)
                    .unwrap()
                    .unwrap()
                    .type_id(),
                expected,
                "{name}",
            );
        }

        let warm = (
            state(&fixture.store, &plan, target),
            fixture.store.type_len(),
            fixture.store.mapper_len(),
            fixture.store.symbol_len(),
        );
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter, boolean],
            ),
            Ok(target),
        );
        assert_eq!(
            (
                state(&fixture.store, &plan, target),
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.symbol_len(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Nested React base arguments, receiver mapping, and poisoned caches are one proof.
    fn generic_react_elements_specialize_nested_forwarded_interface_base_arguments() {
        let mut fixture = interface_fixture(
            concat!(
                "declare namespace React { ",
                "interface ReactHTMLElement<T> ",
                "extends DetailedReactHTMLElement<AllHTMLAttributes<T>, T> ",
                "{ marker: T; } ",
                "interface DetailedReactHTMLElement<Props, Element> ",
                "{ props: Props; element: Element; } ",
                "interface AllHTMLAttributes<T> { value: T; } ",
                "}",
            ),
            3_916,
        );
        let namespace = fixture.store.get_parent_of_symbol(fixture.symbol).unwrap();
        let exports = fixture.store.symbol(namespace).unwrap().exports().unwrap();
        let detailed = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("DetailedReactHTMLElement"))
            .unwrap();
        let attributes = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("AllHTMLAttributes"))
            .unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let [base] = plan.heritage.as_ref().unwrap().bases.as_slice() else {
            panic!("ReactHTMLElement must preserve its detailed generic base")
        };
        assert_eq!(base.symbol, detailed);
        assert_eq!(base.type_arguments.len(), 2);

        let attributes_plan = plan_generic_interface(&fixture.store, &host, attributes).unwrap();
        let attributes_flags = fixture.store.symbol(attributes).unwrap().flags();
        let attributes_target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            attributes,
            attributes_flags,
        )
        .unwrap()
        .unwrap();
        let attributes_parameter =
            validate_direct_generic_reference(&fixture.store, attributes_target)
                .unwrap()
                .type_arguments[0];
        assert!(
            fixture
                .store
                .publish_interface_no_base_resolution(attributes_target)
        );
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &attributes_plan,
                attributes_target,
                &[attributes_parameter],
            ),
            Ok(attributes_target),
        );

        let detailed_plan = plan_generic_interface(&fixture.store, &host, detailed).unwrap();
        let detailed_flags = fixture.store.symbol(detailed).unwrap().flags();
        let detailed_target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            detailed,
            detailed_flags,
        )
        .unwrap()
        .unwrap();
        let detailed_parameters =
            validate_direct_generic_reference(&fixture.store, detailed_target)
                .unwrap()
                .type_arguments;
        assert!(
            fixture
                .store
                .publish_interface_no_base_resolution(detailed_target)
        );
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &detailed_plan,
                detailed_target,
                &detailed_parameters,
            ),
            Ok(detailed_target),
        );

        let flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
        let target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            fixture.symbol,
            flags,
        )
        .unwrap()
        .unwrap();
        let parameter = validate_direct_generic_reference(&fixture.store, target)
            .unwrap()
            .type_arguments[0];
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let arguments = base
            .type_arguments
            .iter()
            .map(|annotation| {
                CanonicalTypeQuery::new(
                    &mut fixture.store,
                    &host,
                    CanonicalCheckerOptions::default(),
                    &mut diagnostics,
                )
                .unwrap()
                .get_type_from_type_node(*annotation)
                .unwrap()
            })
            .collect::<Vec<_>>();
        let nested = validate_direct_generic_reference(&fixture.store, arguments[0]).unwrap();
        assert_eq!(nested.target, attributes_target);
        assert_eq!(nested.type_arguments, [parameter]);
        assert_eq!(arguments[1], parameter);

        let (string, number) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let wrong_attributes = fixture
            .store
            .create_direct_generic_reference_type(attributes_target, &[string])
            .unwrap();
        let forged = fixture
            .store
            .create_direct_generic_reference_type(detailed_target, &[wrong_attributes, parameter])
            .unwrap();
        assert!(fixture.store.set_interface_base_resolution(
            target,
            true,
            None,
            Some(vec![forged]),
        ));
        let poisoned = state(&fixture.store, &plan, target);
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter],
            ),
            Err(PropertyObjectError::InvalidCachedInterface {
                symbol: fixture.symbol,
                type_: target,
            }),
        );
        assert_eq!(state(&fixture.store, &plan, target), poisoned);

        let inherited = fixture
            .store
            .create_direct_generic_reference_type(detailed_target, &arguments)
            .unwrap();
        assert!(fixture.store.set_interface_base_resolution(
            target,
            true,
            None,
            Some(vec![inherited]),
        ));
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter],
            ),
            Ok(target),
        );
        let receiver = fixture
            .store
            .create_direct_generic_reference_type(target, &[number])
            .unwrap();
        let members = fixture
            .store
            .resolve_generic_interface_members(receiver, None)
            .unwrap();
        assert_eq!(
            members
                .properties()
                .iter()
                .map(|property| fixture.store.symbol(*property).unwrap().name().as_utf8())
                .collect::<Vec<_>>(),
            [Some("marker"), Some("props"), Some("element")],
        );
        let properties = fixture
            .store
            .resolve_generic_interface_property(receiver, "props", None)
            .unwrap()
            .unwrap()
            .type_id();
        let instantiated_attributes =
            validate_direct_generic_reference(&fixture.store, properties).unwrap();
        assert_eq!(instantiated_attributes.target, attributes_target);
        assert_eq!(instantiated_attributes.type_arguments, [number]);
        for name in ["marker", "element"] {
            assert_eq!(
                fixture
                    .store
                    .resolve_generic_interface_property(receiver, name, None)
                    .unwrap()
                    .unwrap()
                    .type_id(),
                number,
            );
        }

        let warm = (
            state(&fixture.store, &plan, target),
            fixture.store.type_len(),
            fixture.store.mapper_len(),
            fixture.store.symbol_len(),
        );
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                target,
                &[parameter],
            ),
            Ok(target),
        );
        assert_eq!(
            (
                state(&fixture.store, &plan, target),
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.symbol_len(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_interface_plans_keep_forwarded_base_arguments_without_publication() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Derived<T> extends Base<T> { own: T } ",
                "interface Base<T> { inherited: T }",
            ),
            3_778,
        );
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        let base = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Base"))
            .unwrap();
        fixture.store.merge_global_symbol(globals, base).unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.signature_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();

        let heritage = plan.heritage.as_ref().unwrap();
        let [base] = heritage.bases.as_slice() else {
            panic!("a generic interface must retain one authenticated direct base")
        };
        assert_eq!(base.kind, DirectInterfaceBaseKind::Interface);
        assert_eq!(base.type_arguments.len(), 1);
        assert_eq!(plan.properties.len(), 1);
        assert_eq!(plan.properties[0].name, "own");
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.signature_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn reopened_generic_interfaces_keep_one_forwarded_base_and_warm_inherited_members() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Derived<T> extends Base<T> { own: T } ",
                "interface Derived<T> extends Base<T> { extra: string } ",
                "interface Base<T> { inherited: T }",
            ),
            3_793,
        );
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        let base = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Base"))
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        fixture.store.merge_global_symbol(globals, base).unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let derived_plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();
        assert_eq!(derived_plan.declarations.len(), 2);
        assert_eq!(derived_plan.heritage.as_ref().unwrap().bases.len(), 1);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let derived = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let base_target = fixture
            .store
            .declared_type_links(base)
            .and_then(|links| links.declared_type)
            .unwrap();
        let base_parameter = validate_direct_generic_reference(&fixture.store, base_target)
            .unwrap()
            .type_arguments[0];
        let derived_parameter = validate_direct_generic_reference(&fixture.store, derived)
            .unwrap()
            .type_arguments[0];
        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let base_plan = plan_generic_interface(&fixture.store, &host, base).unwrap();

        assert!(
            fixture
                .store
                .publish_interface_no_base_resolution(base_target)
        );
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &base_plan,
                base_target,
                &[base_parameter],
            ),
            Ok(base_target),
        );
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &derived_plan,
                derived,
                &[derived_parameter, string],
            ),
            Ok(derived),
        );
        let members = fixture
            .store
            .resolve_generic_interface_members(derived, None)
            .unwrap();
        assert_eq!(
            members
                .properties()
                .iter()
                .map(|property| fixture.store.symbol(*property).unwrap().name().as_utf8())
                .collect::<Vec<_>>(),
            [Some("own"), Some("extra"), Some("inherited")],
        );
        assert_ne!(members.properties()[0], derived_plan.properties[0].symbol);
        assert_eq!(
            fixture
                .store
                .value_symbol_links(members.properties()[0])
                .and_then(|links| links.target),
            Some(derived_plan.properties[0].symbol),
        );
        let number = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let concrete = fixture
            .store
            .create_direct_generic_reference_type(derived, &[number])
            .unwrap();
        assert_eq!(
            fixture
                .store
                .resolve_generic_interface_property(concrete, "inherited", None)
                .unwrap()
                .unwrap()
                .type_id(),
            number,
        );

        let warm = state(&fixture.store, &derived_plan, derived);
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &derived_plan,
                derived,
                &[derived_parameter, string],
            ),
            Ok(derived),
        );
        assert_eq!(state(&fixture.store, &derived_plan, derived), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Merged heritage, generic methods, and warm proxies share one graph.
    fn reopened_generic_interfaces_preserve_generic_methods_and_inherited_member_proxies() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Derived<Outer> extends Base<Outer> { own: Outer } ",
                "interface Derived<Outer> extends Base<Outer> { ",
                "map<Value>(value: Value | Outer): Value | Outer; ",
                "} ",
                "interface Base<Outer> { inherited: Outer }",
            ),
            3_897,
        );
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        let base = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Base"))
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        fixture.store.merge_global_symbol(globals, base).unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();
        let [method] = plan.methods.as_slice() else {
            panic!("the reopened interface must retain its generic method")
        };
        assert_eq!(plan.declarations.len(), 2);
        assert_eq!(plan.heritage.as_ref().unwrap().bases.len(), 1);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let derived = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let base_target = fixture
            .store
            .declared_type_links(base)
            .and_then(|links| links.declared_type)
            .unwrap();
        let base_parameter = validate_direct_generic_reference(&fixture.store, base_target)
            .unwrap()
            .type_arguments[0];
        let derived_parameter = validate_direct_generic_reference(&fixture.store, derived)
            .unwrap()
            .type_arguments[0];
        let base_plan = plan_generic_interface(&fixture.store, &host, base).unwrap();
        assert!(
            fixture
                .store
                .publish_interface_no_base_resolution(base_target)
        );
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &base_plan,
                base_target,
                &[base_parameter],
            ),
            Ok(base_target),
        );
        let return_type = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_type_from_type_node(method.return_type)
        .unwrap();
        let declared_parameter = fixture
            .store
            .declared_type_links(method.type_parameters[0].symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Union(declared_union) =
            fixture.store.type_payload(return_type).unwrap().data()
        else {
            panic!("the reopened method must preserve its merged interface parameter union")
        };
        assert_eq!(declared_union.union.types.len(), 2);
        assert!(declared_union.union.types.contains(&declared_parameter));
        assert!(declared_union.union.types.contains(&derived_parameter));
        let property_types = [derived_parameter, return_type];
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                derived,
                &property_types,
            ),
            Ok(derived),
        );

        let members = fixture
            .store
            .resolve_generic_interface_members(derived, None)
            .unwrap();
        assert_eq!(
            members
                .properties()
                .iter()
                .map(|property| fixture.store.symbol(*property).unwrap().name().as_utf8())
                .collect::<Vec<_>>(),
            [Some("own"), Some("map"), Some("inherited")],
        );
        let method_proxy = members.properties()[1];
        assert_ne!(method_proxy, method.symbol);
        assert_eq!(
            fixture
                .store
                .value_symbol_links(method_proxy)
                .and_then(|links| links.target),
            Some(method.symbol),
        );
        let self_method = fixture
            .store
            .resolve_generic_interface_property(derived, "map", None)
            .unwrap()
            .unwrap()
            .type_id();
        let [self_signature] = fixture
            .store
            .type_payload(self_method)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .unwrap()
        else {
            panic!("the self receiver must retain one fresh generic method signature")
        };
        let self_signature = fixture.store.signature(*self_signature).unwrap();
        let [self_parameter] = self_signature.type_parameters() else {
            panic!("the self receiver must freshen its generic method parameter")
        };
        let self_return = self_signature.resolved_return_type().unwrap();
        let TypeData::Union(self_union) = fixture.store.type_payload(self_return).unwrap().data()
        else {
            panic!("the self receiver must retain its fresh method parameter union")
        };
        assert!(self_union.union.types.contains(self_parameter));
        assert!(self_union.union.types.contains(&derived_parameter));

        let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        let receiver = fixture
            .store
            .create_direct_generic_reference_type(derived, &[string])
            .unwrap();
        assert_eq!(
            fixture
                .store
                .resolve_generic_interface_property(receiver, "inherited", None)
                .unwrap()
                .unwrap()
                .type_id(),
            string,
        );
        let callable = fixture
            .store
            .resolve_generic_interface_property(receiver, "map", None)
            .unwrap()
            .unwrap()
            .type_id();
        let [signature] = fixture
            .store
            .type_payload(callable)
            .and_then(|record| record.data().structured())
            .and_then(|structured| structured.signatures.as_deref())
            .unwrap()
        else {
            panic!("the concrete receiver must retain one fresh generic method signature")
        };
        let signature = fixture.store.signature(*signature).unwrap();
        let [parameter] = signature.type_parameters() else {
            panic!("the concrete receiver must freshen its generic method parameter")
        };
        let resolved_return = signature.resolved_return_type().unwrap();
        let TypeData::Union(resolved_union) =
            fixture.store.type_payload(resolved_return).unwrap().data()
        else {
            panic!("the concrete receiver must preserve its specialized method parameter union")
        };
        assert!(resolved_union.union.types.contains(parameter));
        assert!(resolved_union.union.types.contains(&string));

        let warm = state(&fixture.store, &plan, derived);
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &plan,
                derived,
                &property_types,
            ),
            Ok(derived),
        );
        assert_eq!(state(&fixture.store, &plan, derived), warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn reopened_generic_interfaces_substitute_forwarded_parameter_subsets() {
        let mut fixture = interface_fixture(
            concat!(
                "interface Derived<Unused, Value> extends Base<Value> { own: Unused } ",
                "interface Derived<Unused, Value> extends Base<Value> { extra: boolean } ",
                "interface Base<Item> { inherited: Item }",
            ),
            3_819,
        );
        let locals = fixture.bound.locals(fixture.bound.source_file()).unwrap();
        let base_symbol = fixture
            .store
            .symbol_table(locals)
            .and_then(|locals| locals.get_source("Base"))
            .unwrap();
        let globals = fixture.store.intrinsic_bootstrap().unwrap().globals;
        fixture
            .store
            .merge_global_symbol(globals, base_symbol)
            .unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let derived_plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();
        assert_eq!(derived_plan.declarations.len(), 2);
        let [heritage] = derived_plan.heritage.as_ref().unwrap().bases.as_slice() else {
            panic!("the reopened interface must retain one shared base")
        };
        assert_eq!(heritage.type_arguments.len(), 1);

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let derived = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let base = fixture
            .store
            .declared_type_links(base_symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let base_parameter = validate_direct_generic_reference(&fixture.store, base)
            .unwrap()
            .type_arguments[0];
        let derived_parameters = validate_direct_generic_reference(&fixture.store, derived)
            .unwrap()
            .type_arguments;
        let [unused, value] = derived_parameters.as_slice() else {
            panic!("the derived interface must retain both source parameters")
        };
        let (unused, value) = (*unused, *value);
        let expected_base = fixture
            .store
            .type_payload(derived)
            .and_then(|record| match record.data() {
                TypeData::Interface(interface) => interface
                    .resolved_base_types
                    .as_deref()
                    .and_then(|bases| bases.first())
                    .copied(),
                _ => None,
            })
            .unwrap();
        assert_eq!(
            validate_direct_generic_reference(&fixture.store, expected_base)
                .unwrap()
                .type_arguments,
            [value],
        );

        let base_plan = plan_generic_interface(&fixture.store, &host, base_symbol).unwrap();
        assert!(fixture.store.publish_interface_no_base_resolution(base));
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &base_plan,
                base,
                &[base_parameter],
            ),
            Ok(base),
        );

        let boolean = fixture.store.intrinsic_bootstrap().unwrap().boolean_type;
        let forged_base = fixture
            .store
            .create_direct_generic_reference_type(base, &[unused])
            .unwrap();
        assert!(fixture.store.set_interface_base_resolution(
            derived,
            true,
            None,
            Some(vec![forged_base]),
        ));
        let poisoned = state(&fixture.store, &derived_plan, derived);
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &derived_plan,
                derived,
                &[unused, boolean],
            ),
            Err(PropertyObjectError::InvalidCachedInterface {
                symbol: fixture.symbol,
                type_: derived,
            }),
        );
        assert_eq!(state(&fixture.store, &derived_plan, derived), poisoned);
        assert!(fixture.store.set_interface_base_resolution(
            derived,
            true,
            None,
            Some(vec![expected_base]),
        ));

        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &derived_plan,
                derived,
                &[unused, boolean],
            ),
            Ok(derived),
        );
        let members = fixture
            .store
            .resolve_generic_interface_members(derived, None)
            .unwrap();
        assert_eq!(
            members
                .properties()
                .iter()
                .map(|property| fixture.store.symbol(*property).unwrap().name().as_utf8())
                .collect::<Vec<_>>(),
            [Some("own"), Some("extra"), Some("inherited")],
        );

        let (string, number) = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let concrete = fixture
            .store
            .create_direct_generic_reference_type(derived, &[string, number])
            .unwrap();
        for (name, expected) in [("own", string), ("extra", boolean), ("inherited", number)] {
            assert_eq!(
                fixture
                    .store
                    .resolve_generic_interface_property(concrete, name, None)
                    .unwrap()
                    .unwrap()
                    .type_id(),
                expected,
                "{name}",
            );
        }

        let warm = (
            state(&fixture.store, &derived_plan, derived),
            fixture.store.type_len(),
            fixture.store.mapper_len(),
            fixture.store.symbol_len(),
        );
        assert_eq!(
            publish_generic_interface_declared_members(
                &mut fixture.store,
                &derived_plan,
                derived,
                &[unused, boolean],
            ),
            Ok(derived),
        );
        assert_eq!(
            (
                state(&fixture.store, &derived_plan, derived),
                fixture.store.type_len(),
                fixture.store.mapper_len(),
                fixture.store.symbol_len(),
            ),
            warm,
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn reopened_namespace_generic_interfaces_keep_inherited_members_cold() {
        let mut fixture = interface_fixture(
            concat!(
                "declare namespace React { ",
                "interface DOMAttributes<T> { unsupported(value: T): void; } ",
                "interface HTMLAttributes<T> extends DOMAttributes<T> { id?: string; } ",
                "interface HTMLAttributes<T> extends DOMAttributes<T> { title?: string; } ",
                "}",
            ),
            3_724,
        );
        let namespace = fixture
            .store
            .get_parent_of_symbol(fixture.symbol)
            .expect("the first interface belongs to React");
        let exports = fixture.store.symbol(namespace).unwrap().exports().unwrap();
        let symbol = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("HTMLAttributes"))
            .unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let plan = plan_lazy_merged_generic_interface(&fixture.store, &host, symbol).unwrap();

        assert_eq!(plan.symbol, symbol);
        assert_eq!(plan.namespace, namespace);
        assert_eq!(
            fixture.store.get_parent_of_symbol(plan.type_parameter),
            Some(symbol),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );
        assert!(fixture.store.declared_type_links(symbol).is_none());

        assert!(fixture.store.set_symbol_flags(
            symbol,
            SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT,
            CheckFlags::NONE,
        ));
        assert!(fixture.store.set_symbol_flags(
            plan.type_parameter,
            SymbolFlags::TYPE_PARAMETER | SymbolFlags::TRANSIENT,
            CheckFlags::NONE,
        ));
        assert_eq!(
            plan_lazy_merged_generic_interface(&fixture.store, &host, symbol),
            Ok(plan),
        );

        let flags = fixture.store.symbol(symbol).unwrap().flags();
        let target = get_declared_class_interface_or_type_parameter(
            &mut fixture.store,
            &host,
            symbol,
            flags,
        )
        .unwrap()
        .unwrap();
        let TypeData::Interface(interface) = fixture.store.type_payload(target).unwrap().data()
        else {
            panic!("the reopened interface must retain its generic target")
        };
        assert!(!interface.declared_members_resolved);
        let warm = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            plan_lazy_merged_generic_interface(&fixture.store, &host, symbol),
            Ok(plan),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn reopened_namespace_generic_interfaces_reject_mismatched_bases_and_parameter_flags() {
        let mut fixture = interface_fixture(
            concat!(
                "declare namespace React { ",
                "interface First<T> {} ",
                "interface Second<T> {} ",
                "interface HTMLAttributes<T> extends First<T> {} ",
                "interface HTMLAttributes<T> extends Second<T> {} ",
                "}",
            ),
            3_725,
        );
        let namespace = fixture.store.get_parent_of_symbol(fixture.symbol).unwrap();
        let exports = fixture.store.symbol(namespace).unwrap().exports().unwrap();
        let symbol = fixture
            .store
            .symbol_table(exports)
            .and_then(|exports| exports.get_source("HTMLAttributes"))
            .unwrap();
        let host = host(&fixture.parsed, &fixture.bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert!(matches!(
            plan_lazy_merged_generic_interface(&fixture.store, &host, symbol),
            Err(PropertyObjectError::InvalidInterface { .. }),
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );

        let parameter = fixture
            .store
            .symbol(symbol)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| fixture.store.symbol_table(members))
            .and_then(|members| members.get_source("T"))
            .unwrap();
        assert!(fixture.store.set_symbol_flags(
            parameter,
            SymbolFlags::TYPE_PARAMETER | SymbolFlags::PROPERTY,
            CheckFlags::NONE,
        ));
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.symbol_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert!(matches!(
            plan_lazy_merged_generic_interface(&fixture.store, &host, symbol),
            Err(PropertyObjectError::InvalidInterface { .. }),
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.symbol_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            poisoned,
        );
    }

    #[test]
    fn exported_generic_interfaces_publish_with_their_canonical_parent() {
        for (source, module_state, file) in [
            (
                "export interface Box<T> { value: T }",
                CanonicalModuleState::External,
                3_711,
            ),
            (
                "declare namespace Models { interface Box<T> { value: T } }",
                CanonicalModuleState::Script,
                3_712,
            ),
        ] {
            let mut fixture = interface_fixture_with_module_state(source, file, module_state);
            let host = host(&fixture.parsed, &fixture.bound);
            let plan = plan_generic_interface(&fixture.store, &host, fixture.symbol).unwrap();
            assert!(fixture.store.get_parent_of_symbol(plan.symbol).is_some());

            let flags = fixture.store.symbol(fixture.symbol).unwrap().flags();
            let target = get_declared_class_interface_or_type_parameter(
                &mut fixture.store,
                &host,
                fixture.symbol,
                flags,
            )
            .unwrap()
            .unwrap();
            let parameter = match fixture.store.type_payload(target).unwrap().data() {
                TypeData::Interface(interface) => interface
                    .reference
                    .resolved_type_arguments
                    .as_ref()
                    .unwrap()[0],
                _ => panic!("exported declaration must produce one generic interface target"),
            };
            assert!(fixture.store.publish_interface_no_base_resolution(target));
            assert_eq!(
                publish_generic_interface_declared_members(
                    &mut fixture.store,
                    &plan,
                    target,
                    &[parameter],
                ),
                Ok(target),
            );

            let string = fixture.store.intrinsic_bootstrap().unwrap().string_type;
            let reference = fixture
                .store
                .create_direct_generic_reference_type(target, &[string])
                .unwrap();
            assert_eq!(
                fixture
                    .store
                    .resolve_generic_interface_property(reference, "value", None)
                    .unwrap()
                    .unwrap()
                    .type_id(),
                string,
            );
        }
    }

    #[test]
    fn merged_interfaces_keep_quoted_properties_and_template_pattern_indexes() {
        let mut fixture = interface_fixture(
            "interface Attributes { key?: string } \
             interface Attributes { \
                [key: `do-${string}`]: number; \
                'ns:thing'?: string; \
             }",
            3_707,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let plan = plan_interface(&fixture.store, &host, fixture.symbol).unwrap();
        assert_eq!(
            plan.properties
                .iter()
                .map(|property| property.name.as_str())
                .collect::<Vec<_>>(),
            ["key", "ns:thing"]
        );
        let [index] = plan.indexes.as_slice() else {
            panic!("merged interface must retain its template index")
        };
        assert_eq!(
            fixture.store.source_node_kind(index.key_type_node),
            Some(SyntaxKind::TemplateLiteralType)
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let type_ = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalCheckerOptions::default(),
            &mut diagnostics,
        )
        .unwrap()
        .get_declared_type_of_symbol(fixture.symbol)
        .unwrap();
        let TypeData::Interface(interface) = fixture.store.type_payload(type_).unwrap().data()
        else {
            panic!("merged declaration must publish one interface type")
        };
        let [index] = interface.declared_index_infos.as_deref().unwrap() else {
            panic!("merged declaration must publish one template index")
        };
        assert!(
            fixture
                .store
                .type_payload(fixture.store.index_info(*index).unwrap().key_type())
                .unwrap()
                .flags()
                .contains(TypeFlags::TEMPLATE_LITERAL)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn incompatible_merged_property_annotations_fail_before_publication() {
        let fixture = interface_fixture(
            "interface Item { value: string } interface Item { value: number }",
            3_708,
        );
        let host = host(&fixture.parsed, &fixture.bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert!(matches!(
            plan_interface(&fixture.store, &host, fixture.symbol),
            Err(PropertyObjectError::UnsupportedMember {
                kind: SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature,
                ..
            })
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before
        );
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

    #[test]
    #[allow(clippy::too_many_lines)] // Preserve real cross-file binder and export-assignment identities.
    fn ambient_react_module_augmentations_keep_the_export_equals_namespace_owner() {
        let library = parse_source_file(concat!(
            "declare module 'react' { ",
            "export = React; ",
            "namespace React { interface Attributes { key?: string; } } ",
            "}",
        ));
        let source = parse_source_file(concat!(
            "export {}; ",
            "declare module 'react' { ",
            "interface Attributes { ",
            "[key: `do-${string}`]: number; ",
            "'ns:thing'?: string; ",
            "} }",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let library_file = FileId::new(3_760);
        let source_file = FileId::new(3_761);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, declaration, module_state) in [
            (&library, library_file, true, CanonicalModuleState::Script),
            (&source, source_file, false, CanonicalModuleState::External),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"/react-module-{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        declaration,
                        module_state,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let library_bound = files.remove(&library_file).unwrap();
        let source_bound = files.remove(&source_file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        for (parsed, file) in [(&library, library_file), (&source, source_file)] {
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .unwrap();
        }
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();

        let react_declaration = library
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &library.arena.get(module.name)?.data else {
                    return None;
                };
                (name.text == "React").then_some(NodeRef::new(
                    library.arena.id(),
                    library_file,
                    node,
                ))
            })
            .unwrap();
        let namespace = library_bound.symbol(react_declaration).unwrap();
        let namespace_exports = store.symbol(namespace).unwrap().exports().unwrap();
        let original = store
            .symbol_table(namespace_exports)
            .and_then(|exports| exports.get_source("Attributes"))
            .unwrap();
        let augmentation = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(&record.data, NodeData::ModuleDeclaration(_)).then_some(NodeRef::new(
                    source.arena.id(),
                    source_file,
                    node,
                ))
            })
            .unwrap();
        let augmentation_symbol = source_bound.symbol(augmentation).unwrap();
        let augmentation_exports = store
            .symbol(augmentation_symbol)
            .unwrap()
            .exports()
            .unwrap();
        let contributed = store
            .symbol_table(augmentation_exports)
            .and_then(|exports| exports.get_source("Attributes"))
            .unwrap();
        let merged_namespace = store
            .merge_symbol(namespace, augmentation_symbol, false)
            .unwrap();
        assert_ne!(merged_namespace, namespace);
        assert_ne!(merged_namespace, augmentation_symbol);
        assert_eq!(store.get_merged_symbol(namespace), Some(merged_namespace));
        assert_eq!(
            store.get_merged_symbol(augmentation_symbol),
            Some(merged_namespace),
        );
        let namespace_exports = store.symbol(merged_namespace).unwrap().exports().unwrap();
        let symbol = store
            .symbol_table(namespace_exports)
            .and_then(|exports| exports.get_source("Attributes"))
            .unwrap();
        assert_ne!(symbol, original);
        assert_ne!(symbol, contributed);
        assert_eq!(
            store.symbol(symbol).unwrap().flags(),
            SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT,
        );
        assert_eq!(store.get_parent_of_symbol(symbol), Some(merged_namespace));
        assert!(authenticated_merged_react_declared_property_interface(
            &store, symbol,
        ));
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, &library_bound),
                (&source.arena, &source_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let before = (
            store.type_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );

        let plan = plan_interface(&store, &host, symbol).unwrap();

        assert_eq!(plan.symbol, symbol);
        assert_eq!(plan.declarations.len(), 2);
        assert_eq!(
            plan.properties
                .iter()
                .map(|property| property.name.as_str())
                .collect::<Vec<_>>(),
            ["key", "ns:thing"],
        );
        assert_eq!(plan.indexes.len(), 1);
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
            ),
            before,
        );
        assert_eq!(plan_interface(&store, &host, contributed), Ok(plan));

        let original_module = library
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                matches!(
                    &library.arena.get(module.name)?.data,
                    NodeData::StringLiteral(_)
                )
                .then_some(NodeRef::new(library.arena.id(), library_file, node))
            })
            .and_then(|module| library_bound.symbol(module))
            .unwrap();
        let owner = store.symbol(symbol).unwrap();
        let relationships = (owner.members(), owner.exports(), owner.export_symbol());
        assert!(store.set_symbol_relationships(
            symbol,
            relationships.0,
            relationships.1,
            Some(original_module),
            relationships.2,
        ));
        assert!(!authenticated_merged_react_declared_property_interface(
            &store, symbol,
        ));
        let poisoned = (
            store.type_len(),
            store.symbol_len(),
            store.checker_link_allocated_lengths(),
        );
        assert!(matches!(
            plan_interface(&store, &host, symbol),
            Err(PropertyObjectError::InvalidInterface { .. }),
        ));
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.checker_link_allocated_lengths(),
            ),
            poisoned,
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Bind the DOM value owner and validate all lazy boundaries.
    fn empty_interfaces_keep_authenticated_default_library_dom_bases_cold() {
        let library = parse_source_file(concat!(
            "interface DomFirst {} ",
            "interface DomSecond {} ",
            "interface DomThird {} ",
            "interface DomFourth {} ",
            "interface DomFifth {} ",
            "interface HTMLElement extends ",
            "DomFirst, DomSecond, DomThird, DomFourth, DomFifth { ",
            "addEventListener(value: string): void; ",
            "[key: string]: unknown; ",
            "} ",
            "declare var HTMLElement: unknown;",
        ));
        let source = parse_source_file(concat!(
            "interface HTMLWebViewElement extends HTMLElement {} ",
            "interface InvalidWebViewElement extends HTMLElement { own: string } ",
            "interface MultipleWebViewElement extends HTMLElement, DomFirst {}",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let library_file = FileId::new(3_762);
        let source_file = FileId::new(3_763);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, default_library) in [
            (&library, library_file, true),
            (&source, source_file, false),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!("\"/dom-plan-{}.d.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        true,
                        default_library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let (symbols, mut files) = binder.finish().try_into_parts().unwrap();
        let library_bound = files.remove(&library_file).unwrap();
        let source_bound = files.remove(&source_file).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        for (parsed, file) in [(&library, library_file), (&source, source_file)] {
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .unwrap();
        }
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let globals = store.intrinsic_bootstrap().unwrap().globals;
        for bound in [&library_bound, &source_bound] {
            let symbols = store
                .symbol_table(bound.locals(bound.source_file()).unwrap())
                .unwrap()
                .iter()
                .map(|(_, symbol)| symbol)
                .collect::<Vec<_>>();
            for symbol in symbols {
                store.merge_global_symbol(globals, symbol).unwrap();
            }
        }
        let base = store
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("HTMLElement"))
            .unwrap();
        let derived = store
            .symbol_table(globals)
            .and_then(|globals| globals.get_source("HTMLWebViewElement"))
            .unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, &library_bound),
                (&source.arena, &source_bound),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let before = (
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.index_info_len(),
            store.checker_link_allocated_lengths(),
        );

        let plan = plan_interface(&store, &host, derived).unwrap();

        let [inherited] = plan.heritage.as_ref().unwrap().bases.as_slice() else {
            panic!("the empty DOM extension must retain exactly one authenticated base")
        };
        assert_eq!(inherited.symbol, base);
        assert_eq!(
            inherited.kind,
            DirectInterfaceBaseKind::DefaultLibraryInterface,
        );
        assert!(plan.properties.is_empty());
        assert!(plan.indexes.is_empty());
        assert!(plan.call_signatures.is_empty());
        assert!(store.declared_type_links(base).is_none());
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.index_info_len(),
                store.checker_link_allocated_lengths(),
            ),
            before,
        );
        assert_eq!(plan_interface(&store, &host, derived), Ok(plan));

        for name in ["InvalidWebViewElement", "MultipleWebViewElement"] {
            let invalid = store
                .symbol_table(globals)
                .and_then(|globals| globals.get_source(name))
                .unwrap();
            assert!(
                matches!(
                    plan_interface(&store, &host, invalid),
                    Err(PropertyObjectError::UnsupportedMember {
                        kind: SyntaxKind::InterfaceDeclaration,
                        ..
                    })
                ),
                "{name}",
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.index_info_len(),
                    store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }
}
