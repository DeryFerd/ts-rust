//! Property-only object construction for the first canonical checker slice.
//!
//! This module owns the exact syntax-to-member-table boundary.  It deliberately
//! does not recurse through property annotations: [`super::type_nodes`] plans
//! and executes those nodes so one query retains a single dependency graph and
//! resolution stack.

use std::collections::HashSet;

use ts_ast::{NodeData, NodeList, NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, InternalSymbolName, SemanticSymbolId, SymbolData, SymbolFlags,
    SymbolTableId,
};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeHost, TypeId, ValueSymbolLinks,
    declared::preflight_node,
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PlannedProperty {
    pub declaration: NodeRef,
    pub symbol: SemanticSymbolId,
    #[allow(dead_code)] // Retained for the next property-diagnostic range slice.
    pub name_node: NodeRef,
    pub type_node: NodeRef,
    pub optional: bool,
    #[allow(dead_code)] // Retained for the next readonly-property diagnostic slice.
    pub readonly: bool,
    pub name: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PropertyObjectPlan {
    pub kind: PropertyObjectKind,
    pub node: NodeRef,
    pub symbol: SemanticSymbolId,
    pub members: Option<SymbolTableId>,
    pub properties: Vec<PlannedProperty>,
    pub alias_symbol: Option<SemanticSymbolId>,
}

impl PropertyObjectPlan {
    pub(super) fn property_type_nodes(&self) -> impl ExactSizeIterator<Item = NodeRef> + '_ {
        self.properties.iter().map(|property| property.type_node)
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
    plan_members(
        store,
        host,
        PropertyObjectKind::ObjectLiteral,
        node,
        symbol,
        symbol_record.members(),
        &object.properties,
        None,
    )
}

pub(super) fn plan_type_literal(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    alias_symbol: Option<SemanticSymbolId>,
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
    let expected_parent = interface_declaration_parent(
        store,
        host,
        declaration,
        symbol,
        name,
        interface.modifiers.as_ref(),
    )?;
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
        || symbol_record.parent() != expected_parent
        || symbol_record.exports().is_some()
        || symbol_record.export_symbol().is_some()
        || name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(declaration.node)
        || interface.flow_node.is_some()
        || interface.local_symbol.is_some()
        || interface.symbol.is_some()
        || interface.type_parameters.is_some()
        || interface.heritage_clauses.is_some()
        || interface.members.has_trailing_comma
        || interface.members.range.start < record.range.start
        || interface.members.range.end != record.range.end
    {
        return Err(PropertyObjectError::InvalidInterface {
            declaration,
            symbol,
        });
    }
    plan_members(
        store,
        host,
        PropertyObjectKind::Interface,
        declaration,
        symbol,
        symbol_record.members(),
        &interface.members,
        None,
    )
}

fn interface_declaration_parent(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    name: NodeRef,
    modifiers: Option<&ts_ast::ModifierList>,
) -> Result<Option<SemanticSymbolId>, PropertyObjectError> {
    let invalid = || PropertyObjectError::InvalidInterface {
        declaration,
        symbol,
    };
    let Some(modifiers) = modifiers else {
        return Ok(None);
    };
    let (_, bound) = host.source(declaration).ok_or_else(invalid)?;
    let declaration_record = preflight_node(store, host, declaration).map_err(|_| invalid())?;
    let name_record = preflight_node(store, host, name).map_err(|_| invalid())?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invalid());
    };
    let source = bound.source_file();
    let source_record = preflight_node(store, host, source).map_err(|_| invalid())?;
    let NodeData::SourceFile(source_data) = &source_record.data else {
        return Err(invalid());
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
        return Err(invalid());
    }
    if !is_exact_export_modifier(
        store,
        host,
        declaration,
        declaration_record,
        name_record,
        modifiers,
    ) {
        return Err(invalid());
    }
    let facts = bound.source_facts().ok_or_else(invalid)?;
    if facts.is_javascript_file() || !facts.is_external_module() || facts.is_common_js_module() {
        return Err(invalid());
    }
    let source_symbol = bound.symbol(source).ok_or_else(invalid)?;
    let source_symbol_record = store.symbol(source_symbol).ok_or_else(invalid)?;
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
        return Err(invalid());
    }
    Ok(Some(source_symbol))
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
) -> Result<PropertyObjectPlan, PropertyObjectError> {
    let provisional = PropertyObjectPlan {
        kind,
        node,
        symbol,
        members,
        properties: Vec::new(),
        alias_symbol,
    };
    if kind != PropertyObjectKind::ObjectLiteral && member_nodes.has_trailing_comma
        || members.is_some() == member_nodes.nodes.is_empty()
    {
        return Err(invalid_plan(&provisional));
    }
    let table = members.and_then(|members| store.symbol_table(members));
    if members.is_some() != table.is_some()
        || table.is_some_and(|table| table.len() != member_nodes.nodes.len())
    {
        return Err(invalid_plan(&provisional));
    }

    let owner_record = preflight_node(store, host, node).map_err(|_| invalid_plan(&provisional))?;
    let mut previous_end = member_nodes.range.start;
    let mut seen_nodes = HashSet::new();
    let mut seen_symbols = HashSet::new();
    let mut seen_names = HashSet::new();
    let mut properties = Vec::with_capacity(member_nodes.nodes.len());
    for member in &member_nodes.nodes {
        let member = NodeRef::new(node.arena, node.file, *member);
        let member_record =
            preflight_node(store, host, member).map_err(|_| invalid_plan(&provisional))?;
        let admitted_kind = match kind {
            PropertyObjectKind::ObjectLiteral => {
                member_record.kind == SyntaxKind::PropertyAssignment
            }
            PropertyObjectKind::TypeLiteral | PropertyObjectKind::Interface => matches!(
                member_record.kind,
                SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature
            ),
        };
        if !admitted_kind {
            return Err(PropertyObjectError::UnsupportedMember {
                node: member,
                kind: member_record.kind,
            });
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
                _ => return Err(invalid_plan(&provisional)),
            };
        if member_record.parent != Some(node.node)
            || member_record.flags.0 & NODE_FLAG_JSDOC != 0
            || member_record.range.start < previous_end
            || member_record.range.start < member_nodes.range.start
            || member_record.range.end > member_nodes.range.end
            || member_record.range.start < owner_record.range.start
            || member_record.range.end > owner_record.range.end
            || !seen_nodes.insert(member)
            || !valid_payload
        {
            return Err(invalid_plan(&provisional));
        }
        if let Some(initializer) = signature_initializer
            && !missing_signature_initializer(store, host, member, initializer)
        {
            return Err(invalid_plan(&provisional));
        }
        previous_end = member_record.range.end;

        let name = NodeRef::new(member.arena, member.file, name_id);
        let name_record =
            preflight_node(store, host, name).map_err(|_| invalid_plan(&provisional))?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(PropertyObjectError::UnsupportedMember {
                node: name,
                kind: name_record.kind,
            });
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.parent != Some(member.node)
            || name_record.range.start < member_record.range.start
            || name_record.range.end > member_record.range.end
            || !seen_names.insert(identifier.text.clone())
        {
            return Err(invalid_plan(&provisional));
        }

        let type_node = NodeRef::new(member.arena, member.file, value_id.expect("checked above"));
        let type_record =
            preflight_node(store, host, type_node).map_err(|_| invalid_plan(&provisional))?;
        if type_record.parent != Some(member.node)
            || type_record.range.start < name_record.range.end
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
        if property_record.flags() != expected_flags
            || property_record.check_flags() != CheckFlags::NONE
            || property_record.name().as_utf8() != Some(identifier.text.as_str())
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
            || table.and_then(|table| table.get_source(&identifier.text)) != Some(property_symbol)
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
            name: identifier.text.clone(),
        });
    }

    Ok(PropertyObjectPlan {
        properties,
        ..provisional
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
    if plan.properties.is_empty() && plan.alias_symbol.is_none() {
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
    if plan.properties.is_empty() && plan.alias_symbol.is_none() {
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
                && valid_declared_structured_members(object, plan)
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
        && interface.declared_call_signatures.is_none()
        && interface.declared_construct_signatures.is_none()
        && interface.declared_index_infos.is_none()
        && valid_declared_structured_members(&interface.reference.object, plan)
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
            resolved_declared_property_types(store, type_)
                .map_or(
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
                                    SyntaxKind::PropertyDeclaration
                                        | SyntaxKind::PropertySignature
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
        DeclaredPropertyOwnerValidation::TraversableBoundary(declaration) => {
            (declaration, true)
        }
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
    use DetailedDeclaredPropertyObjectValidation::{
        Malformed, TraversableBoundary, Valid,
    };

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
        DeclaredPropertyOwnerValidation::TraversableBoundary(declaration) => {
            (declaration, true)
        }
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
    use DeclaredPropertyOwnerValidation::{
        Malformed, TraversableBoundary, Unsupported, Valid,
    };

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
            })
        {
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
            || property_record.check_flags() != CheckFlags::NONE
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

fn valid_declared_structured_members(object: &ObjectTypeData, plan: &PropertyObjectPlan) -> bool {
    valid_object_tail(object)
        && object.structured.constrained == ConstrainedTypeData::default()
        && object.structured.members == plan.members
        && object.structured.properties == plan.expected_properties()
        && object.structured.signatures.is_none()
        && object.structured.call_signature_count == 0
        && object.structured.index_infos.is_none()
        && object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_none()
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
        store
            .value_symbol_links(property.symbol)
            .is_none_or(|links| links == &ValueSymbolLinks::default())
    })
}

fn resolved_property_links(store: &CanonicalTypeMapperStore, plan: &PropertyObjectPlan) -> bool {
    plan.properties.iter().all(|property| {
        store
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
    })
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
                    store
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

pub(super) fn publish_property_members(
    store: &mut CanonicalTypeMapperStore,
    plan: &PropertyObjectPlan,
    state: PropertyObjectState,
    property_types: &[TypeId],
) -> Result<TypeId, PropertyObjectError> {
    if plan.kind == PropertyObjectKind::ObjectLiteral {
        return Err(PropertyObjectError::InvalidObjectLiteral(plan.node));
    }
    let type_ = state.type_id();
    if state.is_resolved() {
        validate_resolved_property_types(store, plan, property_types)?;
        return Ok(type_);
    }
    if property_types.len() != plan.properties.len()
        || property_types
            .iter()
            .any(|type_| store.type_payload(*type_).is_none())
        || !unresolved_property_links(store, plan)
    {
        return Err(invalid_cache(plan, type_));
    }

    // All fallible checks precede publication.  The store setters below can
    // only reject foreign identities, all of which were validated above.
    for (property, property_type) in plan.properties.iter().zip(property_types) {
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
                None,
                None,
                None,
            ));
        }
        PropertyObjectKind::Interface => {
            assert!(store.set_interface_declared_members(
                type_,
                true,
                plan.members,
                None,
                None,
                None,
            ));
            assert!(store.set_interface_base_resolution(type_, true, None, None));
            assert!(store.set_structured_type_members(
                type_,
                plan.members,
                plan.expected_properties(),
                None,
                None,
                None,
            ));
        }
        PropertyObjectKind::ObjectLiteral => {
            unreachable!("object-literal plans were rejected before publication")
        }
    }
    Ok(type_)
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
