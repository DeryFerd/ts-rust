//! Lazy annotated values and selected ordinary interface properties.

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedNameRef, InternalSymbolName, SemanticSymbolId, SymbolFlags, SymbolTableId,
};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, DeclaredTypeUnavailable,
    RelationUnavailable, TypeId,
    declared::{cached_interface_type, preflight_class_or_interface_reference, preflight_node},
    links::ValueSymbolLinks,
    object_members::{
        cached_planned_type_identity, missing_signature_initializer, preflight_readonly_modifier,
    },
    relater::ResolvedOwnProperty,
    store::SourceNodeParent,
    type_nodes::TypeNodeUnavailable,
    type_records::{StructuredTypeData, TypeData},
    types::{ObjectFlags, TypeFlags},
};

#[derive(Clone, Copy, Debug)]
pub(super) struct DeclaredValuePlan {
    pub(super) symbol: SemanticSymbolId,
    pub(super) annotation: NodeRef,
    pub(super) readonly: Option<bool>,
    pub(super) cached_type: Option<TypeId>,
}

/// Keeps the source query's result separate from mutable node and value caches.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DeclaredValueProvenance {
    pub(super) annotation: NodeRef,
    pub(super) type_: TypeId,
    pub(super) resolved_symbol: Option<SemanticSymbolId>,
    pub(super) readonly: Option<bool>,
}

impl DeclaredValueProvenance {
    pub(super) fn is_current(
        self,
        store: &CanonicalTypeMapperStore,
        symbol: SemanticSymbolId,
    ) -> bool {
        store
            .symbol(symbol)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            .and_then(|declaration| store.source_direct_type_annotation(declaration))
            == Some(self.annotation)
            && store.value_symbol_links(symbol)
                == Some(&ValueSymbolLinks {
                    resolved_type: Some(self.type_),
                    ..ValueSymbolLinks::default()
                })
            && store.source_direct_type_annotation_is_exact(self.annotation, self.type_)
            && store
                .symbol_node_links(self.annotation)
                .and_then(|links| links.resolved_symbol)
                == self.resolved_symbol
    }
}

fn invalid_value(symbol: SemanticSymbolId) -> DeclaredTypeError {
    DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol))
}

fn unsupported_value(node: NodeRef, kind: SyntaxKind) -> DeclaredTypeError {
    DeclaredTypeError::TypeNodeUnavailable(TypeNodeUnavailable::UnsupportedSyntax { node, kind })
}

/// Proves the source annotation and value cache without reading sibling types.
pub(super) fn plan_declared_value(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<DeclaredValuePlan, DeclaredTypeError> {
    let invalid = || invalid_value(symbol);
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    let declarations = record.declarations().ok_or_else(invalid)?;
    let declaration = record.value_declaration().ok_or_else(invalid)?;
    if store.get_merged_symbol(symbol) != Some(symbol)
        || declarations
            .iter()
            .filter(|node| **node == declaration)
            .count()
            != 1
        || record.exports().is_some()
        || record.export_symbol().is_some()
        || !host.symbol_matches(store, declaration, symbol)
    {
        return Err(invalid());
    }
    let node = preflight_node(store, host, declaration)?;
    if node.flags.0 != 0 {
        return Err(unsupported_value(declaration, node.kind));
    }
    let (name, annotation, readonly) = match &node.data {
        NodeData::VariableDeclaration(variable) if node.kind == SyntaxKind::VariableDeclaration => {
            let flags = record.flags().without(SymbolFlags::TRANSIENT);
            let variable_flags = flags.without(SymbolFlags::INTERFACE);
            if !matches!(
                variable_flags,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::BLOCK_SCOPED_VARIABLE
            ) || flags.contains(SymbolFlags::INTERFACE)
                && variable_flags != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                || !flags.contains(SymbolFlags::INTERFACE) && record.members().is_some()
                || record.check_flags() != CheckFlags::NONE
                || variable.initializer.is_some()
                || variable.exclamation_token.is_some()
                || variable.symbol.is_some()
                || variable.local_symbol.is_some()
                || variable.facts != 0
            {
                return Err(unsupported_value(declaration, node.kind));
            }
            let mut seen = std::collections::HashSet::new();
            for &candidate in declarations {
                if !seen.insert(candidate) || !host.symbol_matches(store, candidate, symbol) {
                    return Err(invalid());
                }
                if candidate != declaration {
                    let candidate_node = preflight_node(store, host, candidate)?;
                    let NodeData::InterfaceDeclaration(interface) = &candidate_node.data else {
                        return Err(invalid());
                    };
                    let name = NodeRef::new(candidate.arena, candidate.file, interface.name);
                    if !flags.contains(SymbolFlags::INTERFACE)
                        || candidate_node.kind != SyntaxKind::InterfaceDeclaration
                        || store.source_identifier_text(name) != record.name().as_utf8()
                    {
                        return Err(invalid());
                    }
                }
            }
            if flags.contains(SymbolFlags::INTERFACE) != (declarations.len() > 1) {
                return Err(invalid());
            }
            let list = node
                .parent
                .map(|parent| NodeRef::new(declaration.arena, declaration.file, parent))
                .ok_or_else(invalid)?;
            let list_node = preflight_node(store, host, list)?;
            let NodeData::VariableDeclarationList(declarations) = &list_node.data else {
                return Err(invalid());
            };
            let statement = list_node
                .parent
                .map(|parent| NodeRef::new(list.arena, list.file, parent))
                .ok_or_else(invalid)?;
            let statement_node = preflight_node(store, host, statement)?;
            let NodeData::VariableStatement(statement_data) = &statement_node.data else {
                return Err(invalid());
            };
            let bound = host.bound_file(declaration).ok_or_else(invalid)?;
            let block_scoped = list_node.flags.0 & 3 != 0;
            plan_variable_owner(store, host, symbol, declaration, statement)?;
            if list_node.kind != SyntaxKind::VariableDeclarationList
                || list_node.flags.0 & !3 != 0
                || declarations
                    .declarations
                    .nodes
                    .iter()
                    .filter(|candidate| **candidate == declaration.node)
                    .count()
                    != 1
                || statement_node.kind != SyntaxKind::VariableStatement
                || statement_data.declaration_list != list.node
                || statement_node.parent != Some(bound.source_file().node)
                || block_scoped != record.flags().contains(SymbolFlags::BLOCK_SCOPED_VARIABLE)
            {
                return Err(invalid());
            }
            (
                variable.name,
                variable
                    .type_
                    .ok_or_else(|| unsupported_value(declaration, node.kind))?,
                None,
            )
        }
        NodeData::PropertyDeclaration(property) if node.kind == SyntaxKind::PropertyDeclaration => {
            if declarations != [declaration]
                || record.members().is_some()
                || property.initializer.is_some()
                || property.symbol.is_some()
                || property.facts != 0
            {
                return Err(unsupported_value(declaration, node.kind));
            }
            let readonly =
                preflight_readonly_modifier(store, host, declaration, property.modifiers.as_ref())
                    .ok_or_else(invalid)?;
            plan_property_owner(
                store,
                host,
                symbol,
                declaration,
                property.postfix_token,
                readonly,
            )?;
            (
                property.name,
                property
                    .type_
                    .ok_or_else(|| unsupported_value(declaration, node.kind))?,
                Some(readonly),
            )
        }
        NodeData::PropertySignatureDeclaration(property)
            if node.kind == SyntaxKind::PropertySignature =>
        {
            if declarations != [declaration]
                || record.members().is_some()
                || property.symbol.is_some()
                || !missing_signature_initializer(store, host, declaration, property.initializer)
            {
                return Err(invalid());
            }
            let readonly =
                preflight_readonly_modifier(store, host, declaration, property.modifiers.as_ref())
                    .ok_or_else(invalid)?;
            plan_property_owner(
                store,
                host,
                symbol,
                declaration,
                property.postfix_token,
                readonly,
            )?;
            (property.name, property.type_, Some(readonly))
        }
        _ => return Err(unsupported_value(declaration, node.kind)),
    };
    let name = NodeRef::new(declaration.arena, declaration.file, name);
    let name_node = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_node.data else {
        return Err(unsupported_value(name, name_node.kind));
    };
    let annotation = NodeRef::new(declaration.arena, declaration.file, annotation);
    let annotation_node = preflight_node(store, host, annotation)?;
    if name_node.kind != SyntaxKind::Identifier
        || name_node.flags.0 != 0
        || name_node.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || record.name().as_utf8() != Some(identifier.text.as_str())
        || annotation_node.parent != Some(declaration.node)
        || name_node.range.start < node.range.start
        || name_node.range.end > annotation_node.range.start
        || annotation_node.range.end > node.range.end
        || store.source_direct_type_annotation(declaration) != Some(annotation)
    {
        return Err(invalid());
    }
    let links = store
        .value_symbol_links(symbol)
        .cloned()
        .unwrap_or_default();
    if links
        != (ValueSymbolLinks {
            resolved_type: links.resolved_type,
            ..ValueSymbolLinks::default()
        })
        || links.resolved_type.is_some_and(|type_| {
            !store.source_direct_type_annotation_is_exact(annotation, type_)
                || readonly == Some(true) && record.check_flags() != CheckFlags::READONLY
        })
    {
        return Err(invalid());
    }
    if store
        .declared_value_provenance(symbol)
        .is_some_and(|provenance| {
            provenance.annotation != annotation
                || provenance.readonly != readonly
                || !provenance.is_current(store, symbol)
        })
    {
        return Err(invalid());
    }
    Ok(DeclaredValuePlan {
        symbol,
        annotation,
        readonly,
        cached_type: links.resolved_type,
    })
}

fn plan_variable_owner(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
    statement: NodeRef,
) -> Result<(), DeclaredTypeError> {
    let invalid = || invalid_value(symbol);
    let unsupported = || unsupported_value(declaration, SyntaxKind::VariableDeclaration);
    let (arena, bound) = host.source(declaration).ok_or_else(invalid)?;
    let value = store.symbol(symbol).ok_or_else(invalid)?;
    let Some(local) = bound.local_symbol(declaration) else {
        return if value.parent().is_none() {
            Ok(())
        } else {
            Err(unsupported())
        };
    };
    let facts = bound.source_facts().ok_or_else(invalid)?;
    if !facts.is_external_module()
        || facts.is_javascript_file()
        || facts.is_common_js_module()
        || bound.container(declaration) != Some(bound.source_file())
        || !matches!(
            value.flags(),
            SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::BLOCK_SCOPED_VARIABLE
        )
        || value.declarations() != Some(&[declaration])
    {
        return Err(unsupported());
    }
    let statement_node = preflight_node(store, host, statement)?;
    let NodeData::VariableStatement(variable_statement) = &statement_node.data else {
        return Err(invalid());
    };
    if statement_node.flags.0 != 0
        || variable_statement.flow_node.is_some()
        || variable_statement.facts != 0
    {
        return Err(invalid());
    }
    let mut exported = false;
    let mut declared = false;
    if let Some(modifiers) = &variable_statement.modifiers {
        if modifiers.flags.0 != 0
            || modifiers.list.has_trailing_comma
            || modifiers.list.nodes.is_empty()
        {
            return Err(invalid());
        }
        let mut previous_end = statement_node.range.start;
        for modifier in &modifiers.list.nodes {
            let modifier = NodeRef::new(statement.arena, statement.file, *modifier);
            let node = preflight_node(store, host, modifier)?;
            let spelling = match node.kind {
                SyntaxKind::ExportKeyword if !exported && !declared => {
                    exported = true;
                    "export"
                }
                SyntaxKind::DeclareKeyword if !declared => {
                    declared = true;
                    "declare"
                }
                _ => return Err(unsupported()),
            };
            if !matches!(node.data, NodeData::Token(_))
                || node.flags.0 != 0
                || node.parent != Some(statement.node)
                || node.range.start < previous_end
                || node.range.end > statement_node.range.end
                || arena.source_text().is_some_and(|source| {
                    source.get(node.range.start.get() as usize..node.range.end.get() as usize)
                        != Some(spelling)
                })
            {
                return Err(invalid());
            }
            previous_end = node.range.end;
        }
    }
    if !facts.is_declaration_file() && (!exported || !declared) {
        return Err(unsupported());
    }

    let source = bound.source_file();
    let source_node = preflight_node(store, host, source)?;
    let module = bound.symbol(source).ok_or_else(invalid)?;
    let module_record = store.symbol(module).ok_or_else(invalid)?;
    let local_record = store.symbol(local).ok_or_else(invalid)?;
    if source_node.kind != SyntaxKind::SourceFile
        || source_node.parent.is_some()
        || bound.container(declaration) != Some(source)
        || bound.symbol(declaration) != Some(symbol)
        || value.parent() != Some(module)
        || !store.source_symbol_declarations_match(symbol)
        || module_record.flags() != SymbolFlags::VALUE_MODULE
        || module_record.check_flags() != CheckFlags::NONE
        || module_record.name() != facts.source_file_symbol_name()
        || module_record.declarations() != Some(&[source])
        || module_record.value_declaration() != Some(source)
        || module_record.parent().is_some()
        || module_record.members().is_some()
        || module_record.export_symbol().is_some()
        || store.get_merged_symbol(module) != Some(module)
        || !store.source_symbol_declarations_match(module)
        || module_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(value.name()))
            != Some(symbol)
        || local_record.flags() != SymbolFlags::EXPORT_VALUE
        || local_record.check_flags() != CheckFlags::NONE
        || local_record.name() != value.name()
        || local_record.declarations() != Some(&[declaration])
        || local_record.value_declaration().is_some()
        || local_record.parent().is_some()
        || local_record.members().is_some()
        || local_record.exports().is_some()
        || local_record.export_symbol() != Some(symbol)
        || store.get_merged_symbol(local) != Some(local)
        || !store.source_symbol_declarations_match(local)
        || bound
            .locals(source)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get(value.name()))
            != Some(local)
        || store
            .value_symbol_links(local)
            .is_some_and(|links| links != &ValueSymbolLinks::default())
    {
        return Err(invalid());
    }
    Ok(())
}

fn plan_property_owner(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
    question: Option<ts_ast::NodeId>,
    readonly: bool,
) -> Result<(), DeclaredTypeError> {
    let invalid = || invalid_value(symbol);
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    let owner = store.get_parent_of_symbol(symbol).ok_or_else(invalid)?;
    let owner_record = store.symbol(owner).ok_or_else(invalid)?;
    let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(declaration) else {
        return Err(invalid());
    };
    let parent_node = preflight_node(store, host, parent)?;
    let NodeData::InterfaceDeclaration(interface) = &parent_node.data else {
        return Err(unsupported_value(parent, parent_node.kind));
    };
    if !owner_record.flags().contains(SymbolFlags::INTERFACE)
        || owner_record.flags().contains(SymbolFlags::CLASS)
        || !host.symbol_matches(store, parent, owner)
        || owner_record
            .declarations()
            .is_none_or(|declarations| !declarations.contains(&parent))
        || interface
            .members
            .nodes
            .iter()
            .filter(|member| **member == declaration.node)
            .count()
            != 1
        || owner_record
            .members()
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get(record.name()))
            .and_then(|member| store.get_merged_symbol(member))
            != Some(symbol)
    {
        return Err(invalid());
    }
    preflight_class_or_interface_reference(store, host, owner, owner_record.flags())?;
    let optional = if let Some(question) = question {
        let question = NodeRef::new(declaration.arena, declaration.file, question);
        let question_node = preflight_node(store, host, question)?;
        if question_node.kind != SyntaxKind::QuestionToken
            || question_node.flags.0 != 0
            || question_node.parent != Some(declaration.node)
        {
            return Err(invalid());
        }
        true
    } else {
        false
    };
    if record.flags()
        != SymbolFlags::PROPERTY
            | if optional {
                SymbolFlags::OPTIONAL
            } else {
                SymbolFlags::NONE
            }
        || record.check_flags() != CheckFlags::NONE
            && (!readonly || record.check_flags() != CheckFlags::READONLY)
    {
        return Err(invalid());
    }
    Ok(())
}

pub(super) enum SelectedDeclaredProperty {
    Missing,
    Unresolved(SemanticSymbolId),
    Resolved(ResolvedOwnProperty),
}

/// Reads one ordinary member from an authenticated, unresolved interface.
/// Complete members and generic instances retain their existing providers.
pub(super) fn selected_declared_property(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
    name: EscapedNameRef<'_>,
) -> Result<Option<SelectedDeclaredProperty>, RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(receiver);
    let record = store
        .type_payload(receiver)
        .ok_or(RelationUnavailable::Type(receiver))?;
    let TypeData::Interface(interface) = record.data() else {
        return Ok(None);
    };
    if interface.declared_members_resolved
        || record
            .object_flags()
            .intersects(ObjectFlags::CLASS | ObjectFlags::MEMBERS_RESOLVED)
        || interface
            .reference
            .resolved_type_arguments
            .as_ref()
            .is_some_and(|arguments| !arguments.is_empty())
    {
        return Ok(None);
    }
    let owner = record.symbol().ok_or_else(invalid)?;
    let owner_record = store.symbol(owner).ok_or_else(invalid)?;
    if !owner_record.flags().contains(SymbolFlags::INTERFACE) {
        return Ok(None);
    }
    if cached_interface_type(store, owner).map_err(|_| invalid())? != Some(receiver)
        || interface.declared_members.is_some()
        || interface.declared_index_infos.is_some()
        || interface.declared_call_signatures.is_some()
        || interface.declared_construct_signatures.is_some()
        || interface.resolved_base_types.is_some()
        || interface.resolved_base_constructor_type.is_some()
        || interface.reference.object.structured != StructuredTypeData::default()
        || store.get_merged_symbol(owner) != Some(owner)
        || owner_record.flags().without(
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT,
        ) != SymbolFlags::NONE
        || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.exports().is_some()
        || owner_record.export_symbol().is_some()
    {
        return Err(invalid());
    }
    let declarations = owner_record.declarations().ok_or_else(invalid)?;
    let has_heritage = declarations.iter().any(|declaration| {
        store.source_node_kind(*declaration) == Some(SyntaxKind::InterfaceDeclaration)
            && store
                .source_child_with_kind(*declaration, SyntaxKind::HeritageClause)
                .is_some()
    });
    if has_heritage && interface.base_types_resolved {
        return Err(invalid());
    }
    if store
        .source_computed_member_count(owner)
        .is_none_or(|count| count != 0)
    {
        return Ok(None);
    }
    if !cold_member_names_are_exact(store, owner, owner_record.members())? {
        return Ok(None);
    }
    let Some(members) = owner_record.members() else {
        return Ok((!has_heritage).then_some(SelectedDeclaredProperty::Missing));
    };
    let members = store.symbol_table(members).ok_or_else(invalid)?;
    let Some(symbol) = members.get(name) else {
        return Ok((!has_heritage).then_some(SelectedDeclaredProperty::Missing));
    };
    let symbol = store.get_merged_symbol(symbol).ok_or_else(invalid)?;
    let property = store.symbol(symbol).ok_or_else(invalid)?;
    if !property.flags().contains(SymbolFlags::PROPERTY) {
        return Ok(None);
    }
    let Some([declaration]) = property.declarations() else {
        return Ok(None);
    };
    let declaration = *declaration;
    let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(declaration) else {
        return Err(invalid());
    };
    let readonly = store
        .source_child_with_kind(declaration, SyntaxKind::ReadonlyKeyword)
        .is_some();
    let optional = store
        .source_child_with_kind(declaration, SyntaxKind::QuestionToken)
        .is_some();
    let expected_flags = SymbolFlags::PROPERTY
        | if optional {
            SymbolFlags::OPTIONAL
        } else {
            SymbolFlags::NONE
        };
    let identifier = store
        .source_child_with_kind(declaration, SyntaxKind::Identifier)
        .and_then(|name| store.source_identifier_text(name));
    if property.flags() != expected_flags
        || property.check_flags() != CheckFlags::NONE
            && (!readonly || property.check_flags() != CheckFlags::READONLY)
        || property.value_declaration() != Some(declaration)
        || property.members().is_some()
        || property.exports().is_some()
        || property.export_symbol().is_some()
        || store.get_parent_of_symbol(symbol) != Some(owner)
        || !declarations.contains(&parent)
        || store.source_node_kind(parent) != Some(SyntaxKind::InterfaceDeclaration)
        || !matches!(
            store.source_node_kind(declaration),
            Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
        )
        || identifier != property.name().as_utf8()
        || property.name() != name
    {
        return Err(invalid());
    }
    let annotation = store
        .source_direct_type_annotation(declaration)
        .ok_or(RelationUnavailable::UnsupportedProperty(symbol))?;
    let links = store
        .value_symbol_links(symbol)
        .cloned()
        .unwrap_or_default();
    if links
        != (ValueSymbolLinks {
            resolved_type: links.resolved_type,
            ..ValueSymbolLinks::default()
        })
    {
        return Err(invalid());
    }
    let Some(type_) = links.resolved_type else {
        if store.declared_value_provenance(symbol).is_some() {
            return Err(invalid());
        }
        return Ok(Some(SelectedDeclaredProperty::Unresolved(symbol)));
    };
    if !store.source_direct_type_annotation_is_exact(annotation, type_)
        || cached_planned_type_identity(store, annotation) != Some(type_)
        || store.type_payload(type_).is_none()
        || readonly && property.check_flags() != CheckFlags::READONLY
        || store.source_type_operator(annotation) == Some(SyntaxKind::UniqueKeyword)
            && store.type_payload(type_).is_none_or(|record| {
                record.symbol() != Some(symbol)
                    || record.flags() != TypeFlags::UNIQUE_ES_SYMBOL
                    || record.object_flags() != ObjectFlags::NONE
                    || record.alias().is_some()
                    || !matches!(record.data(), TypeData::UniqueEsSymbol(_))
            })
    {
        return Err(invalid());
    }
    let Some(provenance) = store.declared_value_provenance(symbol) else {
        return Ok(Some(SelectedDeclaredProperty::Unresolved(symbol)));
    };
    if provenance.readonly != Some(readonly) || !provenance.is_current(store, symbol) {
        return Err(invalid());
    }
    Ok(Some(SelectedDeclaredProperty::Resolved(
        ResolvedOwnProperty {
            symbol,
            type_,
            optional,
            readonly,
        },
    )))
}

fn cold_member_names_are_exact(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    members: Option<SymbolTableId>,
) -> Result<bool, RelationUnavailable> {
    let invalid = || RelationUnavailable::Symbol(owner);
    let record = store.symbol(owner).ok_or_else(invalid)?;
    let declarations = record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
        .ok_or_else(invalid)?;
    let table = members
        .map(|members| store.symbol_table(members).ok_or_else(invalid))
        .transpose()?;
    let mut selected = std::collections::HashMap::<SemanticSymbolId, Vec<NodeRef>>::new();
    let mut saw_interface = false;
    for &declaration in declarations {
        if store.source_node_kind(declaration) != Some(SyntaxKind::InterfaceDeclaration) {
            if store.source_node_kind(declaration) == Some(SyntaxKind::VariableDeclaration)
                && record.value_declaration() == Some(declaration)
                && record
                    .flags()
                    .contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
            {
                continue;
            }
            return Err(invalid());
        }
        saw_interface = true;
        if store
            .source_child_with_kind(declaration, SyntaxKind::Identifier)
            .and_then(|name| store.source_identifier_text(name))
            != record.name().as_utf8()
        {
            return Err(invalid());
        }
        for member in store
            .source_direct_children(declaration)
            .ok_or_else(invalid)?
        {
            let name = match store.source_node_kind(member) {
                Some(SyntaxKind::CallSignature) => InternalSymbolName::Call.as_ref(),
                Some(SyntaxKind::ConstructSignature) => InternalSymbolName::New.as_ref(),
                Some(SyntaxKind::IndexSignature) => InternalSymbolName::Index.as_ref(),
                Some(
                    SyntaxKind::PropertyDeclaration
                    | SyntaxKind::PropertySignature
                    | SyntaxKind::MethodSignature
                    | SyntaxKind::GetAccessor
                    | SyntaxKind::SetAccessor,
                ) => {
                    let Some(name) = store
                        .source_child_with_kind(member, SyntaxKind::Identifier)
                        .and_then(|name| store.source_identifier_text(name))
                    else {
                        return Ok(false);
                    };
                    EscapedNameRef::source(name)
                }
                Some(SyntaxKind::TypeParameter) => return Ok(false),
                // Heritage clauses do not declare own member names.
                Some(_) => continue,
                None => return Err(invalid()),
            };
            let symbol = table
                .and_then(|table| table.get(name))
                .and_then(|symbol| store.get_merged_symbol(symbol))
                .ok_or_else(invalid)?;
            let member_record = store.symbol(symbol).ok_or_else(invalid)?;
            if member_record.name() != name
                || store.get_parent_of_symbol(symbol) != Some(owner)
                || member_record
                    .declarations()
                    .is_none_or(|nodes| !nodes.contains(&member))
            {
                return Err(invalid());
            }
            selected.entry(symbol).or_default().push(member);
        }
    }
    if !saw_interface
        || selected.len() != table.map_or(0, ts_binder::semantic::SymbolTable::len)
        || selected.iter().any(|(symbol, nodes)| {
            store
                .symbol(*symbol)
                .and_then(ts_binder::semantic::Symbol::declarations)
                .is_none_or(|declarations| {
                    declarations.len() != nodes.len()
                        || declarations
                            .iter()
                            .any(|declaration| !nodes.contains(declaration))
                })
        })
    {
        return Err(invalid());
    }
    Ok(true)
}

/// Publishes only the selected value. The interface member table stays cold.
pub(super) fn publish_declared_value(
    store: &mut CanonicalTypeMapperStore,
    plan: DeclaredValuePlan,
    type_: TypeId,
) -> Result<TypeId, DeclaredTypeError> {
    if plan.cached_type.is_some_and(|cached| cached != type_)
        || !store.source_direct_type_annotation_is_exact(plan.annotation, type_)
        || !store.set_value_symbol_links(
            plan.symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        )
    {
        return Err(invalid_value(plan.symbol));
    }
    if let Some(readonly) = plan.readonly
        && !store.set_source_property_readonly(plan.symbol, readonly)
    {
        return Err(invalid_value(plan.symbol));
    }
    let provenance = DeclaredValueProvenance {
        annotation: plan.annotation,
        type_,
        resolved_symbol: store
            .symbol_node_links(plan.annotation)
            .and_then(|links| links.resolved_symbol),
        readonly: plan.readonly,
    };
    if !store.publish_declared_value_provenance(plan.symbol, provenance) {
        return Err(invalid_value(plan.symbol));
    }
    Ok(type_)
}
