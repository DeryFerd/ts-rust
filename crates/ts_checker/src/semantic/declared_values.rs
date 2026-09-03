//! Lazy annotated values and selected source-owned properties.

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedNameRef, InternalSymbolName, SemanticSymbolId, SymbolFlags, SymbolTableId,
};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, DeclaredTypeUnavailable,
    RelationUnavailable, TypeId,
    declared::{cached_interface_type, preflight_class_or_interface_reference, preflight_node},
    links::ValueSymbolLinks,
    object_aliases::{
        PropertyObjectAliasProjection, SourcePropertyObjectProjection,
        source_property_object_projection,
    },
    object_members::{
        DeclaredPropertyObjectProof, DeclaredPropertyObjectValidation, PlannedProperty,
        cached_planned_type_identity, missing_signature_initializer, preflight_readonly_modifier,
        validate_resolved_declared_property_object,
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
    if let Some(plan) = plan_global_type_literal_value(store, host, symbol)? {
        return Ok(plan);
    }
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
            let namespace_variable =
                global_callable_namespace_variable(store, host, symbol, declaration, statement);
            if !namespace_variable {
                plan_variable_owner(store, host, symbol, declaration, statement)?;
            }
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
                || !namespace_variable && statement_node.parent != Some(bound.source_file().node)
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
    plan_declared_value_cache(store, symbol, annotation, readonly)
}

pub(super) fn plan_declared_value_cache(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    annotation: NodeRef,
    readonly: Option<bool>,
) -> Result<DeclaredValuePlan, DeclaredTypeError> {
    let invalid = || invalid_value(symbol);
    let record = store.symbol(symbol).ok_or_else(invalid)?;
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

/// Reads the selected library value without removing any global augmentation.
/// The saved declaration order, not the mutable value selector, admits this route.
pub(super) fn plan_global_type_literal_value(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<Option<DeclaredValuePlan>, DeclaredTypeError> {
    plan_global_annotated_value(store, host, symbol, SyntaxKind::TypeLiteral)
}

/// A named constructor keeps the same selected value and complete global merge.
pub(super) fn plan_global_named_constructor_value(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<Option<DeclaredValuePlan>, DeclaredTypeError> {
    plan_global_annotated_value(store, host, symbol, SyntaxKind::TypeReference)
}

#[allow(clippy::too_many_lines)] // The complete merge and selected source form one proof.
fn plan_global_annotated_value(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    annotation_kind: SyntaxKind,
) -> Result<Option<DeclaredValuePlan>, DeclaredTypeError> {
    let invalid = || invalid_value(symbol);
    let Some(globals) = store.source_global_bindings() else {
        return Ok(None);
    };
    let Some(original) = globals.iter().find(|entry| entry.symbol == symbol) else {
        return Ok(None);
    };
    let declarations = original.declarations().unwrap_or_default();
    let Some(selected) = declarations
        .iter()
        .copied()
        .find(|&node| store.source_node_kind(node) == Some(SyntaxKind::VariableDeclaration))
    else {
        return Ok(None);
    };
    let Some(annotation) = store.source_direct_type_annotation(selected) else {
        return Ok(None);
    };
    if !store.source_is_default_library_declaration(selected)
        || store.source_node_kind(annotation) != Some(annotation_kind)
    {
        return Ok(None);
    }
    // The type-side and value-side readers share this ordered mixed-owner proof.
    // The variable-only route retains its complete host proof below.
    let mixed = store.source_global_interface_value_owner(symbol)?;
    let (table, table_symbol, selected, annotation) = mixed.as_ref().map_or(
        (globals.table, original.table_symbol, selected, annotation),
        |owner| {
            (
                owner.globals_table(),
                owner.table_symbol(),
                owner.value_declaration(),
                owner.value_annotation(),
            )
        },
    );
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    if store.get_merged_symbol(symbol) != Some(symbol)
        || store.get_merged_symbol(table_symbol) != Some(symbol)
        || globals
            .get(record.name())
            .is_none_or(|entry| entry.symbol != symbol || entry.table_symbol != table_symbol)
        || store
            .intrinsic_bootstrap()
            .is_none_or(|bootstrap| bootstrap.globals != table)
        || store
            .symbol_table(table)
            .and_then(|table| table.get(record.name()))
            != Some(table_symbol)
        || record.flags() != original.flags
        || record.declarations() != Some(declarations)
        || !store.source_merged_symbol_declarations_match(symbol)
        || record.value_declaration() != Some(selected)
        || record.check_flags() != CheckFlags::NONE
        || record.parent().is_some()
        || record.exports().is_some()
        || record.export_symbol().is_some()
        || !record.flags().contains(SymbolFlags::INTERFACE) && record.members().is_some()
    {
        return Err(invalid());
    }
    let mut flags = SymbolFlags::NONE;
    for &declaration in declarations {
        let node = preflight_node(store, host, declaration)?;
        let bound = host.bound_file(declaration).ok_or_else(invalid)?;
        let facts = bound.source_facts().ok_or_else(invalid)?;
        if !facts.is_declaration_file()
            || facts.is_javascript_file()
            || facts.is_common_js_module()
            || store.source_file_rank(declaration.file).is_none()
            || !host.symbol_matches(store, declaration, symbol)
            || node.flags.0 != 0
        {
            return Err(invalid());
        }
        match &node.data {
            NodeData::VariableDeclaration(_) if node.kind == SyntaxKind::VariableDeclaration => {
                flags |= plan_global_variable_declaration(store, host, symbol, declaration)?;
            }
            NodeData::InterfaceDeclaration(interface)
                if node.kind == SyntaxKind::InterfaceDeclaration =>
            {
                flags |= SymbolFlags::INTERFACE;
                let name = NodeRef::new(declaration.arena, declaration.file, interface.name);
                let name_node = preflight_node(store, host, name)?;
                if name_node.kind != SyntaxKind::Identifier
                    || name_node.flags.0 != 0
                    || name_node.parent != Some(declaration.node)
                    || !matches!(&name_node.data, NodeData::Identifier(name)
                        if name.flow_node.is_none()
                            && record.name().as_utf8() == Some(name.text.as_str()))
                    || interface.symbol.is_some()
                    || interface.local_symbol.is_some()
                    || interface.flow_node.is_some()
                    || if facts.is_external_module()
                        || node.parent != Some(bound.source_file().node)
                    {
                        !store.source_global_interface_augmentation_is_exact(symbol, declaration)
                    } else {
                        node.parent != Some(bound.source_file().node)
                    }
                {
                    return Err(invalid());
                }
                if node.parent != Some(bound.source_file().node) {
                    let block = node.parent.ok_or_else(invalid)?;
                    let module = preflight_node(
                        store,
                        host,
                        NodeRef::new(declaration.arena, declaration.file, block),
                    )?
                    .parent
                    .ok_or_else(invalid)?;
                    plan_global_augmentation_parent(
                        store,
                        host,
                        symbol,
                        NodeRef::new(declaration.arena, declaration.file, module),
                    )?;
                }
            }
            _ => return Err(invalid()),
        }
    }
    if flags != record.flags().without(SymbolFlags::TRANSIENT)
        || flags.contains(SymbolFlags::BLOCK_SCOPED_VARIABLE)
            && (flags.contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
                || flags.contains(SymbolFlags::INTERFACE))
    {
        return Err(invalid());
    }
    plan_declared_value_cache(store, symbol, annotation, None).map(Some)
}

#[allow(clippy::too_many_lines)] // Variable syntax and its script or augmentation edge are inseparable.
fn plan_global_variable_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
) -> Result<SymbolFlags, DeclaredTypeError> {
    let invalid = || invalid_value(symbol);
    let owner = store.symbol(symbol).ok_or_else(invalid)?;
    let node = preflight_node(store, host, declaration)?;
    let NodeData::VariableDeclaration(variable) = &node.data else {
        return Err(invalid());
    };
    let name = NodeRef::new(declaration.arena, declaration.file, variable.name);
    let name_node = preflight_node(store, host, name)?;
    let annotation = variable
        .type_
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(invalid)?;
    let annotation_node = preflight_node(store, host, annotation)?;
    let list = node
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(invalid)?;
    let list_node = preflight_node(store, host, list)?;
    let NodeData::VariableDeclarationList(list_data) = &list_node.data else {
        return Err(invalid());
    };
    let statement = list_node
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(invalid)?;
    let statement_node = preflight_node(store, host, statement)?;
    let NodeData::VariableStatement(statement_data) = &statement_node.data else {
        return Err(invalid());
    };
    let bound = host.bound_file(declaration).ok_or_else(invalid)?;
    if variable.initializer.is_some()
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.facts != 0
        || name_node.kind != SyntaxKind::Identifier
        || name_node.flags.0 != 0
        || name_node.parent != Some(declaration.node)
        || !matches!(&name_node.data, NodeData::Identifier(name)
            if name.flow_node.is_none()
                && owner.name().as_utf8() == Some(name.text.as_str()))
        || annotation_node.flags.0 != 0
        || annotation_node.parent != Some(declaration.node)
        || store.source_direct_type_annotation(declaration) != Some(annotation)
        || name_node.range.start < node.range.start
        || name_node.range.end > annotation_node.range.start
        || annotation_node.range.end > node.range.end
        || list_node.kind != SyntaxKind::VariableDeclarationList
        || !matches!(list_node.flags.0, 0..=2)
        || list_data.declarations.has_trailing_comma
        || list_data
            .declarations
            .nodes
            .iter()
            .filter(|&&node| node == declaration.node)
            .count()
            != 1
        || statement_node.kind != SyntaxKind::VariableStatement
        || statement_node.flags.0 != 0
        || statement_data.declaration_list != list.node
        || statement_data.flow_node.is_some()
        || statement_data.facts != 0
    {
        return Err(invalid());
    }
    if let Some(modifiers) = &statement_data.modifiers {
        let [modifier] = modifiers.list.nodes.as_slice() else {
            return Err(invalid());
        };
        let modifier = NodeRef::new(statement.arena, statement.file, *modifier);
        let modifier_node = preflight_node(store, host, modifier)?;
        if modifiers.flags.0 != 0
            || modifiers.list.has_trailing_comma
            || modifier_node.kind != SyntaxKind::DeclareKeyword
            || modifier_node.flags.0 != 0
            || modifier_node.parent != Some(statement.node)
            || !matches!(modifier_node.data, NodeData::Token(_))
        {
            return Err(invalid());
        }
    }
    if statement_node.parent != Some(bound.source_file().node)
        || bound
            .source_facts()
            .is_some_and(|facts| facts.is_external_module())
    {
        plan_global_variable_augmentation(store, host, symbol, declaration, statement)?;
    } else {
        let source = preflight_node(store, host, bound.source_file())?;
        if statement_node.parent != Some(bound.source_file().node)
            || !matches!(&source.data, NodeData::SourceFile(source)
                if source.statements.nodes.iter().filter(|&&node| node == statement.node).count() == 1)
            || bound.local_symbol(declaration).is_some()
        {
            return Err(invalid());
        }
    }
    Ok(if list_node.flags.0 == 0 {
        SymbolFlags::FUNCTION_SCOPED_VARIABLE
    } else {
        SymbolFlags::BLOCK_SCOPED_VARIABLE
    })
}

#[allow(clippy::too_many_lines)] // The raw export, local placeholder and global merge are distinct owners.
fn plan_global_variable_augmentation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
    statement: NodeRef,
) -> Result<(), DeclaredTypeError> {
    let invalid = || invalid_value(symbol);
    let bound = host.bound_file(declaration).ok_or_else(invalid)?;
    let owner = store.symbol(symbol).ok_or_else(invalid)?;
    let statement_node = preflight_node(store, host, statement)?;
    let block = statement_node
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(invalid)?;
    let block_node = preflight_node(store, host, block)?;
    let NodeData::ModuleBlock(block_data) = &block_node.data else {
        return Err(invalid());
    };
    let module = block_node
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(invalid)?;
    let module_node = preflight_node(store, host, module)?;
    let NodeData::ModuleDeclaration(module_data) = &module_node.data else {
        return Err(invalid());
    };
    plan_global_augmentation_parent(store, host, symbol, module)?;
    let name = NodeRef::new(module.arena, module.file, module_data.name);
    let namespace = bound
        .symbol(module)
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(invalid)?;
    let namespace_record = store.symbol(namespace).ok_or_else(invalid)?;
    let raw = bound.symbol(declaration).ok_or_else(invalid)?;
    let raw_record = store.symbol(raw).ok_or_else(invalid)?;
    let local = bound.local_symbol(declaration).ok_or_else(invalid)?;
    let local_record = store.symbol(local).ok_or_else(invalid)?;
    let declarations = owner.declarations().ok_or_else(invalid)?;
    let raw_declarations = declarations
        .iter()
        .copied()
        .filter(|&candidate| {
            candidate.is_for(declaration.arena, declaration.file)
                && bound.symbol(candidate) == Some(raw)
        })
        .collect::<Vec<_>>();
    let local_declarations = declarations
        .iter()
        .copied()
        .filter(|&candidate| {
            candidate.is_for(declaration.arena, declaration.file)
                && bound.local_symbol(candidate) == Some(local)
        })
        .collect::<Vec<_>>();
    let raw_value = raw_declarations
        .iter()
        .copied()
        .find(|&node| store.source_node_kind(node) == Some(SyntaxKind::VariableDeclaration));
    let raw_flags = SymbolFlags::FUNCTION_SCOPED_VARIABLE
        | if raw_declarations
            .iter()
            .any(|&node| store.source_node_kind(node) == Some(SyntaxKind::InterfaceDeclaration))
        {
            SymbolFlags::INTERFACE
        } else {
            SymbolFlags::NONE
        };
    if block_node.kind != SyntaxKind::ModuleBlock
        || block_data
            .statements
            .nodes
            .iter()
            .filter(|&&node| node == statement.node)
            .count()
            != 1
        || module_node.kind != SyntaxKind::ModuleDeclaration
        || module_data.keyword != SyntaxKind::GlobalKeyword
        || module_data.body != Some(block.node)
        || !bound
            .module_augmentations()
            .iter()
            .any(|augmentation| augmentation.name() == name)
        || store.source_identifier_text(name) != Some("global")
        || !namespace_record.flags().intersects(SymbolFlags::MODULE)
        || namespace_record.flags().without(SymbolFlags::TRANSIENT)
            != store.source_symbol_flags(namespace).ok_or_else(invalid)?
        || namespace_record.check_flags() != CheckFlags::NONE
        || namespace_record.name() != InternalSymbolName::Global.as_ref()
        || !store.source_symbol_declarations_match(namespace)
        || !store.source_symbol_export_table_matches(namespace)
        || !store.source_declaration_belongs_to_symbol(module, namespace)
        || namespace_record
            .exports()
            .and_then(|table| store.symbol_table(table))
            .and_then(|table| table.get(owner.name()))
            != Some(raw)
        || raw == symbol
        || store.get_merged_symbol(raw) != Some(symbol)
        || raw_record.flags() != raw_flags
        || raw_record.check_flags() != CheckFlags::NONE
        || raw_record.name() != owner.name()
        || raw_record.declarations() != Some(raw_declarations.as_slice())
        || raw_record.value_declaration() != raw_value
        || raw_record
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(namespace)
        || raw_record.exports().is_some()
        || raw_record.export_symbol().is_some()
        || !raw_flags.contains(SymbolFlags::INTERFACE) && raw_record.members().is_some()
        || local == raw
        || local == symbol
        || store.get_merged_symbol(local) != Some(local)
        || local_record.flags() != SymbolFlags::EXPORT_VALUE
        || local_record.check_flags() != CheckFlags::NONE
        || local_record.name() != owner.name()
        || local_declarations != raw_declarations
        || local_record.declarations() != Some(local_declarations.as_slice())
        || !store.source_symbol_declarations_match(local)
        || local_record.value_declaration().is_some()
        || local_record.parent().is_some()
        || local_record.members().is_some()
        || local_record.exports().is_some()
        || local_record.export_symbol() != Some(raw)
        || store
            .value_symbol_links(local)
            .is_some_and(|links| links != &ValueSymbolLinks::default())
    {
        return Err(invalid());
    }
    Ok(())
}

/// Checks the written ambient-module parent without querying a contributed value.
#[allow(clippy::too_many_lines)] // The syntax and raw binder module must agree before selecting its global scope.
fn plan_global_augmentation_parent(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    module: NodeRef,
) -> Result<(), DeclaredTypeError> {
    let invalid = || invalid_value(symbol);
    let bound = host.bound_file(module).ok_or_else(invalid)?;
    let source = bound.source_file();
    if !store.source_global_augmentation_parent_is_exact(module, source) {
        return Err(invalid());
    }
    let node = preflight_node(store, host, module)?;
    let NodeData::ModuleDeclaration(global) = &node.data else {
        return Err(invalid());
    };
    let name = NodeRef::new(module.arena, module.file, global.name);
    if global.keyword != SyntaxKind::GlobalKeyword
        || !bound
            .module_augmentations()
            .iter()
            .any(|origin| origin.name() == name)
    {
        return Err(invalid());
    }
    if node.parent == Some(source.node) {
        return Ok(());
    }
    let parent = NodeRef::new(module.arena, module.file, node.parent.ok_or_else(invalid)?);
    let parent_node = preflight_node(store, host, parent)?;
    let NodeData::ModuleBlock(block) = &parent_node.data else {
        return Err(invalid());
    };
    let outer = NodeRef::new(
        module.arena,
        module.file,
        parent_node.parent.ok_or_else(invalid)?,
    );
    let outer_node = preflight_node(store, host, outer)?;
    let NodeData::ModuleDeclaration(ambient) = &outer_node.data else {
        return Err(invalid());
    };
    let name = NodeRef::new(module.arena, module.file, ambient.name);
    let name_node = preflight_node(store, host, name)?;
    let NodeData::StringLiteral(literal) = &name_node.data else {
        return Err(invalid());
    };
    let raw = bound.symbol(outer).ok_or_else(invalid)?;
    let owner = store.get_merged_symbol(raw).ok_or_else(invalid)?;
    let outer_record = store.symbol(owner).ok_or_else(invalid)?;
    if outer_node.kind != SyntaxKind::ModuleDeclaration
        || outer_node.flags.0 != 0
        || outer_node.parent != Some(source.node)
        || ambient.keyword != SyntaxKind::ModuleKeyword
        || ambient.body != Some(parent.node)
        || ambient.symbol.is_some()
        || ambient.local_symbol.is_some()
        || ambient.facts != 0
        || ambient.asterisk_token.is_some()
        || ambient.flow_node.is_some()
        || ambient.end_flow_node.is_some()
        || ambient.next_container.is_some()
        || parent_node.flags.0 != 0
        || block
            .statements
            .nodes
            .iter()
            .filter(|&&child| child == module.node)
            .count()
            != 1
        || bound.container(module) != Some(outer)
        || bound.container(outer) != Some(source)
        || bound.local_symbol(outer).is_some()
        || store.source_declaration_symbol(outer) != Some(owner)
        || name_node.kind != SyntaxKind::StringLiteral
        || name_node.flags.0 != 0
        || name_node.parent != Some(outer.node)
        || literal.token_flags.0 != 0
        || literal.text.is_empty()
        || outer_record.name().as_utf8() != Some(format!("\"{}\"", literal.text).as_str())
    {
        return Err(invalid());
    }
    if let Some(modifiers) = &ambient.modifiers {
        let [modifier] = modifiers.list.nodes.as_slice() else {
            return Err(invalid());
        };
        let modifier = preflight_node(
            store,
            host,
            NodeRef::new(outer.arena, outer.file, *modifier),
        )?;
        if modifiers.flags.0 != 0
            || modifiers.list.has_trailing_comma
            || modifier.kind != SyntaxKind::DeclareKeyword
            || modifier.flags.0 != 0
            || modifier.parent != Some(outer.node)
            || !matches!(modifier.data, NodeData::Token(_))
        {
            return Err(invalid());
        }
    }
    Ok(())
}

fn global_callable_namespace_variable(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
    declaration: NodeRef,
    statement: NodeRef,
) -> bool {
    let Some(owner) = store.get_parent_of_symbol(symbol) else {
        return false;
    };
    if store
        .source_global_function_namespace_declarations(owner)
        .is_none()
    {
        return false;
    }
    let Some(bound) = host.bound_file(declaration) else {
        return false;
    };
    let Some(statement_node) = host.node(statement) else {
        return false;
    };
    let NodeData::VariableStatement(variable) = &statement_node.data else {
        return false;
    };
    let Some(block) = statement_node
        .parent
        .map(|node| NodeRef::new(statement.arena, statement.file, node))
    else {
        return false;
    };
    let Some(block_node) = host.node(block) else {
        return false;
    };
    let NodeData::ModuleBlock(block_data) = &block_node.data else {
        return false;
    };
    let Some(module) = block_node
        .parent
        .map(|node| NodeRef::new(block.arena, block.file, node))
    else {
        return false;
    };
    let Some(NodeData::ModuleDeclaration(module_data)) = host.node(module).map(|node| &node.data)
    else {
        return false;
    };
    statement_node.flags.0 == 0
        && variable.flow_node.is_none()
        && variable.facts == 0
        && module_data.body == Some(block.node)
        && bound.symbol(module).and_then(|raw| store.get_merged_symbol(raw)) == Some(owner)
        && block_data
            .statements
            .nodes
            .iter()
            .filter(|&&node| node == statement.node)
            .count() == 1
        && store.symbol(symbol).is_some_and(|value| {
            value.declarations() == Some(&[declaration])
                && bound.local_symbol(declaration).is_none_or(|local| {
                    store.symbol(local).is_some_and(|local| {
                        local.flags() == SymbolFlags::EXPORT_VALUE
                            && local.check_flags() == CheckFlags::NONE
                            && local.name() == value.name()
                            && local.declarations() == Some(&[declaration])
                            && local.value_declaration().is_none()
                            && local.parent().is_none()
                            && local.members().is_none()
                            && local.exports().is_none()
                            && local.export_symbol() == bound.symbol(declaration)
                    })
                })
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
    if !host.symbol_matches(store, parent, owner)
        || owner_record
            .declarations()
            .is_none_or(|declarations| !declarations.contains(&parent))
        || owner_record
            .members()
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get(record.name()))
            .and_then(|member| store.get_merged_symbol(member))
            != Some(symbol)
    {
        return Err(invalid());
    }
    match &parent_node.data {
        NodeData::InterfaceDeclaration(interface)
            if parent_node.kind == SyntaxKind::InterfaceDeclaration =>
        {
            if !owner_record.flags().contains(SymbolFlags::INTERFACE)
                || owner_record.flags().contains(SymbolFlags::CLASS)
                || interface
                    .members
                    .nodes
                    .iter()
                    .filter(|member| **member == declaration.node)
                    .count()
                    != 1
            {
                return Err(invalid());
            }
            preflight_class_or_interface_reference(store, host, owner, owner_record.flags())?;
        }
        NodeData::TypeLiteralNode(literal) if parent_node.kind == SyntaxKind::TypeLiteral => {
            let receiver = store
                .type_node_links(parent)
                .and_then(|links| links.resolved_type)
                .ok_or_else(|| unsupported_value(parent, parent_node.kind))?;
            let projection = source_property_object_projection(store, receiver)
                .map_err(|_| invalid())?
                .ok_or_else(|| unsupported_value(parent, parent_node.kind))?;
            if projection.type_() != projection.target()
                || projection.declaration() != parent
                || projection.source_symbol() != owner
                || literal
                    .members
                    .nodes
                    .iter()
                    .filter(|member| **member == declaration.node)
                    .count()
                    != 1
                || projection
                    .properties()
                    .iter()
                    .filter(|property| {
                        property.symbol == symbol
                            && property.declaration == declaration
                            && property.readonly == readonly
                            && property.optional == question.is_some()
                    })
                    .count()
                    != 1
            {
                return Err(invalid());
            }
            preflight_source_property_object_rhs(store, host, &projection, symbol)?;
        }
        _ => return Err(unsupported_value(parent, parent_node.kind)),
    }
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

fn preflight_property_object_alias_rhs(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    projection: &PropertyObjectAliasProjection,
    property: SemanticSymbolId,
) -> Result<(), DeclaredTypeError> {
    let invalid = || invalid_value(property);
    let mut current = projection.declaration;
    let mut seen = std::collections::HashSet::new();
    loop {
        if !seen.insert(current) {
            return Err(invalid());
        }
        let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(current) else {
            return Err(invalid());
        };
        let node = preflight_node(store, host, current)?;
        let parent_node = preflight_node(store, host, parent)?;
        if node.parent != Some(parent.node) {
            return Err(invalid());
        }
        match &parent_node.data {
            NodeData::ParenthesizedTypeNode(wrapper)
                if parent_node.kind == SyntaxKind::ParenthesizedType
                    && wrapper.type_ == current.node =>
            {
                current = parent;
            }
            NodeData::TypeAliasDeclaration(alias)
                if parent_node.kind == SyntaxKind::TypeAliasDeclaration
                    && alias.type_ == current.node
                    && host.symbol_matches(store, parent, projection.alias_symbol)
                    && store
                        .symbol(projection.alias_symbol)
                        .and_then(|symbol| symbol.declarations())
                        == Some(&[parent]) =>
            {
                return Ok(());
            }
            _ => return Err(invalid()),
        }
    }
}

fn preflight_source_property_object_rhs(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    projection: &SourcePropertyObjectProjection,
    property: SemanticSymbolId,
) -> Result<(), DeclaredTypeError> {
    if let Some(alias) = projection.as_direct_alias() {
        return preflight_property_object_alias_rhs(store, host, alias, property);
    }
    let invalid = || invalid_value(property);
    let mut current = projection.declaration();
    let mut seen = std::collections::HashSet::new();
    let mut intersection = false;
    loop {
        if !seen.insert(current) {
            return Err(invalid());
        }
        let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(current) else {
            return Err(invalid());
        };
        let node = preflight_node(store, host, current)?;
        let parent_node = preflight_node(store, host, parent)?;
        if node.parent != Some(parent.node) {
            return Err(invalid());
        }
        match &parent_node.data {
            NodeData::ParenthesizedTypeNode(wrapper)
                if parent_node.kind == SyntaxKind::ParenthesizedType
                    && wrapper.type_ == current.node =>
            {
                current = parent;
            }
            NodeData::IntersectionTypeNode(parts)
                if parent_node.kind == SyntaxKind::IntersectionType
                    && parts
                        .types
                        .nodes
                        .iter()
                        .filter(|&&child| child == current.node)
                        .count()
                        == 1 =>
            {
                for &child in &parts.types.nodes {
                    let child = NodeRef::new(parent.arena, parent.file, child);
                    if preflight_node(store, host, child)?.parent != Some(parent.node) {
                        return Err(invalid());
                    }
                }
                intersection = true;
                current = parent;
            }
            NodeData::UnionTypeNode(parts)
                if intersection
                    && parent_node.kind == SyntaxKind::UnionType
                    && parts
                        .types
                        .nodes
                        .iter()
                        .filter(|&&child| child == current.node)
                        .count()
                        == 1 =>
            {
                for &child in &parts.types.nodes {
                    let child = NodeRef::new(parent.arena, parent.file, child);
                    if preflight_node(store, host, child)?.parent != Some(parent.node) {
                        return Err(invalid());
                    }
                }
                current = parent;
            }
            NodeData::TypeAliasDeclaration(alias)
                if intersection
                    && parent_node.kind == SyntaxKind::TypeAliasDeclaration
                    && alias.type_ == current.node
                    && host.symbol_matches(store, parent, projection.parameter_owner())
                    && store
                        .symbol(projection.parameter_owner())
                        .and_then(|symbol| symbol.declarations())
                        == Some(&[parent]) =>
            {
                return Ok(());
            }
            _ => return Err(invalid()),
        }
    }
}

pub(super) enum SelectedDeclaredProperty {
    Missing,
    Unresolved(SemanticSymbolId),
    Resolved(ResolvedOwnProperty),
}

/// Reads one ordinary member from an interface or an exact source property object.
/// Generic instances retain their separate lazy member provider.
pub(super) fn selected_declared_property(
    store: &CanonicalTypeMapperStore,
    receiver: TypeId,
    name: EscapedNameRef<'_>,
) -> Result<Option<SelectedDeclaredProperty>, RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(receiver);
    let record = store
        .type_payload(receiver)
        .ok_or(RelationUnavailable::Type(receiver))?;
    if matches!(record.data(), TypeData::Object(_)) {
        let Some(projection) = source_property_object_projection(store, receiver)? else {
            return Ok(None);
        };
        if projection.type_() != projection.target() {
            return Ok(None);
        }
        let Some(index) = projection
            .properties()
            .iter()
            .position(|property| property.name.as_ref() == name)
        else {
            return Ok(Some(SelectedDeclaredProperty::Missing));
        };
        return selected_source_property_object_property(store, &projection, index).map(Some);
    }
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

/// Reads the original annotation cache without resolving any other property.
pub(super) fn selected_property_object_alias_property(
    store: &CanonicalTypeMapperStore,
    projection: &PropertyObjectAliasProjection,
    index: usize,
) -> Result<SelectedDeclaredProperty, RelationUnavailable> {
    selected_planned_declared_property(
        store,
        projection.target,
        projection.declaration,
        projection.source_symbol,
        &projection.properties,
        index,
    )
}

/// Reads a selected original property without changing its source-kind proof.
pub(super) fn selected_source_property_object_property(
    store: &CanonicalTypeMapperStore,
    projection: &SourcePropertyObjectProjection,
    index: usize,
) -> Result<SelectedDeclaredProperty, RelationUnavailable> {
    if let Some(alias) = projection.as_direct_alias() {
        return selected_property_object_alias_property(store, alias, index);
    }
    selected_planned_declared_property(
        store,
        projection.target(),
        projection.declaration(),
        projection.source_symbol(),
        projection.properties(),
        index,
    )
}

/// Checks one planned property's source and cached value after owner validation.
pub(super) fn selected_planned_declared_property(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    declaration: NodeRef,
    source_symbol: SemanticSymbolId,
    properties: &[PlannedProperty],
    index: usize,
) -> Result<SelectedDeclaredProperty, RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(target);
    let property = properties.get(index).ok_or_else(invalid)?;
    let symbol = store.symbol(property.symbol).ok_or_else(invalid)?;
    let expected_flags = SymbolFlags::PROPERTY
        | if property.optional {
            SymbolFlags::OPTIONAL
        } else {
            SymbolFlags::NONE
        };
    let expected_checks = if property.readonly {
        CheckFlags::READONLY
    } else {
        CheckFlags::NONE
    };
    if symbol.flags() != expected_flags
        || symbol.check_flags() != CheckFlags::NONE && symbol.check_flags() != expected_checks
        || symbol.name() != property.name.as_ref()
        || symbol.declarations() != Some(&[property.declaration])
        || symbol.value_declaration() != Some(property.declaration)
        || symbol.members().is_some()
        || symbol.exports().is_some()
        || symbol.export_symbol().is_some()
        || store.get_merged_symbol(property.symbol) != Some(property.symbol)
        || store.get_parent_of_symbol(property.symbol) != Some(source_symbol)
        || !matches!(
            store.source_node_kind(property.declaration),
            Some(SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature)
        )
        || store.source_node_parent(property.declaration)
            != Some(SourceNodeParent::Parent(declaration))
        || store.source_direct_type_annotation(property.declaration) != Some(property.type_node)
    {
        return Err(invalid());
    }
    let links = store
        .value_symbol_links(property.symbol)
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
        if store.declared_value_provenance(property.symbol).is_some() {
            return Err(invalid());
        }
        return Ok(SelectedDeclaredProperty::Unresolved(property.symbol));
    };
    if symbol.check_flags() != expected_checks
        || store.type_payload(type_).is_none()
        || !store.source_direct_type_annotation_is_exact(property.type_node, type_)
        || cached_planned_type_identity(store, property.type_node) != Some(type_)
        || store.source_type_operator(property.type_node) == Some(SyntaxKind::UniqueKeyword)
            && store.type_payload(type_).is_none_or(|record| {
                record.symbol() != Some(property.symbol)
                    || record.flags() != TypeFlags::UNIQUE_ES_SYMBOL
                    || record.object_flags() != ObjectFlags::NONE
                    || record.alias().is_some()
                    || !matches!(record.data(), TypeData::UniqueEsSymbol(_))
            })
    {
        return Err(invalid());
    }
    if let Some(provenance) = store.declared_value_provenance(property.symbol) {
        if provenance.annotation != property.type_node
            || provenance.readonly != Some(property.readonly)
            || !provenance.is_current(store, property.symbol)
        {
            return Err(invalid());
        }
    } else if !store.type_payload(target).is_some_and(|record| {
        record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
    }) || !matches!(
        validate_resolved_declared_property_object(store, target),
        DeclaredPropertyObjectValidation::Valid(DeclaredPropertyObjectProof::TypeLiteral)
    ) {
        return Err(invalid());
    }
    Ok(SelectedDeclaredProperty::Resolved(ResolvedOwnProperty {
        symbol: property.symbol,
        type_,
        optional: property.optional,
        readonly: property.readonly,
    }))
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
                && record
                    .flags()
                    .contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
                && (record.value_declaration() == Some(declaration)
                    || store
                        .source_global_interface_value_owner(owner)
                        .map_err(|_| invalid())?
                        .is_some_and(|proof| proof.variables().contains(&declaration)))
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
