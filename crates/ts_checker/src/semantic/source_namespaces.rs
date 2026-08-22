//! Canonical source planning for TypeScript namespaces and ambient modules.
//!
//! The binder already owns namespace symbols and export tables. This module
//! checks that graph without creating replacement symbols or accepting an
//! unsupported namespace member as a successful check.

use std::collections::HashSet;

use ts_ast::{ModifierList, Node, NodeArena, NodeData, NodeFlags, NodeRef, SyntaxKind};
use ts_binder::{BoundFile, SemanticSymbolId, SymbolFlags};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, DeclaredTypeUnavailable,
    SourceCheckError, SourceCheckProvenanceError, SourceSyntaxRole, UnsupportedSourceSyntax,
    ValueSymbolLinks, VariableInvariant, instantiate::InstantiationSession,
    type_nodes::CanonicalTypeQuery,
};

const ONLY_AMBIENT_MODULES_CAN_USE_QUOTED_NAMES: u32 = 1_035;
const AMBIENT_MODULES_CANNOT_BE_NESTED: u32 = 2_435;
const AMBIENT_MODULE_NAME_CANNOT_BE_RELATIVE: u32 = 2_436;
const GLOBAL_AUGMENTATION_CONTEXT: u32 = 2_669;
const GLOBAL_AUGMENTATION_DECLARE: u32 = 2_670;
const USE_NAMESPACE_KEYWORD: u32 = 1_540;

/// One checked declaration inside a namespace or ambient module.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum SourceNamespaceMemberPlan {
    Namespace(Box<SourceNamespacePlan>),
    TypeAlias {
        declaration: NodeRef,
        symbol: SemanticSymbolId,
        annotation: NodeRef,
    },
    Interface {
        declaration: NodeRef,
        symbol: SemanticSymbolId,
        annotations: Vec<NodeRef>,
    },
    #[allow(dead_code)] // Source dispatch still matches this pending enum implementation.
    EmptyEnum {
        declaration: NodeRef,
        symbol: SemanticSymbolId,
    },
    AmbientVariable {
        declaration: NodeRef,
        symbol: SemanticSymbolId,
        annotation: NodeRef,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NamespaceDiagnosticPlan {
    node: NodeRef,
    code: u32,
}

/// A complete, read-only namespace declaration and body plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceNamespacePlan {
    pub(super) declaration: NodeRef,
    pub(super) name: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) ambient: bool,
    pub(super) members: Vec<SourceNamespaceMemberPlan>,
    diagnostics: Vec<NamespaceDiagnosticPlan>,
}

#[derive(Clone, Copy)]
struct NamespaceParent {
    node: NodeRef,
    symbol: Option<SemanticSymbolId>,
    ambient: bool,
    ambient_module: bool,
}

#[derive(Clone, Copy)]
struct PendingNamespaceValue {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    type_: super::TypeId,
}

fn unsupported(node: NodeRef, kind: SyntaxKind, role: SourceSyntaxRole) -> SourceCheckError {
    SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax { node, kind, role })
}

fn missing_node(node: NodeRef) -> SourceCheckError {
    SourceCheckError::Provenance(SourceCheckProvenanceError::MissingNode(node))
}

fn invalid_parent(
    node: NodeRef,
    expected: NodeRef,
    actual: Option<ts_ast::NodeId>,
) -> SourceCheckError {
    SourceCheckError::Provenance(SourceCheckProvenanceError::InvalidParent {
        node,
        expected: Some(expected.node),
        actual,
    })
}

fn owned_node<'a>(
    arena: &'a NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<&'a Node, SourceCheckError> {
    if !node.is_for(arena.id(), bound.file_id()) || !bound.contains(node) {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::NodeNotBound(node),
        ));
    }
    if !store.contains_node_ref(node) {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::StoreSourceMismatch(super::SourceFileRef::new(
                store.id(),
                bound.source_file(),
            )),
        ));
    }
    arena.get(node.node).ok_or_else(|| missing_node(node))
}

fn child(parent: NodeRef, node: ts_ast::NodeId) -> NodeRef {
    NodeRef::new(parent.arena, parent.file, node)
}

fn declaration_symbol(
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    expected_flags: SymbolFlags,
) -> Result<SemanticSymbolId, SourceCheckError> {
    let raw = bound
        .symbol(declaration)
        .ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ))?;
    let symbol = store.get_merged_symbol(raw).ok_or_else(|| {
        SourceCheckError::DeclaredType(DeclaredTypeError::Unavailable(
            DeclaredTypeUnavailable::SymbolNotOwned(raw),
        ))
    })?;
    let record = store.symbol(symbol).ok_or_else(|| {
        SourceCheckError::DeclaredType(DeclaredTypeError::Unavailable(
            DeclaredTypeUnavailable::SymbolNotOwned(symbol),
        ))
    })?;
    if !record.flags().intersects(expected_flags)
        || record
            .declarations()
            .is_none_or(|declarations| !declarations.contains(&declaration))
    {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ));
    }
    Ok(symbol)
}

fn modifier_flags(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    owner: NodeRef,
    modifiers: Option<&ModifierList>,
) -> Result<(bool, bool), SourceCheckError> {
    let Some(modifiers) = modifiers else {
        return Ok((false, false));
    };
    if modifiers.list.has_trailing_comma {
        return Err(unsupported(
            owner,
            arena
                .get(owner.node)
                .map_or(SyntaxKind::Unknown, |node| node.kind),
            SourceSyntaxRole::Statement,
        ));
    }

    let mut exported = false;
    let mut declared = false;
    for modifier in &modifiers.list.nodes {
        let modifier = child(owner, *modifier);
        let record = owned_node(arena, bound, store, modifier)?;
        if record.parent != Some(owner.node) || !matches!(record.data, NodeData::Token(_)) {
            return Err(invalid_parent(modifier, owner, record.parent));
        }
        match record.kind {
            SyntaxKind::ExportKeyword if !exported => exported = true,
            SyntaxKind::DeclareKeyword if !declared => declared = true,
            _ => {
                return Err(unsupported(
                    modifier,
                    record.kind,
                    SourceSyntaxRole::Statement,
                ));
            }
        }
        if record.flags.0 != 0
            && !(record.kind == SyntaxKind::ExportKeyword
                && record.flags == NodeFlags::REPARSED
                && record.range.is_empty())
        {
            return Err(unsupported(
                modifier,
                record.kind,
                SourceSyntaxRole::Statement,
            ));
        }
    }
    Ok((exported, declared))
}

fn validate_symbol_parent(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    expected_parent: Option<SemanticSymbolId>,
) -> Result<(), SourceCheckError> {
    let record = store.symbol(symbol).ok_or_else(|| {
        SourceCheckError::DeclaredType(DeclaredTypeError::Unavailable(
            DeclaredTypeUnavailable::SymbolNotOwned(symbol),
        ))
    })?;
    if record.parent().is_none() {
        return Ok(());
    }
    let parent = store
        .get_parent_of_symbol(symbol)
        .ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ))?;
    let expected_parent = expected_parent.and_then(|parent| store.get_merged_symbol(parent));
    if Some(parent) != expected_parent
        || store
            .symbol(parent)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(record.name()))
            .and_then(|export| store.get_merged_symbol(export))
            != Some(symbol)
    {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ));
    }
    Ok(())
}

fn plan_interface_member(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    declaration: NodeRef,
) -> Result<SourceNamespaceMemberPlan, SourceCheckError> {
    let record = owned_node(arena, bound, store, declaration)?;
    let NodeData::InterfaceDeclaration(interface) = &record.data else {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MismatchedNodeData {
                node: declaration,
                kind: record.kind,
            },
        ));
    };
    if record.flags.0 != 0
        || interface.type_parameters.is_some()
        || interface.heritage_clauses.is_some()
        || interface.members.has_trailing_comma
    {
        let node = interface
            .heritage_clauses
            .as_ref()
            .and_then(|clauses| clauses.nodes.first())
            .copied()
            .map_or(declaration, |node| child(declaration, node));
        let kind = arena.get(node.node).map_or(record.kind, |node| node.kind);
        return Err(unsupported(
            node,
            kind,
            SourceSyntaxRole::InterfaceDeclaration,
        ));
    }
    modifier_flags(
        arena,
        bound,
        store,
        declaration,
        interface.modifiers.as_ref(),
    )?;
    let symbol = declaration_symbol(bound, store, declaration, SymbolFlags::INTERFACE)?;
    validate_symbol_parent(store, declaration, symbol, Some(owner))?;

    let mut annotations = Vec::new();
    let mut seen = HashSet::new();
    for member_id in &interface.members.nodes {
        let member = child(declaration, *member_id);
        let member_record = owned_node(arena, bound, store, member)?;
        if member_record.parent != Some(declaration.node) {
            return Err(invalid_parent(member, declaration, member_record.parent));
        }
        if !seen.insert(member) {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::RepeatedNode(member),
            ));
        }
        match &member_record.data {
            NodeData::PropertyDeclaration(property)
                if member_record.kind == SyntaxKind::PropertyDeclaration
                    && property.initializer.is_none() =>
            {
                let annotation = property.type_.ok_or_else(|| {
                    unsupported(
                        member,
                        member_record.kind,
                        SourceSyntaxRole::InterfaceDeclaration,
                    )
                })?;
                annotations.push(child(member, annotation));
            }
            NodeData::PropertySignatureDeclaration(property)
                if member_record.kind == SyntaxKind::PropertySignature =>
            {
                annotations.push(child(member, property.type_));
            }
            NodeData::IndexSignatureDeclaration(index)
                if member_record.kind == SyntaxKind::IndexSignature
                    && index.type_parameters.is_none()
                    && index.parameters.nodes.len() == 1 =>
            {
                let parameter = child(member, index.parameters.nodes[0]);
                let parameter_record = owned_node(arena, bound, store, parameter)?;
                let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
                    return Err(unsupported(
                        parameter,
                        parameter_record.kind,
                        SourceSyntaxRole::InterfaceDeclaration,
                    ));
                };
                let key = parameter_data.type_.ok_or_else(|| {
                    unsupported(
                        parameter,
                        parameter_record.kind,
                        SourceSyntaxRole::InterfaceDeclaration,
                    )
                })?;
                annotations.push(child(parameter, key));
                annotations.push(child(member, index.type_));
            }
            _ => {
                return Err(unsupported(
                    member,
                    member_record.kind,
                    SourceSyntaxRole::InterfaceDeclaration,
                ));
            }
        }
    }
    Ok(SourceNamespaceMemberPlan::Interface {
        declaration,
        symbol,
        annotations,
    })
}

fn plan_type_alias_member(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    declaration: NodeRef,
) -> Result<SourceNamespaceMemberPlan, SourceCheckError> {
    let record = owned_node(arena, bound, store, declaration)?;
    let NodeData::TypeAliasDeclaration(alias) = &record.data else {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MismatchedNodeData {
                node: declaration,
                kind: record.kind,
            },
        ));
    };
    modifier_flags(arena, bound, store, declaration, alias.modifiers.as_ref())?;
    let symbol = declaration_symbol(bound, store, declaration, SymbolFlags::TYPE_ALIAS)?;
    validate_symbol_parent(store, declaration, symbol, Some(owner))?;
    let annotation = child(declaration, alias.type_);
    let annotation_record = owned_node(arena, bound, store, annotation)?;
    if annotation_record.parent != Some(declaration.node) {
        return Err(invalid_parent(
            annotation,
            declaration,
            annotation_record.parent,
        ));
    }
    Ok(SourceNamespaceMemberPlan::TypeAlias {
        declaration,
        symbol,
        annotation,
    })
}

fn plan_namespace_variables(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    ambient: bool,
    statement: NodeRef,
    members: &mut Vec<SourceNamespaceMemberPlan>,
) -> Result<(), SourceCheckError> {
    let record = owned_node(arena, bound, store, statement)?;
    let NodeData::VariableStatement(variable) = &record.data else {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MismatchedNodeData {
                node: statement,
                kind: record.kind,
            },
        ));
    };
    let (_, declared) =
        modifier_flags(arena, bound, store, statement, variable.modifiers.as_ref())?;
    if !ambient && !declared {
        return Err(unsupported(
            statement,
            record.kind,
            SourceSyntaxRole::VariableStatement,
        ));
    }
    let list = child(statement, variable.declaration_list);
    let list_record = owned_node(arena, bound, store, list)?;
    let NodeData::VariableDeclarationList(declarations) = &list_record.data else {
        return Err(unsupported(
            list,
            list_record.kind,
            SourceSyntaxRole::VariableDeclarationList,
        ));
    };
    if list_record.parent != Some(statement.node) {
        return Err(invalid_parent(list, statement, list_record.parent));
    }
    for declaration in &declarations.declarations.nodes {
        let declaration = child(list, *declaration);
        let declaration_record = owned_node(arena, bound, store, declaration)?;
        let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
            return Err(unsupported(
                declaration,
                declaration_record.kind,
                SourceSyntaxRole::VariableDeclaration,
            ));
        };
        if declaration_record.parent != Some(list.node) {
            return Err(invalid_parent(declaration, list, declaration_record.parent));
        }
        if variable.initializer.is_some() {
            return Err(unsupported(
                declaration,
                declaration_record.kind,
                SourceSyntaxRole::VariableInitializer,
            ));
        }
        let annotation = variable.type_.ok_or(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::MissingVariableType(declaration),
        ))?;
        let annotation = child(declaration, annotation);
        let annotation_record = owned_node(arena, bound, store, annotation)?;
        if annotation_record.parent != Some(declaration.node) {
            return Err(invalid_parent(
                annotation,
                declaration,
                annotation_record.parent,
            ));
        }
        let symbol = declaration_symbol(bound, store, declaration, SymbolFlags::VARIABLE)?;
        validate_symbol_parent(store, declaration, symbol, Some(owner))?;
        if store.value_symbol_links(symbol).is_some_and(|links| {
            links.resolved_type.is_none() && links != &ValueSymbolLinks::default()
        }) {
            return Err(SourceCheckError::Variable(
                VariableInvariant::InvalidValueLinks(symbol),
            ));
        }
        members.push(SourceNamespaceMemberPlan::AmbientVariable {
            declaration,
            symbol,
            annotation,
        });
    }
    Ok(())
}

fn plan_namespace(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    parent: NamespaceParent,
) -> Result<SourceNamespacePlan, SourceCheckError> {
    let record = owned_node(arena, bound, store, declaration)?;
    if record.parent != Some(parent.node.node) {
        return Err(invalid_parent(declaration, parent.node, record.parent));
    }
    let NodeData::ModuleDeclaration(namespace) = &record.data else {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MismatchedNodeData {
                node: declaration,
                kind: record.kind,
            },
        ));
    };
    if record.kind != SyntaxKind::ModuleDeclaration
        || namespace.asterisk_token.is_some()
        || namespace.end_flow_node.is_some()
        || namespace.flow_node.is_some()
        || namespace.local_symbol.is_some()
        || namespace.symbol.is_some()
        || namespace.facts != 0
        || !matches!(
            namespace.keyword,
            SyntaxKind::NamespaceKeyword | SyntaxKind::ModuleKeyword | SyntaxKind::GlobalKeyword
        )
    {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    }
    let (_, declared) = modifier_flags(
        arena,
        bound,
        store,
        declaration,
        namespace.modifiers.as_ref(),
    )?;
    let facts = bound.source_facts().ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingSourceFacts(declaration.file),
    ))?;
    let ambient = parent.ambient || declared || facts.is_declaration_file();
    let name = child(declaration, namespace.name);
    let name_record = owned_node(arena, bound, store, name)?;
    if name_record.parent != Some(declaration.node) {
        return Err(invalid_parent(name, declaration, name_record.parent));
    }
    let is_string_module = matches!(&name_record.data, NodeData::StringLiteral(_));
    let is_global_augmentation = namespace.keyword == SyntaxKind::GlobalKeyword;
    if !matches!(
        &name_record.data,
        NodeData::Identifier(_) | NodeData::StringLiteral(_)
    ) || is_global_augmentation && !matches!(&name_record.data, NodeData::Identifier(_))
    {
        return Err(unsupported(
            name,
            name_record.kind,
            SourceSyntaxRole::Statement,
        ));
    }

    let symbol = declaration_symbol(bound, store, declaration, SymbolFlags::MODULE)?;
    let expected_parent = parent.symbol.or_else(|| {
        (parent.node == bound.source_file())
            .then(|| bound.symbol(parent.node))
            .flatten()
    });
    validate_symbol_parent(store, declaration, symbol, expected_parent)?;

    let mut diagnostics = Vec::new();
    if is_string_module && !ambient {
        diagnostics.push(NamespaceDiagnosticPlan {
            node: name,
            code: ONLY_AMBIENT_MODULES_CAN_USE_QUOTED_NAMES,
        });
    }
    if namespace.keyword == SyntaxKind::ModuleKeyword
        && matches!(&name_record.data, NodeData::Identifier(_))
    {
        diagnostics.push(NamespaceDiagnosticPlan {
            node: name,
            code: USE_NAMESPACE_KEYWORD,
        });
    }
    if is_global_augmentation {
        if !ambient {
            diagnostics.push(NamespaceDiagnosticPlan {
                node: name,
                code: GLOBAL_AUGMENTATION_DECLARE,
            });
        }
        if !facts.is_external_module() && !parent.ambient_module {
            diagnostics.push(NamespaceDiagnosticPlan {
                node: name,
                code: GLOBAL_AUGMENTATION_CONTEXT,
            });
        }
    }
    if let NodeData::StringLiteral(module_name) = &name_record.data {
        if parent.symbol.is_some() && !parent.ambient_module {
            diagnostics.push(NamespaceDiagnosticPlan {
                node: name,
                code: AMBIENT_MODULES_CANNOT_BE_NESTED,
            });
        } else if !facts.is_external_module()
            && parent.node == bound.source_file()
            && (ts_path::is_relative(&module_name.text)
                || ts_path::is_rooted_disk_path(&module_name.text))
        {
            diagnostics.push(NamespaceDiagnosticPlan {
                node: name,
                code: AMBIENT_MODULE_NAME_CANNOT_BE_RELATIVE,
            });
        }
    }

    let mut members = Vec::new();
    if let Some(body) = namespace.body {
        let body = child(declaration, body);
        let body_record = owned_node(arena, bound, store, body)?;
        if body_record.parent != Some(declaration.node) {
            return Err(invalid_parent(body, declaration, body_record.parent));
        }
        match &body_record.data {
            NodeData::ModuleDeclaration(_) if body_record.kind == SyntaxKind::ModuleDeclaration => {
                let nested = plan_namespace(
                    arena,
                    bound,
                    store,
                    body,
                    NamespaceParent {
                        node: declaration,
                        symbol: Some(symbol),
                        ambient,
                        ambient_module: is_string_module || is_global_augmentation,
                    },
                )?;
                members.push(SourceNamespaceMemberPlan::Namespace(Box::new(nested)));
            }
            NodeData::ModuleBlock(block) if body_record.kind == SyntaxKind::ModuleBlock => {
                if block.facts != 0 || block.statements.has_trailing_comma {
                    return Err(unsupported(
                        body,
                        body_record.kind,
                        SourceSyntaxRole::Statement,
                    ));
                }
                let mut seen = HashSet::new();
                for statement_id in &block.statements.nodes {
                    let statement = child(body, *statement_id);
                    let statement_record = owned_node(arena, bound, store, statement)?;
                    if statement_record.parent != Some(body.node) {
                        return Err(invalid_parent(statement, body, statement_record.parent));
                    }
                    if !seen.insert(statement) {
                        return Err(SourceCheckError::Provenance(
                            SourceCheckProvenanceError::RepeatedNode(statement),
                        ));
                    }
                    match statement_record.kind {
                        SyntaxKind::ModuleDeclaration => {
                            let nested = plan_namespace(
                                arena,
                                bound,
                                store,
                                statement,
                                NamespaceParent {
                                    node: body,
                                    symbol: Some(symbol),
                                    ambient,
                                    ambient_module: is_string_module || is_global_augmentation,
                                },
                            )?;
                            members.push(SourceNamespaceMemberPlan::Namespace(Box::new(nested)));
                        }
                        SyntaxKind::TypeAliasDeclaration => {
                            members.push(plan_type_alias_member(
                                arena, bound, store, symbol, statement,
                            )?);
                        }
                        SyntaxKind::InterfaceDeclaration => {
                            members.push(plan_interface_member(
                                arena, bound, store, symbol, statement,
                            )?);
                        }
                        SyntaxKind::EnumDeclaration => {
                            return Err(SourceCheckError::Unsupported(
                                UnsupportedSourceSyntax::Enum(statement),
                            ));
                        }
                        SyntaxKind::VariableStatement => {
                            plan_namespace_variables(
                                arena,
                                bound,
                                store,
                                symbol,
                                ambient,
                                statement,
                                &mut members,
                            )?;
                        }
                        SyntaxKind::EmptyStatement => {}
                        kind => {
                            return Err(unsupported(statement, kind, SourceSyntaxRole::Statement));
                        }
                    }
                }
            }
            _ => {
                return Err(unsupported(
                    body,
                    body_record.kind,
                    SourceSyntaxRole::Statement,
                ));
            }
        }
    }

    Ok(SourceNamespacePlan {
        declaration,
        name,
        symbol,
        ambient,
        members,
        diagnostics,
    })
}

/// Plans one complete top-level namespace without changing checker state.
pub(super) fn plan_source_namespace(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> Result<SourceNamespacePlan, SourceCheckError> {
    let source = bound.source_file();
    owned_node(arena, bound, store, source)?;
    plan_namespace(
        arena,
        bound,
        store,
        declaration,
        NamespaceParent {
            node: source,
            symbol: None,
            ambient: bound
                .source_facts()
                .is_some_and(ts_binder::CanonicalSourceFileFacts::is_declaration_file),
            ambient_module: false,
        },
    )
}

fn namespace_annotations<'plan>(
    plan: &'plan SourceNamespacePlan,
    annotations: &mut Vec<NodeRef>,
    declarations: &mut Vec<&'plan SourceNamespaceMemberPlan>,
    diagnostics: &mut Vec<NamespaceDiagnosticPlan>,
) {
    for member in &plan.members {
        match member {
            SourceNamespaceMemberPlan::Namespace(namespace) => {
                namespace_annotations(namespace, annotations, declarations, diagnostics);
            }
            SourceNamespaceMemberPlan::TypeAlias { annotation, .. }
            | SourceNamespaceMemberPlan::AmbientVariable { annotation, .. } => {
                annotations.push(*annotation);
                declarations.push(member);
            }
            SourceNamespaceMemberPlan::Interface {
                annotations: interface_annotations,
                ..
            } => {
                annotations.extend(interface_annotations);
                declarations.push(member);
            }
            SourceNamespaceMemberPlan::EmptyEnum { .. } => declarations.push(member),
        }
    }
    diagnostics.extend(plan.diagnostics.iter().copied());
}

/// Executes a validated namespace and publishes ambient values atomically.
#[allow(clippy::too_many_arguments)] // Mirrors the canonical source-checker query context.
pub(super) fn execute_source_namespace(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &SourceNamespacePlan,
) -> Result<(), SourceCheckError> {
    let (arena, bound) = host
        .source(plan.declaration)
        .ok_or_else(|| missing_node(plan.declaration))?;
    if plan_source_namespace(arena, bound, store, plan.declaration)? != *plan {
        return Err(unsupported(
            plan.declaration,
            SyntaxKind::ModuleDeclaration,
            SourceSyntaxRole::Statement,
        ));
    }

    let mut annotations = Vec::new();
    let mut declarations = Vec::new();
    let mut planned_diagnostics = Vec::new();
    namespace_annotations(
        plan,
        &mut annotations,
        &mut declarations,
        &mut planned_diagnostics,
    );
    for diagnostic in &planned_diagnostics {
        if message_by_code(diagnostic.code).is_none() {
            return Err(SourceCheckError::MissingDiagnostic(diagnostic.code));
        }
    }

    for annotation in annotations {
        session.reset_query();
        let mut staged = CanonicalCheckerDiagnostics::default();
        CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            global_types,
            options,
            session,
            &mut staged,
        )?
        .preflight_type_from_type_node(annotation)?;
        debug_assert!(staged.is_empty());
    }

    let mut values = Vec::<PendingNamespaceValue>::new();
    for declaration in declarations {
        session.reset_query();
        match declaration {
            SourceNamespaceMemberPlan::TypeAlias { symbol, .. } => {
                CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                )?
                .get_declared_type_of_symbol(*symbol)?;
            }
            SourceNamespaceMemberPlan::Interface { symbol, .. } => {
                CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                )?
                .get_declared_type_of_symbol(*symbol)?;
            }
            SourceNamespaceMemberPlan::AmbientVariable {
                declaration,
                symbol,
                annotation,
            } => {
                let type_ = CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                )?
                .get_type_from_type_node(*annotation)?;
                if let Some(existing) = values.iter().find(|value| value.symbol == *symbol) {
                    if existing.type_ != type_ {
                        return Err(SourceCheckError::Variable(
                            VariableInvariant::CachedValueTypeMismatch {
                                symbol: *symbol,
                                cached: existing.type_,
                                expected: type_,
                            },
                        ));
                    }
                    continue;
                }
                if let Some(existing) = store.value_symbol_links(*symbol)
                    && existing != &ValueSymbolLinks::default()
                    && existing
                        != &(ValueSymbolLinks {
                            resolved_type: Some(type_),
                            ..ValueSymbolLinks::default()
                        })
                {
                    return Err(SourceCheckError::Variable(
                        VariableInvariant::CachedValueTypeMismatch {
                            symbol: *symbol,
                            cached: existing.resolved_type.unwrap_or(type_),
                            expected: type_,
                        },
                    ));
                }
                values.push(PendingNamespaceValue {
                    declaration: *declaration,
                    symbol: *symbol,
                    type_,
                });
            }
            SourceNamespaceMemberPlan::Namespace(_) => {
                unreachable!("nested namespaces are expanded before semantic execution")
            }
            SourceNamespaceMemberPlan::EmptyEnum { .. } => {}
        }
    }

    let missing_value_links = values
        .iter()
        .filter(|value| store.value_symbol_links(value.symbol).is_none())
        .count();
    if !store.try_reserve_value_symbol_links(missing_value_links) {
        return Err(SourceCheckError::Variable(
            VariableInvariant::InvalidValueLinks(plan.symbol),
        ));
    }
    for value in values {
        let expected = ValueSymbolLinks {
            resolved_type: Some(value.type_),
            ..ValueSymbolLinks::default()
        };
        if store.value_symbol_links(value.symbol) != Some(&expected)
            && !store.set_value_symbol_links(value.symbol, expected)
        {
            return Err(SourceCheckError::Variable(
                VariableInvariant::ValueTypePublication(value.symbol),
            ));
        }
        debug_assert!(bound.contains(value.declaration));
    }
    for diagnostic in planned_diagnostics {
        let message = message_by_code(diagnostic.code)
            .ok_or(SourceCheckError::MissingDiagnostic(diagnostic.code))?;
        super::source::merge_retry_diagnostic(
            diagnostics,
            super::CanonicalCheckerDiagnostic {
                node: Some(diagnostic.node),
                range_override: None,
                diagnostic: Diagnostic::new(message),
                related_information: Vec::new(),
            },
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext,
        instantiate::{InstantiationLimits, InstantiationSession},
    };

    struct Fixture {
        parsed: &'static ParseResult,
        file: FileId,
        context: CanonicalCheckerContext<'static>,
    }

    fn fixture(source: &'static str, module_state: CanonicalModuleState) -> Fixture {
        let parsed: &'static ParseResult = Box::leak(Box::new(parse_source_file(source)));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(7_401);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/namespaces.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        );
        let context = context.unwrap();
        Fixture {
            parsed,
            file,
            context,
        }
    }

    fn declaration(fixture: &Fixture, index: usize) -> NodeRef {
        let (arena, bound) = fixture.context.file(fixture.file).unwrap();
        let source = arena.get(bound.source_file().node).unwrap();
        let NodeData::SourceFile(source) = &source.data else {
            panic!("namespace fixture must have a source-file root")
        };
        child(bound.source_file(), source.statements.nodes[index])
    }

    fn plan(fixture: &Fixture, index: usize) -> SourceNamespacePlan {
        let declaration = declaration(fixture, index);
        let (arena, bound) = fixture.context.file(fixture.file).unwrap();
        plan_source_namespace(arena, bound, fixture.context.store(), declaration).unwrap()
    }

    fn execute(
        fixture: &mut Fixture,
        plan: &SourceNamespacePlan,
    ) -> Result<CanonicalCheckerDiagnostics, SourceCheckError> {
        let bound = fixture.context.file(fixture.file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([(&fixture.parsed.arena, &bound)]).unwrap();
        let global_types = fixture.context.global_types().clone();
        let options = fixture.context.options();
        let store = fixture.context.store_mut_for_test();
        let error_type = store.intrinsic_bootstrap().unwrap().error_type;
        let mut session =
            InstantiationSession::new_recovering(store, InstantiationLimits::default(), error_type)
                .unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        execute_source_namespace(
            store,
            &host,
            &global_types,
            options,
            &mut session,
            &mut diagnostics,
            plan,
        )?;
        Ok(diagnostics)
    }

    #[test]
    fn empty_namespace_plans_without_checker_publication() {
        let mut fixture = fixture("namespace Values {}", CanonicalModuleState::Script);
        let plan = plan(&fixture, 0);
        assert!(!plan.ambient);
        assert!(plan.members.is_empty());
        let initial = (
            fixture.context.store().type_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );
        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            ),
            initial,
        );
    }

    #[test]
    fn dotted_namespaces_keep_nested_binder_symbols() {
        let fixture = fixture(
            "namespace Root.Middle.Leaf {}",
            CanonicalModuleState::Script,
        );
        let outer = plan(&fixture, 0);
        let [SourceNamespaceMemberPlan::Namespace(middle)] = outer.members.as_slice() else {
            panic!("the first dotted namespace must retain its nested declaration")
        };
        let [SourceNamespaceMemberPlan::Namespace(leaf)] = middle.members.as_slice() else {
            panic!("the second dotted namespace must retain its nested declaration")
        };
        assert!(leaf.members.is_empty());
        assert_ne!(outer.symbol, middle.symbol);
        assert_ne!(middle.symbol, leaf.symbol);
    }

    #[test]
    fn ambient_jsx_namespace_keeps_interface_members_lazy() {
        let mut fixture = fixture(
            "declare namespace JSX { interface Element {} interface IntrinsicElements { div: any; } }",
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        assert!(plan.ambient);
        assert!(matches!(
            plan.members.as_slice(),
            [
                SourceNamespaceMemberPlan::Interface { .. },
                SourceNamespaceMemberPlan::Interface { .. }
            ]
        ));
        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
    }

    #[test]
    fn reopened_ambient_modules_publish_each_typed_variable() {
        let mut fixture = fixture(
            "declare module \"fs\" { var x: string; } declare module 'fs' { var y: number; }",
            CanonicalModuleState::Script,
        );
        let first = plan(&fixture, 0);
        let second = plan(&fixture, 1);
        assert_eq!(first.symbol, second.symbol);
        assert!(execute(&mut fixture, &first).unwrap().is_empty());
        assert!(execute(&mut fixture, &second).unwrap().is_empty());
        for member in first.members.iter().chain(&second.members) {
            let SourceNamespaceMemberPlan::AmbientVariable { symbol, .. } = member else {
                panic!("ambient module bodies must retain their variable members")
            };
            assert!(
                fixture
                    .context
                    .store()
                    .value_symbol_links(*symbol)
                    .and_then(|links| links.resolved_type)
                    .is_some()
            );
        }
    }

    #[test]
    fn relative_ambient_module_name_reports_pinned_ts2436() {
        let mut fixture = fixture(
            "declare module \"./relative\" { var value: string; }",
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let diagnostics = execute(&mut fixture, &plan).unwrap();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2436);
        assert_eq!(diagnostics.as_slice()[0].node, Some(plan.name));
    }

    #[test]
    fn module_keyword_on_identifier_reports_pinned_ts1540() {
        let mut fixture = fixture("module Legacy {}", CanonicalModuleState::Script);
        let plan = plan(&fixture, 0);
        let diagnostics = execute(&mut fixture, &plan).unwrap();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 1540);
        assert_eq!(diagnostics.as_slice()[0].node, Some(plan.name));
    }

    #[test]
    fn script_global_augmentation_reports_pinned_ts2669() {
        let mut fixture = fixture(
            "declare global { interface Window {} }",
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let diagnostics = execute(&mut fixture, &plan).unwrap();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2669);
    }

    #[test]
    fn nested_empty_enums_remain_typed_capability_boundaries() {
        let fixture = fixture(
            "declare namespace JSX { enum ElementType {} }",
            CanonicalModuleState::Script,
        );
        let declaration = declaration(&fixture, 0);
        let (arena, bound) = fixture.context.file(fixture.file).unwrap();
        let before = fixture.context.store().checker_link_allocated_lengths();
        let result = plan_source_namespace(arena, bound, fixture.context.store(), declaration);
        assert!(matches!(
            result,
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Enum(_)
            ))
        ));
        assert_eq!(
            fixture.context.store().checker_link_allocated_lengths(),
            before
        );
    }

    #[test]
    fn unsupported_later_member_cannot_publish_earlier_values() {
        let fixture = fixture(
            "declare namespace N { var value: string; function next(): void; }",
            CanonicalModuleState::Script,
        );
        let declaration = declaration(&fixture, 0);
        let (arena, bound) = fixture.context.file(fixture.file).unwrap();
        let before = fixture.context.store().checker_link_allocated_lengths();
        let result = plan_source_namespace(arena, bound, fixture.context.store(), declaration);
        assert!(matches!(
            result,
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Syntax {
                    kind: SyntaxKind::FunctionDeclaration,
                    ..
                }
            ))
        ));
        assert_eq!(
            fixture.context.store().checker_link_allocated_lengths(),
            before
        );
    }
}
