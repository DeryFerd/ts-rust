//! Canonical source planning for TypeScript namespaces and ambient modules.
//!
//! The binder already owns namespace symbols and export tables. This module
//! checks that graph without creating replacement symbols or accepting an
//! unsupported namespace member as a successful check.

use std::collections::HashSet;

use ts_ast::{ModifierList, Node, NodeArena, NodeData, NodeFlags, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CheckFlags, EscapedName, InternalSymbolName,
    SemanticSymbolId, SymbolFlags, SymbolTableId, canonical_has_syntactic_modifier,
    semantic::PreparedSymbolTable,
};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    AliasTargetState, CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, DeclaredTypeUnavailable,
    SourceAssertionError, SourceCheckError, SourceCheckProvenanceError, SourceFunctionInvariant,
    SourceLiteralCacheError, SourceObjectLiteralError, SourceSyntaxRole, SymbolNodeLinks, TypeData,
    TypeId, TypeMapper, TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
    VariableInvariant,
    alias::{
        CanonicalAliasResolutionEvent, CanonicalAliasResolver, CanonicalAliasTargetHost,
        CanonicalAliasTargetUnavailable, CanonicalImmediateAliasTarget,
    },
    array_types::CanonicalArrayTargets,
    bootstrap::UnionReduction,
    declared::cached_ordinary_type_parameter_owner,
    instantiate::InstantiationSession,
    object_members::{self, PropertyObjectError, PropertyObjectPlan},
    reference_types::validate_direct_generic_reference,
    source_callables::{self, SourceCallableError},
    type_nodes::{CanonicalTypeQuery, TypeNodeUnavailable, normalize_numeric_separators},
    types::{ObjectFlags, TypeFlags},
};

const ONLY_AMBIENT_MODULES_CAN_USE_QUOTED_NAMES: u32 = 1_035;
const AMBIENT_MODULES_CANNOT_BE_NESTED: u32 = 2_435;
const AMBIENT_MODULE_NAME_CANNOT_BE_RELATIVE: u32 = 2_436;
const GLOBAL_AUGMENTATION_CONTEXT: u32 = 2_669;
const GLOBAL_AUGMENTATION_DECLARE: u32 = 2_670;
const AMBIENT_EXPORT_ASSIGNMENT_MUST_BE_ENTITY_NAME: u32 = 2_714;
const USE_NAMESPACE_KEYWORD: u32 = 1_540;
const CIRCULAR_DEFINITION_OF_IMPORT_ALIAS: u32 = 2_303;
const VARIABLE_IMPLICITLY_HAS_ANY_TYPE: u32 = 7_005;
const NODE_FLAG_LET: u32 = 1 << 0;
const NODE_FLAG_CONST: u32 = 1 << 1;

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
        generic: Option<SourceNamespaceGenericInterfacePlan>,
    },
    EmptyEnum {
        declaration: NodeRef,
        symbol: SemanticSymbolId,
    },
    Function {
        declaration: NodeRef,
        symbol: SemanticSymbolId,
    },
    AmbientVariable {
        declaration: NodeRef,
        symbol: SemanticSymbolId,
        annotation: NodeRef,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceNamespaceGenericInterfacePlan {
    members: SymbolTableId,
    type_parameters: Vec<SemanticSymbolId>,
    properties: Vec<SourceNamespacePropertyPlan>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceNamespacePropertyPlan {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    name: String,
    annotation: NodeRef,
    optional: bool,
    readonly: bool,
}

#[derive(Clone, Copy)]
struct SourceNamespacePropertySyntax<'a> {
    name: ts_ast::NodeId,
    annotation: NodeRef,
    postfix_token: Option<ts_ast::NodeId>,
    modifiers: Option<&'a ModifierList>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NamespaceDiagnosticPlan {
    node: NodeRef,
    code: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceNamespaceImportPlan {
    declaration: NodeRef,
    name_text: String,
    symbol: SemanticSymbolId,
    reference: NodeRef,
    ambient_target: Option<SemanticSymbolId>,
    type_only: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceNamespaceImplicitVariablePlan {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    name: String,
    primary_declaration: bool,
    initializer: Option<NodeRef>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SourceNamespaceAmbientInitializer {
    String(String),
    EnumMember {
        owner: SemanticSymbolId,
        member: SemanticSymbolId,
        receiver: NodeRef,
        name: NodeRef,
        key: Option<String>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceNamespaceAmbientVariablePlan {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    initializer: NodeRef,
    value: SourceNamespaceAmbientInitializer,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceNamespaceObjectInitializerPlan {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    interface: SemanticSymbolId,
    annotation: NodeRef,
    object: PropertyObjectPlan,
}

struct NamespaceVariablePlans<'a> {
    members: &'a mut Vec<SourceNamespaceMemberPlan>,
    implicit_variables: &'a mut Vec<SourceNamespaceImplicitVariablePlan>,
    ambient_variables: &'a mut Vec<SourceNamespaceAmbientVariablePlan>,
    object_initializers: &'a mut Vec<SourceNamespaceObjectInitializerPlan>,
    diagnostics: &'a mut Vec<NamespaceDiagnosticPlan>,
}

/// A complete, read-only namespace declaration and body plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceNamespacePlan {
    pub(super) declaration: NodeRef,
    pub(super) name: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) ambient: bool,
    pub(super) members: Vec<SourceNamespaceMemberPlan>,
    imports: Vec<SourceNamespaceImportPlan>,
    implicit_variables: Vec<SourceNamespaceImplicitVariablePlan>,
    ambient_variables: Vec<SourceNamespaceAmbientVariablePlan>,
    object_initializers: Vec<SourceNamespaceObjectInitializerPlan>,
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

#[derive(Clone, Copy)]
struct ResolvedNamespaceImport<'plan> {
    import: &'plan SourceNamespaceImportPlan,
    target: SemanticSymbolId,
}

struct NamespaceAliasTargetHost<'plan> {
    imports: Vec<ResolvedNamespaceImport<'plan>>,
}

impl CanonicalAliasTargetHost<TypeMapper> for NamespaceAliasTargetHost<'_> {
    fn get_target_of_alias_declaration(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        alias: SemanticSymbolId,
    ) -> Result<CanonicalImmediateAliasTarget, CanonicalAliasTargetUnavailable> {
        let Some(resolved) = self
            .imports
            .iter()
            .find(|import| import.import.symbol == alias)
        else {
            return Err(CanonicalAliasTargetUnavailable::UnsupportedDeclarationFamily);
        };
        if store.symbol(resolved.target).is_none() {
            return Err(CanonicalAliasTargetUnavailable::MalformedDeclaration(
                resolved.import.declaration,
            ));
        }
        if resolved.import.type_only {
            let mut links = store
                .alias_symbol_links(alias)
                .cloned()
                .ok_or(CanonicalAliasTargetUnavailable::InvalidAliasLinks(alias))?;
            if links.type_only_declaration.is_none() {
                links.type_only_declaration = Some(resolved.import.declaration);
                if !store.set_alias_symbol_links(alias, links) {
                    return Err(CanonicalAliasTargetUnavailable::InvalidAliasLinks(alias));
                }
            }
        }
        Ok(CanonicalImmediateAliasTarget::Resolved(resolved.target))
    }
}

fn is_external_module_augmentation(
    arena: &NodeArena,
    bound: &BoundFile,
    name: NodeRef,
    parent: NamespaceParent,
) -> bool {
    if bound
        .module_augmentations()
        .iter()
        .any(|augmentation| augmentation.name() == name)
    {
        return true;
    }

    let Some(facts) = bound.source_facts() else {
        return false;
    };
    if parent.node == bound.source_file() {
        return facts.is_external_module();
    }
    if facts.is_external_module() || !parent.ambient_module {
        return false;
    }

    let Some(block) = arena.get(parent.node.node) else {
        return false;
    };
    if block.kind != SyntaxKind::ModuleBlock {
        return false;
    }
    block
        .parent
        .and_then(|module| arena.get(module))
        .is_some_and(|module| {
            module.kind == SyntaxKind::ModuleDeclaration
                && module.parent == Some(bound.source_file().node)
        })
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
    let symbol = store
        .get_merged_symbol(raw)
        .ok_or(SourceCheckError::DeclaredType(
            DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(raw)),
        ))?;
    let record = store.symbol(symbol).ok_or(SourceCheckError::DeclaredType(
        DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol)),
    ))?;
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
    let record = store.symbol(symbol).ok_or(SourceCheckError::DeclaredType(
        DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol)),
    ))?;
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

fn plan_generic_interface_parameters(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    parameters: &ts_ast::NodeList,
    annotations: &mut Vec<NodeRef>,
) -> Result<SourceNamespaceGenericInterfacePlan, SourceCheckError> {
    if parameters.nodes.is_empty() {
        return Err(unsupported(
            declaration,
            SyntaxKind::InterfaceDeclaration,
            SourceSyntaxRole::InterfaceDeclaration,
        ));
    }
    let members = store
        .symbol(symbol)
        .and_then(ts_binder::semantic::Symbol::members)
        .ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ))?;
    let table = store
        .symbol_table(members)
        .ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ))?;
    let mut type_parameters = Vec::with_capacity(parameters.nodes.len());
    let mut seen = HashSet::with_capacity(parameters.nodes.len());
    for parameter_id in &parameters.nodes {
        let parameter = child(declaration, *parameter_id);
        let record = owned_node(arena, bound, store, parameter)?;
        let NodeData::TypeParameterDeclaration(data) = &record.data else {
            return Err(unsupported(
                parameter,
                record.kind,
                SourceSyntaxRole::InterfaceDeclaration,
            ));
        };
        if record.kind != SyntaxKind::TypeParameter
            || record.parent != Some(declaration.node)
            || data.expression.is_some()
            || data.modifiers.is_some()
        {
            return Err(unsupported(
                parameter,
                record.kind,
                SourceSyntaxRole::InterfaceDeclaration,
            ));
        }
        let parameter_symbol =
            declaration_symbol(bound, store, parameter, SymbolFlags::TYPE_PARAMETER)?;
        let parameter_record =
            store
                .symbol(parameter_symbol)
                .ok_or(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::MissingDeclarationSymbol(parameter),
                ))?;
        if parameter_record.flags() != SymbolFlags::TYPE_PARAMETER
            || store.get_parent_of_symbol(parameter_symbol) != Some(symbol)
            || table.get(parameter_record.name()) != Some(parameter_symbol)
            || !seen.insert(parameter_symbol)
        {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingDeclarationSymbol(parameter),
            ));
        }
        type_parameters.push(parameter_symbol);
        for annotation in [data.constraint, data.default_type].into_iter().flatten() {
            let annotation = child(parameter, annotation);
            let annotation_record = owned_node(arena, bound, store, annotation)?;
            if annotation_record.parent != Some(parameter.node) {
                return Err(invalid_parent(
                    annotation,
                    parameter,
                    annotation_record.parent,
                ));
            }
            annotations.push(annotation);
        }
    }
    Ok(SourceNamespaceGenericInterfacePlan {
        members,
        type_parameters,
        properties: Vec::new(),
    })
}

fn plan_generic_interface_property(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    members: SymbolTableId,
    declaration: NodeRef,
    syntax: SourceNamespacePropertySyntax<'_>,
) -> Result<SourceNamespacePropertyPlan, SourceCheckError> {
    let name = child(declaration, syntax.name);
    let name_record = owned_node(arena, bound, store, name)?;
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
            if name_record.kind == SyntaxKind::NoSubstitutionTemplateLiteral =>
        {
            literal.text.clone()
        }
        _ => {
            return Err(unsupported(
                name,
                name_record.kind,
                SourceSyntaxRole::InterfaceDeclaration,
            ));
        }
    };
    if name_record.parent != Some(declaration.node) {
        return Err(invalid_parent(name, declaration, name_record.parent));
    }

    let optional = if let Some(postfix) = syntax.postfix_token {
        let postfix = child(declaration, postfix);
        let postfix_record = owned_node(arena, bound, store, postfix)?;
        if postfix_record.kind != SyntaxKind::QuestionToken
            || postfix_record.parent != Some(declaration.node)
        {
            return Err(unsupported(
                postfix,
                postfix_record.kind,
                SourceSyntaxRole::InterfaceDeclaration,
            ));
        }
        true
    } else {
        false
    };
    if let Some(modifiers) = syntax.modifiers
        && modifiers.list.nodes.iter().any(|modifier| {
            arena
                .get(*modifier)
                .is_none_or(|record| record.kind != SyntaxKind::ReadonlyKeyword)
        })
    {
        return Err(unsupported(
            declaration,
            SyntaxKind::PropertyDeclaration,
            SourceSyntaxRole::InterfaceDeclaration,
        ));
    }
    let readonly =
        canonical_has_syntactic_modifier(arena, declaration.node, SyntaxKind::ReadonlyKeyword);
    let symbol = declaration_symbol(bound, store, declaration, SymbolFlags::PROPERTY)?;
    let record = store.symbol(symbol).ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
    ))?;
    let expected_flags = SymbolFlags::PROPERTY
        | if optional {
            SymbolFlags::OPTIONAL
        } else {
            SymbolFlags::NONE
        };
    if record.flags() != expected_flags
        || store.get_parent_of_symbol(symbol) != Some(owner)
        || store
            .symbol_table(members)
            .and_then(|table| table.get_source(&property_name))
            != Some(symbol)
        || record.check_flags() != CheckFlags::NONE && record.check_flags() != CheckFlags::READONLY
    {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ));
    }
    Ok(SourceNamespacePropertyPlan {
        declaration,
        symbol,
        name: property_name,
        annotation: syntax.annotation,
        optional,
        readonly,
    })
}

fn plan_jsx_record_interface_heritage(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    declaration: NodeRef,
    clauses: &ts_ast::NodeList,
) -> Result<Vec<NodeRef>, SourceCheckError> {
    let invalid = |node: NodeRef, kind: SyntaxKind| {
        unsupported(node, kind, SourceSyntaxRole::InterfaceDeclaration)
    };
    let declaration_record = owned_node(arena, bound, store, declaration)?;
    let NodeData::InterfaceDeclaration(interface) = &declaration_record.data else {
        return Err(invalid(declaration, declaration_record.kind));
    };
    let name = child(declaration, interface.name);
    let name_record = owned_node(arena, bound, store, name)?;
    let NodeData::Identifier(interface_name) = &name_record.data else {
        return Err(invalid(name, name_record.kind));
    };
    if store
        .symbol(owner)
        .and_then(|symbol| symbol.name().as_utf8())
        != Some("JSX")
        || interface_name.text != "IntrinsicElements"
        || interface.type_parameters.is_some()
        || !interface.members.nodes.is_empty()
        || clauses.has_trailing_comma
        || clauses.nodes.len() != 1
    {
        let clause = clauses
            .nodes
            .first()
            .copied()
            .map_or(declaration, |clause| child(declaration, clause));
        let kind = arena
            .get(clause.node)
            .map_or(declaration_record.kind, |record| record.kind);
        return Err(invalid(clause, kind));
    }

    let clause = child(declaration, clauses.nodes[0]);
    let clause_record = owned_node(arena, bound, store, clause)?;
    let NodeData::HeritageClause(heritage) = &clause_record.data else {
        return Err(invalid(clause, clause_record.kind));
    };
    if clause_record.kind != SyntaxKind::HeritageClause
        || clause_record.flags.0 != 0
        || clause_record.parent != Some(declaration.node)
        || heritage.token != SyntaxKind::ExtendsKeyword
        || heritage.facts != 0
        || heritage.types.has_trailing_comma
        || heritage.types.nodes.len() != 1
    {
        return Err(invalid(clause, clause_record.kind));
    }

    let base = child(clause, heritage.types.nodes[0]);
    let base_record = owned_node(arena, bound, store, base)?;
    let NodeData::ExpressionWithTypeArguments(reference) = &base_record.data else {
        return Err(invalid(base, base_record.kind));
    };
    let Some(arguments) = reference.type_arguments.as_ref() else {
        return Err(invalid(base, base_record.kind));
    };
    if base_record.kind != SyntaxKind::ExpressionWithTypeArguments
        || base_record.flags.0 != 0
        || base_record.parent != Some(clause.node)
        || reference.facts != 0
        || arguments.has_trailing_comma
        || arguments.nodes.len() != 2
    {
        return Err(invalid(base, base_record.kind));
    }

    let record_name = child(base, reference.expression);
    let record_name_node = owned_node(arena, bound, store, record_name)?;
    let NodeData::Identifier(record_identifier) = &record_name_node.data else {
        return Err(invalid(record_name, record_name_node.kind));
    };
    let record_symbol = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
        .and_then(|globals| globals.get_source("Record"))
        .and_then(|symbol| store.get_merged_symbol(symbol));
    if record_name_node.kind != SyntaxKind::Identifier
        || record_name_node.flags.0 != 0
        || record_name_node.parent != Some(base.node)
        || record_identifier.flow_node.is_some()
        || record_identifier.text != "Record"
        || record_symbol
            .and_then(|symbol| store.symbol(symbol))
            .is_none_or(|symbol| symbol.flags() != SymbolFlags::TYPE_ALIAS)
    {
        return Err(invalid(record_name, record_name_node.kind));
    }

    let mut annotations = Vec::with_capacity(arguments.nodes.len());
    for (argument, expected) in arguments
        .nodes
        .iter()
        .zip([SyntaxKind::StringKeyword, SyntaxKind::AnyKeyword])
    {
        let argument = child(base, *argument);
        let record = owned_node(arena, bound, store, argument)?;
        if record.kind != expected
            || record.flags.0 != 0
            || record.parent != Some(base.node)
            || !matches!(record.data, NodeData::KeywordTypeNode(_))
        {
            return Err(invalid(argument, record.kind));
        }
        annotations.push(argument);
    }
    Ok(annotations)
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
    if record.flags.0 != 0 || interface.members.has_trailing_comma {
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
    if let Some(heritage) = &interface.heritage_clauses {
        annotations.extend(plan_jsx_record_interface_heritage(
            arena,
            bound,
            store,
            owner,
            declaration,
            heritage,
        )?);
    }
    let mut generic = interface
        .type_parameters
        .as_ref()
        .map(|parameters| {
            plan_generic_interface_parameters(
                arena,
                bound,
                store,
                declaration,
                symbol,
                parameters,
                &mut annotations,
            )
        })
        .transpose()?;
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
                let annotation = child(member, annotation);
                annotations.push(annotation);
                if let Some(generic) = generic.as_mut() {
                    generic.properties.push(plan_generic_interface_property(
                        arena,
                        bound,
                        store,
                        symbol,
                        generic.members,
                        member,
                        SourceNamespacePropertySyntax {
                            name: property.name,
                            annotation,
                            postfix_token: property.postfix_token,
                            modifiers: property.modifiers.as_ref(),
                        },
                    )?);
                }
            }
            NodeData::PropertySignatureDeclaration(property)
                if member_record.kind == SyntaxKind::PropertySignature =>
            {
                let annotation = child(member, property.type_);
                annotations.push(annotation);
                if let Some(generic) = generic.as_mut() {
                    generic.properties.push(plan_generic_interface_property(
                        arena,
                        bound,
                        store,
                        symbol,
                        generic.members,
                        member,
                        SourceNamespacePropertySyntax {
                            name: property.name,
                            annotation,
                            postfix_token: property.postfix_token,
                            modifiers: property.modifiers.as_ref(),
                        },
                    )?);
                }
            }
            NodeData::IndexSignatureDeclaration(index)
                if member_record.kind == SyntaxKind::IndexSignature
                    && index.type_parameters.is_none()
                    && index.parameters.nodes.len() == 1
                    && generic.is_none() =>
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
    if let Some(generic) = generic.as_ref()
        && store
            .symbol_table(generic.members)
            .map_or(0, ts_binder::semantic::SymbolTable::len)
            != generic.type_parameters.len() + generic.properties.len()
    {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ));
    }
    Ok(SourceNamespaceMemberPlan::Interface {
        declaration,
        symbol,
        annotations,
        generic,
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

fn namespace_callable_error(declaration: NodeRef, error: SourceCallableError) -> SourceCheckError {
    match error {
        SourceCallableError::Unsupported(_) => unsupported(
            declaration,
            SyntaxKind::FunctionDeclaration,
            SourceSyntaxRole::FunctionDeclaration,
        ),
        SourceCallableError::Invariant(_) => {
            SourceCheckError::Function(SourceFunctionInvariant::Callable(declaration))
        }
        SourceCallableError::DeclaredType(error) => SourceCheckError::DeclaredType(error),
        SourceCallableError::LiteralCache(error) => error.into(),
    }
}

fn plan_namespace_function(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: (NodeRef, SemanticSymbolId),
    ambient: bool,
    declaration: NodeRef,
) -> Result<SourceNamespaceMemberPlan, SourceCheckError> {
    let (namespace, owner) = namespace;
    let record = owned_node(arena, bound, store, declaration)?;
    let NodeData::FunctionDeclaration(function) = &record.data else {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::FunctionDeclaration,
        ));
    };
    let (exported, declared) = modifier_flags(
        arena,
        bound,
        store,
        declaration,
        function.modifiers.as_ref(),
    )?;
    let Some(name) = function.name else {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::FunctionName,
        ));
    };
    let name = child(declaration, name);
    let name_record = owned_node(arena, bound, store, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(
            name,
            name_record.kind,
            SourceSyntaxRole::FunctionName,
        ));
    };
    let ambient_declaration = ambient
        && bound
            .source_facts()
            .is_some_and(ts_binder::CanonicalSourceFileFacts::is_declaration_file)
        && function.body.is_none();
    let body = if ambient_declaration {
        let annotation = function
            .type_
            .map(|annotation| child(declaration, annotation));
        let Some(annotation) = annotation else {
            return Err(unsupported(
                declaration,
                record.kind,
                SourceSyntaxRole::FunctionDeclaration,
            ));
        };
        let annotation_record = owned_node(arena, bound, store, annotation)?;
        if annotation_record.kind != SyntaxKind::VoidKeyword
            || annotation_record.flags.0 != 0
            || annotation_record.parent != Some(declaration.node)
            || !matches!(annotation_record.data, NodeData::KeywordTypeNode(_))
        {
            return Err(unsupported(
                annotation,
                annotation_record.kind,
                SourceSyntaxRole::FunctionDeclaration,
            ));
        }
        declaration
    } else {
        let Some(body) = function.body else {
            return Err(unsupported(
                declaration,
                record.kind,
                SourceSyntaxRole::FunctionBody,
            ));
        };
        let body = child(declaration, body);
        let body_record = owned_node(arena, bound, store, body)?;
        let NodeData::Block(block) = &body_record.data else {
            return Err(unsupported(
                body,
                body_record.kind,
                SourceSyntaxRole::FunctionBody,
            ));
        };
        if body_record.kind != SyntaxKind::Block
            || body_record.flags.0 != 0
            || body_record.parent != Some(declaration.node)
            || block.flow_node.is_some()
            || block.next_container.is_some()
            || block.facts != 0
            || !block.statements.nodes.is_empty()
            || block.statements.has_trailing_comma
        {
            return Err(unsupported(
                declaration,
                record.kind,
                SourceSyntaxRole::FunctionDeclaration,
            ));
        }
        body
    };
    if ambient != ambient_declaration
        || !exported
        || declared
        || record.kind != SyntaxKind::FunctionDeclaration
        || record.flags.0 != 0
        || function.asterisk_token.is_some()
        || function.end_flow_node.is_some()
        || function.flow_node.is_some()
        || function.full_signature.is_some()
        || function.local_symbol.is_some()
        || function.next_container.is_some()
        || function.return_flow_node.is_some()
        || function.symbol.is_some()
        || function.type_.is_some() != ambient_declaration
        || function.type_parameters.is_some()
        || function.facts != 0
        || !function.parameters.nodes.is_empty()
        || function.parameters.has_trailing_comma
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::FunctionDeclaration,
        ));
    }

    let symbol = declaration_symbol(bound, store, declaration, SymbolFlags::FUNCTION)?;
    let function_record = store.symbol(symbol).ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
    ))?;
    let local = bound
        .local_symbol(declaration)
        .ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ))?;
    let local_record = store.symbol(local).ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
    ))?;
    if function_record.flags() != SymbolFlags::FUNCTION
        || function_record.check_flags() != CheckFlags::NONE
        || function_record.declarations() != Some(&[declaration])
        || function_record.value_declaration() != Some(declaration)
        || function_record.name().as_utf8() != Some(identifier.text.as_str())
        || function_record.members().is_some()
        || function_record.exports().is_some()
        || function_record.export_symbol().is_some()
        || store.get_parent_of_symbol(symbol) != Some(owner)
        || store.get_merged_symbol(local) != Some(local)
        || local_record.flags() != SymbolFlags::EXPORT_VALUE
        || local_record.check_flags() != CheckFlags::NONE
        || local_record.declarations() != Some(&[declaration])
        || local_record.value_declaration().is_some()
        || local_record.name().as_utf8() != Some(identifier.text.as_str())
        || local_record.members().is_some()
        || local_record.exports().is_some()
        || local_record.parent().is_some()
        || local_record.export_symbol() != Some(symbol)
        || store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source(&identifier.text))
            .and_then(|candidate| store.get_merged_symbol(candidate))
            != Some(symbol)
        || bound
            .locals(namespace)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&identifier.text))
            != Some(local)
    {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ));
    }
    let host = DeclaredTypeHost::new([(arena, bound)]).map_err(DeclaredTypeError::from)?;
    let array_targets = store
        .source_callable_type_for_owner(symbol)
        .and_then(|type_| store.source_callable_provenance(type_))
        .and_then(|provenance| provenance.array_targets);
    let callable =
        source_callables::plan_source_callable(store, &host, declaration, symbol, array_targets)
            .map_err(|error| namespace_callable_error(declaration, error))?;
    if callable.owner_parent != Some(owner)
        || callable.export_local != Some(local)
        || !callable.parameters.is_empty()
        || !callable.type_parameters.is_empty()
        || callable.body != body
        || callable.body_mode.is_ambient() != ambient_declaration
        || if ambient_declaration {
            callable.return_type.annotation_identity()
                != function
                    .type_
                    .map(|annotation| (child(declaration, annotation), false))
        } else {
            !callable.return_type.is_inferred()
        }
    {
        return Err(SourceCheckError::Function(
            SourceFunctionInvariant::Callable(declaration),
        ));
    }

    Ok(SourceNamespaceMemberPlan::Function {
        declaration,
        symbol,
    })
}

fn validate_namespace_import_reference(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    parent: NodeRef,
    reference: NodeRef,
) -> Result<(), SourceCheckError> {
    let record = owned_node(arena, bound, store, reference)?;
    if record.parent != Some(parent.node) {
        return Err(invalid_parent(reference, parent, record.parent));
    }
    if record.flags.0 != 0 {
        return Err(unsupported(
            reference,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    }
    match &record.data {
        NodeData::Identifier(identifier)
            if record.kind == SyntaxKind::Identifier
                && !identifier.text.is_empty()
                && identifier.flow_node.is_none() =>
        {
            Ok(())
        }
        NodeData::QualifiedName(qualified)
            if record.kind == SyntaxKind::QualifiedName
                && qualified.flow_node.is_none()
                && qualified.facts == 0 =>
        {
            validate_namespace_import_reference(
                arena,
                bound,
                store,
                reference,
                child(reference, qualified.left),
            )?;
            let right = child(reference, qualified.right);
            let right_record = owned_node(arena, bound, store, right)?;
            if !matches!(right_record.data, NodeData::Identifier(_)) {
                return Err(unsupported(
                    right,
                    right_record.kind,
                    SourceSyntaxRole::Statement,
                ));
            }
            validate_namespace_import_reference(arena, bound, store, reference, right)
        }
        _ => Err(unsupported(
            reference,
            record.kind,
            SourceSyntaxRole::Statement,
        )),
    }
}

fn plan_namespace_import(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: NodeRef,
    owner: SemanticSymbolId,
    declaration: NodeRef,
) -> Result<SourceNamespaceImportPlan, SourceCheckError> {
    let record = owned_node(arena, bound, store, declaration)?;
    let NodeData::ImportEqualsDeclaration(import) = &record.data else {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MismatchedNodeData {
                node: declaration,
                kind: record.kind,
            },
        ));
    };
    if record.kind != SyntaxKind::ImportEqualsDeclaration
        || record.flags.0 != 0
        || import.flow_node.is_some()
        || import.local_symbol.is_some()
        || import.symbol.is_some()
        || import.facts != 0
    {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    }
    let (exported, declared) =
        modifier_flags(arena, bound, store, declaration, import.modifiers.as_ref())?;
    if declared {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    }

    let name = child(declaration, import.name);
    let name_record = owned_node(arena, bound, store, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(
            name,
            name_record.kind,
            SourceSyntaxRole::Statement,
        ));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(declaration.node)
        || name_record.flags.0 != 0
        || identifier.text.is_empty()
        || identifier.flow_node.is_some()
    {
        return Err(invalid_parent(name, declaration, name_record.parent));
    }

    let reference = child(declaration, import.module_reference);
    validate_namespace_import_reference(arena, bound, store, declaration, reference)?;
    let symbol = declaration_symbol(bound, store, declaration, SymbolFlags::ALIAS)?;
    let alias = store.symbol(symbol).ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
    ))?;
    let namespace_table = if exported {
        store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::exports)
    } else {
        bound.locals(namespace)
    };
    if alias.flags() != SymbolFlags::ALIAS
        || alias.check_flags() != CheckFlags::NONE
        || alias.declarations() != Some(&[declaration])
        || alias.value_declaration().is_some()
        || alias.members().is_some()
        || alias.exports().is_some()
        || alias.export_symbol().is_some()
        || alias.name().as_utf8() != Some(identifier.text.as_str())
        || alias.parent().is_some() != exported
        || exported && store.get_parent_of_symbol(symbol) != Some(owner)
        || namespace_table
            .and_then(|table| store.symbol_table(table))
            .and_then(|table| table.get_source(&identifier.text))
            .and_then(|candidate| store.get_merged_symbol(candidate))
            != Some(symbol)
    {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ));
    }
    if let Some(links) = store.alias_symbol_links(symbol)
        && (links
            .immediate_target
            .is_some_and(|target| store.symbol(target).is_none())
            || links
                .alias_target
                .symbol()
                .is_some_and(|target| store.symbol(target).is_none())
            || links
                .type_only_declaration
                .is_some_and(|marker| !store.contains_node_ref(marker)))
    {
        return Err(SourceCheckError::Import(declaration));
    }

    Ok(SourceNamespaceImportPlan {
        declaration,
        name_text: identifier.text.clone(),
        symbol,
        reference,
        ambient_target: None,
        type_only: import.is_type_only,
    })
}

fn ambient_module_import_target(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    specifier: NodeRef,
) -> Result<SemanticSymbolId, SourceCheckError> {
    let record = owned_node(arena, bound, store, specifier)?;
    let NodeData::StringLiteral(name) = &record.data else {
        return Err(unsupported(
            specifier,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    };
    if record.kind != SyntaxKind::StringLiteral
        || record.flags.0 != 0
        || name.token_flags.0 != 0
        || name.text.is_empty()
    {
        return Err(unsupported(
            specifier,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    }
    let quoted_name = EscapedName::source(format!("\"{}\"", name.text));
    let module = bound
        .locals(bound.source_file())
        .and_then(|locals| store.symbol_table(locals))
        .and_then(|locals| locals.get(quoted_name.as_ref()))
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Import(specifier),
        ))?;
    let owner = store
        .symbol(module)
        .filter(|owner| owner.flags().intersects(SymbolFlags::MODULE))
        .ok_or(SourceCheckError::Import(specifier))?;
    let exports = owner
        .exports()
        .and_then(|exports| store.symbol_table(exports))
        .ok_or(SourceCheckError::Import(specifier))?;
    let Some(export_assignment) = exports.get(InternalSymbolName::ExportEquals.as_ref()) else {
        return Ok(module);
    };
    let assignment = store
        .symbol(export_assignment)
        .ok_or(SourceCheckError::Import(specifier))?;
    let Some([declaration]) = assignment.declarations() else {
        return Err(SourceCheckError::Import(specifier));
    };
    let declaration = *declaration;
    let assignment_record = owned_node(arena, bound, store, declaration)?;
    let NodeData::ExportAssignment(export) = &assignment_record.data else {
        return Err(SourceCheckError::Import(specifier));
    };
    let expression = child(declaration, export.expression);
    let expression_record = owned_node(arena, bound, store, expression)?;
    let NodeData::Identifier(identifier) = &expression_record.data else {
        return Err(SourceCheckError::Import(specifier));
    };
    let Some(module_declaration) = owner
        .declarations()
        .and_then(|declarations| declarations.first())
        .copied()
    else {
        return Err(SourceCheckError::Import(specifier));
    };
    if assignment.flags() != SymbolFlags::ALIAS
        || assignment_record.kind != SyntaxKind::ExportAssignment
        || !export.is_export_equals
        || expression_record.kind != SyntaxKind::Identifier
        || expression_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
    {
        return Err(SourceCheckError::Import(specifier));
    }
    let local = bound
        .locals(module_declaration)
        .and_then(|locals| store.symbol_table(locals))
        .and_then(|locals| locals.get_source(&identifier.text))
        .and_then(|local| store.get_merged_symbol(local))
        .ok_or(SourceCheckError::Import(specifier))?;
    let namespace = store
        .symbol(local)
        .map(|record| record.export_symbol().unwrap_or(local))
        .and_then(|namespace| store.get_merged_symbol(namespace))
        .ok_or(SourceCheckError::Import(specifier))?;
    if store
        .symbol(namespace)
        .is_none_or(|record| !record.flags().intersects(SymbolFlags::NAMESPACE))
    {
        return Err(SourceCheckError::Import(specifier));
    }
    Ok(namespace)
}

fn plan_ambient_module_import_binding(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: (NodeRef, NodeRef),
    name: NodeRef,
    reference: NodeRef,
    target: SemanticSymbolId,
) -> Result<SourceNamespaceImportPlan, SourceCheckError> {
    let (namespace, declaration) = namespace;
    let name_record = owned_node(arena, bound, store, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(
            name,
            name_record.kind,
            SourceSyntaxRole::Statement,
        ));
    };
    let symbol = declaration_symbol(bound, store, declaration, SymbolFlags::ALIAS)?;
    let alias = store
        .symbol(symbol)
        .ok_or(SourceCheckError::Import(declaration))?;
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || alias.flags() != SymbolFlags::ALIAS
        || alias.check_flags() != CheckFlags::NONE
        || alias.declarations() != Some(&[declaration])
        || alias.value_declaration().is_some()
        || alias.members().is_some()
        || alias.exports().is_some()
        || alias.parent().is_some()
        || alias.export_symbol().is_some()
        || alias.name().as_utf8() != Some(identifier.text.as_str())
        || bound
            .locals(namespace)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&identifier.text))
            .and_then(|local| store.get_merged_symbol(local))
            != Some(symbol)
        || store.get_merged_symbol(target) != Some(target)
    {
        return Err(SourceCheckError::Import(declaration));
    }
    Ok(SourceNamespaceImportPlan {
        declaration,
        name_text: identifier.text.clone(),
        symbol,
        reference,
        ambient_target: Some(target),
        type_only: false,
    })
}

#[allow(clippy::too_many_lines)] // Validate each binder-owned import shape before publishing aliases.
fn plan_ambient_module_import(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: NodeRef,
    declaration: NodeRef,
) -> Result<Vec<SourceNamespaceImportPlan>, SourceCheckError> {
    let record = owned_node(arena, bound, store, declaration)?;
    let NodeData::ImportDeclaration(import) = &record.data else {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    };
    let Some(clause) = import.import_clause else {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    };
    if record.kind != SyntaxKind::ImportDeclaration
        || record.flags.0 != 0
        || import.attributes.is_some()
        || import.flow_node.is_some()
        || import.symbol.is_some()
        || import.facts != 0
        || import.modifiers.is_some()
    {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    }
    let reference = child(declaration, import.module_specifier);
    let reference_record = owned_node(arena, bound, store, reference)?;
    if reference_record.parent != Some(declaration.node) {
        return Err(invalid_parent(
            reference,
            declaration,
            reference_record.parent,
        ));
    }
    let module = ambient_module_import_target(arena, bound, store, reference)?;
    let exports = store
        .symbol(module)
        .and_then(ts_binder::semantic::Symbol::exports)
        .and_then(|exports| store.symbol_table(exports))
        .ok_or(SourceCheckError::Import(declaration))?;

    let clause = child(declaration, clause);
    let clause_record = owned_node(arena, bound, store, clause)?;
    let NodeData::ImportClause(import_clause) = &clause_record.data else {
        return Err(unsupported(
            clause,
            clause_record.kind,
            SourceSyntaxRole::Statement,
        ));
    };
    let Some(bindings) = import_clause.named_bindings else {
        return Err(unsupported(
            clause,
            clause_record.kind,
            SourceSyntaxRole::Statement,
        ));
    };
    if clause_record.kind != SyntaxKind::ImportClause
        || clause_record.flags.0 != 0
        || clause_record.parent != Some(declaration.node)
        || import_clause.local_symbol.is_some()
        || import_clause.phase_modifier.is_some()
        || import_clause.symbol.is_some()
        || import_clause.facts != 0
        || import_clause.name.is_some()
    {
        return Err(unsupported(
            clause,
            clause_record.kind,
            SourceSyntaxRole::Statement,
        ));
    }
    let bindings = child(clause, bindings);
    let bindings_record = owned_node(arena, bound, store, bindings)?;
    if bindings_record.parent != Some(clause.node) || bindings_record.flags.0 != 0 {
        return Err(unsupported(
            bindings,
            bindings_record.kind,
            SourceSyntaxRole::Statement,
        ));
    }

    match &bindings_record.data {
        NodeData::NamespaceImport(import)
            if bindings_record.kind == SyntaxKind::NamespaceImport =>
        {
            if import.local_symbol.is_some() || import.symbol.is_some() {
                return Err(unsupported(
                    bindings,
                    bindings_record.kind,
                    SourceSyntaxRole::Statement,
                ));
            }
            let name = child(bindings, import.name);
            Ok(vec![plan_ambient_module_import_binding(
                arena,
                bound,
                store,
                (namespace, bindings),
                name,
                reference,
                module,
            )?])
        }
        NodeData::NamedImports(import) if bindings_record.kind == SyntaxKind::NamedImports => {
            if import.facts != 0 || import.elements.has_trailing_comma {
                return Err(unsupported(
                    bindings,
                    bindings_record.kind,
                    SourceSyntaxRole::Statement,
                ));
            }
            let mut planned = Vec::with_capacity(import.elements.nodes.len());
            let mut aliases = HashSet::with_capacity(import.elements.nodes.len());
            for &specifier in &import.elements.nodes {
                let specifier = child(bindings, specifier);
                let specifier_record = owned_node(arena, bound, store, specifier)?;
                let NodeData::ImportSpecifier(binding) = &specifier_record.data else {
                    return Err(unsupported(
                        specifier,
                        specifier_record.kind,
                        SourceSyntaxRole::Statement,
                    ));
                };
                if specifier_record.kind != SyntaxKind::ImportSpecifier
                    || specifier_record.flags.0 != 0
                    || specifier_record.parent != Some(bindings.node)
                    || binding.is_type_only
                    || binding.local_symbol.is_some()
                    || binding.symbol.is_some()
                    || binding.facts != 0
                {
                    return Err(unsupported(
                        specifier,
                        specifier_record.kind,
                        SourceSyntaxRole::Statement,
                    ));
                }
                let imported = child(specifier, binding.property_name.unwrap_or(binding.name));
                let imported_record = owned_node(arena, bound, store, imported)?;
                let NodeData::Identifier(imported_name) = &imported_record.data else {
                    return Err(unsupported(
                        imported,
                        imported_record.kind,
                        SourceSyntaxRole::Statement,
                    ));
                };
                if imported_record.kind != SyntaxKind::Identifier
                    || imported_record.flags.0 != 0
                    || imported_record.parent != Some(specifier.node)
                    || imported_name.flow_node.is_some()
                {
                    return Err(unsupported(
                        imported,
                        imported_record.kind,
                        SourceSyntaxRole::Statement,
                    ));
                }
                let target = exports
                    .get_source(&imported_name.text)
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    .ok_or(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Import(specifier),
                    ))?;
                let name = child(specifier, binding.name);
                let import = plan_ambient_module_import_binding(
                    arena,
                    bound,
                    store,
                    (namespace, specifier),
                    name,
                    reference,
                    target,
                )?;
                if !aliases.insert(import.symbol) {
                    return Err(SourceCheckError::Import(specifier));
                }
                planned.push(import);
            }
            Ok(planned)
        }
        _ => Err(unsupported(
            bindings,
            bindings_record.kind,
            SourceSyntaxRole::Statement,
        )),
    }
}

fn namespace_object_error(node: NodeRef, error: PropertyObjectError) -> SourceCheckError {
    match error {
        PropertyObjectError::Capacity(node) => {
            SourceCheckError::ObjectLiteral(SourceObjectLiteralError::Capacity(node))
        }
        PropertyObjectError::InvalidCachedTypeLiteral { node, type_ } => {
            SourceCheckError::ObjectLiteral(SourceObjectLiteralError::InvalidCache {
                node,
                type_: Some(type_),
            })
        }
        _ => SourceCheckError::ObjectLiteral(SourceObjectLiteralError::InvalidCache {
            node,
            type_: None,
        }),
    }
}

fn plan_namespace_object_initializer(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: (NodeRef, SemanticSymbolId),
    variable: (NodeRef, SemanticSymbolId, NodeRef, NodeRef),
    members: &[SourceNamespaceMemberPlan],
) -> Result<SourceNamespaceObjectInitializerPlan, SourceCheckError> {
    let (namespace, owner) = namespace;
    let (declaration, symbol, annotation, initializer) = variable;
    let declaration_record = owned_node(arena, bound, store, declaration)?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return Err(unsupported(
            declaration,
            declaration_record.kind,
            SourceSyntaxRole::VariableDeclaration,
        ));
    };
    let name = child(declaration, variable.name);
    let name_record = owned_node(arena, bound, store, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(
            name,
            name_record.kind,
            SourceSyntaxRole::VariableName,
        ));
    };
    let symbol_record = store.symbol(symbol).ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
    ))?;
    if declaration_record.kind != SyntaxKind::VariableDeclaration
        || declaration_record.flags.0 != 0
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.facts != 0
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.declarations() != Some(&[declaration])
        || symbol_record.value_declaration() != Some(declaration)
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent().is_some()
        || symbol_record.export_symbol().is_some()
        || declaration_symbol(bound, store, namespace, SymbolFlags::MODULE)? != owner
        || bound
            .locals(namespace)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&identifier.text))
            .and_then(|candidate| store.get_merged_symbol(candidate))
            != Some(symbol)
    {
        return Err(unsupported(
            declaration,
            declaration_record.kind,
            SourceSyntaxRole::VariableDeclaration,
        ));
    }

    let annotation_record = owned_node(arena, bound, store, annotation)?;
    let NodeData::TypeReferenceNode(reference) = &annotation_record.data else {
        return Err(unsupported(
            annotation,
            annotation_record.kind,
            SourceSyntaxRole::VariableDeclaration,
        ));
    };
    if annotation_record.kind != SyntaxKind::TypeReference
        || annotation_record.flags.0 != 0
        || reference.type_arguments.is_some()
    {
        return Err(unsupported(
            annotation,
            annotation_record.kind,
            SourceSyntaxRole::VariableDeclaration,
        ));
    }
    let interface_name = child(annotation, reference.type_name);
    let interface_name_record = owned_node(arena, bound, store, interface_name)?;
    let NodeData::Identifier(interface_identifier) = &interface_name_record.data else {
        return Err(unsupported(
            interface_name,
            interface_name_record.kind,
            SourceSyntaxRole::VariableDeclaration,
        ));
    };
    if interface_name_record.kind != SyntaxKind::Identifier
        || interface_name_record.flags.0 != 0
        || interface_name_record.parent != Some(annotation.node)
        || interface_identifier.flow_node.is_some()
        || interface_identifier.text.is_empty()
    {
        return Err(unsupported(
            interface_name,
            interface_name_record.kind,
            SourceSyntaxRole::VariableDeclaration,
        ));
    }
    let mut candidates = members.iter().filter_map(|member| match member {
        SourceNamespaceMemberPlan::Interface {
            declaration,
            symbol,
            generic: None,
            ..
        } if store
            .symbol(*symbol)
            .and_then(|record| record.name().as_utf8())
            == Some(interface_identifier.text.as_str()) =>
        {
            Some((*declaration, *symbol))
        }
        _ => None,
    });
    let Some((interface_declaration, interface)) = candidates.next() else {
        return Err(unsupported(
            annotation,
            annotation_record.kind,
            SourceSyntaxRole::VariableDeclaration,
        ));
    };
    let interface_record = store.symbol(interface).ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingDeclarationSymbol(interface_declaration),
    ))?;
    if candidates.next().is_some()
        || interface_record.flags() != SymbolFlags::INTERFACE
        || interface_record.check_flags() != CheckFlags::NONE
        || interface_record.parent().is_some()
        || interface_record.declarations() != Some(&[interface_declaration])
        || interface_record.value_declaration().is_some()
        || bound
            .locals(namespace)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&interface_identifier.text))
            .and_then(|candidate| store.get_merged_symbol(candidate))
            != Some(interface)
    {
        return Err(unsupported(
            annotation,
            annotation_record.kind,
            SourceSyntaxRole::VariableDeclaration,
        ));
    }

    let initializer_record = owned_node(arena, bound, store, initializer)?;
    if initializer_record.parent != Some(declaration.node)
        || initializer_record.kind != SyntaxKind::ObjectLiteralExpression
    {
        return Err(unsupported(
            initializer,
            initializer_record.kind,
            SourceSyntaxRole::VariableInitializer,
        ));
    }
    let host = DeclaredTypeHost::new([(arena, bound)]).map_err(DeclaredTypeError::from)?;
    let object = object_members::plan_object_literal(store, &host, initializer).map_err(
        |error| match error {
            PropertyObjectError::UnsupportedMember { node, kind } => {
                unsupported(node, kind, SourceSyntaxRole::ObjectProperty)
            }
            error => namespace_object_error(initializer, error),
        },
    )?;
    let interface_plan = object_members::plan_interface(store, &host, interface).map_err(|_| {
        unsupported(
            annotation,
            annotation_record.kind,
            SourceSyntaxRole::VariableDeclaration,
        )
    })?;
    if object.properties.is_empty()
        || object.properties.len() != interface_plan.properties.len()
        || !object.indexes.is_empty()
        || !object.call_signatures.is_empty()
        || !interface_plan.indexes.is_empty()
        || !interface_plan.call_signatures.is_empty()
        || interface_plan.heritage.is_some()
    {
        return Err(unsupported(
            initializer,
            initializer_record.kind,
            SourceSyntaxRole::VariableInitializer,
        ));
    }
    for property in &object.properties {
        let property_name = owned_node(arena, bound, store, property.name_node)?;
        let Some(expected) = interface_plan
            .properties
            .iter()
            .find(|candidate| candidate.name == property.name)
        else {
            return Err(unsupported(
                property.declaration,
                SyntaxKind::PropertyAssignment,
                SourceSyntaxRole::ObjectProperty,
            ));
        };
        if property_name.kind != SyntaxKind::Identifier
            || property.optional
            || property.readonly
            || expected.optional
            || expected.readonly
            || owned_node(arena, bound, store, expected.type_node)?.kind
                != SyntaxKind::NumberKeyword
        {
            return Err(unsupported(
                property.declaration,
                SyntaxKind::PropertyAssignment,
                SourceSyntaxRole::ObjectProperty,
            ));
        }
        plan_namespace_numeric_initializer(
            arena,
            bound,
            store,
            property.declaration,
            property.type_node,
        )?;
    }

    Ok(SourceNamespaceObjectInitializerPlan {
        declaration,
        symbol,
        interface,
        annotation,
        object,
    })
}

fn plan_namespace_ambient_initializer(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: SemanticSymbolId,
    variable: (NodeRef, SemanticSymbolId, NodeRef),
    members: &[SourceNamespaceMemberPlan],
) -> Result<SourceNamespaceAmbientVariablePlan, SourceCheckError> {
    let (declaration, symbol, initializer) = variable;
    let declaration_record = owned_node(arena, bound, store, declaration)?;
    let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
        return Err(unsupported(
            declaration,
            declaration_record.kind,
            SourceSyntaxRole::VariableDeclaration,
        ));
    };
    let name = child(declaration, variable.name);
    let name_record = owned_node(arena, bound, store, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(
            name,
            name_record.kind,
            SourceSyntaxRole::VariableName,
        ));
    };
    let symbol_record = store.symbol(symbol).ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
    ))?;
    if declaration_record.kind != SyntaxKind::VariableDeclaration
        || declaration_record.flags.0 != 0
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.type_.is_some()
        || variable.facts != 0
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || symbol_record.flags() != SymbolFlags::BLOCK_SCOPED_VARIABLE
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.declarations() != Some(&[declaration])
        || symbol_record.value_declaration() != Some(declaration)
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.export_symbol().is_some()
        || store.get_parent_of_symbol(symbol) != Some(namespace)
        || store
            .symbol(namespace)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source(&identifier.text))
            .and_then(|candidate| store.get_merged_symbol(candidate))
            != Some(symbol)
    {
        return Err(unsupported(
            declaration,
            declaration_record.kind,
            SourceSyntaxRole::VariableDeclaration,
        ));
    }

    let initializer_record = owned_node(arena, bound, store, initializer)?;
    if initializer_record.parent != Some(declaration.node) || initializer_record.flags.0 != 0 {
        return Err(unsupported(
            initializer,
            initializer_record.kind,
            SourceSyntaxRole::VariableInitializer,
        ));
    }
    let value = match &initializer_record.data {
        NodeData::StringLiteral(literal)
            if initializer_record.kind == SyntaxKind::StringLiteral
                && literal.token_flags.0 == 0 =>
        {
            SourceNamespaceAmbientInitializer::String(literal.text.clone())
        }
        NodeData::NoSubstitutionTemplateLiteral(literal)
            if initializer_record.kind == SyntaxKind::NoSubstitutionTemplateLiteral
                && literal.token_flags.0 == 0
                && literal.template_flags.0 == 0
                && literal.symbol.is_none() =>
        {
            SourceNamespaceAmbientInitializer::String(literal.text.clone())
        }
        NodeData::PropertyAccessExpression(access)
            if initializer_record.kind == SyntaxKind::PropertyAccessExpression
                && access.flow_node.is_none()
                && access.question_dot_token.is_none()
                && access.facts == 0 =>
        {
            plan_namespace_ambient_enum_member(
                arena,
                bound,
                store,
                initializer,
                (
                    child(initializer, access.expression),
                    child(initializer, access.name),
                ),
                false,
                members,
            )?
        }
        NodeData::ElementAccessExpression(access)
            if initializer_record.kind == SyntaxKind::ElementAccessExpression
                && access.flow_node.is_none()
                && access.question_dot_token.is_none()
                && access.facts == 0 =>
        {
            plan_namespace_ambient_enum_member(
                arena,
                bound,
                store,
                initializer,
                (
                    child(initializer, access.expression),
                    child(initializer, access.argument_expression),
                ),
                true,
                members,
            )?
        }
        _ => {
            return Err(unsupported(
                initializer,
                initializer_record.kind,
                SourceSyntaxRole::VariableInitializer,
            ));
        }
    };

    Ok(SourceNamespaceAmbientVariablePlan {
        declaration,
        symbol,
        initializer,
        value,
    })
}

fn plan_namespace_ambient_enum_member(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    access: NodeRef,
    nodes: (NodeRef, NodeRef),
    computed: bool,
    members: &[SourceNamespaceMemberPlan],
) -> Result<SourceNamespaceAmbientInitializer, SourceCheckError> {
    let (receiver, name) = nodes;
    let receiver_record = owned_node(arena, bound, store, receiver)?;
    let NodeData::Identifier(identifier) = &receiver_record.data else {
        return Err(unsupported(
            receiver,
            receiver_record.kind,
            SourceSyntaxRole::VariableInitializer,
        ));
    };
    if receiver_record.kind != SyntaxKind::Identifier
        || receiver_record.flags.0 != 0
        || receiver_record.parent != Some(access.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(unsupported(
            receiver,
            receiver_record.kind,
            SourceSyntaxRole::VariableInitializer,
        ));
    }
    let name_record = owned_node(arena, bound, store, name)?;
    if name_record.flags.0 != 0 || name_record.parent != Some(access.node) {
        return Err(unsupported(
            name,
            name_record.kind,
            SourceSyntaxRole::VariableInitializer,
        ));
    }
    let (member_name, key) = match &name_record.data {
        NodeData::Identifier(identifier)
            if !computed
                && name_record.kind == SyntaxKind::Identifier
                && identifier.flow_node.is_none()
                && !identifier.text.is_empty() =>
        {
            (identifier.text.as_str(), None)
        }
        NodeData::StringLiteral(literal)
            if computed
                && name_record.kind == SyntaxKind::StringLiteral
                && literal.token_flags.0 == 0 =>
        {
            (literal.text.as_str(), Some(literal.text.clone()))
        }
        NodeData::NoSubstitutionTemplateLiteral(literal)
            if computed
                && name_record.kind == SyntaxKind::NoSubstitutionTemplateLiteral
                && literal.token_flags.0 == 0
                && literal.template_flags.0 == 0
                && literal.symbol.is_none() =>
        {
            (literal.text.as_str(), Some(literal.text.clone()))
        }
        _ => {
            return Err(unsupported(
                name,
                name_record.kind,
                SourceSyntaxRole::VariableInitializer,
            ));
        }
    };
    let mut candidates = members.iter().filter_map(|member| match member {
        SourceNamespaceMemberPlan::EmptyEnum { symbol, .. }
            if store
                .symbol(*symbol)
                .and_then(|record| record.name().as_utf8())
                == Some(identifier.text.as_str()) =>
        {
            Some(*symbol)
        }
        _ => None,
    });
    let Some(owner) = candidates.next() else {
        return Err(unsupported(
            receiver,
            receiver_record.kind,
            SourceSyntaxRole::VariableInitializer,
        ));
    };
    let member = store
        .symbol(owner)
        .and_then(ts_binder::semantic::Symbol::exports)
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get_source(member_name))
        .and_then(|member| store.get_merged_symbol(member));
    let Some(member) = member else {
        return Err(unsupported(
            name,
            name_record.kind,
            SourceSyntaxRole::VariableInitializer,
        ));
    };
    if candidates.next().is_some()
        || store.symbol(member).is_none_or(|record| {
            record.flags() != SymbolFlags::ENUM_MEMBER || record.parent() != Some(owner)
        })
        || store
            .symbol_node_links(receiver)
            .is_some_and(|links| links.resolved_symbol.is_some_and(|cached| cached != owner))
        || store
            .symbol_node_links(access)
            .is_some_and(|links| links.resolved_symbol.is_some_and(|cached| cached != member))
    {
        return Err(unsupported(
            access,
            arena
                .get(access.node)
                .map_or(SyntaxKind::Unknown, |record| record.kind),
            SourceSyntaxRole::VariableInitializer,
        ));
    }

    Ok(SourceNamespaceAmbientInitializer::EnumMember {
        owner,
        member,
        receiver,
        name,
        key,
    })
}

fn plan_namespace_variables(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: (NodeRef, SemanticSymbolId),
    ambient: bool,
    statement: NodeRef,
    output: NamespaceVariablePlans<'_>,
) -> Result<(), SourceCheckError> {
    let (namespace, owner) = namespace;
    let NamespaceVariablePlans {
        members,
        implicit_variables,
        ambient_variables,
        object_initializers,
        diagnostics,
    } = output;
    let record = owned_node(arena, bound, store, statement)?;
    let NodeData::VariableStatement(variable) = &record.data else {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MismatchedNodeData {
                node: statement,
                kind: record.kind,
            },
        ));
    };
    let (exported, declared) =
        modifier_flags(arena, bound, store, statement, variable.modifiers.as_ref())?;
    let runtime = !ambient && !declared;
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
    if runtime && (list_record.flags.0 != 0 || declarations.declarations.nodes.len() != 1) {
        return Err(unsupported(
            statement,
            record.kind,
            SourceSyntaxRole::VariableStatement,
        ));
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
        if runtime && variable.initializer.is_none() {
            return Err(unsupported(
                statement,
                record.kind,
                SourceSyntaxRole::VariableStatement,
            ));
        }
        if runtime && exported && variable.type_.is_some() {
            return Err(unsupported(
                statement,
                record.kind,
                SourceSyntaxRole::VariableStatement,
            ));
        }
        let initialized_ambient_export = !runtime
            && ambient
            && exported
            && !declared
            && list_record.flags.0 == NODE_FLAG_CONST
            && declarations.declarations.nodes.len() == 1
            && variable.type_.is_none()
            && variable.initializer.is_some_and(|initializer| {
                arena.get(initializer).is_some_and(|record| {
                    matches!(
                        record.kind,
                        SyntaxKind::StringLiteral
                            | SyntaxKind::NoSubstitutionTemplateLiteral
                            | SyntaxKind::PropertyAccessExpression
                            | SyntaxKind::ElementAccessExpression
                    )
                })
            });
        if !runtime && let Some(initializer) = variable.initializer {
            if !ambient || list_record.flags.0 != NODE_FLAG_CONST {
                return Err(unsupported(
                    declaration,
                    declaration_record.kind,
                    SourceSyntaxRole::VariableInitializer,
                ));
            }
            let initializer = child(declaration, initializer);
            if !initialized_ambient_export {
                plan_namespace_numeric_initializer(arena, bound, store, declaration, initializer)?;
                if variable.type_.is_some() {
                    diagnostics.push(NamespaceDiagnosticPlan {
                        node: initializer,
                        code: 1039,
                    });
                }
            }
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
        if initialized_ambient_export {
            let initializer = child(
                declaration,
                variable
                    .initializer
                    .expect("an initialized ambient export retains its initializer"),
            );
            ambient_variables.push(plan_namespace_ambient_initializer(
                arena,
                bound,
                store,
                owner,
                (declaration, symbol, initializer),
                members,
            )?);
            continue;
        }
        if let Some(annotation) = variable.type_ {
            let annotation = child(declaration, annotation);
            let annotation_record = owned_node(arena, bound, store, annotation)?;
            if annotation_record.parent != Some(declaration.node) {
                return Err(invalid_parent(
                    annotation,
                    declaration,
                    annotation_record.parent,
                ));
            }
            if runtime {
                let initializer = child(
                    declaration,
                    variable
                        .initializer
                        .expect("a runtime namespace variable requires an initializer"),
                );
                object_initializers.push(plan_namespace_object_initializer(
                    arena,
                    bound,
                    store,
                    (namespace, owner),
                    (declaration, symbol, annotation, initializer),
                    members,
                )?);
            }
            members.push(SourceNamespaceMemberPlan::AmbientVariable {
                declaration,
                symbol,
                annotation,
            });
            continue;
        }

        let name = child(declaration, variable.name);
        let name_record = owned_node(arena, bound, store, name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(unsupported(
                name,
                name_record.kind,
                SourceSyntaxRole::VariableName,
            ));
        };
        let expected_flags = match list_record.flags.0 {
            0 => SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            NODE_FLAG_LET | NODE_FLAG_CONST => SymbolFlags::BLOCK_SCOPED_VARIABLE,
            _ => {
                return Err(unsupported(
                    list,
                    list_record.kind,
                    SourceSyntaxRole::VariableDeclarationList,
                ));
            }
        };
        let symbol_record = store.symbol(symbol).ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ))?;
        let value_declaration = symbol_record.value_declaration();
        let valid_runtime_binding = if !runtime {
            true
        } else if exported {
            bound
                .local_symbol(declaration)
                .and_then(|local| store.symbol(local).map(|record| (local, record)))
                .is_some_and(|(local, local_record)| {
                    store.get_parent_of_symbol(symbol) == Some(owner)
                        && store.get_merged_symbol(local) == Some(local)
                        && local_record.flags() == SymbolFlags::EXPORT_VALUE
                        && local_record.check_flags() == CheckFlags::NONE
                        && local_record.declarations() == Some(&[declaration])
                        && local_record.value_declaration().is_none()
                        && local_record.name().as_utf8() == Some(identifier.text.as_str())
                        && local_record.members().is_none()
                        && local_record.exports().is_none()
                        && local_record.parent().is_none()
                        && local_record.export_symbol() == Some(symbol)
                        && bound
                            .locals(namespace)
                            .and_then(|locals| store.symbol_table(locals))
                            .and_then(|locals| locals.get_source(&identifier.text))
                            == Some(local)
                        && store
                            .symbol(owner)
                            .and_then(ts_binder::semantic::Symbol::exports)
                            .and_then(|exports| store.symbol_table(exports))
                            .and_then(|exports| exports.get_source(&identifier.text))
                            .and_then(|candidate| store.get_merged_symbol(candidate))
                            == Some(symbol)
                })
        } else {
            symbol_record.parent().is_none()
                && bound
                    .locals(namespace)
                    .and_then(|locals| store.symbol_table(locals))
                    .and_then(|locals| locals.get_source(&identifier.text))
                    .and_then(|candidate| store.get_merged_symbol(candidate))
                    == Some(symbol)
        };
        if record.flags.0 != 0
            || variable.exclamation_token.is_some()
            || variable.local_symbol.is_some()
            || variable.symbol.is_some()
            || variable.facts != 0
            || declaration_record.kind != SyntaxKind::VariableDeclaration
            || declaration_record.flags.0 != 0
            || list_record.kind != SyntaxKind::VariableDeclarationList
            || declarations.facts != 0
            || declarations.declarations.has_trailing_comma
            || name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || name_record.parent != Some(declaration.node)
            || identifier.flow_node.is_some()
            || identifier.text.is_empty()
            || symbol_record.flags() != expected_flags
            || symbol_record.check_flags() != CheckFlags::NONE
            || symbol_record.declarations().is_none_or(|declarations| {
                !declarations.contains(&declaration)
                    || value_declaration.is_none_or(|value| !declarations.contains(&value))
            })
            || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
            || symbol_record.members().is_some()
            || symbol_record.exports().is_some()
            || symbol_record.export_symbol().is_some()
            || runtime
                && (symbol_record.declarations() != Some(&[declaration])
                    || value_declaration != Some(declaration)
                    || declaration_symbol(bound, store, namespace, SymbolFlags::MODULE)? != owner
                    || !valid_runtime_binding)
        {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::MissingVariableType(declaration),
            ));
        }
        let initializer = variable
            .initializer
            .map(|initializer| child(declaration, initializer));
        if let Some(initializer) = initializer {
            plan_namespace_numeric_initializer(arena, bound, store, declaration, initializer)?;
        }
        implicit_variables.push(SourceNamespaceImplicitVariablePlan {
            declaration,
            symbol,
            name: identifier.text.clone(),
            primary_declaration: value_declaration == Some(declaration),
            initializer,
        });
    }
    Ok(())
}

fn plan_namespace_numeric_initializer(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    initializer: NodeRef,
) -> Result<ts_jsnum::Number, SourceCheckError> {
    let record = owned_node(arena, bound, store, initializer)?;
    if record.parent != Some(declaration.node) {
        return Err(invalid_parent(initializer, declaration, record.parent));
    }
    let NodeData::NumericLiteral(literal) = &record.data else {
        return Err(unsupported(
            initializer,
            record.kind,
            SourceSyntaxRole::VariableInitializer,
        ));
    };
    if record.kind != SyntaxKind::NumericLiteral
        || record.flags.0 != 0
        || literal.token_flags.0 != 0
    {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::InvalidLiteralFlags(initializer),
        ));
    }
    let value = ts_jsnum::from_string(&literal.text);
    if value.is_nan() {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::InvalidLiteralSpelling(initializer),
        ));
    }
    if let Some(source) = arena.source_text() {
        let spelling = source
            .get(record.range.start.get() as usize..record.range.end.get() as usize)
            .and_then(normalize_numeric_separators)
            .ok_or(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::InvalidLiteralSpelling(initializer),
            ))?;
        let source_value = ts_jsnum::from_string(&spelling);
        if source_value.is_nan() || source_value != value {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::InvalidLiteralSpelling(initializer),
            ));
        }
    }
    Ok(value)
}

fn cached_namespace_numeric_literal(
    store: &CanonicalTypeMapperStore,
    value: ts_jsnum::Number,
) -> Result<Option<TypeId>, SourceCheckError> {
    let Some(regular) = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| bootstrap.cached_number_literal_type(value))
    else {
        return Ok(None);
    };
    if matches!(
        store
            .type_payload(regular)
            .map(super::type_records::TypeRecord::data),
        Some(TypeData::Literal(literal)) if literal.fresh_type.is_none()
    ) {
        return Ok(None);
    }
    store
        .fresh_type_of_literal_type(regular)
        .map(Some)
        .map_err(Into::into)
}

fn cached_namespace_string_literal(
    store: &CanonicalTypeMapperStore,
    value: &str,
) -> Result<Option<TypeId>, SourceCheckError> {
    let Some(regular) = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| bootstrap.cached_string_literal_type(value))
    else {
        return Ok(None);
    };
    if matches!(
        store
            .type_payload(regular)
            .map(super::type_records::TypeRecord::data),
        Some(TypeData::Literal(literal)) if literal.fresh_type.is_none()
    ) {
        return Ok(None);
    }
    store
        .fresh_type_of_literal_type(regular)
        .map(Some)
        .map_err(Into::into)
}

fn plan_invalid_ambient_export_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    declaration: NodeRef,
) -> Result<NamespaceDiagnosticPlan, SourceCheckError> {
    let record = owned_node(arena, bound, store, declaration)?;
    let NodeData::ExportAssignment(export) = &record.data else {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    };
    if record.kind != SyntaxKind::ExportAssignment
        || record.flags.0 != 0
        || export.flow_node.is_some()
        || export.symbol.is_some()
        || export.type_.is_some()
        || export.facts != 0
        || export.modifiers.is_some()
    {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    }

    let symbol = declaration_symbol(bound, store, declaration, SymbolFlags::PROPERTY)?;
    let symbol_record = store.symbol(symbol).ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
    ))?;
    let expected_name = if export.is_export_equals {
        InternalSymbolName::ExportEquals.as_ref()
    } else {
        InternalSymbolName::Default.as_ref()
    };
    if symbol_record.flags() != SymbolFlags::PROPERTY
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name() != expected_name
        || symbol_record.declarations() != Some(&[declaration])
        || symbol_record.value_declaration() != Some(declaration)
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.export_symbol().is_some()
        || store.get_parent_of_symbol(symbol) != Some(owner)
        || store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(expected_name))
            != Some(symbol)
    {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ));
    }

    let expression = child(declaration, export.expression);
    let expression_record = owned_node(arena, bound, store, expression)?;
    let NodeData::TypeOfExpression(type_of) = &expression_record.data else {
        return Err(unsupported(
            expression,
            expression_record.kind,
            SourceSyntaxRole::Statement,
        ));
    };
    if expression_record.kind != SyntaxKind::TypeOfExpression
        || expression_record.flags.0 != 0
        || expression_record.parent != Some(declaration.node)
        || expression_record.range.start < record.range.start
        || expression_record.range.end > record.range.end
    {
        return Err(unsupported(
            expression,
            expression_record.kind,
            SourceSyntaxRole::Statement,
        ));
    }

    let operand = child(expression, type_of.expression);
    let operand_record = owned_node(arena, bound, store, operand)?;
    if operand_record.flags.0 != 0 || operand_record.parent != Some(expression.node) {
        return Err(unsupported(
            operand,
            operand_record.kind,
            SourceSyntaxRole::Statement,
        ));
    }
    match &operand_record.data {
        NodeData::Identifier(identifier)
            if operand_record.kind == SyntaxKind::Identifier
                && identifier.flow_node.is_none()
                && !identifier.text.is_empty() => {}
        NodeData::PropertyAccessExpression(access)
            if operand_record.kind == SyntaxKind::PropertyAccessExpression
                && access.flow_node.is_none()
                && access.question_dot_token.is_none()
                && access.facts == 0 =>
        {
            let base = child(operand, access.expression);
            let base_record = owned_node(arena, bound, store, base)?;
            let NodeData::Identifier(identifier) = &base_record.data else {
                return Err(unsupported(
                    base,
                    base_record.kind,
                    SourceSyntaxRole::Statement,
                ));
            };
            let name = child(operand, access.name);
            let name_record = owned_node(arena, bound, store, name)?;
            let NodeData::Identifier(property) = &name_record.data else {
                return Err(unsupported(
                    name,
                    name_record.kind,
                    SourceSyntaxRole::Statement,
                ));
            };
            if base_record.kind != SyntaxKind::Identifier
                || base_record.flags.0 != 0
                || base_record.parent != Some(operand.node)
                || identifier.flow_node.is_some()
                || identifier.text.is_empty()
                || name_record.kind != SyntaxKind::Identifier
                || name_record.flags.0 != 0
                || name_record.parent != Some(operand.node)
                || property.flow_node.is_some()
                || property.text != "default"
            {
                return Err(unsupported(
                    operand,
                    operand_record.kind,
                    SourceSyntaxRole::Statement,
                ));
            }
        }
        _ => {
            return Err(unsupported(
                operand,
                operand_record.kind,
                SourceSyntaxRole::Statement,
            ));
        }
    }

    Ok(NamespaceDiagnosticPlan {
        node: expression,
        code: AMBIENT_EXPORT_ASSIGNMENT_MUST_BE_ENTITY_NAME,
    })
}

fn plan_ambient_export_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: (NodeRef, SemanticSymbolId),
    declaration: NodeRef,
) -> Result<Option<SourceNamespaceImportPlan>, SourceCheckError> {
    let (namespace, owner) = namespace;
    let record = owned_node(arena, bound, store, declaration)?;
    let NodeData::ExportAssignment(export) = &record.data else {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    };
    let reference = child(declaration, export.expression);
    let expression = owned_node(arena, bound, store, reference)?;
    let NodeData::Identifier(identifier) = &expression.data else {
        return Ok(None);
    };
    if record.kind != SyntaxKind::ExportAssignment
        || record.flags.0 != 0
        || !export.is_export_equals
        || export.flow_node.is_some()
        || export.symbol.is_some()
        || export.type_.is_some()
        || export.facts != 0
        || export.modifiers.is_some()
        || expression.kind != SyntaxKind::Identifier
        || expression.flags.0 != 0
        || expression.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    }
    let symbol = declaration_symbol(bound, store, declaration, SymbolFlags::ALIAS)?;
    let alias = store
        .symbol(symbol)
        .ok_or(SourceCheckError::Import(declaration))?;
    if alias.flags() != SymbolFlags::ALIAS
        || alias.check_flags() != CheckFlags::NONE
        || alias.name() != InternalSymbolName::ExportEquals.as_ref()
        || alias.declarations() != Some(&[declaration])
        || alias.value_declaration() != Some(declaration)
        || alias.members().is_some()
        || alias.exports().is_some()
        || alias.export_symbol().is_some()
        || store.get_parent_of_symbol(symbol) != Some(owner)
        || store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(InternalSymbolName::ExportEquals.as_ref()))
            != Some(symbol)
    {
        return Err(SourceCheckError::Import(declaration));
    }
    let local = bound
        .locals(namespace)
        .and_then(|locals| store.symbol_table(locals))
        .and_then(|locals| locals.get_source(&identifier.text))
        .and_then(|local| store.get_merged_symbol(local))
        .ok_or(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Import(declaration),
        ))?;
    let target = store
        .symbol(local)
        .map(|record| record.export_symbol().unwrap_or(local))
        .and_then(|target| store.get_merged_symbol(target))
        .ok_or(SourceCheckError::Import(declaration))?;
    Ok(Some(SourceNamespaceImportPlan {
        declaration,
        name_text: identifier.text.clone(),
        symbol,
        reference,
        ambient_target: Some(target),
        type_only: false,
    }))
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
    let is_external_augmentation = (is_string_module || is_global_augmentation)
        && is_external_module_augmentation(arena, bound, name, parent);

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
        if !is_external_augmentation {
            diagnostics.push(NamespaceDiagnosticPlan {
                node: name,
                code: GLOBAL_AUGMENTATION_CONTEXT,
            });
        }
    }
    if let NodeData::StringLiteral(module_name) = &name_record.data
        && !is_external_augmentation
    {
        if parent.node == bound.source_file() && !facts.is_external_or_common_js_module() {
            if ts_path::is_relative(&module_name.text)
                || ts_path::is_rooted_disk_path(&module_name.text)
            {
                diagnostics.push(NamespaceDiagnosticPlan {
                    node: name,
                    code: AMBIENT_MODULE_NAME_CANNOT_BE_RELATIVE,
                });
            }
        } else {
            diagnostics.push(NamespaceDiagnosticPlan {
                node: name,
                code: AMBIENT_MODULES_CANNOT_BE_NESTED,
            });
        }
    }

    let mut members = Vec::new();
    let mut imports = Vec::new();
    let mut implicit_variables = Vec::new();
    let mut ambient_variables = Vec::new();
    let mut object_initializers = Vec::new();
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
                            let member_symbol =
                                declaration_symbol(bound, store, statement, SymbolFlags::ENUM)?;
                            validate_symbol_parent(store, statement, member_symbol, Some(symbol))?;
                            let enum_host = DeclaredTypeHost::new([(arena, bound)])
                                .map_err(DeclaredTypeError::from)?;
                            super::enums::preflight_enum(store, &enum_host, member_symbol)
                                .map_err(|error| namespace_enum_error(statement, error))?;
                            members.push(SourceNamespaceMemberPlan::EmptyEnum {
                                declaration: statement,
                                symbol: member_symbol,
                            });
                        }
                        SyntaxKind::FunctionDeclaration => {
                            members.push(plan_namespace_function(
                                arena,
                                bound,
                                store,
                                (declaration, symbol),
                                ambient,
                                statement,
                            )?);
                        }
                        SyntaxKind::VariableStatement => {
                            plan_namespace_variables(
                                arena,
                                bound,
                                store,
                                (declaration, symbol),
                                ambient,
                                statement,
                                NamespaceVariablePlans {
                                    members: &mut members,
                                    implicit_variables: &mut implicit_variables,
                                    ambient_variables: &mut ambient_variables,
                                    object_initializers: &mut object_initializers,
                                    diagnostics: &mut diagnostics,
                                },
                            )?;
                        }
                        SyntaxKind::ImportEqualsDeclaration => {
                            imports.push(plan_namespace_import(
                                arena,
                                bound,
                                store,
                                declaration,
                                symbol,
                                statement,
                            )?);
                        }
                        SyntaxKind::ImportDeclaration
                            if ambient && is_string_module && facts.is_declaration_file() =>
                        {
                            imports.extend(plan_ambient_module_import(
                                arena,
                                bound,
                                store,
                                declaration,
                                statement,
                            )?);
                        }
                        SyntaxKind::ExportAssignment if ambient && is_string_module => {
                            if let Some(export) = plan_ambient_export_assignment(
                                arena,
                                bound,
                                store,
                                (declaration, symbol),
                                statement,
                            )? {
                                imports.push(export);
                            } else {
                                diagnostics.push(plan_invalid_ambient_export_assignment(
                                    arena, bound, store, symbol, statement,
                                )?);
                            }
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
        imports,
        implicit_variables,
        ambient_variables,
        object_initializers,
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
            SourceNamespaceMemberPlan::EmptyEnum { .. }
            | SourceNamespaceMemberPlan::Function { .. } => declarations.push(member),
        }
    }
    diagnostics.extend(plan.diagnostics.iter().copied());
}

fn namespace_imports<'plan>(
    plan: &'plan SourceNamespacePlan,
    imports: &mut Vec<&'plan SourceNamespaceImportPlan>,
) {
    imports.extend(&plan.imports);
    for member in &plan.members {
        if let SourceNamespaceMemberPlan::Namespace(nested) = member {
            namespace_imports(nested, imports);
        }
    }
}

fn namespace_implicit_variables<'plan>(
    plan: &'plan SourceNamespacePlan,
    variables: &mut Vec<&'plan SourceNamespaceImplicitVariablePlan>,
) {
    variables.extend(&plan.implicit_variables);
    for member in &plan.members {
        if let SourceNamespaceMemberPlan::Namespace(nested) = member {
            namespace_implicit_variables(nested, variables);
        }
    }
}

fn namespace_ambient_variables<'plan>(
    plan: &'plan SourceNamespacePlan,
    variables: &mut Vec<&'plan SourceNamespaceAmbientVariablePlan>,
) {
    variables.extend(&plan.ambient_variables);
    for member in &plan.members {
        if let SourceNamespaceMemberPlan::Namespace(nested) = member {
            namespace_ambient_variables(nested, variables);
        }
    }
}

fn namespace_object_initializers<'plan>(
    plan: &'plan SourceNamespacePlan,
    initializers: &mut Vec<&'plan SourceNamespaceObjectInitializerPlan>,
) {
    initializers.extend(&plan.object_initializers);
    for member in &plan.members {
        if let SourceNamespaceMemberPlan::Namespace(nested) = member {
            namespace_object_initializers(nested, initializers);
        }
    }
}

fn namespace_import_is_circular(
    imports: &[ResolvedNamespaceImport<'_>],
    alias: SemanticSymbolId,
) -> bool {
    let mut visited = HashSet::new();
    let mut current = alias;
    while visited.insert(current) {
        let Some(import) = imports
            .iter()
            .find(|import| import.import.symbol == current)
        else {
            return false;
        };
        current = import.target;
    }
    true
}

fn resolve_qualified_namespace_import(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    imports: &[&SourceNamespaceImportPlan],
    import: &SourceNamespaceImportPlan,
    reference: NodeRef,
    resolving: &mut HashSet<SemanticSymbolId>,
) -> Result<SemanticSymbolId, SourceCheckError> {
    let (arena, bound) = host
        .source(reference)
        .ok_or_else(|| missing_node(reference))?;
    let record = owned_node(arena, bound, store, reference)?;
    let NodeData::QualifiedName(qualified) = &record.data else {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Import(import.declaration),
        ));
    };
    let left = child(reference, qualified.left);
    let left_record = owned_node(arena, bound, store, left)?;
    let mut namespace = match &left_record.data {
        NodeData::QualifiedName(_) => {
            resolve_qualified_namespace_import(store, host, imports, import, left, resolving)?
        }
        NodeData::Identifier(_) => {
            let mut resolver = host.name_resolver_host(store)?;
            resolver
                .resolve_entity_name(left, SymbolFlags::MODULE_MEMBER)
                .map_err(DeclaredTypeError::from)?
                .ok_or(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Import(import.declaration),
                ))?
        }
        _ => {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Import(import.declaration),
            ));
        }
    };

    let mut visited = HashSet::new();
    while store
        .symbol(namespace)
        .is_some_and(|record| record.flags() == SymbolFlags::ALIAS)
    {
        if !visited.insert(namespace) {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Import(import.declaration),
            ));
        }
        namespace = if let Some(candidate) = imports
            .iter()
            .copied()
            .find(|candidate| candidate.symbol == namespace)
        {
            if !resolving.insert(namespace) {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Import(import.declaration),
                ));
            }
            let target =
                resolve_namespace_import_target(store, host, imports, candidate, resolving);
            resolving.remove(&namespace);
            target?
        } else {
            store
                .alias_symbol_links(namespace)
                .and_then(|links| links.alias_target.symbol())
                .ok_or(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Import(import.declaration),
                ))?
        };
    }

    let owner = store
        .symbol(namespace)
        .filter(|record| record.flags().intersects(SymbolFlags::NAMESPACE))
        .ok_or(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Import(import.declaration),
        ))?;
    let right = child(reference, qualified.right);
    let right_record = owned_node(arena, bound, store, right)?;
    let NodeData::Identifier(name) = &right_record.data else {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Import(import.declaration),
        ));
    };
    store
        .module_symbol_links(namespace)
        .and_then(|links| links.resolved_exports)
        .or_else(|| owner.exports())
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get_source(&name.text))
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Import(import.declaration),
        ))
}

fn resolve_namespace_import_target(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    imports: &[&SourceNamespaceImportPlan],
    import: &SourceNamespaceImportPlan,
    resolving: &mut HashSet<SemanticSymbolId>,
) -> Result<SemanticSymbolId, SourceCheckError> {
    if let Some(target) = import.ambient_target {
        return (store.get_merged_symbol(target) == Some(target))
            .then_some(target)
            .ok_or(SourceCheckError::Import(import.declaration));
    }
    let resolution = {
        let mut resolution_host = host.name_resolver_host(store)?;
        resolution_host.resolve_entity_name(import.reference, SymbolFlags::MODULE_MEMBER)
    };
    match resolution {
        Ok(Some(target)) => Ok(target),
        Ok(None) => Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Import(import.declaration),
        )),
        Err(CanonicalNameResolutionError::AliasResolutionUnavailable(alias))
            if imports.iter().any(|candidate| candidate.symbol == alias) =>
        {
            resolve_qualified_namespace_import(
                store,
                host,
                imports,
                import,
                import.reference,
                resolving,
            )
        }
        Err(error) => Err(DeclaredTypeError::from(error).into()),
    }
}

fn preflight_namespace_imports<'plan>(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &'plan SourceNamespacePlan,
) -> Result<Vec<ResolvedNamespaceImport<'plan>>, SourceCheckError> {
    let mut imports = Vec::new();
    namespace_imports(plan, &mut imports);
    if imports.is_empty() {
        return Ok(Vec::new());
    }

    if message_by_code(CIRCULAR_DEFINITION_OF_IMPORT_ALIAS).is_none() {
        return Err(SourceCheckError::MissingDiagnostic(
            CIRCULAR_DEFINITION_OF_IMPORT_ALIAS,
        ));
    }
    let mut resolved_imports = Vec::with_capacity(imports.len());
    for &import in &imports {
        let target =
            resolve_namespace_import_target(store, host, &imports, import, &mut HashSet::new())?;
        let target_record = store
            .symbol(target)
            .ok_or(SourceCheckError::Import(import.declaration))?;
        if let Some(links) = store.alias_symbol_links(import.symbol)
            && (links
                .immediate_target
                .is_some_and(|cached| cached != target)
                || import.type_only
                    && links
                        .type_only_declaration
                        .is_some_and(|marker| marker != import.declaration)
                || target_record.flags() != SymbolFlags::ALIAS
                    && match links.alias_target {
                        AliasTargetState::Unresolved => false,
                        AliasTargetState::Resolved(cached) => cached != target,
                        AliasTargetState::Unknown => true,
                    })
        {
            return Err(SourceCheckError::Import(import.declaration));
        }
        resolved_imports.push(ResolvedNamespaceImport { import, target });
    }
    Ok(resolved_imports)
}

fn resolve_namespace_imports(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    imports: Vec<ResolvedNamespaceImport<'_>>,
) -> Result<(), SourceCheckError> {
    if imports.is_empty() {
        return Ok(());
    }

    let circular_message = message_by_code(CIRCULAR_DEFINITION_OF_IMPORT_ALIAS).ok_or(
        SourceCheckError::MissingDiagnostic(CIRCULAR_DEFINITION_OF_IMPORT_ALIAS),
    )?;
    let mut alias_host = NamespaceAliasTargetHost { imports };
    let mut circular = Vec::new();
    for index in 0..alias_host.imports.len() {
        let import = alias_host.imports[index].import;
        let immediate = CanonicalAliasResolver::new(store, &mut alias_host)
            .get_immediate_aliased_symbol(import.symbol)
            .map_err(|_| SourceCheckError::Import(import.declaration))?;
        if immediate != Some(alias_host.imports[index].target) {
            return Err(SourceCheckError::Import(import.declaration));
        }

        let resolution = CanonicalAliasResolver::new(store, &mut alias_host)
            .resolve_alias(import.symbol)
            .map_err(|_| SourceCheckError::Import(import.declaration))?;
        match resolution.target {
            AliasTargetState::Resolved(target) if store.symbol(target).is_some() => {}
            AliasTargetState::Unknown
                if namespace_import_is_circular(&alias_host.imports, import.symbol) => {}
            AliasTargetState::Resolved(_)
            | AliasTargetState::Unknown
            | AliasTargetState::Unresolved => {
                return Err(SourceCheckError::Import(import.declaration));
            }
        }
        for event in resolution.events {
            let CanonicalAliasResolutionEvent::CircularDefinitionOfImportAlias { alias } = event;
            let circular_import = alias_host
                .imports
                .iter()
                .find(|candidate| candidate.import.symbol == alias)
                .map(|candidate| candidate.import)
                .ok_or(SourceCheckError::Import(import.declaration))?;
            circular.push(circular_import);
        }
    }
    circular.sort_by_key(|import| {
        host.node(import.declaration)
            .map_or(u32::MAX, |node| node.range.start.get())
    });
    for import in circular {
        super::source::merge_retry_diagnostic(
            diagnostics,
            super::CanonicalCheckerDiagnostic {
                node: Some(import.declaration),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(
                    circular_message,
                    [import.name_text.clone()],
                ),
                related_information: Vec::new(),
            },
        );
    }
    Ok(())
}

fn invalid_generic_namespace_interface(declaration: NodeRef) -> SourceCheckError {
    unsupported(
        declaration,
        SyntaxKind::InterfaceDeclaration,
        SourceSyntaxRole::InterfaceDeclaration,
    )
}

fn namespace_enum_error(
    declaration: NodeRef,
    error: super::enums::EnumTypeError,
) -> SourceCheckError {
    match error {
        super::enums::EnumTypeError::Unsupported(_) => {
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Enum(declaration))
        }
        super::enums::EnumTypeError::Invariant(_) => SourceCheckError::Enum(declaration),
    }
}

fn stage_namespace_value(
    store: &CanonicalTypeMapperStore,
    values: &mut Vec<PendingNamespaceValue>,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    type_: TypeId,
) -> Result<(), SourceCheckError> {
    if let Some(existing) = values.iter().find(|value| value.symbol == symbol) {
        if existing.type_ != type_ {
            return Err(SourceCheckError::Variable(
                VariableInvariant::CachedValueTypeMismatch {
                    symbol,
                    cached: existing.type_,
                    expected: type_,
                },
            ));
        }
        return Ok(());
    }
    if let Some(existing) = store.value_symbol_links(symbol)
        && existing != &ValueSymbolLinks::default()
        && existing
            != &(ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
    {
        return Err(SourceCheckError::Variable(
            VariableInvariant::CachedValueTypeMismatch {
                symbol,
                cached: existing.resolved_type.unwrap_or(type_),
                expected: type_,
            },
        ));
    }
    values.push(PendingNamespaceValue {
        declaration,
        symbol,
        type_,
    });
    Ok(())
}

fn resolve_generic_namespace_property_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    property: &SourceNamespacePropertyPlan,
) -> Result<TypeId, SourceCheckError> {
    session.reset_query();
    let mut type_ = CanonicalTypeQuery::new_with_global_types_and_session(
        store,
        host,
        global_types,
        options,
        session,
        diagnostics,
    )?
    .get_type_from_type_node(property.annotation)?;
    if options.intrinsic.strict_null_checks && property.optional {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            ))?;
        let undefined = bootstrap.undefined_or_missing_type;
        let record = store.type_payload(type_).ok_or(SourceCheckError::Variable(
            VariableInvariant::InvalidSymbolShape(property.symbol),
        ))?;
        let already_optional = record
            .flags()
            .intersects(TypeFlags::ANY_OR_UNKNOWN | TypeFlags::UNDEFINED)
            || matches!(
                record.data(),
                TypeData::Union(union) if union.union.types.contains(&undefined)
            );
        if !already_optional {
            type_ = store.expression_union_type_with_global_types(
                global_types,
                &[type_, undefined],
                UnionReduction::Literal,
            )?;
        }
    }
    Ok(type_)
}

fn publish_generic_namespace_interface_members(
    store: &mut CanonicalTypeMapperStore,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    target: TypeId,
    generic: &SourceNamespaceGenericInterfacePlan,
    property_types: &[TypeId],
) -> Result<(), SourceCheckError> {
    let invalid = || invalid_generic_namespace_interface(declaration);
    if generic.properties.len() != property_types.len()
        || store
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            != Some(target)
        || store.symbol(symbol).is_none_or(|owner| {
            owner.flags() != SymbolFlags::INTERFACE
                || owner.members() != Some(generic.members)
                || store.get_parent_of_symbol(symbol).is_none()
        })
    {
        return Err(invalid());
    }
    let reference = validate_direct_generic_reference(store, target).map_err(|_| invalid())?;
    if reference.target != target
        || reference.type_arguments.len() != generic.type_parameters.len()
        || reference
            .type_arguments
            .iter()
            .zip(&generic.type_parameters)
            .any(|(type_, symbol)| {
                cached_ordinary_type_parameter_owner(store, *type_) != Some(*symbol)
            })
    {
        return Err(invalid());
    }
    let record = store.type_payload(target).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = record.data() else {
        return Err(invalid());
    };
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() & ObjectFlags::OBJECT_TYPE_KIND_MASK
            != ObjectFlags::INTERFACE | ObjectFlags::REFERENCE
        || record.symbol() != Some(symbol)
        || interface.resolved_base_constructor_type.is_some()
        || interface.resolved_base_types.is_some()
        || interface.declared_call_signatures.is_some()
        || interface.declared_construct_signatures.is_some()
        || interface.declared_index_infos.is_some()
    {
        return Err(invalid());
    }
    if interface.declared_members_resolved {
        if interface.declared_members == Some(generic.members)
            || interface
                .declared_members
                .and_then(|members| store.symbol_table(members))
                .map_or(0, ts_binder::semantic::SymbolTable::len)
                != generic.properties.len()
            || !generic
                .properties
                .iter()
                .zip(property_types)
                .all(|(property, type_)| {
                    interface
                        .declared_members
                        .and_then(|members| store.symbol_table(members))
                        .and_then(|members| members.get_source(&property.name))
                        == Some(property.symbol)
                        && store.value_symbol_links(property.symbol)
                            == Some(&ValueSymbolLinks {
                                resolved_type: Some(*type_),
                                ..ValueSymbolLinks::default()
                            })
                        && store.symbol(property.symbol).is_some_and(|record| {
                            record.check_flags()
                                == if property.readonly {
                                    CheckFlags::READONLY
                                } else {
                                    CheckFlags::NONE
                                }
                        })
                })
        {
            return Err(invalid());
        }
        return Ok(());
    }
    if record
        .object_flags()
        .contains(ObjectFlags::MEMBERS_RESOLVED)
        || interface.declared_members.is_some()
        || interface.reference.object.structured
            != super::type_records::StructuredTypeData::default()
    {
        return Err(invalid());
    }
    let bases_resolved = interface.base_types_resolved;
    let mut names = HashSet::with_capacity(generic.properties.len());
    for (property, type_) in generic.properties.iter().zip(property_types) {
        if store.type_payload(*type_).is_none()
            || !names.insert(property.name.as_str())
            || store
                .value_symbol_links(property.symbol)
                .is_some_and(|links| {
                    links != &ValueSymbolLinks::default()
                        && links
                            != &(ValueSymbolLinks {
                                resolved_type: Some(*type_),
                                ..ValueSymbolLinks::default()
                            })
                })
        {
            return Err(invalid());
        }
    }
    let prepared = if generic.properties.is_empty() {
        None
    } else {
        Some(PreparedSymbolTable::new(generic.properties.len()).ok_or_else(invalid)?)
    };
    let missing_links = generic
        .properties
        .iter()
        .filter(|property| store.value_symbol_links(property.symbol).is_none())
        .count();
    if !store.try_reserve_checker_symbol_allocations(0, usize::from(prepared.is_some()))
        || !store.try_reserve_value_symbol_links(missing_links)
    {
        return Err(invalid());
    }
    if !bases_resolved && !store.publish_interface_no_base_resolution(target) {
        return Err(invalid());
    }
    let declared_members = prepared.map(|table| store.alloc_prepared_symbol_table(table));
    for (property, type_) in generic.properties.iter().zip(property_types) {
        if !store.set_source_property_readonly(property.symbol, property.readonly)
            || !store.set_value_symbol_links(
                property.symbol,
                ValueSymbolLinks {
                    resolved_type: Some(*type_),
                    ..ValueSymbolLinks::default()
                },
            )
            || store.insert_symbol(
                declared_members.ok_or_else(invalid)?,
                EscapedName::source(&property.name),
                property.symbol,
            ) != Some(None)
        {
            return Err(invalid());
        }
    }
    if !store.set_interface_declared_members(target, true, declared_members, None, None, None) {
        return Err(invalid());
    }
    Ok(())
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
    let mut implicit_variables = Vec::new();
    let mut ambient_variables = Vec::new();
    let mut object_initializers = Vec::new();
    namespace_annotations(
        plan,
        &mut annotations,
        &mut declarations,
        &mut planned_diagnostics,
    );
    namespace_implicit_variables(plan, &mut implicit_variables);
    namespace_ambient_variables(plan, &mut ambient_variables);
    namespace_object_initializers(plan, &mut object_initializers);
    implicit_variables.sort_by_key(|variable| {
        host.node(variable.declaration)
            .map_or(u32::MAX, |node| node.range.start.get())
    });
    for diagnostic in &planned_diagnostics {
        if message_by_code(diagnostic.code).is_none() {
            return Err(SourceCheckError::MissingDiagnostic(diagnostic.code));
        }
    }
    if options.no_implicit_any
        && implicit_variables
            .iter()
            .any(|variable| variable.primary_declaration && variable.initializer.is_none())
        && message_by_code(VARIABLE_IMPLICITLY_HAS_ANY_TYPE).is_none()
    {
        return Err(SourceCheckError::MissingDiagnostic(
            VARIABLE_IMPLICITLY_HAS_ANY_TYPE,
        ));
    }
    for declaration in &declarations {
        let SourceNamespaceMemberPlan::Function {
            declaration,
            symbol,
        } = declaration
        else {
            continue;
        };
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
        .preflight_type_of_source_callable(*declaration, *symbol)?;
        debug_assert!(staged.is_empty());
    }

    let mut values = Vec::<PendingNamespaceValue>::new();
    let mut numeric_initializers = Vec::new();
    if !implicit_variables.is_empty()
        || !ambient_variables.is_empty()
        || !object_initializers.is_empty()
    {
        let bootstrap = store
            .intrinsic_bootstrap()
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            ))?;
        let any = bootstrap.any_type;
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let mut strings = Vec::new();
        for variable in &implicit_variables {
            let type_ = if let Some(initializer) = variable.initializer {
                let value = plan_namespace_numeric_initializer(
                    arena,
                    bound,
                    store,
                    variable.declaration,
                    initializer,
                )?;
                let expected = cached_namespace_numeric_literal(store, value)?;
                if let Some(links) = store.type_node_links(initializer)
                    && (links.outer_type_parameters.is_some()
                        || links
                            .resolved_type
                            .is_some_and(|cached| Some(cached) != expected))
                {
                    return Err(SourceCheckError::Assertion(
                        SourceAssertionError::InvalidExpressionCache {
                            node: initializer,
                            cached: links.resolved_type,
                            expected: expected.unwrap_or(number),
                        },
                    ));
                }
                numeric_initializers.push((initializer, value));
                number
            } else {
                any
            };
            stage_namespace_value(
                store,
                &mut values,
                variable.declaration,
                variable.symbol,
                type_,
            )?;
        }
        for initializer in &object_initializers {
            let state = object_members::object_literal_state(store, &initializer.object)
                .map_err(|error| namespace_object_error(initializer.object.node, error))?;
            if state.is_some() {
                object_members::validate_resolved_property_types(
                    store,
                    &initializer.object,
                    &vec![number; initializer.object.properties.len()],
                )
                .map_err(|error| namespace_object_error(initializer.object.node, error))?;
            }
            if let Some(links) = store.value_symbol_links(initializer.symbol)
                && links != &ValueSymbolLinks::default()
                && store
                    .declared_type_links(initializer.interface)
                    .and_then(|declared| declared.declared_type)
                    != links.resolved_type
            {
                return Err(SourceCheckError::Variable(
                    VariableInvariant::InvalidValueLinks(initializer.symbol),
                ));
            }
            for property in &initializer.object.properties {
                let value = plan_namespace_numeric_initializer(
                    arena,
                    bound,
                    store,
                    property.declaration,
                    property.type_node,
                )?;
                let expected = cached_namespace_numeric_literal(store, value)?;
                let links = store.type_node_links(property.type_node);
                if links.is_some_and(|links| {
                    links.outer_type_parameters.is_some()
                        || links
                            .resolved_type
                            .is_some_and(|cached| Some(cached) != expected)
                }) || state.is_some() && links.and_then(|links| links.resolved_type) != expected
                {
                    return Err(SourceCheckError::Assertion(
                        SourceAssertionError::InvalidExpressionCache {
                            node: property.type_node,
                            cached: links.and_then(|links| links.resolved_type),
                            expected: expected.unwrap_or(number),
                        },
                    ));
                }
                numeric_initializers.push((property.type_node, value));
            }
        }
        for variable in &ambient_variables {
            match &variable.value {
                SourceNamespaceAmbientInitializer::String(value) => {
                    let expected = cached_namespace_string_literal(store, value)?;
                    if let Some(links) = store.type_node_links(variable.initializer)
                        && (links.outer_type_parameters.is_some()
                            || links
                                .resolved_type
                                .is_some_and(|cached| Some(cached) != expected))
                    {
                        return Err(SourceCheckError::Assertion(
                            SourceAssertionError::InvalidExpressionCache {
                                node: variable.initializer,
                                cached: links.resolved_type,
                                expected: expected.unwrap_or(string),
                            },
                        ));
                    }
                    if let Some(links) = store.value_symbol_links(variable.symbol)
                        && links != &ValueSymbolLinks::default()
                        && links.resolved_type != expected
                    {
                        return Err(SourceCheckError::Variable(
                            VariableInvariant::InvalidValueLinks(variable.symbol),
                        ));
                    }
                    strings.push(value.clone());
                }
                SourceNamespaceAmbientInitializer::EnumMember {
                    owner,
                    member,
                    receiver,
                    name,
                    key,
                } => {
                    let receiver_type = store
                        .value_symbol_links(*owner)
                        .and_then(|links| links.resolved_type);
                    let member_type = store
                        .value_symbol_links(*member)
                        .and_then(|links| links.resolved_type);
                    for (node, expected) in [
                        (*receiver, receiver_type),
                        (variable.initializer, member_type),
                    ] {
                        if let Some(links) = store.type_node_links(node)
                            && (links.outer_type_parameters.is_some()
                                || links
                                    .resolved_type
                                    .is_some_and(|cached| Some(cached) != expected))
                        {
                            return Err(SourceCheckError::Assertion(
                                SourceAssertionError::InvalidExpressionCache {
                                    node,
                                    cached: links.resolved_type,
                                    expected: expected.unwrap_or(any),
                                },
                            ));
                        }
                    }
                    if let Some(links) = store.value_symbol_links(variable.symbol)
                        && links != &ValueSymbolLinks::default()
                        && links.resolved_type != member_type
                    {
                        return Err(SourceCheckError::Variable(
                            VariableInvariant::InvalidValueLinks(variable.symbol),
                        ));
                    }
                    if let Some(key) = key {
                        let expected = cached_namespace_string_literal(store, key)?;
                        if let Some(links) = store.type_node_links(*name)
                            && (links.outer_type_parameters.is_some()
                                || links
                                    .resolved_type
                                    .is_some_and(|cached| Some(cached) != expected))
                        {
                            return Err(SourceCheckError::Assertion(
                                SourceAssertionError::InvalidExpressionCache {
                                    node: *name,
                                    cached: links.resolved_type,
                                    expected: expected.unwrap_or(string),
                                },
                            ));
                        }
                        strings.push(key.clone());
                    }
                }
            }
        }
        let numbers = numeric_initializers
            .iter()
            .map(|(_, value)| *value)
            .collect::<Vec<_>>();
        store.prepare_regular_literal_types(&strings, &numbers, &[])?;
        let missing_initializer_links = numeric_initializers
            .iter()
            .filter(|(initializer, _)| store.type_node_links(*initializer).is_none())
            .count()
            + ambient_variables
                .iter()
                .map(|variable| match &variable.value {
                    SourceNamespaceAmbientInitializer::String(_) => {
                        usize::from(store.type_node_links(variable.initializer).is_none())
                    }
                    SourceNamespaceAmbientInitializer::EnumMember {
                        receiver,
                        name,
                        key,
                        ..
                    } => {
                        usize::from(store.type_node_links(variable.initializer).is_none())
                            + usize::from(store.type_node_links(*receiver).is_none())
                            + usize::from(key.is_some() && store.type_node_links(*name).is_none())
                    }
                })
                .sum::<usize>();
        if !store.try_reserve_type_node_links(missing_initializer_links) {
            return Err(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::Capacity,
            ));
        }
        let missing_symbol_links = ambient_variables
            .iter()
            .filter_map(|variable| match &variable.value {
                SourceNamespaceAmbientInitializer::EnumMember { receiver, .. } => Some(
                    usize::from(store.symbol_node_links(*receiver).is_none())
                        + usize::from(store.symbol_node_links(variable.initializer).is_none()),
                ),
                SourceNamespaceAmbientInitializer::String(_) => None,
            })
            .sum();
        if !store.try_reserve_symbol_node_links(missing_symbol_links) {
            return Err(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::Capacity,
            ));
        }
    }

    let imports = preflight_namespace_imports(store, host, plan)?;
    let mut alias_dependent_annotations = Vec::new();
    for annotation in annotations {
        session.reset_query();
        let mut staged = CanonicalCheckerDiagnostics::default();
        let result = CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            global_types,
            options,
            session,
            &mut staged,
        )?
        .preflight_type_from_type_node(annotation);
        match result {
            Ok(()) => {}
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::ImportAliasTypeReference { alias, .. },
            )) if imports.iter().any(|import| import.import.symbol == alias) => {
                alias_dependent_annotations.push(annotation);
            }
            Err(error) => return Err(error.into()),
        }
        debug_assert!(staged.is_empty());
    }

    resolve_namespace_imports(store, host, diagnostics, imports)?;
    for annotation in alias_dependent_annotations {
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
            SourceNamespaceMemberPlan::Interface {
                declaration,
                symbol,
                generic,
                ..
            } => {
                let heritage = host.node(*declaration).is_some_and(|record| {
                    matches!(
                        &record.data,
                        NodeData::InterfaceDeclaration(interface)
                            if interface.heritage_clauses.is_some()
                    )
                });
                let target = if heritage {
                    store.get_declared_type_of_symbol(host, *symbol)?
                } else {
                    CanonicalTypeQuery::new_with_global_types_and_session(
                        store,
                        host,
                        global_types,
                        options,
                        session,
                        diagnostics,
                    )?
                    .get_declared_type_of_symbol(*symbol)?
                };
                if let Some(generic) = generic {
                    let mut property_types = Vec::with_capacity(generic.properties.len());
                    for property in &generic.properties {
                        property_types.push(resolve_generic_namespace_property_type(
                            store,
                            host,
                            global_types,
                            options,
                            session,
                            diagnostics,
                            property,
                        )?);
                    }
                    publish_generic_namespace_interface_members(
                        store,
                        *declaration,
                        *symbol,
                        target,
                        generic,
                        &property_types,
                    )?;
                }
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
                stage_namespace_value(store, &mut values, *declaration, *symbol, type_)?;
            }
            SourceNamespaceMemberPlan::Namespace(_) => {
                unreachable!("nested namespaces are expanded before semantic execution")
            }
            SourceNamespaceMemberPlan::EmptyEnum {
                declaration,
                symbol,
            } => {
                super::enums::get_enum_semantics(store, host, *symbol)
                    .map_err(|error| namespace_enum_error(*declaration, error))?;
            }
            SourceNamespaceMemberPlan::Function {
                declaration,
                symbol,
            } => {
                let callable = CanonicalTypeQuery::new_with_global_types_and_session(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                )?
                .get_type_of_source_callable(*declaration, *symbol)?;
                let signature = store
                    .source_callable_provenance(callable)
                    .filter(|provenance| {
                        provenance.declaration == *declaration && provenance.owner_symbol == *symbol
                    })
                    .map(|provenance| provenance.signature)
                    .ok_or(SourceCheckError::Function(
                        SourceFunctionInvariant::Callable(*declaration),
                    ))?;
                let callable_plan = source_callables::plan_source_callable(
                    store,
                    host,
                    *declaration,
                    *symbol,
                    Some(CanonicalArrayTargets::from_global_types(global_types)),
                )
                .map_err(|error| namespace_callable_error(*declaration, error))?;
                let void = store
                    .intrinsic_bootstrap()
                    .ok_or(SourceCheckError::LiteralCache(
                        SourceLiteralCacheError::BootstrapUninitialized,
                    ))?
                    .void_type;
                if callable_plan.body_mode.is_ambient() {
                    let return_type = CanonicalTypeQuery::new_with_global_types_and_session(
                        store,
                        host,
                        global_types,
                        options,
                        session,
                        diagnostics,
                    )?
                    .get_return_type_of_signature(signature)?;
                    if return_type != void {
                        return Err(SourceCheckError::Function(
                            SourceFunctionInvariant::Callable(*declaration),
                        ));
                    }
                } else {
                    source_callables::publish_inferred_source_callable_return(
                        store,
                        &callable_plan,
                        signature,
                        void,
                    )
                    .map_err(|error| namespace_callable_error(*declaration, error))?;
                }
                stage_namespace_value(store, &mut values, *declaration, *symbol, callable)?;
            }
        }
    }

    let mut ambient_expression_types = Vec::<(NodeRef, TypeId)>::new();
    let mut ambient_expression_symbols = Vec::<(NodeRef, SemanticSymbolId)>::new();
    for variable in ambient_variables {
        let type_ = match &variable.value {
            SourceNamespaceAmbientInitializer::String(value) => {
                let regular = store.regular_string_literal_type(value.clone())?;
                let fresh = store.fresh_type_of_literal_type(regular)?;
                ambient_expression_types.push((variable.initializer, fresh));
                fresh
            }
            SourceNamespaceAmbientInitializer::EnumMember {
                owner,
                member,
                receiver,
                name,
                key,
            } => {
                let receiver_type = store
                    .value_symbol_links(*owner)
                    .and_then(|links| links.resolved_type)
                    .ok_or(SourceCheckError::Enum(*receiver))?;
                let member_name = store
                    .symbol(*member)
                    .and_then(|record| record.name().as_utf8())
                    .ok_or(SourceCheckError::Enum(variable.initializer))?;
                let (resolved, type_) =
                    super::enums::enum_value_member_type(store, receiver_type, member_name)
                        .ok_or(SourceCheckError::Enum(variable.initializer))?;
                if resolved != *member {
                    return Err(SourceCheckError::Enum(variable.initializer));
                }
                ambient_expression_types.push((*receiver, receiver_type));
                ambient_expression_symbols.push((*receiver, *owner));
                if let Some(key) = key {
                    let regular = store.regular_string_literal_type(key.clone())?;
                    let fresh = store.fresh_type_of_literal_type(regular)?;
                    ambient_expression_types.push((*name, fresh));
                }
                ambient_expression_types.push((variable.initializer, type_));
                ambient_expression_symbols.push((variable.initializer, *member));
                type_
            }
        };
        stage_namespace_value(
            store,
            &mut values,
            variable.declaration,
            variable.symbol,
            type_,
        )?;
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
    for (initializer, value) in numeric_initializers {
        let regular = store.regular_number_literal_type(value)?;
        let fresh = store.fresh_type_of_literal_type(regular)?;
        let expected = TypeNodeLinks {
            resolved_type: Some(fresh),
            ..TypeNodeLinks::default()
        };
        if store.type_node_links(initializer) != Some(&expected)
            && !store.set_type_node_links(initializer, expected)
        {
            return Err(SourceCheckError::Assertion(
                SourceAssertionError::InvalidExpressionCache {
                    node: initializer,
                    cached: store
                        .type_node_links(initializer)
                        .and_then(|links| links.resolved_type),
                    expected: fresh,
                },
            ));
        }
    }
    for (node, type_) in ambient_expression_types {
        let expected = TypeNodeLinks {
            resolved_type: Some(type_),
            ..TypeNodeLinks::default()
        };
        if store.type_node_links(node) != Some(&expected)
            && !store.set_type_node_links(node, expected)
        {
            return Err(SourceCheckError::Assertion(
                SourceAssertionError::InvalidExpressionCache {
                    node,
                    cached: store
                        .type_node_links(node)
                        .and_then(|links| links.resolved_type),
                    expected: type_,
                },
            ));
        }
    }
    for (node, symbol) in ambient_expression_symbols {
        let expected = SymbolNodeLinks {
            resolved_symbol: Some(symbol),
        };
        if store.symbol_node_links(node) != Some(&expected)
            && !store.set_symbol_node_links(node, expected)
        {
            return Err(SourceCheckError::Variable(
                VariableInvariant::InvalidSymbolNodeCache {
                    node,
                    cached: store
                        .symbol_node_links(node)
                        .and_then(|links| links.resolved_symbol),
                    expected: symbol,
                },
            ));
        }
    }
    for initializer in object_initializers {
        let target = values
            .iter()
            .find(|value| {
                value.symbol == initializer.symbol && value.declaration == initializer.declaration
            })
            .map(|value| value.type_)
            .ok_or(SourceCheckError::Variable(
                VariableInvariant::InvalidValueLinks(initializer.symbol),
            ))?;
        if store
            .declared_type_links(initializer.interface)
            .and_then(|links| links.declared_type)
            != Some(target)
            || store
                .type_node_links(initializer.annotation)
                .and_then(|links| links.resolved_type)
                != Some(target)
        {
            return Err(SourceCheckError::Variable(
                VariableInvariant::InvalidValueLinks(initializer.symbol),
            ));
        }
        let number = store
            .intrinsic_bootstrap()
            .ok_or(SourceCheckError::LiteralCache(
                SourceLiteralCacheError::BootstrapUninitialized,
            ))?
            .number_type;
        let object = object_members::publish_object_literal(
            store,
            &initializer.object,
            &vec![number; initializer.object.properties.len()],
        )
        .map_err(|error| namespace_object_error(initializer.object.node, error))?;
        if !store.is_type_assignable_to_with_global_types_and_strict_function_types(
            object,
            target,
            global_types,
            options.strict_function_types,
        )? {
            return Err(unsupported(
                initializer.object.node,
                SyntaxKind::ObjectLiteralExpression,
                SourceSyntaxRole::VariableInitializer,
            ));
        }
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
    if options.no_implicit_any {
        let message = message_by_code(VARIABLE_IMPLICITLY_HAS_ANY_TYPE).ok_or(
            SourceCheckError::MissingDiagnostic(VARIABLE_IMPLICITLY_HAS_ANY_TYPE),
        )?;
        for variable in implicit_variables {
            if !variable.primary_declaration || variable.initializer.is_some() {
                continue;
            }
            super::source::merge_retry_diagnostic(
                diagnostics,
                super::CanonicalCheckerDiagnostic {
                    node: Some(variable.declaration),
                    range_override: None,
                    diagnostic: Diagnostic::with_arguments(
                        message,
                        [variable.name.clone(), "any".to_owned()],
                    ),
                    related_information: Vec::new(),
                },
            );
        }
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
        production::GlobalMergeCompletion,
    };

    struct Fixture {
        parsed: &'static ParseResult,
        file: FileId,
        context: CanonicalCheckerContext<'static>,
    }

    fn fixture(source: &'static str, module_state: CanonicalModuleState) -> Fixture {
        fixture_with_options(source, module_state, CanonicalCheckerOptions::default())
    }

    fn fixture_with_options(
        source: &'static str,
        module_state: CanonicalModuleState,
        options: CanonicalCheckerOptions,
    ) -> Fixture {
        fixture_with_source_facts(source, module_state, options, false)
    }

    fn declaration_fixture(source: &'static str, module_state: CanonicalModuleState) -> Fixture {
        fixture_with_source_facts(
            source,
            module_state,
            CanonicalCheckerOptions::default(),
            true,
        )
    }

    fn fixture_with_source_facts(
        source: &'static str,
        module_state: CanonicalModuleState,
        options: CanonicalCheckerOptions,
        declaration_file: bool,
    ) -> Fixture {
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
                    EscapedName::source(if declaration_file {
                        "\"/project/namespaces.d.ts\""
                    } else {
                        "\"/project/namespaces.ts\""
                    }),
                    CanonicalSourceLanguage::TypeScript,
                    declaration_file,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let context =
            CanonicalCheckerContext::new(binder.finish(), vec![(file, &parsed.arena)], options);
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
        let global_types = fixture.context.global_types().clone();
        let options = fixture.context.options();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
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
    fn exported_namespace_functions_publish_inferred_void_cold_and_warm() {
        let mut fixture = fixture(
            "export namespace Values { export function read() {} }",
            CanonicalModuleState::External,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Function {
                declaration,
                symbol,
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the namespace must retain its exported function")
        };
        let declaration = *declaration;
        let symbol = *symbol;

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());

        let callable = fixture
            .context
            .store()
            .value_symbol_links(symbol)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let provenance = fixture
            .context
            .store()
            .source_callable_provenance(callable)
            .unwrap();
        let expected = fixture
            .context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .void_type;
        assert_eq!(provenance.declaration, declaration);
        assert_eq!(provenance.owner_symbol, symbol);
        assert_eq!(
            fixture
                .context
                .store()
                .signature(provenance.signature)
                .and_then(super::super::signatures::Signature::resolved_return_type),
            Some(expected),
        );

        let warm = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );
        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn exported_ambient_namespace_functions_publish_annotated_void_cold_and_warm() {
        let mut fixture = declaration_fixture(
            "declare module \"lib\" { export function fn(): void; }",
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Function {
                declaration,
                symbol,
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the ambient namespace must retain its exported function")
        };
        let declaration = *declaration;
        let symbol = *symbol;
        let bound = fixture.context.file(fixture.file).unwrap().1;
        let local = bound.local_symbol(declaration).unwrap();

        assert!(namespace.ambient);
        assert_eq!(
            fixture.context.store().get_parent_of_symbol(symbol),
            Some(namespace.symbol),
        );
        assert_eq!(
            fixture.context.store().symbol(local).unwrap().flags(),
            SymbolFlags::EXPORT_VALUE,
        );
        assert_eq!(
            fixture
                .context
                .store()
                .symbol(local)
                .unwrap()
                .export_symbol(),
            Some(symbol),
        );
        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());

        let callable = fixture
            .context
            .store()
            .value_symbol_links(symbol)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let provenance = fixture
            .context
            .store()
            .source_callable_provenance(callable)
            .unwrap();
        let void = fixture
            .context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .void_type;
        assert_eq!(provenance.declaration, declaration);
        assert_eq!(provenance.owner_symbol, symbol);
        assert_eq!(
            fixture
                .context
                .store()
                .signature(provenance.signature)
                .and_then(super::super::signatures::Signature::resolved_return_type),
            Some(void),
        );

        let warm = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );
        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn ambient_namespace_functions_reject_other_returns_and_nondeclaration_files() {
        for source in [
            "declare module \"lib\" { export function fn(): string; }",
            "declare module \"lib\" { export function fn(); }",
            "declare module \"lib\" { export function fn(value: string): void; }",
        ] {
            let fixture = declaration_fixture(source, CanonicalModuleState::Script);
            let declaration = declaration(&fixture, 0);
            let (arena, bound) = fixture.context.file(fixture.file).unwrap();
            let before = fixture.context.store().checker_link_allocated_lengths();

            assert!(matches!(
                plan_source_namespace(arena, bound, fixture.context.store(), declaration),
                Err(SourceCheckError::Unsupported(_))
            ));
            assert_eq!(
                fixture.context.store().checker_link_allocated_lengths(),
                before,
            );
        }

        let fixture = fixture(
            "declare module \"lib\" { export function fn(): void; }",
            CanonicalModuleState::Script,
        );
        let declaration = declaration(&fixture, 0);
        let (arena, bound) = fixture.context.file(fixture.file).unwrap();
        assert!(matches!(
            plan_source_namespace(arena, bound, fixture.context.store(), declaration),
            Err(SourceCheckError::Unsupported(_))
        ));
    }

    #[test]
    fn exported_runtime_namespace_variables_preserve_fresh_literals_cold_and_warm() {
        let mut fixture = fixture(
            "namespace Values { export var value = 1; }",
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [variable] = namespace.implicit_variables.as_slice() else {
            panic!("the namespace must retain its exported numeric variable")
        };
        let declaration = variable.declaration;
        let symbol = variable.symbol;
        let initializer = variable.initializer.unwrap();
        let local = fixture
            .context
            .file(fixture.file)
            .unwrap()
            .1
            .local_symbol(declaration)
            .unwrap();

        assert_eq!(
            fixture.context.store().get_parent_of_symbol(symbol),
            Some(namespace.symbol),
        );
        assert_eq!(
            fixture.context.store().symbol(local).unwrap().flags(),
            SymbolFlags::EXPORT_VALUE,
        );
        assert_eq!(
            fixture
                .context
                .store()
                .symbol(local)
                .unwrap()
                .export_symbol(),
            Some(symbol),
        );
        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());

        let number = fixture
            .context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        assert_eq!(
            fixture
                .context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type),
            Some(number),
        );
        let literal = fixture
            .context
            .store()
            .type_node_links(initializer)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_ne!(literal, number);
        assert!(matches!(
            fixture
                .context
                .store()
                .type_payload(literal)
                .unwrap()
                .data(),
            TypeData::Literal(_)
        ));

        let warm = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );
        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn exported_runtime_namespace_variables_reject_other_declaration_shapes() {
        for source in [
            "namespace Values { export var value: number = 1; }",
            "namespace Values { export var value = \"one\"; }",
            "namespace Values { export let value = 1; }",
            "namespace Values { export var first = 1, second = 2; }",
        ] {
            let fixture = fixture(source, CanonicalModuleState::Script);
            let declaration = declaration(&fixture, 0);
            let (arena, bound) = fixture.context.file(fixture.file).unwrap();
            let before = fixture.context.store().checker_link_allocated_lengths();

            assert!(matches!(
                plan_source_namespace(arena, bound, fixture.context.store(), declaration),
                Err(SourceCheckError::Unsupported(_))
            ));
            assert_eq!(
                fixture.context.store().checker_link_allocated_lengths(),
                before,
            );
        }
    }

    #[test]
    fn exported_namespace_functions_replay_importer_published_callable_capabilities() {
        let mut fixture = fixture(
            "export namespace Values { export function read() {} }",
            CanonicalModuleState::External,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Function {
                declaration,
                symbol,
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the namespace must retain its exported function")
        };
        let declaration = *declaration;
        let symbol = *symbol;
        let bound = fixture.context.file(fixture.file).unwrap().1.clone();
        let global_types = fixture.context.global_types().clone();
        let options = fixture.context.options();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        {
            let store = fixture.context.store_mut_for_test();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let error = bootstrap.error_type;
            let void = bootstrap.void_type;
            let mut session =
                InstantiationSession::new_recovering(store, InstantiationLimits::default(), error)
                    .unwrap();
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let callable = CanonicalTypeQuery::new_with_global_types_and_session(
                store,
                &host,
                &global_types,
                options,
                &mut session,
                &mut diagnostics,
            )
            .unwrap()
            .get_type_of_source_callable(declaration, symbol)
            .unwrap();
            let signature = store
                .source_callable_provenance(callable)
                .unwrap()
                .signature;
            let callable_plan = source_callables::plan_source_callable(
                store,
                &host,
                declaration,
                symbol,
                Some(CanonicalArrayTargets::from_global_types(&global_types)),
            )
            .unwrap();
            source_callables::publish_inferred_source_callable_return(
                store,
                &callable_plan,
                signature,
                void,
            )
            .unwrap();
            assert!(diagnostics.is_empty());
        }

        assert_eq!(plan(&fixture, 0), namespace);
        let warm = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );
        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn exported_namespace_imports_publish_canonical_alias_targets() {
        let mut fixture = fixture(
            "namespace Outer { export namespace Inner {} export import Visible = Inner; }",
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [SourceNamespaceMemberPlan::Namespace(inner)] = plan.members.as_slice() else {
            panic!("the namespace must retain its exported target")
        };
        let [import] = plan.imports.as_slice() else {
            panic!("the namespace must retain its import-equals declaration")
        };
        let alias = import.symbol;
        let target = inner.symbol;
        assert_eq!(import.name_text, "Visible");
        assert!(fixture.context.store().alias_symbol_links(alias).is_none());

        assert!(execute(&mut fixture, &plan).unwrap().is_empty());

        let links = fixture.context.store().alias_symbol_links(alias).unwrap();
        assert_eq!(links.immediate_target, Some(target));
        assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
        assert_eq!(links.type_only_declaration, None);

        let before = fixture.context.store().checker_link_allocated_lengths();
        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        assert_eq!(
            fixture.context.store().checker_link_allocated_lengths(),
            before,
        );
    }

    #[test]
    fn namespace_imports_preserve_alias_dependent_type_annotations() {
        let mut fixture = fixture(
            concat!(
                "namespace Outer { ",
                "export namespace Inner { export interface Shape {} } ",
                "export import Visible = Inner; ",
                "type Value = Visible.Shape; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [import] = plan.imports.as_slice() else {
            panic!("the namespace must retain its import-equals declaration")
        };
        let alias = import.symbol;
        let [
            SourceNamespaceMemberPlan::Namespace(inner),
            SourceNamespaceMemberPlan::TypeAlias { symbol: value, .. },
        ] = plan.members.as_slice()
        else {
            panic!("the namespace must retain its target and alias-dependent type")
        };
        let target = inner.symbol;
        let value = *value;

        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        assert_eq!(
            fixture
                .context
                .store()
                .alias_symbol_links(alias)
                .map(|links| links.alias_target),
            Some(AliasTargetState::Resolved(target)),
        );
        assert!(
            fixture
                .context
                .store()
                .type_alias_links(value)
                .and_then(|links| links.declared_type)
                .is_some(),
        );

        let before = fixture.context.store().checker_link_allocated_lengths();
        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        assert_eq!(
            fixture.context.store().checker_link_allocated_lengths(),
            before,
        );
    }

    #[test]
    fn invalid_later_annotation_cannot_publish_namespace_import_aliases() {
        let mut fixture = fixture(
            concat!(
                "namespace Outer { ",
                "export namespace Inner { export interface Shape {} } ",
                "export import Visible = Inner; ",
                "type Value = Visible.Shape; ",
                "type Broken = Missing; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [import] = plan.imports.as_slice() else {
            panic!("the namespace must retain its import-equals declaration")
        };
        let alias = import.symbol;
        let before = fixture.context.store().checker_link_allocated_lengths();

        for _ in 0..2 {
            assert!(matches!(
                execute(&mut fixture, &plan),
                Err(SourceCheckError::DeclaredType(
                    DeclaredTypeError::TypeNodeUnavailable(
                        TypeNodeUnavailable::MissingTypeReference(_)
                    )
                ))
            ));
            assert!(fixture.context.store().alias_symbol_links(alias).is_none());
            assert_eq!(
                fixture.context.store().checker_link_allocated_lengths(),
                before,
            );
        }
    }

    #[test]
    fn namespace_imports_can_reference_private_nested_namespaces() {
        let mut fixture = fixture(
            "namespace Outer { namespace Hidden {} export import Visible = Hidden; }",
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [SourceNamespaceMemberPlan::Namespace(hidden)] = plan.members.as_slice() else {
            panic!("the namespace must retain its private target")
        };
        let [import] = plan.imports.as_slice() else {
            panic!("the namespace must retain its exported import")
        };
        let alias = import.symbol;
        let target = hidden.symbol;

        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        assert_eq!(
            fixture
                .context
                .store()
                .alias_symbol_links(alias)
                .map(|links| links.alias_target),
            Some(AliasTargetState::Resolved(target)),
        );
    }

    #[test]
    fn qualified_namespace_imports_follow_canonical_export_tables() {
        let mut fixture = fixture(
            concat!(
                "namespace Outer { ",
                "export namespace Inner { export namespace Leaf {} } ",
                "export import Visible = Inner.Leaf; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [SourceNamespaceMemberPlan::Namespace(inner)] = plan.members.as_slice() else {
            panic!("the namespace must retain its first target segment")
        };
        let [SourceNamespaceMemberPlan::Namespace(leaf)] = inner.members.as_slice() else {
            panic!("the nested namespace must retain the final target segment")
        };
        let [import] = plan.imports.as_slice() else {
            panic!("the namespace must retain its qualified import")
        };
        let alias = import.symbol;
        let target = leaf.symbol;

        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        assert_eq!(
            fixture
                .context
                .store()
                .alias_symbol_links(alias)
                .map(|links| links.alias_target),
            Some(AliasTargetState::Resolved(target)),
        );
    }

    #[test]
    fn qualified_namespace_imports_follow_earlier_namespace_aliases() {
        let mut fixture = fixture(
            concat!(
                "namespace Outer { ",
                "export namespace Inner { export namespace Leaf {} } ",
                "export import Visible = Inner; ",
                "export import Selected = Visible.Leaf; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [SourceNamespaceMemberPlan::Namespace(inner)] = plan.members.as_slice() else {
            panic!("the namespace must retain its first target segment")
        };
        let [SourceNamespaceMemberPlan::Namespace(leaf)] = inner.members.as_slice() else {
            panic!("the nested namespace must retain the final target segment")
        };
        let [visible, selected] = plan.imports.as_slice() else {
            panic!("the namespace must retain both import aliases")
        };
        let visible_symbol = visible.symbol;
        let selected_symbol = selected.symbol;
        let inner_symbol = inner.symbol;
        let leaf_symbol = leaf.symbol;

        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        assert_eq!(
            fixture
                .context
                .store()
                .alias_symbol_links(visible_symbol)
                .map(|links| links.alias_target),
            Some(AliasTargetState::Resolved(inner_symbol)),
        );
        assert_eq!(
            fixture
                .context
                .store()
                .alias_symbol_links(selected_symbol)
                .map(|links| links.alias_target),
            Some(AliasTargetState::Resolved(leaf_symbol)),
        );

        let before = fixture.context.store().checker_link_allocated_lengths();
        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        assert_eq!(
            fixture.context.store().checker_link_allocated_lengths(),
            before,
        );
    }

    #[test]
    fn qualified_namespace_imports_follow_forward_and_nested_aliases() {
        let mut fixture = fixture(
            concat!(
                "namespace Outer { ",
                "export namespace Inner { export namespace Leaf {} } ",
                "export namespace Nested { export import Forwarded = Visible; } ",
                "export import Selected = Nested.Forwarded.Leaf; ",
                "export import Visible = Inner; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Namespace(inner),
            SourceNamespaceMemberPlan::Namespace(nested),
        ] = plan.members.as_slice()
        else {
            panic!("the namespace must retain both target namespaces")
        };
        let [SourceNamespaceMemberPlan::Namespace(leaf)] = inner.members.as_slice() else {
            panic!("the first target namespace must retain its leaf")
        };
        let [selected, visible] = plan.imports.as_slice() else {
            panic!("the outer namespace must retain both aliases")
        };
        let [forwarded] = nested.imports.as_slice() else {
            panic!("the nested namespace must retain its forwarded alias")
        };
        let selected_symbol = selected.symbol;
        let visible_symbol = visible.symbol;
        let forwarded_symbol = forwarded.symbol;
        let inner_symbol = inner.symbol;
        let leaf_symbol = leaf.symbol;

        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        for (alias, target) in [
            (selected_symbol, leaf_symbol),
            (visible_symbol, inner_symbol),
            (forwarded_symbol, inner_symbol),
        ] {
            assert_eq!(
                fixture
                    .context
                    .store()
                    .alias_symbol_links(alias)
                    .map(|links| links.alias_target),
                Some(AliasTargetState::Resolved(target)),
            );
        }

        let before = fixture.context.store().checker_link_allocated_lengths();
        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        assert_eq!(
            fixture.context.store().checker_link_allocated_lengths(),
            before,
        );
    }

    #[test]
    fn circular_namespace_imports_report_each_declaration_in_source_order() {
        let mut fixture = fixture(
            "namespace Outer { import First = Second; import Second = First; }",
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [first, second] = plan.imports.as_slice() else {
            panic!("the namespace must retain both circular imports")
        };
        let first_symbol = first.symbol;
        let second_symbol = second.symbol;
        let first_declaration = first.declaration;
        let second_declaration = second.declaration;

        let diagnostics = execute(&mut fixture, &plan).unwrap();
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| (diagnostic.diagnostic.code(), diagnostic.node))
                .collect::<Vec<_>>(),
            [
                (2303, Some(first_declaration)),
                (2303, Some(second_declaration)),
            ],
        );
        for symbol in [first_symbol, second_symbol] {
            assert_eq!(
                fixture
                    .context
                    .store()
                    .alias_symbol_links(symbol)
                    .map(|links| links.alias_target),
                Some(AliasTargetState::Unknown),
            );
        }
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
    fn generic_namespace_interfaces_publish_canonical_declared_properties() {
        let mut fixture = fixture(
            concat!(
                "declare namespace Shapes { ",
                "interface Box<T> { readonly value: T; label?: string; } ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface {
                declaration,
                symbol,
                generic: Some(generic),
                ..
            },
        ] = plan.members.as_slice()
        else {
            panic!("the namespace must retain one generic interface")
        };
        let declaration = *declaration;
        let symbol = *symbol;
        let parameters = generic.type_parameters.clone();
        let properties = generic.properties.clone();

        assert!(execute(&mut fixture, &plan).unwrap().is_empty());

        let target = fixture
            .context
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Interface(interface) =
            fixture.context.store().type_payload(target).unwrap().data()
        else {
            panic!("the generic namespace interface must retain its interface identity")
        };
        assert!(interface.base_types_resolved);
        assert!(interface.declared_members_resolved);
        let members = interface.declared_members.unwrap();
        let table = fixture.context.store().symbol_table(members).unwrap();
        assert_eq!(table.len(), properties.len());
        assert_eq!(parameters.len(), 1);
        for property in &properties {
            assert_eq!(table.get_source(&property.name), Some(property.symbol));
            let resolved = fixture
                .context
                .store()
                .value_symbol_links(property.symbol)
                .and_then(|links| links.resolved_type)
                .unwrap();
            if property.name == "value" {
                assert_eq!(
                    cached_ordinary_type_parameter_owner(fixture.context.store(), resolved),
                    Some(parameters[0]),
                );
                assert_eq!(
                    fixture
                        .context
                        .store()
                        .symbol(property.symbol)
                        .unwrap()
                        .check_flags(),
                    CheckFlags::READONLY,
                );
            }
        }

        let before = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_store().symbol_table_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );
        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_store().symbol_table_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            ),
            before,
        );
        assert_eq!(
            fixture
                .context
                .store()
                .symbol(symbol)
                .and_then(|record| record.declarations()),
            Some(&[declaration][..]),
        );
    }

    #[test]
    fn generic_namespace_interfaces_accept_quoted_property_names() {
        let mut fixture = fixture(
            "declare namespace Shapes { interface Box<T> { \"data-value\": T; } }",
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface {
                symbol,
                generic: Some(generic),
                ..
            },
        ] = plan.members.as_slice()
        else {
            panic!("the namespace must retain its generic interface")
        };
        let symbol = *symbol;
        let property = generic.properties[0].symbol;
        assert_eq!(generic.properties[0].name, "data-value");

        assert!(execute(&mut fixture, &plan).unwrap().is_empty());

        let target = fixture
            .context
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Interface(interface) =
            fixture.context.store().type_payload(target).unwrap().data()
        else {
            panic!("the generic declaration must retain its interface type")
        };
        assert_eq!(
            interface
                .declared_members
                .and_then(|members| fixture.context.store().symbol_table(members))
                .and_then(|members| members.get_source("data-value")),
            Some(property),
        );
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
    fn external_module_augmentation_uses_the_merged_export_assignment_namespace() {
        let library = parse_source_file(concat!(
            "declare module 'react' { ",
            "export = React; ",
            "namespace React { interface Attributes { key?: string; } } ",
            "}",
        ));
        let source = parse_source_file(concat!(
            "export {}; ",
            "declare module 'react' { ",
            "interface Attributes { 'ns:thing'?: string; } ",
            "}",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let library_file = FileId::new(7_481);
        let source_file = FileId::new(7_482);
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
                        EscapedName::source(format!("\"/react-namespace-{}.ts\"", file.index())),
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
        let context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(library_file, &library.arena), (source_file, &source.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let (_, bound) = context.file(source_file).unwrap();
        let source_record = source.arena.get(bound.source_file().node).unwrap();
        let NodeData::SourceFile(source_data) = &source_record.data else {
            panic!("the augmentation fixture must retain a source-file root")
        };
        let declaration = child(bound.source_file(), source_data.statements.nodes[1]);
        let raw_namespace = bound.symbol(declaration).unwrap();
        let namespace = context.store().get_merged_symbol(raw_namespace).unwrap();
        assert_ne!(namespace, raw_namespace);
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let plan = plan_source_namespace(&source.arena, bound, context.store(), declaration)
            .expect("the module augmentation must retain its merged React namespace");

        assert_eq!(plan.symbol, namespace);
        let [
            SourceNamespaceMemberPlan::Interface {
                symbol: attributes, ..
            },
        ] = plan.members.as_slice()
        else {
            panic!("the augmentation must retain its Attributes contribution")
        };
        assert_eq!(
            context.store().get_parent_of_symbol(*attributes),
            Some(namespace)
        );
        assert!(
            context
                .store()
                .symbol(*attributes)
                .unwrap()
                .flags()
                .contains(SymbolFlags::INTERFACE | SymbolFlags::TRANSIENT)
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn ambient_module_named_imports_resolve_export_assignment_namespace_members() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module 'react' { ",
                "export = React; ",
                "namespace React { ",
                "type ReactNode = string; ",
                "interface ReactElement {} ",
                "} } ",
                "declare module 'prop-types' { ",
                "import { ReactNode, ReactElement } from 'react'; ",
                "interface Wrapper { node: ReactNode; element: ReactElement; } ",
                "}",
            ),
            CanonicalModuleState::Script,
        );

        let namespace = plan(&fixture, 1);

        assert_eq!(namespace.imports.len(), 2);
        assert_eq!(namespace.imports[0].name_text, "ReactNode");
        assert_eq!(namespace.imports[1].name_text, "ReactElement");
        let aliases = namespace
            .imports
            .iter()
            .map(|import| import.symbol)
            .collect::<Vec<_>>();
        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        for alias in aliases {
            assert!(matches!(
                fixture
                    .context
                    .store()
                    .alias_symbol_links(alias)
                    .map(|links| links.alias_target),
                Some(AliasTargetState::Resolved(_))
            ));
        }
        let before = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );
        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn ambient_module_export_assignments_resolve_their_namespace_alias() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module 'react' { ",
                "export = React; ",
                "namespace React { interface Element {} } ",
                "}",
            ),
            CanonicalModuleState::Script,
        );

        let namespace = plan(&fixture, 0);

        let [export] = namespace.imports.as_slice() else {
            panic!("the ambient module must retain its export-assignment alias")
        };
        let alias = export.symbol;
        let [SourceNamespaceMemberPlan::Namespace(target)] = namespace.members.as_slice() else {
            panic!("the ambient module must retain its exported namespace")
        };
        let target = target.symbol;
        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        assert_eq!(
            fixture
                .context
                .store()
                .alias_symbol_links(alias)
                .map(|links| links.alias_target),
            Some(AliasTargetState::Resolved(target)),
        );
    }

    #[test]
    fn ambient_module_namespace_imports_resolve_same_file_modules() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module 'prop-types' { export interface Value {} } ",
                "declare module 'react' { ",
                "import * as PropTypes from 'prop-types'; ",
                "interface Wrapper { value: PropTypes.Value; } ",
                "}",
            ),
            CanonicalModuleState::Script,
        );

        let namespace = plan(&fixture, 1);

        let [import] = namespace.imports.as_slice() else {
            panic!("the ambient module must retain one namespace import")
        };
        assert_eq!(import.name_text, "PropTypes");
        let alias = import.symbol;
        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        assert!(matches!(
            fixture
                .context
                .store()
                .alias_symbol_links(alias)
                .map(|links| links.alias_target),
            Some(AliasTargetState::Resolved(_))
        ));
    }

    #[test]
    fn ambient_module_imports_reject_missing_exports_without_publishing_aliases() {
        let fixture = declaration_fixture(
            concat!(
                "declare module 'target' { export interface Existing {} } ",
                "declare module 'source' { import { Missing } from 'target'; }",
            ),
            CanonicalModuleState::Script,
        );
        let declaration = declaration(&fixture, 1);
        let (arena, bound) = fixture.context.file(fixture.file).unwrap();
        let before = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );

        assert!(matches!(
            plan_source_namespace(arena, bound, fixture.context.store(), declaration),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Import(_)
            ))
        ));

        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn unannotated_ambient_namespace_variables_use_canonical_any() {
        let mut fixture = fixture(
            "declare namespace Values { const inferred; const explicit: number; }",
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [inferred] = plan.implicit_variables.as_slice() else {
            panic!("the namespace must retain its unannotated variable")
        };
        let inferred_symbol = inferred.symbol;
        let [
            SourceNamespaceMemberPlan::AmbientVariable {
                symbol: explicit_symbol,
                ..
            },
        ] = plan.members.as_slice()
        else {
            panic!("the namespace must retain its annotated variable")
        };
        let explicit_symbol = *explicit_symbol;

        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        let bootstrap = fixture.context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(
            fixture
                .context
                .store()
                .value_symbol_links(inferred_symbol)
                .and_then(|links| links.resolved_type),
            Some(bootstrap.any_type),
        );
        assert_eq!(
            fixture
                .context
                .store()
                .value_symbol_links(explicit_symbol)
                .and_then(|links| links.resolved_type),
            Some(bootstrap.number_type),
        );

        let before = fixture.context.store().checker_link_allocated_lengths();
        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        assert_eq!(
            fixture.context.store().checker_link_allocated_lengths(),
            before,
        );
    }

    #[test]
    fn unannotated_ambient_namespace_variables_report_strict_implicit_any() {
        let mut fixture = fixture_with_options(
            "declare namespace Values { const inferred; }",
            CanonicalModuleState::Script,
            CanonicalCheckerOptions {
                no_implicit_any: true,
                ..CanonicalCheckerOptions::default()
            },
        );
        let plan = plan(&fixture, 0);
        let [inferred] = plan.implicit_variables.as_slice() else {
            panic!("the namespace must retain its unannotated variable")
        };
        let declaration = inferred.declaration;
        let symbol = inferred.symbol;

        for _ in 0..2 {
            let diagnostics = execute(&mut fixture, &plan).unwrap();
            let [diagnostic] = diagnostics.as_slice() else {
                panic!("strict mode must report one implicit-any diagnostic")
            };
            assert_eq!(diagnostic.node, Some(declaration));
            assert_eq!(diagnostic.diagnostic.code(), 7005);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Variable 'inferred' implicitly has an 'any' type.",
            );
        }
        assert_eq!(
            fixture
                .context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type),
            Some(
                fixture
                    .context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .any_type
            ),
        );
    }

    #[test]
    fn merged_ambient_namespace_variables_report_once_in_source_order() {
        let mut fixture = fixture_with_options(
            concat!(
                "declare namespace Values { ",
                "namespace Inner { var first; var first; } ",
                "let second; ",
                "const third; ",
                "}",
            ),
            CanonicalModuleState::Script,
            CanonicalCheckerOptions {
                no_implicit_any: true,
                ..CanonicalCheckerOptions::default()
            },
        );
        let plan = plan(&fixture, 0);
        let [SourceNamespaceMemberPlan::Namespace(nested)] = plan.members.as_slice() else {
            panic!("the namespace must retain its nested declarations")
        };
        let [first, repeated] = nested.implicit_variables.as_slice() else {
            panic!("the nested namespace must retain both merged declarations")
        };
        let [second, third] = plan.implicit_variables.as_slice() else {
            panic!("the outer namespace must retain both block-scoped declarations")
        };
        assert_eq!(first.symbol, repeated.symbol);
        assert!(first.primary_declaration);
        assert!(!repeated.primary_declaration);
        let symbols = [first.symbol, second.symbol, third.symbol];

        for _ in 0..2 {
            let diagnostics = execute(&mut fixture, &plan).unwrap();
            assert_eq!(
                diagnostics
                    .as_slice()
                    .iter()
                    .map(|diagnostic| {
                        (
                            diagnostic.diagnostic.code(),
                            diagnostic.diagnostic.arguments[0].as_str(),
                        )
                    })
                    .collect::<Vec<_>>(),
                [(7005, "first"), (7005, "second"), (7005, "third")],
            );
        }

        let any = fixture
            .context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .any_type;
        for symbol in symbols {
            assert_eq!(
                fixture
                    .context
                    .store()
                    .value_symbol_links(symbol)
                    .and_then(|links| links.resolved_type),
                Some(any),
            );
        }
    }

    #[test]
    fn reopened_ambient_namespace_variables_report_only_the_first_declaration() {
        let mut fixture = fixture_with_options(
            concat!(
                "declare namespace Values { var repeated; } ",
                "declare namespace Values { var repeated; }",
            ),
            CanonicalModuleState::Script,
            CanonicalCheckerOptions {
                no_implicit_any: true,
                ..CanonicalCheckerOptions::default()
            },
        );
        let first = plan(&fixture, 0);
        let second = plan(&fixture, 1);
        let [first_variable] = first.implicit_variables.as_slice() else {
            panic!("the first namespace must retain its variable")
        };
        let [second_variable] = second.implicit_variables.as_slice() else {
            panic!("the reopened namespace must retain its variable")
        };
        assert_eq!(first_variable.symbol, second_variable.symbol);
        assert!(first_variable.primary_declaration);
        assert!(!second_variable.primary_declaration);

        let diagnostics = execute(&mut fixture, &first).unwrap();
        let [diagnostic] = diagnostics.as_slice() else {
            panic!("the first declaration must report exactly one implicit-any diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 7005);
        assert!(execute(&mut fixture, &second).unwrap().is_empty());

        let before = fixture.context.store().checker_link_allocated_lengths();
        assert_eq!(execute(&mut fixture, &first).unwrap().len(), 1);
        assert!(execute(&mut fixture, &second).unwrap().is_empty());
        assert_eq!(
            fixture.context.store().checker_link_allocated_lengths(),
            before,
        );
    }

    #[test]
    fn invalid_implicit_variable_cache_cannot_publish_namespace_aliases_or_enums() {
        let mut fixture = fixture(
            concat!(
                "declare namespace Values { ",
                "export namespace Inner {} ",
                "export import Visible = Inner; ",
                "enum Empty {} ",
                "const poisoned; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Namespace(_),
            SourceNamespaceMemberPlan::EmptyEnum {
                symbol: enumeration,
                ..
            },
        ] = plan.members.as_slice()
        else {
            panic!("the namespace must retain its nested namespace and empty enum")
        };
        let enumeration = *enumeration;
        let [import] = plan.imports.as_slice() else {
            panic!("the namespace must retain its alias")
        };
        let alias = import.symbol;
        let [variable] = plan.implicit_variables.as_slice() else {
            panic!("the namespace must retain its unannotated variable")
        };
        let variable = variable.symbol;
        let bootstrap = fixture.context.store().intrinsic_bootstrap().unwrap();
        let any = bootstrap.any_type;
        let string = bootstrap.string_type;
        assert!(fixture.context.store_mut_for_test().set_value_symbol_links(
            variable,
            ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            },
        ));
        let before = (
            fixture.context.store().type_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );

        for _ in 0..2 {
            assert_eq!(
                execute(&mut fixture, &plan),
                Err(SourceCheckError::Variable(
                    VariableInvariant::CachedValueTypeMismatch {
                        symbol: variable,
                        cached: string,
                        expected: any,
                    },
                )),
            );
            assert!(fixture.context.store().alias_symbol_links(alias).is_none());
            assert!(
                fixture
                    .context
                    .store()
                    .declared_type_links(enumeration)
                    .is_none(),
            );
            assert_eq!(
                (
                    fixture.context.store().type_len(),
                    fixture.context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
        }

        assert!(
            fixture
                .context
                .store_mut_for_test()
                .set_value_symbol_links(variable, ValueSymbolLinks::default()),
        );
        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        assert_eq!(
            fixture
                .context
                .store()
                .value_symbol_links(variable)
                .and_then(|links| links.resolved_type),
            Some(any),
        );
        assert!(fixture.context.store().alias_symbol_links(alias).is_some());
        assert!(
            fixture
                .context
                .store()
                .declared_type_links(enumeration)
                .is_some(),
        );
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
    fn ambient_module_typeof_export_assignments_report_ts2714_without_publication() {
        for (source, expected) in [
            (
                "declare module \"indirect\" { export default typeof Foo.default; }",
                "typeof Foo.default",
            ),
            (
                "declare module \"indirect\" { export = typeof Foo2; }",
                "typeof Foo2",
            ),
        ] {
            let mut fixture = fixture(source, CanonicalModuleState::Script);
            let namespace = plan(&fixture, 0);
            assert!(namespace.members.is_empty());
            assert!(namespace.imports.is_empty());
            let [planned] = namespace.diagnostics.as_slice() else {
                panic!("expected one invalid ambient export diagnostic")
            };
            assert_eq!(planned.code, AMBIENT_EXPORT_ASSIGNMENT_MUST_BE_ENTITY_NAME);
            let range = fixture.parsed.arena.get(planned.node.node).unwrap().range;
            assert_eq!(
                &source[usize::try_from(range.start.get()).unwrap()
                    ..usize::try_from(range.end.get()).unwrap()],
                expected,
            );
            let symbol = fixture
                .parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::ExportAssignment).then_some(NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        node,
                    ))
                })
                .and_then(|node| fixture.context.file(fixture.file).unwrap().1.symbol(node))
                .unwrap();
            let before = (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            );

            for _ in 0..2 {
                let diagnostics = execute(&mut fixture, &namespace).unwrap();
                let [diagnostic] = diagnostics.as_slice() else {
                    panic!("expected one ambient export grammar diagnostic")
                };
                assert_eq!(diagnostic.diagnostic.code(), 2714);
                assert_eq!(diagnostic.node, Some(planned.node));
                assert_eq!(
                    diagnostic.diagnostic.render().unwrap(),
                    "The expression of an export assignment must be an identifier or qualified name in an ambient context.",
                );
                assert!(fixture.context.store().alias_symbol_links(symbol).is_none());
                assert!(fixture.context.store().value_symbol_links(symbol).is_none());
                assert_eq!(
                    (
                        fixture.context.store().type_len(),
                        fixture.context.store().symbol_len(),
                        fixture.context.store().checker_link_allocated_lengths(),
                    ),
                    before,
                );
            }
        }
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
    fn top_level_external_global_augmentation_is_legal() {
        let mut fixture = fixture(
            "export {}; declare global { interface Added {} }",
            CanonicalModuleState::External,
        );
        let plan = plan(&fixture, 1);
        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
    }

    #[test]
    fn global_augmentation_inside_external_namespace_reports_ts2669() {
        let mut fixture = fixture(
            "export {}; namespace A { declare global { interface Added {} } }",
            CanonicalModuleState::External,
        );
        let plan = plan(&fixture, 1);
        let [SourceNamespaceMemberPlan::Namespace(nested)] = plan.members.as_slice() else {
            panic!("the namespace must retain its global augmentation")
        };
        let name = nested.name;
        let diagnostics = execute(&mut fixture, &plan).unwrap();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2669);
        assert_eq!(diagnostics.as_slice()[0].node, Some(name));
    }

    #[test]
    fn direct_global_augmentation_in_top_level_ambient_module_is_legal() {
        let mut fixture = fixture(
            "declare module \"package\" { global { interface Added {} } }",
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
    }

    #[test]
    fn ambient_module_nested_in_external_augmentation_reports_ts2435() {
        let mut fixture = fixture(
            "export {}; declare module \"outer\" { module \"inner\" {} }",
            CanonicalModuleState::External,
        );
        let plan = plan(&fixture, 1);
        let [SourceNamespaceMemberPlan::Namespace(nested)] = plan.members.as_slice() else {
            panic!("the outer module must retain its nested ambient module")
        };
        let name = nested.name;
        let diagnostics = execute(&mut fixture, &plan).unwrap();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2435);
        assert_eq!(diagnostics.as_slice()[0].node, Some(name));
    }

    #[test]
    fn nested_enums_publish_canonical_namespace_owned_semantics() {
        let mut fixture = fixture(
            "declare namespace JSX { enum ElementType {} }",
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [SourceNamespaceMemberPlan::EmptyEnum { symbol, .. }] = plan.members.as_slice() else {
            panic!("the namespace must retain its enum declaration")
        };
        let symbol = *symbol;
        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        assert!(
            fixture
                .context
                .store()
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .is_some()
        );

        let before = (
            fixture.context.store().type_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );
        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            ),
            before,
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
