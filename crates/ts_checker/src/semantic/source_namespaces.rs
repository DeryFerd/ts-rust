//! Canonical source planning for TypeScript namespaces and ambient modules.
//!
//! The binder already owns namespace symbols and export tables. This module
//! checks that graph without creating replacement symbols or accepting an
//! unsupported namespace member as a successful check.
//! An exported class can merge with one namespace that exports its constructor.

use std::collections::HashSet;

use ts_ast::{ModifierList, Node, NodeArena, NodeData, NodeFlags, NodeList, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CheckFlags, EscapedName, InternalSymbolName,
    SemanticSymbolId, SymbolFlags, SymbolTableId, canonical_has_syntactic_modifier,
    semantic::PreparedSymbolTable,
};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    AliasTargetState, CanonicalCheckerDiagnostic, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalCheckerRelatedInformation, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, DeclaredTypeUnavailable,
    ProductionAliasTargetHost, SourceAssertionError, SourceCheckError, SourceCheckProvenanceError,
    SourceFunctionInvariant, SourceLiteralCacheError, SourceObjectLiteralError, SourceSyntaxRole,
    SymbolNodeLinks, TypeData, TypeId, TypeMapper, TypeNodeLinks, UnsupportedSourceSyntax,
    ValueSymbolLinks, VariableInvariant,
    alias::{
        CanonicalAliasResolutionError, CanonicalAliasResolutionEvent, CanonicalAliasResolver,
        CanonicalAliasTargetHost, CanonicalAliasTargetUnavailable, CanonicalImmediateAliasTarget,
    },
    array_types::CanonicalArrayTargets,
    bootstrap::UnionReduction,
    declared::{cached_ordinary_type_parameter_owner, preflight_class_or_interface_reference},
    instantiate::InstantiationSession,
    object_members::{self, PropertyObjectError, PropertyObjectPlan},
    reference_types::validate_direct_generic_reference,
    signatures::SignatureFlags,
    source_callables::{self, SourceCallableError, SourceCallableUnsupported},
    source_overloads::{self, SourceOverloadError},
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
const PROPERTY_DOES_NOT_EXIST: u32 = 2_339;
const TYPE_IS_NOT_A_CONSTRUCTOR: u32 = 2_507;
const PROPERTY_HAS_NO_INITIALIZER: u32 = 2_564;
const VARIABLE_IMPLICITLY_HAS_ANY_TYPE: u32 = 7_005;
const CANNOT_REDECLARE_BLOCK_SCOPED_VARIABLE: u32 = 2_451;
const ALSO_DECLARED_HERE: u32 = 6_203;
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
        parameter_annotations: Vec<NodeRef>,
        deferred: bool,
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
    DeferredAmbientFunction {
        declaration: NodeRef,
        symbol: SemanticSymbolId,
        type_parameters: Vec<SemanticSymbolId>,
        parameters: Vec<SemanticSymbolId>,
        annotations: Vec<NodeRef>,
    },
    DeferredAmbientClass {
        declaration: NodeRef,
        symbol: SemanticSymbolId,
        type_parameters: Vec<SemanticSymbolId>,
        members: Vec<SemanticSymbolId>,
        annotations: Vec<NodeRef>,
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
    call_signatures: Vec<SemanticSymbolId>,
    construct_signatures: Vec<SemanticSymbolId>,
    index_signatures: Vec<SemanticSymbolId>,
    methods: Vec<SemanticSymbolId>,
    computed_properties: Vec<SourceNamespaceComputedPropertyPlan>,
    base_interfaces: Vec<SemanticSymbolId>,
    deferred_annotations: Vec<NodeRef>,
}

impl SourceNamespaceGenericInterfacePlan {
    pub(super) fn annotation_is_deferred(&self, annotation: NodeRef) -> bool {
        self.deferred_annotations.contains(&annotation)
    }
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceNamespaceComputedPropertyPlan {
    symbol: SemanticSymbolId,
    key: SemanticSymbolId,
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

#[derive(Clone, Debug, Eq, PartialEq)]
enum SourceNamespaceClassHeritagePlan {
    MissingPrivateExport {
        property: NodeRef,
        property_name: String,
        namespace_name: String,
    },
    NonConstructorVariable {
        expression: NodeRef,
        symbol: SemanticSymbolId,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceNamespaceClassPropertyPlan {
    declaration: NodeRef,
    name: NodeRef,
    symbol: SemanticSymbolId,
    annotation: NodeRef,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceNamespaceClassPlan {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    heritage: Option<SourceNamespaceClassHeritagePlan>,
    property: Option<SourceNamespaceClassPropertyPlan>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceNamespaceRecursiveClassPlan {
    class_declaration: NodeRef,
    namespace_declaration: NodeRef,
    class_symbol: SemanticSymbolId,
    class_local: SemanticSymbolId,
    prototype: SemanticSymbolId,
    variable_declaration: NodeRef,
    variable_symbol: SemanticSymbolId,
    variable_local: SemanticSymbolId,
    initializer: NodeRef,
    receiver: NodeRef,
    property: NodeRef,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceNamespaceRecursiveClassState {
    instance: TypeId,
    namespace_type: TypeId,
    class_type: TypeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RecursiveNamespaceClassCacheState {
    Cold,
    Warm(SourceNamespaceRecursiveClassState),
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
    classes: Vec<SourceNamespaceClassPlan>,
    recursive_class: Option<SourceNamespaceRecursiveClassPlan>,
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
        if !parameter_record
            .flags()
            .contains(SymbolFlags::TYPE_PARAMETER)
            || parameter_record
                .flags()
                .without(SymbolFlags::TYPE_PARAMETER | SymbolFlags::TRANSIENT)
                != SymbolFlags::NONE
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
        call_signatures: Vec::new(),
        construct_signatures: Vec::new(),
        index_signatures: Vec::new(),
        methods: Vec::new(),
        computed_properties: Vec::new(),
        base_interfaces: Vec::new(),
        deferred_annotations: Vec::new(),
    })
}

fn plan_interface_callable_signature(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    declaration: NodeRef,
    annotations: &mut Vec<NodeRef>,
) -> Result<SemanticSymbolId, SourceCheckError> {
    let invalid = |node, kind| unsupported(node, kind, SourceSyntaxRole::InterfaceDeclaration);
    let record = owned_node(arena, bound, store, declaration)?;
    let (kind, name, type_parameters, parameters, return_type, invalid_cache) = match &record.data {
        NodeData::CallSignatureDeclaration(signature) => (
            SyntaxKind::CallSignature,
            InternalSymbolName::Call,
            signature.type_parameters.as_ref(),
            &signature.parameters,
            signature.type_,
            signature.full_signature.is_some()
                || signature.next_container.is_some()
                || signature.symbol.is_some(),
        ),
        NodeData::ConstructSignatureDeclaration(signature) => (
            SyntaxKind::ConstructSignature,
            InternalSymbolName::New,
            signature.type_parameters.as_ref(),
            &signature.parameters,
            signature.type_,
            signature.full_signature.is_some()
                || signature.next_container.is_some()
                || signature.symbol.is_some(),
        ),
        _ => return Err(invalid(declaration, record.kind)),
    };
    if record.kind != kind || record.flags.0 != 0 || invalid_cache || parameters.has_trailing_comma
    {
        return Err(invalid(declaration, record.kind));
    }

    let symbol = declaration_symbol(bound, store, declaration, SymbolFlags::SIGNATURE)?;
    let symbol_record = store.symbol(symbol).ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
    ))?;
    let members = store
        .symbol(owner)
        .and_then(ts_binder::semantic::Symbol::members)
        .and_then(|members| store.symbol_table(members));
    if symbol_record.flags() != SymbolFlags::SIGNATURE
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name() != name.as_ref()
        || symbol_record.value_declaration().is_some()
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent() != Some(owner)
        || symbol_record.export_symbol().is_some()
        || members.and_then(|members| members.get(name.as_ref())) != Some(symbol)
    {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ));
    }

    plan_interface_signature_annotations(
        arena,
        bound,
        store,
        declaration,
        type_parameters,
        parameters,
        return_type,
        annotations,
    )?;
    Ok(symbol)
}

fn plan_interface_index_signature(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    declaration: NodeRef,
    annotations: &mut Vec<NodeRef>,
) -> Result<SemanticSymbolId, SourceCheckError> {
    let invalid = |node, kind| unsupported(node, kind, SourceSyntaxRole::InterfaceDeclaration);
    let record = owned_node(arena, bound, store, declaration)?;
    let NodeData::IndexSignatureDeclaration(index) = &record.data else {
        return Err(invalid(declaration, record.kind));
    };
    if record.kind != SyntaxKind::IndexSignature
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
        return Err(invalid(declaration, record.kind));
    }

    let parameter = child(declaration, index.parameters.nodes[0]);
    let parameter_record = owned_node(arena, bound, store, parameter)?;
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Err(invalid(parameter, parameter_record.kind));
    };
    if parameter_record.kind != SyntaxKind::Parameter
        || parameter_record.flags.0 != 0
        || parameter_record.parent != Some(declaration.node)
        || parameter_record.range.start < index.parameters.range.start
        || parameter_record.range.end > index.parameters.range.end
        || parameter_data.dot_dot_dot_token.is_some()
        || parameter_data.question_token.is_some()
        || parameter_data.initializer.is_some()
        || parameter_data.modifiers.is_some()
        || parameter_data.symbol.is_some()
        || parameter_data.facts != 0
    {
        return Err(invalid(parameter, parameter_record.kind));
    }
    let key = child(
        parameter,
        parameter_data
            .type_
            .ok_or_else(|| invalid(parameter, parameter_record.kind))?,
    );
    let key_record = owned_node(arena, bound, store, key)?;
    if key_record.kind != SyntaxKind::StringKeyword {
        return Err(invalid(key, key_record.kind));
    }
    owned_node(arena, bound, store, child(declaration, index.type_))?;

    let symbol = declaration_symbol(bound, store, declaration, SymbolFlags::SIGNATURE)?;
    let symbol_record = store.symbol(symbol).ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
    ))?;
    let members = store
        .symbol(owner)
        .and_then(ts_binder::semantic::Symbol::members)
        .and_then(|members| store.symbol_table(members));
    if bound.symbol(declaration) != Some(symbol)
        || symbol_record.flags() != SymbolFlags::SIGNATURE
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name() != InternalSymbolName::Index.as_ref()
        || symbol_record
            .declarations()
            .is_none_or(|declarations| !declarations.contains(&declaration))
        || symbol_record.value_declaration().is_some()
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || store.get_parent_of_symbol(symbol) != Some(owner)
        || symbol_record.export_symbol().is_some()
        || members.and_then(|members| members.get(InternalSymbolName::Index.as_ref()))
            != Some(symbol)
    {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ));
    }

    plan_interface_signature_annotations(
        arena,
        bound,
        store,
        declaration,
        None,
        &index.parameters,
        Some(index.type_),
        annotations,
    )?;
    Ok(symbol)
}

#[allow(clippy::too_many_arguments)] // Signature annotations retain their bound owner and syntax.
fn plan_interface_signature_annotations(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    type_parameters: Option<&NodeList>,
    parameters: &NodeList,
    return_type: Option<ts_ast::NodeId>,
    annotations: &mut Vec<NodeRef>,
) -> Result<(), SourceCheckError> {
    let invalid = |node, kind| unsupported(node, kind, SourceSyntaxRole::InterfaceDeclaration);
    let record = owned_node(arena, bound, store, declaration)?;
    let mut validator = DeferredAmbientFunctionValidator::new(arena, bound, store);
    validator
        .signature(declaration, type_parameters, parameters, return_type)
        .map_err(|error| match error {
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax {
                node, kind, ..
            }) => invalid(node, kind),
            error => error,
        })?;

    if let Some(type_parameters) = type_parameters {
        for parameter in &type_parameters.nodes {
            let parameter = child(declaration, *parameter);
            let NodeData::TypeParameterDeclaration(data) =
                &owned_node(arena, bound, store, parameter)?.data
            else {
                return Err(invalid(parameter, SyntaxKind::TypeParameter));
            };
            annotations.extend(
                [data.constraint, data.default_type]
                    .into_iter()
                    .flatten()
                    .map(|annotation| child(parameter, annotation)),
            );
        }
    }
    for parameter in &parameters.nodes {
        let parameter = child(declaration, *parameter);
        let NodeData::ParameterDeclaration(data) =
            &owned_node(arena, bound, store, parameter)?.data
        else {
            return Err(invalid(parameter, SyntaxKind::Parameter));
        };
        annotations.push(child(
            parameter,
            data.type_
                .ok_or_else(|| invalid(parameter, SyntaxKind::Parameter))?,
        ));
    }
    annotations.push(child(
        declaration,
        return_type.ok_or_else(|| invalid(declaration, record.kind))?,
    ));
    Ok(())
}

fn plan_interface_method_signature(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    declaration: NodeRef,
    annotations: &mut Vec<NodeRef>,
) -> Result<SemanticSymbolId, SourceCheckError> {
    let invalid = |node, kind| unsupported(node, kind, SourceSyntaxRole::InterfaceDeclaration);
    let record = owned_node(arena, bound, store, declaration)?;
    let NodeData::MethodSignatureDeclaration(signature) = &record.data else {
        return Err(invalid(declaration, record.kind));
    };
    if record.kind != SyntaxKind::MethodSignature
        || record.flags.0 != 0
        || signature.full_signature.is_some()
        || signature.next_container.is_some()
        || signature.symbol.is_some()
        || signature.modifiers.is_some()
        || signature.parameters.has_trailing_comma
    {
        return Err(invalid(declaration, record.kind));
    }

    let name = child(declaration, signature.name);
    let name_record = owned_node(arena, bound, store, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invalid(name, name_record.kind));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(invalid(name, name_record.kind));
    }

    let optional = if let Some(token) = signature.postfix_token {
        let token = child(declaration, token);
        let token_record = owned_node(arena, bound, store, token)?;
        if token_record.kind != SyntaxKind::QuestionToken
            || token_record.flags.0 != 0
            || token_record.parent != Some(declaration.node)
            || !matches!(token_record.data, NodeData::Token(_))
        {
            return Err(invalid(token, token_record.kind));
        }
        true
    } else {
        false
    };
    let flags = SymbolFlags::METHOD
        | if optional {
            SymbolFlags::OPTIONAL
        } else {
            SymbolFlags::NONE
        };
    let symbol = declaration_symbol(bound, store, declaration, SymbolFlags::METHOD)?;
    let symbol_record = store.symbol(symbol).ok_or(SourceCheckError::Provenance(
        SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
    ))?;
    let members = store
        .symbol(owner)
        .and_then(ts_binder::semantic::Symbol::members)
        .and_then(|members| store.symbol_table(members));
    if symbol_record.flags() != flags
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || symbol_record
            .declarations()
            .is_none_or(|declarations| !declarations.contains(&declaration))
        || symbol_record.value_declaration().is_none()
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || store.get_parent_of_symbol(symbol) != Some(owner)
        || symbol_record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || members
            .and_then(|members| members.get_source(&identifier.text))
            .and_then(|member| store.get_merged_symbol(member))
            != Some(symbol)
    {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ));
    }

    plan_interface_signature_annotations(
        arena,
        bound,
        store,
        declaration,
        signature.type_parameters.as_ref(),
        &signature.parameters,
        signature.type_,
        annotations,
    )?;
    Ok(symbol)
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

fn plan_generic_computed_interface_property(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    declaration: NodeRef,
    syntax: SourceNamespacePropertySyntax<'_>,
) -> Result<SourceNamespaceComputedPropertyPlan, SourceCheckError> {
    let invalid = |node, kind| unsupported(node, kind, SourceSyntaxRole::InterfaceDeclaration);
    let name = child(declaration, syntax.name);
    let name_record = owned_node(arena, bound, store, name)?;
    let NodeData::ComputedPropertyName(computed) = &name_record.data else {
        return Err(invalid(name, name_record.kind));
    };
    let expression = child(name, computed.expression);
    let expression_record = owned_node(arena, bound, store, expression)?;
    let NodeData::Identifier(identifier) = &expression_record.data else {
        return Err(invalid(expression, expression_record.kind));
    };
    if name_record.kind != SyntaxKind::ComputedPropertyName
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || computed.facts != 0
        || expression_record.kind != SyntaxKind::Identifier
        || expression_record.flags.0 != 0
        || expression_record.parent != Some(name.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(invalid(name, name_record.kind));
    }

    let optional = if let Some(postfix) = syntax.postfix_token {
        let postfix = child(declaration, postfix);
        let postfix_record = owned_node(arena, bound, store, postfix)?;
        if postfix_record.kind != SyntaxKind::QuestionToken
            || postfix_record.parent != Some(declaration.node)
        {
            return Err(invalid(postfix, postfix_record.kind));
        }
        true
    } else {
        false
    };
    if syntax.modifiers.is_some() {
        return Err(invalid(declaration, SyntaxKind::PropertySignature));
    }

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
        || record.check_flags() != CheckFlags::NONE
        || record.name() != InternalSymbolName::Computed.as_ref()
        || record.declarations() != Some(&[declaration])
        || record.value_declaration() != Some(declaration)
        || record.members().is_some()
        || record.exports().is_some()
        || record.parent() != Some(owner)
        || record.export_symbol().is_some()
    {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ));
    }

    let namespace = store
        .get_parent_of_symbol(owner)
        .ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ))?;
    let key = store
        .symbol(namespace)
        .and_then(ts_binder::semantic::Symbol::exports)
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get_source(&identifier.text))
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(|| invalid(expression, expression_record.kind))?;
    let key_record = store
        .symbol(key)
        .ok_or_else(|| invalid(expression, expression_record.kind))?;
    let key_declaration = key_record
        .value_declaration()
        .ok_or_else(|| invalid(expression, expression_record.kind))?;
    let key_declaration_record = owned_node(arena, bound, store, key_declaration)?;
    let NodeData::VariableDeclaration(variable) = &key_declaration_record.data else {
        return Err(invalid(expression, expression_record.kind));
    };
    let annotation = variable
        .type_
        .map(|annotation| child(key_declaration, annotation))
        .ok_or_else(|| invalid(expression, expression_record.kind))?;
    let annotation_record = owned_node(arena, bound, store, annotation)?;
    let NodeData::TypeOperatorNode(operator) = &annotation_record.data else {
        return Err(invalid(expression, expression_record.kind));
    };
    let operand = child(annotation, operator.type_);
    let operand_record = owned_node(arena, bound, store, operand)?;
    if !key_record
        .flags()
        .contains(SymbolFlags::BLOCK_SCOPED_VARIABLE)
        || store.get_parent_of_symbol(key) != Some(namespace)
        || annotation_record.kind != SyntaxKind::TypeOperator
        || annotation_record.parent != Some(key_declaration.node)
        || operator.operator != SyntaxKind::UniqueKeyword
        || operand_record.kind != SyntaxKind::SymbolKeyword
        || operand_record.parent != Some(annotation.node)
    {
        return Err(invalid(expression, expression_record.kind));
    }

    Ok(SourceNamespaceComputedPropertyPlan { symbol, key })
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

#[allow(clippy::too_many_lines)] // Qualified heritage must retain lexical namespace ownership.
fn namespace_interface_heritage_symbol(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: SemanticSymbolId,
    name: NodeRef,
) -> Result<Option<SemanticSymbolId>, SourceCheckError> {
    let record = owned_node(arena, bound, store, name)?;
    if record.flags.0 != 0 {
        return Err(unsupported(
            name,
            record.kind,
            SourceSyntaxRole::InterfaceDeclaration,
        ));
    }
    match &record.data {
        NodeData::Identifier(identifier)
            if record.kind == SyntaxKind::Identifier
                && identifier.flow_node.is_none()
                && !identifier.text.is_empty() =>
        {
            let namespace_export = store
                .symbol(namespace)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| store.symbol_table(exports))
                .and_then(|exports| exports.get_source(&identifier.text));
            let mut local = None;
            let mut current = Some(name);
            while let Some(node) = current {
                local = bound
                    .locals(node)
                    .and_then(|locals| store.symbol_table(locals))
                    .and_then(|locals| locals.get_source(&identifier.text))
                    .and_then(|symbol| {
                        store
                            .symbol(symbol)
                            .map(|record| record.export_symbol().unwrap_or(symbol))
                    });
                if local.is_some() {
                    break;
                }
                current = arena
                    .get(node.node)
                    .and_then(|record| record.parent)
                    .map(|parent| child(node, parent));
            }
            Ok(namespace_export
                .or(local)
                .or_else(|| {
                    store
                        .intrinsic_bootstrap()
                        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
                        .and_then(|globals| globals.get_source(&identifier.text))
                })
                .and_then(|symbol| store.get_merged_symbol(symbol)))
        }
        NodeData::QualifiedName(qualified)
            if record.kind == SyntaxKind::QualifiedName
                && qualified.flow_node.is_none()
                && qualified.facts == 0 =>
        {
            let left = child(name, qualified.left);
            let right = child(name, qualified.right);
            let left_record = owned_node(arena, bound, store, left)?;
            let right_record = owned_node(arena, bound, store, right)?;
            let NodeData::Identifier(identifier) = &right_record.data else {
                return Err(unsupported(
                    right,
                    right_record.kind,
                    SourceSyntaxRole::InterfaceDeclaration,
                ));
            };
            if left_record.parent != Some(name.node)
                || right_record.kind != SyntaxKind::Identifier
                || right_record.flags.0 != 0
                || right_record.parent != Some(name.node)
                || identifier.flow_node.is_some()
                || identifier.text.is_empty()
            {
                return Err(unsupported(
                    name,
                    record.kind,
                    SourceSyntaxRole::InterfaceDeclaration,
                ));
            }
            let owner = namespace_interface_heritage_symbol(arena, bound, store, namespace, left)?;
            Ok(owner
                .and_then(|owner| store.symbol(owner))
                .filter(|owner| owner.flags().intersects(SymbolFlags::NAMESPACE))
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| store.symbol_table(exports))
                .and_then(|exports| exports.get_source(&identifier.text))
                .and_then(|symbol| store.get_merged_symbol(symbol)))
        }
        NodeData::PropertyAccessExpression(access)
            if record.kind == SyntaxKind::PropertyAccessExpression
                && access.flow_node.is_none()
                && access.question_dot_token.is_none()
                && access.facts == 0 =>
        {
            let left = child(name, access.expression);
            let right = child(name, access.name);
            let left_record = owned_node(arena, bound, store, left)?;
            let right_record = owned_node(arena, bound, store, right)?;
            let NodeData::Identifier(identifier) = &right_record.data else {
                return Err(unsupported(
                    right,
                    right_record.kind,
                    SourceSyntaxRole::InterfaceDeclaration,
                ));
            };
            if left_record.parent != Some(name.node)
                || right_record.kind != SyntaxKind::Identifier
                || right_record.flags.0 != 0
                || right_record.parent != Some(name.node)
                || identifier.flow_node.is_some()
                || identifier.text.is_empty()
            {
                return Err(unsupported(
                    name,
                    record.kind,
                    SourceSyntaxRole::InterfaceDeclaration,
                ));
            }
            let owner = namespace_interface_heritage_symbol(arena, bound, store, namespace, left)?;
            Ok(owner
                .and_then(|owner| store.symbol(owner))
                .filter(|owner| owner.flags().intersects(SymbolFlags::NAMESPACE))
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| store.symbol_table(exports))
                .and_then(|exports| exports.get_source(&identifier.text))
                .and_then(|symbol| store.get_merged_symbol(symbol)))
        }
        _ => Err(unsupported(
            name,
            record.kind,
            SourceSyntaxRole::InterfaceDeclaration,
        )),
    }
}

fn plan_namespace_interface_heritage(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    owner: (SemanticSymbolId, NodeRef),
    clauses: &ts_ast::NodeList,
    base_interfaces: &mut Vec<SemanticSymbolId>,
) -> Result<(), SourceCheckError> {
    let (namespace, declaration) = owner;
    let invalid = |node, kind| unsupported(node, kind, SourceSyntaxRole::InterfaceDeclaration);
    let [clause] = clauses.nodes.as_slice() else {
        return Err(invalid(declaration, SyntaxKind::InterfaceDeclaration));
    };
    let clause = child(declaration, *clause);
    let clause_record = owned_node(arena, bound, store, clause)?;
    let NodeData::HeritageClause(heritage) = &clause_record.data else {
        return Err(invalid(clause, clause_record.kind));
    };
    if clauses.has_trailing_comma
        || clause_record.kind != SyntaxKind::HeritageClause
        || clause_record.flags.0 != 0
        || clause_record.parent != Some(declaration.node)
        || heritage.token != SyntaxKind::ExtendsKeyword
        || heritage.facts != 0
        || heritage.types.nodes.is_empty()
        || heritage.types.has_trailing_comma
    {
        return Err(invalid(clause, clause_record.kind));
    }

    for base_id in &heritage.types.nodes {
        let base = child(clause, *base_id);
        let base_record = owned_node(arena, bound, store, base)?;
        let NodeData::ExpressionWithTypeArguments(reference) = &base_record.data else {
            return Err(invalid(base, base_record.kind));
        };
        let name = child(base, reference.expression);
        let name_record = owned_node(arena, bound, store, name)?;
        let symbol = namespace_interface_heritage_symbol(arena, bound, store, namespace, name)?;
        if base_record.kind != SyntaxKind::ExpressionWithTypeArguments
            || base_record.flags.0 != 0
            || base_record.parent != Some(clause.node)
            || reference.facts != 0
            || name_record.parent != Some(base.node)
            || symbol
                .and_then(|symbol| store.symbol(symbol))
                .is_none_or(|record| {
                    !record.flags().intersects(
                        SymbolFlags::INTERFACE | SymbolFlags::CLASS | SymbolFlags::TYPE_ALIAS,
                    )
                })
        {
            return Err(invalid(base, base_record.kind));
        }
        let symbol = symbol.expect("the base symbol was authenticated");
        if base_interfaces.contains(&symbol) {
            return Err(invalid(base, base_record.kind));
        }
        base_interfaces.push(symbol);
        if let Some(arguments) = &reference.type_arguments {
            if arguments.has_trailing_comma || arguments.nodes.is_empty() {
                return Err(invalid(base, base_record.kind));
            }
            let mut validator = DeferredAmbientFunctionValidator::new(arena, bound, store);
            for argument_id in &arguments.nodes {
                let argument = child(base, *argument_id);
                let argument_record = owned_node(arena, bound, store, argument)?;
                if argument_record.parent != Some(base.node) {
                    return Err(invalid_parent(argument, base, argument_record.parent));
                }
                validator.type_node(base, argument)?;
            }
        }
    }

    Ok(())
}

fn merged_namespace_class_interface_members_are_exact(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    members: SymbolTableId,
) -> bool {
    let Some(owner) = store.symbol(symbol) else {
        return false;
    };
    let Some(declarations) = owner.declarations() else {
        return false;
    };
    let Some(class) = owner.value_declaration() else {
        return false;
    };
    let Some(class_record) = arena.get(class.node) else {
        return false;
    };
    let Some(interface_record) = arena.get(declaration.node) else {
        return false;
    };
    if owner.flags() != SymbolFlags::CLASS | SymbolFlags::INTERFACE
        || !declarations.contains(&declaration)
        || !declarations.contains(&class)
        || class_record.kind != SyntaxKind::ClassDeclaration
        || class_record.parent != interface_record.parent
        || bound.symbol(class) != Some(symbol)
        || owner.members() != Some(members)
    {
        return false;
    }

    store.symbol_table(members).is_some_and(|table| {
        table.iter().all(|(_, member)| {
            store.symbol(member).is_some_and(|record| {
                let flags = record.flags();
                record.parent() == Some(symbol)
                    && (flags == SymbolFlags::TYPE_PARAMETER
                        || flags == SymbolFlags::CONSTRUCTOR
                        || flags == SymbolFlags::SIGNATURE
                        || flags == SymbolFlags::METHOD
                        || flags == SymbolFlags::METHOD | SymbolFlags::OPTIONAL
                        || flags == SymbolFlags::PROPERTY
                        || flags == SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL)
                    && record.declarations().is_some_and(|member_declarations| {
                        !member_declarations.is_empty()
                            && member_declarations.iter().all(|member_declaration| {
                                arena
                                    .get(member_declaration.node)
                                    .and_then(|member_record| member_record.parent)
                                    .is_some_and(|parent| {
                                        declarations
                                            .iter()
                                            .any(|declaration| declaration.node == parent)
                                    })
                            })
                    })
            })
        })
    })
}

fn reopened_namespace_generic_interface_members_are_exact(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    namespace: SemanticSymbolId,
    symbol: SemanticSymbolId,
    generic: &SourceNamespaceGenericInterfacePlan,
) -> bool {
    let Some(record) = store.symbol(symbol) else {
        return false;
    };
    let Some(declarations) = record.declarations() else {
        return false;
    };
    if declarations.len() < 2
        || !declarations.contains(&declaration)
        || record.members() != Some(generic.members)
        || store.get_parent_of_symbol(symbol) != Some(namespace)
        || generic.type_parameters.len() != 1
    {
        return false;
    }
    let Ok(host) = DeclaredTypeHost::new([(arena, bound)]) else {
        return false;
    };
    object_members::plan_lazy_merged_generic_interface(store, &host, symbol).is_ok_and(|plan| {
        plan.symbol == symbol
            && plan.namespace == namespace
            && generic.type_parameters == [plan.type_parameter]
            && store.symbol_table(generic.members).is_some_and(|table| {
                table.iter().all(|(name, member)| {
                    store.symbol(member).is_some_and(|member_record| {
                        let flags = member_record.flags();
                        member_record.name() == name
                            && store.get_parent_of_symbol(member) == Some(symbol)
                            && (flags == SymbolFlags::TYPE_PARAMETER
                                || flags == SymbolFlags::TYPE_PARAMETER | SymbolFlags::TRANSIENT
                                || flags == SymbolFlags::SIGNATURE
                                || flags == SymbolFlags::METHOD
                                || flags == SymbolFlags::METHOD | SymbolFlags::OPTIONAL
                                || flags == SymbolFlags::PROPERTY
                                || flags == SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL)
                            && (member_record.check_flags() == CheckFlags::NONE
                                || flags.contains(SymbolFlags::PROPERTY)
                                    && member_record.check_flags() == CheckFlags::READONLY)
                            && member_record.members().is_none()
                            && member_record.exports().is_none()
                            && member_record.export_symbol().is_none()
                            && member_record
                                .declarations()
                                .is_some_and(|member_declarations| {
                                    !member_declarations.is_empty()
                                        && member_declarations.iter().all(|member_declaration| {
                                            owned_node(arena, bound, store, *member_declaration)
                                                .ok()
                                                .and_then(|member_node| member_node.parent)
                                                .is_some_and(|parent| {
                                                    declarations.iter().any(|owner_declaration| {
                                                        owner_declaration.arena
                                                            == member_declaration.arena
                                                            && owner_declaration.file
                                                                == member_declaration.file
                                                            && owner_declaration.node == parent
                                                    })
                                                })
                                                && bound.symbol(*member_declaration).and_then(
                                                    |bound_symbol| {
                                                        store.get_merged_symbol(bound_symbol)
                                                    },
                                                ) == Some(member)
                                        })
                                })
                    })
                })
            })
    })
}

/// Authenticates the source contribution without forcing unrelated global Array members.
#[allow(clippy::too_many_lines)] // Global ownership, augmentation syntax, and method edges are one proof.
fn global_augmentation_array_interface_members_are_exact(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    namespace: SemanticSymbolId,
    symbol: SemanticSymbolId,
    generic: &SourceNamespaceGenericInterfacePlan,
) -> bool {
    let Some(facts) = bound.source_facts() else {
        return false;
    };
    let Some(interface) = arena.get(declaration.node) else {
        return false;
    };
    let NodeData::InterfaceDeclaration(interface_data) = &interface.data else {
        return false;
    };
    let Some(block_id) = interface.parent else {
        return false;
    };
    let Some(block) = arena.get(block_id) else {
        return false;
    };
    let NodeData::ModuleBlock(block_data) = &block.data else {
        return false;
    };
    let Some(global_id) = block.parent else {
        return false;
    };
    let Some(global) = arena.get(global_id) else {
        return false;
    };
    let NodeData::ModuleDeclaration(global_data) = &global.data else {
        return false;
    };
    let global_declaration = child(declaration, global_id);
    let global_name = child(global_declaration, global_data.name);
    let Some(global_name_record) = arena.get(global_name.node) else {
        return false;
    };
    let NodeData::Identifier(global_identifier) = &global_name_record.data else {
        return false;
    };
    let Some(owner) = store.symbol(symbol) else {
        return false;
    };
    let Some(declarations) = owner.declarations() else {
        return false;
    };
    let Some(target) = store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
    else {
        return false;
    };
    let Ok(reference) = validate_direct_generic_reference(store, target) else {
        return false;
    };
    let [parameter] = reference.type_arguments.as_slice() else {
        return false;
    };
    let Some(parameter_symbol) = cached_ordinary_type_parameter_owner(store, *parameter) else {
        return false;
    };
    let Some(members) = store.symbol_table(generic.members) else {
        return false;
    };
    let allowed_flags =
        SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
    if facts.is_default_library()
        || facts.is_javascript_file()
        || !facts.is_external_module()
        || interface.kind != SyntaxKind::InterfaceDeclaration
        || interface.flags.0 != 0
        || interface_data.flow_node.is_some()
        || interface_data.local_symbol.is_some()
        || interface_data.symbol.is_some()
        || interface_data.modifiers.is_some()
        || interface_data.heritage_clauses.is_some()
        || interface_data.members.has_trailing_comma
        || block.kind != SyntaxKind::ModuleBlock
        || block.flags.0 != 0
        || block_data.flow_node.is_some()
        || block_data.facts != 0
        || !block_data.statements.nodes.contains(&declaration.node)
        || global.kind != SyntaxKind::ModuleDeclaration
        || global.flags.0 != 0
        || global.parent != Some(bound.source_file().node)
        || global_data.keyword != SyntaxKind::GlobalKeyword
        || global_data.body != Some(block_id)
        || global_name_record.kind != SyntaxKind::Identifier
        || global_name_record.parent != Some(global_id)
        || global_identifier.flow_node.is_some()
        || global_identifier.text != "global"
        || !bound
            .module_augmentations()
            .iter()
            .any(|augmentation| augmentation.name() == global_name)
        || bound
            .symbol(global_declaration)
            .and_then(|owner| store.get_merged_symbol(owner))
            != Some(namespace)
        || !owner.flags().contains(SymbolFlags::INTERFACE)
        || owner.flags().without(allowed_flags) != SymbolFlags::NONE
        || owner.check_flags() != CheckFlags::NONE
        || owner.name().as_utf8() != Some("Array")
        || owner.parent().is_some()
        || owner.exports().is_some()
        || owner.export_symbol().is_some()
        || owner.members() != Some(generic.members)
        || !declarations.contains(&declaration)
        || !declarations
            .iter()
            .any(|candidate| candidate.file != declaration.file)
        || store
            .intrinsic_bootstrap()
            .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("Array"))
            .and_then(|owner| store.get_merged_symbol(owner))
            != Some(symbol)
        || reference.target != target
        || generic.type_parameters.as_slice() != [parameter_symbol]
        || generic.methods.is_empty()
        || !generic.properties.is_empty()
        || !generic.call_signatures.is_empty()
        || !generic.construct_signatures.is_empty()
        || !generic.index_signatures.is_empty()
        || !generic.computed_properties.is_empty()
        || !generic.base_interfaces.is_empty()
        || interface_data.members.nodes.len() != generic.methods.len()
    {
        return false;
    }

    generic.methods.iter().copied().all(|method| {
        let Some(record) = store.symbol(method) else {
            return false;
        };
        let Some(method_declarations) = record.declarations() else {
            return false;
        };
        record
            .flags()
            .without(SymbolFlags::METHOD | SymbolFlags::OPTIONAL)
            == SymbolFlags::NONE
            && record.flags().contains(SymbolFlags::METHOD)
            && record.check_flags() == CheckFlags::NONE
            && record.members().is_none()
            && record.exports().is_none()
            && record.export_symbol().is_none()
            && store.get_merged_symbol(method) == Some(method)
            && store.get_parent_of_symbol(method) == Some(symbol)
            && members
                .get(record.name())
                .and_then(|member| store.get_merged_symbol(member))
                == Some(method)
            && method_declarations.iter().any(|method_declaration| {
                method_declaration.is_for(arena.id(), bound.file_id())
                    && arena.get(method_declaration.node).is_some_and(|node| {
                        node.kind == SyntaxKind::MethodSignature
                            && node.parent == Some(declaration.node)
                    })
                    && bound
                        .symbol(*method_declaration)
                        .and_then(|bound_symbol| store.get_merged_symbol(bound_symbol))
                        == Some(method)
            })
    })
}

fn namespace_generic_annotation_requires_deferral(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: SemanticSymbolId,
    annotation: NodeRef,
) -> Result<bool, SourceCheckError> {
    let mut pending = vec![annotation];
    let mut visited = HashSet::new();
    while let Some(node) = pending.pop() {
        if !visited.insert(node) {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::RepeatedNode(node),
            ));
        }
        let record = owned_node(arena, bound, store, node)?;
        if let NodeData::TypeReferenceNode(reference) = &record.data {
            let name = child(node, reference.type_name);
            if let Some(target) =
                namespace_interface_heritage_symbol(arena, bound, store, namespace, name)?
                && let Some(target_record) = store.symbol(target)
                && store.get_parent_of_symbol(target) == Some(namespace)
            {
                if target_record.flags() == SymbolFlags::TYPE_ALIAS
                    && target_record.check_flags() == CheckFlags::NONE
                    && target_record.value_declaration().is_none()
                    && target_record.members().is_none()
                    && target_record.exports().is_none()
                    && target_record.export_symbol().is_none()
                    && target_record.declarations().is_some_and(|declarations| {
                        let [declaration] = declarations else {
                            return false;
                        };
                        bound
                            .symbol(*declaration)
                            .and_then(|symbol| store.get_merged_symbol(symbol))
                            == Some(target)
                    })
                    && store
                        .symbol(namespace)
                        .and_then(ts_binder::semantic::Symbol::exports)
                        .and_then(|exports| store.symbol_table(exports))
                        .and_then(|exports| exports.get(target_record.name()))
                        .and_then(|symbol| store.get_merged_symbol(symbol))
                        == Some(target)
                {
                    return Ok(true);
                }

                if node == annotation
                    && authenticated_react_defaulted_component_class_reference(
                        arena, bound, store, namespace, target, node, reference,
                    )
                {
                    return Ok(true);
                }

                if target_record.flags().contains(SymbolFlags::INTERFACE)
                    && !target_record.flags().contains(SymbolFlags::CLASS)
                    && target_record
                        .declarations()
                        .is_some_and(|declarations| declarations.len() > 1)
                {
                    let host =
                        DeclaredTypeHost::new([(arena, bound)]).map_err(DeclaredTypeError::from)?;
                    if object_members::plan_lazy_merged_generic_interface(store, &host, target)
                        .is_ok_and(|plan| plan.namespace == namespace)
                    {
                        return Ok(true);
                    }
                }
            }
        }

        record.for_each_child(|nested| pending.push(child(node, nested)));
    }
    Ok(false)
}

/// Keeps the legacy React component-class default outside eager declaration checks.
#[allow(clippy::too_many_lines)] // Source property, target defaults, and namespace ownership are one proof.
fn authenticated_react_defaulted_component_class_reference(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: SemanticSymbolId,
    target: SemanticSymbolId,
    reference_node: NodeRef,
    reference: &ts_ast::TypeReferenceNodeData,
) -> bool {
    let Some(namespace_record) = store.symbol(namespace) else {
        return false;
    };
    let Some(target_record) = store.symbol(target) else {
        return false;
    };
    let Some([declaration]) = target_record.declarations() else {
        return false;
    };
    let declaration = *declaration;
    let Some(declaration_record) = arena.get(declaration.node) else {
        return false;
    };
    let NodeData::InterfaceDeclaration(interface) = &declaration_record.data else {
        return false;
    };
    let Some(parameters) = interface.type_parameters.as_ref() else {
        return false;
    };
    let Some(arguments) = reference.type_arguments.as_ref() else {
        return false;
    };
    let Some(members) = target_record
        .members()
        .and_then(|members| store.symbol_table(members))
    else {
        return false;
    };
    let Some(facts) = bound.source_facts() else {
        return false;
    };
    let name = child(reference_node, reference.type_name);
    let Some(name_record) = arena.get(name.node) else {
        return false;
    };
    let NodeData::Identifier(identifier) = &name_record.data else {
        return false;
    };
    let Some(reference_record) = arena.get(reference_node.node) else {
        return false;
    };
    let Some(property_node) = reference_record.parent else {
        return false;
    };
    let property_node = child(reference_node, property_node);
    let Some(property_record) = arena.get(property_node.node) else {
        return false;
    };
    let (property_name, property_annotation) = match &property_record.data {
        NodeData::PropertyDeclaration(property)
            if property_record.kind == SyntaxKind::PropertyDeclaration =>
        {
            (property.name, property.type_)
        }
        NodeData::PropertySignatureDeclaration(property)
            if property_record.kind == SyntaxKind::PropertySignature =>
        {
            (property.name, Some(property.type_))
        }
        _ => return false,
    };
    let Some(component_node) = property_record.parent else {
        return false;
    };
    let component_node = child(property_node, component_node);
    let Some(component_record) = arena.get(component_node.node) else {
        return false;
    };
    let NodeData::InterfaceDeclaration(component_interface) = &component_record.data else {
        return false;
    };
    let Some(component) = bound
        .symbol(component_node)
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(component_owner) = store.symbol(component) else {
        return false;
    };
    let Some(component_members) = component_owner
        .members()
        .and_then(|members| store.symbol_table(members))
    else {
        return false;
    };
    let Some(property) = bound
        .symbol(property_node)
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(property_owner) = store.symbol(property) else {
        return false;
    };
    let property_name = child(property_node, property_name);
    let Some(property_name_record) = arena.get(property_name.node) else {
        return false;
    };
    let NodeData::Identifier(property_identifier) = &property_name_record.data else {
        return false;
    };
    if !facts.is_declaration_file()
        || facts.is_default_library()
        || !namespace_record.flags().intersects(SymbolFlags::NAMESPACE)
        || namespace_record.check_flags() != CheckFlags::NONE
        || namespace_record.name().as_utf8() != Some("React")
        || target_record.flags() != SymbolFlags::INTERFACE
        || target_record.check_flags() != CheckFlags::NONE
        || target_record.name().as_utf8() != Some("ComponentClass")
        || target_record.value_declaration().is_some()
        || target_record.exports().is_some()
        || target_record.export_symbol().is_some()
        || !declaration.is_for(arena.id(), bound.file_id())
        || declaration_record.kind != SyntaxKind::InterfaceDeclaration
        || declaration_record.flags.0 != 0
        || bound
            .symbol(declaration)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(target)
        || store.get_parent_of_symbol(target) != Some(namespace)
        || namespace_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source("ComponentClass"))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(target)
        || parameters.has_trailing_comma
        || parameters.nodes.len() != 2
        || arguments.has_trailing_comma
        || arguments.nodes.len() != 1
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(reference_node.node)
        || identifier.flow_node.is_some()
        || identifier.text != "ComponentClass"
        || reference_record.kind != SyntaxKind::TypeReference
        || reference_record.flags.0 != 0
        || property_record.flags.0 != 0
        || property_annotation != Some(reference_node.node)
        || property_name_record.kind != SyntaxKind::Identifier
        || property_name_record.flags.0 != 0
        || property_name_record.parent != Some(property_node.node)
        || property_identifier.flow_node.is_some()
        || property_identifier.text != "type"
        || property_owner.flags() != SymbolFlags::PROPERTY
        || property_owner.check_flags() != CheckFlags::NONE
        || property_owner.name().as_utf8() != Some("type")
        || store.get_parent_of_symbol(property) != Some(component)
        || component_members.get_source("type") != Some(property)
        || component_record.kind != SyntaxKind::InterfaceDeclaration
        || component_record.flags.0 != 0
        || component_interface
            .type_parameters
            .as_ref()
            .is_none_or(|parameters| parameters.nodes.len() != 2)
        || component_owner.flags() != SymbolFlags::INTERFACE
        || component_owner.check_flags() != CheckFlags::NONE
        || component_owner.name().as_utf8() != Some("ComponentElement")
        || store.get_parent_of_symbol(component) != Some(namespace)
        || namespace_record
            .exports()
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source("ComponentElement"))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(component)
    {
        return false;
    }

    let argument = child(reference_node, arguments.nodes[0]);
    let Some(argument_record) = arena.get(argument.node) else {
        return false;
    };
    let NodeData::TypeReferenceNode(argument_reference) = &argument_record.data else {
        return false;
    };
    let argument_name = child(argument, argument_reference.type_name);
    let Some(argument_name_record) = arena.get(argument_name.node) else {
        return false;
    };
    let NodeData::Identifier(argument_identifier) = &argument_name_record.data else {
        return false;
    };
    let Some(argument_parameter) = component_members.get_source("P") else {
        return false;
    };
    let Some(argument_owner) = store.symbol(argument_parameter) else {
        return false;
    };
    if argument_record.kind != SyntaxKind::TypeReference
        || argument_record.flags.0 != 0
        || argument_record.parent != Some(reference_node.node)
        || argument_reference.type_arguments.is_some()
        || argument_name_record.kind != SyntaxKind::Identifier
        || argument_name_record.flags.0 != 0
        || argument_name_record.parent != Some(argument.node)
        || argument_identifier.flow_node.is_some()
        || argument_identifier.text != "P"
        || argument_owner.flags() != SymbolFlags::TYPE_PARAMETER
        || argument_owner.check_flags() != CheckFlags::NONE
        || argument_owner.name().as_utf8() != Some("P")
        || store.get_parent_of_symbol(argument_parameter) != Some(component)
    {
        return false;
    }

    for (parameter, expected_name) in parameters.nodes.iter().zip(["P", "S"]) {
        let parameter = child(declaration, *parameter);
        let Some(parameter_record) = arena.get(parameter.node) else {
            return false;
        };
        let NodeData::TypeParameterDeclaration(data) = &parameter_record.data else {
            return false;
        };
        let Some(default) = data.default_type else {
            return false;
        };
        let default = child(parameter, default);
        let Some(default_record) = arena.get(default.node) else {
            return false;
        };
        let Some(parameter_symbol) = bound
            .symbol(parameter)
            .and_then(|symbol| store.get_merged_symbol(symbol))
        else {
            return false;
        };
        let Some(parameter_owner) = store.symbol(parameter_symbol) else {
            return false;
        };
        if parameter_record.kind != SyntaxKind::TypeParameter
            || parameter_record.flags.0 != 0
            || parameter_record.parent != Some(declaration.node)
            || data.constraint.is_some()
            || data.expression.is_some()
            || data.modifiers.is_some()
            || default_record.parent != Some(parameter.node)
            || parameter_owner.flags() != SymbolFlags::TYPE_PARAMETER
            || parameter_owner.check_flags() != CheckFlags::NONE
            || parameter_owner.name().as_utf8() != Some(expected_name)
            || store.get_parent_of_symbol(parameter_symbol) != Some(target)
            || members.get(parameter_owner.name()) != Some(parameter_symbol)
        {
            return false;
        }
    }

    true
}

/// Proves that a nested, type-only namespace and interface share one binder symbol.
pub(super) fn authenticated_merged_namespace_interface(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Option<NodeRef> {
    let record = store.symbol(symbol)?;
    let declarations = record.declarations()?;
    let first = *declarations.first()?;
    let first_record = host.node(first)?;
    let block = child(first, first_record.parent?);
    let block_record = host.node(block)?;
    let owner_declaration = child(block, block_record.parent?);
    let (_, first_bound) = host.source(first)?;
    let owner = first_bound
        .symbol(owner_declaration)
        .and_then(|owner| store.get_merged_symbol(owner))?;
    let owner_record = store.symbol(owner)?;
    let exports = record
        .exports()
        .and_then(|exports| store.symbol_table(exports))?;
    let exported = owner_record
        .exports()
        .and_then(|exports| store.symbol_table(exports))
        .and_then(|exports| exports.get(record.name()))
        .and_then(|export| store.get_merged_symbol(export));
    let local = first_bound
        .locals(owner_declaration)
        .and_then(|locals| store.symbol_table(locals))
        .and_then(|locals| locals.get(record.name()))
        .and_then(|local| store.get_merged_symbol(local));
    let owner_matches = match store.get_parent_of_symbol(symbol) {
        Some(parent) => parent == owner && exported == Some(symbol),
        None => record.parent().is_none() && local == Some(symbol),
    };
    let allowed = SymbolFlags::INTERFACE | SymbolFlags::NAMESPACE_MODULE | SymbolFlags::TRANSIENT;
    if !record
        .flags()
        .contains(SymbolFlags::INTERFACE | SymbolFlags::NAMESPACE_MODULE)
        || record.flags().without(allowed) != SymbolFlags::NONE
        || record.check_flags() != CheckFlags::NONE
        || record.value_declaration().is_some()
        || record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || !owner_record.flags().intersects(SymbolFlags::MODULE)
        || !owner_matches
        || exports.iter().any(|(_, export)| {
            store
                .get_merged_symbol(export)
                .and_then(|export| store.symbol(export).map(|record| (export, record)))
                .is_none_or(|(export, record)| {
                    !record
                        .flags()
                        .intersects(SymbolFlags::TYPE | SymbolFlags::NAMESPACE)
                        || record.flags().intersects(SymbolFlags::VALUE)
                        || store.get_parent_of_symbol(export) != Some(symbol)
                })
        })
    {
        return None;
    }

    let mut interface = None;
    let mut has_namespace = false;
    let mut seen = HashSet::with_capacity(declarations.len());
    for declaration in declarations {
        let declaration = *declaration;
        let (arena, bound) = host.source(declaration)?;
        let node = host.node(declaration)?;
        if !seen.insert(declaration) || !host.symbol_matches(store, declaration, symbol) {
            return None;
        }

        let block = child(declaration, node.parent?);
        let block_record = host.node(block)?;
        let NodeData::ModuleBlock(body) = &block_record.data else {
            return None;
        };
        let parent = child(block, block_record.parent?);
        if block_record.kind != SyntaxKind::ModuleBlock
            || !body.statements.nodes.contains(&declaration.node)
            || !host.symbol_matches(store, parent, owner)
            || !bound.contains(declaration)
            || arena.id() != declaration.arena
            || record.parent().is_none()
                && bound
                    .locals(parent)
                    .and_then(|locals| store.symbol_table(locals))
                    .and_then(|locals| locals.get(record.name()))
                    .and_then(|local| store.get_merged_symbol(local))
                    != Some(symbol)
        {
            return None;
        }

        match &node.data {
            NodeData::InterfaceDeclaration(data)
                if node.kind == SyntaxKind::InterfaceDeclaration
                    && data.type_parameters.is_none()
                    && data.heritage_clauses.is_none()
                    && (data.members.nodes.is_empty() || record.members().is_some())
                    && host
                        .node(child(declaration, data.name))
                        .is_some_and(|name| {
                            matches!(
                                &name.data,
                                NodeData::Identifier(name)
                                    if record.name().as_utf8() == Some(name.text.as_str())
                            )
                        }) =>
            {
                interface.get_or_insert(declaration);
            }
            NodeData::ModuleDeclaration(data)
                if node.kind == SyntaxKind::ModuleDeclaration
                    && data.keyword == SyntaxKind::NamespaceKeyword
                    && host
                        .node(child(declaration, data.name))
                        .is_some_and(|name| {
                            matches!(
                                &name.data,
                                NodeData::Identifier(name)
                                    if record.name().as_utf8() == Some(name.text.as_str())
                            )
                        }) =>
            {
                has_namespace = true;
            }
            _ => return None,
        }
    }
    interface.filter(|_| has_namespace)
}

/// Authenticates the exact nongeneric React SVG factory before deferring its call annotations.
#[allow(clippy::too_many_lines)] // Namespace, alias, generic arguments, and callable ownership form one proof.
fn authenticated_react_svg_factory_signature(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: SemanticSymbolId,
    factory: SemanticSymbolId,
    declaration: NodeRef,
    signature: NodeRef,
) -> bool {
    let Some(facts) = bound.source_facts() else {
        return false;
    };
    let Some(namespace_owner) = store.symbol(namespace) else {
        return false;
    };
    let Some(factory_owner) = store.symbol(factory) else {
        return false;
    };
    let Some(exports) = namespace_owner
        .exports()
        .and_then(|exports| store.symbol_table(exports))
    else {
        return false;
    };
    let Some(record) = arena.get(declaration.node) else {
        return false;
    };
    let NodeData::InterfaceDeclaration(interface) = &record.data else {
        return false;
    };
    let Some(clauses) = interface.heritage_clauses.as_ref() else {
        return false;
    };
    let [clause] = clauses.nodes.as_slice() else {
        return false;
    };
    let clause = child(declaration, *clause);
    let Some(clause_record) = arena.get(clause.node) else {
        return false;
    };
    let NodeData::HeritageClause(heritage) = &clause_record.data else {
        return false;
    };
    let [base] = heritage.types.nodes.as_slice() else {
        return false;
    };
    let base = child(clause, *base);
    let Some(base_record) = arena.get(base.node) else {
        return false;
    };
    let NodeData::ExpressionWithTypeArguments(base_reference) = &base_record.data else {
        return false;
    };
    let Some([base_attributes, base_element]) = base_reference
        .type_arguments
        .as_ref()
        .map(|arguments| arguments.nodes.as_slice())
    else {
        return false;
    };
    let alias_name = child(base, base_reference.expression);
    let Some(alias_name_record) = arena.get(alias_name.node) else {
        return false;
    };
    let NodeData::Identifier(alias_identifier) = &alias_name_record.data else {
        return false;
    };
    let Some(alias) = exports
        .get_source("DOMFactory")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(alias_owner) = store.symbol(alias) else {
        return false;
    };
    let Some([alias_declaration]) = alias_owner.declarations() else {
        return false;
    };
    let Some(alias_record) = arena.get(alias_declaration.node) else {
        return false;
    };
    let NodeData::TypeAliasDeclaration(alias_data) = &alias_record.data else {
        return false;
    };
    let Some(svg_attributes) = exports
        .get_source("SVGAttributes")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(class_attributes) = exports
        .get_source("ClassAttributes")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(globals) = store
        .intrinsic_bootstrap()
        .and_then(|bootstrap| store.symbol_table(bootstrap.globals))
    else {
        return false;
    };
    let Some(element) = globals
        .get_source("SVGElement")
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return false;
    };
    let Some(element_owner) = store.symbol(element) else {
        return false;
    };
    let Some(signature_record) = arena.get(signature.node) else {
        return false;
    };
    let NodeData::CallSignatureDeclaration(call) = &signature_record.data else {
        return false;
    };
    let [props, children] = call.parameters.nodes.as_slice() else {
        return false;
    };
    let props = child(signature, *props);
    let children = child(signature, *children);
    let Some(props_record) = arena.get(props.node) else {
        return false;
    };
    let NodeData::ParameterDeclaration(props_data) = &props_record.data else {
        return false;
    };
    let Some(children_record) = arena.get(children.node) else {
        return false;
    };
    let NodeData::ParameterDeclaration(children_data) = &children_record.data else {
        return false;
    };
    let Some(annotation) = props_data.type_.map(|annotation| child(props, annotation)) else {
        return false;
    };
    let Some(annotation_record) = arena.get(annotation.node) else {
        return false;
    };
    let NodeData::UnionTypeNode(union) = &annotation_record.data else {
        return false;
    };
    let [intersection, null] = union.types.nodes.as_slice() else {
        return false;
    };
    let intersection = child(annotation, *intersection);
    let null = child(annotation, *null);
    let Some(intersection_record) = arena.get(intersection.node) else {
        return false;
    };
    let NodeData::IntersectionTypeNode(intersection_data) = &intersection_record.data else {
        return false;
    };
    let [class_reference, attributes_reference] = intersection_data.types.nodes.as_slice() else {
        return false;
    };
    let Some(null_record) = arena.get(null.node) else {
        return false;
    };
    let NodeData::LiteralTypeNode(null_data) = &null_record.data else {
        return false;
    };
    let null_keyword = child(null, null_data.literal);

    if !facts.is_declaration_file()
        || facts.is_default_library()
        || namespace_owner.name().as_utf8() != Some("React")
        || !namespace_owner.flags().intersects(SymbolFlags::NAMESPACE)
        || namespace_owner.check_flags() != CheckFlags::NONE
        || store.get_merged_symbol(namespace) != Some(namespace)
        || factory_owner.name().as_utf8() != Some("SVGFactory")
        || factory_owner.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
        || factory_owner.check_flags() != CheckFlags::NONE
        || store.get_parent_of_symbol(factory) != Some(namespace)
        || exports
            .get_source("SVGFactory")
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(factory)
        || factory_owner.declarations() != Some(&[declaration])
        || record.kind != SyntaxKind::InterfaceDeclaration
        || interface.type_parameters.is_some()
        || interface.members.nodes.as_slice() != [signature.node]
        || clause_record.kind != SyntaxKind::HeritageClause
        || clause_record.parent != Some(declaration.node)
        || base_record.kind != SyntaxKind::ExpressionWithTypeArguments
        || base_record.parent != Some(clause.node)
        || alias_name_record.kind != SyntaxKind::Identifier
        || alias_name_record.parent != Some(base.node)
        || alias_identifier.text != "DOMFactory"
        || alias_owner.name().as_utf8() != Some("DOMFactory")
        || alias_owner.flags() != SymbolFlags::TYPE_ALIAS
        || alias_owner.check_flags() != CheckFlags::NONE
        || store.get_parent_of_symbol(alias) != Some(namespace)
        || alias_record.kind != SyntaxKind::TypeAliasDeclaration
        || alias_record.parent != record.parent
        || alias_data
            .type_parameters
            .as_ref()
            .is_none_or(|parameters| parameters.nodes.len() != 2)
        || element_owner.name().as_utf8() != Some("SVGElement")
        || !element_owner.flags().contains(SymbolFlags::INTERFACE)
        || signature_record.kind != SyntaxKind::CallSignature
        || signature_record.parent != Some(declaration.node)
        || call.type_parameters.is_some()
        || props_record.kind != SyntaxKind::Parameter
        || props_record.parent != Some(signature.node)
        || props_data.question_token.is_none()
        || props_data.dot_dot_dot_token.is_some()
        || !matches!(
            arena.get(props_data.name).map(|record| &record.data),
            Some(NodeData::Identifier(identifier)) if identifier.text == "props"
        )
        || children_record.kind != SyntaxKind::Parameter
        || children_record.parent != Some(signature.node)
        || children_data.dot_dot_dot_token.is_none()
        || children_data.question_token.is_some()
        || !matches!(
            arena.get(children_data.name).map(|record| &record.data),
            Some(NodeData::Identifier(identifier)) if identifier.text == "children"
        )
        || annotation_record.kind != SyntaxKind::UnionType
        || annotation_record.parent != Some(props.node)
        || intersection_record.kind != SyntaxKind::IntersectionType
        || intersection_record.parent != Some(annotation.node)
        || null_record.kind != SyntaxKind::LiteralType
        || null_record.parent != Some(annotation.node)
        || arena
            .get(null_keyword.node)
            .is_none_or(|record| record.kind != SyntaxKind::NullKeyword)
    {
        return false;
    }

    for (reference, parent, expected, expected_symbol) in [
        (
            child(base, *base_attributes),
            base,
            "SVGAttributes",
            svg_attributes,
        ),
        (
            child(intersection, *class_reference),
            intersection,
            "ClassAttributes",
            class_attributes,
        ),
        (
            child(intersection, *attributes_reference),
            intersection,
            "SVGAttributes",
            svg_attributes,
        ),
    ] {
        let Some(reference_record) = arena.get(reference.node) else {
            return false;
        };
        let NodeData::TypeReferenceNode(data) = &reference_record.data else {
            return false;
        };
        let Some([argument]) = data
            .type_arguments
            .as_ref()
            .map(|arguments| arguments.nodes.as_slice())
        else {
            return false;
        };
        let name = child(reference, data.type_name);
        let Some(name_record) = arena.get(name.node) else {
            return false;
        };
        let NodeData::Identifier(identifier) = &name_record.data else {
            return false;
        };
        let Some(target) = store.symbol(expected_symbol) else {
            return false;
        };
        let argument = child(reference, *argument);
        let Some(argument_record) = arena.get(argument.node) else {
            return false;
        };
        let NodeData::TypeReferenceNode(argument_data) = &argument_record.data else {
            return false;
        };
        let element_name = child(argument, argument_data.type_name);
        let Some(element_name_record) = arena.get(element_name.node) else {
            return false;
        };
        let NodeData::Identifier(element_identifier) = &element_name_record.data else {
            return false;
        };
        if reference_record.kind != SyntaxKind::TypeReference
            || reference_record.parent != Some(parent.node)
            || name_record.kind != SyntaxKind::Identifier
            || name_record.parent != Some(reference.node)
            || identifier.text != expected
            || target.name().as_utf8() != Some(expected)
            || target.flags().without(SymbolFlags::TRANSIENT) != SymbolFlags::INTERFACE
            || target.check_flags() != CheckFlags::NONE
            || store.get_parent_of_symbol(expected_symbol) != Some(namespace)
            || exports
                .get_source(expected)
                .and_then(|symbol| store.get_merged_symbol(symbol))
                != Some(expected_symbol)
            || argument_record.kind != SyntaxKind::TypeReference
            || argument_record.parent != Some(reference.node)
            || argument_data.type_arguments.is_some()
            || element_name_record.kind != SyntaxKind::Identifier
            || element_name_record.parent != Some(argument.node)
            || element_identifier.text != "SVGElement"
        {
            return false;
        }
    }

    let base_element = child(base, *base_element);
    let Some(base_element_record) = arena.get(base_element.node) else {
        return false;
    };
    let NodeData::TypeReferenceNode(base_element_data) = &base_element_record.data else {
        return false;
    };
    let base_element_name = child(base_element, base_element_data.type_name);
    matches!(
        arena.get(base_element_name.node).map(|record| &record.data),
        Some(NodeData::Identifier(identifier)) if identifier.text == "SVGElement"
    ) && base_element_record.kind == SyntaxKind::TypeReference
        && base_element_record.parent == Some(base.node)
        && base_element_data.type_arguments.is_none()
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
    if let Some(heritage) = &interface.heritage_clauses {
        if let Some(generic) = generic.as_mut() {
            plan_namespace_interface_heritage(
                arena,
                bound,
                store,
                (owner, declaration),
                heritage,
                &mut generic.base_interfaces,
            )?;
        } else if bound
            .source_facts()
            .is_some_and(ts_binder::CanonicalSourceFileFacts::is_declaration_file)
            && !(store
                .symbol(owner)
                .and_then(|symbol| symbol.name().as_utf8())
                == Some("JSX")
                && arena.get(interface.name).is_some_and(|name| {
                    matches!(&name.data, NodeData::Identifier(name) if name.text == "IntrinsicElements")
                }))
        {
            let mut bases = Vec::new();
            plan_namespace_interface_heritage(
                arena,
                bound,
                store,
                (owner, declaration),
                heritage,
                &mut bases,
            )?;
        } else {
            annotations.extend(plan_jsx_record_interface_heritage(
                arena,
                bound,
                store,
                owner,
                declaration,
                heritage,
            )?);
        }
    }
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
            NodeData::CallSignatureDeclaration(_)
                if member_record.kind == SyntaxKind::CallSignature =>
            {
                let first_annotation = annotations.len();
                let call = plan_interface_callable_signature(
                    arena,
                    bound,
                    store,
                    symbol,
                    member,
                    &mut annotations,
                )?;
                if let Some(generic) = generic.as_mut() {
                    generic
                        .deferred_annotations
                        .extend_from_slice(&annotations[first_annotation..]);
                    if !generic.call_signatures.contains(&call) {
                        generic.call_signatures.push(call);
                    }
                } else if authenticated_react_svg_factory_signature(
                    arena,
                    bound,
                    store,
                    owner,
                    symbol,
                    declaration,
                    member,
                ) {
                    annotations.truncate(first_annotation);
                }
            }
            NodeData::ConstructSignatureDeclaration(_)
                if member_record.kind == SyntaxKind::ConstructSignature =>
            {
                let first_annotation = annotations.len();
                let constructor = plan_interface_callable_signature(
                    arena,
                    bound,
                    store,
                    symbol,
                    member,
                    &mut annotations,
                )?;
                if let Some(generic) = generic.as_mut() {
                    generic
                        .deferred_annotations
                        .extend_from_slice(&annotations[first_annotation..]);
                    if !generic.construct_signatures.contains(&constructor) {
                        generic.construct_signatures.push(constructor);
                    }
                }
            }
            NodeData::MethodSignatureDeclaration(_)
                if member_record.kind == SyntaxKind::MethodSignature =>
            {
                let first_annotation = annotations.len();
                let method = plan_interface_method_signature(
                    arena,
                    bound,
                    store,
                    symbol,
                    member,
                    &mut annotations,
                )?;
                if let Some(generic) = generic.as_mut() {
                    generic
                        .deferred_annotations
                        .extend_from_slice(&annotations[first_annotation..]);
                    if !generic.methods.contains(&method) {
                        generic.methods.push(method);
                    }
                }
            }
            NodeData::IndexSignatureDeclaration(_)
                if member_record.kind == SyntaxKind::IndexSignature && generic.is_some() =>
            {
                let first_annotation = annotations.len();
                let index = plan_interface_index_signature(
                    arena,
                    bound,
                    store,
                    symbol,
                    member,
                    &mut annotations,
                )?;
                if let Some(generic) = generic.as_mut() {
                    generic
                        .deferred_annotations
                        .extend_from_slice(&annotations[first_annotation..]);
                    if !generic.index_signatures.contains(&index) {
                        generic.index_signatures.push(index);
                    }
                }
            }
            NodeData::PropertyDeclaration(property)
                if member_record.kind == SyntaxKind::PropertyDeclaration
                    && property.initializer.is_none() =>
            {
                let Some(annotation) = property.type_ else {
                    let augmentation = record
                        .parent
                        .and_then(|body| arena.get(body))
                        .filter(|body| body.kind == SyntaxKind::ModuleBlock)
                        .and_then(|body| body.parent)
                        .map(|namespace| child(declaration, namespace));
                    let augmentation_name = augmentation
                        .and_then(|namespace| {
                            arena.get(namespace.node).map(|record| (namespace, record))
                        })
                        .and_then(|(namespace, record)| match &record.data {
                            NodeData::ModuleDeclaration(module)
                                if record.kind == SyntaxKind::ModuleDeclaration =>
                            {
                                Some(child(namespace, module.name))
                            }
                            _ => None,
                        });
                    let name = child(member, property.name);
                    let name_record = owned_node(arena, bound, store, name)?;
                    let member_symbol =
                        declaration_symbol(bound, store, member, SymbolFlags::PROPERTY)?;
                    let member_owner =
                        store
                            .symbol(member_symbol)
                            .ok_or(SourceCheckError::Provenance(
                                SourceCheckProvenanceError::MissingDeclarationSymbol(member),
                            ))?;
                    if generic.is_some()
                        || augmentation_name.is_none_or(|name| {
                            !bound
                                .module_augmentations()
                                .iter()
                                .any(|augmentation| augmentation.name() == name)
                        })
                        || member_record.flags.0 != 0
                        || property.postfix_token.is_some()
                        || property.modifiers.is_some()
                        || property.symbol.is_some()
                        || property.facts != 0
                        || name_record.kind != SyntaxKind::Identifier
                        || name_record.flags.0 != 0
                        || name_record.parent != Some(member.node)
                        || !matches!(
                            &name_record.data,
                            NodeData::Identifier(identifier)
                                if identifier.flow_node.is_none()
                                    && !identifier.text.is_empty()
                                    && member_owner.name().as_utf8()
                                        == Some(identifier.text.as_str())
                        )
                        || member_owner.flags() != SymbolFlags::PROPERTY
                        || member_owner.check_flags() != CheckFlags::NONE
                        || member_owner.parent() != Some(symbol)
                        || store.get_merged_symbol(member_symbol) != Some(member_symbol)
                        || store
                            .symbol(symbol)
                            .and_then(ts_binder::semantic::Symbol::members)
                            .and_then(|members| store.symbol_table(members))
                            .and_then(|members| members.get(member_owner.name()))
                            != Some(member_symbol)
                    {
                        return Err(unsupported(
                            member,
                            member_record.kind,
                            SourceSyntaxRole::InterfaceDeclaration,
                        ));
                    }
                    continue;
                };
                let annotation = child(member, annotation);
                annotations.push(annotation);
                if let Some(generic) = generic.as_mut() {
                    let syntax = SourceNamespacePropertySyntax {
                        name: property.name,
                        annotation,
                        postfix_token: property.postfix_token,
                        modifiers: property.modifiers.as_ref(),
                    };
                    if arena
                        .get(property.name)
                        .is_some_and(|name| name.kind == SyntaxKind::ComputedPropertyName)
                    {
                        generic
                            .computed_properties
                            .push(plan_generic_computed_interface_property(
                                arena, bound, store, symbol, member, syntax,
                            )?);
                    } else {
                        generic.properties.push(plan_generic_interface_property(
                            arena,
                            bound,
                            store,
                            symbol,
                            generic.members,
                            member,
                            syntax,
                        )?);
                    }
                }
            }
            NodeData::PropertySignatureDeclaration(property)
                if member_record.kind == SyntaxKind::PropertySignature =>
            {
                let annotation = child(member, property.type_);
                annotations.push(annotation);
                if let Some(generic) = generic.as_mut() {
                    let syntax = SourceNamespacePropertySyntax {
                        name: property.name,
                        annotation,
                        postfix_token: property.postfix_token,
                        modifiers: property.modifiers.as_ref(),
                    };
                    if arena
                        .get(property.name)
                        .is_some_and(|name| name.kind == SyntaxKind::ComputedPropertyName)
                    {
                        generic
                            .computed_properties
                            .push(plan_generic_computed_interface_property(
                                arena, bound, store, symbol, member, syntax,
                            )?);
                    } else {
                        generic.properties.push(plan_generic_interface_property(
                            arena,
                            bound,
                            store,
                            symbol,
                            generic.members,
                            member,
                            syntax,
                        )?);
                    }
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
            != generic.type_parameters.len()
                + generic.properties.len()
                + generic.call_signatures.len()
                + generic.construct_signatures.len()
                + generic.index_signatures.len()
                + generic.methods.len()
        && !merged_namespace_class_interface_members_are_exact(
            arena,
            bound,
            store,
            declaration,
            symbol,
            generic.members,
        )
        && !reopened_namespace_generic_interface_members_are_exact(
            arena,
            bound,
            store,
            declaration,
            owner,
            symbol,
            generic,
        )
        && !global_augmentation_array_interface_members_are_exact(
            arena,
            bound,
            store,
            declaration,
            owner,
            symbol,
            generic,
        )
    {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ));
    }
    if bound
        .source_facts()
        .is_some_and(ts_binder::CanonicalSourceFileFacts::is_declaration_file)
        && let Some(generic) = generic.as_mut()
    {
        for annotation in &annotations {
            if generic.annotation_is_deferred(*annotation)
                || !namespace_generic_annotation_requires_deferral(
                    arena,
                    bound,
                    store,
                    owner,
                    *annotation,
                )?
            {
                continue;
            }
            let annotation_record = owned_node(arena, bound, store, *annotation)?;
            let parent = annotation_record
                .parent
                .map(|parent| child(*annotation, parent))
                .ok_or_else(|| invalid_parent(*annotation, declaration, None))?;
            DeferredAmbientFunctionValidator::new(arena, bound, store)
                .type_node(parent, *annotation)
                .map_err(|error| match error {
                    SourceCheckError::Unsupported(UnsupportedSourceSyntax::Syntax {
                        node,
                        kind,
                        ..
                    }) => unsupported(node, kind, SourceSyntaxRole::InterfaceDeclaration),
                    error => error,
                })?;
            generic.deferred_annotations.push(*annotation);
        }
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
    let declaration_file = bound
        .source_facts()
        .is_some_and(ts_binder::CanonicalSourceFileFacts::is_declaration_file);
    let deferred = declaration_file
        && annotation_record.kind != SyntaxKind::IntrinsicKeyword
        && alias
            .type_parameters
            .as_ref()
            .is_some_and(|parameters| !parameters.nodes.is_empty());
    let deferred = if deferred {
        let parameters = alias
            .type_parameters
            .as_ref()
            .expect("generic aliases retain their type parameters");
        match DeferredAmbientFunctionValidator::new(arena, bound, store).type_alias(
            declaration,
            owner,
            symbol,
            parameters,
            annotation,
        ) {
            Ok(()) => {
                let mut references_are_bound = deferred_namespace_alias_references_are_bound(
                    arena, bound, store, owner, annotation,
                )?;
                for parameter in &parameters.nodes {
                    let parameter = child(declaration, *parameter);
                    let NodeData::TypeParameterDeclaration(data) =
                        &owned_node(arena, bound, store, parameter)?.data
                    else {
                        return Err(SourceCheckError::Provenance(
                            SourceCheckProvenanceError::MissingDeclarationSymbol(parameter),
                        ));
                    };
                    for annotation in [data.constraint, data.default_type].into_iter().flatten() {
                        references_are_bound &= deferred_namespace_alias_references_are_bound(
                            arena,
                            bound,
                            store,
                            owner,
                            child(parameter, annotation),
                        )?;
                    }
                }
                references_are_bound
            }
            Err(SourceCheckError::Unsupported(_)) => false,
            Err(error) => return Err(error),
        }
    } else {
        false
    };
    let mut parameter_annotations = Vec::new();
    if declaration_file && !deferred {
        for parameter in alias
            .type_parameters
            .iter()
            .flat_map(|parameters| &parameters.nodes)
        {
            let parameter = child(declaration, *parameter);
            let parameter_record = owned_node(arena, bound, store, parameter)?;
            let NodeData::TypeParameterDeclaration(data) = &parameter_record.data else {
                return Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::MissingDeclarationSymbol(parameter),
                ));
            };
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
                parameter_annotations.push(annotation);
            }
        }
    }
    Ok(SourceNamespaceMemberPlan::TypeAlias {
        declaration,
        symbol,
        annotation,
        parameter_annotations,
        deferred,
    })
}

fn deferred_namespace_alias_references_are_bound(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: SemanticSymbolId,
    annotation: NodeRef,
) -> Result<bool, SourceCheckError> {
    let mut pending = vec![annotation];
    let mut visited = HashSet::new();
    while let Some(node) = pending.pop() {
        if !visited.insert(node) {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::RepeatedNode(node),
            ));
        }
        let record = owned_node(arena, bound, store, node)?;
        if let NodeData::TypeReferenceNode(reference) = &record.data {
            let Some(target) = namespace_interface_heritage_symbol(
                arena,
                bound,
                store,
                namespace,
                child(node, reference.type_name),
            )?
            else {
                return Ok(false);
            };
            let Some(target_record) = store.symbol(target) else {
                return Ok(false);
            };
            let argument_count = reference
                .type_arguments
                .as_ref()
                .map_or(0, |arguments| arguments.nodes.len());
            if target_record.flags().contains(SymbolFlags::TYPE_PARAMETER) {
                if argument_count != 0 {
                    return Ok(false);
                }
            } else if target_record
                .flags()
                .intersects(SymbolFlags::TYPE_ALIAS | SymbolFlags::INTERFACE | SymbolFlags::CLASS)
                && let Some(declaration) = target_record
                    .declarations()
                    .and_then(|declarations| declarations.first())
                    .filter(|declaration| declaration.is_for(arena.id(), bound.file_id()))
                && let Some(declaration_record) = arena.get(declaration.node)
            {
                let parameters = match &declaration_record.data {
                    NodeData::TypeAliasDeclaration(alias) => alias.type_parameters.as_ref(),
                    NodeData::InterfaceDeclaration(interface) => interface.type_parameters.as_ref(),
                    NodeData::ClassDeclaration(class) => class.type_parameters.as_ref(),
                    _ => None,
                };
                let maximum = parameters.map_or(0, |parameters| parameters.nodes.len());
                let minimum = parameters.map_or(0, |parameters| {
                    parameters
                        .nodes
                        .iter()
                        .filter(|parameter| {
                            matches!(
                                arena.get(**parameter).map(|parameter| &parameter.data),
                                Some(NodeData::TypeParameterDeclaration(parameter))
                                    if parameter.default_type.is_none()
                            )
                        })
                        .count()
                });
                if argument_count < minimum || argument_count > maximum {
                    return Ok(false);
                }
            }
        }
        record.for_each_child(|nested| pending.push(child(node, nested)));
    }
    Ok(true)
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

fn namespace_overload_error(declaration: NodeRef, error: SourceOverloadError) -> SourceCheckError {
    match error {
        SourceOverloadError::Unsupported(node) => unsupported(
            node,
            SyntaxKind::FunctionDeclaration,
            SourceSyntaxRole::FunctionDeclaration,
        ),
        SourceOverloadError::Callable(error) => namespace_callable_error(declaration, error),
        SourceOverloadError::Literal(error) => error.into(),
        SourceOverloadError::Invariant(_) => {
            SourceCheckError::Function(SourceFunctionInvariant::Callable(declaration))
        }
    }
}

struct DeferredAmbientFunctionValidator<'a> {
    arena: &'a NodeArena,
    bound: &'a BoundFile,
    store: &'a CanonicalTypeMapperStore,
    visited: HashSet<NodeRef>,
    annotations: Vec<NodeRef>,
}

struct DeferredAmbientSignatureParameters {
    type_parameters: Vec<SemanticSymbolId>,
    parameters: Vec<SemanticSymbolId>,
    names: HashSet<String>,
}

impl<'a> DeferredAmbientFunctionValidator<'a> {
    fn new(
        arena: &'a NodeArena,
        bound: &'a BoundFile,
        store: &'a CanonicalTypeMapperStore,
    ) -> Self {
        Self {
            arena,
            bound,
            store,
            visited: HashSet::new(),
            annotations: Vec::new(),
        }
    }

    fn invalid(node: NodeRef, kind: SyntaxKind) -> SourceCheckError {
        unsupported(node, kind, SourceSyntaxRole::FunctionDeclaration)
    }

    fn visit(&mut self, parent: NodeRef, node: NodeRef) -> Result<&'a Node, SourceCheckError> {
        let record = owned_node(self.arena, self.bound, self.store, node)?;
        let parent_record = owned_node(self.arena, self.bound, self.store, parent)?;
        if record.parent != Some(parent.node) {
            return Err(invalid_parent(node, parent, record.parent));
        }
        if record.flags.0 != 0
            || !record.data.matches_syntax_kind(record.kind)
            || record.range.start < parent_record.range.start
            || record.range.end > parent_record.range.end
        {
            return Err(Self::invalid(node, record.kind));
        }
        if !self.visited.insert(node) {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::RepeatedNode(node),
            ));
        }
        Ok(record)
    }

    fn identifier(&mut self, parent: NodeRef, node: NodeRef) -> Result<String, SourceCheckError> {
        let record = self.visit(parent, node)?;
        let NodeData::Identifier(identifier) = &record.data else {
            return Err(Self::invalid(node, record.kind));
        };
        if record.kind != SyntaxKind::Identifier
            || identifier.flow_node.is_some()
            || identifier.text.is_empty()
        {
            return Err(Self::invalid(node, record.kind));
        }
        Ok(identifier.text.clone())
    }

    fn local_symbol(
        &self,
        container: NodeRef,
        declaration: NodeRef,
        name: &str,
        flags: SymbolFlags,
    ) -> Result<SemanticSymbolId, SourceCheckError> {
        let symbol = declaration_symbol(self.bound, self.store, declaration, flags)?;
        let record = self
            .store
            .symbol(symbol)
            .ok_or(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
            ))?;
        let value_declaration = if flags == SymbolFlags::TYPE_PARAMETER {
            None
        } else {
            Some(declaration)
        };
        if self.bound.symbol(declaration) != Some(symbol)
            || record.flags() != flags
            || record.check_flags() != CheckFlags::NONE
            || record.name().as_utf8() != Some(name)
            || record.declarations() != Some(&[declaration])
            || record.value_declaration() != value_declaration
            || record.members().is_some()
            || record.exports().is_some()
            || record.parent().is_some()
            || record.export_symbol().is_some()
            || self
                .bound
                .locals(container)
                .and_then(|locals| self.store.symbol_table(locals))
                .and_then(|locals| locals.get_source(name))
                != Some(symbol)
        {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
            ));
        }
        Ok(symbol)
    }

    fn type_alias_owner(
        &self,
        declaration: NodeRef,
        namespace: SemanticSymbolId,
        symbol: SemanticSymbolId,
    ) -> bool {
        let Some(owner) = self.store.symbol(symbol) else {
            return false;
        };
        let Some(exports) = self
            .store
            .symbol(namespace)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| self.store.symbol_table(exports))
        else {
            return false;
        };
        if self.store.get_parent_of_symbol(symbol) == Some(namespace) {
            return exports
                .get(owner.name())
                .and_then(|export| self.store.get_merged_symbol(export))
                == Some(symbol);
        }
        if owner.parent().is_some()
            || !self
                .bound
                .source_facts()
                .is_some_and(ts_binder::CanonicalSourceFileFacts::is_declaration_file)
        {
            return false;
        }

        let Some(block_id) = self
            .arena
            .get(declaration.node)
            .and_then(|node| node.parent)
        else {
            return false;
        };
        let block = child(declaration, block_id);
        let Ok(block_record) = owned_node(self.arena, self.bound, self.store, block) else {
            return false;
        };
        let NodeData::ModuleBlock(block_data) = &block_record.data else {
            return false;
        };
        let Some(module_id) = block_record.parent else {
            return false;
        };
        let module = child(block, module_id);
        let Ok(module_record) = owned_node(self.arena, self.bound, self.store, module) else {
            return false;
        };
        let NodeData::ModuleDeclaration(module_data) = &module_record.data else {
            return false;
        };
        let name = child(module, module_data.name);
        let Ok(name_record) = owned_node(self.arena, self.bound, self.store, name) else {
            return false;
        };

        block_record.kind == SyntaxKind::ModuleBlock
            && block_data
                .statements
                .nodes
                .iter()
                .filter(|candidate| **candidate == declaration.node)
                .count()
                == 1
            && module_record.kind == SyntaxKind::ModuleDeclaration
            && module_record.parent == Some(self.bound.source_file().node)
            && module_data.keyword == SyntaxKind::ModuleKeyword
            && module_data.body == Some(block.node)
            && name_record.kind == SyntaxKind::StringLiteral
            && name_record.parent == Some(module.node)
            && matches!(&name_record.data, NodeData::StringLiteral(_))
            && self
                .bound
                .symbol(module)
                .and_then(|module| self.store.get_merged_symbol(module))
                == Some(namespace)
            && self
                .bound
                .locals(module)
                .and_then(|locals| self.store.symbol_table(locals))
                .and_then(|locals| locals.get(owner.name()))
                .and_then(|local| self.store.get_merged_symbol(local))
                == Some(symbol)
            && exports.get(owner.name()).is_none()
    }

    fn type_alias(
        &mut self,
        declaration: NodeRef,
        namespace: SemanticSymbolId,
        symbol: SemanticSymbolId,
        parameters: &NodeList,
        annotation: NodeRef,
    ) -> Result<(), SourceCheckError> {
        let record = owned_node(self.arena, self.bound, self.store, declaration)?;
        let NodeData::TypeAliasDeclaration(alias) = &record.data else {
            return Err(Self::invalid(declaration, record.kind));
        };
        let annotation_record = owned_node(self.arena, self.bound, self.store, annotation)?;
        let name = self.identifier(declaration, child(declaration, alias.name))?;
        let symbol_record = self
            .store
            .symbol(symbol)
            .ok_or(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
            ))?;
        if record.kind != SyntaxKind::TypeAliasDeclaration
            || record.flags.0 != 0
            || alias.flow_node.is_some()
            || alias.local_symbol.is_some()
            || alias.next_container.is_some()
            || alias.symbol.is_some()
            || parameters.nodes.is_empty()
            || parameters.has_trailing_comma
            || parameters.range.start < record.range.start
            || parameters.range.end > annotation_record.range.start
            || symbol_record.flags() != SymbolFlags::TYPE_ALIAS
            || symbol_record.check_flags() != CheckFlags::NONE
            || symbol_record.name().as_utf8() != Some(name.as_str())
            || symbol_record.declarations() != Some(&[declaration])
            || symbol_record.value_declaration().is_some()
            || symbol_record.members().is_some()
            || symbol_record.exports().is_some()
            || symbol_record.export_symbol().is_some()
            || self
                .bound
                .symbol(declaration)
                .and_then(|bound_symbol| self.store.get_merged_symbol(bound_symbol))
                != Some(symbol)
            || !self.type_alias_owner(declaration, namespace, symbol)
        {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
            ));
        }

        let mut names = HashSet::with_capacity(parameters.nodes.len());
        let mut default_seen = false;
        for parameter in &parameters.nodes {
            let parameter = child(declaration, *parameter);
            let (_, has_default) = self.type_parameter(declaration, parameter, &mut names)?;
            if default_seen && !has_default {
                return Err(Self::invalid(parameter, SyntaxKind::TypeParameter));
            }
            default_seen |= has_default;
        }
        if self
            .bound
            .locals(declaration)
            .and_then(|locals| self.store.symbol_table(locals))
            .map_or(0, ts_binder::semantic::SymbolTable::len)
            != parameters.nodes.len()
        {
            return Err(Self::invalid(declaration, record.kind));
        }

        self.type_node(declaration, annotation)
    }

    fn type_parameter(
        &mut self,
        container: NodeRef,
        parameter: NodeRef,
        names: &mut HashSet<String>,
    ) -> Result<(SemanticSymbolId, bool), SourceCheckError> {
        let record = self.visit(container, parameter)?;
        let NodeData::TypeParameterDeclaration(data) = &record.data else {
            return Err(Self::invalid(parameter, record.kind));
        };
        if record.kind != SyntaxKind::TypeParameter
            || data.expression.is_some()
            || data.symbol.is_some()
            || data.modifiers.is_some()
        {
            return Err(Self::invalid(parameter, record.kind));
        }
        let name = self.identifier(parameter, child(parameter, data.name))?;
        if !names.insert(name.clone()) {
            return Err(Self::invalid(parameter, record.kind));
        }
        let symbol = self.local_symbol(container, parameter, &name, SymbolFlags::TYPE_PARAMETER)?;
        for annotation in [data.constraint, data.default_type].into_iter().flatten() {
            let annotation = child(parameter, annotation);
            self.annotations.push(annotation);
            self.type_node(parameter, annotation)?;
        }
        Ok((symbol, data.default_type.is_some()))
    }

    fn parameter(
        &mut self,
        container: NodeRef,
        parameter: NodeRef,
        index: usize,
        count: usize,
        optional_seen: &mut bool,
        names: &mut HashSet<String>,
    ) -> Result<SemanticSymbolId, SourceCheckError> {
        let record = self.visit(container, parameter)?;
        let NodeData::ParameterDeclaration(data) = &record.data else {
            return Err(Self::invalid(parameter, record.kind));
        };
        if record.kind != SyntaxKind::Parameter
            || data.initializer.is_some()
            || data.symbol.is_some()
            || data.modifiers.is_some()
            || data.facts != 0
        {
            return Err(Self::invalid(parameter, record.kind));
        }
        let name = self.identifier(parameter, child(parameter, data.name))?;
        if name == "this" || !names.insert(name.clone()) {
            return Err(Self::invalid(parameter, record.kind));
        }
        let symbol = self.local_symbol(
            container,
            parameter,
            &name,
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
        )?;
        if let Some(token) = data.dot_dot_dot_token {
            let token = child(parameter, token);
            let token_record = self.visit(parameter, token)?;
            if token_record.kind != SyntaxKind::DotDotDotToken
                || index + 1 != count
                || data.question_token.is_some()
            {
                return Err(Self::invalid(token, token_record.kind));
            }
        }
        if let Some(token) = data.question_token {
            let token = child(parameter, token);
            let token_record = self.visit(parameter, token)?;
            if token_record.kind != SyntaxKind::QuestionToken {
                return Err(Self::invalid(token, token_record.kind));
            }
            *optional_seen = true;
        } else if *optional_seen && data.dot_dot_dot_token.is_none() {
            return Err(Self::invalid(parameter, record.kind));
        }
        let annotation = data
            .type_
            .map(|annotation| child(parameter, annotation))
            .ok_or_else(|| Self::invalid(parameter, record.kind))?;
        self.annotations.push(annotation);
        self.type_node(parameter, annotation)?;
        Ok(symbol)
    }

    fn signature_parameters(
        &mut self,
        container: NodeRef,
        type_parameters: Option<&NodeList>,
        parameters: &NodeList,
    ) -> Result<DeferredAmbientSignatureParameters, SourceCheckError> {
        let record = owned_node(self.arena, self.bound, self.store, container)?;
        if parameters.has_trailing_comma
            || parameters.range.start < record.range.start
            || parameters.range.end > record.range.end
            || type_parameters.is_some_and(|list| {
                list.nodes.is_empty()
                    || list.has_trailing_comma
                    || list.range.start < record.range.start
                    || list.range.end > parameters.range.start
            })
        {
            return Err(Self::invalid(container, record.kind));
        }

        let mut type_parameter_names = HashSet::new();
        let mut type_parameter_symbols = Vec::new();
        let mut default_seen = false;
        for parameter in type_parameters.into_iter().flat_map(|list| &list.nodes) {
            let (symbol, has_default) = self.type_parameter(
                container,
                child(container, *parameter),
                &mut type_parameter_names,
            )?;
            if default_seen && !has_default {
                return Err(Self::invalid(
                    child(container, *parameter),
                    SyntaxKind::TypeParameter,
                ));
            }
            default_seen |= has_default;
            type_parameter_symbols.push(symbol);
        }

        let mut parameter_names = HashSet::new();
        let mut parameter_symbols = Vec::with_capacity(parameters.nodes.len());
        let mut optional_seen = false;
        for (index, parameter) in parameters.nodes.iter().enumerate() {
            parameter_symbols.push(self.parameter(
                container,
                child(container, *parameter),
                index,
                parameters.nodes.len(),
                &mut optional_seen,
                &mut parameter_names,
            )?);
        }
        let expected_locals = type_parameter_symbols.len() + parameter_symbols.len();
        if self
            .bound
            .locals(container)
            .and_then(|locals| self.store.symbol_table(locals))
            .map_or(0, ts_binder::semantic::SymbolTable::len)
            != expected_locals
        {
            return Err(Self::invalid(container, record.kind));
        }

        Ok(DeferredAmbientSignatureParameters {
            type_parameters: type_parameter_symbols,
            parameters: parameter_symbols,
            names: parameter_names,
        })
    }

    fn signature(
        &mut self,
        container: NodeRef,
        type_parameters: Option<&NodeList>,
        parameters: &NodeList,
        return_type: Option<ts_ast::NodeId>,
    ) -> Result<(Vec<SemanticSymbolId>, Vec<SemanticSymbolId>), SourceCheckError> {
        let record = owned_node(self.arena, self.bound, self.store, container)?;
        let DeferredAmbientSignatureParameters {
            type_parameters: type_parameter_symbols,
            parameters: parameter_symbols,
            names: parameter_names,
        } = self.signature_parameters(container, type_parameters, parameters)?;
        let return_type = return_type
            .map(|return_type| child(container, return_type))
            .ok_or_else(|| Self::invalid(container, record.kind))?;
        if let Some(NodeData::TypePredicateNode(predicate)) =
            self.arena.get(return_type.node).map(|node| &node.data)
        {
            let parameter_name = child(return_type, predicate.parameter_name);
            let Some(NodeData::Identifier(identifier)) =
                self.arena.get(parameter_name.node).map(|node| &node.data)
            else {
                return Err(Self::invalid(return_type, SyntaxKind::TypePredicate));
            };
            if predicate.asserts_modifier.is_some()
                || predicate.type_.is_none()
                || !parameter_names.contains(&identifier.text)
            {
                return Err(Self::invalid(return_type, SyntaxKind::TypePredicate));
            }
        }
        self.annotations.push(return_type);
        self.type_node(container, return_type)?;
        Ok((type_parameter_symbols, parameter_symbols))
    }

    fn signature_owner(
        &self,
        node: NodeRef,
        signature_name: InternalSymbolName,
    ) -> Result<(), SourceCheckError> {
        let symbol = declaration_symbol(self.bound, self.store, node, SymbolFlags::TYPE_LITERAL)?;
        let owner = self
            .store
            .symbol(symbol)
            .ok_or(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingDeclarationSymbol(node),
            ))?;
        let members = owner
            .members()
            .and_then(|members| self.store.symbol_table(members))
            .ok_or(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingDeclarationSymbol(node),
            ))?;
        let signature = members
            .get(signature_name.as_ref())
            .and_then(|signature| self.store.symbol(signature))
            .ok_or(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingDeclarationSymbol(node),
            ))?;
        if self.bound.symbol(node) != Some(symbol)
            || owner.flags() != SymbolFlags::TYPE_LITERAL
            || owner.check_flags() != CheckFlags::NONE
            || owner.name() != InternalSymbolName::Type.as_ref()
            || owner.declarations() != Some(&[node])
            || owner.value_declaration().is_some()
            || owner.exports().is_some()
            || owner.parent().is_some()
            || owner.export_symbol().is_some()
            || members.len() != 1
            || signature.flags() != SymbolFlags::SIGNATURE
            || signature.check_flags() != CheckFlags::NONE
            || signature.name() != signature_name.as_ref()
            || signature.declarations() != Some(&[node])
            || signature.value_declaration().is_some()
            || signature.members().is_some()
            || signature.exports().is_some()
            || signature.parent().is_some()
            || signature.export_symbol().is_some()
        {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingDeclarationSymbol(node),
            ));
        }
        Ok(())
    }

    fn type_literal_member_symbol(
        &self,
        container: NodeRef,
        declaration: NodeRef,
        name: ts_binder::EscapedNameRef<'_>,
        flags: SymbolFlags,
    ) -> Result<SemanticSymbolId, SourceCheckError> {
        let owner =
            declaration_symbol(self.bound, self.store, container, SymbolFlags::TYPE_LITERAL)?;
        let symbol = declaration_symbol(self.bound, self.store, declaration, flags)?;
        let record = self
            .store
            .symbol(symbol)
            .ok_or(SourceCheckError::Class(declaration))?;
        if record.flags() != flags
            || record.check_flags() != CheckFlags::NONE
                && record.check_flags() != CheckFlags::READONLY
            || record.name() != name
            || record.declarations().is_none_or(|declarations| {
                declarations.is_empty() || !declarations.contains(&declaration)
            })
            || record.members().is_some()
            || record.exports().is_some()
            || record.parent() != Some(owner)
            || record.export_symbol().is_some()
            || self
                .store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| self.store.symbol_table(members))
                .and_then(|members| members.get(name))
                != Some(symbol)
        {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
            ));
        }
        Ok(symbol)
    }

    fn type_node(&mut self, parent: NodeRef, node: NodeRef) -> Result<(), SourceCheckError> {
        let record = self.visit(parent, node)?;
        match &record.data {
            NodeData::Identifier(identifier) => {
                if record.kind != SyntaxKind::Identifier
                    || identifier.flow_node.is_some()
                    || identifier.text.is_empty()
                {
                    return Err(Self::invalid(node, record.kind));
                }
                return Ok(());
            }
            NodeData::ConstructorTypeNode(function) => {
                if function.full_signature.is_some()
                    || function.next_container.is_some()
                    || function.symbol.is_some()
                    || function.modifiers.is_some()
                {
                    return Err(Self::invalid(node, record.kind));
                }
                self.signature_owner(node, InternalSymbolName::New)?;
                self.signature(
                    node,
                    function.type_parameters.as_ref(),
                    &function.parameters,
                    function.type_,
                )?;
                return Ok(());
            }
            NodeData::FunctionTypeNode(function) => {
                if function.full_signature.is_some()
                    || function.next_container.is_some()
                    || function.symbol.is_some()
                    || function.modifiers.is_some()
                {
                    return Err(Self::invalid(node, record.kind));
                }
                self.signature_owner(node, InternalSymbolName::Call)?;
                self.signature(
                    node,
                    function.type_parameters.as_ref(),
                    &function.parameters,
                    function.type_,
                )?;
                return Ok(());
            }
            NodeData::TypeLiteralNode(literal) => {
                let symbol =
                    declaration_symbol(self.bound, self.store, node, SymbolFlags::TYPE_LITERAL)?;
                let owner = self
                    .store
                    .symbol(symbol)
                    .ok_or(SourceCheckError::Class(node))?;
                if literal.symbol.is_some()
                    || literal.members.has_trailing_comma
                    || owner.flags() != SymbolFlags::TYPE_LITERAL
                    || owner.check_flags() != CheckFlags::NONE
                    || owner.name() != InternalSymbolName::Type.as_ref()
                    || owner.declarations() != Some(&[node])
                    || owner.value_declaration().is_some()
                    || owner.exports().is_some()
                    || owner.parent().is_some()
                    || owner.export_symbol().is_some()
                {
                    return Err(Self::invalid(node, record.kind));
                }
                for member in &literal.members.nodes {
                    self.type_node(node, child(node, *member))?;
                }
                return Ok(());
            }
            NodeData::MethodSignatureDeclaration(method) => {
                if record.kind != SyntaxKind::MethodSignature
                    || method.full_signature.is_some()
                    || method.next_container.is_some()
                    || method.symbol.is_some()
                    || method.modifiers.is_some()
                {
                    return Err(Self::invalid(node, record.kind));
                }
                let name = self.identifier(node, child(node, method.name))?;
                let optional = if let Some(token) = method.postfix_token {
                    let token = child(node, token);
                    if self.visit(node, token)?.kind != SyntaxKind::QuestionToken {
                        return Err(Self::invalid(token, SyntaxKind::QuestionToken));
                    }
                    true
                } else {
                    false
                };
                let flags = SymbolFlags::METHOD
                    | if optional {
                        SymbolFlags::OPTIONAL
                    } else {
                        SymbolFlags::NONE
                    };
                self.type_literal_member_symbol(
                    parent,
                    node,
                    EscapedName::source(&name).as_ref(),
                    flags,
                )?;
                self.signature(
                    node,
                    method.type_parameters.as_ref(),
                    &method.parameters,
                    method.type_,
                )?;
                return Ok(());
            }
            NodeData::PropertyDeclaration(property) => {
                if record.kind != SyntaxKind::PropertyDeclaration
                    || property.initializer.is_some()
                    || property.symbol.is_some()
                    || property.facts != 0
                {
                    return Err(Self::invalid(node, record.kind));
                }
                if let Some(modifiers) = &property.modifiers {
                    if modifiers.flags.0 != 0 || modifiers.list.has_trailing_comma {
                        return Err(Self::invalid(node, record.kind));
                    }
                    for modifier in &modifiers.list.nodes {
                        let modifier = child(node, *modifier);
                        if self.visit(node, modifier)?.kind != SyntaxKind::ReadonlyKeyword {
                            return Err(Self::invalid(modifier, SyntaxKind::ReadonlyKeyword));
                        }
                    }
                }
                let name = self.identifier(node, child(node, property.name))?;
                let optional = if let Some(token) = property.postfix_token {
                    let token = child(node, token);
                    if self.visit(node, token)?.kind != SyntaxKind::QuestionToken {
                        return Err(Self::invalid(token, SyntaxKind::QuestionToken));
                    }
                    true
                } else {
                    false
                };
                let flags = SymbolFlags::PROPERTY
                    | if optional {
                        SymbolFlags::OPTIONAL
                    } else {
                        SymbolFlags::NONE
                    };
                self.type_literal_member_symbol(
                    parent,
                    node,
                    EscapedName::source(&name).as_ref(),
                    flags,
                )?;
                let annotation = property
                    .type_
                    .map(|annotation| child(node, annotation))
                    .ok_or_else(|| Self::invalid(node, record.kind))?;
                self.annotations.push(annotation);
                self.type_node(node, annotation)?;
                return Ok(());
            }
            NodeData::IndexSignatureDeclaration(signature) => {
                if record.kind != SyntaxKind::IndexSignature
                    || signature.full_signature.is_some()
                    || signature.next_container.is_some()
                    || signature.symbol.is_some()
                    || signature.type_parameters.is_some()
                    || signature.modifiers.is_some()
                {
                    return Err(Self::invalid(node, record.kind));
                }
                self.type_literal_member_symbol(
                    parent,
                    node,
                    InternalSymbolName::Index.as_ref(),
                    SymbolFlags::SIGNATURE,
                )?;
                self.signature(node, None, &signature.parameters, Some(signature.type_))?;
                return Ok(());
            }
            NodeData::MappedTypeNode(mapped) => {
                if mapped.next_container.is_some() || mapped.symbol.is_some() {
                    return Err(Self::invalid(node, record.kind));
                }
                if let Some(token) = mapped.readonly_token {
                    self.type_node(node, child(node, token))?;
                }
                self.type_parameter(
                    node,
                    child(node, mapped.type_parameter),
                    &mut HashSet::new(),
                )?;
                for nested in [mapped.name_type, mapped.question_token, mapped.type_]
                    .into_iter()
                    .flatten()
                {
                    self.type_node(node, child(node, nested))?;
                }
                if let Some(members) = &mapped.members {
                    if members.has_trailing_comma {
                        return Err(Self::invalid(node, record.kind));
                    }
                    for member in &members.nodes {
                        self.type_node(node, child(node, *member))?;
                    }
                }
                return Ok(());
            }
            NodeData::InferTypeNode(infer) => {
                if record.kind != SyntaxKind::InferType {
                    return Err(Self::invalid(node, record.kind));
                }
                let parameter = child(node, infer.type_parameter);
                let parameter_record = self.visit(node, parameter)?;
                let NodeData::TypeParameterDeclaration(data) = &parameter_record.data else {
                    return Err(Self::invalid(parameter, parameter_record.kind));
                };
                if parameter_record.kind != SyntaxKind::TypeParameter
                    || data.default_type.is_some()
                    || data.expression.is_some()
                    || data.modifiers.is_some()
                    || data.symbol.is_some()
                {
                    return Err(Self::invalid(parameter, parameter_record.kind));
                }
                let name = self.identifier(parameter, child(parameter, data.name))?;
                let mut current = node;
                let container = loop {
                    let current_record = owned_node(self.arena, self.bound, self.store, current)?;
                    let Some(parent) = current_record.parent else {
                        return Err(Self::invalid(node, record.kind));
                    };
                    let parent = child(current, parent);
                    let parent_record = owned_node(self.arena, self.bound, self.store, parent)?;
                    if let NodeData::ConditionalTypeNode(conditional) = &parent_record.data
                        && conditional.extends_type == current.node
                    {
                        break parent;
                    }
                    current = parent;
                };
                self.local_symbol(container, parameter, &name, SymbolFlags::TYPE_PARAMETER)?;
                if let Some(constraint) = data.constraint {
                    self.type_node(parameter, child(parameter, constraint))?;
                }
                return Ok(());
            }
            NodeData::TypeReferenceNode(reference) => {
                if reference.type_arguments.as_ref().is_some_and(|arguments| {
                    arguments.nodes.is_empty() || arguments.has_trailing_comma
                }) {
                    return Err(Self::invalid(node, record.kind));
                }
            }
            _ => {}
        }

        let type_syntax = record.kind.is_keyword_type()
            || (record.kind as u16) >= (SyntaxKind::FIRST_TYPE_NODE as u16)
                && (record.kind as u16) <= (SyntaxKind::LAST_TYPE_NODE as u16)
            || matches!(
                record.kind,
                SyntaxKind::QualifiedName
                    | SyntaxKind::ComputedPropertyName
                    | SyntaxKind::PropertySignature
                    | SyntaxKind::StringLiteral
                    | SyntaxKind::NumericLiteral
                    | SyntaxKind::BigIntLiteral
                    | SyntaxKind::NoSubstitutionTemplateLiteral
                    | SyntaxKind::TemplateHead
                    | SyntaxKind::TemplateMiddle
                    | SyntaxKind::TemplateTail
                    | SyntaxKind::QuestionToken
                    | SyntaxKind::DotDotDotToken
                    | SyntaxKind::ReadonlyKeyword
                    | SyntaxKind::PlusToken
                    | SyntaxKind::MinusToken
                    | SyntaxKind::TrueKeyword
                    | SyntaxKind::FalseKeyword
                    | SyntaxKind::NullKeyword
                    | SyntaxKind::PrefixUnaryExpression
                    | SyntaxKind::PropertyAccessExpression
                    | SyntaxKind::ElementAccessExpression
            );
        if !type_syntax {
            return Err(Self::invalid(node, record.kind));
        }
        let mut children = Vec::new();
        record.for_each_child(|nested| children.push(child(node, nested)));
        for nested in children {
            self.type_node(node, nested)?;
        }
        Ok(())
    }
}

fn plan_deferred_ambient_function(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<SourceNamespaceMemberPlan, SourceCheckError> {
    let record = owned_node(arena, bound, store, declaration)?;
    let NodeData::FunctionDeclaration(function) = &record.data else {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::FunctionDeclaration,
        ));
    };
    if store
        .value_symbol_links(symbol)
        .is_some_and(|links| links != &ValueSymbolLinks::default())
        || store.source_callable_type_for_owner(symbol).is_some()
        || store
            .source_callable_type_for_declaration(declaration)
            .is_some()
    {
        return Err(SourceCheckError::Function(
            SourceFunctionInvariant::Callable(declaration),
        ));
    }

    let mut validator = DeferredAmbientFunctionValidator::new(arena, bound, store);
    let (type_parameters, parameters) = validator.signature(
        declaration,
        function.type_parameters.as_ref(),
        &function.parameters,
        function.type_,
    )?;
    Ok(SourceNamespaceMemberPlan::DeferredAmbientFunction {
        declaration,
        symbol,
        type_parameters,
        parameters,
        annotations: validator.annotations,
    })
}

fn strict_namespace_arguments_variable(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    body: NodeRef,
    statements: &NodeList,
) -> Result<Option<(NodeRef, NodeRef, NodeRef)>, SourceCheckError> {
    let [statement_id] = statements.nodes.as_slice() else {
        return Ok(None);
    };
    let statement = child(body, *statement_id);
    let statement_record = owned_node(arena, bound, store, statement)?;
    let NodeData::VariableStatement(variable_statement) = &statement_record.data else {
        return Ok(None);
    };
    if statement_record.kind != SyntaxKind::VariableStatement
        || statement_record.flags.0 != 0
        || statement_record.parent != Some(body.node)
        || variable_statement.flow_node.is_some()
        || variable_statement.facts != 0
        || variable_statement.modifiers.is_some()
    {
        return Ok(None);
    }

    let list = child(statement, variable_statement.declaration_list);
    let list_record = owned_node(arena, bound, store, list)?;
    let NodeData::VariableDeclarationList(declarations) = &list_record.data else {
        return Ok(None);
    };
    let [variable_id] = declarations.declarations.nodes.as_slice() else {
        return Ok(None);
    };
    if list_record.kind != SyntaxKind::VariableDeclarationList
        || list_record.flags.0 != 0
        || list_record.parent != Some(statement.node)
        || declarations.declarations.has_trailing_comma
        || declarations.facts != 0
    {
        return Ok(None);
    }

    let variable = child(list, *variable_id);
    let variable_record = owned_node(arena, bound, store, variable)?;
    let NodeData::VariableDeclaration(declaration) = &variable_record.data else {
        return Ok(None);
    };
    let Some(initializer) = declaration.initializer else {
        return Ok(None);
    };
    if variable_record.kind != SyntaxKind::VariableDeclaration
        || variable_record.flags.0 != 0
        || variable_record.parent != Some(list.node)
        || declaration.exclamation_token.is_some()
        || declaration.local_symbol.is_some()
        || declaration.symbol.is_some()
        || declaration.type_.is_some()
        || declaration.facts != 0
    {
        return Ok(None);
    }

    Ok(Some((
        variable,
        child(variable, declaration.name),
        child(variable, initializer),
    )))
}

fn diagnosed_strict_namespace_arguments_body(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    function: NodeRef,
    body: NodeRef,
    statements: &NodeList,
) -> Result<bool, SourceCheckError> {
    if !bound
        .source_facts()
        .is_some_and(ts_binder::CanonicalSourceFileFacts::is_always_strict)
    {
        return Ok(false);
    }
    let Some((variable, name, initializer)) =
        strict_namespace_arguments_variable(arena, bound, store, body, statements)?
    else {
        return Ok(false);
    };

    let name_record = owned_node(arena, bound, store, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Ok(false);
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(variable.node)
        || identifier.flow_node.is_some()
        || identifier.text != "arguments"
        || !bound
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.node == name && diagnostic.diagnostic.code() == 1100)
    {
        return Ok(false);
    }

    let initializer_record = owned_node(arena, bound, store, initializer)?;
    let NodeData::ArrayLiteralExpression(array) = &initializer_record.data else {
        return Ok(false);
    };
    if initializer_record.kind != SyntaxKind::ArrayLiteralExpression
        || initializer_record.flags.0 != 0
        || initializer_record.parent != Some(variable.node)
        || !array.elements.nodes.is_empty()
        || array.elements.has_trailing_comma
        || array.facts != 0
    {
        return Ok(false);
    }

    let Some(symbol) = bound.symbol(variable) else {
        return Ok(false);
    };
    let Some(record) = store.symbol(symbol) else {
        return Ok(false);
    };
    Ok(record.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE
        && record.check_flags() == CheckFlags::NONE
        && record.name().as_utf8() == Some("arguments")
        && record.declarations() == Some(&[variable])
        && record.value_declaration() == Some(variable)
        && bound.container(variable) == Some(function)
        && bound
            .locals(function)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source("arguments"))
            == Some(symbol))
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
        if annotation_record.flags.0 != 0 || annotation_record.parent != Some(declaration.node) {
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
            || block.statements.has_trailing_comma
            || (!block.statements.nodes.is_empty()
                && !diagnosed_strict_namespace_arguments_body(
                    arena,
                    bound,
                    store,
                    declaration,
                    body,
                    &block.statements,
                )?)
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
        || !(exported || ambient_declaration)
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
        || function.facts != 0
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
    let declarations = function_record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
        .ok_or(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ))?;
    let overloaded = declarations.len() > 1;
    if function_record.flags() != SymbolFlags::FUNCTION
        || function_record.check_flags() != CheckFlags::NONE
        || function_record.value_declaration() != declarations.first().copied()
        || function_record.name().as_utf8() != Some(identifier.text.as_str())
        || function_record.members().is_some()
        || function_record.exports().is_some()
        || function_record.export_symbol().is_some()
        || store.get_parent_of_symbol(symbol) != Some(owner)
        || store.get_merged_symbol(local) != Some(local)
        || local_record.flags() != SymbolFlags::EXPORT_VALUE
        || local_record.check_flags() != CheckFlags::NONE
        || local_record.declarations() != Some(declarations)
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
    if overloaded {
        if !ambient_declaration
            || declarations.iter().any(|candidate| {
                let Some(candidate_record) = arena.get(candidate.node) else {
                    return true;
                };
                let NodeData::FunctionDeclaration(candidate_function) = &candidate_record.data
                else {
                    return true;
                };
                let candidate_name = candidate_function
                    .name
                    .and_then(|name| arena.get(name))
                    .and_then(|name| match &name.data {
                        NodeData::Identifier(name) => Some(name.text.as_str()),
                        _ => None,
                    });
                !candidate.is_for(declaration.arena, declaration.file)
                    || candidate_record.kind != SyntaxKind::FunctionDeclaration
                    || candidate_record.parent != record.parent
                    || candidate_name != Some(identifier.text.as_str())
                    || bound.symbol(*candidate) != Some(symbol)
                    || bound.local_symbol(*candidate) != Some(local)
            })
        {
            return Err(unsupported(
                declaration,
                record.kind,
                SourceSyntaxRole::FunctionDeclaration,
            ));
        }
        let overload = source_overloads::plan_source_namespace_ambient_overload_group(
            store,
            &host,
            (namespace, owner),
            symbol,
            declarations,
        )
        .map_err(|error| namespace_overload_error(declaration, error))?;
        let planned = overload
            .declarations
            .iter()
            .find(|planned| planned.declaration == declaration)
            .ok_or(SourceCheckError::Function(
                SourceFunctionInvariant::Callable(declaration),
            ))?;
        let deferred = plan_deferred_ambient_function(arena, bound, store, declaration, symbol)?;
        let SourceNamespaceMemberPlan::DeferredAmbientFunction {
            type_parameters,
            parameters,
            annotations,
            ..
        } = &deferred
        else {
            unreachable!("ambient function validation produces a deferred declaration")
        };
        if !type_parameters.iter().copied().eq(planned
            .type_parameters
            .iter()
            .map(|parameter| parameter.symbol))
            || !parameters
                .iter()
                .copied()
                .eq(planned.parameters.iter().map(|parameter| parameter.symbol))
            || !annotations.contains(&planned.return_type)
            || !overload
                .annotations()
                .all(|annotation| host.node(annotation).is_some())
        {
            return Err(SourceCheckError::Function(
                SourceFunctionInvariant::Callable(declaration),
            ));
        }
        return Ok(deferred);
    }

    if ambient_declaration
        && function.type_parameters.is_some()
        && (function
            .type_
            .and_then(|annotation| arena.get(annotation))
            .is_some_and(|annotation| annotation.kind == SyntaxKind::TypePredicate)
            || function.parameters.nodes.iter().any(|parameter| {
                arena
                    .get(*parameter)
                    .and_then(|record| match &record.data {
                        NodeData::ParameterDeclaration(parameter) => parameter.type_,
                        _ => None,
                    })
                    .and_then(|annotation| arena.get(annotation))
                    .is_some_and(|annotation| {
                        matches!(
                            annotation.kind,
                            SyntaxKind::ConstructorType | SyntaxKind::FunctionType
                        )
                    })
            }))
    {
        return plan_deferred_ambient_function(arena, bound, store, declaration, symbol);
    }

    let array_targets = store
        .source_callable_type_for_owner(symbol)
        .and_then(|type_| store.source_callable_provenance(type_))
        .and_then(|provenance| provenance.array_targets);
    let callable = match source_callables::plan_source_callable(
        store,
        &host,
        declaration,
        symbol,
        array_targets,
    ) {
        Ok(callable) => callable,
        Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::GenericSignature(_)
            | SourceCallableUnsupported::TypePredicate(_),
        )) if ambient_declaration && function.type_parameters.is_some() => {
            return plan_deferred_ambient_function(arena, bound, store, declaration, symbol);
        }
        Err(error) => return Err(namespace_callable_error(declaration, error)),
    };
    if callable.owner_parent != Some(owner)
        || callable.export_local != Some(local)
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
    target: Option<SemanticSymbolId>,
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
        || target.is_some_and(|target| store.get_merged_symbol(target) != Some(target))
    {
        return Err(SourceCheckError::Import(declaration));
    }
    Ok(SourceNamespaceImportPlan {
        declaration,
        name_text: identifier.text.clone(),
        symbol,
        reference,
        ambient_target: target,
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
    let Some(clause) = import.import_clause else {
        if reference_record.kind != SyntaxKind::StringLiteral
            || reference_record.flags.0 != 0
            || !matches!(
                &reference_record.data,
                NodeData::StringLiteral(literal)
                    if literal.token_flags.0 == 0 && !literal.text.is_empty()
            )
            || bound.symbol(declaration).is_some()
        {
            return Err(unsupported(
                declaration,
                record.kind,
                SourceSyntaxRole::Statement,
            ));
        }
        return Ok(Vec::new());
    };
    let module = match ambient_module_import_target(arena, bound, store, reference) {
        Ok(module) => Some(module),
        Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Import(node)))
            if node == reference =>
        {
            None
        }
        Err(error) => return Err(error),
    };
    let exports = module
        .map(|module| {
            store
                .symbol(module)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| store.symbol_table(exports))
                .ok_or(SourceCheckError::Import(declaration))
        })
        .transpose()?;

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
                    .map(|exports| {
                        exports
                            .get_source(&imported_name.text)
                            .and_then(|symbol| store.get_merged_symbol(symbol))
                            .ok_or(SourceCheckError::Unsupported(
                                UnsupportedSourceSyntax::Import(specifier),
                            ))
                    })
                    .transpose()?;
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

#[allow(clippy::too_many_lines)] // Every local export keeps its exact binder-owned alias identity.
fn plan_ambient_module_reexport(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: (NodeRef, SemanticSymbolId),
    declaration: NodeRef,
) -> Result<Vec<SourceNamespaceImportPlan>, SourceCheckError> {
    let (namespace, owner) = namespace;
    let record = owned_node(arena, bound, store, declaration)?;
    let NodeData::ExportDeclaration(export) = &record.data else {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::ExportDeclaration,
        ));
    };
    if record.kind != SyntaxKind::ExportDeclaration
        || record.flags.0 != 0
        || export.attributes.is_some()
        || export.flow_node.is_some()
        || export.symbol.is_some()
        || export.facts != 0
        || export.modifiers.is_some()
    {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::ExportDeclaration,
        ));
    }
    let clause = export
        .export_clause
        .map(|clause| child(declaration, clause))
        .ok_or_else(|| {
            unsupported(
                declaration,
                SyntaxKind::ExportDeclaration,
                SourceSyntaxRole::ExportDeclaration,
            )
        })?;
    let clause_record = owned_node(arena, bound, store, clause)?;
    let NodeData::NamedExports(named) = &clause_record.data else {
        return Err(unsupported(
            clause,
            clause_record.kind,
            SourceSyntaxRole::ExportClause,
        ));
    };
    if clause_record.kind != SyntaxKind::NamedExports
        || clause_record.flags.0 != 0
        || clause_record.parent != Some(declaration.node)
        || named.facts != 0
        || named.elements.has_trailing_comma
        || named.elements.nodes.is_empty()
    {
        return Err(unsupported(
            clause,
            clause_record.kind,
            SourceSyntaxRole::ExportClause,
        ));
    }

    let reference = export
        .module_specifier
        .map(|specifier| child(declaration, specifier));
    let module = if let Some(reference) = reference {
        match ambient_module_import_target(arena, bound, store, reference) {
            Ok(module) => Some(module),
            Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Import(node)))
                if node == reference =>
            {
                None
            }
            Err(error) => return Err(error),
        }
    } else {
        None
    };
    let exports = store
        .symbol(owner)
        .and_then(ts_binder::semantic::Symbol::exports)
        .and_then(|exports| store.symbol_table(exports))
        .ok_or(SourceCheckError::Import(declaration))?;
    let mut aliases = HashSet::with_capacity(named.elements.nodes.len());
    let mut planned = Vec::with_capacity(named.elements.nodes.len());
    for &binding in &named.elements.nodes {
        let binding = child(clause, binding);
        let binding_record = owned_node(arena, bound, store, binding)?;
        let NodeData::ExportSpecifier(specifier) = &binding_record.data else {
            return Err(unsupported(
                binding,
                binding_record.kind,
                SourceSyntaxRole::ExportClause,
            ));
        };
        if binding_record.kind != SyntaxKind::ExportSpecifier
            || binding_record.flags.0 != 0
            || binding_record.parent != Some(clause.node)
            || specifier.local_symbol.is_some()
            || specifier.symbol.is_some()
            || specifier.facts != 0
        {
            return Err(unsupported(
                binding,
                binding_record.kind,
                SourceSyntaxRole::ExportClause,
            ));
        }

        let imported_name = child(binding, specifier.property_name.unwrap_or(specifier.name));
        let imported_record = owned_node(arena, bound, store, imported_name)?;
        let NodeData::Identifier(imported) = &imported_record.data else {
            return Err(unsupported(
                imported_name,
                imported_record.kind,
                SourceSyntaxRole::ExportClause,
            ));
        };
        let exported_name = child(binding, specifier.name);
        let exported_record = owned_node(arena, bound, store, exported_name)?;
        let NodeData::Identifier(exported) = &exported_record.data else {
            return Err(unsupported(
                exported_name,
                exported_record.kind,
                SourceSyntaxRole::ExportClause,
            ));
        };
        if imported_record.kind != SyntaxKind::Identifier
            || imported_record.flags.0 != 0
            || imported_record.parent != Some(binding.node)
            || imported.flow_node.is_some()
            || imported.text.is_empty()
            || exported_record.kind != SyntaxKind::Identifier
            || exported_record.flags.0 != 0
            || exported_record.parent != Some(binding.node)
            || exported.flow_node.is_some()
            || exported.text.is_empty()
        {
            return Err(SourceCheckError::Import(binding));
        }

        let symbol = declaration_symbol(bound, store, binding, SymbolFlags::ALIAS)?;
        let alias = store
            .symbol(symbol)
            .ok_or(SourceCheckError::Import(binding))?;
        if alias.flags() != SymbolFlags::ALIAS
            || alias.check_flags() != CheckFlags::NONE
            || alias.declarations() != Some(&[binding])
            || alias.value_declaration().is_some()
            || alias.members().is_some()
            || alias.exports().is_some()
            || alias.export_symbol().is_some()
            || alias.name().as_utf8() != Some(exported.text.as_str())
            || store.get_parent_of_symbol(symbol) != Some(owner)
            || exports
                .get_source(&exported.text)
                .and_then(|candidate| store.get_merged_symbol(candidate))
                != Some(symbol)
            || !aliases.insert(symbol)
        {
            return Err(SourceCheckError::Import(binding));
        }

        let target = match (reference, module) {
            (None, _) => bound
                .locals(namespace)
                .and_then(|locals| store.symbol_table(locals))
                .and_then(|locals| locals.get_source(&imported.text))
                .and_then(|target| store.get_merged_symbol(target))
                .map(|target| {
                    store
                        .symbol(target)
                        .and_then(ts_binder::semantic::Symbol::export_symbol)
                        .unwrap_or(target)
                })
                .and_then(|target| store.get_merged_symbol(target))
                .map(Some)
                .ok_or(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Import(binding),
                ))?,
            (Some(_), Some(module)) => store
                .symbol(module)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| store.symbol_table(exports))
                .and_then(|exports| exports.get_source(&imported.text))
                .and_then(|target| store.get_merged_symbol(target))
                .map(Some)
                .ok_or(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Import(binding),
                ))?,
            (Some(_), None) => None,
        };
        planned.push(SourceNamespaceImportPlan {
            declaration: binding,
            name_text: exported.text.clone(),
            symbol,
            reference: reference.unwrap_or(imported_name),
            ambient_target: target,
            type_only: export.is_type_only || specifier.is_type_only,
        });
    }
    Ok(planned)
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

#[allow(clippy::too_many_arguments)] // Class heritage must retain its namespace and prior locals.
fn plan_namespace_class_heritage(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: (NodeRef, SemanticSymbolId),
    declaration: NodeRef,
    clauses: &ts_ast::NodeList,
    prior_class_plans: &[SourceNamespaceClassPlan],
    variables: &[SourceNamespaceImplicitVariablePlan],
) -> Result<SourceNamespaceClassHeritagePlan, SourceCheckError> {
    let (namespace, owner) = namespace;
    let unsupported_heritage =
        |node: NodeRef, kind: SyntaxKind| unsupported(node, kind, SourceSyntaxRole::Statement);
    let [clause_id] = clauses.nodes.as_slice() else {
        return Err(unsupported_heritage(
            declaration,
            SyntaxKind::ClassDeclaration,
        ));
    };
    let clause = child(declaration, *clause_id);
    let clause_record = owned_node(arena, bound, store, clause)?;
    let NodeData::HeritageClause(heritage) = &clause_record.data else {
        return Err(unsupported_heritage(clause, clause_record.kind));
    };
    let [base_id] = heritage.types.nodes.as_slice() else {
        return Err(unsupported_heritage(clause, clause_record.kind));
    };
    if clauses.has_trailing_comma
        || clause_record.kind != SyntaxKind::HeritageClause
        || clause_record.flags.0 != 0
        || clause_record.parent != Some(declaration.node)
        || heritage.token != SyntaxKind::ExtendsKeyword
        || heritage.facts != 0
        || heritage.types.has_trailing_comma
    {
        return Err(unsupported_heritage(clause, clause_record.kind));
    }

    let base = child(clause, *base_id);
    let base_record = owned_node(arena, bound, store, base)?;
    let NodeData::ExpressionWithTypeArguments(target) = &base_record.data else {
        return Err(unsupported_heritage(base, base_record.kind));
    };
    if base_record.kind != SyntaxKind::ExpressionWithTypeArguments
        || base_record.flags.0 != 0
        || base_record.parent != Some(clause.node)
        || target.type_arguments.is_some()
        || target.facts != 0
    {
        return Err(unsupported_heritage(base, base_record.kind));
    }

    let expression = child(base, target.expression);
    let expression_record = owned_node(arena, bound, store, expression)?;
    if expression_record.flags.0 != 0 || expression_record.parent != Some(base.node) {
        return Err(unsupported_heritage(expression, expression_record.kind));
    }
    match &expression_record.data {
        NodeData::PropertyAccessExpression(_) | NodeData::QualifiedName(_) => {
            let (receiver_id, property_id) = match &expression_record.data {
                NodeData::PropertyAccessExpression(access)
                    if expression_record.kind == SyntaxKind::PropertyAccessExpression
                        && access.flow_node.is_none()
                        && access.question_dot_token.is_none()
                        && access.facts == 0 =>
                {
                    (access.expression, access.name)
                }
                NodeData::QualifiedName(qualified)
                    if expression_record.kind == SyntaxKind::QualifiedName
                        && qualified.flow_node.is_none()
                        && qualified.facts == 0 =>
                {
                    (qualified.left, qualified.right)
                }
                _ => return Err(unsupported_heritage(expression, expression_record.kind)),
            };
            let receiver = child(expression, receiver_id);
            let receiver_record = owned_node(arena, bound, store, receiver)?;
            let NodeData::Identifier(receiver_name) = &receiver_record.data else {
                return Err(unsupported_heritage(receiver, receiver_record.kind));
            };
            let property = child(expression, property_id);
            let property_record = owned_node(arena, bound, store, property)?;
            let NodeData::Identifier(property_name) = &property_record.data else {
                return Err(unsupported_heritage(property, property_record.kind));
            };
            let namespace_record = owned_node(arena, bound, store, namespace)?;
            let NodeData::ModuleDeclaration(namespace_data) = &namespace_record.data else {
                return Err(unsupported_heritage(namespace, namespace_record.kind));
            };
            let namespace_name = child(namespace, namespace_data.name);
            let namespace_name_record = owned_node(arena, bound, store, namespace_name)?;
            let NodeData::Identifier(namespace_identifier) = &namespace_name_record.data else {
                return Err(unsupported_heritage(
                    namespace_name,
                    namespace_name_record.kind,
                ));
            };
            let private_class = prior_class_plans.iter().find(|class| {
                store
                    .symbol(class.symbol)
                    .and_then(|symbol| symbol.name().as_utf8())
                    == Some(property_name.text.as_str())
            });
            let Some(private_class) = private_class else {
                return Err(unsupported_heritage(property, property_record.kind));
            };
            if receiver_record.kind != SyntaxKind::Identifier
                || receiver_record.flags.0 != 0
                || receiver_record.parent != Some(expression.node)
                || receiver_record.range.start < expression_record.range.start
                || receiver_name.flow_node.is_some()
                || receiver_name.text != namespace_identifier.text
                || property_record.kind != SyntaxKind::Identifier
                || property_record.flags.0 != 0
                || property_record.parent != Some(expression.node)
                || property_record.range.start < receiver_record.range.end
                || property_record.range.end > expression_record.range.end
                || property_name.flow_node.is_some()
                || namespace_name_record.kind != SyntaxKind::Identifier
                || namespace_name_record.parent != Some(namespace.node)
                || store
                    .symbol(owner)
                    .and_then(|symbol| symbol.name().as_utf8())
                    != Some(receiver_name.text.as_str())
                || bound
                    .locals(namespace)
                    .and_then(|locals| store.symbol_table(locals))
                    .and_then(|locals| locals.get_source(&property_name.text))
                    != Some(private_class.symbol)
                || store
                    .symbol(owner)
                    .and_then(ts_binder::semantic::Symbol::exports)
                    .and_then(|exports| store.symbol_table(exports))
                    .is_some_and(|exports| exports.get_source(&property_name.text).is_some())
                || store.symbol_node_links(receiver).is_some_and(|links| {
                    links.resolved_symbol.is_some_and(|symbol| symbol != owner)
                })
            {
                return Err(unsupported_heritage(expression, expression_record.kind));
            }
            Ok(SourceNamespaceClassHeritagePlan::MissingPrivateExport {
                property,
                property_name: property_name.text.clone(),
                namespace_name: receiver_name.text.clone(),
            })
        }
        NodeData::Identifier(identifier)
            if expression_record.kind == SyntaxKind::Identifier
                && identifier.flow_node.is_none()
                && !identifier.text.is_empty() =>
        {
            let Some(variable) = variables.iter().find(|variable| {
                variable.name == identifier.text && variable.initializer.is_some()
            }) else {
                return Err(unsupported_heritage(expression, expression_record.kind));
            };
            if store
                .symbol(variable.symbol)
                .is_none_or(|record| record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE)
                || bound
                    .locals(namespace)
                    .and_then(|locals| store.symbol_table(locals))
                    .and_then(|locals| locals.get_source(&identifier.text))
                    != Some(variable.symbol)
                || store.symbol_node_links(expression).is_some_and(|links| {
                    links
                        .resolved_symbol
                        .is_some_and(|symbol| symbol != variable.symbol)
                })
            {
                return Err(unsupported_heritage(expression, expression_record.kind));
            }
            Ok(SourceNamespaceClassHeritagePlan::NonConstructorVariable {
                expression,
                symbol: variable.symbol,
            })
        }
        _ => Err(unsupported_heritage(expression, expression_record.kind)),
    }
}

#[allow(clippy::too_many_arguments)] // Class members retain their owner, export side, and flags.
fn deferred_ambient_class_member_symbol(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    class: (NodeRef, SemanticSymbolId),
    declaration: NodeRef,
    name: ts_binder::EscapedNameRef<'_>,
    flags: SymbolFlags,
    is_static: bool,
) -> Result<SemanticSymbolId, SourceCheckError> {
    let (class_declaration, owner) = class;
    let symbol = declaration_symbol(bound, store, declaration, flags)?;
    let record = store
        .symbol(symbol)
        .ok_or(SourceCheckError::Class(declaration))?;
    let owner_record = store
        .symbol(owner)
        .ok_or(SourceCheckError::Class(class_declaration))?;
    let table = if is_static {
        owner_record.exports()
    } else {
        owner_record.members()
    }
    .and_then(|table| store.symbol_table(table));
    let Some(declarations) = record.declarations() else {
        return Err(SourceCheckError::Class(declaration));
    };
    if record.flags() != flags
        || record.check_flags() != CheckFlags::NONE && record.check_flags() != CheckFlags::READONLY
        || record.name() != name
        || declarations.is_empty()
        || !declarations.contains(&declaration)
        || declarations.iter().any(|candidate| {
            !candidate.is_for(class_declaration.arena, class_declaration.file)
                || arena
                    .get(candidate.node)
                    .is_none_or(|candidate| candidate.parent != Some(class_declaration.node))
                || bound.symbol(*candidate) != Some(symbol)
        })
        || flags == SymbolFlags::CONSTRUCTOR && record.value_declaration().is_some()
        || flags != SymbolFlags::CONSTRUCTOR && record.value_declaration().is_none()
        || record.members().is_some()
        || record.exports().is_some()
        || record.parent() != Some(owner)
        || record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || table.and_then(|table| table.get(name)) != Some(symbol)
    {
        return Err(SourceCheckError::Provenance(
            SourceCheckProvenanceError::MissingDeclarationSymbol(declaration),
        ));
    }
    Ok(symbol)
}

fn deferred_ambient_class_modifiers(
    validator: &mut DeferredAmbientFunctionValidator<'_>,
    declaration: NodeRef,
    modifiers: Option<&ModifierList>,
) -> Result<(bool, bool), SourceCheckError> {
    let Some(modifiers) = modifiers else {
        return Ok((false, false));
    };
    if modifiers.flags.0 != 0 || modifiers.list.has_trailing_comma {
        return Err(SourceCheckError::Class(declaration));
    }
    let mut readonly = false;
    let mut is_static = false;
    let mut visibility = false;
    for modifier in &modifiers.list.nodes {
        let modifier = child(declaration, *modifier);
        let record = validator.visit(declaration, modifier)?;
        match record.kind {
            SyntaxKind::ReadonlyKeyword if !readonly => readonly = true,
            SyntaxKind::StaticKeyword if !is_static => is_static = true,
            SyntaxKind::PublicKeyword
            | SyntaxKind::ProtectedKeyword
            | SyntaxKind::PrivateKeyword
                if !visibility =>
            {
                visibility = true;
            }
            SyntaxKind::AbstractKeyword => {}
            _ => return Err(SourceCheckError::Class(modifier)),
        }
    }
    Ok((readonly, is_static))
}

fn deferred_ambient_class_type_parameters(
    validator: &mut DeferredAmbientFunctionValidator<'_>,
    declaration: NodeRef,
    owner: SemanticSymbolId,
    parameters: Option<&NodeList>,
) -> Result<Vec<SemanticSymbolId>, SourceCheckError> {
    let Some(parameters) = parameters else {
        return Ok(Vec::new());
    };
    let class_record = owned_node(
        validator.arena,
        validator.bound,
        validator.store,
        declaration,
    )?;
    if parameters.nodes.is_empty()
        || parameters.has_trailing_comma
        || parameters.range.start < class_record.range.start
        || parameters.range.end > class_record.range.end
    {
        return Err(SourceCheckError::Class(declaration));
    }

    let mut result = Vec::with_capacity(parameters.nodes.len());
    let mut names = HashSet::with_capacity(parameters.nodes.len());
    let mut default_seen = false;
    for parameter in &parameters.nodes {
        let parameter = child(declaration, *parameter);
        let record = validator.visit(declaration, parameter)?;
        let NodeData::TypeParameterDeclaration(data) = &record.data else {
            return Err(SourceCheckError::Class(parameter));
        };
        if record.kind != SyntaxKind::TypeParameter
            || data.expression.is_some()
            || data.symbol.is_some()
            || data.modifiers.is_some()
            || default_seen && data.default_type.is_none()
        {
            return Err(SourceCheckError::Class(parameter));
        }
        let name = validator.identifier(parameter, child(parameter, data.name))?;
        if !names.insert(name.clone()) {
            return Err(SourceCheckError::Class(parameter));
        }
        let symbol = declaration_symbol(
            validator.bound,
            validator.store,
            parameter,
            SymbolFlags::TYPE_PARAMETER,
        )?;
        let symbol_record = validator
            .store
            .symbol(symbol)
            .ok_or(SourceCheckError::Class(parameter))?;
        let Some(declarations) = symbol_record.declarations() else {
            return Err(SourceCheckError::Class(parameter));
        };
        if symbol_record.flags() != SymbolFlags::TYPE_PARAMETER
            || symbol_record.check_flags() != CheckFlags::NONE
            || symbol_record.name().as_utf8() != Some(name.as_str())
            || !declarations.contains(&parameter)
            || symbol_record.value_declaration().is_some()
            || symbol_record.members().is_some()
            || symbol_record.exports().is_some()
            || symbol_record.parent() != Some(owner)
            || symbol_record.export_symbol().is_some()
            || validator.bound.symbol(parameter) != Some(symbol)
            || validator
                .store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| validator.store.symbol_table(members))
                .and_then(|members| members.get_source(&name))
                != Some(symbol)
        {
            return Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingDeclarationSymbol(parameter),
            ));
        }
        for annotation in [data.constraint, data.default_type].into_iter().flatten() {
            let annotation = child(parameter, annotation);
            validator.annotations.push(annotation);
            validator.type_node(parameter, annotation)?;
        }
        default_seen |= data.default_type.is_some();
        result.push(symbol);
    }
    Ok(result)
}

fn deferred_ambient_class_heritage(
    validator: &mut DeferredAmbientFunctionValidator<'_>,
    namespace: SemanticSymbolId,
    declaration: NodeRef,
    clauses: Option<&NodeList>,
) -> Result<(), SourceCheckError> {
    let Some(clauses) = clauses else {
        return Ok(());
    };
    if clauses.nodes.is_empty() || clauses.has_trailing_comma {
        return Err(SourceCheckError::Class(declaration));
    }
    let mut extends_seen = false;
    let mut implements_seen = false;
    for clause in &clauses.nodes {
        let clause = child(declaration, *clause);
        let record = validator.visit(declaration, clause)?;
        let NodeData::HeritageClause(heritage) = &record.data else {
            return Err(SourceCheckError::Class(clause));
        };
        if record.kind != SyntaxKind::HeritageClause
            || heritage.facts != 0
            || heritage.types.nodes.is_empty()
            || heritage.types.has_trailing_comma
            || match heritage.token {
                SyntaxKind::ExtendsKeyword if !extends_seen => {
                    extends_seen = true;
                    heritage.types.nodes.len() != 1
                }
                SyntaxKind::ImplementsKeyword if !implements_seen => {
                    implements_seen = true;
                    false
                }
                _ => true,
            }
        {
            return Err(SourceCheckError::Class(clause));
        }

        for base in &heritage.types.nodes {
            let base = child(clause, *base);
            let base_record = validator.visit(clause, base)?;
            let NodeData::ExpressionWithTypeArguments(target) = &base_record.data else {
                return Err(SourceCheckError::Class(base));
            };
            if base_record.kind != SyntaxKind::ExpressionWithTypeArguments
                || target.facts != 0
                || target.type_arguments.as_ref().is_some_and(|arguments| {
                    arguments.nodes.is_empty() || arguments.has_trailing_comma
                })
            {
                return Err(SourceCheckError::Class(base));
            }
            let expression = child(base, target.expression);
            let expression_record = owned_node(
                validator.arena,
                validator.bound,
                validator.store,
                expression,
            )?;
            if let NodeData::Identifier(identifier) = &expression_record.data {
                let symbol = validator
                    .store
                    .symbol(namespace)
                    .and_then(ts_binder::semantic::Symbol::exports)
                    .and_then(|exports| validator.store.symbol_table(exports))
                    .and_then(|exports| exports.get_source(&identifier.text))
                    .or_else(|| {
                        validator
                            .store
                            .intrinsic_bootstrap()
                            .and_then(|bootstrap| validator.store.symbol_table(bootstrap.globals))
                            .and_then(|globals| globals.get_source(&identifier.text))
                    })
                    .and_then(|symbol| validator.store.get_merged_symbol(symbol));
                if symbol
                    .and_then(|symbol| validator.store.symbol(symbol))
                    .is_none_or(|symbol| {
                        if heritage.token == SyntaxKind::ExtendsKeyword {
                            !symbol.flags().contains(SymbolFlags::CLASS)
                        } else {
                            !symbol
                                .flags()
                                .intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE)
                        }
                    })
                {
                    return Err(SourceCheckError::Class(expression));
                }
            }
            validator.type_node(base, expression)?;
            validator.annotations.push(base);
            if let Some(arguments) = &target.type_arguments {
                for argument in &arguments.nodes {
                    let argument = child(base, *argument);
                    validator.annotations.push(argument);
                    validator.type_node(base, argument)?;
                }
            }
        }
    }
    Ok(())
}

#[allow(clippy::too_many_lines)] // Ambient classes retain all member and heritage declarations.
fn plan_deferred_ambient_class(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: (NodeRef, SemanticSymbolId),
    declaration: NodeRef,
) -> Result<SourceNamespaceMemberPlan, SourceCheckError> {
    let (namespace_declaration, namespace_symbol) = namespace;
    let record = owned_node(arena, bound, store, declaration)?;
    let NodeData::ClassDeclaration(class) = &record.data else {
        return Err(SourceCheckError::Class(declaration));
    };
    let Some(name) = class.name else {
        return Err(SourceCheckError::Class(declaration));
    };
    let name = child(declaration, name);
    let name_record = owned_node(arena, bound, store, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(SourceCheckError::Class(name));
    };
    let (_, declared) = modifier_flags(arena, bound, store, declaration, class.modifiers.as_ref())?;
    let symbol = declaration_symbol(bound, store, declaration, SymbolFlags::CLASS)?;
    let class_record = store
        .symbol(symbol)
        .ok_or(SourceCheckError::Class(declaration))?;
    let declarations = class_record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
        .ok_or(SourceCheckError::Class(declaration))?;
    let local = bound
        .local_symbol(declaration)
        .ok_or(SourceCheckError::Class(declaration))?;
    let local_record = store
        .symbol(local)
        .ok_or(SourceCheckError::Class(declaration))?;
    let exports = class_record
        .exports()
        .and_then(|exports| store.symbol_table(exports))
        .ok_or(SourceCheckError::Class(declaration))?;
    let (prototype, prototype_record) = exports
        .get_source("prototype")
        .and_then(|prototype| store.symbol(prototype).map(|record| (prototype, record)))
        .ok_or(SourceCheckError::Class(declaration))?;
    let interface_merge = declarations.iter().any(|candidate| {
        arena
            .get(candidate.node)
            .is_some_and(|record| record.kind == SyntaxKind::InterfaceDeclaration)
    });
    let expected_flags = SymbolFlags::CLASS
        | if interface_merge {
            SymbolFlags::INTERFACE
        } else {
            SymbolFlags::NONE
        };
    if record.kind != SyntaxKind::ClassDeclaration
        || record.flags.0 != 0
        || class.flow_node.is_some()
        || class.local_symbol.is_some()
        || class.next_container.is_some()
        || class.symbol.is_some()
        || class.facts != 0
        || class.members.has_trailing_comma
        || declared
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || class_record.flags() != expected_flags
        || class_record.check_flags() != CheckFlags::NONE
        || class_record.name().as_utf8() != Some(identifier.text.as_str())
        || class_record.value_declaration() != Some(declaration)
        || class_record
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(namespace_symbol)
        || class_record.export_symbol().is_some()
        || store.get_parent_of_symbol(symbol) != Some(namespace_symbol)
        || store.get_merged_symbol(symbol) != Some(symbol)
        || declarations.iter().any(|candidate| {
            !candidate.is_for(declaration.arena, declaration.file)
                || arena.get(candidate.node).is_none_or(|candidate_record| {
                    candidate_record.parent != record.parent
                        || !matches!(
                            candidate_record.kind,
                            SyntaxKind::ClassDeclaration | SyntaxKind::InterfaceDeclaration
                        )
                })
                || bound.symbol(*candidate) != Some(symbol)
        })
        || declarations
            .iter()
            .filter(|candidate| {
                arena
                    .get(candidate.node)
                    .is_some_and(|record| record.kind == SyntaxKind::ClassDeclaration)
            })
            .count()
            != 1
        || local_record.flags() != SymbolFlags::EXPORT_VALUE
        || local_record.check_flags() != CheckFlags::NONE
        || local_record.declarations() != Some(declarations)
        || local_record.value_declaration().is_some()
        || local_record.name().as_utf8() != Some(identifier.text.as_str())
        || local_record.members().is_some()
        || local_record.exports().is_some()
        || local_record.parent().is_some()
        || local_record.export_symbol() != Some(symbol)
        || store.get_merged_symbol(local) != Some(local)
        || bound
            .locals(namespace_declaration)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&identifier.text))
            != Some(local)
        || store
            .symbol(namespace_symbol)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source(&identifier.text))
            != Some(symbol)
        || prototype_record.flags() != SymbolFlags::PROPERTY | SymbolFlags::PROTOTYPE
        || prototype_record.check_flags() != CheckFlags::NONE
        || prototype_record.declarations().is_some()
        || prototype_record.value_declaration().is_some()
        || prototype_record.members().is_some()
        || prototype_record.exports().is_some()
        || prototype_record.parent() != Some(symbol)
        || prototype_record.export_symbol().is_some()
        || store.get_merged_symbol(prototype) != Some(prototype)
        || store
            .value_symbol_links(symbol)
            .is_some_and(|links| links != &ValueSymbolLinks::default())
    {
        return Err(SourceCheckError::Class(declaration));
    }

    let mut validator = DeferredAmbientFunctionValidator::new(arena, bound, store);
    let type_parameters = deferred_ambient_class_type_parameters(
        &mut validator,
        declaration,
        symbol,
        class.type_parameters.as_ref(),
    )?;
    deferred_ambient_class_heritage(
        &mut validator,
        namespace_symbol,
        declaration,
        class.heritage_clauses.as_ref(),
    )?;

    let mut members = Vec::with_capacity(class.members.nodes.len());
    for member in &class.members.nodes {
        let member = child(declaration, *member);
        let member_record = validator.visit(declaration, member)?;
        let symbol = match &member_record.data {
            NodeData::ConstructorDeclaration(constructor)
                if member_record.kind == SyntaxKind::Constructor =>
            {
                if constructor.asterisk_token.is_some()
                    || constructor.body.is_some()
                    || constructor.end_flow_node.is_some()
                    || constructor.full_signature.is_some()
                    || constructor.next_container.is_some()
                    || constructor.return_flow_node.is_some()
                    || constructor.symbol.is_some()
                    || constructor.type_.is_some()
                    || constructor.type_parameters.is_some()
                    || constructor.facts != 0
                    || constructor.modifiers.is_some()
                {
                    return Err(SourceCheckError::Class(member));
                }
                let member_symbol = deferred_ambient_class_member_symbol(
                    arena,
                    bound,
                    store,
                    (declaration, symbol),
                    member,
                    InternalSymbolName::Constructor.as_ref(),
                    SymbolFlags::CONSTRUCTOR,
                    false,
                )?;
                validator.signature_parameters(member, None, &constructor.parameters)?;
                member_symbol
            }
            NodeData::MethodDeclaration(method)
                if member_record.kind == SyntaxKind::MethodDeclaration =>
            {
                if method.asterisk_token.is_some()
                    || method.body.is_some()
                    || method.end_flow_node.is_some()
                    || method.flow_node.is_some()
                    || method.full_signature.is_some()
                    || method.next_container.is_some()
                    || method.symbol.is_some()
                    || method.facts != 0
                {
                    return Err(SourceCheckError::Class(member));
                }
                let (readonly, is_static) = deferred_ambient_class_modifiers(
                    &mut validator,
                    member,
                    method.modifiers.as_ref(),
                )?;
                if readonly {
                    return Err(SourceCheckError::Class(member));
                }
                let name = validator.identifier(member, child(member, method.name))?;
                let optional = if let Some(token) = method.postfix_token {
                    let token = child(member, token);
                    if validator.visit(member, token)?.kind != SyntaxKind::QuestionToken {
                        return Err(SourceCheckError::Class(token));
                    }
                    true
                } else {
                    false
                };
                let flags = SymbolFlags::METHOD
                    | if optional {
                        SymbolFlags::OPTIONAL
                    } else {
                        SymbolFlags::NONE
                    };
                let member_symbol = deferred_ambient_class_member_symbol(
                    arena,
                    bound,
                    store,
                    (declaration, symbol),
                    member,
                    EscapedName::source(&name).as_ref(),
                    flags,
                    is_static,
                )?;
                validator.signature(
                    member,
                    method.type_parameters.as_ref(),
                    &method.parameters,
                    method.type_,
                )?;
                member_symbol
            }
            NodeData::PropertyDeclaration(property)
                if member_record.kind == SyntaxKind::PropertyDeclaration =>
            {
                if property.initializer.is_some()
                    || property.symbol.is_some()
                    || property.facts != 0
                {
                    return Err(SourceCheckError::Class(member));
                }
                let (_, is_static) = deferred_ambient_class_modifiers(
                    &mut validator,
                    member,
                    property.modifiers.as_ref(),
                )?;
                let name = validator.identifier(member, child(member, property.name))?;
                let optional = if let Some(token) = property.postfix_token {
                    let token = child(member, token);
                    if validator.visit(member, token)?.kind != SyntaxKind::QuestionToken {
                        return Err(SourceCheckError::Class(token));
                    }
                    true
                } else {
                    false
                };
                let flags = SymbolFlags::PROPERTY
                    | if optional {
                        SymbolFlags::OPTIONAL
                    } else {
                        SymbolFlags::NONE
                    };
                let member_symbol = deferred_ambient_class_member_symbol(
                    arena,
                    bound,
                    store,
                    (declaration, symbol),
                    member,
                    EscapedName::source(&name).as_ref(),
                    flags,
                    is_static,
                )?;
                let annotation = property
                    .type_
                    .map(|annotation| child(member, annotation))
                    .ok_or(SourceCheckError::Class(member))?;
                validator.annotations.push(annotation);
                validator.type_node(member, annotation)?;
                member_symbol
            }
            _ => return Err(SourceCheckError::Class(member)),
        };
        members.push(symbol);
    }

    Ok(SourceNamespaceMemberPlan::DeferredAmbientClass {
        declaration,
        symbol,
        type_parameters,
        members,
        annotations: validator.annotations,
    })
}

fn classify_ambient_class_error(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: SemanticSymbolId,
    declaration: NodeRef,
    error: SourceCheckError,
) -> SourceCheckError {
    if !matches!(error, SourceCheckError::Class(node) if node == declaration) {
        return error;
    }
    let Some(record) = arena.get(declaration.node) else {
        return error;
    };
    let NodeData::ClassDeclaration(class) = &record.data else {
        return error;
    };
    let Some(name) = class.name.and_then(|name| arena.get(name)) else {
        return error;
    };
    let NodeData::Identifier(identifier) = &name.data else {
        return error;
    };
    let Some(symbol) = bound
        .symbol(declaration)
        .and_then(|symbol| store.get_merged_symbol(symbol))
    else {
        return error;
    };
    let Some(owner) = store.symbol(symbol) else {
        return error;
    };
    let Some(local) = bound.local_symbol(declaration) else {
        return error;
    };
    let Some(local_record) = store.symbol(local) else {
        return error;
    };

    if record.kind == SyntaxKind::ClassDeclaration
        && record.flags.0 == 0
        && name.kind == SyntaxKind::Identifier
        && name.flags.0 == 0
        && name.parent == Some(declaration.node)
        && identifier.flow_node.is_none()
        && !identifier.text.is_empty()
        && owner.flags().contains(SymbolFlags::CLASS)
        && owner.check_flags() == CheckFlags::NONE
        && owner.name().as_utf8() == Some(identifier.text.as_str())
        && owner
            .declarations()
            .is_some_and(|declarations| declarations.contains(&declaration))
        && owner.value_declaration() == Some(declaration)
        && store.get_parent_of_symbol(symbol) == Some(namespace)
        && local_record.flags().contains(SymbolFlags::EXPORT_VALUE)
        && local_record
            .declarations()
            .is_some_and(|declarations| declarations.contains(&declaration))
        && local_record
            .export_symbol()
            .and_then(|export| store.get_merged_symbol(export))
            == Some(symbol)
        && store
            .symbol(namespace)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get_source(&identifier.text))
            .and_then(|export| store.get_merged_symbol(export))
            == Some(symbol)
    {
        unsupported(
            declaration,
            SyntaxKind::ClassDeclaration,
            SourceSyntaxRole::Statement,
        )
    } else {
        error
    }
}

#[allow(clippy::too_many_arguments)] // Local class ownership includes earlier namespace members.
fn plan_namespace_class(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: (NodeRef, SemanticSymbolId),
    ambient: bool,
    declaration: NodeRef,
    classes: &[SourceNamespaceClassPlan],
    variables: &[SourceNamespaceImplicitVariablePlan],
) -> Result<SourceNamespaceClassPlan, SourceCheckError> {
    let (namespace, owner) = namespace;
    let record = owned_node(arena, bound, store, declaration)?;
    let NodeData::ClassDeclaration(class) = &record.data else {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    };
    let Some(name_id) = class.name else {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    };
    let name = child(declaration, name_id);
    let name_record = owned_node(arena, bound, store, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(
            name,
            name_record.kind,
            SourceSyntaxRole::Statement,
        ));
    };
    let symbol = declaration_symbol(bound, store, declaration, SymbolFlags::CLASS)?;
    let class_record = store
        .symbol(symbol)
        .ok_or(SourceCheckError::Class(declaration))?;
    let exports = class_record
        .exports()
        .and_then(|exports| store.symbol_table(exports))
        .ok_or(SourceCheckError::Class(declaration))?;
    let prototype = exports
        .get_source("prototype")
        .and_then(|symbol| store.symbol(symbol).map(|record| (symbol, record)))
        .ok_or(SourceCheckError::Class(declaration))?;
    if ambient
        || record.kind != SyntaxKind::ClassDeclaration
        || record.flags.0 != 0
        || class.flow_node.is_some()
        || class.local_symbol.is_some()
        || class.next_container.is_some()
        || class.symbol.is_some()
        || class.type_parameters.is_some()
        || class.modifiers.is_some()
        || class.facts != 0
        || class.members.has_trailing_comma
        || class.members.nodes.len() > 1
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || class_record.flags() != SymbolFlags::CLASS
        || class_record.check_flags() != CheckFlags::NONE
        || class_record.name().as_utf8() != Some(identifier.text.as_str())
        || class_record.declarations() != Some(&[declaration])
        || class_record.value_declaration() != Some(declaration)
        || class_record.parent().is_some()
        || class_record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || bound.local_symbol(declaration).is_some()
        || bound
            .locals(namespace)
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&identifier.text))
            != Some(symbol)
        || store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .is_some_and(|exports| exports.get_source(&identifier.text).is_some())
        || exports.len() != 1
        || prototype.1.flags() != SymbolFlags::PROPERTY | SymbolFlags::PROTOTYPE
        || prototype.1.check_flags() != CheckFlags::NONE
        || prototype.1.name().as_utf8() != Some("prototype")
        || prototype.1.declarations().is_some()
        || prototype.1.value_declaration().is_some()
        || prototype.1.members().is_some()
        || prototype.1.exports().is_some()
        || prototype.1.parent() != Some(symbol)
        || prototype.1.export_symbol().is_some()
        || store.get_merged_symbol(prototype.0) != Some(prototype.0)
    {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    }

    let property = match class.members.nodes.as_slice() {
        [] => None,
        [member_id] => {
            let member = child(declaration, *member_id);
            let member_record = owned_node(arena, bound, store, member)?;
            let NodeData::PropertyDeclaration(property) = &member_record.data else {
                return Err(unsupported(
                    member,
                    member_record.kind,
                    SourceSyntaxRole::Statement,
                ));
            };
            let Some(annotation_id) = property.type_ else {
                return Err(unsupported(
                    member,
                    member_record.kind,
                    SourceSyntaxRole::Statement,
                ));
            };
            let annotation = child(member, annotation_id);
            let annotation_record = owned_node(arena, bound, store, annotation)?;
            let property_name = child(member, property.name);
            let property_name_record = owned_node(arena, bound, store, property_name)?;
            let NodeData::Identifier(property_identifier) = &property_name_record.data else {
                return Err(unsupported(
                    property_name,
                    property_name_record.kind,
                    SourceSyntaxRole::Statement,
                ));
            };
            let property_symbol = declaration_symbol(bound, store, member, SymbolFlags::PROPERTY)?;
            let property_owner = store
                .symbol(property_symbol)
                .ok_or(SourceCheckError::Class(declaration))?;
            if member_record.kind != SyntaxKind::PropertyDeclaration
                || member_record.flags.0 != 0
                || member_record.parent != Some(declaration.node)
                || property.initializer.is_some()
                || property.postfix_token.is_some()
                || property.symbol.is_some()
                || property.modifiers.is_some()
                || property.facts != 0
                || !matches!(
                    annotation_record.kind,
                    SyntaxKind::StringKeyword | SyntaxKind::NumberKeyword
                )
                || annotation_record.flags.0 != 0
                || annotation_record.parent != Some(member.node)
                || !matches!(annotation_record.data, NodeData::KeywordTypeNode(_))
                || property_name_record.kind != SyntaxKind::Identifier
                || property_name_record.flags.0 != 0
                || property_name_record.parent != Some(member.node)
                || property_identifier.flow_node.is_some()
                || property_identifier.text.is_empty()
                || property_owner.flags() != SymbolFlags::PROPERTY
                || property_owner.check_flags() != CheckFlags::NONE
                || property_owner.name().as_utf8() != Some(property_identifier.text.as_str())
                || property_owner.declarations() != Some(&[member])
                || property_owner.value_declaration() != Some(member)
                || property_owner.members().is_some()
                || property_owner.exports().is_some()
                || property_owner.parent() != Some(symbol)
                || property_owner.export_symbol().is_some()
                || store.get_merged_symbol(property_symbol) != Some(property_symbol)
                || class_record
                    .members()
                    .and_then(|members| store.symbol_table(members))
                    .and_then(|members| members.get_source(&property_identifier.text))
                    != Some(property_symbol)
            {
                return Err(unsupported(
                    member,
                    member_record.kind,
                    SourceSyntaxRole::Statement,
                ));
            }
            Some(SourceNamespaceClassPropertyPlan {
                declaration: member,
                name: property_name,
                symbol: property_symbol,
                annotation,
            })
        }
        _ => unreachable!("namespace classes admit at most one member"),
    };
    if class_record
        .members()
        .and_then(|members| store.symbol_table(members))
        .map_or(0, ts_binder::semantic::SymbolTable::len)
        != usize::from(property.is_some())
    {
        return Err(SourceCheckError::Class(declaration));
    }

    let heritage = class
        .heritage_clauses
        .as_ref()
        .map(|clauses| {
            plan_namespace_class_heritage(
                arena,
                bound,
                store,
                (namespace, owner),
                declaration,
                clauses,
                classes,
                variables,
            )
        })
        .transpose()?;
    if property.is_some()
        && !matches!(
            heritage,
            Some(SourceNamespaceClassHeritagePlan::NonConstructorVariable { .. })
        )
    {
        return Err(unsupported(
            declaration,
            record.kind,
            SourceSyntaxRole::Statement,
        ));
    }

    Ok(SourceNamespaceClassPlan {
        declaration,
        symbol,
        heritage,
        property,
    })
}

fn exact_recursive_namespace_export_modifier(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    modifiers: Option<&ModifierList>,
) -> Option<()> {
    let declaration_record = owned_node(arena, bound, store, declaration).ok()?;
    let modifiers = modifiers?;
    let [modifier] = modifiers.list.nodes.as_slice() else {
        return None;
    };
    let modifier = child(declaration, *modifier);
    let record = owned_node(arena, bound, store, modifier).ok()?;
    (modifiers.flags.0 == 0
        && !modifiers.list.has_trailing_comma
        && modifiers.list.range.start == declaration_record.range.start
        && record.kind == SyntaxKind::ExportKeyword
        && record.flags.0 == 0
        && record.parent == Some(declaration.node)
        && matches!(record.data, NodeData::Token(_))
        && record.range.start == modifiers.list.range.start
        && record.range.end <= modifiers.list.range.end)
        .then_some(())
}

fn plan_recursive_namespace_class(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    namespace: (NodeRef, SemanticSymbolId),
    body: NodeRef,
    statements: &NodeList,
) -> Option<SourceNamespaceRecursiveClassPlan> {
    let (namespace_declaration, namespace_symbol) = namespace;
    let [class_declaration, merged_namespace] = statements.nodes.as_slice() else {
        return None;
    };
    let class_declaration = child(body, *class_declaration);
    let merged_namespace = child(body, *merged_namespace);
    let namespace_record = owned_node(arena, bound, store, namespace_declaration).ok()?;
    let NodeData::ModuleDeclaration(namespace_data) = &namespace_record.data else {
        return None;
    };
    let namespace_name = child(namespace_declaration, namespace_data.name);
    let namespace_name_record = owned_node(arena, bound, store, namespace_name).ok()?;
    let NodeData::Identifier(namespace_identifier) = &namespace_name_record.data else {
        return None;
    };
    let outer = store.symbol(namespace_symbol)?;
    let outer_exports = outer.exports()?;
    let outer_export_table = store.symbol_table(outer_exports)?;

    let class_record = owned_node(arena, bound, store, class_declaration).ok()?;
    let NodeData::ClassDeclaration(class) = &class_record.data else {
        return None;
    };
    exact_recursive_namespace_export_modifier(
        arena,
        bound,
        store,
        class_declaration,
        class.modifiers.as_ref(),
    )?;
    let class_name = child(class_declaration, class.name?);
    let class_name_record = owned_node(arena, bound, store, class_name).ok()?;
    let NodeData::Identifier(class_identifier) = &class_name_record.data else {
        return None;
    };
    let class_symbol =
        declaration_symbol(bound, store, class_declaration, SymbolFlags::CLASS).ok()?;
    let class_owner = store.symbol(class_symbol)?;
    let class_local = bound.local_symbol(class_declaration)?;
    let class_local_record = store.symbol(class_local)?;
    let class_exports = class_owner.exports()?;
    let class_export_table = store.symbol_table(class_exports)?;
    let prototype = class_export_table.get_source("prototype")?;
    let prototype_record = store.symbol(prototype)?;

    let merged_record = owned_node(arena, bound, store, merged_namespace).ok()?;
    let NodeData::ModuleDeclaration(merged_data) = &merged_record.data else {
        return None;
    };
    exact_recursive_namespace_export_modifier(
        arena,
        bound,
        store,
        merged_namespace,
        merged_data.modifiers.as_ref(),
    )?;
    let merged_name = child(merged_namespace, merged_data.name);
    let merged_name_record = owned_node(arena, bound, store, merged_name).ok()?;
    let NodeData::Identifier(merged_identifier) = &merged_name_record.data else {
        return None;
    };
    let merged_body = child(merged_namespace, merged_data.body?);
    let merged_body_record = owned_node(arena, bound, store, merged_body).ok()?;
    let NodeData::ModuleBlock(merged_block) = &merged_body_record.data else {
        return None;
    };
    let [variable_statement] = merged_block.statements.nodes.as_slice() else {
        return None;
    };
    let variable_statement = child(merged_body, *variable_statement);
    let statement_record = owned_node(arena, bound, store, variable_statement).ok()?;
    let NodeData::VariableStatement(statement) = &statement_record.data else {
        return None;
    };
    exact_recursive_namespace_export_modifier(
        arena,
        bound,
        store,
        variable_statement,
        statement.modifiers.as_ref(),
    )?;
    let variable_list = child(variable_statement, statement.declaration_list);
    let variable_list_record = owned_node(arena, bound, store, variable_list).ok()?;
    let NodeData::VariableDeclarationList(variable_list_data) = &variable_list_record.data else {
        return None;
    };
    let [variable_declaration] = variable_list_data.declarations.nodes.as_slice() else {
        return None;
    };
    let variable_declaration = child(variable_list, *variable_declaration);
    let variable_record = owned_node(arena, bound, store, variable_declaration).ok()?;
    let NodeData::VariableDeclaration(variable) = &variable_record.data else {
        return None;
    };
    let variable_name = child(variable_declaration, variable.name);
    let variable_name_record = owned_node(arena, bound, store, variable_name).ok()?;
    let NodeData::Identifier(variable_identifier) = &variable_name_record.data else {
        return None;
    };
    let variable_symbol =
        declaration_symbol(bound, store, variable_declaration, SymbolFlags::VARIABLE).ok()?;
    let variable_owner = store.symbol(variable_symbol)?;
    let variable_local = bound.local_symbol(variable_declaration)?;
    let variable_local_record = store.symbol(variable_local)?;

    let initializer = child(variable_declaration, variable.initializer?);
    let initializer_record = owned_node(arena, bound, store, initializer).ok()?;
    let NodeData::PropertyAccessExpression(access) = &initializer_record.data else {
        return None;
    };
    let receiver = child(initializer, access.expression);
    let receiver_record = owned_node(arena, bound, store, receiver).ok()?;
    let NodeData::Identifier(receiver_identifier) = &receiver_record.data else {
        return None;
    };
    let property = child(initializer, access.name);
    let property_record = owned_node(arena, bound, store, property).ok()?;
    let NodeData::Identifier(property_identifier) = &property_record.data else {
        return None;
    };
    let outer_locals = bound
        .locals(namespace_declaration)
        .and_then(|locals| store.symbol_table(locals))?;
    let merged_locals = bound
        .locals(merged_namespace)
        .and_then(|locals| store.symbol_table(locals))?;

    if namespace_record.kind != SyntaxKind::ModuleDeclaration
        || namespace_record.flags.0 != 0
        || namespace_record.parent != Some(bound.source_file().node)
        || namespace_data.keyword != SyntaxKind::NamespaceKeyword
        || namespace_data.modifiers.is_some()
        || namespace_name_record.kind != SyntaxKind::Identifier
        || namespace_name_record.flags.0 != 0
        || namespace_name_record.parent != Some(namespace_declaration.node)
        || namespace_identifier.flow_node.is_some()
        || namespace_identifier.text.is_empty()
        || outer.flags() != SymbolFlags::VALUE_MODULE
        || outer.check_flags() != CheckFlags::NONE
        || outer.name().as_utf8() != Some(namespace_identifier.text.as_str())
        || outer.declarations() != Some(&[namespace_declaration])
        || outer.members().is_some()
        || outer.parent().is_some()
        || outer.export_symbol().is_some()
        || store.get_merged_symbol(namespace_symbol) != Some(namespace_symbol)
        || outer_export_table.len() != 1
        || outer_locals.len() != 1
        || class_record.kind != SyntaxKind::ClassDeclaration
        || class_record.flags.0 != 0
        || class_record.parent != Some(body.node)
        || class.flow_node.is_some()
        || class.local_symbol.is_some()
        || class.next_container.is_some()
        || class.symbol.is_some()
        || class.type_parameters.is_some()
        || class.heritage_clauses.is_some()
        || class.facts != 0
        || class.members.has_trailing_comma
        || !class.members.nodes.is_empty()
        || class_name_record.kind != SyntaxKind::Identifier
        || class_name_record.flags.0 != 0
        || class_name_record.parent != Some(class_declaration.node)
        || class_identifier.flow_node.is_some()
        || class_identifier.text.is_empty()
        || class_owner.flags() != (SymbolFlags::CLASS | SymbolFlags::VALUE_MODULE)
        || class_owner.check_flags() != CheckFlags::NONE
        || class_owner.name().as_utf8() != Some(class_identifier.text.as_str())
        || class_owner.declarations() != Some(&[class_declaration, merged_namespace])
        || class_owner.value_declaration() != Some(class_declaration)
        || class_owner.members().is_some()
        || class_owner.parent() != Some(namespace_symbol)
        || class_owner.export_symbol().is_some()
        || store.get_parent_of_symbol(class_symbol) != Some(namespace_symbol)
        || store.get_merged_symbol(class_symbol) != Some(class_symbol)
        || outer_export_table.get_source(&class_identifier.text) != Some(class_symbol)
        || class_local == class_symbol
        || class_local_record.flags() != SymbolFlags::EXPORT_VALUE
        || class_local_record.check_flags() != CheckFlags::NONE
        || class_local_record.name().as_utf8() != Some(class_identifier.text.as_str())
        || class_local_record.declarations() != Some(&[class_declaration, merged_namespace])
        || class_local_record.value_declaration().is_some()
        || class_local_record.members().is_some()
        || class_local_record.exports().is_some()
        || class_local_record.parent().is_some()
        || class_local_record.export_symbol() != Some(class_symbol)
        || store.get_merged_symbol(class_local) != Some(class_local)
        || outer_locals.get_source(&class_identifier.text) != Some(class_local)
        || class_export_table.len() != 2
        || prototype_record.flags() != (SymbolFlags::PROPERTY | SymbolFlags::PROTOTYPE)
        || prototype_record.check_flags() != CheckFlags::NONE
        || prototype_record.name().as_utf8() != Some("prototype")
        || prototype_record.declarations().is_some()
        || prototype_record.value_declaration().is_some()
        || prototype_record.members().is_some()
        || prototype_record.exports().is_some()
        || prototype_record.parent() != Some(class_symbol)
        || prototype_record.export_symbol().is_some()
        || store.get_merged_symbol(prototype) != Some(prototype)
        || merged_record.kind != SyntaxKind::ModuleDeclaration
        || merged_record.flags.0 != 0
        || merged_record.parent != Some(body.node)
        || merged_record.range.start < class_record.range.end
        || merged_data.asterisk_token.is_some()
        || merged_data.end_flow_node.is_some()
        || merged_data.flow_node.is_some()
        || merged_data.keyword != SyntaxKind::NamespaceKeyword
        || merged_data.local_symbol.is_some()
        || merged_data.next_container.is_some()
        || merged_data.symbol.is_some()
        || merged_data.facts != 0
        || bound.symbol(merged_namespace) != Some(class_symbol)
        || bound.local_symbol(merged_namespace) != Some(class_local)
        || merged_name_record.kind != SyntaxKind::Identifier
        || merged_name_record.flags.0 != 0
        || merged_name_record.parent != Some(merged_namespace.node)
        || merged_identifier.flow_node.is_some()
        || merged_identifier.text != class_identifier.text
        || merged_body_record.kind != SyntaxKind::ModuleBlock
        || merged_body_record.flags.0 != 0
        || merged_body_record.parent != Some(merged_namespace.node)
        || merged_block.flow_node.is_some()
        || merged_block.facts != 0
        || merged_block.statements.has_trailing_comma
        || merged_locals.len() != 1
        || statement_record.kind != SyntaxKind::VariableStatement
        || statement_record.flags.0 != 0
        || statement_record.parent != Some(merged_body.node)
        || statement.flow_node.is_some()
        || statement.facts != 0
        || variable_list_record.kind != SyntaxKind::VariableDeclarationList
        || variable_list_record.flags.0 != 0
        || variable_list_record.parent != Some(variable_statement.node)
        || variable_list_data.facts != 0
        || variable_list_data.declarations.has_trailing_comma
        || variable_record.kind != SyntaxKind::VariableDeclaration
        || variable_record.flags.0 != 0
        || variable_record.parent != Some(variable_list.node)
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.type_.is_some()
        || variable.facts != 0
        || variable_name_record.kind != SyntaxKind::Identifier
        || variable_name_record.flags.0 != 0
        || variable_name_record.parent != Some(variable_declaration.node)
        || variable_identifier.flow_node.is_some()
        || variable_identifier.text != class_identifier.text
        || variable_symbol == class_symbol
        || variable_owner.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || variable_owner.check_flags() != CheckFlags::NONE
        || variable_owner.name().as_utf8() != Some(class_identifier.text.as_str())
        || variable_owner.declarations() != Some(&[variable_declaration])
        || variable_owner.value_declaration() != Some(variable_declaration)
        || variable_owner.members().is_some()
        || variable_owner.exports().is_some()
        || variable_owner.parent() != Some(class_symbol)
        || variable_owner.export_symbol().is_some()
        || store.get_parent_of_symbol(variable_symbol) != Some(class_symbol)
        || store.get_merged_symbol(variable_symbol) != Some(variable_symbol)
        || class_export_table.get_source(&class_identifier.text) != Some(variable_symbol)
        || variable_local == variable_symbol
        || variable_local_record.flags() != SymbolFlags::EXPORT_VALUE
        || variable_local_record.check_flags() != CheckFlags::NONE
        || variable_local_record.name().as_utf8() != Some(class_identifier.text.as_str())
        || variable_local_record.declarations() != Some(&[variable_declaration])
        || variable_local_record.value_declaration().is_some()
        || variable_local_record.members().is_some()
        || variable_local_record.exports().is_some()
        || variable_local_record.parent().is_some()
        || variable_local_record.export_symbol() != Some(variable_symbol)
        || store.get_merged_symbol(variable_local) != Some(variable_local)
        || merged_locals.get_source(&class_identifier.text) != Some(variable_local)
        || initializer_record.kind != SyntaxKind::PropertyAccessExpression
        || initializer_record.flags.0 != 0
        || initializer_record.parent != Some(variable_declaration.node)
        || access.flow_node.is_some()
        || access.question_dot_token.is_some()
        || access.facts != 0
        || receiver_record.kind != SyntaxKind::Identifier
        || receiver_record.flags.0 != 0
        || receiver_record.parent != Some(initializer.node)
        || receiver_identifier.flow_node.is_some()
        || receiver_identifier.text != namespace_identifier.text
        || property_record.kind != SyntaxKind::Identifier
        || property_record.flags.0 != 0
        || property_record.parent != Some(initializer.node)
        || property_identifier.flow_node.is_some()
        || property_identifier.text != class_identifier.text
        || bound
            .locals(bound.source_file())
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&namespace_identifier.text))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(namespace_symbol)
    {
        return None;
    }

    let plan = SourceNamespaceRecursiveClassPlan {
        class_declaration,
        namespace_declaration: merged_namespace,
        class_symbol,
        class_local,
        prototype,
        variable_declaration,
        variable_symbol,
        variable_local,
        initializer,
        receiver,
        property,
    };
    recursive_namespace_class_state(store, namespace_symbol, &plan)?;
    Some(plan)
}

fn recursive_namespace_class_state(
    store: &CanonicalTypeMapperStore,
    namespace: SemanticSymbolId,
    class: &SourceNamespaceRecursiveClassPlan,
) -> Option<RecursiveNamespaceClassCacheState> {
    let exact_value = |symbol| {
        let Some(links) = store.value_symbol_links(symbol) else {
            return Some(None);
        };
        (links
            == &(ValueSymbolLinks {
                resolved_type: links.resolved_type,
                ..ValueSymbolLinks::default()
            }))
            .then_some(links.resolved_type)
    };
    let namespace_type = exact_value(namespace)?;
    let class_type = exact_value(class.class_symbol)?;
    let local_type = exact_value(class.class_local)?;
    let variable_type = exact_value(class.variable_symbol)?;
    let instance = store
        .declared_type_links(class.class_symbol)
        .and_then(|links| links.declared_type);
    if store
        .value_symbol_links(class.variable_local)
        .is_some_and(|links| links != &ValueSymbolLinks::default())
        || store
            .type_node_links(class.property)
            .is_some_and(|links| links != &TypeNodeLinks::default())
        || store
            .symbol_node_links(class.property)
            .is_some_and(|links| links != &SymbolNodeLinks::default())
    {
        return None;
    }

    let (namespace_type, class_type, instance) = match (
        namespace_type,
        class_type,
        local_type,
        variable_type,
        instance,
    ) {
        (None, None, None, None, None) => {
            if [class.receiver, class.initializer].iter().any(|node| {
                store
                    .type_node_links(*node)
                    .is_some_and(|links| links != &TypeNodeLinks::default())
                    || store
                        .symbol_node_links(*node)
                        .is_some_and(|links| links != &SymbolNodeLinks::default())
            }) {
                return None;
            }
            return Some(RecursiveNamespaceClassCacheState::Cold);
        }
        (Some(namespace_type), Some(class_type), Some(local), Some(variable), Some(instance))
            if local == class_type && variable == class_type =>
        {
            (namespace_type, class_type, instance)
        }
        _ => return None,
    };

    let namespace_exports = store.symbol(namespace)?.exports()?;
    let namespace_record = store.type_payload(namespace_type)?;
    let TypeData::Object(namespace_data) = namespace_record.data() else {
        return None;
    };
    let class_exports = store.symbol(class.class_symbol)?.exports()?;
    let class_record = store.type_payload(class_type)?;
    let TypeData::Object(class_data) = class_record.data() else {
        return None;
    };
    let [signature] = class_data.structured.signatures.as_deref()? else {
        return None;
    };
    let signature = store.signature(*signature)?;
    let instance_record = store.type_payload(instance)?;
    let TypeData::Interface(instance_data) = instance_record.data() else {
        return None;
    };
    let undefined = store.intrinsic_bootstrap()?.undefined_type;
    if namespace_record.flags() != TypeFlags::OBJECT
        || namespace_record.object_flags()
            != (ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
        || namespace_record.symbol() != Some(namespace)
        || namespace_record.alias().is_some()
        || namespace_data.structured.members != Some(namespace_exports)
        || namespace_data.structured.properties.as_deref() != Some(&[class.class_symbol])
        || namespace_data.structured.signatures.is_some()
        || namespace_data.structured.call_signature_count != 0
        || namespace_data.structured.index_infos.is_some()
        || class_record.flags() != TypeFlags::OBJECT
        || class_record.object_flags() != (ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
        || class_record.symbol() != Some(class.class_symbol)
        || class_record.alias().is_some()
        || class_data.structured.members != Some(class_exports)
        || class_data.structured.properties.as_deref()
            != Some(&[class.variable_symbol, class.prototype])
        || class_data.structured.call_signature_count != 0
        || class_data.structured.index_infos.is_some()
        || signature.flags() != SignatureFlags::CONSTRUCT
        || signature.declaration().is_some()
        || !signature.type_parameters().is_empty()
        || !signature.parameters().is_empty()
        || signature.this_parameter().is_some()
        || signature.min_argument_count() != 0
        || signature.resolved_min_argument_count() != -1
        || signature.resolved_return_type() != Some(instance)
        || signature.resolved_type_predicate().is_some()
        || signature.target().is_some()
        || signature.mapper().is_some()
        || signature.isolated_signature_type().is_some()
        || signature.composite().is_some()
        || instance_record.flags() != TypeFlags::OBJECT
        || instance_record.object_flags()
            != (ObjectFlags::CLASS | ObjectFlags::REFERENCE | ObjectFlags::MEMBERS_RESOLVED)
        || instance_record.symbol() != Some(class.class_symbol)
        || instance_record.alias().is_some()
        || !instance_data.base_types_resolved
        || instance_data.resolved_base_constructor_type != Some(undefined)
        || instance_data.resolved_base_types.is_some()
        || !instance_data.declared_members_resolved
        || instance_data.declared_members.is_some()
        || instance_data.declared_call_signatures.is_some()
        || instance_data.declared_construct_signatures.is_some()
        || instance_data.declared_index_infos.is_some()
        || instance_data.reference.object.structured.members.is_some()
        || instance_data
            .reference
            .object
            .structured
            .properties
            .is_some()
        || instance_data
            .reference
            .object
            .structured
            .signatures
            .is_some()
        || instance_data
            .reference
            .object
            .structured
            .index_infos
            .is_some()
        || instance_data
            .reference
            .resolved_type_arguments
            .as_ref()
            .is_none_or(|arguments| !arguments.is_empty())
        || store.type_node_links(class.receiver)
            != Some(&TypeNodeLinks {
                resolved_type: Some(namespace_type),
                ..TypeNodeLinks::default()
            })
        || store.type_node_links(class.initializer)
            != Some(&TypeNodeLinks {
                resolved_type: Some(class_type),
                ..TypeNodeLinks::default()
            })
        || store.symbol_node_links(class.receiver)
            != Some(&SymbolNodeLinks {
                resolved_symbol: Some(namespace),
            })
        || store.symbol_node_links(class.initializer)
            != Some(&SymbolNodeLinks {
                resolved_symbol: Some(class.class_symbol),
            })
    {
        return None;
    }

    Some(RecursiveNamespaceClassCacheState::Warm(
        SourceNamespaceRecursiveClassState {
            instance,
            namespace_type,
            class_type,
        },
    ))
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
    let expected_name = if export.is_export_equals {
        InternalSymbolName::ExportEquals.as_ref()
    } else {
        InternalSymbolName::Default.as_ref()
    };
    if alias.flags() != SymbolFlags::ALIAS
        || alias.check_flags() != CheckFlags::NONE
        || alias.name() != expected_name
        || alias.declarations() != Some(&[declaration])
        || alias.value_declaration() != export.is_export_equals.then_some(declaration)
        || alias.members().is_some()
        || alias.exports().is_some()
        || alias.export_symbol().is_some()
        || store.get_parent_of_symbol(symbol) != Some(owner)
        || store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| store.symbol_table(exports))
            .and_then(|exports| exports.get(expected_name))
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
    let mut classes = Vec::new();
    let mut recursive_class: Option<SourceNamespaceRecursiveClassPlan> = None;
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
                            if recursive_class
                                .as_ref()
                                .is_some_and(|class| class.namespace_declaration == statement)
                            {
                                continue;
                            }
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
                        SyntaxKind::ClassDeclaration if ambient => {
                            let class = plan_deferred_ambient_class(
                                arena,
                                bound,
                                store,
                                (declaration, symbol),
                                statement,
                            )
                            .map_err(|error| {
                                classify_ambient_class_error(
                                    arena, bound, store, symbol, statement, error,
                                )
                            })?;
                            members.push(class);
                        }
                        SyntaxKind::ClassDeclaration if !ambient => {
                            if let Some(class) = plan_recursive_namespace_class(
                                arena,
                                bound,
                                store,
                                (declaration, symbol),
                                body,
                                &block.statements,
                            ) {
                                recursive_class = Some(class);
                                continue;
                            }
                            let class = plan_namespace_class(
                                arena,
                                bound,
                                store,
                                (declaration, symbol),
                                ambient,
                                statement,
                                &classes,
                                &implicit_variables,
                            )?;
                            classes.push(class);
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
                        SyntaxKind::ExportDeclaration
                            if ambient && is_string_module && facts.is_declaration_file() =>
                        {
                            imports.extend(plan_ambient_module_reexport(
                                arena,
                                bound,
                                store,
                                (declaration, symbol),
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
        classes,
        recursive_class,
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
            SourceNamespaceMemberPlan::TypeAlias {
                annotation,
                parameter_annotations,
                deferred: false,
                ..
            } => {
                annotations.extend(parameter_annotations.iter().copied());
                annotations.push(*annotation);
                declarations.push(member);
            }
            SourceNamespaceMemberPlan::AmbientVariable { annotation, .. } => {
                annotations.push(*annotation);
                declarations.push(member);
            }
            SourceNamespaceMemberPlan::Interface {
                annotations: interface_annotations,
                generic,
                ..
            } => {
                annotations.extend(interface_annotations.iter().copied().filter(|annotation| {
                    generic
                        .as_ref()
                        .is_none_or(|generic| !generic.annotation_is_deferred(*annotation))
                }));
                declarations.push(member);
            }
            SourceNamespaceMemberPlan::TypeAlias { deferred: true, .. }
            | SourceNamespaceMemberPlan::EmptyEnum { .. }
            | SourceNamespaceMemberPlan::Function { .. }
            | SourceNamespaceMemberPlan::DeferredAmbientFunction { .. }
            | SourceNamespaceMemberPlan::DeferredAmbientClass { .. } => {
                declarations.push(member);
            }
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

/// Resolves manifest-backed imports nested in quoted ambient modules.
pub(super) fn resolve_source_namespace_external_imports(
    store: &mut CanonicalTypeMapperStore,
    alias_host: &mut ProductionAliasTargetHost<'_, '_, '_>,
    plan: &SourceNamespacePlan,
) -> Result<(), SourceCheckError> {
    let unavailable = |declaration, error| match error {
        CanonicalAliasResolutionError::TargetUnavailable {
            reason:
                CanonicalAliasTargetUnavailable::ModuleResolutionCapabilityUnavailable(_)
                | CanonicalAliasTargetUnavailable::ModuleResolutionEntryAbsent(_)
                | CanonicalAliasTargetUnavailable::ModuleResolutionUnresolved(_)
                | CanonicalAliasTargetUnavailable::MissingExport { .. }
                | CanonicalAliasTargetUnavailable::UnsupportedAliasDeclaration(_)
                | CanonicalAliasTargetUnavailable::UnsupportedLocalExport(_)
                | CanonicalAliasTargetUnavailable::ExportStarResolutionUnsupported { .. }
                | CanonicalAliasTargetUnavailable::ExportEqualsResolutionUnsupported { .. },
            ..
        } => SourceCheckError::Unsupported(UnsupportedSourceSyntax::Import(declaration)),
        _ => SourceCheckError::Import(declaration),
    };
    let mut imports = Vec::new();
    namespace_imports(plan, &mut imports);
    for import in imports {
        if import.ambient_target.is_some()
            || store.source_node_kind(import.reference) != Some(SyntaxKind::StringLiteral)
        {
            continue;
        }
        let immediate = CanonicalAliasResolver::new(store, alias_host)
            .get_immediate_aliased_symbol(import.symbol)
            .map_err(|error| unavailable(import.declaration, error))?
            .ok_or(SourceCheckError::Import(import.declaration))?;
        let resolution = CanonicalAliasResolver::new(store, alias_host)
            .resolve_alias(import.symbol)
            .map_err(|error| unavailable(import.declaration, error))?;
        let Some(target) = resolution.target.symbol() else {
            return Err(SourceCheckError::Import(import.declaration));
        };
        if !resolution.events.is_empty()
            || store.get_merged_symbol(immediate) != Some(immediate)
            || store.get_merged_symbol(target) != Some(target)
            || store.alias_symbol_links(import.symbol).is_none_or(|links| {
                links.immediate_target != Some(immediate)
                    || links.alias_target != AliasTargetState::Resolved(target)
            })
        {
            return Err(SourceCheckError::Import(import.declaration));
        }
    }
    Ok(())
}

fn ambient_module_export_name(
    host: &DeclaredTypeHost<'_>,
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    fallback: NodeRef,
) -> Result<(NodeRef, String), SourceCheckError> {
    let record = store
        .symbol(symbol)
        .ok_or(SourceCheckError::Import(fallback))?;
    let Some([declaration]) = record.declarations() else {
        return Err(SourceCheckError::Import(fallback));
    };
    let declaration = *declaration;
    let node = host
        .node(declaration)
        .ok_or_else(|| missing_node(declaration))?;
    let name = match &node.data {
        NodeData::ExportSpecifier(export) if node.kind == SyntaxKind::ExportSpecifier => {
            child(declaration, export.name)
        }
        NodeData::VariableDeclaration(variable) if node.kind == SyntaxKind::VariableDeclaration => {
            child(declaration, variable.name)
        }
        _ => return Err(SourceCheckError::Import(declaration)),
    };
    let name_record = host.node(name).ok_or_else(|| missing_node(name))?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(SourceCheckError::Import(declaration));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || record.name().as_utf8() != Some(identifier.text.as_str())
        || !host.symbol_matches(store, declaration, symbol)
    {
        return Err(SourceCheckError::Import(declaration));
    }
    Ok((name, identifier.text.clone()))
}

fn issue_ambient_module_export_collision(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    declaration: NodeRef,
    first: SemanticSymbolId,
    second: SemanticSymbolId,
) -> Result<(), SourceCheckError> {
    let (first_name, name) = ambient_module_export_name(host, store, first, declaration)?;
    let (second_name, second_text) = ambient_module_export_name(host, store, second, declaration)?;
    if name != second_text {
        return Err(SourceCheckError::Import(second_name));
    }
    let primary = message_by_code(CANNOT_REDECLARE_BLOCK_SCOPED_VARIABLE).ok_or(
        SourceCheckError::MissingDiagnostic(CANNOT_REDECLARE_BLOCK_SCOPED_VARIABLE),
    )?;
    let related = message_by_code(ALSO_DECLARED_HERE)
        .ok_or(SourceCheckError::MissingDiagnostic(ALSO_DECLARED_HERE))?;
    for (declaration, other) in [(first_name, second_name), (second_name, first_name)] {
        super::source::merge_retry_diagnostic(
            diagnostics,
            CanonicalCheckerDiagnostic {
                node: Some(declaration),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(primary, [name.clone()]),
                related_information: vec![CanonicalCheckerRelatedInformation {
                    node: Some(other),
                    diagnostic: Diagnostic::with_arguments(related, [name.clone()]),
                }],
            },
        );
    }
    Ok(())
}

/// Registers reopened ambient modules and reports exact block-scoped export collisions.
pub(super) fn merge_source_ambient_module_exports(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &SourceNamespacePlan,
) -> Result<(), SourceCheckError> {
    let Some(name_record) = host.node(plan.name) else {
        return Err(missing_node(plan.name));
    };
    let NodeData::StringLiteral(name) = &name_record.data else {
        return Ok(());
    };
    let Some((_, bound)) = host.source(plan.declaration) else {
        return Err(missing_node(plan.declaration));
    };
    if !plan.ambient
        || !bound
            .source_facts()
            .is_some_and(ts_binder::CanonicalSourceFileFacts::is_declaration_file)
        || name.text.contains('*')
    {
        return Ok(());
    }
    let owner = store
        .symbol(plan.symbol)
        .ok_or(SourceCheckError::Import(plan.declaration))?;
    let key = owner.name().to_owned();
    let Some(exports) = owner.exports() else {
        return Ok(());
    };
    let globals = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.globals)
        .ok_or(SourceCheckError::LiteralCache(
            SourceLiteralCacheError::BootstrapUninitialized,
        ))?;
    let existing = store
        .symbol_table(globals)
        .and_then(|globals| globals.get(key.as_ref()))
        .and_then(|symbol| store.get_merged_symbol(symbol));
    let Some(existing) = existing else {
        return store
            .insert_symbol(globals, key, plan.symbol)
            .filter(Option::is_none)
            .map(|_| ())
            .ok_or(SourceCheckError::Import(plan.declaration));
    };
    if existing == plan.symbol {
        return Ok(());
    }
    let existing_exports = store
        .symbol(existing)
        .and_then(ts_binder::semantic::Symbol::exports)
        .and_then(|exports| store.symbol_table(exports))
        .ok_or(SourceCheckError::Import(plan.declaration))?;
    let current_exports = store
        .symbol_table(exports)
        .ok_or(SourceCheckError::Import(plan.declaration))?;
    let mut collisions = Vec::new();
    let mut overlaps = false;
    for (name, current) in current_exports.iter() {
        let Some(previous) = existing_exports
            .get(name)
            .and_then(|previous| store.get_merged_symbol(previous))
        else {
            continue;
        };
        overlaps = true;
        let current = store
            .get_merged_symbol(current)
            .ok_or(SourceCheckError::Import(plan.declaration))?;
        if previous == current {
            continue;
        }
        let previous_flags = store
            .symbol(previous)
            .map(ts_binder::semantic::Symbol::flags)
            .ok_or(SourceCheckError::Import(plan.declaration))?;
        let current_flags = store
            .symbol(current)
            .map(ts_binder::semantic::Symbol::flags)
            .ok_or(SourceCheckError::Import(plan.declaration))?;
        if (previous_flags | current_flags).intersects(SymbolFlags::BLOCK_SCOPED_VARIABLE)
            && (previous_flags.intersects(SymbolFlags::ALIAS | SymbolFlags::VALUE)
                && current_flags.intersects(SymbolFlags::ALIAS | SymbolFlags::VALUE))
        {
            collisions.push((name.to_owned(), previous, current));
        }
    }
    collisions.sort_by(|left, right| left.0.as_bytes().cmp(right.0.as_bytes()));
    for (_, first, second) in collisions {
        issue_ambient_module_export_collision(
            store,
            host,
            diagnostics,
            plan.declaration,
            first,
            second,
        )?;
    }
    if overlaps {
        return Ok(());
    }
    let merged = store
        .merge_symbol(existing, plan.symbol, false)
        .map_err(|_| SourceCheckError::Import(plan.declaration))?;
    store
        .insert_symbol(globals, key, merged)
        .filter(|previous| previous.is_some_and(|previous| previous == existing))
        .map(|_| ())
        .ok_or(SourceCheckError::Import(plan.declaration))
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

fn namespace_classes<'plan>(
    plan: &'plan SourceNamespacePlan,
    classes: &mut Vec<&'plan SourceNamespaceClassPlan>,
) {
    classes.extend(&plan.classes);
    for member in &plan.members {
        if let SourceNamespaceMemberPlan::Namespace(nested) = member {
            namespace_classes(nested, classes);
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
    if store.source_node_kind(import.reference) == Some(SyntaxKind::StringLiteral) {
        let links =
            store
                .alias_symbol_links(import.symbol)
                .ok_or(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Import(import.declaration),
                ))?;
        let target = links
            .immediate_target
            .ok_or(SourceCheckError::Import(import.declaration))?;
        if links.alias_target.symbol().is_none() || store.get_merged_symbol(target) != Some(target)
        {
            return Err(SourceCheckError::Import(import.declaration));
        }
        return Ok(target);
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

fn execute_recursive_namespace_class(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: &SourceNamespacePlan,
    class: &SourceNamespaceRecursiveClassPlan,
) -> Result<(), SourceCheckError> {
    let invalid = || SourceCheckError::Class(class.class_declaration);
    if namespace.ambient
        || !namespace.members.is_empty()
        || !namespace.imports.is_empty()
        || !namespace.implicit_variables.is_empty()
        || !namespace.ambient_variables.is_empty()
        || !namespace.object_initializers.is_empty()
        || !namespace.classes.is_empty()
        || !namespace.diagnostics.is_empty()
    {
        return Err(invalid());
    }
    let state =
        recursive_namespace_class_state(store, namespace.symbol, class).ok_or_else(invalid)?;
    if matches!(state, RecursiveNamespaceClassCacheState::Warm(_)) {
        return Ok(());
    }
    if preflight_class_or_interface_reference(store, host, class.class_symbol, SymbolFlags::CLASS)?
        != 0
    {
        return Err(invalid());
    }
    let namespace_exports = store
        .symbol(namespace.symbol)
        .and_then(ts_binder::semantic::Symbol::exports)
        .ok_or_else(invalid)?;
    let class_exports = store
        .symbol(class.class_symbol)
        .and_then(ts_binder::semantic::Symbol::exports)
        .ok_or_else(invalid)?;
    let undefined = store
        .intrinsic_bootstrap()
        .ok_or_else(invalid)?
        .undefined_type;
    let value_symbols = [
        class.class_symbol,
        class.class_local,
        namespace.symbol,
        class.variable_symbol,
    ];
    let missing_values = value_symbols
        .iter()
        .filter(|symbol| store.value_symbol_links(**symbol).is_none())
        .count();
    let expressions = [class.receiver, class.initializer];
    let missing_types = expressions
        .iter()
        .filter(|node| store.type_node_links(**node).is_none())
        .count();
    let missing_symbols = expressions
        .iter()
        .filter(|node| store.symbol_node_links(**node).is_none())
        .count();
    if !store.try_reserve_types(4)
        || !store.try_reserve_signatures(1)
        || !store.try_reserve_value_symbol_links(missing_values)
        || !store.try_reserve_type_node_links(missing_types)
        || !store.try_reserve_symbol_node_links(missing_symbols)
    {
        return Err(invalid());
    }

    let instance = store.get_declared_type_of_symbol(host, class.class_symbol)?;
    let class_type = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(class.class_symbol))
        .ok_or_else(invalid)?;
    let namespace_type = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(namespace.symbol))
        .ok_or_else(invalid)?;
    let signature = store
        .alloc_signature(
            SignatureFlags::CONSTRUCT,
            None,
            Vec::new(),
            None,
            Vec::new(),
            Some(instance),
            None,
            0,
        )
        .ok_or_else(invalid)?;
    if !store.set_interface_base_resolution(instance, true, Some(undefined), None)
        || !store.set_interface_declared_members(instance, true, None, None, None, None)
        || !store.set_structured_type_members(instance, None, None, None, None, None)
        || !store.set_structured_type_members(
            class_type,
            Some(class_exports),
            Some(vec![class.variable_symbol, class.prototype]),
            None,
            Some(vec![signature]),
            None,
        )
        || !store.set_structured_type_members(
            namespace_type,
            Some(namespace_exports),
            Some(vec![class.class_symbol]),
            None,
            None,
            None,
        )
        || !store.set_type_node_links(
            class.receiver,
            TypeNodeLinks {
                resolved_type: Some(namespace_type),
                ..TypeNodeLinks::default()
            },
        )
        || !store.set_type_node_links(
            class.initializer,
            TypeNodeLinks {
                resolved_type: Some(class_type),
                ..TypeNodeLinks::default()
            },
        )
        || !store.set_symbol_node_links(
            class.receiver,
            SymbolNodeLinks {
                resolved_symbol: Some(namespace.symbol),
            },
        )
        || !store.set_symbol_node_links(
            class.initializer,
            SymbolNodeLinks {
                resolved_symbol: Some(class.class_symbol),
            },
        )
    {
        return Err(invalid());
    }
    for (symbol, type_) in [
        (class.class_symbol, class_type),
        (class.class_local, class_type),
        (namespace.symbol, namespace_type),
        (class.variable_symbol, class_type),
    ] {
        if !store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ) {
            return Err(invalid());
        }
    }

    (recursive_namespace_class_state(store, namespace.symbol, class)
        == Some(RecursiveNamespaceClassCacheState::Warm(
            SourceNamespaceRecursiveClassState {
                instance,
                namespace_type,
                class_type,
            },
        )))
    .then_some(())
    .ok_or_else(invalid)
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
    if let Some(class) = plan.recursive_class.as_ref() {
        return execute_recursive_namespace_class(store, host, plan, class);
    }

    let mut annotations = Vec::new();
    let mut declarations = Vec::new();
    let mut planned_diagnostics = Vec::new();
    let mut implicit_variables = Vec::new();
    let mut ambient_variables = Vec::new();
    let mut object_initializers = Vec::new();
    let mut classes = Vec::new();
    namespace_annotations(
        plan,
        &mut annotations,
        &mut declarations,
        &mut planned_diagnostics,
    );
    namespace_implicit_variables(plan, &mut implicit_variables);
    namespace_ambient_variables(plan, &mut ambient_variables);
    namespace_object_initializers(plan, &mut object_initializers);
    namespace_classes(plan, &mut classes);
    for class in &classes {
        if let Some(property) = class.property.as_ref() {
            annotations.push(property.annotation);
        }
        if preflight_class_or_interface_reference(store, host, class.symbol, SymbolFlags::CLASS)?
            != 0
        {
            return Err(SourceCheckError::Class(class.declaration));
        }
        let diagnostic = match class.heritage.as_ref() {
            Some(SourceNamespaceClassHeritagePlan::MissingPrivateExport { .. }) => {
                Some(PROPERTY_DOES_NOT_EXIST)
            }
            Some(SourceNamespaceClassHeritagePlan::NonConstructorVariable { .. }) => {
                Some(TYPE_IS_NOT_A_CONSTRUCTOR)
            }
            None => None,
        };
        if let Some(code) = diagnostic
            && message_by_code(code).is_none()
        {
            return Err(SourceCheckError::MissingDiagnostic(code));
        }
        if class.property.is_some()
            && options.intrinsic.strict_null_checks
            && options.strict_property_initialization
            && message_by_code(PROPERTY_HAS_NO_INITIALIZER).is_none()
        {
            return Err(SourceCheckError::MissingDiagnostic(
                PROPERTY_HAS_NO_INITIALIZER,
            ));
        }
    }
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
            SourceNamespaceMemberPlan::TypeAlias {
                symbol,
                annotation,
                deferred,
                ..
            } => {
                if !*deferred
                    || store.type_alias_links(*symbol).is_some()
                    || store.type_node_links(*annotation).is_some()
                {
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
                    if !generic.call_signatures.is_empty()
                        || !generic.construct_signatures.is_empty()
                        || !generic.index_signatures.is_empty()
                        || !generic.methods.is_empty()
                        || !generic.computed_properties.is_empty()
                        || !generic.base_interfaces.is_empty()
                        || generic
                            .properties
                            .iter()
                            .any(|property| generic.annotation_is_deferred(property.annotation))
                        || object_members::plan_lazy_merged_generic_interface(store, host, *symbol)
                            .is_ok()
                    {
                        continue;
                    }
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
                if callable_plan.body_mode.is_ambient() {
                    CanonicalTypeQuery::new_with_global_types_and_session(
                        store,
                        host,
                        global_types,
                        options,
                        session,
                        diagnostics,
                    )?
                    .get_return_type_of_signature(signature)?;
                } else {
                    let void = store
                        .intrinsic_bootstrap()
                        .ok_or(SourceCheckError::LiteralCache(
                            SourceLiteralCacheError::BootstrapUninitialized,
                        ))?
                        .void_type;
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
            SourceNamespaceMemberPlan::DeferredAmbientFunction { .. }
            | SourceNamespaceMemberPlan::DeferredAmbientClass { .. } => {}
        }
    }

    for class in &classes {
        let instance = store.get_declared_type_of_symbol(host, class.symbol)?;
        let Some(record) = store.type_payload(instance) else {
            return Err(SourceCheckError::Class(class.declaration));
        };
        if record.symbol() != Some(class.symbol)
            || !record.object_flags().contains(ObjectFlags::CLASS)
            || !matches!(record.data(), TypeData::Interface(_))
        {
            return Err(SourceCheckError::Class(class.declaration));
        }
        if let Some(property) = class.property.as_ref() {
            session.reset_query();
            let type_ = CanonicalTypeQuery::new_with_global_types_and_session(
                store,
                host,
                global_types,
                options,
                session,
                diagnostics,
            )?
            .get_type_from_type_node(property.annotation)?;
            stage_namespace_value(
                store,
                &mut values,
                property.declaration,
                property.symbol,
                type_,
            )?;
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
    for class in classes {
        if let Some(heritage) = class.heritage.as_ref() {
            let (node, code, arguments) = match heritage {
                SourceNamespaceClassHeritagePlan::MissingPrivateExport {
                    property,
                    property_name,
                    namespace_name,
                } => (
                    *property,
                    PROPERTY_DOES_NOT_EXIST,
                    vec![property_name.clone(), format!("typeof {namespace_name}")],
                ),
                SourceNamespaceClassHeritagePlan::NonConstructorVariable { expression, symbol } => {
                    let number = store
                        .intrinsic_bootstrap()
                        .ok_or(SourceCheckError::LiteralCache(
                            SourceLiteralCacheError::BootstrapUninitialized,
                        ))?
                        .number_type;
                    if store
                        .value_symbol_links(*symbol)
                        .and_then(|links| links.resolved_type)
                        != Some(number)
                    {
                        return Err(SourceCheckError::Class(class.declaration));
                    }
                    (
                        *expression,
                        TYPE_IS_NOT_A_CONSTRUCTOR,
                        vec!["number".to_owned()],
                    )
                }
            };
            let message = message_by_code(code).ok_or(SourceCheckError::MissingDiagnostic(code))?;
            super::source::merge_retry_diagnostic(
                diagnostics,
                super::CanonicalCheckerDiagnostic {
                    node: Some(node),
                    range_override: None,
                    diagnostic: Diagnostic::with_arguments(message, arguments),
                    related_information: Vec::new(),
                },
            );
        }
        if let Some(property) = class.property.as_ref()
            && options.intrinsic.strict_null_checks
            && options.strict_property_initialization
        {
            let name = host
                .node(property.name)
                .ok_or_else(|| missing_node(property.name))?;
            let NodeData::Identifier(identifier) = &name.data else {
                return Err(SourceCheckError::Class(class.declaration));
            };
            let message = message_by_code(PROPERTY_HAS_NO_INITIALIZER).ok_or(
                SourceCheckError::MissingDiagnostic(PROPERTY_HAS_NO_INITIALIZER),
            )?;
            super::source::merge_retry_diagnostic(
                diagnostics,
                super::CanonicalCheckerDiagnostic {
                    node: Some(property.name),
                    range_override: None,
                    diagnostic: Diagnostic::with_arguments(message, [identifier.text.clone()]),
                    related_information: Vec::new(),
                },
            );
        }
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
        CanonicalCheckerContext, TypeAliasLinks,
        instantiate::{InstantiationLimits, InstantiationSession},
        module_resolution::{
            CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
            CanonicalModuleResolutionMode, CanonicalResolvedModuleInput,
        },
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
        fixture_with_strict_source_facts(source, module_state, options, declaration_file, false)
    }

    fn fixture_with_strict_source_facts(
        source: &'static str,
        module_state: CanonicalModuleState,
        options: CanonicalCheckerOptions,
        declaration_file: bool,
        always_strict: bool,
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
                )
                .with_always_strict(always_strict),
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

    fn ambient_module_context<'arena>(
        files: &[(FileId, &'arena ParseResult, CanonicalModuleState)],
        manifest: Option<CanonicalModuleResolutionManifestInput>,
    ) -> CanonicalCheckerContext<'arena> {
        let mut binder = CanonicalBinder::new();
        for &(file, parsed, state) in files {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"/ambient-{}.d.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        true,
                        state,
                    ),
                )
                .unwrap();
        }
        for &(file, parsed, _) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let arenas = files
            .iter()
            .map(|(file, parsed, _)| (*file, &parsed.arena))
            .collect();
        match manifest {
            Some(manifest) => CanonicalCheckerContext::new_with_module_resolutions(
                binder.finish(),
                arenas,
                CanonicalCheckerOptions::default(),
                manifest,
            )
            .unwrap(),
            None => CanonicalCheckerContext::new(
                binder.finish(),
                arenas,
                CanonicalCheckerOptions::default(),
            )
            .unwrap(),
        }
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
    fn recursive_exported_namespace_classes_preserve_merged_constructor_identity() {
        let mut fixture = fixture(
            concat!(
                "namespace M { ",
                "export class C {} ",
                "export namespace C { export var C = M.C; } ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let cold = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().signature_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );
        let namespace = plan(&fixture, 0);
        let class = namespace
            .recursive_class
            .as_ref()
            .expect("the exported class and namespace must retain one recursive plan")
            .clone();
        let bound = fixture.context.file(fixture.file).unwrap().1;

        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().signature_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            ),
            cold,
        );
        assert_eq!(
            bound.symbol(class.class_declaration),
            Some(class.class_symbol),
        );
        assert_eq!(
            bound.symbol(class.namespace_declaration),
            Some(class.class_symbol),
        );
        assert_eq!(
            bound.local_symbol(class.class_declaration),
            Some(class.class_local),
        );
        assert_eq!(
            bound.local_symbol(class.namespace_declaration),
            Some(class.class_local),
        );
        assert_eq!(
            fixture
                .context
                .store()
                .symbol(class.class_symbol)
                .unwrap()
                .flags(),
            SymbolFlags::CLASS | SymbolFlags::VALUE_MODULE,
        );
        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());

        let Some(RecursiveNamespaceClassCacheState::Warm(state)) =
            recursive_namespace_class_state(fixture.context.store(), namespace.symbol, &class)
        else {
            panic!("the completed recursive class must retain its exact warm graph");
        };
        assert_ne!(state.instance, state.class_type);
        assert_ne!(state.namespace_type, state.class_type);
        for symbol in [class.class_symbol, class.class_local, class.variable_symbol] {
            assert_eq!(
                fixture
                    .context
                    .store()
                    .value_symbol_links(symbol)
                    .and_then(|links| links.resolved_type),
                Some(state.class_type),
            );
        }
        assert_eq!(
            fixture
                .context
                .store()
                .value_symbol_links(namespace.symbol)
                .and_then(|links| links.resolved_type),
            Some(state.namespace_type),
        );
        assert_eq!(
            fixture
                .context
                .store()
                .symbol(class.variable_symbol)
                .and_then(ts_binder::semantic::Symbol::parent),
            Some(class.class_symbol),
        );
        assert_eq!(
            fixture
                .context
                .store()
                .symbol_node_links(class.initializer)
                .and_then(|links| links.resolved_symbol),
            Some(class.class_symbol),
        );
        let static_side = fixture
            .context
            .store()
            .type_payload(state.class_type)
            .and_then(|record| record.data().structured())
            .unwrap();
        assert_eq!(
            static_side.properties.as_deref(),
            Some(&[class.variable_symbol, class.prototype][..]),
        );
        let [constructor] = static_side.signatures.as_deref().unwrap() else {
            panic!("the recursive static side must retain one constructor")
        };
        assert_eq!(
            fixture
                .context
                .store()
                .signature(*constructor)
                .and_then(super::super::signatures::Signature::resolved_return_type),
            Some(state.instance),
        );

        let warm = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().signature_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );
        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().signature_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn recursive_exported_namespace_classes_reject_private_and_unrelated_shapes() {
        for source in [
            concat!(
                "namespace M { ",
                "export class C { private static hidden = 1; } ",
                "export namespace C { export var C = M.C; } ",
                "}",
            ),
            concat!(
                "namespace M { ",
                "export class C {} ",
                "export namespace C { export var C = Other.C; } ",
                "}",
            ),
            concat!(
                "namespace M { ",
                "export class C {} ",
                "export namespace C { export var D = M.C; } ",
                "}",
            ),
            concat!(
                "namespace M { ",
                "export class C {} ",
                "export namespace C { var C = M.C; } ",
                "}",
            ),
            concat!(
                "namespace M { ",
                "export class C {} ",
                "export namespace C { export var C = M.Other; } ",
                "}",
            ),
        ] {
            let fixture = fixture(source, CanonicalModuleState::Script);
            let declaration = declaration(&fixture, 0);
            let (arena, bound) = fixture.context.file(fixture.file).unwrap();
            let before = (
                fixture.context.store().type_len(),
                fixture.context.store().signature_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            );

            assert!(
                matches!(
                    plan_source_namespace(arena, bound, fixture.context.store(), declaration),
                    Err(SourceCheckError::Unsupported(_))
                ),
                "{source}",
            );
            assert_eq!(
                (
                    fixture.context.store().type_len(),
                    fixture.context.store().signature_len(),
                    fixture.context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn recursive_exported_namespace_classes_reject_forged_owners_and_caches() {
        for poison_owner in [false, true] {
            let mut fixture = fixture(
                concat!(
                    "namespace M { ",
                    "export class C {} ",
                    "export namespace C { export var C = M.C; } ",
                    "}",
                ),
                CanonicalModuleState::Script,
            );
            let namespace = plan(&fixture, 0);
            let class = namespace.recursive_class.as_ref().unwrap().clone();
            if poison_owner {
                assert!(
                    fixture
                        .context
                        .store_mut_for_test()
                        .set_symbol_relationships(
                            class.variable_symbol,
                            None,
                            None,
                            Some(namespace.symbol),
                            None,
                        ),
                );
            } else {
                let wrong = fixture
                    .context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .string_type;
                assert!(fixture.context.store_mut_for_test().set_value_symbol_links(
                    class.variable_symbol,
                    ValueSymbolLinks {
                        resolved_type: Some(wrong),
                        ..ValueSymbolLinks::default()
                    },
                ));
            }
            let before = (
                fixture.context.store().type_len(),
                fixture.context.store().signature_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            );

            assert!(matches!(
                execute(&mut fixture, &namespace),
                Err(SourceCheckError::Unsupported(_))
            ));
            assert_eq!(
                (
                    fixture.context.store().type_len(),
                    fixture.context.store().signature_len(),
                    fixture.context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
            assert!(
                fixture
                    .context
                    .store()
                    .declared_type_links(class.class_symbol)
                    .is_none(),
            );
        }
    }

    #[test]
    fn recursive_exported_namespace_classes_check_source_and_replay_warm() {
        let mut fixture = fixture(
            concat!(
                "namespace M {\n",
                "  export class C {}\n",
                "  export namespace C {\n",
                "    export var C = M.C;\n",
                "  }\n",
                "}\n",
            ),
            CanonicalModuleState::Script,
        );

        fixture.context.check_source_file(fixture.file).unwrap();
        assert!(fixture.context.diagnostics().is_empty());
        let namespace = plan(&fixture, 0);
        let class = namespace.recursive_class.as_ref().unwrap();
        assert!(matches!(
            recursive_namespace_class_state(fixture.context.store(), namespace.symbol, class,),
            Some(RecursiveNamespaceClassCacheState::Warm(_)),
        ));
        let warm = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().signature_len(),
            fixture.context.store().checker_link_allocated_lengths(),
            fixture.context.diagnostics().len(),
        );

        fixture.context.recheck_source_file(fixture.file).unwrap();

        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().signature_len(),
                fixture.context.store().checker_link_allocated_lengths(),
                fixture.context.diagnostics().len(),
            ),
            warm,
        );
    }

    #[test]
    fn private_namespace_classes_report_unexported_qualified_bases_cold_and_warm() {
        let mut fixture = fixture(
            "namespace M { class C {} class D extends M.C {} }",
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [base, derived] = namespace.classes.as_slice() else {
            panic!("the namespace must retain both private classes")
        };
        let base_symbol = base.symbol;
        let derived_symbol = derived.symbol;
        let Some(SourceNamespaceClassHeritagePlan::MissingPrivateExport { property, .. }) =
            derived.heritage.as_ref()
        else {
            panic!("the derived class must retain its missing private export")
        };
        let property = *property;
        let qualified = fixture
            .parsed
            .arena
            .get(property.node)
            .and_then(|record| record.parent)
            .and_then(|parent| fixture.parsed.arena.get(parent))
            .expect("the private class name must retain its heritage expression");
        assert_eq!(qualified.kind, SyntaxKind::QualifiedName);

        let diagnostics = execute(&mut fixture, &namespace).unwrap();
        let [diagnostic] = diagnostics.as_slice() else {
            panic!("the private qualified base must produce one diagnostic")
        };
        assert_eq!(diagnostic.node, Some(property));
        assert_eq!(diagnostic.diagnostic.code(), PROPERTY_DOES_NOT_EXIST);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Property 'C' does not exist on type 'typeof M'.",
        );
        for symbol in [base_symbol, derived_symbol] {
            let type_ = fixture
                .context
                .store()
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .unwrap();
            assert!(
                fixture
                    .context
                    .store()
                    .type_payload(type_)
                    .unwrap()
                    .object_flags()
                    .contains(ObjectFlags::CLASS)
            );
            assert!(fixture.context.store().value_symbol_links(symbol).is_none());
        }

        let warm = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );
        let diagnostics = execute(&mut fixture, &namespace).unwrap();
        assert_eq!(diagnostics.len(), 1);
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
    fn private_namespace_classes_report_numeric_base_and_strict_field_in_order() {
        let mut options = CanonicalCheckerOptions::default();
        options.intrinsic.strict_null_checks = true;
        options.strict_property_initialization = true;
        let mut fixture = fixture_with_options(
            "namespace Foo { var A = 1; class B extends A { b: string; } }",
            CanonicalModuleState::Script,
            options,
        );
        let namespace = plan(&fixture, 0);
        let [class] = namespace.classes.as_slice() else {
            panic!("the namespace must retain its private derived class")
        };
        let class_symbol = class.symbol;
        let property = class.property.as_ref().unwrap().clone();
        let Some(SourceNamespaceClassHeritagePlan::NonConstructorVariable { expression, symbol }) =
            class.heritage.as_ref()
        else {
            panic!("the class must retain its numeric local base")
        };
        let expression = *expression;
        let base_symbol = *symbol;

        let diagnostics = execute(&mut fixture, &namespace).unwrap();
        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [TYPE_IS_NOT_A_CONSTRUCTOR, PROPERTY_HAS_NO_INITIALIZER],
        );
        assert_eq!(diagnostics.as_slice()[0].node, Some(expression));
        assert_eq!(diagnostics.as_slice()[1].node, Some(property.name));
        assert_eq!(
            diagnostics.as_slice()[0].diagnostic.render().unwrap(),
            "Type 'number' is not a constructor function type.",
        );
        assert_eq!(
            diagnostics.as_slice()[1].diagnostic.render().unwrap(),
            "Property 'b' has no initializer and is not definitely assigned in the constructor.",
        );
        let bootstrap = fixture.context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(
            fixture
                .context
                .store()
                .value_symbol_links(base_symbol)
                .and_then(|links| links.resolved_type),
            Some(bootstrap.number_type),
        );
        assert_eq!(
            fixture
                .context
                .store()
                .value_symbol_links(property.symbol)
                .and_then(|links| links.resolved_type),
            Some(bootstrap.string_type),
        );
        assert!(
            fixture
                .context
                .store()
                .declared_type_links(class_symbol)
                .and_then(|links| links.declared_type)
                .is_some()
        );

        let warm = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );
        assert_eq!(execute(&mut fixture, &namespace).unwrap().len(), 2);
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
    fn private_namespace_class_fields_follow_strict_initialization_options() {
        for (strict_null_checks, strict_property_initialization, expected) in [
            (false, false, 1),
            (true, false, 1),
            (false, true, 1),
            (true, true, 2),
        ] {
            let mut options = CanonicalCheckerOptions::default();
            options.intrinsic.strict_null_checks = strict_null_checks;
            options.strict_property_initialization = strict_property_initialization;
            let mut fixture = fixture_with_options(
                "namespace Foo { var A = 1; class B extends A { b: string; } }",
                CanonicalModuleState::Script,
                options,
            );
            let namespace = plan(&fixture, 0);

            assert_eq!(execute(&mut fixture, &namespace).unwrap().len(), expected);
        }
    }

    #[test]
    fn private_namespace_class_diagnostics_preserve_earlier_top_level_class_order() {
        let mut options = CanonicalCheckerOptions::default();
        options.intrinsic.strict_null_checks = true;
        options.strict_property_initialization = true;
        let mut fixture = fixture_with_options(
            "class A { a: number; } namespace Foo { var A = 1; class B extends A { b: string; } }",
            CanonicalModuleState::Script,
            options,
        );

        fixture.context.check_source_file(fixture.file).unwrap();

        assert_eq!(
            fixture
                .context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [
                PROPERTY_HAS_NO_INITIALIZER,
                TYPE_IS_NOT_A_CONSTRUCTOR,
                PROPERTY_HAS_NO_INITIALIZER,
            ],
        );
    }

    #[test]
    fn forged_namespace_class_plans_fail_before_publication() {
        let mut fixture = fixture(
            "namespace M { class C {} class D extends M.C {} }",
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let mut forged = namespace.clone();
        forged.classes[0].symbol = namespace.symbol;
        let before = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );

        assert!(matches!(
            execute(&mut fixture, &forged),
            Err(SourceCheckError::Unsupported(_))
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
    fn namespace_classes_reject_exported_generic_and_unsupported_shapes() {
        for source in [
            "namespace M { export class C {} }",
            "namespace M { class C<T> {} }",
            "namespace M { class C { value: string; } }",
            "namespace M { class C {} class D extends C {} }",
            "namespace M { class C {} class D extends Other.C {} }",
            "namespace M { class C {} class D extends M.Unknown {} }",
        ] {
            let fixture = fixture(source, CanonicalModuleState::Script);
            let declaration = declaration(&fixture, 0);
            let (arena, bound) = fixture.context.file(fixture.file).unwrap();

            assert!(matches!(
                plan_source_namespace(arena, bound, fixture.context.store(), declaration),
                Err(SourceCheckError::Unsupported(_))
            ));
        }
    }

    #[test]
    fn ambient_react_classes_preserve_merged_interfaces_and_cold_values() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare namespace React { ",
                "interface Lifecycle<P, S, SS> {} ",
                "interface Component<P = {}, S = {}, SS = any> ",
                "extends Lifecycle<P, S, SS> {} ",
                "class Component<P, S> { ",
                "constructor(props: P); ",
                "constructor(props: P, context?: any); ",
                "setState<K extends keyof S>(",
                "state: ((previous: S) => K) | K, callback?: () => void",
                "): void; ",
                "readonly props: { children?: P }; ",
                "refs: { [key: string]: P }; ",
                "} ",
                "class PureComponent<P = {}, S = {}, SS = any> ",
                "extends Component<P, S, SS> {} ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface { .. },
            SourceNamespaceMemberPlan::Interface {
                symbol: merged_interface,
                ..
            },
            SourceNamespaceMemberPlan::DeferredAmbientClass {
                declaration: component_declaration,
                symbol: component,
                type_parameters: component_parameters,
                members: component_members,
                annotations: component_annotations,
            },
            SourceNamespaceMemberPlan::DeferredAmbientClass {
                declaration: pure_declaration,
                symbol: pure,
                type_parameters: pure_parameters,
                members: pure_members,
                annotations: pure_annotations,
            },
        ] = namespace.members.as_slice()
        else {
            panic!("React must retain its merged component and generic derived class")
        };
        let component_declaration = *component_declaration;
        let component = *component;
        let pure_declaration = *pure_declaration;
        let pure = *pure;
        assert_eq!(*merged_interface, component);
        assert_eq!(component_parameters.len(), 2);
        assert_eq!(component_members.len(), 5);
        assert_eq!(component_members[0], component_members[1]);
        assert_eq!(pure_parameters.len(), 3);
        assert!(pure_members.is_empty());
        assert!(component_annotations.iter().any(|annotation| {
            fixture.parsed.arena.get(annotation.node).unwrap().kind == SyntaxKind::FunctionType
        }));
        assert!(pure_annotations.iter().any(|annotation| {
            fixture.parsed.arena.get(annotation.node).unwrap().kind
                == SyntaxKind::ExpressionWithTypeArguments
        }));
        let bound = fixture.context.file(fixture.file).unwrap().1;
        assert_eq!(bound.symbol(component_declaration), Some(component));
        assert_eq!(bound.symbol(pure_declaration), Some(pure));
        assert_eq!(
            fixture.context.store().symbol(component).unwrap().flags(),
            SymbolFlags::CLASS | SymbolFlags::INTERFACE,
        );
        assert_eq!(
            fixture.context.store().get_parent_of_symbol(component),
            Some(namespace.symbol),
        );
        assert!(
            fixture
                .context
                .store()
                .value_symbol_links(component)
                .is_none()
        );
        assert!(fixture.context.store().value_symbol_links(pure).is_none());

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        assert!(
            fixture
                .context
                .store()
                .value_symbol_links(component)
                .is_none()
        );
        assert!(fixture.context.store().value_symbol_links(pure).is_none());
        assert!(fixture.context.store().declared_type_links(pure).is_none());

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
    fn reopened_ambient_namespaces_accept_canonical_class_parents() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare namespace React { interface Marker {} } ",
                "declare namespace React { class Component<T> { value: T; } }",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 1);
        let [SourceNamespaceMemberPlan::DeferredAmbientClass { symbol, .. }] =
            namespace.members.as_slice()
        else {
            panic!("the reopened namespace must retain its ambient class")
        };
        assert_eq!(
            fixture.context.store().get_parent_of_symbol(*symbol),
            Some(namespace.symbol),
        );
        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
    }

    #[test]
    fn unsupported_ambient_class_namespace_merges_do_not_become_fatal_invariants() {
        let fixture = declaration_fixture(
            concat!(
                "declare namespace React { ",
                "class Component<T> {} ",
                "namespace Component { export interface Marker {} } ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = declaration(&fixture, 0);
        let (arena, bound) = fixture.context.file(fixture.file).unwrap();
        let before = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );

        assert!(matches!(
            plan_source_namespace(arena, bound, fixture.context.store(), namespace),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Syntax {
                    kind: SyntaxKind::ClassDeclaration,
                    role: SourceSyntaxRole::Statement,
                    ..
                }
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
    fn exported_ambient_generic_classes_stay_unmaterialized() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module \"react\" { ",
                "export class Component<P, S> { ",
                "constructor(props: P); ",
                "render(): P; ",
                "readonly state: S; ",
                "} ",
                "export class PureComponent<P = {}, S = {}> ",
                "extends Component<P, S> {} ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::DeferredAmbientClass {
                declaration,
                symbol,
                type_parameters,
                members,
                ..
            },
            SourceNamespaceMemberPlan::DeferredAmbientClass {
                symbol: derived, ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("exported ambient classes must remain checked declarations")
        };
        let declaration = *declaration;
        let symbol = *symbol;
        let derived = *derived;
        assert_eq!(type_parameters.len(), 2);
        assert_eq!(members.len(), 3);
        let local = fixture
            .context
            .file(fixture.file)
            .unwrap()
            .1
            .local_symbol(declaration)
            .unwrap();
        assert_eq!(
            fixture
                .context
                .store()
                .symbol(local)
                .unwrap()
                .export_symbol(),
            Some(symbol),
        );
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
        for owner in [symbol, derived] {
            assert!(fixture.context.store().value_symbol_links(owner).is_none());
            assert!(fixture.context.store().declared_type_links(owner).is_none());
        }

        let bound = fixture.context.file(fixture.file).unwrap().1;
        let host = DeclaredTypeHost::new([(&fixture.parsed.arena, bound)]).unwrap();
        assert!(
            super::super::classes::plan_nongeneric_class(fixture.context.store(), &host, symbol)
                .is_err()
        );
    }

    #[test]
    fn deferred_ambient_classes_reject_forged_member_identity_before_writes() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module \"react\" { ",
                "export class Component<P> { ",
                "constructor(props: P); ",
                "render(): P; ",
                "} ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let mut forged = namespace.clone();
        let SourceNamespaceMemberPlan::DeferredAmbientClass {
            symbol, members, ..
        } = &mut forged.members[0]
        else {
            panic!("the ambient class must retain its checked members")
        };
        members[0] = *symbol;
        let before = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );

        assert!(matches!(
            execute(&mut fixture, &forged),
            Err(SourceCheckError::Unsupported(_))
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
    fn strict_namespace_arguments_keep_binder_diagnostics_and_warm_callable_state() {
        let source = "namespace Values { export function read() { var arguments = []; } }";
        let mut fixture = fixture_with_strict_source_facts(
            source,
            CanonicalModuleState::Script,
            CanonicalCheckerOptions::default(),
            false,
            true,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Function {
                declaration: function_declaration,
                symbol,
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the diagnosed namespace function must retain its callable plan")
        };
        let function_declaration = *function_declaration;
        let symbol = *symbol;
        let (_, bound) = fixture.context.file(fixture.file).unwrap();
        let [diagnostic] = bound.diagnostics() else {
            panic!("the strict argument must retain exactly one binder diagnostic")
        };
        assert_eq!(diagnostic.diagnostic.code(), 1100);
        assert_eq!(diagnostic.diagnostic.arguments, ["arguments"]);
        let argument = bound
            .locals(function_declaration)
            .and_then(|locals| fixture.context.store().symbol_table(locals))
            .and_then(|locals| locals.get_source("arguments"))
            .unwrap();

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        assert!(
            fixture
                .context
                .store()
                .value_symbol_links(argument)
                .is_none()
        );
        assert!(
            fixture
                .context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type)
                .is_some()
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
    fn strict_namespace_arguments_reject_unproven_nonempty_bodies() {
        for (invalid, always_strict) in [
            (
                "namespace Values { export function read() { var arguments = []; } }",
                false,
            ),
            (
                "namespace Values { export function read() { var arguments = [1]; } }",
                true,
            ),
            (
                "namespace Values { export function read() { var arguments = []; var other = 1; } }",
                true,
            ),
        ] {
            let fixture = fixture_with_strict_source_facts(
                invalid,
                CanonicalModuleState::Script,
                CanonicalCheckerOptions::default(),
                false,
                always_strict,
            );
            let declaration = declaration(&fixture, 0);
            let (arena, bound) = fixture.context.file(fixture.file).unwrap();
            assert!(
                matches!(
                    plan_source_namespace(arena, bound, fixture.context.store(), declaration),
                    Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Syntax {
                            kind: SyntaxKind::FunctionDeclaration,
                            role: SourceSyntaxRole::FunctionDeclaration,
                            ..
                        }
                    ))
                ),
                "{invalid}"
            );
        }
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
    fn ambient_namespace_functions_publish_annotated_and_generic_signatures() {
        for (source, parameters, type_parameters) in [
            (
                "declare module \"lib\" { export function fn(): string; }",
                0,
                0,
            ),
            (
                "declare module \"lib\" { export function fn(value: string): void; }",
                1,
                0,
            ),
            (
                "declare module \"lib\" { export function fn<T>(value: T): T; }",
                1,
                1,
            ),
        ] {
            let mut fixture = declaration_fixture(source, CanonicalModuleState::Script);
            let namespace = plan(&fixture, 0);
            let [SourceNamespaceMemberPlan::Function { symbol, .. }] = namespace.members.as_slice()
            else {
                panic!("the namespace must retain its annotated function: {source}")
            };
            let symbol = *symbol;

            assert!(execute(&mut fixture, &namespace).unwrap().is_empty());

            let callable = fixture
                .context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let signature = fixture
                .context
                .store()
                .source_callable_provenance(callable)
                .and_then(|provenance| fixture.context.store().signature(provenance.signature))
                .unwrap();
            assert_eq!(signature.parameters().len(), parameters, "{source}");
            assert_eq!(
                signature.type_parameters().len(),
                type_parameters,
                "{source}"
            );
        }
    }

    #[test]
    fn ambient_generic_constructor_functions_remain_checked_and_unmaterialized() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module \"prop-types\" { ",
                "export interface Requireable<T> {} ",
                "export function instanceOf<T>(",
                "expectedClass: new (...args: any[]) => T",
                "): Requireable<T>; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface { .. },
            SourceNamespaceMemberPlan::DeferredAmbientFunction {
                declaration,
                symbol,
                type_parameters,
                parameters,
                annotations,
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the constructor function must retain its checked ambient declaration")
        };
        let declaration = *declaration;
        let symbol = *symbol;
        let type_parameters = type_parameters.clone();
        let parameters = parameters.clone();
        let annotations = annotations.clone();
        let (arena, bound) = fixture.context.file(fixture.file).unwrap();
        let local = bound.local_symbol(declaration).unwrap();

        assert_eq!(type_parameters.len(), 1);
        assert_eq!(parameters.len(), 1);
        assert_eq!(
            annotations
                .iter()
                .map(|annotation| arena.get(annotation.node).unwrap().kind)
                .collect::<Vec<_>>(),
            [
                SyntaxKind::ConstructorType,
                SyntaxKind::ArrayType,
                SyntaxKind::TypeReference,
                SyntaxKind::TypeReference,
            ],
        );
        assert_eq!(
            fixture.context.store().get_parent_of_symbol(symbol),
            Some(namespace.symbol),
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
        assert!(fixture.context.store().value_symbol_links(symbol).is_none());
        assert!(
            fixture
                .context
                .store()
                .source_callable_type_for_owner(symbol)
                .is_none()
        );

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        assert!(fixture.context.store().value_symbol_links(symbol).is_none());
        assert!(annotations.iter().all(|annotation| {
            fixture
                .context
                .store()
                .type_node_links(*annotation)
                .is_none()
        }));

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

        let bound = fixture.context.file(fixture.file).unwrap().1;
        let host = DeclaredTypeHost::new([(&fixture.parsed.arena, bound)]).unwrap();
        let callable = source_callables::plan_source_callable(
            fixture.context.store(),
            &host,
            declaration,
            symbol,
            None,
        )
        .expect("the deferred constructor function retains an authenticated source signature");
        assert_eq!(callable.type_parameters.len(), 1);
        assert_eq!(callable.parameters.len(), 1);
        assert!(fixture.context.store().value_symbol_links(symbol).is_none());
    }

    #[test]
    fn ambient_generic_callback_functions_remain_checked_and_unmaterialized() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare namespace React { ",
                "interface Context<T> {} ",
                "function createContext<T>(",
                "defaultValue: T, ",
                "calculateChangedBits?: (prev: T, next: T) => number",
                "): Context<T>; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface { .. },
            SourceNamespaceMemberPlan::DeferredAmbientFunction {
                symbol,
                type_parameters,
                parameters,
                annotations,
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the callback function must retain its checked ambient declaration")
        };
        let symbol = *symbol;
        assert_eq!(type_parameters.len(), 1);
        assert_eq!(parameters.len(), 2);
        assert!(annotations.iter().any(|annotation| {
            fixture.parsed.arena.get(annotation.node).unwrap().kind == SyntaxKind::FunctionType
        }));

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        assert!(fixture.context.store().value_symbol_links(symbol).is_none());

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
    fn ambient_generic_type_predicates_remain_checked_and_unmaterialized() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare namespace React { ",
                "interface ReactElement<T> {} ",
                "function isValidElement<T>(",
                "value: {} | null | undefined",
                "): value is ReactElement<T>; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface { .. },
            SourceNamespaceMemberPlan::DeferredAmbientFunction {
                symbol,
                type_parameters,
                parameters,
                annotations,
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the type predicate must retain its checked ambient declaration")
        };
        let symbol = *symbol;
        assert_eq!(type_parameters.len(), 1);
        assert_eq!(parameters.len(), 1);
        assert!(annotations.iter().any(|annotation| {
            fixture.parsed.arena.get(annotation.node).unwrap().kind == SyntaxKind::TypePredicate
        }));

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        assert!(fixture.context.store().value_symbol_links(symbol).is_none());

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
    fn ambient_generic_functions_validate_constraints_and_mapped_returns() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module \"prop-types\" { ",
                "export interface Validator<T> {} ",
                "export interface Requireable<T> {} ",
                "export function objectOf<T extends Validator<any>>(",
                "type: Validator<T>",
                "): Requireable<{ [K in keyof any]: T }>; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface { .. },
            SourceNamespaceMemberPlan::Interface { .. },
            SourceNamespaceMemberPlan::DeferredAmbientFunction {
                declaration,
                symbol,
                type_parameters,
                parameters,
                annotations,
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the mapped return must retain its checked generic declaration")
        };
        let declaration = *declaration;
        let symbol = *symbol;
        let annotations = annotations.clone();
        let (arena, bound) = fixture.context.file(fixture.file).unwrap();

        assert_eq!(type_parameters.len(), 1);
        assert_eq!(parameters.len(), 1);
        assert!(annotations.iter().any(|annotation| {
            arena.get(annotation.node).unwrap().kind == SyntaxKind::TypeOperator
        }));
        let mapped = arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::MappedType).then_some(NodeRef::new(
                    arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let NodeData::MappedTypeNode(mapped_type) = &arena.get(mapped.node).unwrap().data else {
            panic!("the return annotation must contain a mapped type")
        };
        let mapped_parameter = child(mapped, mapped_type.type_parameter);
        let mapped_symbol = bound.symbol(mapped_parameter).unwrap();
        assert_eq!(
            fixture
                .context
                .store()
                .symbol(mapped_symbol)
                .unwrap()
                .flags(),
            SymbolFlags::TYPE_PARAMETER,
        );

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        assert!(fixture.context.store().value_symbol_links(symbol).is_none());
        assert!(
            fixture
                .context
                .store()
                .source_callable_type_for_declaration(declaration)
                .is_none()
        );
    }

    #[test]
    fn ambient_namespace_overloads_retain_binder_order_without_publication() {
        for source in [
            concat!(
                "declare namespace React { ",
                "function createFactory<T extends object>(value: T): T; ",
                "function createFactory(value: string): string; ",
                "function createFactory(...children: string[]): string; ",
                "}",
            ),
            concat!(
                "declare module \"react\" { ",
                "export function createFactory<T extends object>(value: T): T; ",
                "export function createFactory(value: string): string; ",
                "export function createFactory(...children: string[]): string; ",
                "}",
            ),
        ] {
            let mut fixture = declaration_fixture(source, CanonicalModuleState::Script);
            let namespace = plan(&fixture, 0);
            let mut declarations = Vec::new();
            let mut owner = None;
            for (index, member) in namespace.members.iter().enumerate() {
                let SourceNamespaceMemberPlan::DeferredAmbientFunction {
                    declaration,
                    symbol,
                    type_parameters,
                    parameters,
                    ..
                } = member
                else {
                    panic!("every overload must remain an authenticated ambient declaration")
                };
                assert_eq!(type_parameters.len(), usize::from(index == 0), "{source}");
                assert_eq!(parameters.len(), 1, "{source}");
                declarations.push(*declaration);
                if let Some(expected) = owner {
                    assert_eq!(*symbol, expected, "{source}");
                } else {
                    owner = Some(*symbol);
                }
            }
            let owner = owner.unwrap();
            assert_eq!(
                fixture
                    .context
                    .store()
                    .symbol(owner)
                    .unwrap()
                    .declarations(),
                Some(declarations.as_slice()),
                "{source}",
            );
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
                "{source}",
            );
            assert!(fixture.context.store().value_symbol_links(owner).is_none());
        }
    }

    #[test]
    fn deferred_ambient_functions_reject_forged_parameter_identity_before_writes() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module \"prop-types\" { ",
                "export interface Requireable<T> {} ",
                "export function instanceOf<T>(",
                "expectedClass: new (...args: any[]) => T",
                "): Requireable<T>; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let mut forged = namespace.clone();
        let SourceNamespaceMemberPlan::DeferredAmbientFunction {
            type_parameters,
            parameters,
            ..
        } = &mut forged.members[1]
        else {
            panic!("the constructor function must remain deferred")
        };
        parameters[0] = type_parameters[0];
        let before = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );

        assert!(matches!(
            execute(&mut fixture, &forged),
            Err(SourceCheckError::Unsupported(_))
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
    fn ambient_namespace_functions_are_implicitly_exported() {
        let mut fixture = declaration_fixture(
            "declare module \"lib\" { function read(value: string): string; }",
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
            panic!("the ambient namespace must retain its implicitly exported function")
        };
        let declaration = *declaration;
        let symbol = *symbol;
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
        let signature = fixture
            .context
            .store()
            .source_callable_provenance(callable)
            .and_then(|provenance| fixture.context.store().signature(provenance.signature))
            .unwrap();
        assert_eq!(signature.parameters().len(), 1);
        assert!(signature.type_parameters().is_empty());

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
    fn ambient_namespace_functions_reject_missing_returns_and_nondeclaration_files() {
        let missing_return = declaration_fixture(
            "declare module \"lib\" { export function fn(); }",
            CanonicalModuleState::Script,
        );
        let missing_declaration = declaration(&missing_return, 0);
        let (arena, bound) = missing_return.context.file(missing_return.file).unwrap();
        let before = missing_return
            .context
            .store()
            .checker_link_allocated_lengths();

        assert!(matches!(
            plan_source_namespace(
                arena,
                bound,
                missing_return.context.store(),
                missing_declaration,
            ),
            Err(SourceCheckError::Unsupported(_))
        ));
        assert_eq!(
            missing_return
                .context
                .store()
                .checker_link_allocated_lengths(),
            before,
        );

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
    fn ambient_generic_namespace_aliases_keep_mapped_inferred_and_intersection_types_cold() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module 'prop-types' { ",
                "export interface Validator<T> {} ",
                "export type InferType<V> = V extends Validator<infer T> ? T : never; ",
                "export type RequiredKeys<V> = ",
                "{ [K in keyof V]: V[K] extends Validator<infer T> ? T : never }[keyof V]; ",
                "export type InferPropsInner<V> = { [K in keyof V]: InferType<V[K]> }; ",
                "export type InferProps<V> = InferPropsInner<V> & InferPropsInner<V>; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let aliases = namespace
            .members
            .iter()
            .filter_map(|member| match member {
                SourceNamespaceMemberPlan::TypeAlias {
                    declaration,
                    symbol,
                    annotation,
                    deferred,
                    ..
                } => Some((*declaration, *symbol, *annotation, *deferred)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(aliases.len(), 4);
        let exports = fixture
            .context
            .store()
            .symbol(namespace.symbol)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| fixture.context.store().symbol_table(exports))
            .unwrap();
        for (declaration, symbol, annotation, deferred) in &aliases {
            let owner = fixture.context.store().symbol(*symbol).unwrap();
            assert!(*deferred, "{:?}", owner.name());
            assert_eq!(exports.get(owner.name()), Some(*symbol));
            assert_eq!(owner.declarations(), Some(&[*declaration][..]));
            assert!(fixture.context.store().type_alias_links(*symbol).is_none());
            assert!(
                fixture
                    .context
                    .store()
                    .type_node_links(*annotation)
                    .is_none()
            );
        }

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        for (_, symbol, annotation, _) in &aliases {
            assert!(fixture.context.store().type_alias_links(*symbol).is_none());
            assert!(
                fixture
                    .context
                    .store()
                    .type_node_links(*annotation)
                    .is_none()
            );
        }

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
    fn ambient_module_private_generic_aliases_keep_their_local_owners_cold_and_warm() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module 'react' { ",
                "export = React; ",
                "namespace React { interface Element {} } ",
                "type MergePropTypes<Props, Inferred> = Props & Inferred; ",
                "type Defaultize<Props, Defaults> = Props | Defaults; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let locals = fixture
            .context
            .file(fixture.file)
            .and_then(|(_, bound)| bound.locals(namespace.declaration))
            .and_then(|locals| fixture.context.store().symbol_table(locals))
            .unwrap();
        let exports = fixture
            .context
            .store()
            .symbol(namespace.symbol)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| fixture.context.store().symbol_table(exports))
            .unwrap();
        let aliases = namespace
            .members
            .iter()
            .filter_map(|member| match member {
                SourceNamespaceMemberPlan::TypeAlias {
                    declaration,
                    symbol,
                    annotation,
                    deferred,
                    ..
                } => Some((*declaration, *symbol, *annotation, *deferred)),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(aliases.len(), 2);
        for (declaration, symbol, annotation, deferred) in &aliases {
            let owner = fixture.context.store().symbol(*symbol).unwrap();
            assert!(*deferred, "{:?}", owner.name());
            assert!(owner.parent().is_none());
            assert_eq!(owner.declarations(), Some(&[*declaration][..]));
            assert_eq!(locals.get(owner.name()), Some(*symbol));
            assert!(exports.get(owner.name()).is_none());
            assert!(fixture.context.store().type_alias_links(*symbol).is_none());
            assert!(
                fixture
                    .context
                    .store()
                    .type_node_links(*annotation)
                    .is_none()
            );
        }

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        for (_, symbol, annotation, _) in &aliases {
            assert!(fixture.context.store().type_alias_links(*symbol).is_none());
            assert!(
                fixture
                    .context
                    .store()
                    .type_node_links(*annotation)
                    .is_none()
            );
        }
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
    fn ambient_module_private_generic_aliases_reject_forged_ownership() {
        for mutation in 0..3 {
            let mut fixture = declaration_fixture(
                concat!(
                    "declare module 'react' { ",
                    "export = React; ",
                    "namespace React { interface Element {} } ",
                    "type MergePropTypes<Props, Inferred> = Props & Inferred; ",
                    "}",
                ),
                CanonicalModuleState::Script,
            );
            let namespace = plan(&fixture, 0);
            let (alias_declaration, symbol) = namespace
                .members
                .iter()
                .find_map(|member| match member {
                    SourceNamespaceMemberPlan::TypeAlias {
                        declaration,
                        symbol,
                        deferred,
                        ..
                    } => {
                        assert!(*deferred);
                        Some((*declaration, *symbol))
                    }
                    _ => None,
                })
                .unwrap();
            let locals = fixture
                .context
                .file(fixture.file)
                .and_then(|(_, bound)| bound.locals(namespace.declaration))
                .unwrap();
            let exports = fixture
                .context
                .store()
                .symbol(namespace.symbol)
                .and_then(ts_binder::semantic::Symbol::exports)
                .unwrap();
            let store = fixture.context.store_mut_for_test();
            match mutation {
                0 => assert!(store.set_symbol_relationships(
                    symbol,
                    None,
                    None,
                    Some(namespace.symbol),
                    None,
                )),
                1 => assert_eq!(
                    store.insert_symbol(
                        locals,
                        EscapedName::source("MergePropTypes"),
                        namespace.symbol,
                    ),
                    Some(Some(symbol)),
                ),
                2 => assert_eq!(
                    store.insert_symbol(exports, EscapedName::source("MergePropTypes"), symbol),
                    Some(None),
                ),
                _ => unreachable!(),
            }
            let before = (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            );
            let root = declaration(&fixture, 0);
            let (arena, bound) = fixture.context.file(fixture.file).unwrap();

            assert!(matches!(
                plan_source_namespace(arena, bound, fixture.context.store(), root),
                Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::MissingDeclarationSymbol(node),
                )) if node == alias_declaration
            ));
            assert!(fixture.context.store().type_alias_links(symbol).is_none());
            assert_eq!(
                (
                    fixture.context.store().type_len(),
                    fixture.context.store().symbol_len(),
                    fixture.context.store().checker_link_allocated_lengths(),
                ),
                before,
                "mutation {mutation}",
            );
        }
    }

    #[test]
    fn source_check_keeps_unreferenced_ambient_generic_aliases_cold() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module 'prop-types' { ",
                "export type InferProps<V = string> = V & V; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::TypeAlias {
                symbol,
                annotation,
                deferred,
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the declaration module must retain its generic alias")
        };
        let symbol = *symbol;
        let annotation = *annotation;
        assert!(*deferred);
        let before = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
        );

        fixture.context.check_source_file(fixture.file).unwrap();

        assert!(fixture.context.store().type_alias_links(symbol).is_none());
        assert!(
            fixture
                .context
                .store()
                .type_node_links(annotation)
                .is_none()
        );
        assert_eq!(
            (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
            ),
            before,
        );
    }

    #[test]
    fn ambient_generic_namespace_aliases_materialize_when_an_export_uses_them() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module 'prop-types' { ",
                "export type Value<T> = T; ",
                "export const value: Value<string>; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::TypeAlias {
                symbol: alias,
                deferred,
                ..
            },
            SourceNamespaceMemberPlan::AmbientVariable { symbol: value, .. },
        ] = namespace.members.as_slice()
        else {
            panic!("the declaration module must retain its alias and typed export")
        };
        let alias = *alias;
        let value = *value;
        assert!(*deferred);
        assert!(fixture.context.store().type_alias_links(alias).is_none());

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        assert!(
            fixture
                .context
                .store()
                .type_alias_links(alias)
                .and_then(|links| links.declared_type)
                .is_some()
        );
        assert_eq!(
            fixture
                .context
                .store()
                .value_symbol_links(value)
                .and_then(|links| links.resolved_type),
            Some(
                fixture
                    .context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .string_type
            ),
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
    fn ambient_generic_namespace_aliases_reject_forged_owner_and_parameter_symbols() {
        for mutation in 0..4 {
            let mut fixture = declaration_fixture(
                "declare module 'prop-types' { export type Value<T> = T; }",
                CanonicalModuleState::Script,
            );
            let namespace = plan(&fixture, 0);
            let [
                SourceNamespaceMemberPlan::TypeAlias {
                    declaration: alias_declaration,
                    symbol,
                    deferred,
                    ..
                },
            ] = namespace.members.as_slice()
            else {
                panic!("the declaration module must retain its generic alias")
            };
            assert!(*deferred);
            let alias_declaration = *alias_declaration;
            let symbol = *symbol;
            let NodeData::TypeAliasDeclaration(alias) = &fixture
                .parsed
                .arena
                .get(alias_declaration.node)
                .unwrap()
                .data
            else {
                panic!("the alias symbol must retain its declaration")
            };
            let parameter = child(
                alias_declaration,
                alias.type_parameters.as_ref().unwrap().nodes[0],
            );
            let parameter_symbol = fixture
                .context
                .file(fixture.file)
                .unwrap()
                .1
                .symbol(parameter)
                .unwrap();
            let expected = if mutation < 2 {
                alias_declaration
            } else {
                parameter
            };
            let store = fixture.context.store_mut_for_test();
            match mutation {
                0 => assert!(store.set_symbol_flags(
                    symbol,
                    SymbolFlags::TYPE_ALIAS | SymbolFlags::PROPERTY,
                    CheckFlags::NONE,
                )),
                1 => assert!(store.set_symbol_relationships(symbol, None, None, None, None)),
                2 => assert!(store.set_symbol_flags(
                    parameter_symbol,
                    SymbolFlags::TYPE_PARAMETER | SymbolFlags::PROPERTY,
                    CheckFlags::NONE,
                )),
                3 => assert!(store.set_symbol_relationships(
                    parameter_symbol,
                    None,
                    None,
                    Some(symbol),
                    None,
                )),
                _ => unreachable!(),
            }
            let before = (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            );
            let root = declaration(&fixture, 0);
            let (arena, bound) = fixture.context.file(fixture.file).unwrap();

            assert!(matches!(
                plan_source_namespace(arena, bound, fixture.context.store(), root),
                Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::MissingDeclarationSymbol(node),
                )) if node == expected
            ));
            assert!(fixture.context.store().type_alias_links(symbol).is_none());
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

    #[test]
    fn ambient_generic_namespace_aliases_do_not_hide_missing_type_names() {
        for (source, expected_parameter_annotations) in [
            (
                "declare module 'prop-types' { export type Broken<T> = Missing<T>; }",
                0,
            ),
            (
                "declare module 'prop-types' { export type Broken<T extends Missing> = T; }",
                1,
            ),
            (
                "declare module 'prop-types' { export type Broken<T = Missing> = T; }",
                1,
            ),
        ] {
            let mut fixture = declaration_fixture(source, CanonicalModuleState::Script);
            let namespace = plan(&fixture, 0);
            let [
                SourceNamespaceMemberPlan::TypeAlias {
                    symbol,
                    deferred,
                    parameter_annotations,
                    ..
                },
            ] = namespace.members.as_slice()
            else {
                panic!("the declaration module must retain its unresolved generic alias")
            };
            let symbol = *symbol;
            assert!(!*deferred, "{source}");
            assert_eq!(
                parameter_annotations.len(),
                expected_parameter_annotations,
                "{source}",
            );
            let before = (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            );

            assert!(
                matches!(
                    execute(&mut fixture, &namespace),
                    Err(SourceCheckError::DeclaredType(
                        DeclaredTypeError::TypeNodeUnavailable(
                            TypeNodeUnavailable::MissingTypeReference(_)
                        )
                    ))
                ),
                "{source}",
            );
            assert!(fixture.context.store().type_alias_links(symbol).is_none());
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

    #[test]
    fn source_check_reports_missing_ambient_generic_alias_defaults_before_publication() {
        let mut fixture = declaration_fixture(
            "declare module 'prop-types' { export type Broken<T = Missing> = T; }",
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::TypeAlias {
                symbol,
                deferred,
                parameter_annotations,
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the declaration module must retain its generic alias")
        };
        let symbol = *symbol;
        assert!(!*deferred);
        let [default] = parameter_annotations.as_slice() else {
            panic!("the generic alias must retain its missing default annotation")
        };
        let default = *default;
        let before = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );

        assert!(matches!(
            fixture.context.check_source_file(fixture.file),
            Err(SourceCheckError::DeclaredType(
                DeclaredTypeError::TypeNodeUnavailable(TypeNodeUnavailable::MissingTypeReference(
                    node,
                ))
            )) if node == default
        ));
        assert!(fixture.context.store().type_alias_links(symbol).is_none());
        assert!(fixture.context.store().type_node_links(default).is_none());
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
    fn ambient_generic_namespace_aliases_keep_invalid_reference_arity_eager() {
        let fixture = declaration_fixture(
            concat!(
                "declare module 'prop-types' { ",
                "export type Value<T> = T; ",
                "export type Broken<T> = Value<T, T>; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::TypeAlias {
                deferred: valid, ..
            },
            SourceNamespaceMemberPlan::TypeAlias {
                deferred: invalid, ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the declaration module must retain both generic aliases")
        };

        assert!(*valid);
        assert!(!*invalid);
    }

    #[test]
    fn ambient_generic_namespace_aliases_reject_invalid_cached_metadata() {
        let mut fixture = declaration_fixture(
            "declare module 'prop-types' { export type Value<T> = T; }",
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::TypeAlias {
                symbol, deferred, ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the declaration module must retain its generic alias")
        };
        let symbol = *symbol;
        assert!(*deferred);
        let string = fixture
            .context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .string_type;
        assert!(fixture.context.store_mut_for_test().set_type_alias_links(
            symbol,
            TypeAliasLinks {
                declared_type: Some(string),
                ..TypeAliasLinks::default()
            },
        ));
        let before = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );

        assert!(matches!(
            execute(&mut fixture, &namespace),
            Err(SourceCheckError::DeclaredType(
                DeclaredTypeError::TypeNodeUnavailable(TypeNodeUnavailable::InvalidCachedTypeAlias(
                    alias,
                ))
            )) if alias == symbol
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
    fn ambient_namespace_interfaces_accept_call_signatures() {
        let mut fixture = fixture(
            "declare namespace Shapes { interface Validator { (value: string): string; } }",
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [SourceNamespaceMemberPlan::Interface { annotations, .. }] = plan.members.as_slice()
        else {
            panic!("the namespace must retain its callable interface")
        };
        assert_eq!(annotations.len(), 2);
        assert!(execute(&mut fixture, &plan).unwrap().is_empty());
    }

    #[test]
    fn ambient_react_svg_factory_signature_annotations_remain_lazy() {
        let fixture = declaration_fixture(
            concat!(
                "interface SVGElement {} declare var SVGElement: unknown; ",
                "declare module 'react' { export = React; namespace React { ",
                "interface ClassAttributes<T> {} ",
                "interface SVGAttributes<T> {} ",
                "interface ReactSVGElement {} type ReactNode = string; ",
                "type DOMFactory<P, T> = (props?: P, ...children: ReactNode[]) => T; ",
                "interface SVGFactory extends DOMFactory<SVGAttributes<SVGElement>, SVGElement> { ",
                "(props?: ClassAttributes<SVGElement> & SVGAttributes<SVGElement> | null, ",
                "...children: ReactNode[]): ReactSVGElement; } } }",
            ),
            CanonicalModuleState::Script,
        );
        let module = plan(&fixture, 2);
        let react = module
            .members
            .iter()
            .find_map(|member| match member {
                SourceNamespaceMemberPlan::Namespace(namespace)
                    if fixture
                        .context
                        .store()
                        .symbol(namespace.symbol)
                        .and_then(|symbol| symbol.name().as_utf8())
                        == Some("React") =>
                {
                    Some(namespace)
                }
                _ => None,
            })
            .expect("the ambient module must retain its React namespace");
        let factory = react
            .members
            .iter()
            .find_map(|member| match member {
                SourceNamespaceMemberPlan::Interface {
                    symbol,
                    annotations,
                    generic,
                    ..
                } if fixture
                    .context
                    .store()
                    .symbol(*symbol)
                    .and_then(|symbol| symbol.name().as_utf8())
                    == Some("SVGFactory") =>
                {
                    Some((annotations, generic))
                }
                _ => None,
            })
            .expect("React must retain its SVG factory interface");

        assert!(factory.0.is_empty());
        assert!(factory.1.is_none());
    }

    #[test]
    fn generic_interface_call_signatures_accept_optional_callbacks_and_rest() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare namespace React { ",
                "interface Attributes<T> { value: T; } ",
                "interface Factory<P, T> { ",
                "<U extends P>(",
                "props?: Attributes<T> & P | null, ",
                "callback?: (value: U) => void, ",
                "...children: U[]",
                "): Attributes<U>; ",
                "} }",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface { .. },
            SourceNamespaceMemberPlan::Interface {
                symbol,
                generic: Some(generic),
                annotations,
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the factory must retain its generic callable interface")
        };
        let symbol = *symbol;
        let call = generic.call_signatures[0];
        let signature = fixture
            .context
            .store()
            .symbol(call)
            .and_then(ts_binder::semantic::Symbol::declarations)
            .and_then(|declarations| declarations.first())
            .copied()
            .unwrap();
        let NodeData::CallSignatureDeclaration(call_signature) =
            &fixture.parsed.arena.get(signature.node).unwrap().data
        else {
            panic!("the factory must retain its call signature")
        };
        assert_eq!(
            call_signature.type_parameters.as_ref().unwrap().nodes.len(),
            1
        );
        assert_eq!(call_signature.parameters.nodes.len(), 3);
        assert_eq!(annotations.len(), 5);

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        let target = fixture
            .context
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Interface(interface) =
            fixture.context.store().type_payload(target).unwrap().data()
        else {
            panic!("the factory must retain its interface type")
        };
        assert!(!interface.declared_members_resolved);
        assert!(fixture.context.store().signature_links(signature).is_none());

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
    fn generic_interface_construct_signatures_remain_authenticated_and_lazy() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare namespace React { ",
                "interface Component<P, S> {} ",
                "interface ComponentClass<P, S> { ",
                "new(props: P, context?: any): Component<P, S>; ",
                "new<T extends P>(props: T, ...children: T[]): Component<T, S>; ",
                "label?: string; ",
                "} }",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface { .. },
            SourceNamespaceMemberPlan::Interface {
                symbol,
                generic: Some(generic),
                annotations,
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the component class must retain its construct signatures")
        };
        let symbol = *symbol;
        let constructor = generic.construct_signatures[0];
        let property = generic.properties[0].symbol;
        let declarations = fixture
            .context
            .store()
            .symbol(constructor)
            .and_then(ts_binder::semantic::Symbol::declarations)
            .unwrap()
            .to_vec();
        assert_eq!(generic.construct_signatures.len(), 1);
        assert_eq!(declarations.len(), 2);
        assert_eq!(annotations.len(), 8);
        assert_eq!(
            fixture.context.store().symbol(constructor).unwrap().name(),
            InternalSymbolName::New.as_ref(),
        );
        assert!(
            fixture
                .context
                .store()
                .value_symbol_links(property)
                .is_none()
        );

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        let target = fixture
            .context
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Interface(interface) =
            fixture.context.store().type_payload(target).unwrap().data()
        else {
            panic!("the component class must retain its declared interface type")
        };
        assert!(!interface.declared_members_resolved);
        assert!(
            fixture
                .context
                .store()
                .value_symbol_links(property)
                .is_none()
        );
        for declaration in declarations {
            assert!(
                fixture
                    .context
                    .store()
                    .signature_links(declaration)
                    .is_none()
            );
        }

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
    fn merged_generic_namespace_interfaces_preserve_each_declaration_and_shared_members() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare namespace React { ",
                "interface HTMLAttributes<T> { id?: string; } ",
                "interface HTMLAttributes<T> { 'aria-label'?: string; } ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface {
                declaration: first_declaration,
                symbol: first_symbol,
                generic: Some(first),
                ..
            },
            SourceNamespaceMemberPlan::Interface {
                declaration: second_declaration,
                symbol: second_symbol,
                generic: Some(second),
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the namespace must retain both merged interface declarations")
        };
        assert_eq!(first_symbol, second_symbol);
        assert_eq!(first.members, second.members);
        assert_eq!(
            fixture
                .context
                .store()
                .symbol(*first_symbol)
                .unwrap()
                .declarations(),
            Some(&[*first_declaration, *second_declaration][..]),
        );
        assert_eq!(first.properties[0].name, "id");
        assert_eq!(second.properties[0].name, "aria-label");
        assert_eq!(
            fixture
                .context
                .store()
                .symbol_table(first.members)
                .unwrap()
                .len(),
            3,
        );

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
    }

    #[test]
    fn nested_type_only_namespace_interface_merges_keep_one_declared_identity() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module 'foo' { ",
                "namespace B { export interface A {} } ",
                "interface B { bar(name: string): B.A; } ",
                "export = B; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Namespace(nested),
            SourceNamespaceMemberPlan::Interface {
                declaration,
                symbol,
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the ambient module must retain its merged namespace and interface")
        };
        let declaration = *declaration;
        let symbol = *symbol;
        assert_eq!(nested.symbol, symbol);
        let record = fixture.context.store().symbol(symbol).unwrap();
        assert!(
            record
                .flags()
                .contains(SymbolFlags::INTERFACE | SymbolFlags::NAMESPACE_MODULE)
        );
        assert!(!record.flags().intersects(SymbolFlags::VALUE));
        let [
            SourceNamespaceMemberPlan::Interface {
                symbol: exported, ..
            },
        ] = nested.members.as_slice()
        else {
            panic!("the merged namespace must retain its exported interface")
        };
        let exported = *exported;
        let bound = fixture.context.file(fixture.file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&fixture.parsed.arena, &bound)],
            GlobalMergeCompletion::for_test(fixture.context.options().name_resolution),
        )
        .unwrap();
        assert_eq!(
            authenticated_merged_namespace_interface(fixture.context.store(), &host, symbol),
            Some(declaration)
        );

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        let target = fixture
            .context
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Interface(interface) =
            fixture.context.store().type_payload(target).unwrap().data()
        else {
            panic!("the merged namespace must keep its original interface identity")
        };
        assert!(!interface.declared_members_resolved);
        assert_eq!(
            fixture
                .context
                .store()
                .symbol(symbol)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| fixture.context.store().symbol_table(exports))
                .and_then(|exports| exports.get_source("A")),
            Some(exported)
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
    fn generic_namespace_interface_index_signatures_stay_authenticated_and_lazy() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare namespace React { ",
                "interface Mixin<P, S> { render(): P; } ",
                "interface ComponentSpec<P, S> extends Mixin<P, S> { ",
                "render(): P; ",
                "[propertyName: string]: any; ",
                "} }",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface { .. },
            SourceNamespaceMemberPlan::Interface {
                symbol,
                generic: Some(generic),
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the component specification must retain its indexed interface")
        };
        let symbol = *symbol;
        let [index] = generic.index_signatures.as_slice() else {
            panic!("the indexed interface must retain one binder-owned index symbol")
        };
        let index = *index;
        let index_record = fixture.context.store().symbol(index).unwrap();
        let [index_declaration] = index_record.declarations().unwrap() else {
            panic!("the index symbol must retain its declaration")
        };
        let index_declaration = *index_declaration;
        let NodeData::IndexSignatureDeclaration(index_syntax) = &fixture
            .parsed
            .arena
            .get(index_declaration.node)
            .unwrap()
            .data
        else {
            panic!("the index symbol must retain its index signature")
        };
        let parameter = child(index_declaration, index_syntax.parameters.nodes[0]);
        let NodeData::ParameterDeclaration(parameter_syntax) =
            &fixture.parsed.arena.get(parameter.node).unwrap().data
        else {
            panic!("the index signature must retain its key parameter")
        };
        let key = child(parameter, parameter_syntax.type_.unwrap());
        let value = child(index_declaration, index_syntax.type_);
        assert_eq!(index_record.flags(), SymbolFlags::SIGNATURE);
        assert_eq!(index_record.name(), InternalSymbolName::Index.as_ref());
        assert_eq!(
            fixture.context.store().get_parent_of_symbol(index),
            Some(symbol)
        );
        assert_eq!(
            fixture
                .context
                .store()
                .symbol_table(generic.members)
                .and_then(|members| members.get(InternalSymbolName::Index.as_ref())),
            Some(index),
        );
        assert!(generic.annotation_is_deferred(key));
        assert!(generic.annotation_is_deferred(value));

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        let target = fixture
            .context
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Interface(interface) =
            fixture.context.store().type_payload(target).unwrap().data()
        else {
            panic!("the component specification must retain its declared interface type")
        };
        assert!(!interface.declared_members_resolved);
        assert!(interface.declared_index_infos.is_none());
        assert!(
            fixture
                .context
                .store()
                .signature_links(index_declaration)
                .is_none()
        );
        assert!(fixture.context.store().type_node_links(key).is_none());
        assert!(fixture.context.store().type_node_links(value).is_none());

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
    fn generic_namespace_interface_index_signatures_reject_malformed_binder_symbols() {
        for mutation in 0..4 {
            let mut fixture = declaration_fixture(
                concat!(
                    "declare namespace React { ",
                    "interface ComponentSpec<P, S> { ",
                    "[propertyName: string]: any; ",
                    "} }",
                ),
                CanonicalModuleState::Script,
            );
            let namespace = plan(&fixture, 0);
            let [
                SourceNamespaceMemberPlan::Interface {
                    symbol,
                    generic: Some(generic),
                    ..
                },
            ] = namespace.members.as_slice()
            else {
                panic!("the component specification must retain its indexed interface")
            };
            let owner = *symbol;
            let index = generic.index_signatures[0];
            let index_declaration = fixture
                .context
                .store()
                .symbol(index)
                .and_then(ts_binder::semantic::Symbol::declarations)
                .and_then(|declarations| declarations.first())
                .copied()
                .unwrap();
            let NodeData::IndexSignatureDeclaration(index_syntax) = &fixture
                .parsed
                .arena
                .get(index_declaration.node)
                .unwrap()
                .data
            else {
                panic!("the index symbol must retain its index signature")
            };
            let parameter = child(index_declaration, index_syntax.parameters.nodes[0]);
            let parameter_symbol = fixture
                .context
                .file(fixture.file)
                .unwrap()
                .1
                .symbol(parameter)
                .unwrap();
            let expected = if mutation == 3 {
                parameter
            } else {
                index_declaration
            };
            let store = fixture.context.store_mut_for_test();
            match mutation {
                0 => {
                    assert!(store.set_symbol_flags(index, SymbolFlags::PROPERTY, CheckFlags::NONE));
                }
                1 => assert!(store.set_symbol_relationships(index, None, None, None, None)),
                2 => assert!(store.set_symbol_relationships(
                    index,
                    None,
                    None,
                    Some(namespace.symbol),
                    None,
                )),
                3 => assert!(store.set_symbol_flags(
                    parameter_symbol,
                    SymbolFlags::PROPERTY,
                    CheckFlags::NONE,
                )),
                _ => unreachable!(),
            }
            let before = (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            );
            let root = declaration(&fixture, 0);
            let (arena, bound) = fixture.context.file(fixture.file).unwrap();

            assert!(matches!(
                plan_source_namespace(arena, bound, fixture.context.store(), root),
                Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::MissingDeclarationSymbol(node),
                )) if node == expected
            ));
            assert!(fixture.context.store().declared_type_links(owner).is_none());
            assert!(
                fixture
                    .context
                    .store()
                    .signature_links(index_declaration)
                    .is_none()
            );
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

    #[test]
    fn generic_namespace_interface_methods_stay_authenticated_and_lazy() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare namespace React { ",
                "interface Component<P, S> {} ",
                "interface ClassicComponent<P, S> extends Component<P, S> { ",
                "replaceState(nextState: S, callback?: () => void): void; ",
                "isMounted(): boolean; ",
                "getInitialState?(): S; ",
                "map<U extends S>(first: U, ...rest: U[]): U; ",
                "} }",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface { .. },
            SourceNamespaceMemberPlan::Interface {
                symbol,
                generic: Some(generic),
                annotations,
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the classic component must retain its generic method interface")
        };
        let symbol = *symbol;
        let methods = generic.methods.clone();
        assert_eq!(methods.len(), 4);
        assert_eq!(annotations.len(), 9);
        assert_eq!(
            fixture.context.store().symbol(methods[2]).unwrap().flags(),
            SymbolFlags::METHOD | SymbolFlags::OPTIONAL,
        );
        for method in &methods {
            assert!(
                fixture
                    .context
                    .store()
                    .value_symbol_links(*method)
                    .is_none()
            );
        }

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        let target = fixture
            .context
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Interface(interface) =
            fixture.context.store().type_payload(target).unwrap().data()
        else {
            panic!("the component must retain its declared interface type")
        };
        assert!(!interface.declared_members_resolved);
        for method in methods {
            let declaration = fixture
                .context
                .store()
                .symbol(method)
                .and_then(ts_binder::semantic::Symbol::value_declaration)
                .unwrap();
            assert!(fixture.context.store().value_symbol_links(method).is_none());
            assert!(
                fixture
                    .context
                    .store()
                    .signature_links(declaration)
                    .is_none()
            );
        }

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
    fn generic_callable_namespace_interfaces_keep_declared_members_lazy() {
        let mut fixture = fixture(
            concat!(
                "declare namespace Shapes { ",
                "interface Validator<T> { (value: string): string; value?: T; } ",
                "}",
            ),
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
            panic!("the namespace must retain its generic callable interface")
        };
        let symbol = *symbol;
        let property = generic.properties[0].symbol;
        assert_eq!(generic.call_signatures.len(), 1);

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
            panic!("the generic callable must retain its interface type")
        };
        assert!(!interface.declared_members_resolved);
        assert!(
            fixture
                .context
                .store()
                .value_symbol_links(property)
                .is_none()
        );
    }

    #[test]
    fn generic_callable_namespace_interfaces_retain_computed_symbol_properties() {
        let fixture = fixture(
            concat!(
                "declare namespace Shapes { ",
                "const key: unique symbol; ",
                "interface Validator<T> { (value: string): string; [key]?: T; } ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::AmbientVariable { symbol: key, .. },
            SourceNamespaceMemberPlan::Interface {
                generic: Some(generic),
                ..
            },
        ] = plan.members.as_slice()
        else {
            panic!("the namespace must retain its unique symbol and callable interface")
        };
        assert_eq!(generic.call_signatures.len(), 1);
        assert_eq!(generic.computed_properties.len(), 1);
        assert_eq!(generic.computed_properties[0].key, *key);
        assert!(generic.properties.is_empty());
    }

    #[test]
    fn generic_namespace_interface_heritage_keeps_base_and_members_lazy() {
        let mut fixture = fixture(
            concat!(
                "declare namespace Shapes { ",
                "interface Validator<T> { (value: T): string; } ",
                "interface Requireable<T> extends Validator<T | undefined> { ",
                "isRequired: Validator<T>; ",
                "} }",
            ),
            CanonicalModuleState::Script,
        );
        let plan = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface { symbol: base, .. },
            SourceNamespaceMemberPlan::Interface {
                symbol: derived,
                generic: Some(generic),
                ..
            },
        ] = plan.members.as_slice()
        else {
            panic!("the namespace must retain its callable and derived interfaces")
        };
        let base = *base;
        let derived = *derived;
        assert_eq!(generic.base_interfaces, [base]);
        assert_eq!(generic.properties.len(), 1);

        assert!(execute(&mut fixture, &plan).unwrap().is_empty());

        let target = fixture
            .context
            .store()
            .declared_type_links(derived)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Interface(interface) =
            fixture.context.store().type_payload(target).unwrap().data()
        else {
            panic!("the derived declaration must retain its interface type")
        };
        assert!(!interface.declared_members_resolved);
    }

    #[test]
    fn reopened_generic_namespace_interfaces_keep_shared_members_and_references_lazy() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare namespace React { ",
                "interface DOMAttributes<T> { value?: T; } ",
                "interface HTMLAttributes<T> extends DOMAttributes<T> { id?: string; } ",
                "interface HTMLAttributes<T> extends DOMAttributes<T> { title?: string; } ",
                "interface Wrapper<P extends HTMLAttributes<string>> { ",
                "value?: HTMLAttributes<P>; ",
                "} }",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface { .. },
            SourceNamespaceMemberPlan::Interface {
                declaration: first_declaration,
                symbol: first_symbol,
                generic: Some(first),
                ..
            },
            SourceNamespaceMemberPlan::Interface {
                declaration: second_declaration,
                symbol: second_symbol,
                generic: Some(second),
                ..
            },
            SourceNamespaceMemberPlan::Interface {
                symbol: wrapper,
                generic: Some(wrapper_generic),
                annotations,
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("React must retain its reopened interface and dependent generic interface")
        };
        let symbol = *first_symbol;
        let wrapper = *wrapper;
        let parameter = first.type_parameters[0];
        let properties = [first.properties[0].symbol, second.properties[0].symbol];
        let wrapper_property = wrapper_generic.properties[0].symbol;
        let deferred = annotations.clone();
        assert_eq!(*second_symbol, symbol);
        assert_eq!(first.type_parameters, second.type_parameters);
        assert_eq!(first.members, second.members);
        assert_eq!(
            fixture.context.store().get_parent_of_symbol(parameter),
            Some(symbol),
        );
        assert_eq!(
            fixture
                .context
                .store()
                .symbol(symbol)
                .unwrap()
                .declarations(),
            Some(&[*first_declaration, *second_declaration][..]),
        );
        let members = fixture.context.store().symbol_table(first.members).unwrap();
        assert_eq!(members.len(), 3);
        assert_eq!(members.get_source("T"), Some(parameter));
        assert_eq!(members.get_source("id"), Some(properties[0]));
        assert_eq!(members.get_source("title"), Some(properties[1]));
        assert_eq!(deferred.len(), 2);
        assert!(
            deferred
                .iter()
                .all(|annotation| { wrapper_generic.annotation_is_deferred(*annotation) })
        );

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        for owner in [symbol, wrapper] {
            let target = fixture
                .context
                .store()
                .declared_type_links(owner)
                .and_then(|links| links.declared_type)
                .unwrap();
            let TypeData::Interface(interface) =
                fixture.context.store().type_payload(target).unwrap().data()
            else {
                panic!("the React interface must retain its declared identity")
            };
            assert!(!interface.declared_members_resolved);
        }
        for property in properties.into_iter().chain([wrapper_property]) {
            assert!(
                fixture
                    .context
                    .store()
                    .value_symbol_links(property)
                    .is_none()
            );
        }
        assert!(deferred.iter().all(|annotation| {
            fixture
                .context
                .store()
                .type_node_links(*annotation)
                .is_none()
        }));

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
    fn reopened_generic_namespace_interfaces_reject_invalid_owner_parameter_and_members() {
        for mutation in 0..4 {
            let mut fixture = declaration_fixture(
                concat!(
                    "declare namespace React { ",
                    "interface DOMAttributes<T> {} ",
                    "interface HTMLAttributes<T> extends DOMAttributes<T> { id?: string; } ",
                    "interface HTMLAttributes<T> extends DOMAttributes<T> { title?: string; } ",
                    "}",
                ),
                CanonicalModuleState::Script,
            );
            let namespace = plan(&fixture, 0);
            let [
                SourceNamespaceMemberPlan::Interface { .. },
                SourceNamespaceMemberPlan::Interface {
                    declaration: owner_declaration,
                    symbol,
                    generic: Some(generic),
                    ..
                },
                SourceNamespaceMemberPlan::Interface { .. },
            ] = namespace.members.as_slice()
            else {
                panic!("React must retain both reopened generic declarations")
            };
            let symbol = *symbol;
            let owner_declaration = *owner_declaration;
            let parameter = generic.type_parameters[0];
            let parameter_declaration = fixture
                .context
                .store()
                .symbol(parameter)
                .and_then(ts_binder::semantic::Symbol::declarations)
                .and_then(|declarations| declarations.first())
                .copied()
                .unwrap();
            let property = generic.properties[0].symbol;
            let property_declaration = generic.properties[0].declaration;
            let expected = match mutation {
                0 => owner_declaration,
                1 | 3 => parameter_declaration,
                2 => property_declaration,
                _ => unreachable!(),
            };
            let store = fixture.context.store_mut_for_test();
            match mutation {
                0 => assert!(store.set_symbol_flags(
                    symbol,
                    SymbolFlags::INTERFACE | SymbolFlags::PROPERTY,
                    CheckFlags::NONE,
                )),
                1 => assert!(store.set_symbol_flags(
                    parameter,
                    SymbolFlags::TYPE_PARAMETER | SymbolFlags::PROPERTY,
                    CheckFlags::NONE,
                )),
                2 => assert!(store.set_symbol_relationships(
                    property,
                    None,
                    None,
                    Some(namespace.symbol),
                    None,
                )),
                3 => assert!(store.set_symbol_relationships(parameter, None, None, None, None)),
                _ => unreachable!(),
            }
            let before = (
                fixture.context.store().type_len(),
                fixture.context.store().symbol_len(),
                fixture.context.store().checker_link_allocated_lengths(),
            );
            let root = declaration(&fixture, 0);
            let (arena, bound) = fixture.context.file(fixture.file).unwrap();

            assert!(matches!(
                plan_source_namespace(arena, bound, fixture.context.store(), root),
                Err(SourceCheckError::Provenance(
                    SourceCheckProvenanceError::MissingDeclarationSymbol(node),
                )) if node == expected
            ));
            assert!(
                fixture
                    .context
                    .store()
                    .declared_type_links(symbol)
                    .is_none()
            );
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

    #[test]
    fn declaration_generic_interfaces_do_not_defer_missing_type_references() {
        let mut fixture = declaration_fixture(
            "declare namespace React { interface Wrapper<T> { value?: Missing<T>; } }",
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface {
                symbol,
                generic: Some(generic),
                annotations,
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the declaration must retain its generic interface")
        };
        let symbol = *symbol;
        let [annotation] = annotations.as_slice() else {
            panic!("the generic interface must retain its missing property type")
        };
        assert!(!generic.annotation_is_deferred(*annotation));
        let before = (
            fixture.context.store().type_len(),
            fixture.context.store().symbol_len(),
            fixture.context.store().checker_link_allocated_lengths(),
        );

        assert!(matches!(
            execute(&mut fixture, &namespace),
            Err(SourceCheckError::DeclaredType(
                DeclaredTypeError::TypeNodeUnavailable(TypeNodeUnavailable::MissingTypeReference(
                    _
                ))
            ))
        ));
        assert!(
            fixture
                .context
                .store()
                .declared_type_links(symbol)
                .is_none()
        );
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
    fn declaration_generic_namespace_interface_alias_annotations_remain_lazy() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare namespace Shapes { ",
                "type Value<T> = T; ",
                "interface Wrapper<T> { value: Value<T>; } ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::TypeAlias { .. },
            SourceNamespaceMemberPlan::Interface {
                symbol,
                generic: Some(generic),
                annotations,
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the declaration namespace must retain its alias and generic interface")
        };
        let symbol = *symbol;
        let property = generic.properties[0].symbol;
        let [annotation] = annotations.as_slice() else {
            panic!("the declaration interface must retain its alias-backed property")
        };
        let annotation = *annotation;
        assert!(generic.annotation_is_deferred(annotation));

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        let target = fixture
            .context
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Interface(interface) =
            fixture.context.store().type_payload(target).unwrap().data()
        else {
            panic!("the declaration interface must retain its declared identity")
        };
        assert!(!interface.declared_members_resolved);
        assert!(
            fixture
                .context
                .store()
                .value_symbol_links(property)
                .is_none()
        );
        assert!(
            fixture
                .context
                .store()
                .type_node_links(annotation)
                .is_none()
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
    fn ordinary_generic_namespace_interface_alias_annotations_remain_eager() {
        let mut fixture = fixture(
            concat!(
                "declare namespace Shapes { ",
                "type Value<T> = T; ",
                "interface Wrapper<T> { value: Value<T>; } ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::TypeAlias { .. },
            SourceNamespaceMemberPlan::Interface {
                symbol,
                generic: Some(generic),
                annotations,
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the ordinary namespace must retain its alias and generic interface")
        };
        let symbol = *symbol;
        let property = generic.properties[0].symbol;
        assert_eq!(annotations.len(), 1);
        assert!(!generic.annotation_is_deferred(annotations[0]));

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        let target = fixture
            .context
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Interface(interface) =
            fixture.context.store().type_payload(target).unwrap().data()
        else {
            panic!("the ordinary generic interface must retain its declared identity")
        };
        assert!(interface.declared_members_resolved);
        assert!(
            fixture
                .context
                .store()
                .value_symbol_links(property)
                .is_some()
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep nested base arguments and cold-cache checks together.
    fn nongeneric_namespace_interfaces_accept_concrete_generic_heritage_lazily() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare namespace React { ",
                "interface SVGElement {} ",
                "interface SVGAttributes<T> { value?: T; } ",
                "interface DOMElement<P, T> { props: P; } ",
                "interface ReactSVG { path: any; } ",
                "interface ReactSVGElement ",
                "extends DOMElement<SVGAttributes<SVGElement>, SVGElement> { ",
                "type: keyof ReactSVG; ",
                "} ",
                "interface ReactPortal extends DOMElement<any, SVGElement> {} ",
                "interface ReactDOM extends ReactSVG, ReactSVGElement {} ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let mut derived = Vec::new();
        let mut heritage_arguments = Vec::new();
        for member in &namespace.members {
            let SourceNamespaceMemberPlan::Interface {
                declaration,
                symbol,
                generic,
                ..
            } = member
            else {
                panic!("the React fixture must contain only interfaces")
            };
            let name = fixture
                .context
                .store()
                .symbol(*symbol)
                .and_then(|symbol| symbol.name().as_utf8())
                .unwrap();
            if !matches!(name, "ReactSVGElement" | "ReactPortal" | "ReactDOM") {
                continue;
            }
            assert!(generic.is_none(), "{name}");
            derived.push(*symbol);
            let NodeData::InterfaceDeclaration(interface) =
                &fixture.parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("the derived symbol must retain its interface declaration")
            };
            for clause in &interface.heritage_clauses.as_ref().unwrap().nodes {
                let clause = child(*declaration, *clause);
                let NodeData::HeritageClause(heritage) =
                    &fixture.parsed.arena.get(clause.node).unwrap().data
                else {
                    panic!("the derived interface must retain its extends clause")
                };
                for base in &heritage.types.nodes {
                    let base = child(clause, *base);
                    let NodeData::ExpressionWithTypeArguments(reference) =
                        &fixture.parsed.arena.get(base.node).unwrap().data
                    else {
                        panic!("the extends clause must retain its generic expression")
                    };
                    heritage_arguments.extend(
                        reference
                            .type_arguments
                            .iter()
                            .flat_map(|arguments| &arguments.nodes)
                            .map(|argument| child(base, *argument)),
                    );
                }
            }
        }
        assert_eq!(derived.len(), 3);
        assert_eq!(heritage_arguments.len(), 4);

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        for symbol in derived {
            let type_ = fixture
                .context
                .store()
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .unwrap();
            let TypeData::Interface(interface) =
                fixture.context.store().type_payload(type_).unwrap().data()
            else {
                panic!("the derived interface must retain its declared type")
            };
            assert!(!interface.declared_members_resolved);
        }
        assert!(
            heritage_arguments
                .iter()
                .all(|argument| { fixture.context.store().type_node_links(*argument).is_none() })
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
    fn reopened_generic_namespace_interfaces_preserve_their_shared_member_table() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare namespace React { ",
                "interface DOMAttributes<T> {} ",
                "interface HTMLAttributes<T> extends DOMAttributes<T> { id?: string; } ",
                "interface HTMLAttributes<T> extends DOMAttributes<T> { title?: string; } ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [
            SourceNamespaceMemberPlan::Interface { .. },
            SourceNamespaceMemberPlan::Interface {
                symbol: first,
                generic: Some(first_generic),
                ..
            },
            SourceNamespaceMemberPlan::Interface {
                symbol: second,
                generic: Some(second_generic),
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the namespace must retain its base and reopened generic interfaces")
        };
        assert_eq!(first, second);
        assert_eq!(first_generic.members, second_generic.members);
        assert_eq!(first_generic.properties.len(), 1);
        assert_eq!(second_generic.properties.len(), 1);
        assert_eq!(
            fixture
                .context
                .store()
                .symbol_table(first_generic.members)
                .map(ts_binder::semantic::SymbolTable::len),
            Some(3),
        );
        let symbol = *first;

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());

        let target = fixture
            .context
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            .unwrap();
        let TypeData::Interface(interface) =
            fixture.context.store().type_payload(target).unwrap().data()
        else {
            panic!("the reopened symbol must retain its generic interface identity")
        };
        assert!(!interface.declared_members_resolved);

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
    fn ambient_module_side_effect_imports_keep_target_and_alias_state_lazy() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module 'dependency' { export interface Value {} } ",
                "declare module 'consumer' { ",
                "import 'dependency'; ",
                "interface Wrapper { label: string; } ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 1);
        let import = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ImportDeclaration).then_some(NodeRef::new(
                    fixture.parsed.arena.id(),
                    fixture.file,
                    node,
                ))
            })
            .unwrap();
        let (_, bound) = fixture.context.file(fixture.file).unwrap();
        assert!(bound.symbol(import).is_none());
        assert!(namespace.imports.is_empty());
        assert_eq!(namespace.members.len(), 1);

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());

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
    fn ambient_module_local_reexports_preserve_import_aliases_cold_and_warm() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module 'target' { export interface Value {} } ",
                "declare module 'source' { ",
                "import * as imported from 'target'; ",
                "export { imported as exposed }; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 1);
        let [import, reexport] = namespace.imports.as_slice() else {
            panic!("the ambient module must retain its import and reexport aliases")
        };
        let imported = import.symbol;
        let exposed = reexport.symbol;
        let target = import.ambient_target.unwrap();
        assert_eq!(reexport.ambient_target, Some(imported));
        assert_eq!(reexport.name_text, "exposed");

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());
        for alias in [imported, exposed] {
            assert_eq!(
                fixture
                    .context
                    .store()
                    .alias_symbol_links(alias)
                    .map(|links| links.alias_target),
                Some(AliasTargetState::Resolved(target)),
            );
        }
        assert_eq!(
            fixture
                .context
                .store()
                .alias_symbol_links(exposed)
                .and_then(|links| links.immediate_target),
            Some(imported),
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
    fn ambient_module_external_imports_and_reexports_use_exact_manifest_aliases() {
        let provider = parse_source_file("export declare const value: number;");
        let ambient = parse_source_file(concat!(
            "declare module 'mymod' { ",
            "import * as external from 'provider'; ",
            "export { external }; ",
            "}",
        ));
        let provider_file = FileId::new(7_490);
        let ambient_file = FileId::new(7_491);
        let specifier = ambient
            .arena
            .iter()
            .find_map(|(_, record)| match &record.data {
                NodeData::ImportDeclaration(import) => Some(import.module_specifier),
                _ => None,
            })
            .unwrap();
        let manifest = CanonicalModuleResolutionManifestInput::new([
            CanonicalModuleResolutionEntry::resolved(
                NodeRef::new(ambient.arena.id(), ambient_file, specifier),
                CanonicalResolvedModuleInput::new(
                    provider_file,
                    CanonicalModuleResolutionMode::Esm,
                    CanonicalModuleResolutionMode::Esm,
                ),
            ),
        ]);
        let mut context = ambient_module_context(
            &[
                (provider_file, &provider, CanonicalModuleState::External),
                (ambient_file, &ambient, CanonicalModuleState::Script),
            ],
            Some(manifest),
        );
        let (_, ambient_bound) = context.file(ambient_file).unwrap();
        let imports = ambient
            .arena
            .iter()
            .filter_map(|(node, record)| {
                matches!(
                    record.kind,
                    SyntaxKind::NamespaceImport | SyntaxKind::ExportSpecifier
                )
                .then_some(NodeRef::new(ambient.arena.id(), ambient_file, node))
            })
            .map(|declaration| ambient_bound.symbol(declaration).unwrap())
            .collect::<Vec<_>>();
        let [imported, reexported] = imports.as_slice() else {
            panic!("the ambient module must retain both binder-owned aliases")
        };
        let imported = *imported;
        let reexported = *reexported;
        let provider_module = context
            .file(provider_file)
            .and_then(|(_, bound)| bound.symbol(bound.source_file()))
            .unwrap();

        context.check_source_file(ambient_file).unwrap();

        for alias in [imported, reexported] {
            assert_eq!(
                context
                    .store()
                    .alias_symbol_links(alias)
                    .map(|links| links.alias_target),
                Some(AliasTargetState::Resolved(provider_module)),
            );
        }
        assert_eq!(
            context
                .store()
                .alias_symbol_links(reexported)
                .and_then(|links| links.immediate_target),
            Some(imported),
        );
        let warm = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
            context.diagnostics().as_slice().to_vec(),
        );
        context.recheck_source_file(ambient_file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().as_slice().to_vec(),
            ),
            warm,
        );
    }

    #[test]
    fn reopened_ambient_module_reexports_report_exact_cross_file_block_scoped_collisions() {
        let first = parse_source_file(concat!(
            "declare module 'target' { export interface Value {} } ",
            "declare module 'mymod' { ",
            "import * as foo from 'target'; export { foo }; ",
            "}",
        ));
        let second = parse_source_file("declare module 'mymod' { export const foo: number; }");
        let first_file = FileId::new(7_492);
        let second_file = FileId::new(7_493);
        let mut context = ambient_module_context(
            &[
                (first_file, &first, CanonicalModuleState::Script),
                (second_file, &second, CanonicalModuleState::Script),
            ],
            None,
        );
        let first_name = first
            .arena
            .iter()
            .find_map(|(declaration, record)| match &record.data {
                NodeData::ExportSpecifier(export) if record.kind == SyntaxKind::ExportSpecifier => {
                    Some(child(
                        NodeRef::new(first.arena.id(), first_file, declaration),
                        export.name,
                    ))
                }
                _ => None,
            })
            .unwrap();
        let second_name = second
            .arena
            .iter()
            .find_map(|(declaration, record)| match &record.data {
                NodeData::VariableDeclaration(variable)
                    if record.kind == SyntaxKind::VariableDeclaration =>
                {
                    Some(child(
                        NodeRef::new(second.arena.id(), second_file, declaration),
                        variable.name,
                    ))
                }
                _ => None,
            })
            .unwrap();

        context.check_source_file(first_file).unwrap();
        assert!(context.diagnostics().is_empty());
        context.check_source_file(second_file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2);
        for (diagnostic, (name, related)) in diagnostics
            .iter()
            .zip([(first_name, second_name), (second_name, first_name)])
        {
            assert_eq!(diagnostic.node, Some(name));
            assert_eq!(diagnostic.diagnostic.code(), 2451);
            assert_eq!(diagnostic.diagnostic.arguments, ["foo"]);
            let [other] = diagnostic.related_information.as_slice() else {
                panic!("each duplicate must retain one exact cross-file declaration")
            };
            assert_eq!(other.node, Some(related));
            assert_eq!(other.diagnostic.code(), 6203);
            assert_eq!(other.diagnostic.arguments, ["foo"]);
        }

        let warm = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
            context.diagnostics().as_slice().to_vec(),
        );
        context.recheck_source_file(second_file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().as_slice().to_vec(),
            ),
            warm,
        );
    }

    #[test]
    fn reopened_ambient_modules_merge_nonconflicting_export_tables() {
        let first = parse_source_file("declare module 'pkg' { export interface First {} }");
        let second = parse_source_file("declare module 'pkg' { export interface Second {} }");
        let first_file = FileId::new(7_494);
        let second_file = FileId::new(7_495);
        let mut context = ambient_module_context(
            &[
                (first_file, &first, CanonicalModuleState::Script),
                (second_file, &second, CanonicalModuleState::Script),
            ],
            None,
        );
        let first_module = first
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ModuleDeclaration).then_some(NodeRef::new(
                    first.arena.id(),
                    first_file,
                    node,
                ))
            })
            .and_then(|declaration| context.file(first_file)?.1.symbol(declaration))
            .unwrap();
        let second_module = second
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ModuleDeclaration).then_some(NodeRef::new(
                    second.arena.id(),
                    second_file,
                    node,
                ))
            })
            .and_then(|declaration| context.file(second_file)?.1.symbol(declaration))
            .unwrap();

        context.check_source_file(first_file).unwrap();
        context.check_source_file(second_file).unwrap();

        let merged = context.store().get_merged_symbol(first_module).unwrap();
        assert_eq!(
            context.store().get_merged_symbol(second_module),
            Some(merged)
        );
        let exports = context
            .store()
            .symbol(merged)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| context.store().symbol_table(exports))
            .unwrap();
        assert!(exports.get_source("First").is_some());
        assert!(exports.get_source("Second").is_some());
        assert!(context.diagnostics().is_empty());
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
    fn ambient_module_default_export_assignments_preserve_interface_aliases() {
        let mut fixture = declaration_fixture(
            concat!(
                "declare module 'library' { ",
                "interface Model { value: string; } ",
                "export default Model; ",
                "}",
            ),
            CanonicalModuleState::Script,
        );
        let namespace = plan(&fixture, 0);
        let [export] = namespace.imports.as_slice() else {
            panic!("the ambient module must retain its default-export alias")
        };
        let alias = export.symbol;
        let [SourceNamespaceMemberPlan::Interface { symbol: target, .. }] =
            namespace.members.as_slice()
        else {
            panic!("the ambient module must retain its exported interface")
        };
        let target = *target;
        let record = fixture.context.store().symbol(alias).unwrap();
        assert_eq!(record.name(), InternalSymbolName::Default.as_ref());
        assert_eq!(record.value_declaration(), None);

        assert!(execute(&mut fixture, &namespace).unwrap().is_empty());

        assert_eq!(
            fixture
                .context
                .store()
                .alias_symbol_links(alias)
                .map(|links| (links.immediate_target, links.alias_target)),
            Some((Some(target), AliasTargetState::Resolved(target))),
        );
        assert!(fixture.context.store().value_symbol_links(alias).is_none());

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
    #[allow(clippy::too_many_lines)] // Keep merged ownership, warm identity, and forgery checks together.
    fn external_global_array_method_augmentation_authenticates_merged_parent() {
        let library = parse_source_file(concat!(
            "interface Array<T> { length: number; } ",
            "declare var Array: any; ",
            "interface ReadonlyArray<T> {}",
        ));
        let augmentation = parse_source_file(concat!(
            "declare global { interface Array<T> { customMethod(): T; } } ",
            "export {};",
        ));
        assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
        assert!(
            augmentation.diagnostics.is_empty(),
            "{:?}",
            augmentation.diagnostics,
        );

        let library_file = FileId::new(7_496);
        let augmentation_file = FileId::new(7_497);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, default_library, module_state) in [
            (&library, library_file, true, CanonicalModuleState::Script),
            (
                &augmentation,
                augmentation_file,
                false,
                CanonicalModuleState::External,
            ),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(if default_library {
                            "\"/lib.array.d.ts\""
                        } else {
                            "\"/augment.ts\""
                        }),
                        CanonicalSourceLanguage::TypeScript,
                        default_library,
                        default_library,
                        module_state,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![
                (library_file, &library.arena),
                (augmentation_file, &augmentation.arena),
            ],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let (_, bound) = context.file(augmentation_file).unwrap();
        let namespace_declaration = augmentation
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ModuleDeclaration).then_some(NodeRef::new(
                    augmentation.arena.id(),
                    augmentation_file,
                    node,
                ))
            })
            .unwrap();
        let method_declaration = augmentation
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::MethodSignature).then_some(NodeRef::new(
                    augmentation.arena.id(),
                    augmentation_file,
                    node,
                ))
            })
            .unwrap();
        let method = bound
            .symbol(method_declaration)
            .and_then(|symbol| context.store().get_merged_symbol(symbol))
            .unwrap();
        let array = context
            .store()
            .intrinsic_bootstrap()
            .and_then(|bootstrap| context.store().symbol_table(bootstrap.globals))
            .and_then(|globals| globals.get_source("Array"))
            .and_then(|symbol| context.store().get_merged_symbol(symbol))
            .unwrap();
        assert_ne!(
            context.store().symbol(method).unwrap().parent(),
            Some(array)
        );
        assert_eq!(context.store().get_parent_of_symbol(method), Some(array));

        let members = context
            .store()
            .symbol(array)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| context.store().symbol_table(members))
            .unwrap();
        assert!(members.get_source("length").is_some());
        assert_eq!(
            members
                .get_source("customMethod")
                .and_then(|symbol| context.store().get_merged_symbol(symbol)),
            Some(method),
        );

        let namespace = plan_source_namespace(
            &augmentation.arena,
            bound,
            context.store(),
            namespace_declaration,
        )
        .unwrap();
        let [
            SourceNamespaceMemberPlan::Interface {
                symbol,
                generic: Some(generic),
                ..
            },
        ] = namespace.members.as_slice()
        else {
            panic!("the global augmentation must retain its generic Array contribution")
        };
        assert_eq!(*symbol, array);
        assert_eq!(generic.methods.as_slice(), [method]);

        context.check_source_file(augmentation_file).unwrap();
        assert!(context.diagnostics().is_empty());
        let warm = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
            context.diagnostics().as_slice().to_vec(),
        );
        context.recheck_source_file(augmentation_file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().as_slice().to_vec(),
            ),
            warm,
        );

        assert_ne!(namespace.symbol, array);
        assert!(context.store_mut_for_test().set_symbol_relationships(
            method,
            None,
            None,
            Some(namespace.symbol),
            None,
        ));
        let (arena, bound) = context.file(augmentation_file).unwrap();
        assert!(matches!(
            plan_source_namespace(arena, bound, context.store(), namespace_declaration),
            Err(SourceCheckError::Provenance(
                SourceCheckProvenanceError::MissingDeclarationSymbol(node),
            )) if node == method_declaration
        ));
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
