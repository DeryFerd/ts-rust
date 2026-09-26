//! Read-only planning for the first assignment-expression source slice.
//!
//! The installed slice is deliberately narrow: a top-level expression statement
//! containing a simple or arithmetic compound identifier assignment, where the
//! identifier resolves to one
//! unique, same-file, explicitly typed and initialized ordinary `var` declaration.
//! Source planning may additionally supply exact capabilities for mutable ambient
//! declarations or admitted annotated uninitialized variables. Those
//! routes independently revalidate their direct `var`/`let` AST and binder shape
//! before admission.
//! Separate `CommonJS` routes admit binder-authenticated assignments to
//! `module.exports` and static named assignments on `exports` or `module.exports`.
//! Prototype writes reuse an existing class method or authenticate a JavaScript
//! function alias without inventing an assignment-owned property.
//! Direct arrow and function expandos retain their binder-owned properties and
//! authenticate the source declaration before admission. Nested JavaScript
//! function-expando writes reuse their previously declared outer property.
//! JavaScript object expandos retain the initializer's real assignment exports.
//! Same-file own class fields retain their source receiver and assignment position.
//! Ordinary element writes reuse the assignment proof and the source element checker.
//! Name lookup follows the pinned lexical resolver and checker export/merge routing.
//! Valid syntax outside that closure is a typed unsupported result; malformed AST,
//! binder, or semantic-store provenance is an invariant failure.

use std::collections::HashSet;

use ts_ast::{
    FileId, Node, NodeArena, NodeArenaId, NodeArenaRevision, NodeData, NodeRef, SyntaxKind,
};
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation,
    CheckFlags, InternalSymbolName, SemanticSymbolId, SymbolFlags,
};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost,
    primitive_operators::compound_assignment_binary_operator,
};

const NODE_FLAG_LET: u32 = 1 << 0;
const NODE_FLAG_CONST: u32 = 1 << 1;

/// The real nodes shared by identifier and element assignment planning.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct AssignmentSyntaxPlan {
    pub(super) expression: NodeRef,
    pub(super) left: NodeRef,
    pub(super) operator: SyntaxKind,
    pub(super) right: NodeRef,
}

/// The source nodes needed by assignment contextual typing and execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SimpleAssignmentPlan {
    pub expression: NodeRef,
    pub left: NodeRef,
    pub operator: SyntaxKind,
    pub right: NodeRef,
    pub target_symbol: SemanticSymbolId,
    pub target_type_node: Option<NodeRef>,
}

/// A direct top-level write whose receiver names one same-file source class.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct OwnClassPropertyAssignmentPlan {
    pub(super) statement: NodeRef,
    pub(super) expression: NodeRef,
    pub(super) left: NodeRef,
    pub(super) right: NodeRef,
    pub(super) receiver: NodeRef,
    pub(super) receiver_symbol: SemanticSymbolId,
    pub(super) class_symbol: SemanticSymbolId,
    pub(super) class_declaration: NodeRef,
    pub(super) side: super::classes::ClassPropertySide,
}

/// One binder-authenticated `CommonJS` export assignment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CommonJsAssignmentPlan {
    pub(super) expression: NodeRef,
    pub(super) left: NodeRef,
    pub(super) right: NodeRef,
    pub(super) target_symbol: SemanticSymbolId,
}

/// One binder-authenticated property assignment on a preceding source callable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ArrowExpandoAssignmentPlan {
    pub(super) expression: NodeRef,
    pub(super) left: NodeRef,
    pub(super) right: NodeRef,
    pub(super) receiver: NodeRef,
    pub(super) variable_symbol: SemanticSymbolId,
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) property_symbol: SemanticSymbolId,
}

/// One imported namespace property owned by a matching module augmentation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ImportedNamespaceAssignmentPlan {
    pub(super) expression: NodeRef,
    pub(super) left: NodeRef,
    pub(super) right: NodeRef,
    pub(super) receiver: NodeRef,
    pub(super) alias_symbol: SemanticSymbolId,
    pub(super) namespace_symbol: SemanticSymbolId,
    pub(super) property_symbol: SemanticSymbolId,
    pub(super) property_type_node: NodeRef,
}

/// One binder-authenticated static property assignment on a source function.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct FunctionExpandoAssignmentPlan {
    pub(super) expression: NodeRef,
    pub(super) left: NodeRef,
    pub(super) right: NodeRef,
    pub(super) receiver: NodeRef,
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) property_symbol: SemanticSymbolId,
}

/// One binder-authenticated static property assignment on a JavaScript object.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ObjectExpandoAssignmentPlan {
    pub(super) expression: NodeRef,
    pub(super) left: NodeRef,
    pub(super) right: NodeRef,
    pub(super) receiver: NodeRef,
    pub(super) name: NodeRef,
    pub(super) index: Option<NodeRef>,
    pub(super) variable_symbol: SemanticSymbolId,
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) property_symbol: SemanticSymbolId,
}

/// One unbound prototype write that reuses a class member or function owner.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PrototypeAssignmentPlan {
    pub(super) expression: NodeRef,
    pub(super) left: NodeRef,
    pub(super) right: NodeRef,
    pub(super) receiver: NodeRef,
    pub(super) prototype: NodeRef,
    pub(super) receiver_symbol: SemanticSymbolId,
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) prototype_symbol: Option<SemanticSymbolId>,
    pub(super) property_symbol: Option<SemanticSymbolId>,
}

/// The syntactic position at which the assignment slice ended.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssignmentSyntaxRole {
    Statement,
    Expression,
    Operator,
    LeftHandSide,
    TargetDeclaration,
    TargetName,
    TargetModifier,
}

/// Valid TypeScript semantics that are outside this dependency-closed slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssignmentUnsupported {
    Syntax {
        node: NodeRef,
        kind: SyntaxKind,
        role: AssignmentSyntaxRole,
    },
    UnresolvedIdentifier(NodeRef),
    ResolverDeferred {
        node: NodeRef,
        error: CanonicalNameResolutionError,
    },
    AliasTarget {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    ShadowedCommonJsModule {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    BlockScopedTarget {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    NonVariableTarget {
        node: NodeRef,
        symbol: SemanticSymbolId,
        flags: SymbolFlags,
    },
    NonUniqueTarget {
        node: NodeRef,
        symbol: SemanticSymbolId,
        declaration_count: usize,
    },
    MergedTarget {
        node: NodeRef,
        source: SemanticSymbolId,
        target: SemanticSymbolId,
    },
    CrossFileTarget {
        node: NodeRef,
        declaration: NodeRef,
    },
    MissingTargetType(NodeRef),
    MissingTargetInitializer(NodeRef),
    TargetNotPrior {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    ChainedAssignment(NodeRef),
    NestedTarget(NodeRef),
    NonOrdinaryAssignment(NodeRef),
    NonOrdinaryVariable(NodeRef),
}

/// Malformed AST, binder, resolver, or checker-store provenance.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssignmentInvariant {
    WrongArena {
        file: FileId,
        expected: NodeArenaId,
        actual: NodeArenaId,
    },
    ArenaRevisionMismatch {
        file: FileId,
        expected: NodeArenaRevision,
        actual: NodeArenaRevision,
    },
    StoreSourceMismatch(NodeRef),
    MissingNode(NodeRef),
    NodeNotBound(NodeRef),
    MismatchedNodeData {
        node: NodeRef,
        kind: SyntaxKind,
    },
    InvalidParent {
        node: NodeRef,
        expected: Option<ts_ast::NodeId>,
        actual: Option<ts_ast::NodeId>,
    },
    InvalidStatementShape(NodeRef),
    InvalidIdentifierShape(NodeRef),
    InvalidOperatorToken(NodeRef),
    NameResolution(CanonicalNameResolutionError),
    InvalidSymbol(SemanticSymbolId),
    MissingExportSymbol(SemanticSymbolId),
    InvalidExportSymbol {
        value_symbol: SemanticSymbolId,
        export_symbol: SemanticSymbolId,
    },
    InvalidExportLocalShape(SemanticSymbolId),
    InvalidMergedSymbol(SemanticSymbolId),
    InvalidSymbolShape(SemanticSymbolId),
    MissingDeclarations(SemanticSymbolId),
    ValueDeclarationMismatch {
        symbol: SemanticSymbolId,
        declaration: NodeRef,
        value_declaration: Option<NodeRef>,
    },
    MissingDeclarationSymbol(NodeRef),
    DeclarationSymbolMismatch {
        declaration: NodeRef,
        expected: SemanticSymbolId,
        actual: SemanticSymbolId,
    },
    ResolvedSymbolMismatch {
        node: NodeRef,
        expected: SemanticSymbolId,
        actual: SemanticSymbolId,
    },
    MissingSourceSymbol(NodeRef),
    InvalidTargetParent {
        symbol: SemanticSymbolId,
        expected: Option<SemanticSymbolId>,
        actual: Option<SemanticSymbolId>,
    },
    LocalExportSymbolMismatch {
        declaration: NodeRef,
        expected: Option<SemanticSymbolId>,
        actual: Option<SemanticSymbolId>,
    },
    InvalidDeclarationList(NodeRef),
    InvalidVariableStatement(NodeRef),
    IdentifierNameMismatch {
        reference: NodeRef,
        declaration: NodeRef,
    },
}

/// Exact failure category used by source dispatch to distinguish capability
/// boundaries from corrupt provenance.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum AssignmentPlanError {
    Unsupported(AssignmentUnsupported),
    Invariant(AssignmentInvariant),
    DeclaredType(DeclaredTypeError),
}

impl From<AssignmentInvariant> for AssignmentPlanError {
    fn from(error: AssignmentInvariant) -> Self {
        Self::Invariant(error)
    }
}

struct AssignmentPlanner<'a, 'sources> {
    arena: &'a NodeArena,
    bound: &'a BoundFile,
    store: &'a CanonicalTypeMapperStore,
    host: &'a DeclaredTypeHost<'sources>,
    ambient_targets: &'a HashSet<SemanticSymbolId>,
    uninitialized_targets: &'a HashSet<SemanticSymbolId>,
    mutable_targets: &'a HashSet<SemanticSymbolId>,
}

struct CommonJsAssignmentPlanner<'a> {
    arena: &'a NodeArena,
    bound: &'a BoundFile,
    store: &'a CanonicalTypeMapperStore,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CommonJsNamedAssignmentShape {
    expression: NodeRef,
    left: NodeRef,
    right: NodeRef,
    receiver: NodeRef,
    module_receiver: Option<NodeRef>,
    name: NodeRef,
    alias: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RoutedValueSymbol {
    target: SemanticSymbolId,
    redirect: Option<(SemanticSymbolId, SemanticSymbolId)>,
    export_local: Option<SemanticSymbolId>,
}

/// Plans one simple assignment without publishing semantic state or resolver
/// callbacks with observable side effects.
pub(super) fn plan_simple_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    statement: NodeRef,
) -> Result<SimpleAssignmentPlan, AssignmentPlanError> {
    plan_simple_assignment_with_source_targets(
        arena,
        bound,
        store,
        host,
        &HashSet::new(),
        &HashSet::new(),
        statement,
    )
}

/// Selects ordinary element writes without changing identifier assignment rules.
pub(super) fn plan_element_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    statement: NodeRef,
) -> Result<Option<AssignmentSyntaxPlan>, AssignmentPlanError> {
    let planner = AssignmentPlanner {
        arena,
        bound,
        store,
        host,
        ambient_targets: &HashSet::new(),
        uninitialized_targets: &HashSet::new(),
        mutable_targets: &HashSet::new(),
    };
    let syntax = planner.plan_syntax(statement)?;
    Ok((syntax.operator == SyntaxKind::EqualsToken
        && matches!(
            planner.node(syntax.left)?.data,
            NodeData::ElementAccessExpression(_)
        ))
    .then_some(syntax))
}

/// Selects class writes before the ordinary identifier-assignment boundary.
pub(super) fn plan_own_class_property_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    statement: NodeRef,
) -> Result<Option<OwnClassPropertyAssignmentPlan>, AssignmentPlanError> {
    AssignmentPlanner {
        arena,
        bound,
        store,
        host,
        ambient_targets: &HashSet::new(),
        uninitialized_targets: &HashSet::new(),
        mutable_targets: &HashSet::new(),
    }
    .plan_own_class_property_assignment(statement)
}

/// Authenticates one direct `CommonJS` export alias without changing checker state.
pub(super) fn plan_commonjs_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
) -> Result<Option<CommonJsAssignmentPlan>, AssignmentPlanError> {
    CommonJsAssignmentPlanner {
        arena,
        bound,
        store,
    }
    .plan(statement)
}

/// Authenticates static `exports` and `module.exports` member assignments.
#[cfg_attr(not(test), allow(dead_code))]
pub(super) fn plan_commonjs_named_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
) -> Result<Option<CommonJsAssignmentPlan>, AssignmentPlanError> {
    CommonJsAssignmentPlanner {
        arena,
        bound,
        store,
    }
    .plan_named(statement)
}

/// Authenticates source arrow/function-expression expandos against binder symbols.
pub(super) fn plan_arrow_expando_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
) -> Result<Option<ArrowExpandoAssignmentPlan>, AssignmentPlanError> {
    CommonJsAssignmentPlanner {
        arena,
        bound,
        store,
    }
    .plan_arrow_expando(statement)
}

/// Authenticates `function.property = value` against the original binder symbols.
pub(super) fn plan_function_expando_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
) -> Result<Option<FunctionExpandoAssignmentPlan>, AssignmentPlanError> {
    CommonJsAssignmentPlanner {
        arena,
        bound,
        store,
    }
    .plan_function_expando(statement)
}

/// Authenticates a write through an earlier binder-owned function expando.
pub(super) fn plan_nested_function_expando_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
) -> Result<Option<FunctionExpandoAssignmentPlan>, AssignmentPlanError> {
    CommonJsAssignmentPlanner {
        arena,
        bound,
        store,
    }
    .plan_nested_function_expando(statement)
}

/// Authenticates `object.name` and `object["name"]` against binder-owned exports.
pub(super) fn plan_javascript_object_expando_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
) -> Result<Option<ObjectExpandoAssignmentPlan>, AssignmentPlanError> {
    CommonJsAssignmentPlanner {
        arena,
        bound,
        store,
    }
    .plan_object_expando(statement)
}

/// Authenticates class-member and JavaScript function-alias prototype writes.
pub(super) fn plan_prototype_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
) -> Result<Option<PrototypeAssignmentPlan>, AssignmentPlanError> {
    CommonJsAssignmentPlanner {
        arena,
        bound,
        store,
    }
    .plan_prototype(statement)
}

/// Authenticates an imported property against its ambient module declaration.
pub(super) fn plan_imported_namespace_assignment(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    statement: NodeRef,
) -> Result<Option<ImportedNamespaceAssignmentPlan>, AssignmentPlanError> {
    CommonJsAssignmentPlanner {
        arena,
        bound,
        store,
    }
    .plan_imported_namespace(statement)
}

/// Plans one assignment with source-minted capabilities for exact mutable
/// ambient declarations. Membership is not sufficient by itself: the target
/// must still prove the direct `declare var`/`declare let` AST and binder shape.
pub(super) fn plan_simple_assignment_with_ambient_targets(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    ambient_targets: &HashSet<SemanticSymbolId>,
    statement: NodeRef,
) -> Result<SimpleAssignmentPlan, AssignmentPlanError> {
    plan_simple_assignment_with_source_targets(
        arena,
        bound,
        store,
        host,
        ambient_targets,
        &HashSet::new(),
        statement,
    )
}

/// Plans one assignment with source-minted capabilities for exact mutable
/// ambient declarations and exact annotated uninitialized variables.
/// Membership is never sufficient by itself: the target's symbol, declaration,
/// binding kind, initializer shape, and statement provenance are all revalidated.
pub(super) fn plan_simple_assignment_with_source_targets(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    ambient_targets: &HashSet<SemanticSymbolId>,
    uninitialized_targets: &HashSet<SemanticSymbolId>,
    statement: NodeRef,
) -> Result<SimpleAssignmentPlan, AssignmentPlanError> {
    plan_simple_assignment_with_all_source_targets(
        arena,
        bound,
        store,
        host,
        ambient_targets,
        uninitialized_targets,
        &HashSet::new(),
        statement,
    )
}

/// Plans an assignment with exact ambient, uninitialized, or mutable source targets.
#[allow(clippy::too_many_arguments)] // Each target family has a distinct provenance contract.
pub(super) fn plan_simple_assignment_with_all_source_targets(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    ambient_targets: &HashSet<SemanticSymbolId>,
    uninitialized_targets: &HashSet<SemanticSymbolId>,
    mutable_targets: &HashSet<SemanticSymbolId>,
    statement: NodeRef,
) -> Result<SimpleAssignmentPlan, AssignmentPlanError> {
    AssignmentPlanner {
        arena,
        bound,
        store,
        host,
        ambient_targets,
        uninitialized_targets,
        mutable_targets,
    }
    .plan(statement)
}

impl CommonJsAssignmentPlanner<'_> {
    #[allow(clippy::too_many_lines)] // Authenticate the complete prototype chain and its owner.
    fn plan_prototype(
        &self,
        statement: NodeRef,
    ) -> Result<Option<PrototypeAssignmentPlan>, AssignmentPlanError> {
        self.preflight_program()?;
        let Some(facts) = self.bound.source_facts() else {
            return Ok(None);
        };
        if facts.is_declaration_file() {
            return Ok(None);
        }

        let statement_record = self.node(statement)?;
        let NodeData::ExpressionStatement(statement_data) = &statement_record.data else {
            return Ok(None);
        };
        if statement_record.parent != Some(self.bound.source_file().node)
            || statement_record.flags.0 != 0
            || statement_data.flow_node.is_some()
        {
            return Err(AssignmentInvariant::InvalidStatementShape(statement).into());
        }
        let expression = self.reference(statement_data.expression);
        self.require_parent(expression, Some(statement.node))?;
        let expression_record = self.node(expression)?;
        let NodeData::BinaryExpression(binary) = &expression_record.data else {
            return Ok(None);
        };
        if expression_record.flags.0 != 0
            || binary.symbol.is_some()
            || binary.type_.is_some()
            || binary.modifiers.is_some()
            || binary.facts != 0
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryAssignment(expression),
            ));
        }
        let operator = self.reference(binary.operator_token);
        self.require_parent(operator, Some(expression.node))?;
        let operator_record = self.node(operator)?;
        if !matches!(operator_record.data, NodeData::Token(_)) || operator_record.flags.0 != 0 {
            return Err(AssignmentInvariant::InvalidOperatorToken(operator).into());
        }
        if operator_record.kind != SyntaxKind::EqualsToken
            || self.bound.symbol(expression).is_some()
        {
            return Ok(None);
        }

        let left = self.reference(binary.left);
        let right = self.reference(binary.right);
        self.require_parent(left, Some(expression.node))?;
        self.require_parent(right, Some(expression.node))?;
        let left_record = self.node(left)?;
        let NodeData::PropertyAccessExpression(member_access) = &left_record.data else {
            return Ok(None);
        };
        if left_record.flags.0 != 0
            || member_access.flow_node.is_some()
            || member_access.question_dot_token.is_some()
            || member_access.facts != 0
        {
            return Err(AssignmentInvariant::InvalidStatementShape(left).into());
        }
        let prototype = self.reference(member_access.expression);
        let member_name = self.reference(member_access.name);
        self.require_parent(prototype, Some(left.node))?;
        self.require_parent(member_name, Some(left.node))?;
        let prototype_record = self.node(prototype)?;
        let NodeData::PropertyAccessExpression(prototype_access) = &prototype_record.data else {
            return Ok(None);
        };
        if prototype_record.flags.0 != 0
            || prototype_access.flow_node.is_some()
            || prototype_access.question_dot_token.is_some()
            || prototype_access.facts != 0
        {
            return Err(AssignmentInvariant::InvalidStatementShape(prototype).into());
        }
        let receiver = self.reference(prototype_access.expression);
        let prototype_name = self.reference(prototype_access.name);
        self.require_parent(receiver, Some(prototype.node))?;
        self.require_parent(prototype_name, Some(prototype.node))?;
        if !self.is_identifier_named(prototype_name, "prototype")? {
            return Ok(None);
        }
        let receiver_record = self.node(receiver)?;
        let NodeData::Identifier(receiver_name) = &receiver_record.data else {
            return Ok(None);
        };
        if receiver_record.flags.0 != 0
            || receiver_name.flow_node.is_some()
            || receiver_name.text.is_empty()
        {
            return Err(AssignmentInvariant::InvalidIdentifierShape(receiver).into());
        }
        let member_record = self.node(member_name)?;
        let NodeData::Identifier(member_name_data) = &member_record.data else {
            return Ok(None);
        };
        if member_record.flags.0 != 0
            || member_name_data.flow_node.is_some()
            || member_name_data.text.is_empty()
        {
            return Err(AssignmentInvariant::InvalidIdentifierShape(member_name).into());
        }

        let Some(receiver_symbol) = self
            .bound
            .locals(self.bound.source_file())
            .and_then(|locals| self.store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&receiver_name.text))
        else {
            return Ok(None);
        };
        let receiver_symbol_record = self
            .store
            .symbol(receiver_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(receiver_symbol))?;
        if self.store.get_merged_symbol(receiver_symbol) != Some(receiver_symbol) {
            return Err(AssignmentInvariant::InvalidMergedSymbol(receiver_symbol).into());
        }
        if let Some(cached) = self
            .store
            .symbol_node_links(receiver)
            .and_then(|links| links.resolved_symbol)
            && cached != receiver_symbol
        {
            return Err(AssignmentInvariant::ResolvedSymbolMismatch {
                node: receiver,
                expected: receiver_symbol,
                actual: cached,
            }
            .into());
        }

        let (owner_symbol, prototype_symbol, property_symbol) = if receiver_symbol_record.flags()
            == SymbolFlags::CLASS
        {
            let owner = receiver_symbol_record;
            let Some([declaration]) = owner.declarations() else {
                return Err(AssignmentInvariant::InvalidSymbolShape(receiver_symbol).into());
            };
            if owner.check_flags() != CheckFlags::NONE
                || owner.name().as_utf8() != Some(receiver_name.text.as_str())
                || owner.value_declaration() != Some(*declaration)
                || owner.parent().is_some()
                || owner.export_symbol().is_some()
                || self.bound.symbol(*declaration) != Some(receiver_symbol)
                || self.store.source_node_kind(*declaration) != Some(SyntaxKind::ClassDeclaration)
            {
                return Err(AssignmentInvariant::InvalidSymbolShape(receiver_symbol).into());
            }
            let prototype_symbol = owner
                .exports()
                .and_then(|exports| self.store.symbol_table(exports))
                .and_then(|exports| exports.get_source("prototype"))
                .ok_or(AssignmentInvariant::MissingExportSymbol(receiver_symbol))?;
            let prototype_record = self
                .store
                .symbol(prototype_symbol)
                .ok_or(AssignmentInvariant::InvalidSymbol(prototype_symbol))?;
            if prototype_record.flags() != SymbolFlags::PROPERTY | SymbolFlags::PROTOTYPE
                || prototype_record.check_flags() != CheckFlags::NONE
                || prototype_record.declarations().is_some()
                || prototype_record.value_declaration().is_some()
                || prototype_record.members().is_some()
                || prototype_record.exports().is_some()
                || prototype_record.parent() != Some(receiver_symbol)
                || prototype_record.export_symbol().is_some()
                || self.store.get_merged_symbol(prototype_symbol) != Some(prototype_symbol)
            {
                return Err(AssignmentInvariant::InvalidSymbolShape(prototype_symbol).into());
            }
            let property_symbol = owner
                .members()
                .and_then(|members| self.store.symbol_table(members))
                .and_then(|members| members.get_source(&member_name_data.text))
                .ok_or(AssignmentInvariant::MissingExportSymbol(receiver_symbol))?;
            let property = self
                .store
                .symbol(property_symbol)
                .ok_or(AssignmentInvariant::InvalidSymbol(property_symbol))?;
            let Some([declaration]) = property.declarations() else {
                return Err(AssignmentInvariant::InvalidSymbolShape(property_symbol).into());
            };
            if property.flags() != SymbolFlags::METHOD
                || property.check_flags() != CheckFlags::NONE
                || property.name().as_utf8() != Some(member_name_data.text.as_str())
                || property.value_declaration() != Some(*declaration)
                || property.members().is_some()
                || property.exports().is_some()
                || property.parent() != Some(receiver_symbol)
                || property.export_symbol().is_some()
                || self.store.get_merged_symbol(property_symbol) != Some(property_symbol)
                || self.bound.symbol(*declaration) != Some(property_symbol)
                || self.store.source_node_kind(*declaration) != Some(SyntaxKind::MethodDeclaration)
            {
                return Err(AssignmentInvariant::InvalidSymbolShape(property_symbol).into());
            }
            (
                receiver_symbol,
                Some(prototype_symbol),
                Some(property_symbol),
            )
        } else if facts.is_javascript_file() {
            let Some(owner_symbol) =
                self.prototype_function_owner(receiver_symbol, &receiver_name.text)?
            else {
                return Ok(None);
            };
            (owner_symbol, None, None)
        } else {
            return Ok(None);
        };

        for (node, expected) in [(prototype, prototype_symbol), (left, property_symbol)] {
            let Some(expected) = expected else {
                continue;
            };
            if let Some(cached) = self
                .store
                .symbol_node_links(node)
                .and_then(|links| links.resolved_symbol)
                && cached != expected
            {
                return Err(AssignmentInvariant::ResolvedSymbolMismatch {
                    node,
                    expected,
                    actual: cached,
                }
                .into());
            }
        }

        Ok(Some(PrototypeAssignmentPlan {
            expression,
            left,
            right,
            receiver,
            prototype,
            receiver_symbol,
            owner_symbol,
            prototype_symbol,
            property_symbol,
        }))
    }

    fn prototype_function_owner(
        &self,
        symbol: SemanticSymbolId,
        expected_name: &str,
    ) -> Result<Option<SemanticSymbolId>, AssignmentPlanError> {
        let mut current = symbol;
        let mut expected = expected_name;
        for _ in 0..2 {
            let record = self
                .store
                .symbol(current)
                .ok_or(AssignmentInvariant::InvalidSymbol(current))?;
            let Some([declaration]) = record.declarations() else {
                return Ok(None);
            };
            if !matches!(
                record.flags(),
                SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::BLOCK_SCOPED_VARIABLE
            ) || record.check_flags() != CheckFlags::NONE
                || record.name().as_utf8() != Some(expected)
                || record.value_declaration() != Some(*declaration)
                || record.members().is_some()
                || record.exports().is_some()
                || record.parent().is_some()
                || record.export_symbol().is_some()
                || self.store.get_merged_symbol(current) != Some(current)
                || self.bound.symbol(*declaration) != Some(current)
            {
                return Err(AssignmentInvariant::InvalidSymbolShape(current).into());
            }
            let declaration_record = self.node(*declaration)?;
            let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
                return Ok(None);
            };
            let Some(initializer) = variable.initializer.map(|node| self.reference(node)) else {
                return Ok(None);
            };
            self.require_parent(initializer, Some(declaration.node))?;
            match &self.node(initializer)?.data {
                NodeData::Identifier(identifier) if !identifier.text.is_empty() => {
                    expected = identifier.text.as_str();
                    current = self
                        .bound
                        .locals(self.bound.source_file())
                        .and_then(|locals| self.store.symbol_table(locals))
                        .and_then(|locals| locals.get_source(expected))
                        .ok_or(AssignmentInvariant::MissingDeclarationSymbol(initializer))?;
                    if let Some(cached) = self
                        .store
                        .symbol_node_links(initializer)
                        .and_then(|links| links.resolved_symbol)
                        && cached != current
                    {
                        return Err(AssignmentInvariant::ResolvedSymbolMismatch {
                            node: initializer,
                            expected: current,
                            actual: cached,
                        }
                        .into());
                    }
                }
                NodeData::FunctionExpression(_) => {
                    let owner = self
                        .bound
                        .symbol(initializer)
                        .ok_or(AssignmentInvariant::MissingDeclarationSymbol(initializer))?;
                    let owner_record = self
                        .store
                        .symbol(owner)
                        .ok_or(AssignmentInvariant::InvalidSymbol(owner))?;
                    if owner_record.flags() != SymbolFlags::FUNCTION
                        || owner_record.check_flags() != CheckFlags::NONE
                        || owner_record.name() != InternalSymbolName::Function.as_ref()
                        || owner_record.declarations() != Some(&[initializer])
                        || owner_record.value_declaration() != Some(initializer)
                        || owner_record.members().is_some()
                        || owner_record.exports().is_some()
                        || owner_record.parent().is_some()
                        || owner_record.export_symbol().is_some()
                        || self.store.get_merged_symbol(owner) != Some(owner)
                    {
                        return Err(AssignmentInvariant::InvalidSymbolShape(owner).into());
                    }
                    return Ok(Some(owner));
                }
                _ => return Ok(None),
            }
        }
        Ok(None)
    }

    #[allow(clippy::too_many_lines)] // Proves the assignment, import, and ambient member together.
    fn plan_imported_namespace(
        &self,
        statement: NodeRef,
    ) -> Result<Option<ImportedNamespaceAssignmentPlan>, AssignmentPlanError> {
        self.preflight_program()?;
        if self.bound.source_facts().is_none_or(|facts| {
            facts.is_javascript_file() || facts.is_declaration_file() || !facts.is_external_module()
        }) {
            return Ok(None);
        }

        let statement_record = self.node(statement)?;
        let NodeData::ExpressionStatement(statement_data) = &statement_record.data else {
            return Ok(None);
        };
        if statement_record.parent != Some(self.bound.source_file().node)
            || statement_record.flags.0 != 0
            || statement_data.flow_node.is_some()
        {
            return Err(AssignmentInvariant::InvalidStatementShape(statement).into());
        }
        let expression = self.reference(statement_data.expression);
        self.require_parent(expression, Some(statement.node))?;
        let expression_record = self.node(expression)?;
        let NodeData::BinaryExpression(binary) = &expression_record.data else {
            return Ok(None);
        };
        if expression_record.flags.0 != 0
            || binary.symbol.is_some()
            || binary.type_.is_some()
            || binary.facts != 0
            || binary.modifiers.is_some()
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryAssignment(expression),
            ));
        }
        let operator = self.reference(binary.operator_token);
        self.require_parent(operator, Some(expression.node))?;
        let operator_record = self.node(operator)?;
        if !matches!(operator_record.data, NodeData::Token(_)) || operator_record.flags.0 != 0 {
            return Err(AssignmentInvariant::InvalidOperatorToken(operator).into());
        }
        if operator_record.kind != SyntaxKind::EqualsToken
            || self.bound.symbol(expression).is_some()
        {
            return Ok(None);
        }

        let left = self.reference(binary.left);
        let right = self.reference(binary.right);
        self.require_parent(left, Some(expression.node))?;
        self.require_parent(right, Some(expression.node))?;
        let left_record = self.node(left)?;
        let NodeData::PropertyAccessExpression(access) = &left_record.data else {
            return Ok(None);
        };
        if left_record.kind != SyntaxKind::PropertyAccessExpression
            || left_record.flags.0 != 0
            || access.flow_node.is_some()
            || access.question_dot_token.is_some()
            || access.facts != 0
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::Syntax {
                    node: left,
                    kind: left_record.kind,
                    role: AssignmentSyntaxRole::LeftHandSide,
                },
            ));
        }
        let receiver = self.reference(access.expression);
        let name = self.reference(access.name);
        self.require_parent(receiver, Some(left.node))?;
        self.require_parent(name, Some(left.node))?;
        let receiver_record = self.node(receiver)?;
        let NodeData::Identifier(receiver_name) = &receiver_record.data else {
            return Ok(None);
        };
        let name_record = self.node(name)?;
        let NodeData::Identifier(property_name) = &name_record.data else {
            return Ok(None);
        };
        if receiver_record.flags.0 != 0
            || receiver_name.flow_node.is_some()
            || receiver_name.text.is_empty()
            || name_record.flags.0 != 0
            || property_name.flow_node.is_some()
            || property_name.text.is_empty()
        {
            return Err(AssignmentInvariant::InvalidIdentifierShape(receiver).into());
        }

        let Some(alias_symbol) = self
            .bound
            .locals(self.bound.source_file())
            .and_then(|locals| self.store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&receiver_name.text))
        else {
            return Ok(None);
        };
        let alias = self
            .store
            .symbol(alias_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(alias_symbol))?;
        if alias.flags() != SymbolFlags::ALIAS {
            return Ok(None);
        }
        let Some([import]) = alias.declarations() else {
            return Err(AssignmentInvariant::InvalidSymbolShape(alias_symbol).into());
        };
        let import = *import;
        if alias.check_flags() != CheckFlags::NONE
            || alias.name().as_bytes() != receiver_name.text.as_bytes()
            || alias.value_declaration().is_some()
            || alias.members().is_some()
            || alias.exports().is_some()
            || alias.export_symbol().is_some()
            || self.store.get_merged_symbol(alias_symbol) != Some(alias_symbol)
            || self.bound.symbol(import) != Some(alias_symbol)
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(alias_symbol).into());
        }
        if let Some(cached) = self
            .store
            .symbol_node_links(receiver)
            .and_then(|links| links.resolved_symbol)
            && cached != alias_symbol
        {
            return Err(AssignmentInvariant::ResolvedSymbolMismatch {
                node: receiver,
                expected: alias_symbol,
                actual: cached,
            }
            .into());
        }

        let import_record = self.node(import)?;
        let (import_statement, specifier) = match &import_record.data {
            NodeData::ImportEqualsDeclaration(import_data)
                if import_record.kind == SyntaxKind::ImportEqualsDeclaration
                    && !import_data.is_type_only =>
            {
                let reference = self.reference(import_data.module_reference);
                self.require_parent(reference, Some(import.node))?;
                let reference_record = self.node(reference)?;
                let NodeData::ExternalModuleReference(external) = &reference_record.data else {
                    return Ok(None);
                };
                (import, self.reference(external.expression))
            }
            NodeData::NamespaceImport(namespace)
                if import_record.kind == SyntaxKind::NamespaceImport
                    && namespace.local_symbol.is_none()
                    && namespace.symbol.is_none() =>
            {
                let Some(clause) = import_record.parent.map(|parent| self.reference(parent)) else {
                    return Err(AssignmentInvariant::InvalidSymbolShape(alias_symbol).into());
                };
                let clause_record = self.node(clause)?;
                let NodeData::ImportClause(clause_data) = &clause_record.data else {
                    return Err(AssignmentInvariant::InvalidSymbolShape(alias_symbol).into());
                };
                let Some(import_statement) =
                    clause_record.parent.map(|parent| self.reference(parent))
                else {
                    return Err(AssignmentInvariant::InvalidSymbolShape(alias_symbol).into());
                };
                let statement_record = self.node(import_statement)?;
                let NodeData::ImportDeclaration(import_data) = &statement_record.data else {
                    return Err(AssignmentInvariant::InvalidSymbolShape(alias_symbol).into());
                };
                if clause_data.named_bindings != Some(import.node)
                    || import_data.import_clause != Some(clause.node)
                {
                    return Err(AssignmentInvariant::InvalidSymbolShape(alias_symbol).into());
                }
                (
                    import_statement,
                    self.reference(import_data.module_specifier),
                )
            }
            _ => return Ok(None),
        };
        let import_statement_record = self.node(import_statement)?;
        if import_statement_record.parent != Some(self.bound.source_file().node)
            || import_statement_record.range.end > statement_record.range.start
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::TargetNotPrior {
                    node: receiver,
                    symbol: alias_symbol,
                },
            ));
        }
        let specifier_record = self.node(specifier)?;
        let NodeData::StringLiteral(module_name) = &specifier_record.data else {
            return Ok(None);
        };
        if specifier_record.kind != SyntaxKind::StringLiteral
            || specifier_record.flags.0 != 0
            || module_name.token_flags.0 != 0
            || module_name.text.is_empty()
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(alias_symbol).into());
        }

        let source_record = self.node(self.bound.source_file())?;
        let NodeData::SourceFile(source_data) = &source_record.data else {
            return Err(AssignmentInvariant::StoreSourceMismatch(self.bound.source_file()).into());
        };
        let mut matched = None;
        for candidate in &source_data.statements.nodes {
            let namespace_declaration = self.reference(*candidate);
            let namespace_record = self.node(namespace_declaration)?;
            let NodeData::ModuleDeclaration(namespace_data) = &namespace_record.data else {
                continue;
            };
            let namespace_name = self.reference(namespace_data.name);
            let namespace_name_record = self.node(namespace_name)?;
            let NodeData::StringLiteral(augmentation_name) = &namespace_name_record.data else {
                continue;
            };
            if augmentation_name.text != module_name.text
                || !self
                    .bound
                    .module_augmentations()
                    .iter()
                    .any(|augmentation| augmentation.name() == namespace_name)
            {
                continue;
            }
            let raw_namespace = self.bound.symbol(namespace_declaration).ok_or(
                AssignmentInvariant::MissingDeclarationSymbol(namespace_declaration),
            )?;
            let namespace_symbol = self
                .store
                .get_merged_symbol(raw_namespace)
                .ok_or(AssignmentInvariant::InvalidMergedSymbol(raw_namespace))?;
            let namespace = self
                .store
                .symbol(namespace_symbol)
                .ok_or(AssignmentInvariant::InvalidSymbol(namespace_symbol))?;
            let Some(property_symbol) = namespace
                .exports()
                .and_then(|exports| self.store.symbol_table(exports))
                .and_then(|exports| exports.get_source(&property_name.text))
                .and_then(|symbol| self.store.get_merged_symbol(symbol))
            else {
                continue;
            };
            let property = self
                .store
                .symbol(property_symbol)
                .ok_or(AssignmentInvariant::InvalidSymbol(property_symbol))?;
            let Some([property_declaration]) = property.declarations() else {
                return Err(AssignmentInvariant::InvalidSymbolShape(property_symbol).into());
            };
            let property_declaration = *property_declaration;
            let declaration_record = self.node(property_declaration)?;
            let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
                return Err(AssignmentInvariant::InvalidSymbolShape(property_symbol).into());
            };
            let Some(annotation) = variable.type_.map(|annotation| self.reference(annotation))
            else {
                return Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::MissingTargetType(property_declaration),
                ));
            };
            self.require_parent(annotation, Some(property_declaration.node))?;
            let list = declaration_record
                .parent
                .map(|node| self.reference(node))
                .ok_or(AssignmentInvariant::InvalidDeclarationList(
                    property_declaration,
                ))?;
            let list_record = self.node(list)?;
            let NodeData::VariableDeclarationList(list_data) = &list_record.data else {
                return Err(AssignmentInvariant::InvalidDeclarationList(list).into());
            };
            let member_statement = list_record
                .parent
                .map(|node| self.reference(node))
                .ok_or(AssignmentInvariant::InvalidVariableStatement(list))?;
            let member_statement_record = self.node(member_statement)?;
            let NodeData::VariableStatement(member_statement_data) = &member_statement_record.data
            else {
                return Err(AssignmentInvariant::InvalidVariableStatement(member_statement).into());
            };
            let Some(body) = namespace_data.body.map(|body| self.reference(body)) else {
                return Err(AssignmentInvariant::InvalidSymbolShape(namespace_symbol).into());
            };
            let body_record = self.node(body)?;
            let NodeData::ModuleBlock(module_block) = &body_record.data else {
                return Err(AssignmentInvariant::InvalidSymbolShape(namespace_symbol).into());
            };
            if !matches!(
                property.flags(),
                SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::BLOCK_SCOPED_VARIABLE
            ) || property.check_flags() != CheckFlags::NONE
                || property.name().as_bytes() != property_name.text.as_bytes()
                || property.value_declaration() != Some(property_declaration)
                || property.members().is_some()
                || property.exports().is_some()
                || property.export_symbol().is_some()
                || self.store.get_parent_of_symbol(property_symbol) != Some(namespace_symbol)
                || self
                    .bound
                    .symbol(property_declaration)
                    .and_then(|symbol| self.store.get_merged_symbol(symbol))
                    != Some(property_symbol)
                || variable.initializer.is_some()
                || variable.symbol.is_some()
                || variable.local_symbol.is_some()
                || variable.facts != 0
                || declaration_record.parent != Some(list.node)
                || list_record.kind != SyntaxKind::VariableDeclarationList
                || list_data.facts != 0
                || list_data
                    .declarations
                    .nodes
                    .iter()
                    .filter(|candidate| **candidate == property_declaration.node)
                    .count()
                    != 1
                || member_statement_record.kind != SyntaxKind::VariableStatement
                || member_statement_record.parent != Some(body.node)
                || member_statement_data.declaration_list != list.node
                || member_statement_data.flow_node.is_some()
                || member_statement_data.facts != 0
                || body_record.kind != SyntaxKind::ModuleBlock
                || body_record.parent != Some(namespace_declaration.node)
                || module_block.flow_node.is_some()
                || module_block.facts != 0
                || module_block
                    .statements
                    .nodes
                    .iter()
                    .filter(|candidate| **candidate == member_statement.node)
                    .count()
                    != 1
            {
                return Err(AssignmentInvariant::InvalidSymbolShape(property_symbol).into());
            }
            let plan = ImportedNamespaceAssignmentPlan {
                expression,
                left,
                right,
                receiver,
                alias_symbol,
                namespace_symbol,
                property_symbol,
                property_type_node: annotation,
            };
            if matched.replace(plan).is_some() {
                return Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::NonUniqueTarget {
                        node: left,
                        symbol: property_symbol,
                        declaration_count: 2,
                    },
                ));
            }
        }
        Ok(matched)
    }

    #[allow(clippy::too_many_lines)] // Proves the assignment and its complete function owner.
    fn plan_function_expando(
        &self,
        statement: NodeRef,
    ) -> Result<Option<FunctionExpandoAssignmentPlan>, AssignmentPlanError> {
        self.preflight_program()?;
        if self
            .bound
            .source_facts()
            .is_none_or(ts_binder::CanonicalSourceFileFacts::is_declaration_file)
        {
            return Ok(None);
        }

        let statement_node = self.node(statement)?;
        let NodeData::ExpressionStatement(statement_data) = &statement_node.data else {
            return Ok(None);
        };
        if statement_node.flags.0 != 0 || statement_data.flow_node.is_some() {
            return Err(AssignmentInvariant::InvalidStatementShape(statement).into());
        }
        if statement_node.parent != Some(self.bound.source_file().node) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NestedTarget(statement),
            ));
        }

        let expression = self.reference(statement_data.expression);
        self.require_parent(expression, Some(statement.node))?;
        let expression_node = self.node(expression)?;
        let NodeData::BinaryExpression(binary) = &expression_node.data else {
            return Ok(None);
        };
        if expression_node.flags.0 != 0
            || binary.symbol.is_some()
            || binary.type_.is_some()
            || binary.facts != 0
            || binary.modifiers.is_some()
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryAssignment(expression),
            ));
        }
        let operator = self.reference(binary.operator_token);
        self.require_parent(operator, Some(expression.node))?;
        let operator_node = self.node(operator)?;
        if !matches!(operator_node.data, NodeData::Token(_)) || operator_node.flags.0 != 0 {
            return Err(AssignmentInvariant::InvalidOperatorToken(operator).into());
        }
        if operator_node.kind != SyntaxKind::EqualsToken {
            return Ok(None);
        }

        let left = self.reference(binary.left);
        let right = self.reference(binary.right);
        self.require_parent(left, Some(expression.node))?;
        self.require_parent(right, Some(expression.node))?;
        let left_node = self.node(left)?;
        let NodeData::PropertyAccessExpression(access) = &left_node.data else {
            return Ok(None);
        };
        if left_node.flags.0 != 0
            || access.flow_node.is_some()
            || access.question_dot_token.is_some()
            || access.facts != 0
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::Syntax {
                    node: left,
                    kind: left_node.kind,
                    role: AssignmentSyntaxRole::LeftHandSide,
                },
            ));
        }
        let receiver = self.reference(access.expression);
        let name = self.reference(access.name);
        self.require_parent(receiver, Some(left.node))?;
        self.require_parent(name, Some(left.node))?;
        let receiver_record = self.node(receiver)?;
        let NodeData::Identifier(receiver_name) = &receiver_record.data else {
            return Ok(None);
        };
        if receiver_record.flags.0 != 0
            || receiver_name.flow_node.is_some()
            || receiver_name.text.is_empty()
        {
            return Err(AssignmentInvariant::InvalidIdentifierShape(receiver).into());
        }
        let property_name_record = self.node(name)?;
        let NodeData::Identifier(property_name) = &property_name_record.data else {
            return Ok(None);
        };
        if property_name_record.flags.0 != 0
            || property_name.flow_node.is_some()
            || property_name.text.is_empty()
        {
            return Err(AssignmentInvariant::InvalidIdentifierShape(name).into());
        }

        let Some(property_symbol) = self.bound.symbol(expression) else {
            return Ok(None);
        };
        let property = self
            .store
            .symbol(property_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(property_symbol))?;
        let Some(owner_symbol) = property.parent() else {
            return Ok(None);
        };
        let owner = self
            .store
            .symbol(owner_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(owner_symbol))?;
        let Some(declaration) = owner.value_declaration() else {
            return Ok(None);
        };
        if self.store.source_node_kind(declaration) != Some(SyntaxKind::FunctionDeclaration)
            || owner.flags() != SymbolFlags::FUNCTION
            || owner.parent().is_some()
        {
            return Ok(None);
        }
        if property.flags() != SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT
            || property.check_flags() != CheckFlags::NONE
            || property.name().as_bytes() != property_name.text.as_bytes()
            || property.declarations() != Some(&[expression])
            || property.value_declaration() != Some(expression)
            || property.members().is_some()
            || property.exports().is_some()
            || property.export_symbol().is_some()
            || self.store.get_merged_symbol(property_symbol) != Some(property_symbol)
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(property_symbol).into());
        }
        if owner.check_flags() != CheckFlags::NONE
            || owner.name().as_bytes() != receiver_name.text.as_bytes()
            || owner.declarations() != Some(&[declaration])
            || owner.members().is_some()
            || owner.export_symbol().is_some()
            || self.store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
            || self.bound.symbol(declaration) != Some(owner_symbol)
            || !super::source_callables::source_function_owner_expando_exports_are_valid(
                self.store,
                owner_symbol,
                declaration,
            )
            || owner
                .exports()
                .and_then(|exports| self.store.symbol_table(exports))
                .and_then(|exports| exports.get_source(&property_name.text))
                != Some(property_symbol)
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(owner_symbol).into());
        }
        if self
            .bound
            .locals(self.bound.source_file())
            .and_then(|locals| self.store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&receiver_name.text))
            != Some(owner_symbol)
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(owner_symbol).into());
        }
        if let Some(cached) = self
            .store
            .symbol_node_links(receiver)
            .and_then(|links| links.resolved_symbol)
            && cached != owner_symbol
        {
            return Err(AssignmentInvariant::ResolvedSymbolMismatch {
                node: receiver,
                expected: owner_symbol,
                actual: cached,
            }
            .into());
        }

        Ok(Some(FunctionExpandoAssignmentPlan {
            expression,
            left,
            right,
            receiver,
            owner_symbol,
            property_symbol,
        }))
    }

    #[allow(clippy::too_many_lines)] // Reuse the proven outer assignment and validate this write.
    fn plan_nested_function_expando(
        &self,
        statement: NodeRef,
    ) -> Result<Option<FunctionExpandoAssignmentPlan>, AssignmentPlanError> {
        self.preflight_program()?;
        if self
            .bound
            .source_facts()
            .is_none_or(|facts| !facts.is_javascript_file() || facts.is_declaration_file())
        {
            return Ok(None);
        }

        let statement_record = self.node(statement)?;
        let NodeData::ExpressionStatement(statement_data) = &statement_record.data else {
            return Ok(None);
        };
        if statement_record.parent != Some(self.bound.source_file().node)
            || statement_record.flags.0 != 0
            || statement_data.flow_node.is_some()
        {
            return Err(AssignmentInvariant::InvalidStatementShape(statement).into());
        }
        let expression = self.reference(statement_data.expression);
        self.require_parent(expression, Some(statement.node))?;
        let expression_record = self.node(expression)?;
        let NodeData::BinaryExpression(binary) = &expression_record.data else {
            return Ok(None);
        };
        if expression_record.flags.0 != 0
            || binary.symbol.is_some()
            || binary.type_.is_some()
            || binary.modifiers.is_some()
            || binary.facts != 0
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryAssignment(expression),
            ));
        }
        let operator = self.reference(binary.operator_token);
        self.require_parent(operator, Some(expression.node))?;
        let operator_record = self.node(operator)?;
        if !matches!(operator_record.data, NodeData::Token(_)) || operator_record.flags.0 != 0 {
            return Err(AssignmentInvariant::InvalidOperatorToken(operator).into());
        }
        if operator_record.kind != SyntaxKind::EqualsToken
            || self.bound.symbol(expression).is_some()
        {
            return Ok(None);
        }

        let left = self.reference(binary.left);
        let right = self.reference(binary.right);
        self.require_parent(left, Some(expression.node))?;
        self.require_parent(right, Some(expression.node))?;
        let left_record = self.node(left)?;
        let NodeData::PropertyAccessExpression(nested) = &left_record.data else {
            return Ok(None);
        };
        if left_record.flags.0 != 0
            || nested.flow_node.is_some()
            || nested.question_dot_token.is_some()
            || nested.facts != 0
        {
            return Err(AssignmentInvariant::InvalidStatementShape(left).into());
        }
        let parent = self.reference(nested.expression);
        let nested_name = self.reference(nested.name);
        self.require_parent(parent, Some(left.node))?;
        self.require_parent(nested_name, Some(left.node))?;
        let nested_name_record = self.node(nested_name)?;
        let NodeData::Identifier(nested_identifier) = &nested_name_record.data else {
            return Ok(None);
        };
        if nested_name_record.flags.0 != 0
            || nested_identifier.flow_node.is_some()
            || nested_identifier.text.is_empty()
        {
            return Err(AssignmentInvariant::InvalidIdentifierShape(nested_name).into());
        }
        let parent_record = self.node(parent)?;
        let NodeData::PropertyAccessExpression(property_access) = &parent_record.data else {
            return Ok(None);
        };
        if parent_record.flags.0 != 0
            || property_access.flow_node.is_some()
            || property_access.question_dot_token.is_some()
            || property_access.facts != 0
        {
            return Err(AssignmentInvariant::InvalidStatementShape(parent).into());
        }
        let receiver = self.reference(property_access.expression);
        let property_name = self.reference(property_access.name);
        self.require_parent(receiver, Some(parent.node))?;
        self.require_parent(property_name, Some(parent.node))?;
        let receiver_record = self.node(receiver)?;
        let NodeData::Identifier(receiver_name) = &receiver_record.data else {
            return Ok(None);
        };
        let property_name_record = self.node(property_name)?;
        let NodeData::Identifier(property_identifier) = &property_name_record.data else {
            return Ok(None);
        };
        if receiver_record.flags.0 != 0
            || receiver_name.flow_node.is_some()
            || receiver_name.text.is_empty()
            || property_name_record.flags.0 != 0
            || property_identifier.flow_node.is_some()
            || property_identifier.text.is_empty()
        {
            return Err(AssignmentInvariant::InvalidIdentifierShape(receiver).into());
        }

        let Some(owner_symbol) = self
            .bound
            .locals(self.bound.source_file())
            .and_then(|locals| self.store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&receiver_name.text))
        else {
            return Ok(None);
        };
        let owner = self
            .store
            .symbol(owner_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(owner_symbol))?;
        if owner.flags() != SymbolFlags::FUNCTION {
            return Ok(None);
        }
        let Some(property_symbol) = owner
            .exports()
            .and_then(|exports| self.store.symbol_table(exports))
            .and_then(|exports| exports.get_source(&property_identifier.text))
        else {
            return Ok(None);
        };
        let declaration = self
            .store
            .symbol(property_symbol)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            .ok_or(AssignmentInvariant::MissingDeclarations(property_symbol))?;
        let previous_statement = self
            .node(declaration)?
            .parent
            .map(|node| self.reference(node))
            .ok_or(AssignmentInvariant::InvalidStatementShape(declaration))?;
        let Some(previous) = self.plan_function_expando(previous_statement)? else {
            return Err(AssignmentInvariant::InvalidSymbolShape(property_symbol).into());
        };
        if previous.owner_symbol != owner_symbol
            || previous.property_symbol != property_symbol
            || self.node(previous_statement)?.range.end > statement_record.range.start
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::TargetNotPrior {
                    node: parent,
                    symbol: property_symbol,
                },
            ));
        }
        for (node, expected) in [(receiver, owner_symbol), (parent, property_symbol)] {
            if let Some(cached) = self
                .store
                .symbol_node_links(node)
                .and_then(|links| links.resolved_symbol)
                && cached != expected
            {
                return Err(AssignmentInvariant::ResolvedSymbolMismatch {
                    node,
                    expected,
                    actual: cached,
                }
                .into());
            }
        }

        Ok(Some(FunctionExpandoAssignmentPlan {
            expression,
            left,
            right,
            receiver,
            owner_symbol,
            property_symbol,
        }))
    }

    #[allow(clippy::too_many_lines)] // Proves the complete object, receiver, and expando graph.
    fn plan_object_expando(
        &self,
        statement: NodeRef,
    ) -> Result<Option<ObjectExpandoAssignmentPlan>, AssignmentPlanError> {
        self.preflight_program()?;
        if self
            .bound
            .source_facts()
            .is_none_or(|facts| !facts.is_javascript_file() || facts.is_declaration_file())
        {
            return Ok(None);
        }

        let statement_node = self.node(statement)?;
        let NodeData::ExpressionStatement(statement_data) = &statement_node.data else {
            return Ok(None);
        };
        if statement_node.flags.0 != 0 || statement_data.flow_node.is_some() {
            return Err(AssignmentInvariant::InvalidStatementShape(statement).into());
        }
        if statement_node.parent != Some(self.bound.source_file().node) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NestedTarget(statement),
            ));
        }

        let expression = self.reference(statement_data.expression);
        self.require_parent(expression, Some(statement.node))?;
        let expression_node = self.node(expression)?;
        let NodeData::BinaryExpression(binary) = &expression_node.data else {
            return Ok(None);
        };
        if expression_node.flags.0 != 0
            || binary.symbol.is_some()
            || binary.type_.is_some()
            || binary.facts != 0
            || binary.modifiers.is_some()
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryAssignment(expression),
            ));
        }
        let operator = self.reference(binary.operator_token);
        self.require_parent(operator, Some(expression.node))?;
        let operator_node = self.node(operator)?;
        if !matches!(operator_node.data, NodeData::Token(_)) || operator_node.flags.0 != 0 {
            return Err(AssignmentInvariant::InvalidOperatorToken(operator).into());
        }
        if operator_node.kind != SyntaxKind::EqualsToken {
            return Ok(None);
        }

        let left = self.reference(binary.left);
        let right = self.reference(binary.right);
        self.require_parent(left, Some(expression.node))?;
        self.require_parent(right, Some(expression.node))?;
        let left_node = self.node(left)?;
        let (receiver, name, index) = match &left_node.data {
            NodeData::PropertyAccessExpression(access)
                if left_node.flags.0 == 0
                    && access.flow_node.is_none()
                    && access.question_dot_token.is_none()
                    && access.facts == 0 =>
            {
                (
                    self.reference(access.expression),
                    self.reference(access.name),
                    None,
                )
            }
            NodeData::ElementAccessExpression(access)
                if left_node.flags.0 == 0
                    && access.flow_node.is_none()
                    && access.question_dot_token.is_none()
                    && access.facts == 0 =>
            {
                let index = self.reference(access.argument_expression);
                (self.reference(access.expression), index, Some(index))
            }
            _ => return Ok(None),
        };
        self.require_parent(receiver, Some(left.node))?;
        self.require_parent(name, Some(left.node))?;
        let receiver_record = self.node(receiver)?;
        let NodeData::Identifier(receiver_name) = &receiver_record.data else {
            return Ok(None);
        };
        if receiver_record.flags.0 != 0
            || receiver_name.flow_node.is_some()
            || receiver_name.text.is_empty()
        {
            return Err(AssignmentInvariant::InvalidIdentifierShape(receiver).into());
        }
        let name_record = self.node(name)?;
        let property_name = match &name_record.data {
            NodeData::Identifier(identifier)
                if index.is_none()
                    && name_record.flags.0 == 0
                    && identifier.flow_node.is_none()
                    && !identifier.text.is_empty() =>
            {
                identifier.text.as_str()
            }
            NodeData::StringLiteral(literal)
                if index.is_some()
                    && name_record.kind == SyntaxKind::StringLiteral
                    && name_record.flags.0 == 0
                    && literal.token_flags.0 == 0
                    && !literal.text.is_empty() =>
            {
                literal.text.as_str()
            }
            _ => return Ok(None),
        };

        let Some(property_symbol) = self.bound.symbol(expression) else {
            return Ok(None);
        };
        let property = self
            .store
            .symbol(property_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(property_symbol))?;
        let Some(owner_symbol) = property.parent() else {
            return Ok(None);
        };
        let owner = self
            .store
            .symbol(owner_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(owner_symbol))?;
        let Some(object) = owner.value_declaration() else {
            return Ok(None);
        };
        if self.store.source_node_kind(object) != Some(SyntaxKind::ObjectLiteralExpression) {
            return Ok(None);
        }
        if property.flags() != SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT
            || property.check_flags() != CheckFlags::NONE
            || property.name().as_bytes() != property_name.as_bytes()
            || property.declarations() != Some(&[expression])
            || property.value_declaration() != Some(expression)
            || property.members().is_some()
            || property.exports().is_some()
            || property.export_symbol().is_some()
            || self.store.get_merged_symbol(property_symbol) != Some(property_symbol)
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(property_symbol).into());
        }
        if owner.flags() != SymbolFlags::OBJECT_LITERAL
            || owner.check_flags() != CheckFlags::NONE
            || owner.name() != InternalSymbolName::Object.as_ref()
            || owner.declarations() != Some(&[object])
            || owner.members().is_some()
            || owner.parent().is_some()
            || owner.export_symbol().is_some()
            || self.store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
            || self.bound.symbol(object) != Some(owner_symbol)
            || owner
                .exports()
                .and_then(|exports| self.store.symbol_table(exports))
                .and_then(|exports| exports.get_source(property_name))
                != Some(property_symbol)
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(owner_symbol).into());
        }
        let object_record = self.node(object)?;
        let NodeData::ObjectLiteralExpression(object_data) = &object_record.data else {
            return Err(AssignmentInvariant::InvalidSymbolShape(owner_symbol).into());
        };
        if object_record.flags.0 != 0
            || object_data.symbol.is_some()
            || object_data.facts != 0
            || !object_data.properties.nodes.is_empty()
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(owner_symbol).into());
        }

        self.validate_local_identifier(receiver, &receiver_name.text)?;
        let variable_symbol = self
            .bound
            .locals(self.bound.source_file())
            .and_then(|locals| self.store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&receiver_name.text))
            .ok_or(AssignmentInvariant::MissingDeclarationSymbol(receiver))?;
        let variable = self
            .store
            .symbol(variable_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(variable_symbol))?;
        let declaration = variable
            .value_declaration()
            .ok_or(AssignmentInvariant::MissingDeclarations(variable_symbol))?;
        let declaration_record = self.node(declaration)?;
        let NodeData::VariableDeclaration(variable_data) = &declaration_record.data else {
            return Err(AssignmentInvariant::InvalidSymbolShape(variable_symbol).into());
        };
        if variable_data.initializer != Some(object.node)
            || object_record.parent != Some(declaration.node)
            || variable_data.type_.is_some()
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryVariable(declaration),
            ));
        }
        let list = declaration_record
            .parent
            .map(|node| self.reference(node))
            .ok_or(AssignmentInvariant::InvalidDeclarationList(declaration))?;
        let variable_statement = self
            .node(list)?
            .parent
            .map(|node| self.reference(node))
            .ok_or(AssignmentInvariant::InvalidVariableStatement(list))?;
        if self.node(variable_statement)?.range.end > statement_node.range.start {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::TargetNotPrior {
                    node: receiver,
                    symbol: variable_symbol,
                },
            ));
        }

        Ok(Some(ObjectExpandoAssignmentPlan {
            expression,
            left,
            right,
            receiver,
            name,
            index,
            variable_symbol,
            owner_symbol,
            property_symbol,
        }))
    }

    #[allow(clippy::too_many_lines)] // Authenticate the assignment, callable, and source variable.
    fn plan_arrow_expando(
        &self,
        statement: NodeRef,
    ) -> Result<Option<ArrowExpandoAssignmentPlan>, AssignmentPlanError> {
        self.preflight_program()?;
        let Some(facts) = self.bound.source_facts() else {
            return Ok(None);
        };
        if facts.is_declaration_file() {
            return Ok(None);
        }

        let statement_node = self.node(statement)?;
        let NodeData::ExpressionStatement(statement_data) = &statement_node.data else {
            return Ok(None);
        };
        if statement_node.flags.0 != 0 || statement_data.flow_node.is_some() {
            return Err(AssignmentInvariant::InvalidStatementShape(statement).into());
        }
        if statement_node.parent != Some(self.bound.source_file().node) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NestedTarget(statement),
            ));
        }

        let expression = self.reference(statement_data.expression);
        self.require_parent(expression, Some(statement.node))?;
        let expression_node = self.node(expression)?;
        let NodeData::BinaryExpression(binary) = &expression_node.data else {
            return Ok(None);
        };
        if expression_node.flags.0 != 0
            || binary.symbol.is_some()
            || binary.type_.is_some()
            || binary.facts != 0
            || binary.modifiers.is_some()
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryAssignment(expression),
            ));
        }

        let operator = self.reference(binary.operator_token);
        self.require_parent(operator, Some(expression.node))?;
        let operator_node = self.node(operator)?;
        if !matches!(operator_node.data, NodeData::Token(_)) || operator_node.flags.0 != 0 {
            return Err(AssignmentInvariant::InvalidOperatorToken(operator).into());
        }
        if operator_node.kind != SyntaxKind::EqualsToken {
            return Ok(None);
        }

        let left = self.reference(binary.left);
        let right = self.reference(binary.right);
        self.require_parent(left, Some(expression.node))?;
        self.require_parent(right, Some(expression.node))?;
        let left_node = self.node(left)?;
        let NodeData::PropertyAccessExpression(access) = &left_node.data else {
            return Ok(None);
        };
        if left_node.flags.0 != 0
            || access.flow_node.is_some()
            || access.question_dot_token.is_some()
            || access.facts != 0
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::Syntax {
                    node: left,
                    kind: left_node.kind,
                    role: AssignmentSyntaxRole::LeftHandSide,
                },
            ));
        }

        let receiver = self.reference(access.expression);
        let name = self.reference(access.name);
        self.require_parent(receiver, Some(left.node))?;
        self.require_parent(name, Some(left.node))?;
        let receiver_node = self.node(receiver)?;
        let NodeData::Identifier(receiver_name) = &receiver_node.data else {
            return Ok(None);
        };
        if receiver_node.flags.0 != 0
            || receiver_name.flow_node.is_some()
            || receiver_name.text.is_empty()
        {
            return Err(AssignmentInvariant::InvalidIdentifierShape(receiver).into());
        }
        let name_node = self.node(name)?;
        let NodeData::Identifier(property_name) = &name_node.data else {
            return Ok(None);
        };
        if name_node.flags.0 != 0
            || property_name.flow_node.is_some()
            || property_name.text.is_empty()
        {
            return Err(AssignmentInvariant::InvalidIdentifierShape(name).into());
        }

        let Some(property_symbol) = self.bound.symbol(expression) else {
            return Ok(None);
        };
        let property = self
            .store
            .symbol(property_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(property_symbol))?;
        let Some(owner_symbol) = property.parent() else {
            return Ok(None);
        };
        let owner = self
            .store
            .symbol(owner_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(owner_symbol))?;
        let Some(initializer) = owner.value_declaration() else {
            return Ok(None);
        };
        if !matches!(
            self.store.source_node_kind(initializer),
            Some(SyntaxKind::ArrowFunction | SyntaxKind::FunctionExpression)
        ) {
            return Ok(None);
        }

        if property.flags() != SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT
            || property.check_flags() != CheckFlags::NONE
            || property.name().as_bytes() != property_name.text.as_bytes()
            || property.members().is_some()
            || property.exports().is_some()
            || property.export_symbol().is_some()
            || self.store.get_merged_symbol(property_symbol) != Some(property_symbol)
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(property_symbol).into());
        }
        let declarations = property
            .declarations()
            .ok_or(AssignmentInvariant::MissingDeclarations(property_symbol))?;
        let [declaration] = declarations else {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonUniqueTarget {
                    node: left,
                    symbol: property_symbol,
                    declaration_count: declarations.len(),
                },
            ));
        };
        if *declaration != expression {
            return Err(AssignmentInvariant::DeclarationSymbolMismatch {
                declaration: *declaration,
                expected: property_symbol,
                actual: self
                    .bound
                    .symbol(*declaration)
                    .ok_or(AssignmentInvariant::MissingDeclarationSymbol(*declaration))?,
            }
            .into());
        }
        if property.value_declaration() != Some(expression) {
            return Err(AssignmentInvariant::ValueDeclarationMismatch {
                symbol: property_symbol,
                declaration: expression,
                value_declaration: property.value_declaration(),
            }
            .into());
        }

        if owner.flags() != SymbolFlags::FUNCTION
            || owner.check_flags() != CheckFlags::NONE
            || owner.name() != InternalSymbolName::Function.as_ref()
            || owner.declarations() != Some(&[initializer])
            || owner.members().is_some()
            || owner.parent().is_some()
            || owner.export_symbol().is_some()
            || self.store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
            || self.bound.symbol(initializer) != Some(owner_symbol)
            || !super::source_callables::source_arrow_owner_expando_exports_are_valid(
                self.store,
                owner_symbol,
                initializer,
            )
            || owner
                .exports()
                .and_then(|exports| self.store.symbol_table(exports))
                .and_then(|exports| exports.get_source(&property_name.text))
                != Some(property_symbol)
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(owner_symbol).into());
        }

        self.validate_local_identifier(receiver, &receiver_name.text)?;
        let variable_symbol = self
            .bound
            .locals(self.bound.source_file())
            .and_then(|locals| self.store.symbol_table(locals))
            .and_then(|locals| locals.get_source(&receiver_name.text))
            .ok_or(AssignmentInvariant::MissingDeclarationSymbol(receiver))?;
        let variable = self
            .store
            .symbol(variable_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(variable_symbol))?;
        let variable_declaration = variable
            .value_declaration()
            .ok_or(AssignmentInvariant::MissingDeclarations(variable_symbol))?;
        let variable_node = self.node(variable_declaration)?;
        let NodeData::VariableDeclaration(variable_data) = &variable_node.data else {
            return Err(AssignmentInvariant::InvalidSymbolShape(variable_symbol).into());
        };
        if variable_data.initializer != Some(initializer.node)
            || self.node(initializer)?.parent != Some(variable_declaration.node)
            || variable_data.type_.is_some_and(|annotation| {
                facts.is_javascript_file()
                    || !self.annotated_callable_array_expando_is_exact(
                        variable_declaration,
                        self.reference(annotation),
                        &property_name.text,
                        right,
                    )
            })
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryVariable(variable_declaration),
            ));
        }

        let list = variable_node
            .parent
            .map(|node| self.reference(node))
            .ok_or(AssignmentInvariant::InvalidDeclarationList(
                variable_declaration,
            ))?;
        let list_node = self.node(list)?;
        let NodeData::VariableDeclarationList(list_data) = &list_node.data else {
            return Err(AssignmentInvariant::InvalidDeclarationList(list).into());
        };
        let binding_matches = if facts.is_javascript_file() {
            variable.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE && list_node.flags.0 == 0
                || variable.flags() == SymbolFlags::BLOCK_SCOPED_VARIABLE
                    && matches!(list_node.flags.0, NODE_FLAG_LET | NODE_FLAG_CONST)
        } else {
            variable.flags() == SymbolFlags::BLOCK_SCOPED_VARIABLE
                && list_node.flags.0 == NODE_FLAG_CONST
        };
        if !binding_matches
            || list_data.declarations.nodes.as_slice() != [variable_declaration.node]
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryVariable(variable_declaration),
            ));
        }
        let variable_statement = list_node
            .parent
            .map(|node| self.reference(node))
            .ok_or(AssignmentInvariant::InvalidVariableStatement(list))?;
        if self.node(variable_statement)?.range.end > statement_node.range.start {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::TargetNotPrior {
                    node: receiver,
                    symbol: variable_symbol,
                },
            ));
        }

        Ok(Some(ArrowExpandoAssignmentPlan {
            expression,
            left,
            right,
            receiver,
            variable_symbol,
            owner_symbol,
            property_symbol,
        }))
    }

    /// Authenticates the declared callable-array property behind a typed expando.
    fn annotated_callable_array_expando_is_exact(
        &self,
        variable: NodeRef,
        annotation: NodeRef,
        property_name: &str,
        right: NodeRef,
    ) -> bool {
        let Some(annotation_record) = self.arena.get(annotation.node) else {
            return false;
        };
        let NodeData::TypeLiteralNode(literal) = &annotation_record.data else {
            return false;
        };
        let Some(owner_symbol) = self.bound.symbol(annotation) else {
            return false;
        };
        let Some(owner) = self.store.symbol(owner_symbol) else {
            return false;
        };
        let Some(property_symbol) = owner
            .members()
            .and_then(|members| self.store.symbol_table(members))
            .and_then(|members| members.get_source(property_name))
        else {
            return false;
        };
        let Some(property) = self.store.symbol(property_symbol) else {
            return false;
        };
        let Some([property_declaration]) = property.declarations() else {
            return false;
        };
        let property_declaration = *property_declaration;
        let Some(property_record) = self.arena.get(property_declaration.node) else {
            return false;
        };
        let NodeData::PropertyDeclaration(property_data) = &property_record.data else {
            return false;
        };
        let Some(array_type) = property_data.type_.map(|node| self.reference(node)) else {
            return false;
        };
        let Some(array_record) = self.arena.get(array_type.node) else {
            return false;
        };
        let NodeData::ArrayTypeNode(array) = &array_record.data else {
            return false;
        };
        let element = self.reference(array.element_type);
        let Some(element_record) = self.arena.get(element.node) else {
            return false;
        };
        let Some(right_record) = self.arena.get(right.node) else {
            return false;
        };
        let NodeData::ArrayLiteralExpression(value) = &right_record.data else {
            return false;
        };
        let mut signatures = literal.members.nodes.iter().filter_map(|member| {
            let member = self.reference(*member);
            let record = self.arena.get(member.node)?;
            (record.kind == SyntaxKind::CallSignature).then_some((member, record))
        });
        let Some((signature, signature_record)) = signatures.next() else {
            return false;
        };
        let NodeData::CallSignatureDeclaration(call) = &signature_record.data else {
            return false;
        };
        let Some(return_type) = call.type_.map(|node| self.reference(node)) else {
            return false;
        };
        let Some(return_record) = self.arena.get(return_type.node) else {
            return false;
        };
        let property_flags = property.flags();

        annotation_record.kind == SyntaxKind::TypeLiteral
            && annotation_record.parent == Some(variable.node)
            && annotation_record.flags.0 == 0
            && literal.symbol.is_none()
            && literal.members.nodes.len() == 2
            && !literal.members.has_trailing_comma
            && owner.flags() == SymbolFlags::TYPE_LITERAL
            && owner.check_flags() == CheckFlags::NONE
            && owner.declarations() == Some(&[annotation])
            && owner.value_declaration().is_none()
            && owner.exports().is_none()
            && owner.parent().is_none()
            && owner.export_symbol().is_none()
            && self.store.get_merged_symbol(owner_symbol) == Some(owner_symbol)
            && (property_flags == SymbolFlags::PROPERTY
                || property_flags == (SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL))
            && property.check_flags() == CheckFlags::NONE
            && property.name().as_utf8() == Some(property_name)
            && property.value_declaration() == Some(property_declaration)
            && property.members().is_none()
            && property.exports().is_none()
            && property.parent() == Some(owner_symbol)
            && property.export_symbol().is_none()
            && self.store.get_merged_symbol(property_symbol) == Some(property_symbol)
            && property_record.kind == SyntaxKind::PropertyDeclaration
            && property_record.parent == Some(annotation.node)
            && property_record.flags.0 == 0
            && property_data.initializer.is_none()
            && property_data.symbol.is_none()
            && property_data.modifiers.is_none()
            && property_data.facts == 0
            && array_record.kind == SyntaxKind::ArrayType
            && array_record.parent == Some(property_declaration.node)
            && array_record.flags.0 == 0
            && element_record.kind == SyntaxKind::StringKeyword
            && element_record.parent == Some(array_type.node)
            && element_record.flags.0 == 0
            && signature_record.parent == Some(annotation.node)
            && signature_record.flags.0 == 0
            && call.full_signature.is_none()
            && call.next_container.is_none()
            && call.symbol.is_none()
            && call.type_parameters.is_none()
            && call.parameters.nodes.is_empty()
            && !call.parameters.has_trailing_comma
            && return_record.kind == SyntaxKind::VoidKeyword
            && return_record.parent == Some(signature.node)
            && return_record.flags.0 == 0
            && signatures.next().is_none()
            && right_record.kind == SyntaxKind::ArrayLiteralExpression
            && right_record.flags.0 == 0
            && value.elements.nodes.is_empty()
            && !value.elements.has_trailing_comma
            && value.facts == 0
    }

    fn plan_named(
        &self,
        statement: NodeRef,
    ) -> Result<Option<CommonJsAssignmentPlan>, AssignmentPlanError> {
        self.preflight_program()?;
        if self
            .bound
            .source_facts()
            .is_none_or(|facts| !facts.is_javascript_file() || !facts.is_common_js_module())
        {
            return Ok(None);
        }

        let Some(assignment) = self.named_assignment_shape(statement)? else {
            return Ok(None);
        };
        let name = match &self.node(assignment.name)?.data {
            NodeData::Identifier(name) => name.text.as_str(),
            NodeData::StringLiteral(name) => name.text.as_str(),
            _ => {
                return Err(AssignmentInvariant::InvalidIdentifierShape(assignment.name).into());
            }
        };
        let source = self.bound.source_file();
        let source_symbol = self
            .bound
            .symbol(source)
            .ok_or(AssignmentInvariant::MissingSourceSymbol(source))?;
        let source_record = self
            .store
            .symbol(source_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(source_symbol))?;
        if source_record.flags() != SymbolFlags::VALUE_MODULE {
            return Err(AssignmentInvariant::InvalidSymbolShape(source_symbol).into());
        }
        let merged_source = self
            .store
            .get_merged_symbol(source_symbol)
            .ok_or(AssignmentInvariant::InvalidMergedSymbol(source_symbol))?;
        if merged_source != source_symbol {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::MergedTarget {
                    node: source,
                    source: source_symbol,
                    target: merged_source,
                },
            ));
        }

        let expected = source_record
            .exports()
            .and_then(|exports| self.store.symbol_table(exports))
            .and_then(|exports| exports.get_source(name))
            .ok_or(AssignmentInvariant::MissingExportSymbol(source_symbol))?;
        let target_symbol = self.bound.symbol(assignment.expression).ok_or(
            AssignmentInvariant::MissingDeclarationSymbol(assignment.expression),
        )?;
        if target_symbol != expected {
            return Err(AssignmentInvariant::DeclarationSymbolMismatch {
                declaration: assignment.expression,
                expected,
                actual: target_symbol,
            }
            .into());
        }

        self.validate_named_export_assignment(&assignment, name, source_symbol)?;

        Ok(Some(CommonJsAssignmentPlan {
            expression: assignment.expression,
            left: assignment.left,
            right: assignment.right,
            target_symbol,
        }))
    }

    fn named_assignment_shape(
        &self,
        statement: NodeRef,
    ) -> Result<Option<CommonJsNamedAssignmentShape>, AssignmentPlanError> {
        let statement_node = self.node(statement)?;
        let NodeData::ExpressionStatement(statement_data) = &statement_node.data else {
            return Ok(None);
        };
        if statement_node.flags.0 != 0 || statement_data.flow_node.is_some() {
            return Err(AssignmentInvariant::InvalidStatementShape(statement).into());
        }
        if statement_node.parent != Some(self.bound.source_file().node) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NestedTarget(statement),
            ));
        }

        let expression = self.reference(statement_data.expression);
        self.require_parent(expression, Some(statement.node))?;
        let expression_node = self.node(expression)?;
        let NodeData::BinaryExpression(binary) = &expression_node.data else {
            return Ok(None);
        };
        if expression_node.flags.0 != 0
            || binary.symbol.is_some()
            || binary.type_.is_some()
            || binary.facts != 0
            || binary.modifiers.is_some()
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryAssignment(expression),
            ));
        }

        let operator = self.reference(binary.operator_token);
        self.require_parent(operator, Some(expression.node))?;
        let operator_node = self.node(operator)?;
        if !matches!(operator_node.data, NodeData::Token(_)) || operator_node.flags.0 != 0 {
            return Err(AssignmentInvariant::InvalidOperatorToken(operator).into());
        }
        if operator_node.kind != SyntaxKind::EqualsToken {
            return Ok(None);
        }

        let left = self.reference(binary.left);
        let right = self.reference(binary.right);
        self.require_parent(left, Some(expression.node))?;
        self.require_parent(right, Some(expression.node))?;
        let left_node = self.node(left)?;
        let (receiver, name) = match &left_node.data {
            NodeData::PropertyAccessExpression(access) => {
                if left_node.flags.0 != 0
                    || access.flow_node.is_some()
                    || access.question_dot_token.is_some()
                    || access.facts != 0
                {
                    return Err(AssignmentPlanError::Unsupported(
                        AssignmentUnsupported::Syntax {
                            node: left,
                            kind: left_node.kind,
                            role: AssignmentSyntaxRole::LeftHandSide,
                        },
                    ));
                }
                (
                    self.reference(access.expression),
                    self.reference(access.name),
                )
            }
            NodeData::ElementAccessExpression(access) => {
                if left_node.flags.0 != 0
                    || access.flow_node.is_some()
                    || access.question_dot_token.is_some()
                    || access.facts != 0
                {
                    return Err(AssignmentPlanError::Unsupported(
                        AssignmentUnsupported::Syntax {
                            node: left,
                            kind: left_node.kind,
                            role: AssignmentSyntaxRole::LeftHandSide,
                        },
                    ));
                }
                (
                    self.reference(access.expression),
                    self.reference(access.argument_expression),
                )
            }
            _ => return Ok(None),
        };
        self.require_parent(receiver, Some(left.node))?;
        self.require_parent(name, Some(left.node))?;
        let module_receiver = if self.is_identifier_named(receiver, "exports")? {
            None
        } else {
            let receiver_node = self.node(receiver)?;
            let NodeData::PropertyAccessExpression(module_exports) = &receiver_node.data else {
                return Ok(None);
            };
            if receiver_node.flags.0 != 0
                || module_exports.flow_node.is_some()
                || module_exports.question_dot_token.is_some()
                || module_exports.facts != 0
            {
                return Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::Syntax {
                        node: receiver,
                        kind: receiver_node.kind,
                        role: AssignmentSyntaxRole::LeftHandSide,
                    },
                ));
            }
            let module = self.reference(module_exports.expression);
            let exports = self.reference(module_exports.name);
            self.require_parent(module, Some(receiver.node))?;
            self.require_parent(exports, Some(receiver.node))?;
            if !self.is_identifier_named(module, "module")?
                || !self.is_identifier_named(exports, "exports")?
            {
                return Ok(None);
            }
            Some(module)
        };
        let name_node = self.node(name)?;
        match &name_node.data {
            NodeData::Identifier(identifier) => {
                if name_node.flags.0 != 0
                    || identifier.flow_node.is_some()
                    || identifier.text.is_empty()
                {
                    return Err(AssignmentInvariant::InvalidIdentifierShape(name).into());
                }
            }
            NodeData::StringLiteral(literal)
                if name_node.kind == SyntaxKind::StringLiteral
                    && name_node.flags.0 == 0
                    && literal.token_flags.0 == 0
                    && !literal.text.is_empty() => {}
            NodeData::StringLiteral(_) => {
                return Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::Syntax {
                        node: name,
                        kind: name_node.kind,
                        role: AssignmentSyntaxRole::TargetName,
                    },
                ));
            }
            _ => return Ok(None),
        }
        let Some(alias) = self.named_assignment_value_is_alias(right)? else {
            return Ok(None);
        };

        Ok(Some(CommonJsNamedAssignmentShape {
            expression,
            left,
            right,
            receiver,
            module_receiver,
            name,
            alias,
        }))
    }

    fn named_assignment_value_is_alias(
        &self,
        value: NodeRef,
    ) -> Result<Option<bool>, AssignmentPlanError> {
        let record = self.node(value)?;
        if record.flags.0 != 0 {
            return Ok(None);
        }
        match &record.data {
            NodeData::Identifier(identifier) => {
                if identifier.flow_node.is_some() || identifier.text.is_empty() {
                    return Err(AssignmentInvariant::InvalidIdentifierShape(value).into());
                }
                Ok(Some(true))
            }
            NodeData::NumericLiteral(literal) if literal.token_flags.0 == 0 => Ok(Some(false)),
            NodeData::StringLiteral(literal) if literal.token_flags.0 == 0 => Ok(Some(false)),
            NodeData::KeywordExpression(keyword)
                if keyword.flow_node.is_none()
                    && matches!(
                        record.kind,
                        SyntaxKind::TrueKeyword
                            | SyntaxKind::FalseKeyword
                            | SyntaxKind::NullKeyword
                    ) =>
            {
                Ok(Some(false))
            }
            NodeData::ObjectLiteralExpression(object)
                if object.symbol.is_none() && object.facts == 0 =>
            {
                Ok(Some(false))
            }
            NodeData::ArrayLiteralExpression(array) if array.facts == 0 => Ok(Some(false)),
            NodeData::FunctionExpression(function)
                if record.kind == SyntaxKind::FunctionExpression
                    && function.name.is_none()
                    && function.parameters.nodes.is_empty()
                    && !function.parameters.has_trailing_comma =>
            {
                Ok(Some(false))
            }
            _ => Ok(None),
        }
    }

    fn validate_named_export_assignment(
        &self,
        assignment: &CommonJsNamedAssignmentShape,
        name: &str,
        source_symbol: SemanticSymbolId,
    ) -> Result<(), AssignmentPlanError> {
        let target = self.bound.symbol(assignment.expression).ok_or(
            AssignmentInvariant::MissingDeclarationSymbol(assignment.expression),
        )?;
        let merged = self
            .store
            .get_merged_symbol(target)
            .ok_or(AssignmentInvariant::InvalidMergedSymbol(target))?;
        if merged != target {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::MergedTarget {
                    node: assignment.left,
                    source: target,
                    target: merged,
                },
            ));
        }

        let record = self
            .store
            .symbol(target)
            .ok_or(AssignmentInvariant::InvalidSymbol(target))?;
        let expected_flags = if assignment.alias {
            SymbolFlags::ALIAS
        } else {
            SymbolFlags::FUNCTION_SCOPED_VARIABLE
        };
        if record.flags() == (SymbolFlags::ALIAS | SymbolFlags::FUNCTION_SCOPED_VARIABLE) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonVariableTarget {
                    node: assignment.left,
                    symbol: target,
                    flags: record.flags(),
                },
            ));
        }
        if record.flags() != expected_flags
            || record.check_flags() != CheckFlags::NONE
            || record.name().as_bytes() != name.as_bytes()
            || record.members().is_some()
            || record.exports().is_some()
            || record.export_symbol().is_some()
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(target).into());
        }
        if record.parent() != Some(source_symbol) {
            return Err(AssignmentInvariant::InvalidTargetParent {
                symbol: target,
                expected: Some(source_symbol),
                actual: record.parent(),
            }
            .into());
        }

        let declarations = record
            .declarations()
            .filter(|declarations| !declarations.is_empty())
            .ok_or(AssignmentInvariant::MissingDeclarations(target))?;
        let expected_value = (!assignment.alias).then_some(declarations[0]);
        if record.value_declaration() != expected_value {
            return Err(AssignmentInvariant::ValueDeclarationMismatch {
                symbol: target,
                declaration: declarations[0],
                value_declaration: record.value_declaration(),
            }
            .into());
        }

        let mut occurrences = 0;
        for &declaration in declarations {
            if declaration.file != assignment.expression.file
                || declaration.arena != assignment.expression.arena
            {
                return Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::CrossFileTarget {
                        node: assignment.left,
                        declaration,
                    },
                ));
            }
            if self.bound.symbol(declaration) != Some(target) {
                return Err(AssignmentInvariant::DeclarationSymbolMismatch {
                    declaration,
                    expected: target,
                    actual: self
                        .bound
                        .symbol(declaration)
                        .ok_or(AssignmentInvariant::MissingDeclarationSymbol(declaration))?,
                }
                .into());
            }
            let statement = self
                .node(declaration)?
                .parent
                .map(|node| self.reference(node))
                .ok_or(AssignmentInvariant::InvalidStatementShape(declaration))?;
            let Some(candidate) = self.named_assignment_shape(statement)? else {
                return Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::NonUniqueTarget {
                        node: assignment.left,
                        symbol: target,
                        declaration_count: declarations.len(),
                    },
                ));
            };
            let candidate_name = self.node(candidate.name)?;
            let matching_name = match &candidate_name.data {
                NodeData::Identifier(identifier) => identifier.text == name,
                NodeData::StringLiteral(literal) => literal.text == name,
                _ => false,
            };
            if candidate.expression != declaration
                || !matching_name
                || candidate.alias != assignment.alias
            {
                return Err(AssignmentInvariant::InvalidSymbolShape(target).into());
            }
            if let Some(module) = candidate.module_receiver {
                self.validate_implicit_module(module, source_symbol)?;
                self.validate_module_exports_receiver(candidate.receiver, module)?;
            } else {
                self.validate_implicit_exports(candidate.receiver, source_symbol)?;
            }
            if candidate.alias {
                let NodeData::Identifier(local) = &self.node(candidate.right)?.data else {
                    return Err(AssignmentInvariant::InvalidIdentifierShape(candidate.right).into());
                };
                self.validate_local_identifier(candidate.right, &local.text)?;
            }
            occurrences += usize::from(declaration == assignment.expression);
        }
        if occurrences != 1 {
            return Err(AssignmentInvariant::InvalidSymbolShape(target).into());
        }

        Ok(())
    }

    fn validate_module_exports_receiver(
        &self,
        receiver: NodeRef,
        module: NodeRef,
    ) -> Result<(), AssignmentPlanError> {
        let implicit_module = self
            .bound
            .locals(self.bound.source_file())
            .and_then(|locals| self.store.symbol_table(locals))
            .and_then(|locals| locals.get_source("module"))
            .ok_or(AssignmentInvariant::MissingSourceSymbol(
                self.bound.source_file(),
            ))?;
        let exports = self
            .store
            .symbol(implicit_module)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| self.store.symbol_table(members))
            .and_then(|members| members.get_source("exports"))
            .ok_or(AssignmentInvariant::MissingExportSymbol(implicit_module))?;
        if let Some(cached) = self
            .store
            .symbol_node_links(receiver)
            .and_then(|links| links.resolved_symbol)
            && cached != exports
        {
            return Err(AssignmentInvariant::ResolvedSymbolMismatch {
                node: receiver,
                expected: exports,
                actual: cached,
            }
            .into());
        }
        if let Some(cached) = self
            .store
            .symbol_node_links(module)
            .and_then(|links| links.resolved_symbol)
            && cached != implicit_module
        {
            return Err(AssignmentInvariant::ResolvedSymbolMismatch {
                node: module,
                expected: implicit_module,
                actual: cached,
            }
            .into());
        }
        Ok(())
    }

    fn validate_implicit_exports(
        &self,
        receiver: NodeRef,
        source_symbol: SemanticSymbolId,
    ) -> Result<(), AssignmentPlanError> {
        let source = self.bound.source_file();
        let exports = self
            .bound
            .locals(source)
            .and_then(|locals| self.store.symbol_table(locals))
            .and_then(|locals| locals.get_source("exports"))
            .ok_or(AssignmentInvariant::MissingExportSymbol(source_symbol))?;
        let record = self
            .store
            .symbol(exports)
            .ok_or(AssignmentInvariant::InvalidSymbol(exports))?;
        if !record.flags().contains(SymbolFlags::MODULE_EXPORTS) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::ShadowedCommonJsModule {
                    node: receiver,
                    symbol: exports,
                },
            ));
        }
        let merged = self
            .store
            .get_merged_symbol(exports)
            .ok_or(AssignmentInvariant::InvalidMergedSymbol(exports))?;
        if merged != exports {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::MergedTarget {
                    node: receiver,
                    source: exports,
                    target: merged,
                },
            ));
        }
        if record.flags() != (SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::MODULE_EXPORTS)
            || record.check_flags() != CheckFlags::NONE
            || record.name().as_bytes() != b"exports"
            || record.declarations() != Some(&[source])
            || record.value_declaration() != Some(source)
            || record.members().is_some()
            || record.exports().is_some()
            || record.parent().is_some()
            || record.export_symbol().is_some()
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(exports).into());
        }
        if let Some(cached) = self
            .store
            .symbol_node_links(receiver)
            .and_then(|links| links.resolved_symbol)
            && cached != exports
        {
            return Err(AssignmentInvariant::ResolvedSymbolMismatch {
                node: receiver,
                expected: exports,
                actual: cached,
            }
            .into());
        }

        Ok(())
    }

    fn plan(
        &self,
        statement: NodeRef,
    ) -> Result<Option<CommonJsAssignmentPlan>, AssignmentPlanError> {
        self.preflight_program()?;
        if self
            .bound
            .source_facts()
            .is_none_or(|facts| !facts.is_javascript_file() || !facts.is_common_js_module())
        {
            return Ok(None);
        }

        let statement_node = self.node(statement)?;
        let NodeData::ExpressionStatement(statement_data) = &statement_node.data else {
            return Ok(None);
        };
        if statement_node.flags.0 != 0 || statement_data.flow_node.is_some() {
            return Err(AssignmentInvariant::InvalidStatementShape(statement).into());
        }
        if statement_node.parent != Some(self.bound.source_file().node) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NestedTarget(statement),
            ));
        }

        let expression = self.reference(statement_data.expression);
        self.require_parent(expression, Some(statement.node))?;
        let expression_node = self.node(expression)?;
        let NodeData::BinaryExpression(binary) = &expression_node.data else {
            return Ok(None);
        };
        if expression_node.flags.0 != 0
            || binary.symbol.is_some()
            || binary.type_.is_some()
            || binary.facts != 0
            || binary.modifiers.is_some()
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryAssignment(expression),
            ));
        }

        let operator = self.reference(binary.operator_token);
        self.require_parent(operator, Some(expression.node))?;
        let operator_node = self.node(operator)?;
        if !matches!(operator_node.data, NodeData::Token(_)) || operator_node.flags.0 != 0 {
            return Err(AssignmentInvariant::InvalidOperatorToken(operator).into());
        }
        if operator_node.kind != SyntaxKind::EqualsToken {
            return Ok(None);
        }

        let left = self.reference(binary.left);
        let right = self.reference(binary.right);
        self.require_parent(left, Some(expression.node))?;
        self.require_parent(right, Some(expression.node))?;
        let left_node = self.node(left)?;
        let NodeData::PropertyAccessExpression(access) = &left_node.data else {
            return Ok(None);
        };
        if left_node.flags.0 != 0
            || access.flow_node.is_some()
            || access.question_dot_token.is_some()
            || access.facts != 0
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::Syntax {
                    node: left,
                    kind: left_node.kind,
                    role: AssignmentSyntaxRole::LeftHandSide,
                },
            ));
        }

        let receiver = self.reference(access.expression);
        let property = self.reference(access.name);
        self.require_parent(receiver, Some(left.node))?;
        self.require_parent(property, Some(left.node))?;
        if !self.is_identifier_named(receiver, "module")?
            || !self.is_identifier_named(property, "exports")?
        {
            return Ok(None);
        }

        let right_node = self.node(right)?;
        let local_name = match &right_node.data {
            NodeData::Identifier(local_name) => {
                if right_node.flags.0 != 0 || local_name.flow_node.is_some() {
                    return Err(AssignmentInvariant::InvalidIdentifierShape(right).into());
                }
                Some(local_name.text.as_str())
            }
            NodeData::ObjectLiteralExpression(object)
                if right_node.kind == SyntaxKind::ObjectLiteralExpression
                    && right_node.flags.0 == 0
                    && object.symbol.is_none()
                    && object.facts == 0 =>
            {
                None
            }
            NodeData::FunctionExpression(function)
                if right_node.kind == SyntaxKind::FunctionExpression
                    && right_node.flags.0 == 0
                    && function.name.is_none()
                    && function.parameters.nodes.is_empty()
                    && !function.parameters.has_trailing_comma =>
            {
                None
            }
            _ => return Ok(None),
        };

        let source = self.bound.source_file();
        let source_symbol = self
            .bound
            .symbol(source)
            .ok_or(AssignmentInvariant::MissingSourceSymbol(source))?;
        let source_record = self
            .store
            .symbol(source_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(source_symbol))?;
        if source_record.flags() != SymbolFlags::VALUE_MODULE {
            return Err(AssignmentInvariant::InvalidSymbolShape(source_symbol).into());
        }
        let merged_source = self
            .store
            .get_merged_symbol(source_symbol)
            .ok_or(AssignmentInvariant::InvalidMergedSymbol(source_symbol))?;
        if merged_source != source_symbol {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::MergedTarget {
                    node: source,
                    source: source_symbol,
                    target: merged_source,
                },
            ));
        }
        let exports = source_record
            .exports()
            .and_then(|exports| self.store.symbol_table(exports))
            .ok_or(AssignmentInvariant::InvalidSymbolShape(source_symbol))?;
        let expected = exports
            .get(InternalSymbolName::ExportEquals.as_ref())
            .ok_or(AssignmentInvariant::MissingExportSymbol(source_symbol))?;
        let target_symbol = self
            .bound
            .symbol(expression)
            .ok_or(AssignmentInvariant::MissingDeclarationSymbol(expression))?;
        if target_symbol != expected {
            return Err(AssignmentInvariant::DeclarationSymbolMismatch {
                declaration: expression,
                expected,
                actual: target_symbol,
            }
            .into());
        }

        self.validate_export_assignment(
            expression,
            left,
            source_symbol,
            target_symbol,
            local_name.is_some(),
        )?;
        self.validate_implicit_module(receiver, source_symbol)?;
        if let Some(local_name) = local_name {
            self.validate_local_identifier(right, local_name)?;
        }

        Ok(Some(CommonJsAssignmentPlan {
            expression,
            left,
            right,
            target_symbol,
        }))
    }

    fn validate_export_assignment(
        &self,
        expression: NodeRef,
        left: NodeRef,
        source_symbol: SemanticSymbolId,
        target_symbol: SemanticSymbolId,
        alias: bool,
    ) -> Result<(), AssignmentPlanError> {
        let merged = self
            .store
            .get_merged_symbol(target_symbol)
            .ok_or(AssignmentInvariant::InvalidMergedSymbol(target_symbol))?;
        if merged != target_symbol {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::MergedTarget {
                    node: left,
                    source: target_symbol,
                    target: merged,
                },
            ));
        }

        let record = self
            .store
            .symbol(target_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(target_symbol))?;
        let declarations = record
            .declarations()
            .ok_or(AssignmentInvariant::MissingDeclarations(target_symbol))?;
        let [declaration] = declarations else {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonUniqueTarget {
                    node: left,
                    symbol: target_symbol,
                    declaration_count: declarations.len(),
                },
            ));
        };
        if *declaration != expression {
            return Err(AssignmentInvariant::InvalidSymbolShape(target_symbol).into());
        }

        let promoted_type_exports = record.flags().contains(SymbolFlags::NAMESPACE_MODULE);
        let assignment_flags = if alias {
            SymbolFlags::ALIAS
        } else {
            SymbolFlags::PROPERTY
        };
        let expected_flags = if promoted_type_exports {
            assignment_flags | SymbolFlags::NAMESPACE_MODULE
        } else {
            assignment_flags
        };
        if record.flags() != expected_flags
            || record.check_flags() != CheckFlags::NONE
            || record.name() != InternalSymbolName::ExportEquals.as_ref()
            || record.members().is_some()
            || record.export_symbol().is_some()
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(target_symbol).into());
        }
        match (promoted_type_exports, record.exports()) {
            (false, None) => {}
            (true, Some(promoted)) => {
                let promoted = self
                    .store
                    .symbol_table(promoted)
                    .ok_or(AssignmentInvariant::InvalidSymbolShape(target_symbol))?;
                let source_exports = self
                    .store
                    .symbol(source_symbol)
                    .and_then(ts_binder::semantic::Symbol::exports)
                    .and_then(|exports| self.store.symbol_table(exports))
                    .ok_or(AssignmentInvariant::InvalidSymbolShape(source_symbol))?;
                if promoted.is_empty()
                    || promoted.iter().any(|(name, symbol)| {
                        name == InternalSymbolName::ExportEquals.as_ref()
                            || source_exports.get(name) != Some(symbol)
                            || self.store.symbol(symbol).is_none_or(|record| {
                                !record
                                    .flags()
                                    .intersects(SymbolFlags::TYPE | SymbolFlags::NAMESPACE)
                            })
                    })
                {
                    return Err(AssignmentInvariant::InvalidSymbolShape(target_symbol).into());
                }
            }
            _ => return Err(AssignmentInvariant::InvalidSymbolShape(target_symbol).into()),
        }
        if record.value_declaration() != Some(expression) {
            return Err(AssignmentInvariant::ValueDeclarationMismatch {
                symbol: target_symbol,
                declaration: expression,
                value_declaration: record.value_declaration(),
            }
            .into());
        }
        if record.parent() != Some(source_symbol) {
            return Err(AssignmentInvariant::InvalidTargetParent {
                symbol: target_symbol,
                expected: Some(source_symbol),
                actual: record.parent(),
            }
            .into());
        }
        Ok(())
    }

    fn validate_implicit_module(
        &self,
        receiver: NodeRef,
        source_symbol: SemanticSymbolId,
    ) -> Result<(), AssignmentPlanError> {
        let source = self.bound.source_file();
        let locals = self
            .bound
            .locals(source)
            .and_then(|locals| self.store.symbol_table(locals))
            .ok_or(AssignmentInvariant::InvalidSymbolShape(source_symbol))?;
        let module = locals
            .get_source("module")
            .ok_or(AssignmentInvariant::MissingExportSymbol(source_symbol))?;
        let record = self
            .store
            .symbol(module)
            .ok_or(AssignmentInvariant::InvalidSymbol(module))?;
        if !record.flags().contains(SymbolFlags::MODULE_EXPORTS) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::ShadowedCommonJsModule {
                    node: receiver,
                    symbol: module,
                },
            ));
        }
        let merged = self
            .store
            .get_merged_symbol(module)
            .ok_or(AssignmentInvariant::InvalidMergedSymbol(module))?;
        if merged != module {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::MergedTarget {
                    node: receiver,
                    source: module,
                    target: merged,
                },
            ));
        }
        if record.flags() != (SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::MODULE_EXPORTS)
            || record.check_flags() != CheckFlags::NONE
            || record.name().as_bytes() != b"module"
            || record.declarations() != Some(&[source])
            || record.value_declaration() != Some(source)
            || record.exports().is_some()
            || record.parent().is_some()
            || record.export_symbol().is_some()
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(module).into());
        }

        let exports = record
            .members()
            .and_then(|members| self.store.symbol_table(members))
            .and_then(|members| members.get_source("exports"))
            .ok_or(AssignmentInvariant::MissingExportSymbol(module))?;
        let exports_record = self
            .store
            .symbol(exports)
            .ok_or(AssignmentInvariant::InvalidSymbol(exports))?;
        let merged_exports = self
            .store
            .get_merged_symbol(exports)
            .ok_or(AssignmentInvariant::InvalidMergedSymbol(exports))?;
        if merged_exports != exports {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::MergedTarget {
                    node: receiver,
                    source: exports,
                    target: merged_exports,
                },
            ));
        }
        if exports_record.flags() != (SymbolFlags::PROPERTY | SymbolFlags::MODULE_EXPORTS)
            || exports_record.check_flags() != CheckFlags::NONE
            || exports_record.name().as_bytes() != b"exports"
            || exports_record.declarations() != Some(&[source])
            || exports_record.value_declaration() != Some(source)
            || exports_record.members().is_some()
            || exports_record.exports().is_some()
            || exports_record.export_symbol().is_some()
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(exports).into());
        }
        if exports_record.parent() != Some(module) {
            return Err(AssignmentInvariant::InvalidTargetParent {
                symbol: exports,
                expected: Some(module),
                actual: exports_record.parent(),
            }
            .into());
        }
        if let Some(cached) = self
            .store
            .symbol_node_links(receiver)
            .and_then(|links| links.resolved_symbol)
            && cached != module
        {
            return Err(AssignmentInvariant::ResolvedSymbolMismatch {
                node: receiver,
                expected: module,
                actual: cached,
            }
            .into());
        }
        Ok(())
    }

    fn validate_local_identifier(
        &self,
        reference: NodeRef,
        name: &str,
    ) -> Result<(), AssignmentPlanError> {
        let locals = self
            .bound
            .locals(self.bound.source_file())
            .and_then(|locals| self.store.symbol_table(locals))
            .ok_or(AssignmentInvariant::MissingSourceSymbol(
                self.bound.source_file(),
            ))?;
        let target = locals
            .get_source(name)
            .ok_or(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::UnresolvedIdentifier(reference),
            ))?;
        let merged = self
            .store
            .get_merged_symbol(target)
            .ok_or(AssignmentInvariant::InvalidMergedSymbol(target))?;
        if merged != target {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::MergedTarget {
                    node: reference,
                    source: target,
                    target: merged,
                },
            ));
        }
        let record = self
            .store
            .symbol(target)
            .ok_or(AssignmentInvariant::InvalidSymbol(target))?;
        if record.flags().intersects(SymbolFlags::ALIAS) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::AliasTarget {
                    node: reference,
                    symbol: target,
                },
            ));
        }
        if record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            && record.flags() != SymbolFlags::BLOCK_SCOPED_VARIABLE
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonVariableTarget {
                    node: reference,
                    symbol: target,
                    flags: record.flags(),
                },
            ));
        }
        if record.check_flags() != CheckFlags::NONE
            || record.members().is_some()
            || record.exports().is_some()
            || record.export_symbol().is_some()
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(target).into());
        }
        let declarations = record
            .declarations()
            .ok_or(AssignmentInvariant::MissingDeclarations(target))?;
        let [declaration] = declarations else {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonUniqueTarget {
                    node: reference,
                    symbol: target,
                    declaration_count: declarations.len(),
                },
            ));
        };
        if declaration.file != reference.file || declaration.arena != reference.arena {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::CrossFileTarget {
                    node: reference,
                    declaration: *declaration,
                },
            ));
        }
        if record.name().as_bytes() != name.as_bytes() {
            return Err(AssignmentInvariant::IdentifierNameMismatch {
                reference,
                declaration: *declaration,
            }
            .into());
        }
        if record.value_declaration() != Some(*declaration) {
            return Err(AssignmentInvariant::ValueDeclarationMismatch {
                symbol: target,
                declaration: *declaration,
                value_declaration: record.value_declaration(),
            }
            .into());
        }
        let actual = self
            .bound
            .symbol(*declaration)
            .ok_or(AssignmentInvariant::MissingDeclarationSymbol(*declaration))?;
        if actual != target {
            return Err(AssignmentInvariant::DeclarationSymbolMismatch {
                declaration: *declaration,
                expected: target,
                actual,
            }
            .into());
        }
        let local = self.bound.local_symbol(*declaration);
        if local.is_some() {
            return Err(AssignmentInvariant::LocalExportSymbolMismatch {
                declaration: *declaration,
                expected: None,
                actual: local,
            }
            .into());
        }
        if record.parent().is_some() {
            return Err(AssignmentInvariant::InvalidTargetParent {
                symbol: target,
                expected: None,
                actual: record.parent(),
            }
            .into());
        }
        if let Some(cached) = self
            .store
            .symbol_node_links(reference)
            .and_then(|links| links.resolved_symbol)
            && cached != target
        {
            return Err(AssignmentInvariant::ResolvedSymbolMismatch {
                node: reference,
                expected: target,
                actual: cached,
            }
            .into());
        }
        self.validate_local_declaration(reference, *declaration, name, record.flags())?;
        Ok(())
    }

    fn validate_local_declaration(
        &self,
        reference: NodeRef,
        declaration: NodeRef,
        expected_name: &str,
        flags: SymbolFlags,
    ) -> Result<(), AssignmentPlanError> {
        let declaration_node = self.node(declaration)?;
        let NodeData::VariableDeclaration(variable) = &declaration_node.data else {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::Syntax {
                    node: declaration,
                    kind: declaration_node.kind,
                    role: AssignmentSyntaxRole::TargetDeclaration,
                },
            ));
        };
        if declaration_node.flags.0 != 0
            || variable.exclamation_token.is_some()
            || variable.local_symbol.is_some()
            || variable.symbol.is_some()
            || variable.facts != 0
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryVariable(declaration),
            ));
        }

        let name = self.reference(variable.name);
        self.require_parent(name, Some(declaration.node))?;
        let name_node = self.node(name)?;
        let NodeData::Identifier(identifier) = &name_node.data else {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::Syntax {
                    node: name,
                    kind: name_node.kind,
                    role: AssignmentSyntaxRole::TargetName,
                },
            ));
        };
        if name_node.flags.0 != 0 || identifier.flow_node.is_some() {
            return Err(AssignmentInvariant::InvalidIdentifierShape(name).into());
        }
        if identifier.text != expected_name {
            return Err(AssignmentInvariant::IdentifierNameMismatch {
                reference,
                declaration: name,
            }
            .into());
        }
        if let Some(type_node) = variable.type_.map(|node| self.reference(node)) {
            self.require_parent(type_node, Some(declaration.node))?;
        }
        if let Some(initializer) = variable.initializer.map(|node| self.reference(node)) {
            self.require_parent(initializer, Some(declaration.node))?;
        }

        let list = declaration_node
            .parent
            .map(|node| self.reference(node))
            .ok_or(AssignmentInvariant::InvalidDeclarationList(declaration))?;
        let list_node = self.node(list)?;
        let NodeData::VariableDeclarationList(list_data) = &list_node.data else {
            return Err(AssignmentInvariant::InvalidDeclarationList(list).into());
        };
        if !matches!(list_node.flags.0, 0 | NODE_FLAG_LET | NODE_FLAG_CONST) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryVariable(list),
            ));
        }
        let binding_matches = flags == SymbolFlags::FUNCTION_SCOPED_VARIABLE
            && list_node.flags.0 == 0
            || flags == SymbolFlags::BLOCK_SCOPED_VARIABLE
                && matches!(list_node.flags.0, NODE_FLAG_LET | NODE_FLAG_CONST);
        let occurrences = list_data
            .declarations
            .nodes
            .iter()
            .filter(|candidate| **candidate == declaration.node)
            .count();
        if !binding_matches
            || list_data.facts != 0
            || list_data.declarations.range != list_node.range
            || occurrences != 1
        {
            return Err(AssignmentInvariant::InvalidDeclarationList(list).into());
        }
        if list_data.declarations.has_trailing_comma {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryVariable(list),
            ));
        }

        let variable_statement = list_node
            .parent
            .map(|node| self.reference(node))
            .ok_or(AssignmentInvariant::InvalidVariableStatement(list))?;
        let statement_node = self.node(variable_statement)?;
        let NodeData::VariableStatement(statement) = &statement_node.data else {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NestedTarget(declaration),
            ));
        };
        if statement_node.flags.0 != 0
            || statement.declaration_list != list.node
            || statement.flow_node.is_some()
            || statement.facts != 0
        {
            return Err(AssignmentInvariant::InvalidVariableStatement(variable_statement).into());
        }
        if statement.modifiers.is_some() {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryVariable(variable_statement),
            ));
        }
        if statement_node.parent != Some(self.bound.source_file().node) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NestedTarget(variable_statement),
            ));
        }
        Ok(())
    }

    fn is_identifier_named(
        &self,
        reference: NodeRef,
        expected: &str,
    ) -> Result<bool, AssignmentPlanError> {
        let node = self.node(reference)?;
        let NodeData::Identifier(identifier) = &node.data else {
            return Ok(false);
        };
        if node.flags.0 != 0 || identifier.flow_node.is_some() {
            return Err(AssignmentInvariant::InvalidIdentifierShape(reference).into());
        }
        Ok(identifier.text == expected)
    }

    fn preflight_program(&self) -> Result<(), AssignmentPlanError> {
        let file = self.bound.file_id();
        if self.bound.node_arena_id() != self.arena.id() {
            return Err(AssignmentInvariant::WrongArena {
                file,
                expected: self.bound.node_arena_id(),
                actual: self.arena.id(),
            }
            .into());
        }
        if self.bound.node_arena_revision() != self.arena.revision() {
            return Err(AssignmentInvariant::ArenaRevisionMismatch {
                file,
                expected: self.bound.node_arena_revision(),
                actual: self.arena.revision(),
            }
            .into());
        }
        if !self.store.contains_node_ref(self.bound.source_file()) {
            return Err(AssignmentInvariant::StoreSourceMismatch(self.bound.source_file()).into());
        }
        Ok(())
    }

    fn node(&self, reference: NodeRef) -> Result<&Node, AssignmentPlanError> {
        if !reference.is_for(self.arena.id(), self.bound.file_id())
            || !self.store.contains_node_ref(reference)
        {
            return Err(AssignmentInvariant::MissingNode(reference).into());
        }
        if !self.bound.contains(reference) {
            return Err(AssignmentInvariant::NodeNotBound(reference).into());
        }
        let node = self
            .arena
            .get(reference.node)
            .ok_or(AssignmentInvariant::MissingNode(reference))?;
        if !node.data.matches_syntax_kind(node.kind) {
            return Err(AssignmentInvariant::MismatchedNodeData {
                node: reference,
                kind: node.kind,
            }
            .into());
        }
        Ok(node)
    }

    fn require_parent(
        &self,
        node: NodeRef,
        expected: Option<ts_ast::NodeId>,
    ) -> Result<(), AssignmentPlanError> {
        let actual = self.node(node)?.parent;
        if actual != expected {
            return Err(AssignmentInvariant::InvalidParent {
                node,
                expected,
                actual,
            }
            .into());
        }
        Ok(())
    }

    fn reference(&self, node: ts_ast::NodeId) -> NodeRef {
        NodeRef::new(self.arena.id(), self.bound.file_id(), node)
    }
}

impl AssignmentPlanner<'_, '_> {
    #[allow(clippy::too_many_lines)] // Prove the statement, receiver declaration, and actual class together.
    fn plan_own_class_property_assignment(
        &self,
        statement: NodeRef,
    ) -> Result<Option<OwnClassPropertyAssignmentPlan>, AssignmentPlanError> {
        self.preflight_program()?;
        if self
            .bound
            .source_facts()
            .is_none_or(ts_binder::CanonicalSourceFileFacts::is_javascript_file)
        {
            return Ok(None);
        }
        let statement_node = self.node(statement)?;
        let NodeData::ExpressionStatement(statement_data) = &statement_node.data else {
            return Ok(None);
        };
        let expression = self.reference(statement_data.expression);
        let expression_node = self.node(expression)?;
        let NodeData::BinaryExpression(binary) = &expression_node.data else {
            return Ok(None);
        };
        let left = self.reference(binary.left);
        let NodeData::PropertyAccessExpression(access) = &self.node(left)?.data else {
            return Ok(None);
        };
        let receiver = self.reference(access.expression);
        let receiver_node = self.node(receiver)?;
        let NodeData::Identifier(identifier) = &receiver_node.data else {
            return Ok(None);
        };
        let operator = self.reference(binary.operator_token);
        let operator_node = self.node(operator)?;
        if operator_node.kind != SyntaxKind::EqualsToken {
            return Ok(None);
        }
        if statement_node.kind != SyntaxKind::ExpressionStatement
            || statement_node.flags.0 != 0
            || statement_data.flow_node.is_some()
        {
            return Err(AssignmentInvariant::InvalidStatementShape(statement).into());
        }
        if statement_node.parent != Some(self.bound.source_file().node) {
            return Ok(None);
        }
        let NodeData::SourceFile(source) = &self.node(self.bound.source_file())?.data else {
            return Err(AssignmentInvariant::InvalidStatementShape(statement).into());
        };
        if !source.statements.nodes.contains(&statement.node) {
            return Err(AssignmentInvariant::InvalidStatementShape(statement).into());
        }
        if expression_node.flags.0 != 0
            || binary.symbol.is_some()
            || binary.type_.is_some()
            || binary.facts != 0
            || binary.modifiers.is_some()
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryAssignment(expression),
            ));
        }
        if operator_node.flags.0 != 0 || !matches!(operator_node.data, NodeData::Token(_)) {
            return Err(AssignmentInvariant::InvalidOperatorToken(operator).into());
        }
        if receiver_node.flags.0 != 0 || identifier.flow_node.is_some() {
            return Err(AssignmentInvariant::InvalidIdentifierShape(receiver).into());
        }
        let right = self.reference(binary.right);
        self.require_parent(expression, Some(statement.node))?;
        self.require_parent(left, Some(expression.node))?;
        self.require_parent(right, Some(expression.node))?;
        self.require_parent(operator, Some(expression.node))?;
        self.require_parent(receiver, Some(left.node))?;
        if self.is_assignment_expression(right)? {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::ChainedAssignment(right),
            ));
        }
        let resolved = self.resolve(receiver, &identifier.text)?;
        let routed = self.route_value_symbol(resolved)?;
        if routed.redirect.is_some() || routed.export_local.is_some() {
            return Ok(None);
        }
        let receiver_symbol = routed.target;
        if let Some(cached) = self
            .store
            .symbol_node_links(receiver)
            .and_then(|links| links.resolved_symbol)
            && cached != receiver_symbol
        {
            return Err(AssignmentInvariant::ResolvedSymbolMismatch {
                node: receiver,
                expected: receiver_symbol,
                actual: cached,
            }
            .into());
        }
        let owner = self
            .store
            .symbol(receiver_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(receiver_symbol))?;
        let (class_symbol, side) = if owner.flags() == SymbolFlags::CLASS {
            (receiver_symbol, super::classes::ClassPropertySide::Static)
        } else {
            if !matches!(
                owner.flags(),
                SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::BLOCK_SCOPED_VARIABLE
            ) {
                return Ok(None);
            }
            let Some([declaration]) = owner.declarations() else {
                return Ok(None);
            };
            if !declaration.is_for(receiver.arena, receiver.file) {
                return Ok(None);
            }
            if owner.value_declaration() != Some(*declaration) {
                return Err(AssignmentInvariant::InvalidSymbolShape(receiver_symbol).into());
            }
            self.validate_declaration_symbol(
                receiver,
                *declaration,
                receiver_symbol,
                None,
                &identifier.text,
            )?;
            let variable_node = self.node(*declaration)?;
            let NodeData::VariableDeclaration(variable) = &variable_node.data else {
                return Ok(None);
            };
            if variable_node.range.end > statement_node.range.start {
                return Ok(None);
            }
            let (name, meaning) = if let Some(annotation) = variable.type_ {
                let annotation = self.reference(annotation);
                self.require_parent(annotation, Some(declaration.node))?;
                let NodeData::TypeReferenceNode(reference) = &self.node(annotation)?.data else {
                    return Ok(None);
                };
                if reference.type_arguments.is_some() {
                    return Ok(None);
                }
                let name = self.reference(reference.type_name);
                self.require_parent(name, Some(annotation.node))?;
                (name, SymbolFlags::TYPE)
            } else if let Some(initializer) = variable.initializer {
                let initializer = self.reference(initializer);
                self.require_parent(initializer, Some(declaration.node))?;
                let NodeData::NewExpression(construction) = &self.node(initializer)?.data else {
                    return Ok(None);
                };
                if construction.type_arguments.is_some() {
                    return Ok(None);
                }
                let name = self.reference(construction.expression);
                self.require_parent(name, Some(initializer.node))?;
                (name, SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE)
            } else {
                return Ok(None);
            };
            let NodeData::Identifier(identifier) = &self.node(name)?.data else {
                return Ok(None);
            };
            let resolved = self.resolve_with_meaning(name, &identifier.text, meaning)?;
            let routed = self.route_value_symbol(resolved)?;
            if routed.redirect.is_some() || routed.export_local.is_some() {
                return Ok(None);
            }
            (routed.target, super::classes::ClassPropertySide::Instance)
        };
        let owner = self
            .store
            .symbol(class_symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(class_symbol))?;
        if owner.flags() != SymbolFlags::CLASS {
            return Ok(None);
        }
        let Some([class_declaration]) = owner.declarations() else {
            return Ok(None);
        };
        if !class_declaration.is_for(receiver.arena, receiver.file) {
            return Ok(None);
        }
        let class_node = self.node(*class_declaration)?;
        let NodeData::ClassDeclaration(class) = &class_node.data else {
            return Err(AssignmentInvariant::InvalidSymbolShape(class_symbol).into());
        };
        if owner.value_declaration() != Some(*class_declaration)
            || owner.check_flags() != CheckFlags::NONE
            || owner.export_symbol().is_some()
            || self.bound.symbol(*class_declaration) != Some(class_symbol)
            || self.store.get_merged_symbol(class_symbol) != Some(class_symbol)
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(class_symbol).into());
        }
        if class_node.parent != Some(self.bound.source_file().node)
            || class_node.range.end > statement_node.range.start
            || class.type_parameters.is_some()
            || class.heritage_clauses.is_some()
        {
            return Ok(None);
        }
        if owner.parent().is_some() {
            match super::classes::source_class_type_owner_declaration(
                self.store,
                self.host,
                class_symbol,
            ) {
                Ok(declaration) if declaration == *class_declaration => {}
                Err(super::classes::ClassError::Unsupported(_)) => return Ok(None),
                Err(super::classes::ClassError::DeclaredType(error)) => {
                    return Err(AssignmentPlanError::DeclaredType(error));
                }
                Ok(_) | Err(super::classes::ClassError::Invariant(_)) => {
                    return Err(AssignmentInvariant::InvalidSymbolShape(class_symbol).into());
                }
            }
        }
        Ok(Some(OwnClassPropertyAssignmentPlan {
            statement,
            expression,
            left,
            right,
            receiver,
            receiver_symbol,
            class_symbol,
            class_declaration: *class_declaration,
            side,
        }))
    }

    fn plan_syntax(&self, statement: NodeRef) -> Result<AssignmentSyntaxPlan, AssignmentPlanError> {
        self.preflight_program()?;
        let statement_node = self.node(statement)?;
        let NodeData::ExpressionStatement(statement_data) = &statement_node.data else {
            return Err(Self::unsupported(
                statement,
                statement_node.kind,
                AssignmentSyntaxRole::Statement,
            ));
        };
        if statement_node.kind != SyntaxKind::ExpressionStatement
            || statement_node.flags.0 != 0
            || statement_data.flow_node.is_some()
        {
            return Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidStatementShape(statement),
            ));
        }
        if statement_node.parent != Some(self.bound.source_file().node) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NestedTarget(statement),
            ));
        }

        let expression = self.reference(statement_data.expression);
        self.require_parent(expression, Some(statement.node))?;
        let expression_node = self.node(expression)?;
        let NodeData::BinaryExpression(binary) = &expression_node.data else {
            return Err(Self::unsupported(
                expression,
                expression_node.kind,
                AssignmentSyntaxRole::Expression,
            ));
        };
        if expression_node.kind != SyntaxKind::BinaryExpression
            || expression_node.flags.0 != 0
            || binary.symbol.is_some()
            || binary.type_.is_some()
            || binary.facts != 0
            || binary.modifiers.is_some()
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryAssignment(expression),
            ));
        }

        let operator = self.reference(binary.operator_token);
        self.require_parent(operator, Some(expression.node))?;
        let operator_node = self.node(operator)?;
        if !matches!(operator_node.data, NodeData::Token(_)) || operator_node.flags.0 != 0 {
            return Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidOperatorToken(operator),
            ));
        }
        if operator_node.kind != SyntaxKind::EqualsToken
            && compound_assignment_binary_operator(operator_node.kind).is_none()
        {
            return Err(Self::unsupported(
                operator,
                operator_node.kind,
                AssignmentSyntaxRole::Operator,
            ));
        }

        let left = self.reference(binary.left);
        let right = self.reference(binary.right);
        self.require_parent(left, Some(expression.node))?;
        self.require_parent(right, Some(expression.node))?;
        if self.is_assignment_expression(right)? {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::ChainedAssignment(right),
            ));
        }

        Ok(AssignmentSyntaxPlan {
            expression,
            left,
            operator: operator_node.kind,
            right,
        })
    }

    fn plan(&self, statement: NodeRef) -> Result<SimpleAssignmentPlan, AssignmentPlanError> {
        let AssignmentSyntaxPlan {
            expression,
            left,
            operator,
            right,
        } = self.plan_syntax(statement)?;
        let left_node = self.node(left)?;
        let NodeData::Identifier(identifier) = &left_node.data else {
            return Err(Self::unsupported(
                left,
                left_node.kind,
                AssignmentSyntaxRole::LeftHandSide,
            ));
        };
        if left_node.kind != SyntaxKind::Identifier
            || left_node.flags.0 != 0
            || identifier.flow_node.is_some()
        {
            return Err(AssignmentInvariant::InvalidIdentifierShape(left).into());
        }
        let name = identifier.text.clone();

        let resolved = self.resolve(left, &name)?;
        let routed = self.route_value_symbol(resolved)?;
        if let Some((source, target)) = routed.redirect {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::MergedTarget {
                    node: left,
                    source,
                    target,
                },
            ));
        }
        let target = routed.target;
        let export_local = routed.export_local;
        let ambient_target = self.ambient_targets.contains(&target);
        let uninitialized_target = self.uninitialized_targets.contains(&target);
        let mutable_target = self.mutable_targets.contains(&target);
        let javascript_target = self
            .bound
            .source_facts()
            .is_some_and(ts_binder::CanonicalSourceFileFacts::is_javascript_file);
        if u8::from(ambient_target) + u8::from(uninitialized_target) + u8::from(mutable_target) > 1
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(target).into());
        }
        let target_record = self
            .store
            .symbol(target)
            .ok_or(AssignmentInvariant::InvalidSymbol(target))?;
        let flags = target_record.flags();
        if flags.intersects(SymbolFlags::ALIAS) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::AliasTarget {
                    node: left,
                    symbol: target,
                },
            ));
        }
        if flags.intersects(SymbolFlags::BLOCK_SCOPED_VARIABLE)
            && !ambient_target
            && !uninitialized_target
            && !mutable_target
            && !javascript_target
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::BlockScopedTarget {
                    node: left,
                    symbol: target,
                },
            ));
        }
        if flags != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            && flags != SymbolFlags::BLOCK_SCOPED_VARIABLE
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonVariableTarget {
                    node: left,
                    symbol: target,
                    flags,
                },
            ));
        }
        if target_record.check_flags() != CheckFlags::NONE
            || target_record.members().is_some()
            || target_record.exports().is_some()
            || target_record.export_symbol().is_some()
        {
            return Err(AssignmentInvariant::InvalidSymbolShape(target).into());
        }
        let declarations = target_record
            .declarations()
            .ok_or(AssignmentInvariant::MissingDeclarations(target))?;
        let [declaration] = declarations else {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonUniqueTarget {
                    node: left,
                    symbol: target,
                    declaration_count: declarations.len(),
                },
            ));
        };
        let declaration = *declaration;
        if declaration.file != left.file || declaration.arena != left.arena {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::CrossFileTarget {
                    node: left,
                    declaration,
                },
            ));
        }
        if target_record.value_declaration() != Some(declaration) {
            return Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::ValueDeclarationMismatch {
                    symbol: target,
                    declaration,
                    value_declaration: target_record.value_declaration(),
                },
            ));
        }
        if target_record.name().as_bytes() != name.as_bytes() {
            return Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::IdentifierNameMismatch {
                    reference: left,
                    declaration,
                },
            ));
        }

        self.validate_declaration_symbol(left, declaration, target, export_local, &name)?;
        let target_type_node = self.validate_variable_declaration(
            left,
            declaration,
            &name,
            ambient_target.then_some((target, flags)),
            uninitialized_target.then_some((target, flags)),
            mutable_target.then_some((target, flags)),
            javascript_target.then_some((target, flags)),
        )?;
        Ok(SimpleAssignmentPlan {
            expression,
            left,
            operator,
            right,
            target_symbol: target,
            target_type_node,
        })
    }

    fn preflight_program(&self) -> Result<(), AssignmentPlanError> {
        let file = self.bound.file_id();
        if self.bound.node_arena_id() != self.arena.id() {
            return Err(AssignmentInvariant::WrongArena {
                file,
                expected: self.bound.node_arena_id(),
                actual: self.arena.id(),
            }
            .into());
        }
        if self.bound.node_arena_revision() != self.arena.revision() {
            return Err(AssignmentInvariant::ArenaRevisionMismatch {
                file,
                expected: self.bound.node_arena_revision(),
                actual: self.arena.revision(),
            }
            .into());
        }
        if !self.store.contains_node_ref(self.bound.source_file()) {
            return Err(AssignmentInvariant::StoreSourceMismatch(self.bound.source_file()).into());
        }
        Ok(())
    }

    fn resolve(&self, left: NodeRef, name: &str) -> Result<SemanticSymbolId, AssignmentPlanError> {
        self.resolve_with_meaning(left, name, SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE)
    }

    fn resolve_with_meaning(
        &self,
        left: NodeRef,
        name: &str,
        meaning: SymbolFlags,
    ) -> Result<SemanticSymbolId, AssignmentPlanError> {
        let mut callback_host = self
            .host
            .name_resolver_host(self.store)
            .map_err(AssignmentPlanError::DeclaredType)?;
        let mut resolver = CanonicalNameResolver::new(
            self.arena,
            self.bound,
            self.store.symbol_store(),
            &mut callback_host,
        )
        .map_err(|error| Self::name_resolution_error(left, error))?;
        match resolver.resolve(
            Some(CanonicalResolutionLocation::Bound(left)),
            name,
            meaning,
            None,
            false,
            false,
        ) {
            Ok(Some(symbol)) => Ok(symbol),
            Ok(None) => Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::UnresolvedIdentifier(left),
            )),
            Err(CanonicalNameResolutionError::AliasResolutionUnavailable(symbol)) => {
                Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::AliasTarget { node: left, symbol },
                ))
            }
            Err(error) => Err(Self::name_resolution_error(left, error)),
        }
    }

    fn name_resolution_error(
        node: NodeRef,
        error: CanonicalNameResolutionError,
    ) -> AssignmentPlanError {
        match error {
            error @ (CanonicalNameResolutionError::JavaScriptDeferred(_)
            | CanonicalNameResolutionError::CommonJsDeferred(_)
            | CanonicalNameResolutionError::JsDocDeferred(_)) => {
                AssignmentPlanError::Unsupported(AssignmentUnsupported::ResolverDeferred {
                    node,
                    error,
                })
            }
            error => AssignmentPlanError::Invariant(AssignmentInvariant::NameResolution(error)),
        }
    }

    fn route_value_symbol(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<RoutedValueSymbol, AssignmentPlanError> {
        let record = self
            .store
            .symbol(symbol)
            .ok_or(AssignmentInvariant::InvalidSymbol(symbol))?;
        let export_local = record.flags().intersects(SymbolFlags::EXPORT_VALUE);
        let routed = if export_local {
            if record.flags() != SymbolFlags::EXPORT_VALUE
                || record.check_flags() != CheckFlags::NONE
                || !matches!(record.declarations(), Some([_]))
                || record.value_declaration().is_some()
                || record.members().is_some()
                || record.exports().is_some()
                || record.parent().is_some()
            {
                return Err(AssignmentInvariant::InvalidExportLocalShape(symbol).into());
            }
            let export_symbol = record
                .export_symbol()
                .ok_or(AssignmentInvariant::MissingExportSymbol(symbol))?;
            if self.store.symbol(export_symbol).is_none() {
                return Err(AssignmentInvariant::InvalidExportSymbol {
                    value_symbol: symbol,
                    export_symbol,
                }
                .into());
            }
            export_symbol
        } else {
            symbol
        };
        let merged = self
            .store
            .get_merged_symbol(routed)
            .ok_or(AssignmentInvariant::InvalidMergedSymbol(routed))?;
        let redirect = (merged != routed).then_some((routed, merged));
        Ok(RoutedValueSymbol {
            target: merged,
            redirect,
            export_local: export_local.then_some(symbol),
        })
    }

    fn validate_declaration_symbol(
        &self,
        left: NodeRef,
        declaration: NodeRef,
        target: SemanticSymbolId,
        export_local: Option<SemanticSymbolId>,
        reference_name: &str,
    ) -> Result<(), AssignmentPlanError> {
        let raw = self
            .bound
            .symbol(declaration)
            .ok_or(AssignmentInvariant::MissingDeclarationSymbol(declaration))?;
        let merged = self
            .store
            .get_merged_symbol(raw)
            .ok_or(AssignmentInvariant::InvalidMergedSymbol(raw))?;
        if merged != raw {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::MergedTarget {
                    node: left,
                    source: raw,
                    target: merged,
                },
            ));
        }
        if merged != target {
            return Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::DeclarationSymbolMismatch {
                    declaration,
                    expected: target,
                    actual: merged,
                },
            ));
        }
        let local = self.bound.local_symbol(declaration);
        if local != export_local {
            return Err(AssignmentInvariant::LocalExportSymbolMismatch {
                declaration,
                expected: export_local,
                actual: local,
            }
            .into());
        }
        if let Some(local) = local {
            self.validate_export_local(local, declaration, target, reference_name)?;
        }
        self.validate_target_parent(target, export_local.is_some())?;
        Ok(())
    }

    fn validate_export_local(
        &self,
        local: SemanticSymbolId,
        declaration: NodeRef,
        target: SemanticSymbolId,
        reference_name: &str,
    ) -> Result<(), AssignmentPlanError> {
        let record = self
            .store
            .symbol(local)
            .ok_or(AssignmentInvariant::InvalidSymbol(local))?;
        if record.flags() != SymbolFlags::EXPORT_VALUE
            || record.check_flags() != CheckFlags::NONE
            || record.name().as_bytes() != reference_name.as_bytes()
            || record.declarations() != Some(&[declaration])
            || record.value_declaration().is_some()
            || record.members().is_some()
            || record.exports().is_some()
            || record.parent().is_some()
            || record.export_symbol() != Some(target)
            || self.store.get_merged_symbol(local) != Some(local)
        {
            return Err(AssignmentInvariant::InvalidExportLocalShape(local).into());
        }
        Ok(())
    }

    fn validate_target_parent(
        &self,
        target: SemanticSymbolId,
        exported: bool,
    ) -> Result<(), AssignmentPlanError> {
        let expected = if exported {
            let source = self.bound.source_file();
            let raw = self
                .bound
                .symbol(source)
                .ok_or(AssignmentInvariant::MissingSourceSymbol(source))?;
            let merged = self
                .store
                .get_merged_symbol(raw)
                .ok_or(AssignmentInvariant::InvalidMergedSymbol(raw))?;
            if merged != raw {
                return Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::MergedTarget {
                        node: source,
                        source: raw,
                        target: merged,
                    },
                ));
            }
            Some(merged)
        } else {
            None
        };
        let actual = self
            .store
            .symbol(target)
            .ok_or(AssignmentInvariant::InvalidSymbol(target))?
            .parent();
        if actual != expected {
            return Err(AssignmentInvariant::InvalidTargetParent {
                symbol: target,
                expected,
                actual,
            }
            .into());
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)] // Each assignment-target family has distinct provenance.
    fn validate_variable_declaration(
        &self,
        left: NodeRef,
        declaration: NodeRef,
        reference_name: &str,
        ambient_target: Option<(SemanticSymbolId, SymbolFlags)>,
        uninitialized_target: Option<(SemanticSymbolId, SymbolFlags)>,
        mutable_target: Option<(SemanticSymbolId, SymbolFlags)>,
        javascript_target: Option<(SemanticSymbolId, SymbolFlags)>,
    ) -> Result<Option<NodeRef>, AssignmentPlanError> {
        let declaration_node = self.node(declaration)?;
        let NodeData::VariableDeclaration(variable) = &declaration_node.data else {
            return Err(Self::unsupported(
                declaration,
                declaration_node.kind,
                AssignmentSyntaxRole::TargetDeclaration,
            ));
        };
        if declaration_node.kind != SyntaxKind::VariableDeclaration
            || declaration_node.flags.0 != 0
            || variable.exclamation_token.is_some()
            || variable.local_symbol.is_some()
            || variable.symbol.is_some()
            || variable.facts != 0
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryVariable(declaration),
            ));
        }

        let name = self.reference(variable.name);
        self.require_parent(name, Some(declaration.node))?;
        let name_node = self.node(name)?;
        let NodeData::Identifier(identifier) = &name_node.data else {
            return Err(Self::unsupported(
                name,
                name_node.kind,
                AssignmentSyntaxRole::TargetName,
            ));
        };
        if name_node.kind != SyntaxKind::Identifier
            || name_node.flags.0 != 0
            || identifier.flow_node.is_some()
        {
            return Err(AssignmentInvariant::InvalidIdentifierShape(name).into());
        }
        if identifier.text != reference_name {
            return Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::IdentifierNameMismatch {
                    reference: left,
                    declaration: name,
                },
            ));
        }

        let type_node = variable.type_.map(|node| self.reference(node));
        if let Some(type_node) = type_node {
            self.require_parent(type_node, Some(declaration.node))?;
            self.node(type_node)?;
        } else if javascript_target.is_none()
            && mutable_target.is_none()
            && ambient_target.is_none()
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::MissingTargetType(declaration),
            ));
        }
        if let Some((ambient_target, ambient_flags)) = ambient_target {
            self.validate_ambient_variable_statement(
                left,
                declaration,
                ambient_target,
                ambient_flags,
            )?;
            return Ok(type_node);
        }
        match (variable.initializer, uninitialized_target) {
            (Some(initializer), None) => {
                let initializer = self.reference(initializer);
                self.require_parent(initializer, Some(declaration.node))?;
                self.node(initializer)?;
            }
            (None, None) if javascript_target.is_none() => {
                return Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::MissingTargetInitializer(declaration),
                ));
            }
            (None, _) => {}
            (Some(_), Some(_)) => {
                return Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::NonOrdinaryVariable(declaration),
                ));
            }
        }

        let list = declaration_node
            .parent
            .map(|node| self.reference(node))
            .ok_or(AssignmentInvariant::InvalidDeclarationList(declaration))?;
        let list_node = self.node(list)?;
        let NodeData::VariableDeclarationList(list_data) = &list_node.data else {
            return Err(AssignmentInvariant::InvalidDeclarationList(list).into());
        };
        let expected_list_flags = match uninitialized_target
            .or(mutable_target)
            .or(javascript_target)
        {
            None => 0,
            Some((_, flags)) if flags == SymbolFlags::FUNCTION_SCOPED_VARIABLE => 0,
            Some((_, flags)) if flags == SymbolFlags::BLOCK_SCOPED_VARIABLE => NODE_FLAG_LET,
            Some(_) => return Err(AssignmentInvariant::InvalidDeclarationList(list).into()),
        };
        if list_node.flags.0 != expected_list_flags
            && list_node.flags.0 & (NODE_FLAG_LET | NODE_FLAG_CONST) != 0
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::BlockScopedTarget {
                    node: left,
                    symbol: uninitialized_target
                        .or(mutable_target)
                        .or(javascript_target)
                        .map_or_else(
                            || {
                                self.bound.symbol(declaration).ok_or(
                                    AssignmentInvariant::MissingDeclarationSymbol(declaration),
                                )
                            },
                            |(symbol, _)| Ok(symbol),
                        )?,
                },
            ));
        }
        let occurrences = list_data
            .declarations
            .nodes
            .iter()
            .filter(|candidate| **candidate == declaration.node)
            .count();
        if list_node.kind != SyntaxKind::VariableDeclarationList
            || list_node.flags.0 != expected_list_flags
            || list_data.facts != 0
            || list_data.declarations.range != list_node.range
            || occurrences != 1
        {
            return Err(AssignmentInvariant::InvalidDeclarationList(list).into());
        }
        if list_data.declarations.has_trailing_comma {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryVariable(list),
            ));
        }

        let variable_statement = list_node
            .parent
            .map(|node| self.reference(node))
            .ok_or(AssignmentInvariant::InvalidVariableStatement(list))?;
        let statement_node = self.node(variable_statement)?;
        let NodeData::VariableStatement(statement) = &statement_node.data else {
            return Err(AssignmentInvariant::InvalidVariableStatement(variable_statement).into());
        };
        if statement_node.kind != SyntaxKind::VariableStatement
            || statement_node.flags.0 != 0
            || statement.declaration_list != list.node
            || statement.flow_node.is_some()
            || statement.facts != 0
        {
            return Err(AssignmentInvariant::InvalidVariableStatement(variable_statement).into());
        }
        if statement_node.parent != Some(self.bound.source_file().node) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NestedTarget(variable_statement),
            ));
        }
        self.validate_variable_modifiers(variable_statement, statement.modifiers.as_ref())?;
        Ok(type_node)
    }

    fn validate_ambient_variable_statement(
        &self,
        left: NodeRef,
        declaration: NodeRef,
        ambient_target: SemanticSymbolId,
        ambient_flags: SymbolFlags,
    ) -> Result<(), AssignmentPlanError> {
        let declaration_node = self.node(declaration)?;
        let NodeData::VariableDeclaration(variable) = &declaration_node.data else {
            return Err(Self::unsupported(
                declaration,
                declaration_node.kind,
                AssignmentSyntaxRole::TargetDeclaration,
            ));
        };
        if let Some(initializer) = variable.initializer {
            let initializer = self.reference(initializer);
            self.require_parent(initializer, Some(declaration.node))?;
            let initializer_node = self.node(initializer)?;
            if ambient_flags != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                || variable.type_.is_some()
                || initializer_node.kind != SyntaxKind::NumericLiteral
                || initializer_node.flags.0 != 0
            {
                return Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::NonOrdinaryVariable(declaration),
                ));
            }
        }

        let list = declaration_node
            .parent
            .map(|node| self.reference(node))
            .ok_or(AssignmentInvariant::InvalidDeclarationList(declaration))?;
        let list_node = self.node(list)?;
        let NodeData::VariableDeclarationList(list_data) = &list_node.data else {
            return Err(AssignmentInvariant::InvalidDeclarationList(list).into());
        };
        let expected_list_flags = if ambient_flags == SymbolFlags::FUNCTION_SCOPED_VARIABLE {
            0
        } else if ambient_flags == SymbolFlags::BLOCK_SCOPED_VARIABLE {
            NODE_FLAG_LET
        } else {
            return Err(AssignmentInvariant::InvalidDeclarationList(list).into());
        };
        let occurrences = list_data
            .declarations
            .nodes
            .iter()
            .filter(|candidate| **candidate == declaration.node)
            .count();
        if list_node.kind != SyntaxKind::VariableDeclarationList
            || list_data.facts != 0
            || list_data.declarations.range != list_node.range
            || occurrences != 1
        {
            return Err(AssignmentInvariant::InvalidDeclarationList(list).into());
        }
        if list_node.flags.0 != expected_list_flags {
            if list_node.flags.0 & NODE_FLAG_CONST != 0 {
                return Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::BlockScopedTarget {
                        node: left,
                        symbol: ambient_target,
                    },
                ));
            }
            return Err(AssignmentInvariant::InvalidDeclarationList(list).into());
        }
        if list_data.declarations.has_trailing_comma {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryVariable(list),
            ));
        }

        let variable_statement = list_node
            .parent
            .map(|node| self.reference(node))
            .ok_or(AssignmentInvariant::InvalidVariableStatement(list))?;
        let statement_node = self.node(variable_statement)?;
        let NodeData::VariableStatement(statement) = &statement_node.data else {
            return Err(AssignmentInvariant::InvalidVariableStatement(variable_statement).into());
        };
        if statement_node.kind != SyntaxKind::VariableStatement
            || statement_node.flags.0 != 0
            || statement.declaration_list != list.node
            || statement.flow_node.is_some()
            || statement.facts != 0
        {
            return Err(AssignmentInvariant::InvalidVariableStatement(variable_statement).into());
        }
        if statement_node.parent != Some(self.bound.source_file().node) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NestedTarget(variable_statement),
            ));
        }
        self.validate_ambient_variable_modifiers(variable_statement, statement.modifiers.as_ref())?;
        if !self.ambient_targets.contains(&ambient_target) {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::BlockScopedTarget {
                    node: left,
                    symbol: ambient_target,
                },
            ));
        }
        Ok(())
    }

    fn validate_ambient_variable_modifiers(
        &self,
        statement: NodeRef,
        modifiers: Option<&ts_ast::ModifierList>,
    ) -> Result<(), AssignmentPlanError> {
        let Some(modifiers) = modifiers else {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryVariable(statement),
            ));
        };
        let [modifier] = modifiers.list.nodes.as_slice() else {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryVariable(statement),
            ));
        };
        let modifier = self.reference(*modifier);
        self.require_parent(modifier, Some(statement.node))?;
        let modifier_node = self.node(modifier)?;
        if modifier_node.kind != SyntaxKind::DeclareKeyword
            || !matches!(modifier_node.data, NodeData::Token(_))
            || modifier_node.flags.0 != 0
            || modifiers.flags.0 != 0
            || modifiers.list.has_trailing_comma
        {
            return Err(Self::unsupported(
                modifier,
                modifier_node.kind,
                AssignmentSyntaxRole::TargetModifier,
            ));
        }
        Ok(())
    }

    fn validate_variable_modifiers(
        &self,
        statement: NodeRef,
        modifiers: Option<&ts_ast::ModifierList>,
    ) -> Result<(), AssignmentPlanError> {
        let Some(modifiers) = modifiers else {
            return Ok(());
        };
        let [modifier] = modifiers.list.nodes.as_slice() else {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryVariable(statement),
            ));
        };
        let modifier = self.reference(*modifier);
        self.require_parent(modifier, Some(statement.node))?;
        let modifier_node = self.node(modifier)?;
        if modifier_node.kind != SyntaxKind::ExportKeyword
            || !matches!(modifier_node.data, NodeData::Token(_))
            || modifier_node.flags.0 != 0
            || modifiers.flags.0 != 0
            || modifiers.list.has_trailing_comma
        {
            return Err(Self::unsupported(
                modifier,
                modifier_node.kind,
                AssignmentSyntaxRole::TargetModifier,
            ));
        }
        Ok(())
    }

    fn is_assignment_expression(&self, expression: NodeRef) -> Result<bool, AssignmentPlanError> {
        let node = self.node(expression)?;
        let NodeData::BinaryExpression(binary) = &node.data else {
            return Ok(false);
        };
        let operator = self.reference(binary.operator_token);
        self.require_parent(operator, Some(expression.node))?;
        Ok(self.node(operator)?.kind.is_assignment_operator())
    }

    fn node(&self, reference: NodeRef) -> Result<&Node, AssignmentPlanError> {
        if !reference.is_for(self.arena.id(), self.bound.file_id())
            || !self.store.contains_node_ref(reference)
        {
            return Err(AssignmentInvariant::MissingNode(reference).into());
        }
        if !self.bound.contains(reference) {
            return Err(AssignmentInvariant::NodeNotBound(reference).into());
        }
        let node = self
            .arena
            .get(reference.node)
            .ok_or(AssignmentInvariant::MissingNode(reference))?;
        if !node.data.matches_syntax_kind(node.kind) {
            return Err(AssignmentInvariant::MismatchedNodeData {
                node: reference,
                kind: node.kind,
            }
            .into());
        }
        Ok(node)
    }

    fn require_parent(
        &self,
        node: NodeRef,
        expected: Option<ts_ast::NodeId>,
    ) -> Result<(), AssignmentPlanError> {
        let actual = self.node(node)?.parent;
        if actual != expected {
            return Err(AssignmentInvariant::InvalidParent {
                node,
                expected,
                actual,
            }
            .into());
        }
        Ok(())
    }

    fn reference(&self, node: ts_ast::NodeId) -> NodeRef {
        NodeRef::new(self.arena.id(), self.bound.file_id(), node)
    }

    fn unsupported(
        node: NodeRef,
        kind: SyntaxKind,
        role: AssignmentSyntaxRole,
    ) -> AssignmentPlanError {
        AssignmentPlanError::Unsupported(AssignmentUnsupported::Syntax { node, kind, role })
    }
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName, SymbolData,
    };
    use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
        SymbolNodeLinks, production::GlobalMergeCompletion,
    };

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        bound: BoundFile,
        store: CanonicalTypeMapperStore,
    }

    impl Fixture {
        fn new(source: &str) -> Self {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(901);
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    source_facts(file),
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
                .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
                .unwrap();
            Self {
                parsed,
                file,
                bound,
                store,
            }
        }

        fn javascript(source: &str) -> Self {
            Self::javascript_parsed(parse_javascript_source_file(source))
        }

        fn javascript_parsed(parsed: ParseResult) -> Self {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(905);
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/common.js\""),
                        CanonicalSourceLanguage::JavaScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_javascript_declaration_slice(&parsed.arena, file)
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
                .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
                .unwrap();
            Self {
                parsed,
                file,
                bound,
                store,
            }
        }

        fn host(&self) -> DeclaredTypeHost<'_> {
            DeclaredTypeHost::new_after_global_merge(
                [(&self.parsed.arena, &self.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap()
        }

        fn expression_statement(&self, index: usize) -> NodeRef {
            expression_statements(&self.parsed, self.file)[index]
        }

        fn variable_declaration(&self, expected: &str) -> NodeRef {
            variable_declaration(&self.parsed, self.file, expected)
        }

        fn source_local(&self, name: &str) -> SemanticSymbolId {
            self.bound
                .locals(self.bound.source_file())
                .and_then(|locals| self.store.symbol_table(locals))
                .and_then(|locals| locals.get_source(name))
                .unwrap_or_else(|| panic!("missing source local {name}"))
        }

        fn plan(&self, index: usize) -> Result<SimpleAssignmentPlan, AssignmentPlanError> {
            let host = self.host();
            plan_simple_assignment(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                &host,
                self.expression_statement(index),
            )
        }

        fn commonjs_plan(
            &self,
            index: usize,
        ) -> Result<Option<CommonJsAssignmentPlan>, AssignmentPlanError> {
            plan_commonjs_assignment(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                self.expression_statement(index),
            )
        }

        fn commonjs_named_plan(
            &self,
            index: usize,
        ) -> Result<Option<CommonJsAssignmentPlan>, AssignmentPlanError> {
            plan_commonjs_named_assignment(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                self.expression_statement(index),
            )
        }

        fn arrow_expando_plan(
            &self,
            index: usize,
        ) -> Result<Option<ArrowExpandoAssignmentPlan>, AssignmentPlanError> {
            plan_arrow_expando_assignment(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                self.expression_statement(index),
            )
        }

        fn function_expando_plan(
            &self,
            index: usize,
        ) -> Result<Option<FunctionExpandoAssignmentPlan>, AssignmentPlanError> {
            plan_function_expando_assignment(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                self.expression_statement(index),
            )
        }

        fn nested_function_expando_plan(
            &self,
            index: usize,
        ) -> Result<Option<FunctionExpandoAssignmentPlan>, AssignmentPlanError> {
            plan_nested_function_expando_assignment(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                self.expression_statement(index),
            )
        }

        fn object_expando_plan(
            &self,
            index: usize,
        ) -> Result<Option<ObjectExpandoAssignmentPlan>, AssignmentPlanError> {
            plan_javascript_object_expando_assignment(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                self.expression_statement(index),
            )
        }

        fn prototype_plan(
            &self,
            index: usize,
        ) -> Result<Option<PrototypeAssignmentPlan>, AssignmentPlanError> {
            plan_prototype_assignment(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                self.expression_statement(index),
            )
        }

        fn imported_namespace_plan(
            &self,
            index: usize,
        ) -> Result<Option<ImportedNamespaceAssignmentPlan>, AssignmentPlanError> {
            plan_imported_namespace_assignment(
                &self.parsed.arena,
                &self.bound,
                &self.store,
                self.expression_statement(index),
            )
        }
    }

    fn source_facts(file: FileId) -> CanonicalSourceFileFacts {
        source_facts_with_module_state(file, CanonicalModuleState::External)
    }

    fn source_facts_with_module_state(
        file: FileId,
        module_state: CanonicalModuleState,
    ) -> CanonicalSourceFileFacts {
        CanonicalSourceFileFacts::new(
            EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
            CanonicalSourceLanguage::TypeScript,
            false,
            module_state,
        )
    }

    fn expression_statements(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
        let source = parsed.arena.get(parsed.source_file).unwrap();
        let NodeData::SourceFile(source) = &source.data else {
            panic!("expected source file")
        };
        source
            .statements
            .nodes
            .iter()
            .filter(|node| {
                parsed.arena.get(**node).unwrap().kind == SyntaxKind::ExpressionStatement
            })
            .map(|node| NodeRef::new(parsed.arena.id(), file, *node))
            .collect()
    }

    fn variable_declaration(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                    return None;
                };
                (name.text == expected).then_some(node)
            })
            .unwrap_or_else(|| panic!("missing variable {expected}"));
        NodeRef::new(parsed.arena.id(), file, declaration)
    }

    fn variable_type(parsed: &ParseResult, declaration: NodeRef) -> NodeRef {
        let NodeData::VariableDeclaration(variable) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("expected variable declaration")
        };
        NodeRef::new(parsed.arena.id(), declaration.file, variable.type_.unwrap())
    }

    fn assignment_parts(parsed: &ParseResult, statement: NodeRef) -> (NodeRef, NodeRef, NodeRef) {
        let NodeData::ExpressionStatement(statement_data) =
            &parsed.arena.get(statement.node).unwrap().data
        else {
            panic!("expected expression statement")
        };
        let NodeData::BinaryExpression(binary) =
            &parsed.arena.get(statement_data.expression).unwrap().data
        else {
            panic!("expected binary expression")
        };
        (
            NodeRef::new(parsed.arena.id(), statement.file, statement_data.expression),
            NodeRef::new(parsed.arena.id(), statement.file, binary.left),
            NodeRef::new(parsed.arena.id(), statement.file, binary.right),
        )
    }

    fn observable_state(
        store: &CanonicalTypeMapperStore,
    ) -> (
        usize,
        usize,
        [usize; 26],
        crate::semantic::RelationStateSnapshot,
    ) {
        (
            store.type_len(),
            store.merged_symbol_len(),
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
        )
    }

    #[test]
    fn plans_initialized_typed_var_without_semantic_writes() {
        let fixture = Fixture::new("var target: number = 0; target = 1;");
        let statement = fixture.expression_statement(0);
        let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
        let declaration = fixture.variable_declaration("target");
        let before = observable_state(&fixture.store);

        assert_eq!(
            fixture.plan(0),
            Ok(SimpleAssignmentPlan {
                expression,
                left,
                operator: SyntaxKind::EqualsToken,
                right,
                target_symbol: fixture
                    .bound
                    .symbol(declaration)
                    .expect("target declaration symbol"),
                target_type_node: Some(variable_type(&fixture.parsed, declaration)),
            })
        );
        assert_eq!(observable_state(&fixture.store), before);
    }

    #[test]
    fn plans_exact_arrow_expando_without_semantic_writes() {
        let fixture = Fixture::new("const foo = () => {}; foo.bar = 42; export {};");
        let statement = fixture.expression_statement(0);
        let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
        let NodeData::PropertyAccessExpression(access) =
            &fixture.parsed.arena.get(left.node).unwrap().data
        else {
            panic!("expected foo.bar property access")
        };
        let receiver = NodeRef::new(fixture.parsed.arena.id(), fixture.file, access.expression);
        let declaration = fixture.variable_declaration("foo");
        let NodeData::VariableDeclaration(variable) =
            &fixture.parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("expected foo variable declaration")
        };
        let arrow = NodeRef::new(
            fixture.parsed.arena.id(),
            fixture.file,
            variable.initializer.unwrap(),
        );
        let before = observable_state(&fixture.store);

        assert_eq!(
            fixture.arrow_expando_plan(0),
            Ok(Some(ArrowExpandoAssignmentPlan {
                expression,
                left,
                right,
                receiver,
                variable_symbol: fixture.bound.symbol(declaration).unwrap(),
                owner_symbol: fixture.bound.symbol(arrow).unwrap(),
                property_symbol: fixture.bound.symbol(expression).unwrap(),
            })),
        );
        assert_eq!(observable_state(&fixture.store), before);
    }

    #[test]
    fn plans_javascript_arrow_expandos_for_all_ordinary_variable_bindings() {
        for source in [
            "var callback = () => {}; callback.value = 1;",
            "let callback = () => {}; callback.value = 1;",
            "const callback = () => {}; callback.value = 1;",
        ] {
            let fixture = Fixture::javascript(source);
            let statement = fixture.expression_statement(0);
            let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
            let NodeData::PropertyAccessExpression(access) =
                &fixture.parsed.arena.get(left.node).unwrap().data
            else {
                panic!("expected callback.value property access")
            };
            let receiver = NodeRef::new(fixture.parsed.arena.id(), fixture.file, access.expression);
            let declaration = fixture.variable_declaration("callback");
            let NodeData::VariableDeclaration(variable) =
                &fixture.parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected callback variable declaration")
            };
            let arrow = NodeRef::new(
                fixture.parsed.arena.id(),
                fixture.file,
                variable.initializer.unwrap(),
            );
            let before = observable_state(&fixture.store);

            assert_eq!(
                fixture.arrow_expando_plan(0),
                Ok(Some(ArrowExpandoAssignmentPlan {
                    expression,
                    left,
                    right,
                    receiver,
                    variable_symbol: fixture.bound.symbol(declaration).unwrap(),
                    owner_symbol: fixture.bound.symbol(arrow).unwrap(),
                    property_symbol: fixture.bound.symbol(expression).unwrap(),
                })),
                "{source}",
            );
            assert_eq!(observable_state(&fixture.store), before, "{source}");
        }
    }

    #[test]
    fn anonymous_function_expression_expandos_keep_their_binder_owned_property() {
        for fixture in [
            Fixture::new("const callback = function () {}; callback.value = 1; export {};"),
            Fixture::javascript("var callback = function () {}; callback.value = 1;"),
            Fixture::javascript("const callback = function () {}; callback.value = 1;"),
        ] {
            let statement = fixture.expression_statement(0);
            let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
            let NodeData::PropertyAccessExpression(access) =
                &fixture.parsed.arena.get(left.node).unwrap().data
            else {
                panic!("expected the anonymous function expando property")
            };
            let receiver = NodeRef::new(fixture.parsed.arena.id(), fixture.file, access.expression);
            let declaration = fixture.variable_declaration("callback");
            let NodeData::VariableDeclaration(variable) =
                &fixture.parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected the anonymous function variable")
            };
            let function = NodeRef::new(
                fixture.parsed.arena.id(),
                fixture.file,
                variable.initializer.unwrap(),
            );
            let before = observable_state(&fixture.store);

            assert_eq!(
                fixture.arrow_expando_plan(0),
                Ok(Some(ArrowExpandoAssignmentPlan {
                    expression,
                    left,
                    right,
                    receiver,
                    variable_symbol: fixture.bound.symbol(declaration).unwrap(),
                    owner_symbol: fixture.bound.symbol(function).unwrap(),
                    property_symbol: fixture.bound.symbol(expression).unwrap(),
                })),
            );
            assert_eq!(observable_state(&fixture.store), before);
        }
    }

    #[test]
    fn plans_anonymous_function_expression_expandos_without_semantic_writes() {
        for fixture in [
            Fixture::new("const work = function () {}; work.items = []; export {};"),
            Fixture::javascript("var work = function () {}; work.items = [];"),
            Fixture::javascript("let work = function () {}; work.items = [];"),
            Fixture::javascript("const work = function () {}; work.items = [];"),
        ] {
            let statement = fixture.expression_statement(0);
            let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
            let NodeData::PropertyAccessExpression(access) =
                &fixture.parsed.arena.get(left.node).unwrap().data
            else {
                panic!("expected work.items property access")
            };
            let receiver = NodeRef::new(fixture.parsed.arena.id(), fixture.file, access.expression);
            let declaration = fixture.variable_declaration("work");
            let NodeData::VariableDeclaration(variable) =
                &fixture.parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected work variable declaration")
            };
            let initializer = NodeRef::new(
                fixture.parsed.arena.id(),
                fixture.file,
                variable.initializer.unwrap(),
            );
            let before = observable_state(&fixture.store);

            assert_eq!(
                fixture.arrow_expando_plan(0),
                Ok(Some(ArrowExpandoAssignmentPlan {
                    expression,
                    left,
                    right,
                    receiver,
                    variable_symbol: fixture.bound.symbol(declaration).unwrap(),
                    owner_symbol: fixture.bound.symbol(initializer).unwrap(),
                    property_symbol: fixture.bound.symbol(expression).unwrap(),
                })),
            );
            assert_eq!(observable_state(&fixture.store), before);
        }
    }

    #[test]
    fn annotated_callable_array_expandos_require_exact_declared_properties() {
        for source in [
            concat!(
                "const callback: { (): void; items?: string[] } = () => undefined; ",
                "callback.items = [];",
            ),
            concat!(
                "const callback: { (): void; items: string[] } = () => {}; ",
                "callback.items = [];",
            ),
            concat!(
                "const callback: { (): void; items: string[] } = function () {}; ",
                "callback.items = [];",
            ),
        ] {
            let fixture = Fixture::new(source);
            let statement = fixture.expression_statement(0);
            let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
            let NodeData::PropertyAccessExpression(access) =
                &fixture.parsed.arena.get(left.node).unwrap().data
            else {
                panic!("expected the annotated callable property")
            };
            let receiver = NodeRef::new(fixture.parsed.arena.id(), fixture.file, access.expression);
            let declaration = fixture.variable_declaration("callback");
            let NodeData::VariableDeclaration(variable) =
                &fixture.parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected the annotated callable declaration")
            };
            let initializer = NodeRef::new(
                fixture.parsed.arena.id(),
                fixture.file,
                variable.initializer.unwrap(),
            );
            let before = observable_state(&fixture.store);

            assert_eq!(
                fixture.arrow_expando_plan(0),
                Ok(Some(ArrowExpandoAssignmentPlan {
                    expression,
                    left,
                    right,
                    receiver,
                    variable_symbol: fixture.bound.symbol(declaration).unwrap(),
                    owner_symbol: fixture.bound.symbol(initializer).unwrap(),
                    property_symbol: fixture.bound.symbol(expression).unwrap(),
                })),
                "{source}",
            );
            assert_eq!(observable_state(&fixture.store), before, "{source}");
        }

        for source in [
            "const callback: () => void = () => {}; callback.items = [];",
            concat!(
                "const callback: { (): void; other: string[] } = () => {}; ",
                "callback.items = [];",
            ),
            concat!(
                "const callback: { (): void; items: number[] } = () => {}; ",
                "callback.items = [];",
            ),
            concat!(
                "const callback: { (): void; items: string[] } = () => {}; ",
                "callback.items = ['value'];",
            ),
        ] {
            let fixture = Fixture::new(source);
            let declaration = fixture.variable_declaration("callback");
            let before = observable_state(&fixture.store);

            assert!(matches!(
                fixture.arrow_expando_plan(0),
                Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::NonOrdinaryVariable(node)
                )) if node == declaration
            ));
            assert_eq!(observable_state(&fixture.store), before, "{source}");
        }
    }

    #[test]
    fn imported_namespace_assignments_use_the_ambient_member_without_semantic_writes() {
        let fixture = Fixture::new(concat!(
            "import selected = require('./target'); ",
            "selected.value = 1; ",
            "declare module './target' { let value: number; }",
        ));
        let statement = fixture.expression_statement(0);
        let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
        let NodeData::PropertyAccessExpression(access) =
            &fixture.parsed.arena.get(left.node).unwrap().data
        else {
            panic!("expected selected.value property access")
        };
        let receiver = NodeRef::new(fixture.parsed.arena.id(), fixture.file, access.expression);
        let alias_symbol = fixture.source_local("selected");
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
            .unwrap();
        let namespace_symbol = fixture.bound.symbol(namespace).unwrap();
        let declaration = fixture.variable_declaration("value");
        let property_symbol = fixture.bound.symbol(declaration).unwrap();
        let before = observable_state(&fixture.store);

        assert_eq!(
            fixture.imported_namespace_plan(0),
            Ok(Some(ImportedNamespaceAssignmentPlan {
                expression,
                left,
                right,
                receiver,
                alias_symbol,
                namespace_symbol,
                property_symbol,
                property_type_node: variable_type(&fixture.parsed, declaration),
            })),
        );
        assert!(fixture.bound.symbol(expression).is_none());
        assert_eq!(observable_state(&fixture.store), before);
    }

    #[test]
    fn imported_namespace_assignments_reject_poisoned_receiver_and_foreign_module() {
        let mut fixture = Fixture::new(concat!(
            "import selected = require('./target'); ",
            "selected.value = 1; ",
            "declare module './target' { let value: number; }",
        ));
        let statement = fixture.expression_statement(0);
        let (_, left, _) = assignment_parts(&fixture.parsed, statement);
        let NodeData::PropertyAccessExpression(access) =
            &fixture.parsed.arena.get(left.node).unwrap().data
        else {
            panic!("expected selected.value property access")
        };
        let receiver = NodeRef::new(fixture.parsed.arena.id(), fixture.file, access.expression);
        let alias = fixture.source_local("selected");
        let property = fixture
            .bound
            .symbol(fixture.variable_declaration("value"))
            .unwrap();
        assert!(fixture.store.set_symbol_node_links(
            receiver,
            SymbolNodeLinks {
                resolved_symbol: Some(property),
            },
        ));
        assert_eq!(
            fixture.imported_namespace_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::ResolvedSymbolMismatch {
                    node: receiver,
                    expected: alias,
                    actual: property,
                },
            )),
        );

        let unrelated = Fixture::new(concat!(
            "import selected = require('./target'); ",
            "selected.value = 1; ",
            "declare module './different' { let value: number; }",
        ));
        assert_eq!(unrelated.imported_namespace_plan(0), Ok(None));
    }

    #[test]
    fn arrow_expandos_reject_invalid_property_flags_and_receiver_cache() {
        let mut invalid_property = Fixture::new("const foo = () => {}; foo.bar = 42; export {};");
        let statement = invalid_property.expression_statement(0);
        let (expression, _, _) = assignment_parts(&invalid_property.parsed, statement);
        let property = invalid_property.bound.symbol(expression).unwrap();
        assert!(invalid_property.store.set_symbol_flags(
            property,
            SymbolFlags::PROPERTY,
            CheckFlags::NONE,
        ));
        assert_eq!(
            invalid_property.arrow_expando_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidSymbolShape(property),
            )),
        );

        let mut poisoned_receiver = Fixture::new("const foo = () => {}; foo.bar = 42; export {};");
        let statement = poisoned_receiver.expression_statement(0);
        let (expression, left, _) = assignment_parts(&poisoned_receiver.parsed, statement);
        let NodeData::PropertyAccessExpression(access) =
            &poisoned_receiver.parsed.arena.get(left.node).unwrap().data
        else {
            panic!("expected foo.bar property access")
        };
        let receiver = NodeRef::new(
            poisoned_receiver.parsed.arena.id(),
            poisoned_receiver.file,
            access.expression,
        );
        let variable = poisoned_receiver.source_local("foo");
        let owner = poisoned_receiver
            .bound
            .symbol(expression)
            .and_then(|property| poisoned_receiver.store.symbol(property))
            .and_then(ts_binder::semantic::Symbol::parent)
            .unwrap();
        assert!(poisoned_receiver.store.set_symbol_node_links(
            receiver,
            SymbolNodeLinks {
                resolved_symbol: Some(owner),
            },
        ));
        assert_eq!(
            poisoned_receiver.arrow_expando_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::ResolvedSymbolMismatch {
                    node: receiver,
                    expected: variable,
                    actual: owner,
                },
            )),
        );
    }

    #[test]
    fn arrow_expandos_require_the_source_const_to_appear_first() {
        let fixture = Fixture::new("foo.bar = 42; const foo = () => {}; export {};");
        let statement = fixture.expression_statement(0);
        let (_, left, _) = assignment_parts(&fixture.parsed, statement);
        let NodeData::PropertyAccessExpression(access) =
            &fixture.parsed.arena.get(left.node).unwrap().data
        else {
            panic!("expected foo.bar property access")
        };
        let receiver = NodeRef::new(fixture.parsed.arena.id(), fixture.file, access.expression);

        assert_eq!(
            fixture.arrow_expando_plan(0),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::TargetNotPrior {
                    node: receiver,
                    symbol: fixture.source_local("foo"),
                },
            )),
        );
    }

    #[test]
    fn plans_binder_owned_function_expandos_without_semantic_writes() {
        for fixture in [
            Fixture::new("function work() {} work.value = 1; export {};"),
            Fixture::javascript("function work() {} work.value = 1;"),
        ] {
            let statement = fixture.expression_statement(0);
            let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
            let NodeData::PropertyAccessExpression(access) =
                &fixture.parsed.arena.get(left.node).unwrap().data
            else {
                panic!("expected a direct function expando property")
            };
            let receiver = NodeRef::new(fixture.parsed.arena.id(), fixture.file, access.expression);
            let owner = fixture.source_local("work");
            let property = fixture.bound.symbol(expression).unwrap();
            let before = observable_state(&fixture.store);

            assert_eq!(
                fixture.function_expando_plan(0),
                Ok(Some(FunctionExpandoAssignmentPlan {
                    expression,
                    left,
                    right,
                    receiver,
                    owner_symbol: owner,
                    property_symbol: property,
                })),
            );
            assert_eq!(observable_state(&fixture.store), before);
        }
    }

    #[test]
    fn function_expandos_reject_forged_properties_and_receiver_caches() {
        let mut forged = Fixture::new("function work() {} work.value = 1; export {};");
        let statement = forged.expression_statement(0);
        let (expression, _, _) = assignment_parts(&forged.parsed, statement);
        let property = forged.bound.symbol(expression).unwrap();
        assert!(
            forged
                .store
                .set_symbol_flags(property, SymbolFlags::PROPERTY, CheckFlags::NONE,)
        );
        let before = observable_state(&forged.store);
        assert_eq!(
            forged.function_expando_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidSymbolShape(property),
            )),
        );
        assert_eq!(observable_state(&forged.store), before);

        let mut poisoned = Fixture::new(concat!(
            "function work() {} const other = 1; ",
            "work.value = 1; export {};",
        ));
        let statement = poisoned.expression_statement(0);
        let (_, left, _) = assignment_parts(&poisoned.parsed, statement);
        let NodeData::PropertyAccessExpression(access) =
            &poisoned.parsed.arena.get(left.node).unwrap().data
        else {
            panic!("expected a direct function expando property")
        };
        let receiver = NodeRef::new(poisoned.parsed.arena.id(), poisoned.file, access.expression);
        let owner = poisoned.source_local("work");
        let other = poisoned.source_local("other");
        assert!(poisoned.store.set_symbol_node_links(
            receiver,
            SymbolNodeLinks {
                resolved_symbol: Some(other),
            },
        ));
        let before = observable_state(&poisoned.store);
        assert_eq!(
            poisoned.function_expando_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::ResolvedSymbolMismatch {
                    node: receiver,
                    expected: owner,
                    actual: other,
                },
            )),
        );
        assert_eq!(observable_state(&poisoned.store), before);
    }

    #[test]
    fn nested_function_expandos_reuse_the_earlier_assignment_symbol() {
        let fixture = Fixture::javascript(concat!(
            "function work() {} ",
            "/** @type {{ ready: boolean }} */ ",
            "work.value = { ready: true }; ",
            "work.value.ready = false;",
        ));
        let statement = fixture.expression_statement(1);
        let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
        let NodeData::PropertyAccessExpression(nested) =
            &fixture.parsed.arena.get(left.node).unwrap().data
        else {
            panic!("expected the nested function expando access")
        };
        let parent = NodeRef::new(fixture.parsed.arena.id(), fixture.file, nested.expression);
        let NodeData::PropertyAccessExpression(property) =
            &fixture.parsed.arena.get(parent.node).unwrap().data
        else {
            panic!("expected the binder-owned function expando")
        };
        let receiver = NodeRef::new(fixture.parsed.arena.id(), fixture.file, property.expression);
        let owner = fixture.source_local("work");
        let property = fixture
            .store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| fixture.store.symbol_table(exports))
            .and_then(|exports| exports.get_source("value"))
            .unwrap();
        let before = observable_state(&fixture.store);

        assert!(fixture.bound.symbol(expression).is_none());
        assert_eq!(
            fixture.nested_function_expando_plan(1),
            Ok(Some(FunctionExpandoAssignmentPlan {
                expression,
                left,
                right,
                receiver,
                owner_symbol: owner,
                property_symbol: property,
            })),
        );
        assert_eq!(observable_state(&fixture.store), before);
    }

    #[test]
    fn nested_function_expandos_reject_poisoned_outer_property_cache() {
        let mut fixture = Fixture::javascript(concat!(
            "function work() {} ",
            "/** @type {{ ready: boolean }} */ ",
            "work.value = { ready: true }; ",
            "work.value.ready = false;",
        ));
        let statement = fixture.expression_statement(1);
        let (_, left, _) = assignment_parts(&fixture.parsed, statement);
        let NodeData::PropertyAccessExpression(nested) =
            &fixture.parsed.arena.get(left.node).unwrap().data
        else {
            panic!("expected the nested function expando access")
        };
        let parent = NodeRef::new(fixture.parsed.arena.id(), fixture.file, nested.expression);
        let owner = fixture.source_local("work");
        let property = fixture
            .store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::exports)
            .and_then(|exports| fixture.store.symbol_table(exports))
            .and_then(|exports| exports.get_source("value"))
            .unwrap();
        assert!(fixture.store.set_symbol_node_links(
            parent,
            SymbolNodeLinks {
                resolved_symbol: Some(owner),
            },
        ));
        let before = observable_state(&fixture.store);

        assert_eq!(
            fixture.nested_function_expando_plan(1),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::ResolvedSymbolMismatch {
                    node: parent,
                    expected: property,
                    actual: owner,
                },
            )),
        );
        assert_eq!(observable_state(&fixture.store), before);
    }

    #[test]
    fn prototype_assignments_reuse_ambient_class_method_ownership() {
        let fixture = Fixture::new(concat!(
            "declare class Point { add(dx: number, dy: number): void; } ",
            "Point.prototype.add = function(dx, dy) {};",
        ));
        let statement = fixture.expression_statement(0);
        let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
        let NodeData::PropertyAccessExpression(member) =
            &fixture.parsed.arena.get(left.node).unwrap().data
        else {
            panic!("expected the prototype member access")
        };
        let prototype = NodeRef::new(fixture.parsed.arena.id(), fixture.file, member.expression);
        let NodeData::PropertyAccessExpression(access) =
            &fixture.parsed.arena.get(prototype.node).unwrap().data
        else {
            panic!("expected the class prototype access")
        };
        let receiver = NodeRef::new(fixture.parsed.arena.id(), fixture.file, access.expression);
        let owner = fixture.source_local("Point");
        let owner_record = fixture.store.symbol(owner).unwrap();
        let prototype_symbol = owner_record
            .exports()
            .and_then(|exports| fixture.store.symbol_table(exports))
            .and_then(|exports| exports.get_source("prototype"))
            .unwrap();
        let property = owner_record
            .members()
            .and_then(|members| fixture.store.symbol_table(members))
            .and_then(|members| members.get_source("add"))
            .unwrap();
        let before = observable_state(&fixture.store);

        assert_eq!(fixture.bound.symbol(expression), None);
        assert_eq!(
            fixture.prototype_plan(0),
            Ok(Some(PrototypeAssignmentPlan {
                expression,
                left,
                right,
                receiver,
                prototype,
                receiver_symbol: owner,
                owner_symbol: owner,
                prototype_symbol: Some(prototype_symbol),
                property_symbol: Some(property),
            })),
        );
        assert_eq!(observable_state(&fixture.store), before);
    }

    #[test]
    fn javascript_prototype_assignments_follow_one_function_alias() {
        let fixture = Fixture::javascript(concat!(
            "const original = function () {}; ",
            "var alias = original; ",
            "alias.prototype.method = function () { this; };",
        ));
        let statement = fixture.expression_statement(0);
        let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
        let NodeData::PropertyAccessExpression(member) =
            &fixture.parsed.arena.get(left.node).unwrap().data
        else {
            panic!("expected the prototype member access")
        };
        let prototype = NodeRef::new(fixture.parsed.arena.id(), fixture.file, member.expression);
        let NodeData::PropertyAccessExpression(access) =
            &fixture.parsed.arena.get(prototype.node).unwrap().data
        else {
            panic!("expected the function prototype access")
        };
        let receiver = NodeRef::new(fixture.parsed.arena.id(), fixture.file, access.expression);
        let original = fixture.variable_declaration("original");
        let NodeData::VariableDeclaration(variable) =
            &fixture.parsed.arena.get(original.node).unwrap().data
        else {
            panic!("expected the original function declaration")
        };
        let function = NodeRef::new(
            fixture.parsed.arena.id(),
            fixture.file,
            variable.initializer.unwrap(),
        );
        let before = observable_state(&fixture.store);

        assert_eq!(fixture.bound.symbol(expression), None);
        assert_eq!(
            fixture.prototype_plan(0),
            Ok(Some(PrototypeAssignmentPlan {
                expression,
                left,
                right,
                receiver,
                prototype,
                receiver_symbol: fixture.source_local("alias"),
                owner_symbol: fixture.bound.symbol(function).unwrap(),
                prototype_symbol: None,
                property_symbol: None,
            })),
        );
        assert_eq!(observable_state(&fixture.store), before);
    }

    #[test]
    fn prototype_assignments_reject_poisoned_member_resolution() {
        let mut fixture = Fixture::new(concat!(
            "declare class Point { add(dx: number, dy: number): void; } ",
            "Point.prototype.add = function(dx, dy) {};",
        ));
        let statement = fixture.expression_statement(0);
        let (_, left, _) = assignment_parts(&fixture.parsed, statement);
        let owner = fixture.source_local("Point");
        let method = fixture
            .store
            .symbol(owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| fixture.store.symbol_table(members))
            .and_then(|members| members.get_source("add"))
            .unwrap();
        assert!(fixture.store.set_symbol_node_links(
            left,
            SymbolNodeLinks {
                resolved_symbol: Some(owner),
            },
        ));
        let before = observable_state(&fixture.store);

        assert_eq!(
            fixture.prototype_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::ResolvedSymbolMismatch {
                    node: left,
                    expected: method,
                    actual: owner,
                },
            )),
        );
        assert_eq!(observable_state(&fixture.store), before);
    }

    #[test]
    fn commonjs_function_assignments_keep_their_binder_owned_exports() {
        for (source, named) in [
            ("module.exports = function () {};", false),
            ("exports.method = function () {};", true),
        ] {
            let fixture = Fixture::javascript(source);
            let statement = fixture.expression_statement(0);
            let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
            let target = fixture.bound.symbol(expression).unwrap();
            let before = observable_state(&fixture.store);

            let planned = if named {
                fixture.commonjs_named_plan(0)
            } else {
                fixture.commonjs_plan(0)
            };
            assert_eq!(
                planned,
                Ok(Some(CommonJsAssignmentPlan {
                    expression,
                    left,
                    right,
                    target_symbol: target,
                })),
                "{source}",
            );
            assert_eq!(observable_state(&fixture.store), before, "{source}");
        }
    }

    #[test]
    fn plans_javascript_object_expandos_with_static_property_names() {
        for source in [
            "var object = {}; object['if'] = 1;",
            "let object = {}; object.value = 1;",
            "const object = {}; object[\"ready\"] = true;",
        ] {
            let fixture = Fixture::javascript(source);
            let statement = fixture.expression_statement(0);
            let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
            let (receiver, name, index) = match &fixture.parsed.arena.get(left.node).unwrap().data {
                NodeData::PropertyAccessExpression(access) => (
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, access.expression),
                    NodeRef::new(fixture.parsed.arena.id(), fixture.file, access.name),
                    None,
                ),
                NodeData::ElementAccessExpression(access) => {
                    let index = NodeRef::new(
                        fixture.parsed.arena.id(),
                        fixture.file,
                        access.argument_expression,
                    );
                    (
                        NodeRef::new(fixture.parsed.arena.id(), fixture.file, access.expression),
                        index,
                        Some(index),
                    )
                }
                _ => panic!("expected a static object expando"),
            };
            let declaration = fixture.variable_declaration("object");
            let NodeData::VariableDeclaration(variable) =
                &fixture.parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected one object variable declaration")
            };
            let object = NodeRef::new(
                fixture.parsed.arena.id(),
                fixture.file,
                variable.initializer.unwrap(),
            );
            let before = observable_state(&fixture.store);

            assert_eq!(
                fixture.object_expando_plan(0),
                Ok(Some(ObjectExpandoAssignmentPlan {
                    expression,
                    left,
                    right,
                    receiver,
                    name,
                    index,
                    variable_symbol: fixture.bound.symbol(declaration).unwrap(),
                    owner_symbol: fixture.bound.symbol(object).unwrap(),
                    property_symbol: fixture.bound.symbol(expression).unwrap(),
                })),
                "{source}",
            );
            assert_eq!(observable_state(&fixture.store), before, "{source}");
        }
    }

    #[test]
    fn javascript_object_expandos_reject_invalid_property_and_receiver_provenance() {
        let mut invalid_property = Fixture::javascript("var object = {}; object['if'] = 1;");
        let statement = invalid_property.expression_statement(0);
        let (expression, _, _) = assignment_parts(&invalid_property.parsed, statement);
        let property = invalid_property.bound.symbol(expression).unwrap();
        assert!(invalid_property.store.set_symbol_flags(
            property,
            SymbolFlags::PROPERTY,
            CheckFlags::NONE,
        ));
        let before = observable_state(&invalid_property.store);
        assert_eq!(
            invalid_property.object_expando_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidSymbolShape(property),
            )),
        );
        assert_eq!(observable_state(&invalid_property.store), before);

        let mut poisoned_receiver =
            Fixture::javascript("var object = {}; const other = 1; object['if'] = 1;");
        let statement = poisoned_receiver.expression_statement(0);
        let (_, left, _) = assignment_parts(&poisoned_receiver.parsed, statement);
        let NodeData::ElementAccessExpression(access) =
            &poisoned_receiver.parsed.arena.get(left.node).unwrap().data
        else {
            panic!("expected object['if'] element access")
        };
        let receiver = NodeRef::new(
            poisoned_receiver.parsed.arena.id(),
            poisoned_receiver.file,
            access.expression,
        );
        let object = poisoned_receiver.source_local("object");
        let other = poisoned_receiver.source_local("other");
        assert!(poisoned_receiver.store.set_symbol_node_links(
            receiver,
            SymbolNodeLinks {
                resolved_symbol: Some(other),
            },
        ));
        let before = observable_state(&poisoned_receiver.store);
        assert_eq!(
            poisoned_receiver.object_expando_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::ResolvedSymbolMismatch {
                    node: receiver,
                    expected: object,
                    actual: other,
                },
            )),
        );
        assert_eq!(observable_state(&poisoned_receiver.store), before);
    }

    #[test]
    fn plans_exact_commonjs_export_alias_without_semantic_writes() {
        for source in [
            "const local = 1; module.exports = local;",
            "const local = {}; module.exports = local;",
            "let local = 1; module.exports = local;",
            "var local = 1; module.exports = local;",
            "var local; module.exports = local;",
            concat!(
                "/** @typedef {{ value: number }} Item */\n",
                "const local = 0; module.exports = local;",
            ),
        ] {
            let fixture = Fixture::javascript(source);
            let statement = fixture.expression_statement(0);
            let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
            let target_symbol = fixture.bound.symbol(expression).unwrap();
            let before = observable_state(&fixture.store);

            assert_eq!(
                fixture.commonjs_plan(0),
                Ok(Some(CommonJsAssignmentPlan {
                    expression,
                    left,
                    right,
                    target_symbol,
                })),
                "{source}",
            );
            assert_eq!(observable_state(&fixture.store), before, "{source}");
        }
    }

    #[test]
    fn plans_commonjs_object_literal_exports_without_semantic_writes() {
        for source in [
            "module.exports = {};",
            "module.exports = { value: 1 };",
            "const local = 1; module.exports = { value: local };",
        ] {
            let fixture = Fixture::javascript(source);
            let statement = fixture.expression_statement(0);
            let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
            let target_symbol = fixture.bound.symbol(expression).unwrap();
            let before = observable_state(&fixture.store);

            assert_eq!(
                fixture.store.symbol(target_symbol).unwrap().flags(),
                SymbolFlags::PROPERTY,
                "{source}",
            );
            assert_eq!(
                fixture.commonjs_plan(0),
                Ok(Some(CommonJsAssignmentPlan {
                    expression,
                    left,
                    right,
                    target_symbol,
                })),
                "{source}",
            );
            assert_eq!(observable_state(&fixture.store), before, "{source}");
        }
    }

    #[test]
    fn plans_named_commonjs_exports_without_semantic_writes() {
        for (source, expected_flags) in [
            ("exports.value = 1;", SymbolFlags::FUNCTION_SCOPED_VARIABLE),
            (
                "module.exports.value = 1;",
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            ),
            (
                r#"exports["value"] = 1;"#,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            ),
            (
                r#"module.exports["value"] = 1;"#,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            ),
            (
                r#"exports.value = "hello";"#,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            ),
            (
                r#"module.exports.value = "hello";"#,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            ),
            (
                "exports.value = true;",
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            ),
            (
                "exports.value = false;",
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            ),
            (
                "exports.value = null;",
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            ),
            (
                "exports.value = { nested: 1 };",
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            ),
            (
                "module.exports.value = { nested: 1 };",
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            ),
            (
                "exports.value = [1, 2];",
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            ),
            (
                "const local = 1; exports.value = local;",
                SymbolFlags::ALIAS,
            ),
            (
                "const local = 1; module.exports.value = local;",
                SymbolFlags::ALIAS,
            ),
            (
                r#"const local = 1; exports["value"] = local;"#,
                SymbolFlags::ALIAS,
            ),
        ] {
            let fixture = Fixture::javascript(source);
            let statement = fixture.expression_statement(0);
            let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
            let target_symbol = fixture.bound.symbol(expression).unwrap();
            let before = observable_state(&fixture.store);

            assert_eq!(
                fixture.store.symbol(target_symbol).unwrap().flags(),
                expected_flags,
                "{source}",
            );
            assert_eq!(
                fixture.commonjs_named_plan(0),
                Ok(Some(CommonJsAssignmentPlan {
                    expression,
                    left,
                    right,
                    target_symbol,
                })),
                "{source}",
            );
            assert_eq!(observable_state(&fixture.store), before, "{source}");
        }
    }

    #[test]
    fn named_commonjs_exports_authenticate_repeated_assignments() {
        for (source, expected_flags) in [
            (
                r#"exports.value = 1; exports.value = "text"; exports.value = true;"#,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            ),
            (
                concat!(
                    "exports.value = 1; ",
                    r#"module.exports.value = "text"; "#,
                    "exports.value = true;",
                ),
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            ),
            (
                concat!(
                    r#"exports["value"] = 1; "#,
                    r#"module.exports.value = "text"; "#,
                    r#"module.exports["value"] = true;"#,
                ),
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            ),
            (
                concat!(
                    "const first = 1; const second = 2; ",
                    "exports.value = first; exports.value = second;",
                ),
                SymbolFlags::ALIAS,
            ),
            (
                concat!(
                    "const first = 1; const second = 2; ",
                    "exports.value = first; module.exports.value = second;",
                ),
                SymbolFlags::ALIAS,
            ),
        ] {
            let fixture = Fixture::javascript(source);
            let statements = expression_statements(&fixture.parsed, fixture.file);
            let target = fixture
                .bound
                .symbol(assignment_parts(&fixture.parsed, statements[0]).0)
                .unwrap();
            let record = fixture.store.symbol(target).unwrap();
            assert_eq!(record.flags(), expected_flags, "{source}");
            assert_eq!(record.declarations().unwrap().len(), statements.len());
            let before = observable_state(&fixture.store);

            for (index, statement) in statements.into_iter().enumerate() {
                let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
                assert_eq!(
                    fixture.commonjs_named_plan(index),
                    Ok(Some(CommonJsAssignmentPlan {
                        expression,
                        left,
                        right,
                        target_symbol: target,
                    })),
                    "{source}",
                );
                assert_eq!(observable_state(&fixture.store), before, "{source}");
            }
        }
    }

    #[test]
    fn named_commonjs_exports_leave_other_assignment_families_untouched() {
        let ordinary = Fixture::new("var local: number = 0; local = 1;");
        let before = observable_state(&ordinary.store);
        assert_eq!(ordinary.commonjs_named_plan(0), Ok(None));
        assert_eq!(observable_state(&ordinary.store), before);

        for source in [
            "const local = 1; module.exports = local;",
            "module.exports = {};",
            "const key = 'value'; exports[key] = 1;",
            "const local = { value: 1 }; exports.value = local.value;",
        ] {
            let fixture = Fixture::javascript(source);
            let before = observable_state(&fixture.store);

            assert_eq!(fixture.commonjs_named_plan(0), Ok(None), "{source}");
            assert_eq!(observable_state(&fixture.store), before, "{source}");
        }
    }

    #[test]
    fn named_commonjs_exports_reject_shadowed_exports() {
        for source in [
            "const exports = {}; exports.value = 1;",
            "var exports = {}; exports.value = 1;",
            "function exports() {} exports.value = 1;",
        ] {
            let fixture = Fixture::javascript(source);
            let exports = fixture.source_local("exports");
            let before = observable_state(&fixture.store);

            assert!(matches!(
                fixture.commonjs_named_plan(0),
                Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::ShadowedCommonJsModule { symbol, .. }
                )) if symbol == exports
            ));
            assert_eq!(observable_state(&fixture.store), before, "{source}");
        }
    }

    #[test]
    fn named_commonjs_module_exports_reject_shadowed_module() {
        for source in [
            "const module = {}; module.exports.value = 1;",
            "var module = {}; module.exports.value = 1;",
            "function module() {} module.exports.value = 1;",
        ] {
            let fixture = Fixture::javascript(source);
            let module = fixture.source_local("module");
            let before = observable_state(&fixture.store);

            assert!(matches!(
                fixture.commonjs_named_plan(0),
                Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::ShadowedCommonJsModule { symbol, .. }
                )) if symbol == module
            ));
            assert_eq!(observable_state(&fixture.store), before, "{source}");
        }
    }

    #[test]
    fn named_commonjs_exports_reject_mixed_alias_and_value_declarations() {
        let fixture = Fixture::javascript(concat!(
            "const local = 1; ",
            "exports.value = 1; exports.value = local;",
        ));
        let statement = fixture.expression_statement(0);
        let (expression, _, _) = assignment_parts(&fixture.parsed, statement);
        let target = fixture.bound.symbol(expression).unwrap();
        let before = observable_state(&fixture.store);

        for index in 0..2 {
            assert!(matches!(
                fixture.commonjs_named_plan(index),
                Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::NonVariableTarget { symbol, flags, .. }
                )) if symbol == target
                    && flags == (SymbolFlags::ALIAS | SymbolFlags::FUNCTION_SCOPED_VARIABLE)
            ));
            assert_eq!(observable_state(&fixture.store), before);
        }
    }

    #[test]
    fn named_commonjs_exports_reject_invalid_symbol_provenance_atomically() {
        let mut invalid_flags = Fixture::javascript("exports.value = 1;");
        let statement = invalid_flags.expression_statement(0);
        let (expression, _, _) = assignment_parts(&invalid_flags.parsed, statement);
        let target = invalid_flags.bound.symbol(expression).unwrap();
        assert!(invalid_flags.store.set_symbol_flags(
            target,
            SymbolFlags::PROPERTY,
            CheckFlags::NONE,
        ));
        let before = observable_state(&invalid_flags.store);
        assert!(matches!(
            invalid_flags.commonjs_named_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidSymbolShape(symbol)
            )) if symbol == target
        ));
        assert_eq!(observable_state(&invalid_flags.store), before);

        let mut missing_value = Fixture::javascript("exports.value = 1;");
        let statement = missing_value.expression_statement(0);
        let (expression, _, _) = assignment_parts(&missing_value.parsed, statement);
        let target = missing_value.bound.symbol(expression).unwrap();
        assert!(
            missing_value
                .store
                .set_symbol_declarations(target, Some(vec![expression]), None,)
        );
        let before = observable_state(&missing_value.store);
        assert!(matches!(
            missing_value.commonjs_named_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::ValueDeclarationMismatch { symbol, .. }
            )) if symbol == target
        ));
        assert_eq!(observable_state(&missing_value.store), before);

        let mut missing_parent = Fixture::javascript("exports.value = 1;");
        let statement = missing_parent.expression_statement(0);
        let (expression, _, _) = assignment_parts(&missing_parent.parsed, statement);
        let target = missing_parent.bound.symbol(expression).unwrap();
        assert!(
            missing_parent
                .store
                .set_symbol_relationships(target, None, None, None, None,)
        );
        let before = observable_state(&missing_parent.store);
        assert!(matches!(
            missing_parent.commonjs_named_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidTargetParent { symbol, .. }
            )) if symbol == target
        ));
        assert_eq!(observable_state(&missing_parent.store), before);
    }

    #[test]
    fn named_commonjs_exports_authenticate_implicit_exports_and_receiver_cache() {
        let mut forged_exports = Fixture::javascript("const local = 1; exports.value = 1;");
        let exports = forged_exports.source_local("exports");
        let declaration = forged_exports.variable_declaration("local");
        assert!(forged_exports.store.set_symbol_declarations(
            exports,
            Some(vec![declaration]),
            Some(declaration),
        ));
        let before = observable_state(&forged_exports.store);
        assert!(matches!(
            forged_exports.commonjs_named_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidSymbolShape(symbol)
            )) if symbol == exports
        ));
        assert_eq!(observable_state(&forged_exports.store), before);

        let mut poisoned_cache = Fixture::javascript("const local = 1; exports.value = 1;");
        let statement = poisoned_cache.expression_statement(0);
        let (_, left, _) = assignment_parts(&poisoned_cache.parsed, statement);
        let NodeData::PropertyAccessExpression(access) =
            &poisoned_cache.parsed.arena.get(left.node).unwrap().data
        else {
            panic!("expected exports.value property access")
        };
        let receiver = NodeRef::new(
            poisoned_cache.parsed.arena.id(),
            poisoned_cache.file,
            access.expression,
        );
        let exports = poisoned_cache.source_local("exports");
        let local = poisoned_cache.source_local("local");
        assert!(poisoned_cache.store.set_symbol_node_links(
            receiver,
            SymbolNodeLinks {
                resolved_symbol: Some(local),
            },
        ));
        let before = observable_state(&poisoned_cache.store);
        assert!(matches!(
            poisoned_cache.commonjs_named_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::ResolvedSymbolMismatch {
                    node,
                    expected,
                    actual,
                }
            )) if node == receiver && expected == exports && actual == local
        ));
        assert_eq!(observable_state(&poisoned_cache.store), before);
    }

    #[test]
    fn named_commonjs_module_exports_authenticate_receiver_cache() {
        let mut fixture =
            Fixture::javascript(concat!("const local = 1; ", "module.exports.value = 1;",));
        let statement = fixture.expression_statement(0);
        let (_, left, _) = assignment_parts(&fixture.parsed, statement);
        let NodeData::PropertyAccessExpression(access) =
            &fixture.parsed.arena.get(left.node).unwrap().data
        else {
            panic!("expected module.exports.value property access")
        };
        let receiver = NodeRef::new(fixture.parsed.arena.id(), fixture.file, access.expression);
        let module = fixture.source_local("module");
        let exports = fixture
            .store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| fixture.store.symbol_table(members))
            .and_then(|members| members.get_source("exports"))
            .unwrap();
        let local = fixture.source_local("local");
        assert!(fixture.store.set_symbol_node_links(
            receiver,
            SymbolNodeLinks {
                resolved_symbol: Some(local),
            },
        ));
        let before = observable_state(&fixture.store);

        assert!(matches!(
            fixture.commonjs_named_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::ResolvedSymbolMismatch {
                    node,
                    expected,
                    actual,
                }
            )) if node == receiver && expected == exports && actual == local
        ));
        assert_eq!(observable_state(&fixture.store), before);
    }

    #[test]
    fn commonjs_export_alias_preserves_promoted_type_exports() {
        let mut parsed = parse_source_file(concat!(
            "type Exported = number; ",
            "const local = 1; module.exports = local;",
        ));
        let type_alias = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeAliasDeclaration).then_some(node)
            })
            .unwrap();
        parsed.arena.get_mut(type_alias).unwrap().kind = SyntaxKind::JsTypeAliasDeclaration;
        let fixture = Fixture::javascript_parsed(parsed);
        let statement = fixture.expression_statement(0);
        let (expression, left, right) = assignment_parts(&fixture.parsed, statement);
        let target_symbol = fixture.bound.symbol(expression).unwrap();
        let target = fixture.store.symbol(target_symbol).unwrap();
        assert_eq!(
            target.flags(),
            SymbolFlags::ALIAS | SymbolFlags::NAMESPACE_MODULE
        );
        assert!(
            fixture
                .store
                .symbol_table(target.exports().unwrap())
                .unwrap()
                .get_source("Exported")
                .is_some()
        );
        let before = observable_state(&fixture.store);

        assert_eq!(
            fixture.commonjs_plan(0),
            Ok(Some(CommonJsAssignmentPlan {
                expression,
                left,
                right,
                target_symbol,
            }))
        );
        assert_eq!(observable_state(&fixture.store), before);
    }

    #[test]
    fn commonjs_export_alias_leaves_other_assignment_families_to_source_dispatch() {
        let ordinary = Fixture::new("var local: number = 0; local = 1;");
        let before = observable_state(&ordinary.store);
        assert_eq!(ordinary.commonjs_plan(0), Ok(None));
        assert_eq!(observable_state(&ordinary.store), before);

        for source in [
            "const local = 1; exports.value = local;",
            "const local = 1; module.exports.value = local;",
            r#"const local = 1; module["exports"] = local;"#,
            "const local = 1; module.exports = (local);",
            "const local = { value: 1 }; module.exports = local.value;",
            "const local = 1; module.exports = exports;",
        ] {
            let fixture = Fixture::javascript(source);
            let before = observable_state(&fixture.store);

            assert_eq!(fixture.commonjs_plan(0), Ok(None), "{source}");
            assert_eq!(observable_state(&fixture.store), before, "{source}");
        }
    }

    #[test]
    fn commonjs_export_alias_rejects_shadowed_module_as_unsupported() {
        for source in [
            "const module = {}; const local = 1; module.exports = local;",
            "var module = {}; const local = 1; module.exports = local;",
            "function module() {} const local = 1; module.exports = local;",
        ] {
            let fixture = Fixture::javascript(source);
            let module = fixture.source_local("module");
            let before = observable_state(&fixture.store);

            assert!(matches!(
                fixture.commonjs_plan(0),
                Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::ShadowedCommonJsModule { symbol, .. }
                )) if symbol == module
            ));
            assert_eq!(observable_state(&fixture.store), before, "{source}");
        }
    }

    #[test]
    fn commonjs_export_alias_rejects_duplicate_declarations_as_unsupported() {
        let duplicate_exports = Fixture::javascript(concat!(
            "const local = 1; ",
            "module.exports = local; module.exports = local;",
        ));
        let first = duplicate_exports.expression_statement(0);
        let (expression, _, _) = assignment_parts(&duplicate_exports.parsed, first);
        let target = duplicate_exports.bound.symbol(expression).unwrap();
        let before = observable_state(&duplicate_exports.store);
        for index in 0..2 {
            assert!(matches!(
                duplicate_exports.commonjs_plan(index),
                Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::NonUniqueTarget {
                        symbol,
                        declaration_count: 2,
                        ..
                    }
                )) if symbol == target
            ));
            assert_eq!(observable_state(&duplicate_exports.store), before);
        }

        let mixed_exports = Fixture::javascript(concat!(
            "const local = 1; ",
            "module.exports = local; module.exports = {};",
        ));
        let before = observable_state(&mixed_exports.store);
        assert!(matches!(
            mixed_exports.commonjs_plan(0),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonUniqueTarget {
                    declaration_count: 2,
                    ..
                }
            ))
        ));
        assert_eq!(observable_state(&mixed_exports.store), before);

        let duplicate_local = Fixture::javascript(concat!(
            "var local = 1; var local = 2; ",
            "module.exports = local;",
        ));
        let local = duplicate_local.source_local("local");
        let before = observable_state(&duplicate_local.store);
        assert!(matches!(
            duplicate_local.commonjs_plan(0),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonUniqueTarget {
                    symbol,
                    declaration_count: 2,
                    ..
                }
            )) if symbol == local
        ));
        assert_eq!(observable_state(&duplicate_local.store), before);
    }

    #[test]
    fn commonjs_export_alias_rejects_unsupported_rhs_bindings() {
        let unresolved = Fixture::javascript("module.exports = missing;");
        let before = observable_state(&unresolved.store);
        assert!(matches!(
            unresolved.commonjs_plan(0),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::UnresolvedIdentifier(_)
            ))
        ));
        assert_eq!(observable_state(&unresolved.store), before);

        let alias = Fixture::javascript(concat!(
            r#"const local = require("./dependency"); "#,
            "module.exports = local;",
        ));
        let local = alias.source_local("local");
        let before = observable_state(&alias.store);
        assert!(matches!(
            alias.commonjs_plan(0),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::AliasTarget { symbol, .. }
            )) if symbol == local
        ));
        assert_eq!(observable_state(&alias.store), before);

        let function = Fixture::javascript("function local() {} module.exports = local;");
        let local = function.source_local("local");
        let before = observable_state(&function.store);
        assert!(matches!(
            function.commonjs_plan(0),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonVariableTarget { symbol, .. }
            )) if symbol == local
        ));
        assert_eq!(observable_state(&function.store), before);

        let destructured = Fixture::javascript(concat!(
            "const { local } = { local: 1 }; ",
            "module.exports = local;",
        ));
        let before = observable_state(&destructured.store);
        assert!(matches!(
            destructured.commonjs_plan(0),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::Syntax {
                    kind: SyntaxKind::BindingElement,
                    role: AssignmentSyntaxRole::TargetDeclaration,
                    ..
                }
            ))
        ));
        assert_eq!(observable_state(&destructured.store), before);
    }

    #[test]
    fn commonjs_export_alias_rejects_nested_assignment_as_unsupported() {
        let fixture = Fixture::javascript(concat!(
            "const local = 1; ",
            "function publish() { module.exports = local; }",
        ));
        let statement = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ExpressionStatement
                    && record.parent != Some(fixture.parsed.source_file))
                .then_some(NodeRef::new(fixture.parsed.arena.id(), fixture.file, node))
            })
            .unwrap();
        let before = observable_state(&fixture.store);

        assert_eq!(
            plan_commonjs_assignment(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                statement,
            ),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NestedTarget(statement),
            ))
        );
        assert_eq!(observable_state(&fixture.store), before);
    }

    #[test]
    fn commonjs_export_alias_rejects_invalid_symbol_provenance_atomically() {
        let mut invalid_flags = Fixture::javascript("const local = 1; module.exports = local;");
        let statement = invalid_flags.expression_statement(0);
        let (expression, _, _) = assignment_parts(&invalid_flags.parsed, statement);
        let target = invalid_flags.bound.symbol(expression).unwrap();
        assert!(invalid_flags.store.set_symbol_flags(
            target,
            SymbolFlags::PROPERTY,
            CheckFlags::NONE,
        ));
        let before = observable_state(&invalid_flags.store);
        assert!(matches!(
            invalid_flags.commonjs_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidSymbolShape(symbol)
            )) if symbol == target
        ));
        assert_eq!(observable_state(&invalid_flags.store), before);

        let mut extra_flags = Fixture::javascript("const local = 1; module.exports = local;");
        let statement = extra_flags.expression_statement(0);
        let (expression, _, _) = assignment_parts(&extra_flags.parsed, statement);
        let target = extra_flags.bound.symbol(expression).unwrap();
        assert!(extra_flags.store.set_symbol_flags(
            target,
            SymbolFlags::ALIAS | SymbolFlags::PROPERTY,
            CheckFlags::NONE,
        ));
        let before = observable_state(&extra_flags.store);
        assert!(matches!(
            extra_flags.commonjs_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidSymbolShape(symbol)
            )) if symbol == target
        ));
        assert_eq!(observable_state(&extra_flags.store), before);

        let mut missing_promoted_exports =
            Fixture::javascript("const local = 1; module.exports = local;");
        let statement = missing_promoted_exports.expression_statement(0);
        let (expression, _, _) = assignment_parts(&missing_promoted_exports.parsed, statement);
        let target = missing_promoted_exports.bound.symbol(expression).unwrap();
        assert!(missing_promoted_exports.store.set_symbol_flags(
            target,
            SymbolFlags::ALIAS | SymbolFlags::NAMESPACE_MODULE,
            CheckFlags::NONE,
        ));
        let before = observable_state(&missing_promoted_exports.store);
        assert!(matches!(
            missing_promoted_exports.commonjs_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidSymbolShape(symbol)
            )) if symbol == target
        ));
        assert_eq!(observable_state(&missing_promoted_exports.store), before);

        let mut missing_value = Fixture::javascript("const local = 1; module.exports = local;");
        let statement = missing_value.expression_statement(0);
        let (expression, _, _) = assignment_parts(&missing_value.parsed, statement);
        let target = missing_value.bound.symbol(expression).unwrap();
        assert!(
            missing_value
                .store
                .set_symbol_declarations(target, Some(vec![expression]), None,)
        );
        let before = observable_state(&missing_value.store);
        assert!(matches!(
            missing_value.commonjs_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::ValueDeclarationMismatch { symbol, .. }
            )) if symbol == target
        ));
        assert_eq!(observable_state(&missing_value.store), before);

        let mut missing_parent = Fixture::javascript("const local = 1; module.exports = local;");
        let statement = missing_parent.expression_statement(0);
        let (expression, _, _) = assignment_parts(&missing_parent.parsed, statement);
        let target = missing_parent.bound.symbol(expression).unwrap();
        let record = missing_parent.store.symbol(target).unwrap();
        let (members, exports, export_symbol) =
            (record.members(), record.exports(), record.export_symbol());
        assert!(missing_parent.store.set_symbol_relationships(
            target,
            members,
            exports,
            None,
            export_symbol,
        ));
        let before = observable_state(&missing_parent.store);
        assert!(matches!(
            missing_parent.commonjs_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidTargetParent { symbol, .. }
            )) if symbol == target
        ));
        assert_eq!(observable_state(&missing_parent.store), before);
    }

    #[test]
    fn commonjs_export_alias_authenticates_implicit_module_provenance_atomically() {
        let mut forged_module = Fixture::javascript("const local = 1; module.exports = local;");
        let module = forged_module.source_local("module");
        let declaration = forged_module.variable_declaration("local");
        assert!(forged_module.store.set_symbol_declarations(
            module,
            Some(vec![declaration]),
            Some(declaration),
        ));
        let before = observable_state(&forged_module.store);
        assert!(matches!(
            forged_module.commonjs_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidSymbolShape(symbol)
            )) if symbol == module
        ));
        assert_eq!(observable_state(&forged_module.store), before);

        let mut forged_member = Fixture::javascript("const local = 1; module.exports = local;");
        let module = forged_member.source_local("module");
        let exports = forged_member
            .store
            .symbol(module)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| forged_member.store.symbol_table(members))
            .and_then(|members| members.get_source("exports"))
            .unwrap();
        let declaration = forged_member.variable_declaration("local");
        assert!(forged_member.store.set_symbol_declarations(
            exports,
            Some(vec![declaration]),
            Some(declaration),
        ));
        let before = observable_state(&forged_member.store);
        assert!(matches!(
            forged_member.commonjs_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidSymbolShape(symbol)
            )) if symbol == exports
        ));
        assert_eq!(observable_state(&forged_member.store), before);

        let mut poisoned_receiver = Fixture::javascript("const local = 1; module.exports = local;");
        let statement = poisoned_receiver.expression_statement(0);
        let (_, left, _) = assignment_parts(&poisoned_receiver.parsed, statement);
        let NodeData::PropertyAccessExpression(access) =
            &poisoned_receiver.parsed.arena.get(left.node).unwrap().data
        else {
            panic!("expected module.exports property access")
        };
        let receiver = NodeRef::new(
            poisoned_receiver.parsed.arena.id(),
            poisoned_receiver.file,
            access.expression,
        );
        let module = poisoned_receiver.source_local("module");
        let local = poisoned_receiver.source_local("local");
        assert!(poisoned_receiver.store.set_symbol_node_links(
            receiver,
            SymbolNodeLinks {
                resolved_symbol: Some(local),
            },
        ));
        let before = observable_state(&poisoned_receiver.store);
        assert!(matches!(
            poisoned_receiver.commonjs_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::ResolvedSymbolMismatch {
                    node,
                    expected,
                    actual,
                }
            )) if node == receiver && expected == module && actual == local
        ));
        assert_eq!(observable_state(&poisoned_receiver.store), before);
    }

    #[test]
    fn commonjs_export_alias_authenticates_rhs_local_provenance_atomically() {
        let mut substituted = Fixture::javascript(concat!(
            "const local = 1; const donor = 2; ",
            "module.exports = local;",
        ));
        let locals = substituted
            .bound
            .locals(substituted.bound.source_file())
            .unwrap();
        let local = substituted.source_local("local");
        let donor = substituted.source_local("donor");
        assert_eq!(
            substituted
                .store
                .insert_symbol(locals, EscapedName::source("local"), donor),
            Some(Some(local))
        );
        let before = observable_state(&substituted.store);
        assert!(matches!(
            substituted.commonjs_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::IdentifierNameMismatch { .. }
            ))
        ));
        assert_eq!(observable_state(&substituted.store), before);

        let mut merged = Fixture::javascript("const local = 1; module.exports = local;");
        let raw = merged.source_local("local");
        let declaration = merged.variable_declaration("local");
        let mut data = SymbolData::new(
            SymbolFlags::BLOCK_SCOPED_VARIABLE,
            EscapedName::source("local"),
        );
        data.declarations = Some(vec![declaration]);
        data.value_declaration = Some(declaration);
        let redirected = merged.store.alloc_symbol(data).unwrap();
        merged.store.record_merged_symbol(redirected, raw).unwrap();
        let before = observable_state(&merged.store);
        assert!(matches!(
            merged.commonjs_plan(0),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::MergedTarget { source, target, .. }
            )) if source == raw && target == redirected
        ));
        assert_eq!(observable_state(&merged.store), before);

        let mut parented = Fixture::javascript("const local = 1; module.exports = local;");
        let local = parented.source_local("local");
        let parent = parented.bound.symbol(parented.bound.source_file()).unwrap();
        let record = parented.store.symbol(local).unwrap();
        let (members, exports, export_symbol) =
            (record.members(), record.exports(), record.export_symbol());
        assert!(parented.store.set_symbol_relationships(
            local,
            members,
            exports,
            Some(parent),
            export_symbol,
        ));
        let before = observable_state(&parented.store);
        assert!(matches!(
            parented.commonjs_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidTargetParent {
                    symbol,
                    expected: None,
                    actual: Some(actual),
                }
            )) if symbol == local && actual == parent
        ));
        assert_eq!(observable_state(&parented.store), before);

        let mut poisoned_cache = Fixture::javascript(concat!(
            "const local = 1; const donor = 2; ",
            "module.exports = local;",
        ));
        let statement = poisoned_cache.expression_statement(0);
        let (_, _, reference) = assignment_parts(&poisoned_cache.parsed, statement);
        let local = poisoned_cache.source_local("local");
        let donor = poisoned_cache.source_local("donor");
        assert!(poisoned_cache.store.set_symbol_node_links(
            reference,
            SymbolNodeLinks {
                resolved_symbol: Some(donor),
            },
        ));
        let before = observable_state(&poisoned_cache.store);
        assert!(matches!(
            poisoned_cache.commonjs_plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::ResolvedSymbolMismatch {
                    node,
                    expected,
                    actual,
                }
            )) if node == reference && expected == local && actual == donor
        ));
        assert_eq!(observable_state(&poisoned_cache.store), before);
    }

    #[test]
    fn commonjs_export_alias_rejects_foreign_arena_without_semantic_writes() {
        let fixture = Fixture::javascript("const local = 1; module.exports = local;");
        let foreign = parse_javascript_source_file("const local = 2; module.exports = local;");
        let before = observable_state(&fixture.store);

        assert!(matches!(
            plan_commonjs_assignment(
                &foreign.arena,
                &fixture.bound,
                &fixture.store,
                fixture.expression_statement(0),
            ),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::WrongArena { .. }
            ))
        ));
        assert_eq!(observable_state(&fixture.store), before);
    }

    #[test]
    fn plans_hoisted_and_exported_vars_through_canonical_resolution() {
        let hoisted = Fixture::new("target = 1; var target: number = 0;");
        assert!(hoisted.plan(0).is_ok());

        let exported = Fixture::new("export var target: number = 0; target = 1;");
        let declaration = exported.variable_declaration("target");
        let export = exported.bound.symbol(declaration).unwrap();
        let local = exported.bound.local_symbol(declaration).unwrap();
        assert_ne!(local, export);
        assert_eq!(
            exported.store.symbol(local).unwrap().export_symbol(),
            Some(export)
        );
        assert!(exported.plan(0).is_ok());
    }

    #[test]
    fn resolves_hoisted_script_var_from_production_merged_globals() {
        let file = FileId::new(904);
        let parsed = parse_source_file("target = 1; var target: number = 0;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                source_facts_with_module_state(file, CanonicalModuleState::Script),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let (arena, bound) = context.file(file).unwrap();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(arena, bound)],
            GlobalMergeCompletion::for_test(context.options().name_resolution),
        )
        .unwrap();
        let statement = expression_statements(&parsed, file)[0];
        let before = observable_state(context.store());

        assert!(plan_simple_assignment(arena, bound, context.store(), &host, statement).is_ok());
        assert_eq!(observable_state(context.store()), before);
    }

    #[test]
    fn poisoned_export_routing_fails_closed_without_semantic_writes() {
        let mut aliased = Fixture::new("export var target: number = 0; target = 1;");
        let declaration = aliased.variable_declaration("target");
        let local = aliased.bound.local_symbol(declaration).unwrap();
        assert!(aliased.store.set_symbol_flags(
            local,
            SymbolFlags::EXPORT_VALUE | SymbolFlags::ALIAS,
            CheckFlags::NONE,
        ));
        let before = observable_state(&aliased.store);
        assert!(matches!(
            aliased.plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidExportLocalShape(symbol)
            )) if symbol == local
        ));
        assert_eq!(observable_state(&aliased.store), before);

        let mut unlinked = Fixture::new("export var target: number = 0; target = 1;");
        let declaration = unlinked.variable_declaration("target");
        let local = unlinked.bound.local_symbol(declaration).unwrap();
        assert!(
            unlinked
                .store
                .set_symbol_relationships(local, None, None, None, None)
        );
        assert!(matches!(
            unlinked.plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::MissingExportSymbol(symbol)
            )) if symbol == local
        ));

        let mut bad_parent = Fixture::new("export var target: number = 0; target = 1;");
        let declaration = bad_parent.variable_declaration("target");
        let target = bad_parent.bound.symbol(declaration).unwrap();
        assert!(
            bad_parent
                .store
                .set_symbol_relationships(target, None, None, None, None)
        );
        assert!(matches!(
            bad_parent.plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidTargetParent { symbol, .. }
            )) if symbol == target
        ));
    }

    #[test]
    fn valid_but_unimplemented_target_families_are_typed_unsupported() {
        let unresolved = Fixture::new("missing = 1;");
        assert!(matches!(
            unresolved.plan(0),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::UnresolvedIdentifier(_)
            ))
        ));

        for source in [
            "let target: number = 0; target = 1;",
            "const target: number = 0; target = 1;",
        ] {
            let fixture = Fixture::new(source);
            assert!(matches!(
                fixture.plan(0),
                Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::BlockScopedTarget { .. }
                ))
            ));
        }

        let alias = Fixture::new("import { target } from './dep'; target = 1;");
        assert!(matches!(
            alias.plan(0),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::AliasTarget { .. }
            ))
        ));

        for source in [
            "function target() {} target = 1;",
            "class target {} target = 1;",
        ] {
            let fixture = Fixture::new(source);
            assert!(matches!(
                fixture.plan(0),
                Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::NonVariableTarget { .. }
                ))
            ));
        }
    }

    #[test]
    fn ambient_assignment_capability_requires_exact_mutable_declaration_provenance() {
        for source in [
            "declare var target: number; target = 1;",
            "declare let target: number; target = 1;",
        ] {
            let fixture = Fixture::new(source);
            let declaration = fixture.variable_declaration("target");
            let raw = fixture.bound.symbol(declaration).unwrap();
            let target = fixture.store.get_merged_symbol(raw).unwrap();
            let ambient_targets = HashSet::from([target]);
            let host = fixture.host();
            let before = observable_state(&fixture.store);

            assert!(
                plan_simple_assignment_with_ambient_targets(
                    &fixture.parsed.arena,
                    &fixture.bound,
                    &fixture.store,
                    &host,
                    &ambient_targets,
                    fixture.expression_statement(0),
                )
                .is_ok(),
                "exact mutable ambient target was rejected: {source}",
            );
            assert_eq!(observable_state(&fixture.store), before);
        }

        for source in [
            "var target: number = 0; target = 1;",
            "let target: number = 0; target = 1;",
            "const target: number = 0; target = 1;",
            "declare const target: number; target = 1;",
        ] {
            let fixture = Fixture::new(source);
            let declaration = fixture.variable_declaration("target");
            let raw = fixture.bound.symbol(declaration).unwrap();
            let target = fixture.store.get_merged_symbol(raw).unwrap();
            let ambient_targets = HashSet::from([target]);
            let host = fixture.host();
            let before = observable_state(&fixture.store);

            let result = plan_simple_assignment_with_ambient_targets(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                &host,
                &ambient_targets,
                fixture.expression_statement(0),
            );
            if source.starts_with("declare const") {
                assert!(matches!(
                    result,
                    Err(AssignmentPlanError::Unsupported(
                        AssignmentUnsupported::BlockScopedTarget { symbol, .. }
                    )) if symbol == target
                ));
            } else {
                assert!(
                    result.is_err(),
                    "forged ambient capability bypassed declaration proof: {source}",
                );
            }
            assert_eq!(observable_state(&fixture.store), before);
        }
    }

    #[test]
    fn uninitialized_assignment_capability_requires_exact_mutable_declaration_provenance() {
        for source in [
            "var target: number; target = 1;",
            "let target: number; target = 1;",
        ] {
            let fixture = Fixture::new(source);
            let declaration = fixture.variable_declaration("target");
            let raw = fixture.bound.symbol(declaration).unwrap();
            let target = fixture.store.get_merged_symbol(raw).unwrap();
            let uninitialized_targets = HashSet::from([target]);
            let host = fixture.host();
            let before = observable_state(&fixture.store);

            assert!(
                plan_simple_assignment_with_source_targets(
                    &fixture.parsed.arena,
                    &fixture.bound,
                    &fixture.store,
                    &host,
                    &HashSet::new(),
                    &uninitialized_targets,
                    fixture.expression_statement(0),
                )
                .is_ok(),
                "exact mutable uninitialized target was rejected: {source}",
            );
            assert_eq!(observable_state(&fixture.store), before);
        }

        for source in [
            "var target: number = 0; target = 1;",
            "let target: number = 0; target = 1;",
            "const target: number = 0; target = 1;",
            "declare var target: number; target = 1;",
            "declare let target: number; target = 1;",
            "declare const target: number; target = 1;",
        ] {
            let fixture = Fixture::new(source);
            let declaration = fixture.variable_declaration("target");
            let raw = fixture.bound.symbol(declaration).unwrap();
            let target = fixture.store.get_merged_symbol(raw).unwrap();
            let uninitialized_targets = HashSet::from([target]);
            let host = fixture.host();
            let before = observable_state(&fixture.store);

            assert!(
                plan_simple_assignment_with_source_targets(
                    &fixture.parsed.arena,
                    &fixture.bound,
                    &fixture.store,
                    &host,
                    &HashSet::new(),
                    &uninitialized_targets,
                    fixture.expression_statement(0),
                )
                .is_err(),
                "forged uninitialized capability bypassed declaration proof: {source}",
            );
            assert_eq!(observable_state(&fixture.store), before);
        }

        let fixture = Fixture::new("var target: number; target = 1;");
        let declaration = fixture.variable_declaration("target");
        let raw = fixture.bound.symbol(declaration).unwrap();
        let target = fixture.store.get_merged_symbol(raw).unwrap();
        let targets = HashSet::from([target]);
        let host = fixture.host();
        let before = observable_state(&fixture.store);

        assert!(matches!(
            plan_simple_assignment_with_source_targets(
                &fixture.parsed.arena,
                &fixture.bound,
                &fixture.store,
                &host,
                &targets,
                &targets,
                fixture.expression_statement(0),
            ),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::InvalidSymbolShape(symbol)
            )) if symbol == target
        ));
        assert_eq!(observable_state(&fixture.store), before);
    }

    #[test]
    fn initialized_mutable_assignment_capability_requires_exact_declaration_provenance() {
        for source in [
            "var target: number = 0; target = 1;",
            "let target: number = 0; target = 1;",
            "var target = 0; target = 1;",
            "let target = 0; target = 1;",
        ] {
            let fixture = Fixture::new(source);
            let declaration = fixture.variable_declaration("target");
            let raw = fixture.bound.symbol(declaration).unwrap();
            let target = fixture.store.get_merged_symbol(raw).unwrap();
            let mutable_targets = HashSet::from([target]);
            let host = fixture.host();
            let before = observable_state(&fixture.store);

            assert!(
                plan_simple_assignment_with_all_source_targets(
                    &fixture.parsed.arena,
                    &fixture.bound,
                    &fixture.store,
                    &host,
                    &HashSet::new(),
                    &HashSet::new(),
                    &mutable_targets,
                    fixture.expression_statement(0),
                )
                .is_ok(),
                "exact mutable target was rejected: {source}",
            );
            assert_eq!(observable_state(&fixture.store), before);
        }

        for source in [
            "const target: number = 0; target = 1;",
            "var target: number; target = 1;",
            "declare var target: number; target = 1;",
        ] {
            let fixture = Fixture::new(source);
            let declaration = fixture.variable_declaration("target");
            let raw = fixture.bound.symbol(declaration).unwrap();
            let target = fixture.store.get_merged_symbol(raw).unwrap();
            let mutable_targets = HashSet::from([target]);
            let host = fixture.host();
            let before = observable_state(&fixture.store);

            assert!(
                plan_simple_assignment_with_all_source_targets(
                    &fixture.parsed.arena,
                    &fixture.bound,
                    &fixture.store,
                    &host,
                    &HashSet::new(),
                    &HashSet::new(),
                    &mutable_targets,
                    fixture.expression_statement(0),
                )
                .is_err(),
                "forged mutable capability bypassed declaration proof: {source}",
            );
            assert_eq!(observable_state(&fixture.store), before);
        }
    }

    #[test]
    fn deferred_source_families_are_capability_boundaries_from_resolver_construction() {
        let fixture = Fixture::new("var target: number = 0; target = 1;");
        let (_, left, _) = assignment_parts(&fixture.parsed, fixture.expression_statement(0));

        for error in [
            CanonicalNameResolutionError::JavaScriptDeferred(fixture.file),
            CanonicalNameResolutionError::CommonJsDeferred(fixture.file),
            CanonicalNameResolutionError::JsDocDeferred(left),
        ] {
            assert!(matches!(
                AssignmentPlanner::name_resolution_error(left, error),
                AssignmentPlanError::Unsupported(AssignmentUnsupported::ResolverDeferred {
                    node,
                    error: actual,
                }) if node == left && actual == error
            ));
        }
    }

    #[test]
    fn inferred_uninitialized_and_non_identifier_targets_are_unsupported() {
        let inferred = Fixture::new("var target = 0; target = 1;");
        assert!(matches!(
            inferred.plan(0),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::MissingTargetType(_)
            ))
        ));

        let uninitialized = Fixture::new("var target: number; target = 1;");
        assert!(matches!(
            uninitialized.plan(0),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::MissingTargetInitializer(_)
            ))
        ));

        for source in [
            "var target: { p: number } = { p: 0 }; target.p = 1;",
            "var target: number[] = []; target[0] = 1;",
            "var target: number = 0; [target] = [1];",
        ] {
            let fixture = Fixture::new(source);
            assert!(matches!(
                fixture.plan(0),
                Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::Syntax {
                        role: AssignmentSyntaxRole::LeftHandSide,
                        ..
                    }
                ))
            ));
        }
    }

    #[test]
    fn compound_assignments_preserve_the_authenticated_operator() {
        for (source, operator) in [
            (
                "var target: number = 0; target += 1;",
                SyntaxKind::PlusEqualsToken,
            ),
            (
                "var target: number = 0; target -= 1;",
                SyntaxKind::MinusEqualsToken,
            ),
            (
                "var target: number = 0; target <<= 1;",
                SyntaxKind::LessThanLessThanEqualsToken,
            ),
        ] {
            let fixture = Fixture::new(source);
            let before = observable_state(&fixture.store);

            assert_eq!(fixture.plan(0).unwrap().operator, operator);
            assert_eq!(observable_state(&fixture.store), before);
        }
    }

    #[test]
    fn chained_and_logical_compound_assignments_remain_unsupported() {
        let logical = Fixture::new("var target: number = 0; target ||= 1;");
        assert!(matches!(
            logical.plan(0),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::Syntax {
                    role: AssignmentSyntaxRole::Operator,
                    ..
                }
            ))
        ));

        let chained =
            Fixture::new("var first: number = 0; var second: number = 0; first = second = 1;");
        assert!(matches!(
            chained.plan(0),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::ChainedAssignment(_)
            ))
        ));
    }

    #[test]
    fn wrong_arena_and_poisoned_value_declaration_are_invariants() {
        let mut fixture = Fixture::new("var target: number = 0; target = 1;");
        let foreign = parse_source_file("foreign = 1;");
        let host = fixture.host();
        assert!(matches!(
            plan_simple_assignment(
                &foreign.arena,
                &fixture.bound,
                &fixture.store,
                &host,
                fixture.expression_statement(0),
            ),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::WrongArena { .. }
            ))
        ));
        drop(host);

        let declaration = fixture.variable_declaration("target");
        let symbol = fixture.bound.symbol(declaration).unwrap();
        assert!(
            fixture
                .store
                .set_symbol_declarations(symbol, Some(vec![declaration]), None,)
        );
        let before = observable_state(&fixture.store);
        assert!(matches!(
            fixture.plan(0),
            Err(AssignmentPlanError::Invariant(
                AssignmentInvariant::ValueDeclarationMismatch { .. }
            ))
        ));
        assert_eq!(observable_state(&fixture.store), before);
    }

    #[test]
    fn merged_target_is_an_explicit_capability_boundary() {
        let mut fixture = Fixture::new("var target: number = 0; target = 1;");
        let declaration = fixture.variable_declaration("target");
        let raw = fixture.bound.symbol(declaration).unwrap();
        let mut data = SymbolData::new(
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            EscapedName::source("target"),
        );
        data.declarations = Some(vec![declaration]);
        data.value_declaration = Some(declaration);
        let merged = fixture.store.alloc_symbol(data).unwrap();
        fixture.store.record_merged_symbol(merged, raw).unwrap();
        let before = observable_state(&fixture.store);

        assert!(matches!(
            fixture.plan(0),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::MergedTarget {
                    source,
                    target,
                    ..
                }
            )) if source == raw && target == merged
        ));
        assert_eq!(observable_state(&fixture.store), before);
    }

    #[test]
    fn cross_file_target_is_an_explicit_capability_boundary() {
        let first_file = FileId::new(902);
        let second_file = FileId::new(903);
        let first = parse_source_file("var target: number = 0; target = 1;");
        let second = parse_source_file("var donor: number = 0;");
        let mut binder = CanonicalBinder::new();
        for (file, parsed) in [(first_file, &first), (second_file, &second)] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    source_facts(file),
                )
                .unwrap();
        }
        for (file, parsed) in [(first_file, &first), (second_file, &second)] {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        for (file, parsed) in [(first_file, &first), (second_file, &second)] {
            assert!(
                store
                    .register_source_file(&parsed.arena, parsed.source_file, file)
                    .is_some()
            );
        }
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let first_bound = &files[&first_file];
        let target_declaration = variable_declaration(&first, first_file, "target");
        let donor_declaration = variable_declaration(&second, second_file, "donor");
        let target = first_bound.symbol(target_declaration).unwrap();
        assert!(store.set_symbol_declarations(
            target,
            Some(vec![donor_declaration]),
            Some(donor_declaration),
        ));
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&first.arena, &files[&first_file]),
                (&second.arena, &files[&second_file]),
            ],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap();
        let statement = expression_statements(&first, first_file)[0];

        assert!(matches!(
            plan_simple_assignment(
                &first.arena,
                first_bound,
                &store,
                &host,
                statement,
            ),
            Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::CrossFileTarget { declaration, .. }
            )) if declaration == donor_declaration
        ));
    }
}
