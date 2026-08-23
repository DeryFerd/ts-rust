//! Read-only planning for the first assignment-expression source slice.
//!
//! The installed slice is deliberately narrow: a top-level expression statement
//! containing `identifier = expression`, where the identifier resolves to one
//! unique, same-file, explicitly typed and initialized ordinary `var` declaration.
//! Source planning may additionally supply exact capabilities for mutable ambient
//! declarations or admitted annotated uninitialized variables. Those
//! routes independently revalidate their direct `var`/`let` AST and binder shape
//! before admission.
//! A separate `CommonJS` route admits only binder-authenticated
//! `module.exports = local` assignments in JavaScript modules.
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

use super::{CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost};

const NODE_FLAG_LET: u32 = 1 << 0;
const NODE_FLAG_CONST: u32 = 1 << 1;

/// The source nodes needed by assignment contextual typing and execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SimpleAssignmentPlan {
    pub expression: NodeRef,
    pub left: NodeRef,
    pub right: NodeRef,
    pub target_symbol: SemanticSymbolId,
    pub target_type_node: Option<NodeRef>,
}

/// One binder-authenticated `module.exports = local` assignment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CommonJsAssignmentPlan {
    pub(super) expression: NodeRef,
    pub(super) left: NodeRef,
    pub(super) right: NodeRef,
    pub(super) target_symbol: SemanticSymbolId,
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
        let NodeData::Identifier(local_name) = &right_node.data else {
            return Ok(None);
        };
        if right_node.flags.0 != 0 || local_name.flow_node.is_some() {
            return Err(AssignmentInvariant::InvalidIdentifierShape(right).into());
        }

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

        self.validate_export_alias(expression, left, source_symbol, target_symbol)?;
        self.validate_implicit_module(receiver, source_symbol)?;
        self.validate_local_identifier(right, &local_name.text)?;

        Ok(Some(CommonJsAssignmentPlan {
            expression,
            left,
            right,
            target_symbol,
        }))
    }

    fn validate_export_alias(
        &self,
        expression: NodeRef,
        left: NodeRef,
        source_symbol: SemanticSymbolId,
        target_symbol: SemanticSymbolId,
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
        let expected_flags = if promoted_type_exports {
            SymbolFlags::ALIAS | SymbolFlags::NAMESPACE_MODULE
        } else {
            SymbolFlags::ALIAS
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
    fn plan(&self, statement: NodeRef) -> Result<SimpleAssignmentPlan, AssignmentPlanError> {
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
        if operator_node.kind != SyntaxKind::EqualsToken {
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
            SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
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
        } else if javascript_target.is_none() && mutable_target.is_none() {
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
        if variable.initializer.is_some() {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::NonOrdinaryVariable(declaration),
            ));
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
            "const local = 1; module.exports = { value: local };",
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
    fn compound_and_chained_assignments_are_unsupported() {
        let compound = Fixture::new("var target: number = 0; target += 1;");
        assert!(matches!(
            compound.plan(0),
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
