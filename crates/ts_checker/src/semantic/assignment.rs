//! Read-only planning for the first assignment-expression source slice.
//!
//! The installed slice is deliberately narrow: a top-level expression statement
//! containing `identifier = expression`, where the identifier resolves to one
//! unique, same-file, explicitly typed and initialized ordinary `var` declaration.
//! Source planning may additionally supply exact capabilities for mutable ambient
//! declarations or admitted annotated uninitialized variables. Those
//! routes independently revalidate their direct `var`/`let` AST and binder shape
//! before admission.
//! Name lookup follows the pinned lexical resolver and checker export/merge routing.
//! Valid syntax outside that closure is a typed unsupported result; malformed AST,
//! binder, or semantic-store provenance is an invariant failure.

use std::collections::HashSet;

use ts_ast::{
    FileId, Node, NodeArena, NodeArenaId, NodeArenaRevision, NodeData, NodeRef, SyntaxKind,
};
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation,
    CheckFlags, SemanticSymbolId, SymbolFlags,
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
    pub target_type_node: NodeRef,
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
    AssignmentPlanner {
        arena,
        bound,
        store,
        host,
        ambient_targets,
        uninitialized_targets,
    }
    .plan(statement)
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
        if ambient_target && uninitialized_target {
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
        {
            return Err(AssignmentPlanError::Unsupported(
                AssignmentUnsupported::BlockScopedTarget {
                    node: left,
                    symbol: target,
                },
            ));
        }
        if (!ambient_target
            && !uninitialized_target
            && flags != SymbolFlags::FUNCTION_SCOPED_VARIABLE)
            || ((ambient_target || uninitialized_target)
                && flags != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                && flags != SymbolFlags::BLOCK_SCOPED_VARIABLE)
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

    fn validate_variable_declaration(
        &self,
        left: NodeRef,
        declaration: NodeRef,
        reference_name: &str,
        ambient_target: Option<(SemanticSymbolId, SymbolFlags)>,
        uninitialized_target: Option<(SemanticSymbolId, SymbolFlags)>,
    ) -> Result<NodeRef, AssignmentPlanError> {
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

        let type_node = variable.type_.map(|node| self.reference(node)).ok_or(
            AssignmentPlanError::Unsupported(AssignmentUnsupported::MissingTargetType(declaration)),
        )?;
        self.require_parent(type_node, Some(declaration.node))?;
        self.node(type_node)?;
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
            (None, Some(_)) => {}
            (None, None) => {
                return Err(AssignmentPlanError::Unsupported(
                    AssignmentUnsupported::MissingTargetInitializer(declaration),
                ));
            }
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
        let expected_list_flags = match uninitialized_target {
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
                    symbol: uninitialized_target.map_or_else(
                        || {
                            self.bound
                                .symbol(declaration)
                                .ok_or(AssignmentInvariant::MissingDeclarationSymbol(declaration))
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
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
        production::GlobalMergeCompletion,
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
                target_type_node: variable_type(&fixture.parsed, declaration),
            })
        );
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
