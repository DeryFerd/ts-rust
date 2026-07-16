//! Planning for exact annotated arrow values in direct `const` declarations.
//!
//! This adapter deliberately proves only an unannotated, non-exported, top-level
//! declaration of the form `const name = (parameters): Return => body`. The
//! variable keeps its ordinary block-scoped symbol while the arrow is owned by
//! the binder's distinct anonymous FUNCTION symbol. Signature publication is
//! delegated to `source_callables`; body checking and publication of the
//! variable symbol's eventual `resolvedType` remain deferred to source dispatch.

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{InternalSymbolName, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost,
    array_types::CanonicalArrayTargets,
    bootstrap::LiteralTypeCacheError,
    declared::preflight_node,
    source_callables::{
        SourceCallableError, SourceCallableFamily, SourceCallableInvariant, SourceCallablePlan,
        SourceCallableUnsupported, plan_source_callable,
    },
    variables::{
        VariableBindingKind, VariableInvariant, VariablePlanError, VariableUnsupported,
        plan_top_level_variable,
    },
};

const NODE_FLAG_CONST: u32 = 1 << 1;

/// The bounded body shapes whose semantics can be added without replanning the
/// declaration or callable identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceArrowBodyPlan {
    EmptyBlock {
        block: NodeRef,
    },
    ReturnExpression {
        block: NodeRef,
        statement: NodeRef,
        expression: NodeRef,
    },
    ConciseExpression {
        expression: NodeRef,
    },
}

/// Immutable syntax/binder proof retained by future source dispatch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceArrowPlan {
    pub(super) variable_declaration: NodeRef,
    pub(super) variable_name: NodeRef,
    pub(super) variable_symbol: SemanticSymbolId,
    pub(super) callable: SourceCallablePlan,
    pub(super) body: SourceArrowBodyPlan,
}

/// Valid TypeScript source shapes intentionally deferred beyond this direct,
/// noncontextual arrow cut.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceArrowUnsupported {
    NonConstDeclaration(NodeRef),
    NonSingleDeclaration(NodeRef),
    NestedDeclaration(NodeRef),
    ModifiedOrExportedDeclaration(NodeRef),
    NonIdentifierName(NodeRef),
    VariableAnnotation(NodeRef),
    MissingInitializer(NodeRef),
    NonArrowInitializer(NodeRef),
    ComplexBlock(NodeRef),
    BareReturn(NodeRef),
    Variable(VariableUnsupported),
    Callable(SourceCallableUnsupported),
}

/// Malformed AST, binder provenance, or a violated identity invariant.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceArrowInvariant {
    InvalidVariableDeclaration(NodeRef),
    InvalidDeclarationList(NodeRef),
    InvalidVariableStatement(NodeRef),
    InvalidSourceFile(NodeRef),
    InvalidVariableName(NodeRef),
    InvalidVariableType(NodeRef),
    InvalidInitializer(NodeRef),
    InvalidOwnerSymbol(NodeRef),
    InvalidBody(NodeRef),
    Variable(VariableInvariant),
    Callable(SourceCallableInvariant),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceArrowError {
    Unsupported(SourceArrowUnsupported),
    Invariant(SourceArrowInvariant),
    DeclaredType(DeclaredTypeError),
    LiteralCache(LiteralTypeCacheError),
}

impl SourceArrowError {
    pub(super) const fn node(self) -> Option<NodeRef> {
        match self {
            Self::Unsupported(reason) => match reason {
                SourceArrowUnsupported::NonConstDeclaration(node)
                | SourceArrowUnsupported::NonSingleDeclaration(node)
                | SourceArrowUnsupported::NestedDeclaration(node)
                | SourceArrowUnsupported::ModifiedOrExportedDeclaration(node)
                | SourceArrowUnsupported::NonIdentifierName(node)
                | SourceArrowUnsupported::VariableAnnotation(node)
                | SourceArrowUnsupported::MissingInitializer(node)
                | SourceArrowUnsupported::NonArrowInitializer(node)
                | SourceArrowUnsupported::ComplexBlock(node)
                | SourceArrowUnsupported::BareReturn(node) => Some(node),
                SourceArrowUnsupported::Variable(_) => None,
                SourceArrowUnsupported::Callable(reason) => {
                    SourceCallableError::Unsupported(reason).node()
                }
            },
            Self::Invariant(reason) => match reason {
                SourceArrowInvariant::InvalidVariableDeclaration(node)
                | SourceArrowInvariant::InvalidDeclarationList(node)
                | SourceArrowInvariant::InvalidVariableStatement(node)
                | SourceArrowInvariant::InvalidSourceFile(node)
                | SourceArrowInvariant::InvalidVariableName(node)
                | SourceArrowInvariant::InvalidVariableType(node)
                | SourceArrowInvariant::InvalidInitializer(node)
                | SourceArrowInvariant::InvalidOwnerSymbol(node)
                | SourceArrowInvariant::InvalidBody(node) => Some(node),
                SourceArrowInvariant::Variable(_) => None,
                SourceArrowInvariant::Callable(reason) => {
                    SourceCallableError::Invariant(reason).node()
                }
            },
            Self::DeclaredType(_) | Self::LiteralCache(_) => None,
        }
    }
}

impl From<DeclaredTypeError> for SourceArrowError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<LiteralTypeCacheError> for SourceArrowError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::LiteralCache(error)
    }
}

/// Proves one direct annotated arrow without mutating semantic state.
pub(super) fn plan_source_arrow(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    variable_declaration: NodeRef,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceArrowPlan, SourceArrowError> {
    let declaration_record = preflight_node(store, host, variable_declaration)?;
    let NodeData::VariableDeclaration(declaration) = &declaration_record.data else {
        return Err(unsupported(SourceArrowUnsupported::NonConstDeclaration(
            variable_declaration,
        )));
    };
    if declaration_record.kind != SyntaxKind::VariableDeclaration
        || declaration_record.flags.0 != 0
        || declaration.exclamation_token.is_some()
        || declaration.local_symbol.is_some()
        || declaration.symbol.is_some()
        || declaration.facts != 0
    {
        return Err(invariant(SourceArrowInvariant::InvalidVariableDeclaration(
            variable_declaration,
        )));
    }

    let Some(list_id) = declaration_record.parent else {
        return Err(unsupported(SourceArrowUnsupported::NestedDeclaration(
            variable_declaration,
        )));
    };
    let list = NodeRef::new(
        variable_declaration.arena,
        variable_declaration.file,
        list_id,
    );
    let list_record = preflight_node(store, host, list)?;
    let NodeData::VariableDeclarationList(list_data) = &list_record.data else {
        return Err(unsupported(SourceArrowUnsupported::NestedDeclaration(
            variable_declaration,
        )));
    };
    if list_record.kind != SyntaxKind::VariableDeclarationList
        || !range_contains(list_record.range, declaration_record.range)
        || list_data.declarations.range != list_record.range
        || list_data.declarations.has_trailing_comma
        || list_data.facts != 0
    {
        return Err(invariant(SourceArrowInvariant::InvalidDeclarationList(
            list,
        )));
    }
    if list_record.flags.0 != NODE_FLAG_CONST {
        return Err(unsupported(SourceArrowUnsupported::NonConstDeclaration(
            list,
        )));
    }
    if list_data.declarations.nodes.len() != 1 {
        return Err(unsupported(SourceArrowUnsupported::NonSingleDeclaration(
            list,
        )));
    }
    if list_data.declarations.nodes[0] != variable_declaration.node {
        return Err(invariant(SourceArrowInvariant::InvalidDeclarationList(
            list,
        )));
    }

    let Some(statement_id) = list_record.parent else {
        return Err(unsupported(SourceArrowUnsupported::NestedDeclaration(list)));
    };
    let statement = NodeRef::new(
        variable_declaration.arena,
        variable_declaration.file,
        statement_id,
    );
    let statement_record = preflight_node(store, host, statement)?;
    let NodeData::VariableStatement(statement_data) = &statement_record.data else {
        return Err(unsupported(SourceArrowUnsupported::NestedDeclaration(list)));
    };
    if statement_record.kind != SyntaxKind::VariableStatement
        || statement_data.declaration_list != list.node
        || statement_record.flags.0 != 0
        || statement_data.flow_node.is_some()
        || statement_data.facts != 0
        || !range_contains(statement_record.range, list_record.range)
    {
        return Err(invariant(SourceArrowInvariant::InvalidVariableStatement(
            statement,
        )));
    }
    if statement_data.modifiers.is_some() {
        return Err(unsupported(
            SourceArrowUnsupported::ModifiedOrExportedDeclaration(statement),
        ));
    }

    let bound = host
        .bound_file(variable_declaration)
        .ok_or_else(|| invariant(SourceArrowInvariant::InvalidSourceFile(statement)))?;
    let source = bound.source_file();
    if statement_record.parent != Some(source.node) {
        return Err(unsupported(SourceArrowUnsupported::NestedDeclaration(
            statement,
        )));
    }
    let source_record = preflight_node(store, host, source)?;
    let NodeData::SourceFile(source_data) = &source_record.data else {
        return Err(invariant(SourceArrowInvariant::InvalidSourceFile(source)));
    };
    if source_record.kind != SyntaxKind::SourceFile
        || !range_contains(source_record.range, statement_record.range)
        || source_data
            .statements
            .nodes
            .iter()
            .filter(|node| **node == statement.node)
            .count()
            != 1
    {
        return Err(invariant(SourceArrowInvariant::InvalidSourceFile(source)));
    }

    let variable_name = NodeRef::new(
        variable_declaration.arena,
        variable_declaration.file,
        declaration.name,
    );
    let name_record = preflight_node(store, host, variable_name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(SourceArrowUnsupported::NonIdentifierName(
            variable_name,
        )));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(variable_declaration.node)
        || name_record.flags.0 != 0
        || identifier.flow_node.is_some()
        || !range_contains(declaration_record.range, name_record.range)
    {
        return Err(invariant(SourceArrowInvariant::InvalidVariableName(
            variable_name,
        )));
    }

    if let Some(type_id) = declaration.type_ {
        let type_node = NodeRef::new(
            variable_declaration.arena,
            variable_declaration.file,
            type_id,
        );
        let type_record = preflight_node(store, host, type_node)?;
        if type_record.parent != Some(variable_declaration.node)
            || !range_contains(declaration_record.range, type_record.range)
            || type_record.range.start < name_record.range.end
        {
            return Err(invariant(SourceArrowInvariant::InvalidVariableType(
                type_node,
            )));
        }
        return Err(unsupported(SourceArrowUnsupported::VariableAnnotation(
            type_node,
        )));
    }

    let Some(initializer_id) = declaration.initializer else {
        return Err(unsupported(SourceArrowUnsupported::MissingInitializer(
            variable_declaration,
        )));
    };
    let initializer = NodeRef::new(
        variable_declaration.arena,
        variable_declaration.file,
        initializer_id,
    );
    let initializer_record = preflight_node(store, host, initializer)?;
    if initializer_record.parent != Some(variable_declaration.node)
        || !range_contains(declaration_record.range, initializer_record.range)
        || initializer_record.range.start < name_record.range.end
    {
        return Err(invariant(SourceArrowInvariant::InvalidInitializer(
            initializer,
        )));
    }
    if initializer_record.kind != SyntaxKind::ArrowFunction
        || !matches!(initializer_record.data, NodeData::ArrowFunction(_))
    {
        return Err(unsupported(SourceArrowUnsupported::NonArrowInitializer(
            initializer,
        )));
    }

    let variable_symbol = plan_top_level_variable(
        bound,
        store,
        variable_declaration,
        variable_name,
        &identifier.text,
        VariableBindingKind::Const,
        false,
    )
    .map_err(map_variable_error)?;
    let owner_symbol = bound
        .symbol(initializer)
        .ok_or_else(|| invariant(SourceArrowInvariant::InvalidOwnerSymbol(initializer)))?;
    if owner_symbol == variable_symbol
        || store.symbol(owner_symbol).is_some_and(|symbol| {
            symbol.flags() != SymbolFlags::FUNCTION
                || symbol.name() != InternalSymbolName::Function.as_ref()
        })
    {
        return Err(invariant(SourceArrowInvariant::InvalidOwnerSymbol(
            initializer,
        )));
    }

    let callable = plan_source_callable(store, host, initializer, owner_symbol, array_targets)
        .map_err(map_callable_error)?;
    if callable.family != SourceCallableFamily::ArrowFunction
        || callable.declaration != initializer
        || callable.owner_symbol != owner_symbol
    {
        return Err(invariant(SourceArrowInvariant::InvalidOwnerSymbol(
            initializer,
        )));
    }
    let body = plan_body(store, host, &callable)?;
    Ok(SourceArrowPlan {
        variable_declaration,
        variable_name,
        variable_symbol,
        callable,
        body,
    })
}

fn plan_body(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    callable: &SourceCallablePlan,
) -> Result<SourceArrowBodyPlan, SourceArrowError> {
    let body = callable.body;
    let body_record = preflight_node(store, host, body)?;
    if body_record.parent != Some(callable.declaration.node) {
        return Err(invariant(SourceArrowInvariant::InvalidBody(body)));
    }
    if body_record.kind != SyntaxKind::Block {
        if !is_concise_expression(body_record.kind) {
            return Err(invariant(SourceArrowInvariant::InvalidBody(body)));
        }
        return Ok(SourceArrowBodyPlan::ConciseExpression { expression: body });
    }

    let NodeData::Block(block) = &body_record.data else {
        return Err(invariant(SourceArrowInvariant::InvalidBody(body)));
    };
    if body_record.flags.0 != 0
        || block.flow_node.is_some()
        || block.next_container.is_some()
        || block.statements.has_trailing_comma
        || block.facts != 0
    {
        return Err(invariant(SourceArrowInvariant::InvalidBody(body)));
    }
    match block.statements.nodes.as_slice() {
        [] => Ok(SourceArrowBodyPlan::EmptyBlock { block: body }),
        [statement_id] => {
            let statement = NodeRef::new(body.arena, body.file, *statement_id);
            let statement_record = preflight_node(store, host, statement)?;
            if statement_record.parent != Some(body.node)
                || !range_contains(body_record.range, statement_record.range)
            {
                return Err(invariant(SourceArrowInvariant::InvalidBody(statement)));
            }
            let NodeData::ReturnStatement(return_statement) = &statement_record.data else {
                return Err(unsupported(SourceArrowUnsupported::ComplexBlock(body)));
            };
            if statement_record.kind != SyntaxKind::ReturnStatement
                || statement_record.flags.0 != 0
                || return_statement.flow_node.is_some()
                || return_statement.facts != 0
            {
                return Err(invariant(SourceArrowInvariant::InvalidBody(statement)));
            }
            let Some(expression_id) = return_statement.expression else {
                return Err(unsupported(SourceArrowUnsupported::BareReturn(statement)));
            };
            let expression = NodeRef::new(body.arena, body.file, expression_id);
            let expression_record = preflight_node(store, host, expression)?;
            if expression_record.parent != Some(statement.node)
                || !range_contains(statement_record.range, expression_record.range)
                || !is_concise_expression(expression_record.kind)
            {
                return Err(invariant(SourceArrowInvariant::InvalidBody(expression)));
            }
            Ok(SourceArrowBodyPlan::ReturnExpression {
                block: body,
                statement,
                expression,
            })
        }
        _ => Err(unsupported(SourceArrowUnsupported::ComplexBlock(body))),
    }
}

fn is_concise_expression(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Identifier
            | SyntaxKind::NumericLiteral
            | SyntaxKind::BigIntLiteral
            | SyntaxKind::StringLiteral
            | SyntaxKind::RegularExpressionLiteral
            | SyntaxKind::NoSubstitutionTemplateLiteral
            | SyntaxKind::FalseKeyword
            | SyntaxKind::NullKeyword
            | SyntaxKind::SuperKeyword
            | SyntaxKind::ThisKeyword
            | SyntaxKind::TrueKeyword
            | SyntaxKind::ArrayLiteralExpression
            | SyntaxKind::ObjectLiteralExpression
            | SyntaxKind::PropertyAccessExpression
            | SyntaxKind::ElementAccessExpression
            | SyntaxKind::CallExpression
            | SyntaxKind::NewExpression
            | SyntaxKind::TaggedTemplateExpression
            | SyntaxKind::TypeAssertionExpression
            | SyntaxKind::ParenthesizedExpression
            | SyntaxKind::FunctionExpression
            | SyntaxKind::ArrowFunction
            | SyntaxKind::DeleteExpression
            | SyntaxKind::TypeOfExpression
            | SyntaxKind::VoidExpression
            | SyntaxKind::AwaitExpression
            | SyntaxKind::PrefixUnaryExpression
            | SyntaxKind::PostfixUnaryExpression
            | SyntaxKind::BinaryExpression
            | SyntaxKind::ConditionalExpression
            | SyntaxKind::TemplateExpression
            | SyntaxKind::YieldExpression
            | SyntaxKind::ClassExpression
            | SyntaxKind::AsExpression
            | SyntaxKind::NonNullExpression
            | SyntaxKind::MetaProperty
            | SyntaxKind::SatisfiesExpression
            | SyntaxKind::JsxElement
            | SyntaxKind::JsxSelfClosingElement
            | SyntaxKind::JsxFragment
    )
}

fn range_contains(parent: ts_core::TextRange, child: ts_core::TextRange) -> bool {
    child.start >= parent.start && child.end <= parent.end
}

fn map_variable_error(error: VariablePlanError) -> SourceArrowError {
    match error {
        VariablePlanError::Unsupported(reason) => {
            unsupported(SourceArrowUnsupported::Variable(reason))
        }
        VariablePlanError::Invariant(reason) => invariant(SourceArrowInvariant::Variable(reason)),
        VariablePlanError::DeclaredType(error) => SourceArrowError::DeclaredType(error),
    }
}

fn map_callable_error(error: SourceCallableError) -> SourceArrowError {
    match error {
        SourceCallableError::Unsupported(reason) => {
            unsupported(SourceArrowUnsupported::Callable(reason))
        }
        SourceCallableError::Invariant(reason) => invariant(SourceArrowInvariant::Callable(reason)),
        SourceCallableError::DeclaredType(error) => SourceArrowError::DeclaredType(error),
        SourceCallableError::LiteralCache(error) => SourceArrowError::LiteralCache(error),
    }
}

const fn unsupported(reason: SourceArrowUnsupported) -> SourceArrowError {
    SourceArrowError::Unsupported(reason)
}

const fn invariant(reason: SourceArrowInvariant) -> SourceArrowError {
    SourceArrowError::Invariant(reason)
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions,
        production::GlobalMergeCompletion,
        source_callables::{SourceCallableState, source_callable_state},
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
            let file = FileId::new(913);
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/source_arrows.ts\""),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::External,
                    ),
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

        fn declarations(&self) -> Vec<NodeRef> {
            variable_declarations(&self.parsed, self.file)
        }

        fn plan(&self, index: usize) -> Result<SourceArrowPlan, SourceArrowError> {
            let host = self.host();
            plan_source_arrow(&self.store, &host, self.declarations()[index], None)
        }
    }

    fn variable_declarations(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
        let source = parsed.arena.get(parsed.source_file).unwrap();
        let NodeData::SourceFile(source) = &source.data else {
            panic!("expected source file")
        };
        let mut declarations = Vec::new();
        for statement_id in &source.statements.nodes {
            let statement = parsed.arena.get(*statement_id).unwrap();
            let NodeData::VariableStatement(statement) = &statement.data else {
                continue;
            };
            let list = parsed.arena.get(statement.declaration_list).unwrap();
            let NodeData::VariableDeclarationList(list) = &list.data else {
                panic!("expected variable declaration list")
            };
            declarations.extend(
                list.declarations
                    .nodes
                    .iter()
                    .map(|node| NodeRef::new(parsed.arena.id(), file, *node)),
            );
        }
        declarations
    }

    #[test]
    fn direct_arrow_retains_distinct_variable_and_anonymous_callable_identity() {
        let fixture = Fixture::new("const f = (x: number): string => \"ok\";");
        let plan = fixture.plan(0).unwrap();

        assert_ne!(plan.variable_symbol, plan.callable.owner_symbol);
        assert_eq!(
            fixture.bound.symbol(plan.variable_declaration),
            Some(plan.variable_symbol)
        );
        assert_eq!(
            fixture.bound.symbol(plan.callable.declaration),
            Some(plan.callable.owner_symbol)
        );
        assert_eq!(
            fixture
                .store
                .symbol(plan.variable_symbol)
                .unwrap()
                .name()
                .as_utf8(),
            Some("f")
        );
        assert_eq!(
            fixture
                .store
                .symbol(plan.callable.owner_symbol)
                .unwrap()
                .name(),
            InternalSymbolName::Function.as_ref()
        );
        assert_eq!(plan.callable.family, SourceCallableFamily::ArrowFunction);
        assert_eq!(plan.callable.parameters.len(), 1);
        assert_eq!(plan.callable.min_argument_count, 1);
        assert!(!plan.callable.parameters[0].optional);
        assert_eq!(
            fixture
                .parsed
                .arena
                .get(plan.callable.return_type.node)
                .unwrap()
                .kind,
            SyntaxKind::StringKeyword
        );
        assert!(matches!(
            plan.body,
            SourceArrowBodyPlan::ConciseExpression { expression }
                if fixture.parsed.arena.get(expression.node).unwrap().kind
                    == SyntaxKind::StringLiteral
        ));
        assert_eq!(
            source_callable_state(&fixture.store, &plan.callable, true).unwrap(),
            SourceCallableState::Cold
        );
    }

    #[test]
    fn required_then_optional_parameters_have_exact_arity() {
        let fixture =
            Fixture::new("const f = (required: string, optional?: number): boolean => true;");
        let plan = fixture.plan(0).unwrap();

        assert_eq!(plan.callable.parameters.len(), 2);
        assert_eq!(plan.callable.min_argument_count, 1);
        assert!(!plan.callable.parameters[0].optional);
        assert!(plan.callable.parameters[1].optional);
        assert_ne!(
            plan.callable.parameters[0].symbol,
            plan.callable.parameters[1].symbol
        );
    }

    #[test]
    fn classifies_only_the_three_bounded_body_shapes() {
        let fixture = Fixture::new(
            r#"
                const empty = (): void => {};
                const returned = (): string => { return "ok"; };
                const concise = (): number => 1;
            "#,
        );
        let empty = fixture.plan(0).unwrap();
        let returned = fixture.plan(1).unwrap();
        let concise = fixture.plan(2).unwrap();

        assert!(matches!(
            empty.body,
            SourceArrowBodyPlan::EmptyBlock { block } if block == empty.callable.body
        ));
        assert!(matches!(
            returned.body,
            SourceArrowBodyPlan::ReturnExpression {
                block,
                statement: _,
                expression,
            } if block == returned.callable.body
                && fixture.parsed.arena.get(expression.node).unwrap().kind
                    == SyntaxKind::StringLiteral
        ));
        assert!(matches!(
            concise.body,
            SourceArrowBodyPlan::ConciseExpression { expression }
                if expression == concise.callable.body
                    && fixture.parsed.arena.get(expression.node).unwrap().kind
                        == SyntaxKind::NumericLiteral
        ));
    }

    #[test]
    fn rejects_contextual_or_non_direct_variable_shapes() {
        let annotated =
            Fixture::new("const f: (x: number) => string = (x: number): string => \"ok\";");
        assert!(matches!(
            annotated.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::VariableAnnotation(_)
            ))
        ));

        let mutable = Fixture::new("let f = (x: number): string => \"ok\";");
        assert!(matches!(
            mutable.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::NonConstDeclaration(_)
            ))
        ));

        let siblings =
            Fixture::new("const f = (x: number): number => x, g = (x: number): number => x;");
        assert!(matches!(
            siblings.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::NonSingleDeclaration(_)
            ))
        ));

        let exported = Fixture::new("export const f = (x: number): string => \"ok\";");
        assert!(matches!(
            exported.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::ModifiedOrExportedDeclaration(_)
            ))
        ));

        let wrapped = Fixture::new("const f = ((x: number): string => \"ok\");");
        assert!(matches!(
            wrapped.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::NonArrowInitializer(_)
            ))
        ));
    }

    #[test]
    fn rejects_unbounded_block_bodies_without_claiming_corruption() {
        let complex = Fixture::new("const f = (): void => { 1; };");
        assert!(matches!(
            complex.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::ComplexBlock(_)
            ))
        ));

        let bare = Fixture::new("const f = (): void => { return; };");
        assert!(matches!(
            bare.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::BareReturn(_)
            ))
        ));
    }

    #[test]
    fn preserves_shared_callable_unsupported_reasons() {
        let generic = Fixture::new("const f = <T>(x: T): T => x;");
        assert!(matches!(
            generic.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::Callable(SourceCallableUnsupported::GenericSignature(_))
            ))
        ));

        let missing_parameter_type = Fixture::new("const f = (x): number => x;");
        assert!(matches!(
            missing_parameter_type.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::Callable(SourceCallableUnsupported::MissingParameterType(
                    _
                ))
            ))
        ));

        let missing_return_type = Fixture::new("const f = (x: number) => x;");
        assert!(matches!(
            missing_return_type.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::Callable(SourceCallableUnsupported::MissingReturnType(_))
            ))
        ));

        let initialized = Fixture::new("const f = (x: number = 0): number => x;");
        assert!(matches!(
            initialized.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::Callable(SourceCallableUnsupported::InitializedParameter(
                    _
                ))
            ))
        ));

        let predicate = Fixture::new("const f = (x: unknown): x is string => true;");
        assert!(matches!(
            predicate.plan(0),
            Err(SourceArrowError::Unsupported(
                SourceArrowUnsupported::Callable(SourceCallableUnsupported::TypePredicate(_))
            ))
        ));
    }
}
