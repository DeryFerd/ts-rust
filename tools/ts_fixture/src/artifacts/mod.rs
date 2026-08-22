//! Ordered AST walks for the pinned type and symbol baseline generator.

use std::{error::Error, fmt};

use ts_ast::{Node, NodeArena, NodeData, NodeFlags, NodeId, NodeRef, SyntaxKind};
use ts_compiler::{Program, SourceFile};

use crate::{Case, virtual_unit_path};

pub(crate) mod symbols;
pub(crate) mod types;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SemanticArtifactKind {
    Types,
    Symbols,
}

impl SemanticArtifactKind {
    pub(crate) const fn extension(self) -> &'static str {
        match self {
            Self::Types => types::EXTENSION,
            Self::Symbols => symbols::EXTENSION,
        }
    }

    pub(crate) const fn unavailable_detail(self) -> &'static str {
        match self {
            Self::Types => types::UNAVAILABLE_DETAIL,
            Self::Symbols => symbols::UNAVAILABLE_DETAIL,
        }
    }

    pub(crate) fn baseline_base(self, file_name: &str) -> Option<&str> {
        match self {
            Self::Types => types::baseline_base(file_name),
            Self::Symbols => symbols::baseline_base(file_name),
        }
    }
}

/// Nodes visited by each pinned baseline walk, grouped in fixture-file order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct SemanticArtifactWalk {
    pub(crate) types: Vec<NodeRef>,
    pub(crate) symbols: Vec<NodeRef>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ArtifactWalkError {
    MissingNode {
        file_name: String,
        node: NodeId,
    },
    MissingParent {
        file_name: String,
        node: NodeId,
        parent: NodeId,
    },
    ForeignNode {
        file_name: String,
        node: NodeId,
    },
}

impl fmt::Display for ArtifactWalkError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingNode { file_name, node } => {
                write!(
                    formatter,
                    "semantic artifact walk cannot resolve {node:?} in '{file_name}'"
                )
            }
            Self::MissingParent {
                file_name,
                node,
                parent,
            } => write!(
                formatter,
                "semantic artifact node {node:?} in '{file_name}' has invalid parent {parent:?}"
            ),
            Self::ForeignNode { file_name, node } => write!(
                formatter,
                "semantic artifact node {node:?} does not belong to Program source '{file_name}'"
            ),
        }
    }
}

impl Error for ArtifactWalkError {}

pub(crate) fn walk_program(
    case: &Case,
    program: &Program,
) -> Result<SemanticArtifactWalk, ArtifactWalkError> {
    let mut result = SemanticArtifactWalk::default();
    for (index, unit) in case.units.iter().enumerate() {
        let file_name = virtual_unit_path(case, unit, index);
        let Some(source) = program.source_file(&file_name) else {
            continue;
        };
        walk_source(source, SemanticArtifactKind::Types, &mut result.types)?;
        walk_source(source, SemanticArtifactKind::Symbols, &mut result.symbols)?;
    }
    Ok(result)
}

fn walk_source(
    source: &SourceFile,
    artifact: SemanticArtifactKind,
    results: &mut Vec<NodeRef>,
) -> Result<(), ArtifactWalkError> {
    let arena = &source.parse.arena;
    let mut pending = vec![source.parse.source_file];
    let mut children = Vec::new();

    while let Some(node_id) = pending.pop() {
        let node = node(source, node_id)?;
        let parent = node
            .parent
            .map(|parent| parent_node(source, node_id, parent))
            .transpose()?;
        if !should_traverse_reparsed(node_id, node, parent) {
            continue;
        }

        if should_include_reparsed(node, parent)
            && is_artifact_candidate(arena, node_id, node, parent)
            && match artifact {
                SemanticArtifactKind::Types => types::includes(arena, node_id, node, parent),
                SemanticArtifactKind::Symbols => symbols::includes(node),
            }
        {
            let reference =
                source
                    .node_ref(node_id)
                    .ok_or_else(|| ArtifactWalkError::ForeignNode {
                        file_name: source.file_name.clone(),
                        node: node_id,
                    })?;
            results.push(reference);
        }

        children.clear();
        node.for_each_child(|child| children.push(child));
        pending.extend(children.iter().rev().copied());
    }

    Ok(())
}

fn node(source: &SourceFile, node_id: NodeId) -> Result<&Node, ArtifactWalkError> {
    source
        .parse
        .arena
        .get(node_id)
        .ok_or_else(|| ArtifactWalkError::MissingNode {
            file_name: source.file_name.clone(),
            node: node_id,
        })
}

fn parent_node(
    source: &SourceFile,
    node_id: NodeId,
    parent: NodeId,
) -> Result<&Node, ArtifactWalkError> {
    source
        .parse
        .arena
        .get(parent)
        .ok_or_else(|| ArtifactWalkError::MissingParent {
            file_name: source.file_name.clone(),
            node: node_id,
            parent,
        })
}

fn should_traverse_reparsed(node_id: NodeId, node: &Node, parent: Option<&Node>) -> bool {
    if node.flags.0 & NodeFlags::REPARSED.0 == 0
        || matches!(
            node.kind,
            SyntaxKind::AsExpression | SyntaxKind::SatisfiesExpression
        )
    {
        return true;
    }

    parent.is_some_and(|parent| match &parent.data {
        NodeData::AsExpression(expression) => expression.expression == node_id,
        NodeData::SatisfiesExpression(expression) => expression.expression == node_id,
        _ => false,
    })
}

fn should_include_reparsed(node: &Node, parent: Option<&Node>) -> bool {
    node.flags.0 & NodeFlags::REPARSED.0 == 0
        || parent.is_some_and(|parent| {
            matches!(
                parent.kind,
                SyntaxKind::AsExpression | SyntaxKind::SatisfiesExpression
            )
        })
}

pub(super) fn is_artifact_candidate(
    arena: &NodeArena,
    node_id: NodeId,
    node: &Node,
    parent: Option<&Node>,
) -> bool {
    node.kind == SyntaxKind::Identifier
        || is_expression_node(arena, node_id, node, parent)
        || parent.is_some_and(|parent| declaration_name(parent) == Some(node_id))
}

fn is_expression_node(
    arena: &NodeArena,
    node_id: NodeId,
    node: &Node,
    parent: Option<&Node>,
) -> bool {
    match node.kind {
        SyntaxKind::SuperKeyword
        | SyntaxKind::NullKeyword
        | SyntaxKind::TrueKeyword
        | SyntaxKind::FalseKeyword
        | SyntaxKind::RegularExpressionLiteral
        | SyntaxKind::ArrayLiteralExpression
        | SyntaxKind::ObjectLiteralExpression
        | SyntaxKind::PropertyAccessExpression
        | SyntaxKind::ElementAccessExpression
        | SyntaxKind::CallExpression
        | SyntaxKind::NewExpression
        | SyntaxKind::TaggedTemplateExpression
        | SyntaxKind::AsExpression
        | SyntaxKind::TypeAssertionExpression
        | SyntaxKind::SatisfiesExpression
        | SyntaxKind::NonNullExpression
        | SyntaxKind::ParenthesizedExpression
        | SyntaxKind::FunctionExpression
        | SyntaxKind::ClassExpression
        | SyntaxKind::ArrowFunction
        | SyntaxKind::VoidExpression
        | SyntaxKind::DeleteExpression
        | SyntaxKind::TypeOfExpression
        | SyntaxKind::PrefixUnaryExpression
        | SyntaxKind::PostfixUnaryExpression
        | SyntaxKind::BinaryExpression
        | SyntaxKind::ConditionalExpression
        | SyntaxKind::SpreadElement
        | SyntaxKind::TemplateExpression
        | SyntaxKind::OmittedExpression
        | SyntaxKind::JsxElement
        | SyntaxKind::JsxSelfClosingElement
        | SyntaxKind::JsxFragment
        | SyntaxKind::YieldExpression
        | SyntaxKind::AwaitExpression => true,
        SyntaxKind::ExpressionWithTypeArguments => {
            parent.is_none_or(|parent| parent.kind != SyntaxKind::HeritageClause)
        }
        SyntaxKind::MetaProperty => parent.is_none_or(|parent| {
            !matches!(&parent.data, NodeData::CallExpression(call) if call.expression == node_id)
        }),
        SyntaxKind::PrivateIdentifier => parent.is_some_and(|parent| {
            matches!(
                &parent.data,
                NodeData::BinaryExpression(binary)
                    if binary.left == node_id
                        && arena
                            .get(binary.operator_token)
                            .is_some_and(|operator| operator.kind == SyntaxKind::InKeyword)
            )
        }),
        SyntaxKind::QualifiedName => is_qualified_expression(arena, node_id, parent),
        SyntaxKind::Identifier => {
            parent.is_some_and(|parent| parent.kind == SyntaxKind::TypeQuery)
                || is_jsx_tag(node_id, parent)
                || parent.is_some_and(|parent| in_expression_context(arena, node_id, parent))
        }
        SyntaxKind::NumericLiteral
        | SyntaxKind::BigIntLiteral
        | SyntaxKind::StringLiteral
        | SyntaxKind::NoSubstitutionTemplateLiteral
        | SyntaxKind::ThisKeyword => {
            parent.is_some_and(|parent| in_expression_context(arena, node_id, parent))
        }
        _ => false,
    }
}

fn is_qualified_expression<'arena>(
    arena: &'arena NodeArena,
    mut node_id: NodeId,
    mut parent: Option<&'arena Node>,
) -> bool {
    while let Some(current_parent) = parent {
        if current_parent.kind != SyntaxKind::QualifiedName {
            return current_parent.kind == SyntaxKind::TypeQuery
                || is_jsx_tag(node_id, Some(current_parent));
        }
        let Some(parent_id) = current_parent.parent else {
            return false;
        };
        node_id = parent_id;
        parent = arena.get(parent_id);
    }
    false
}

fn is_jsx_tag(node_id: NodeId, parent: Option<&Node>) -> bool {
    parent.is_some_and(|parent| match &parent.data {
        NodeData::JsxOpeningElement(element) => element.tag_name == node_id,
        NodeData::JsxClosingElement(element) => element.tag_name == node_id,
        NodeData::JsxSelfClosingElement(element) => element.tag_name == node_id,
        _ => false,
    })
}

fn in_expression_context(arena: &NodeArena, node_id: NodeId, parent: &Node) -> bool {
    match &parent.data {
        NodeData::VariableDeclaration(data) => data.initializer == Some(node_id),
        NodeData::ParameterDeclaration(data) => data.initializer == Some(node_id),
        NodeData::PropertyDeclaration(data) => data.initializer == Some(node_id),
        NodeData::PropertySignatureDeclaration(data) => data.initializer == node_id,
        NodeData::EnumMember(data) => data.initializer == Some(node_id),
        NodeData::PropertyAssignment(data) => data.initializer == node_id,
        NodeData::BindingElement(data) => data.initializer == Some(node_id),
        NodeData::ExpressionStatement(data) => data.expression == node_id,
        NodeData::IfStatement(data) => data.expression == node_id,
        NodeData::DoStatement(data) => data.expression == node_id,
        NodeData::WhileStatement(data) => data.expression == node_id,
        NodeData::ReturnStatement(data) => data.expression == Some(node_id),
        NodeData::WithStatement(data) => data.expression == node_id,
        NodeData::SwitchStatement(data) => data.expression == node_id,
        NodeData::ThrowStatement(data) => data.expression == node_id,
        NodeData::TypeAssertion(data) => data.expression == node_id,
        NodeData::AsExpression(data) => data.expression == node_id,
        NodeData::SatisfiesExpression(data) => data.expression == node_id,
        NodeData::TemplateSpan(data) => data.expression == node_id,
        NodeData::ComputedPropertyName(data) => data.expression == node_id,
        NodeData::ForStatement(data) => {
            data.condition == Some(node_id)
                || data.incrementor == Some(node_id)
                || (data.initializer == Some(node_id)
                    && arena
                        .get(node_id)
                        .is_some_and(|node| node.kind != SyntaxKind::VariableDeclarationList))
        }
        NodeData::ForInOrOfStatement(data) => {
            data.expression == node_id
                || (data.initializer == node_id
                    && arena
                        .get(node_id)
                        .is_some_and(|node| node.kind != SyntaxKind::VariableDeclarationList))
        }
        NodeData::Decorator(_)
        | NodeData::JsxExpression(_)
        | NodeData::JsxSpreadAttribute(_)
        | NodeData::SpreadAssignment(_) => true,
        NodeData::ExpressionWithTypeArguments(data) => {
            data.expression == node_id && !types::is_part_of_type_node(arena, node_id, parent)
        }
        NodeData::ShorthandPropertyAssignment(data) => {
            data.object_assignment_initializer == Some(node_id)
        }
        _ => parent
            .parent
            .and_then(|parent_id| arena.get(parent_id))
            .is_some_and(|grandparent| {
                is_expression_node(arena, node_id, parent, Some(grandparent))
            }),
    }
}

pub(super) fn declaration_name(parent: &Node) -> Option<NodeId> {
    match &parent.data {
        NodeData::BindingElement(data) => data.name,
        NodeData::ClassDeclaration(data) => data.name,
        NodeData::ClassExpression(data) => data.name,
        NodeData::EnumDeclaration(data) => Some(data.name),
        NodeData::EnumMember(data) => Some(data.name),
        NodeData::ExportSpecifier(data) => Some(data.name),
        NodeData::FunctionDeclaration(data) => data.name,
        NodeData::FunctionExpression(data) => data.name,
        NodeData::GetAccessorDeclaration(data) => Some(data.name),
        NodeData::ImportClause(data) => data.name,
        NodeData::ImportEqualsDeclaration(data) => Some(data.name),
        NodeData::ImportSpecifier(data) => Some(data.name),
        NodeData::InterfaceDeclaration(data) => Some(data.name),
        NodeData::JsxAttribute(data) => Some(data.name),
        NodeData::MethodDeclaration(data) => Some(data.name),
        NodeData::MethodSignatureDeclaration(data) => Some(data.name),
        NodeData::ModuleDeclaration(data) => Some(data.name),
        NodeData::NamedTupleMember(data) => Some(data.name),
        NodeData::NamespaceExport(data) => Some(data.name),
        NodeData::NamespaceExportDeclaration(data) => Some(data.name),
        NodeData::NamespaceImport(data) => Some(data.name),
        NodeData::ParameterDeclaration(data) => Some(data.name),
        NodeData::PropertyAssignment(data) => Some(data.name),
        NodeData::PropertyDeclaration(data) => Some(data.name),
        NodeData::PropertySignatureDeclaration(data) => Some(data.name),
        NodeData::SetAccessorDeclaration(data) => Some(data.name),
        NodeData::ShorthandPropertyAssignment(data) => Some(data.name),
        NodeData::TypeAliasDeclaration(data) => Some(data.name),
        NodeData::TypeParameterDeclaration(data) => Some(data.name),
        NodeData::VariableDeclaration(data) => Some(data.name),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use ts_ast::{NodeData, SyntaxKind};
    use ts_compiler::Program;
    use ts_options::CompilerOptions;
    use ts_vfs::{FileSystem, MemoryFileSystem};

    use crate::Case;

    use super::walk_program;

    #[test]
    fn walks_type_and_symbol_candidates_in_source_child_order() {
        let source = "type Alias = string;\nconst value: Alias = 'ok';\n";
        let case = Case::parse("input.ts", source).unwrap();
        let filesystem = MemoryFileSystem::new(true);
        filesystem.write_file("/.src/input.ts", source).unwrap();
        let options = CompilerOptions {
            no_lib: true,
            ..CompilerOptions::default()
        };
        let program = Program::new_with_options(
            &filesystem,
            "/.src",
            &["/.src/input.ts".to_owned()],
            options,
        );

        let walk = walk_program(&case, &program).unwrap();
        let source_file = program.source_file("/.src/input.ts").unwrap();
        let descriptions = |nodes: &[ts_ast::NodeRef]| {
            nodes
                .iter()
                .map(|reference| {
                    let node = source_file.parse.arena.get(reference.node).unwrap();
                    match &node.data {
                        NodeData::Identifier(identifier) => identifier.text.clone(),
                        NodeData::StringLiteral(literal) => format!("'{}'", literal.text),
                        _ => node.kind.as_str().to_owned(),
                    }
                })
                .collect::<Vec<_>>()
        };

        assert_eq!(descriptions(&walk.types), ["Alias", "value", "'ok'"]);
        assert_eq!(
            descriptions(&walk.symbols),
            ["Alias", "value", "Alias", "'ok'"]
        );
        assert!(walk.types.iter().all(|reference| {
            source_file
                .parse
                .arena
                .get(reference.node)
                .is_some_and(|node| node.kind != SyntaxKind::StringKeyword)
        }));
    }
}
