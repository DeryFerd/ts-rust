//! Pinned `.types` baseline selection and node filtering.

use ts_ast::{Node, NodeArena, NodeData, NodeFlags, NodeId, SyntaxKind};

use super::declaration_name;

pub(crate) const EXTENSION: &str = ".types";

pub(crate) fn baseline_base(file_name: &str) -> Option<&str> {
    file_name.strip_suffix(EXTENSION)
}

pub(super) fn includes(
    arena: &NodeArena,
    node_id: NodeId,
    node: &Node,
    parent: Option<&Node>,
) -> bool {
    if node.kind == SyntaxKind::OmittedExpression || is_part_of_type_node(arena, node_id, node) {
        return false;
    }

    if matches!(
        node.kind,
        SyntaxKind::AsExpression | SyntaxKind::SatisfiesExpression
    ) {
        let type_node = match &node.data {
            NodeData::AsExpression(expression) => Some(expression.type_),
            NodeData::SatisfiesExpression(expression) => Some(expression.type_),
            _ => None,
        };
        if type_node
            .and_then(|type_node| arena.get(type_node))
            .is_some_and(|type_node| type_node.flags.0 & NodeFlags::REPARSED.0 != 0)
        {
            return false;
        }
    }

    if node.kind != SyntaxKind::Identifier {
        return true;
    }
    let Some(parent) = parent else {
        return true;
    };
    if matches!(
        parent.kind,
        SyntaxKind::TypeAliasDeclaration | SyntaxKind::JsTypeAliasDeclaration
    ) && declaration_name(parent) == Some(node_id)
    {
        return true;
    }

    !matches!(
        parent.kind,
        SyntaxKind::TypeParameter
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::TypeAliasDeclaration
            | SyntaxKind::JsTypeAliasDeclaration
            | SyntaxKind::TypeLiteral
    )
}

pub(super) fn is_part_of_type_node(arena: &NodeArena, node_id: NodeId, node: &Node) -> bool {
    let kind = node.kind as u16;
    if kind >= SyntaxKind::FIRST_TYPE_NODE as u16 && kind <= SyntaxKind::LAST_TYPE_NODE as u16 {
        return true;
    }

    match node.kind {
        SyntaxKind::AnyKeyword
        | SyntaxKind::UnknownKeyword
        | SyntaxKind::NumberKeyword
        | SyntaxKind::BigIntKeyword
        | SyntaxKind::StringKeyword
        | SyntaxKind::BooleanKeyword
        | SyntaxKind::SymbolKeyword
        | SyntaxKind::ObjectKeyword
        | SyntaxKind::UndefinedKeyword
        | SyntaxKind::NullKeyword
        | SyntaxKind::NeverKeyword => true,
        SyntaxKind::VoidKeyword => node
            .parent
            .and_then(|parent| arena.get(parent))
            .is_none_or(|parent| parent.kind != SyntaxKind::VoidExpression),
        SyntaxKind::ExpressionWithTypeArguments => is_type_heritage_expression(arena, node),
        SyntaxKind::TypeParameter => node
            .parent
            .and_then(|parent| arena.get(parent))
            .is_some_and(|parent| {
                matches!(parent.kind, SyntaxKind::MappedType | SyntaxKind::InferType)
            }),
        SyntaxKind::Identifier => {
            let Some(parent) = node.parent.and_then(|parent| arena.get(parent)) else {
                return false;
            };
            if matches!(&parent.data, NodeData::QualifiedName(name) if name.right == node_id)
                || matches!(&parent.data, NodeData::PropertyAccessExpression(access) if access.name == node_id)
            {
                let Some(parent_id) = node.parent else {
                    return false;
                };
                return is_part_of_type_node_in_parent(arena, parent_id, parent);
            }
            is_part_of_type_node_in_parent(arena, node_id, node)
        }
        SyntaxKind::QualifiedName
        | SyntaxKind::PropertyAccessExpression
        | SyntaxKind::ThisKeyword => is_part_of_type_node_in_parent(arena, node_id, node),
        _ => false,
    }
}

fn is_part_of_type_node_in_parent(arena: &NodeArena, node_id: NodeId, node: &Node) -> bool {
    let Some(parent) = node.parent.and_then(|parent| arena.get(parent)) else {
        return false;
    };
    if parent.kind == SyntaxKind::TypeQuery {
        return false;
    }
    if let NodeData::ImportTypeNode(import) = &parent.data {
        return !import.is_type_of;
    }
    let parent_kind = parent.kind as u16;
    if parent_kind >= SyntaxKind::FIRST_TYPE_NODE as u16
        && parent_kind <= SyntaxKind::LAST_TYPE_NODE as u16
    {
        return true;
    }
    if parent.kind == SyntaxKind::ExpressionWithTypeArguments {
        return is_type_heritage_expression(arena, parent);
    }

    match &parent.data {
        NodeData::TypeParameterDeclaration(parameter) => parameter.constraint == Some(node_id),
        NodeData::VariableDeclaration(declaration) => declaration.type_ == Some(node_id),
        NodeData::ParameterDeclaration(declaration) => declaration.type_ == Some(node_id),
        NodeData::PropertyDeclaration(declaration) => declaration.type_ == Some(node_id),
        NodeData::PropertySignatureDeclaration(declaration) => declaration.type_ == node_id,
        NodeData::FunctionDeclaration(declaration) => declaration.type_ == Some(node_id),
        NodeData::FunctionExpression(declaration) => declaration.type_ == Some(node_id),
        NodeData::ArrowFunction(declaration) => declaration.type_ == Some(node_id),
        NodeData::MethodDeclaration(declaration) => declaration.type_ == Some(node_id),
        NodeData::MethodSignatureDeclaration(declaration) => declaration.type_ == Some(node_id),
        NodeData::GetAccessorDeclaration(declaration) => declaration.type_ == Some(node_id),
        NodeData::SetAccessorDeclaration(declaration) => declaration.type_ == Some(node_id),
        NodeData::CallSignatureDeclaration(declaration) => declaration.type_ == Some(node_id),
        NodeData::ConstructSignatureDeclaration(declaration) => declaration.type_ == Some(node_id),
        NodeData::IndexSignatureDeclaration(declaration) => declaration.type_ == node_id,
        NodeData::TypeAssertion(assertion) => assertion.type_ == node_id,
        NodeData::CallExpression(call) => call
            .type_arguments
            .as_ref()
            .is_some_and(|arguments| arguments.nodes.contains(&node_id)),
        NodeData::NewExpression(call) => call
            .type_arguments
            .as_ref()
            .is_some_and(|arguments| arguments.nodes.contains(&node_id)),
        NodeData::TaggedTemplateExpression(call) => call
            .type_arguments
            .as_ref()
            .is_some_and(|arguments| arguments.nodes.contains(&node_id)),
        _ => false,
    }
}

fn is_type_heritage_expression(arena: &NodeArena, node: &Node) -> bool {
    let Some(parent) = node.parent.and_then(|parent| arena.get(parent)) else {
        return false;
    };
    if let NodeData::HeritageClause(heritage) = &parent.data {
        return parent
            .parent
            .and_then(|owner| arena.get(owner))
            .is_none_or(|owner| {
                !matches!(
                    owner.kind,
                    SyntaxKind::ClassDeclaration | SyntaxKind::ClassExpression
                ) || heritage.token == SyntaxKind::ImplementsKeyword
            });
    }
    matches!(
        parent.kind,
        SyntaxKind::JsDocImplementsTag | SyntaxKind::JsDocAugmentsTag
    )
}

#[cfg(test)]
mod tests {
    use super::baseline_base;

    #[test]
    fn recognizes_configured_type_baselines_without_accepting_diffs() {
        assert_eq!(baseline_base("case.types"), Some("case"));
        assert_eq!(
            baseline_base("case(target=esnext).types"),
            Some("case(target=esnext)")
        );
        assert_eq!(baseline_base("case.types.diff"), None);
    }
}
