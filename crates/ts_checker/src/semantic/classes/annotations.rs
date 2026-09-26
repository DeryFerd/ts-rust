//! Class annotation queries retain the real owner while its members are checked.

use super::{
    CanonicalArrayTargets, CanonicalGlobalTypes, CanonicalTypeMapperStore, CheckFlags, ClassError,
    ClassHeritageMembersValidation, ClassInvariant, ClassPropertySide, ClassTypeQueryContext,
    DeclaredTypeHost, NodeData, NodeRef, ObjectFlags, SemanticSymbolId, SourceClassPlan,
    StructuredTypeData, SymbolFlags, SyntaxKind, TypeData, TypeId, TypeRecord, ValueSymbolLinks,
    bound_symbol, class_member_modifiers, class_property_modifiers, exact_class_instance_identity,
    invariant, preflight_class_or_interface_reference, preflight_source_class_annotation,
    source_class_binding, source_class_plan_is_current, source_class_type_owner_declaration,
    source_class_type_parameter_plans, validate_class_heritage_members,
    validate_direct_generic_reference, validate_source_class_header,
    validate_source_class_stored_header,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::semantic) struct SourceClassAnnotationScope {
    plan: SourceClassPlan,
    instance: TypeId,
    targets: CanonicalArrayTargets,
}

/// Each expanded annotation keeps its actual class declaration role.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::semantic) enum SourceClassAnnotationRole {
    TypeParameterConstraint {
        parameter: NodeRef,
    },
    TypeParameterDefault {
        parameter: NodeRef,
    },
    Field {
        declaration: NodeRef,
    },
    ConstructorParameter {
        constructor: NodeRef,
        parameter: NodeRef,
    },
    MethodParameter {
        method: NodeRef,
        parameter: NodeRef,
    },
    MethodReturn {
        method: NodeRef,
    },
    HeritageArgument {
        heritage: NodeRef,
        index: usize,
    },
}

fn source_annotation_instance_member(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    declaration: NodeRef,
    member: NodeRef,
) -> Result<bool, ClassError> {
    let invalid = || invariant(ClassInvariant::InvalidPropertySymbol(member));
    let class_record = super::preflight_node(store, host, declaration)?;
    let NodeData::ClassDeclaration(class) = &class_record.data else {
        return Err(invalid());
    };
    let record = super::preflight_node(store, host, member)?;
    if record.parent != Some(declaration.node) {
        return Ok(false);
    }
    if record.flags.0 != 0
        || class
            .members
            .nodes
            .iter()
            .filter(|&&node| node == member.node)
            .count()
            != 1
    {
        return Err(invalid());
    }
    let (name, modifiers, flags) = match &record.data {
        NodeData::PropertyDeclaration(data) => {
            (data.name, data.modifiers.as_ref(), SymbolFlags::PROPERTY)
        }
        NodeData::MethodDeclaration(data) if data.type_parameters.is_none() => {
            (data.name, data.modifiers.as_ref(), SymbolFlags::METHOD)
        }
        NodeData::ConstructorDeclaration(data) if data.type_parameters.is_none() => {
            let symbol = bound_symbol(store, host, member).ok_or_else(invalid)?;
            let record = store.symbol(symbol).ok_or_else(invalid)?;
            if record.flags() != SymbolFlags::CONSTRUCTOR
                || record.parent() != Some(owner)
                || !record
                    .declarations()
                    .is_some_and(|declarations| declarations.contains(&member))
                || record.value_declaration().is_some()
                || store.get_merged_symbol(symbol) != Some(symbol)
                || store
                    .symbol(owner)
                    .and_then(|owner| owner.members())
                    .and_then(|members| store.symbol_table(members))
                    .and_then(|members| members.get(record.name()))
                    != Some(symbol)
            {
                return Err(invalid());
            }
            return Ok(true);
        }
        _ => return Ok(false),
    };
    let (side, _) = class_member_modifiers(
        store,
        host,
        member,
        NodeRef::new(member.arena, member.file, name),
        modifiers,
        None,
        flags == SymbolFlags::METHOD,
    )?;
    if side != ClassPropertySide::Instance {
        return Ok(false);
    }
    let symbol = bound_symbol(store, host, member).ok_or_else(invalid)?;
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    if record.flags().without(SymbolFlags::OPTIONAL) != flags
        || record.parent() != Some(owner)
        || store.get_merged_symbol(symbol) != Some(symbol)
        || !record
            .declarations()
            .is_some_and(|declarations| declarations.contains(&member))
        || store
            .symbol(owner)
            .and_then(|owner| owner.members())
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get(record.name()))
            != Some(symbol)
    {
        return Err(invalid());
    }
    Ok(true)
}

/// Proves an annotation root without demanding the containing class's bodies.
#[allow(clippy::too_many_lines)] // Every accepted root keeps its own syntax and binder role.
pub(in crate::semantic) fn source_class_annotation_role(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    annotation: NodeRef,
) -> Result<Option<SourceClassAnnotationRole>, ClassError> {
    let declaration = source_class_type_owner_declaration(store, host, owner)?;
    if !annotation.is_for(declaration.arena, declaration.file) {
        return Ok(None);
    }
    let record = super::preflight_node(store, host, annotation)?;
    let Some(parent) = record
        .parent
        .map(|node| NodeRef::new(annotation.arena, annotation.file, node))
    else {
        return Ok(None);
    };
    let parent_record = super::preflight_node(store, host, parent)?;
    let invalid = || invariant(ClassInvariant::InvalidPropertyTypeCache(annotation));
    if record.flags.0 != 0
        || record.range.start < parent_record.range.start
        || record.range.end > parent_record.range.end
    {
        return Err(invalid());
    }
    match &parent_record.data {
        NodeData::TypeParameterDeclaration(_) => {
            let plans = source_class_type_parameter_plans(store, host, owner)?;
            Ok(plans.iter().find_map(|parameter| {
                if parameter.declaration != parent {
                    None
                } else if parameter.constraint == Some(annotation) {
                    Some(SourceClassAnnotationRole::TypeParameterConstraint { parameter: parent })
                } else if parameter.default_type == Some(annotation) {
                    Some(SourceClassAnnotationRole::TypeParameterDefault { parameter: parent })
                } else {
                    None
                }
            }))
        }
        NodeData::PropertyDeclaration(property) if property.type_ == Some(annotation.node) => Ok(
            source_annotation_instance_member(store, host, owner, declaration, parent)?.then_some(
                SourceClassAnnotationRole::Field {
                    declaration: parent,
                },
            ),
        ),
        NodeData::MethodDeclaration(method) if method.type_ == Some(annotation.node) => Ok(
            source_annotation_instance_member(store, host, owner, declaration, parent)?
                .then_some(SourceClassAnnotationRole::MethodReturn { method: parent }),
        ),
        NodeData::ParameterDeclaration(parameter) if parameter.type_ == Some(annotation.node) => {
            let Some(member) = parent_record
                .parent
                .map(|node| NodeRef::new(parent.arena, parent.file, node))
            else {
                return Ok(None);
            };
            if !source_annotation_instance_member(store, host, owner, declaration, member)? {
                return Ok(None);
            }
            let member_record = super::preflight_node(store, host, member)?;
            let (parameters, role) = match &member_record.data {
                NodeData::ConstructorDeclaration(data) => (
                    &data.parameters,
                    SourceClassAnnotationRole::ConstructorParameter {
                        constructor: member,
                        parameter: parent,
                    },
                ),
                NodeData::MethodDeclaration(data) => (
                    &data.parameters,
                    SourceClassAnnotationRole::MethodParameter {
                        method: member,
                        parameter: parent,
                    },
                ),
                _ => return Ok(None),
            };
            if parameters
                .nodes
                .iter()
                .filter(|&&node| node == parent.node)
                .count()
                != 1
            {
                return Err(invalid());
            }
            let name = NodeRef::new(parent.arena, parent.file, parameter.name);
            let name_record = super::preflight_node(store, host, name)?;
            let NodeData::Identifier(identifier) = &name_record.data else {
                return Ok(None);
            };
            let bound = host.bound_file(member).ok_or_else(invalid)?;
            let local = bound
                .locals(member)
                .and_then(|locals| store.symbol_table(locals))
                .and_then(|locals| locals.get_source(&identifier.text))
                .ok_or_else(invalid)?;
            let local_record = store.symbol(local).ok_or_else(invalid)?;
            if name_record.parent != Some(parent.node)
                || name_record.flags.0 != 0
                || identifier.flow_node.is_some()
                || local_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                || local_record.declarations() != Some(&[parent])
                || local_record.value_declaration() != Some(parent)
                || local_record.parent().is_some()
                || store.get_merged_symbol(local) != Some(local)
            {
                return Err(invalid());
            }
            Ok(Some(role))
        }
        NodeData::ExpressionWithTypeArguments(base) => {
            let Some(arguments) = base.type_arguments.as_ref() else {
                return Ok(None);
            };
            let Some(index) = arguments
                .nodes
                .iter()
                .position(|&node| node == annotation.node)
            else {
                return Ok(None);
            };
            let Some(clause) = parent_record
                .parent
                .map(|node| NodeRef::new(parent.arena, parent.file, node))
            else {
                return Ok(None);
            };
            let clause_record = super::preflight_node(store, host, clause)?;
            let NodeData::HeritageClause(heritage) = &clause_record.data else {
                return Ok(None);
            };
            let class_record = super::preflight_node(store, host, declaration)?;
            let NodeData::ClassDeclaration(class) = &class_record.data else {
                return Err(invalid());
            };
            if parent_record.kind != SyntaxKind::ExpressionWithTypeArguments
                || parent_record.flags.0 != 0
                || base.facts != 0
                || arguments
                    .nodes
                    .iter()
                    .filter(|&&node| node == annotation.node)
                    .count()
                    != 1
                || clause_record.kind != SyntaxKind::HeritageClause
                || clause_record.flags.0 != 0
                || clause_record.parent != Some(declaration.node)
                || !matches!(
                    heritage.token,
                    SyntaxKind::ExtendsKeyword | SyntaxKind::ImplementsKeyword
                )
                || heritage.token == SyntaxKind::ExtendsKeyword
                    && heritage.types.nodes.as_slice() != [parent.node]
                || heritage
                    .types
                    .nodes
                    .iter()
                    .filter(|&&node| node == parent.node)
                    .count()
                    != 1
                || class.heritage_clauses.as_ref().is_none_or(|clauses| {
                    clauses
                        .nodes
                        .iter()
                        .filter(|&&node| node == clause.node)
                        .count()
                        != 1
                })
            {
                return Err(invalid());
            }
            Ok(Some(SourceClassAnnotationRole::HeritageArgument {
                heritage: parent,
                index,
            }))
        }
        _ => Ok(None),
    }
}

/// Class formals remain lexical. Static members and other class owners gain no scope.
pub(in crate::semantic) fn source_class_type_parameter_reference_is_owned(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<bool, ClassError> {
    let Some(parameter) = store
        .symbol(symbol)
        .filter(|parameter| parameter.flags() == SymbolFlags::TYPE_PARAMETER)
    else {
        return Ok(false);
    };
    let Some(owner) = parameter.parent().filter(|owner| {
        store
            .symbol(*owner)
            .is_some_and(|owner| owner.flags() == SymbolFlags::CLASS)
    }) else {
        return Ok(false);
    };
    let plans = source_class_type_parameter_plans(store, host, owner)?;
    let Some(parameter_index) = plans
        .iter()
        .position(|parameter| parameter.symbol == symbol)
    else {
        return Ok(false);
    };
    let declaration = source_class_type_owner_declaration(store, host, owner)?;
    let record = super::preflight_node(store, host, node)?;
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return Ok(false);
    };
    let name = NodeRef::new(node.arena, node.file, reference.type_name);
    let name_record = super::preflight_node(store, host, name)?;
    if reference.type_arguments.is_some()
        || name_record.parent != Some(node.node)
        || !matches!(&name_record.data, NodeData::Identifier(name) if parameter.name().as_utf8() == Some(name.text.as_str()) && name.flow_node.is_none())
    {
        return Ok(false);
    }
    let mut current = node;
    let mut visited = std::collections::HashSet::new();
    while visited.insert(current) && current != declaration {
        if let Some(role) = source_class_annotation_role(store, host, owner, current)? {
            return Ok(match role {
                SourceClassAnnotationRole::TypeParameterDefault { parameter } => plans
                    .iter()
                    .position(|planned| planned.declaration == parameter)
                    .is_some_and(|index| parameter_index < index),
                _ => true,
            });
        }
        let record = super::preflight_node(store, host, current)?;
        if record.parent == Some(declaration.node) {
            return source_annotation_instance_member(store, host, owner, declaration, current);
        }
        let Some(parent) = record.parent else {
            break;
        };
        current = NodeRef::new(current.arena, current.file, parent);
    }
    Ok(false)
}

pub(in crate::semantic) fn source_class_annotation_is_owned(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    annotation: NodeRef,
) -> bool {
    if source_class_annotation_role(store, host, owner, annotation)
        .ok()
        .flatten()
        .is_some()
    {
        return true;
    }
    if source_class_method_annotation_is_owned(store, host, owner, annotation)
        || source_class_method_return_annotation_is_owned(store, host, owner, annotation)
    {
        return true;
    }
    let Some(record) = host.node(annotation) else {
        return false;
    };
    let Some(parent) = record
        .parent
        .map(|node| NodeRef::new(annotation.arena, annotation.file, node))
    else {
        return false;
    };
    let Some(record) = host.node(parent) else {
        return false;
    };
    let declaration = match &record.data {
        NodeData::PropertyDeclaration(property) if property.type_ == Some(annotation.node) => {
            record
                .parent
                .map(|node| NodeRef::new(annotation.arena, annotation.file, node))
        }
        NodeData::ParameterDeclaration(parameter) if parameter.type_ == Some(annotation.node) => {
            record
                .parent
                .map(|node| NodeRef::new(annotation.arena, annotation.file, node))
                .and_then(|constructor| host.node(constructor))
                .filter(|record| record.kind == SyntaxKind::Constructor)
                .and_then(|record| record.parent)
                .map(|node| NodeRef::new(annotation.arena, annotation.file, node))
        }
        _ => None,
    };
    declaration.is_some_and(|declaration| {
        host.node(declaration)
            .is_some_and(|record| record.kind == SyntaxKind::ClassDeclaration)
            && bound_symbol(store, host, declaration) == Some(owner)
            && preflight_class_or_interface_reference(store, host, owner, SymbolFlags::CLASS)
                == Ok(0)
    })
}

/// Written returns keep the actual method and its instance or static member table.
pub(in crate::semantic) fn source_class_method_return_annotation_is_owned(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    annotation: NodeRef,
) -> bool {
    let owned = || {
        let annotation_record = super::preflight_node(store, host, annotation).ok()?;
        let method = NodeRef::new(annotation.arena, annotation.file, annotation_record.parent?);
        let method_record = super::preflight_node(store, host, method).ok()?;
        let NodeData::MethodDeclaration(data) = &method_record.data else {
            return None;
        };
        let declaration = NodeRef::new(annotation.arena, annotation.file, method_record.parent?);
        let class_record = super::preflight_node(store, host, declaration).ok()?;
        let NodeData::ClassDeclaration(class) = &class_record.data else {
            return None;
        };
        if annotation_record.flags.0 != 0
            || method_record.kind != SyntaxKind::MethodDeclaration
            || method_record.flags.0 != 0
            || data.type_ != Some(annotation.node)
            || data.type_parameters.is_some()
            || annotation_record.range.start < data.parameters.range.end
            || annotation_record.range.end > method_record.range.end
            || class_record.kind != SyntaxKind::ClassDeclaration
            || class.type_parameters.is_some()
            || method_record.range.start < class.members.range.start
            || method_record.range.end > class.members.range.end
            || class
                .members
                .nodes
                .iter()
                .filter(|&&node| node == method.node)
                .count()
                != 1
            || bound_symbol(store, host, declaration) != Some(owner)
            || preflight_class_or_interface_reference(store, host, owner, SymbolFlags::CLASS)
                != Ok(0)
        {
            return None;
        }
        let symbol = bound_symbol(store, host, method)?;
        let method_owner = store.symbol(symbol)?;
        let (side, readonly) = class_member_modifiers(
            store,
            host,
            method,
            NodeRef::new(method.arena, method.file, data.name),
            data.modifiers.as_ref(),
            None,
            true,
        )
        .ok()?;
        let class_owner = store.symbol(owner)?;
        let table = match side {
            ClassPropertySide::Instance => class_owner.members(),
            ClassPropertySide::Static => class_owner.exports(),
        }?;
        if readonly
            || method_owner.flags() != SymbolFlags::METHOD
            || method_owner.check_flags() != CheckFlags::NONE
            || method_owner.parent() != Some(owner)
            || store.get_merged_symbol(symbol) != Some(symbol)
            || method_owner
                .declarations()?
                .iter()
                .filter(|&&node| node == method)
                .count()
                != 1
            || !store.source_symbol_declarations_match(symbol)
            || store.symbol_table(table)?.get(method_owner.name()) != Some(symbol)
        {
            return None;
        }
        Some(())
    };
    owned().is_some()
}
pub(in crate::semantic) fn source_class_method_annotation_is_owned(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    annotation: NodeRef,
) -> bool {
    source_nongeneric_class_method_annotation_is_owned(store, host, owner, annotation)
        || source_class_method_type_parameter_plan(store, host, owner, annotation)
            .ok()
            .flatten()
            .is_some()
}

/// Method annotations retain the actual class, local formals, and written operand roles.
pub(in crate::semantic) fn source_class_method_type_parameter_plan(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    annotation: NodeRef,
) -> Result<
    Option<Vec<super::super::object_members::PlannedInterfaceMethodTypeParameter>>,
    ClassError,
> {
    source_class_method_type_parameter_plan_worker(store, host, owner, annotation, false)
}

/// Prepares the same method formals even when it has no written value annotation.
pub(in crate::semantic) fn source_class_method_type_parameters(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    method: NodeRef,
) -> Result<
    Option<Vec<super::super::object_members::PlannedInterfaceMethodTypeParameter>>,
    ClassError,
> {
    source_class_method_type_parameter_plan_worker(store, host, owner, method, true)
}

#[allow(clippy::too_many_lines)] // One read-only proof keeps source roles, member ownership, and formals together.
fn source_class_method_type_parameter_plan_worker(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    annotation: NodeRef,
    method_root: bool,
) -> Result<
    Option<Vec<super::super::object_members::PlannedInterfaceMethodTypeParameter>>,
    ClassError,
> {
    let selected = (|| {
        let (method, parameter) = if method_root {
            (annotation, None)
        } else {
            let annotation_record = host.node(annotation)?;
            let parent = NodeRef::new(annotation.arena, annotation.file, annotation_record.parent?);
            let parent_record = host.node(parent)?;
            match &parent_record.data {
                NodeData::ParameterDeclaration(data)
                    if data.type_ == Some(annotation.node)
                        && data.dot_dot_dot_token.is_none()
                        && data.question_token.is_none()
                        && data.initializer.is_none()
                        && data.modifiers.is_none() =>
                {
                    (
                        NodeRef::new(parent.arena, parent.file, parent_record.parent?),
                        Some(parent),
                    )
                }
                NodeData::MethodDeclaration(data) if data.type_ == Some(annotation.node) => {
                    (parent, None)
                }
                NodeData::TypeParameterDeclaration(data)
                    if data.constraint == Some(annotation.node)
                        || data.default_type == Some(annotation.node) =>
                {
                    (
                        NodeRef::new(parent.arena, parent.file, parent_record.parent?),
                        None,
                    )
                }
                _ => return None,
            }
        };
        let method_record = host.node(method)?;
        let NodeData::MethodDeclaration(data) = &method_record.data else {
            return None;
        };
        let declaration = NodeRef::new(method.arena, method.file, method_record.parent?);
        let class_record = host.node(declaration)?;
        let NodeData::ClassDeclaration(class) = &class_record.data else {
            return None;
        };
        if method_record.kind != SyntaxKind::MethodDeclaration
            || method_record.flags.0 != 0
            || data
                .type_parameters
                .as_ref()
                .is_none_or(|parameters| parameters.nodes.is_empty())
            || data.body.is_none()
            || data.asterisk_token.is_some()
            || data.postfix_token.is_some()
            || data.full_signature.is_some()
            || data.symbol.is_some()
            || data.flow_node.is_some()
            || data.end_flow_node.is_some()
            || data.next_container.is_some()
            || data.facts != 0
            || data.parameters.nodes.iter().any(|&node| {
                let parameter = NodeRef::new(method.arena, method.file, node);
                host.node(parameter).is_none_or(|record| {
                    let NodeData::ParameterDeclaration(parameter) = &record.data else {
                        return true;
                    };
                    record.kind != SyntaxKind::Parameter
                        || record.flags.0 != 0
                        || record.parent != Some(method.node)
                        || parameter.type_.is_none()
                        || parameter.dot_dot_dot_token.is_some()
                        || parameter.question_token.is_some()
                        || parameter.initializer.is_some()
                        || parameter.modifiers.is_some()
                        || parameter.symbol.is_some()
                        || parameter.facts != 0
                        || host
                            .node(NodeRef::new(method.arena, method.file, parameter.name))
                            .is_none_or(|name| name.kind != SyntaxKind::Identifier)
                })
            })
            || class_record.kind != SyntaxKind::ClassDeclaration
            || class.type_parameters.is_some()
            || class
                .members
                .nodes
                .iter()
                .filter(|&&node| node == method.node)
                .count()
                != 1
            || bound_symbol(store, host, declaration) != Some(owner)
            || preflight_class_or_interface_reference(store, host, owner, SymbolFlags::CLASS)
                != Ok(0)
        {
            return None;
        }
        let method_symbol = bound_symbol(store, host, method)?;
        let method_owner = store.symbol(method_symbol)?;
        let (side, readonly) = class_property_modifiers(
            store,
            host,
            method,
            NodeRef::new(method.arena, method.file, data.name),
            data.modifiers.as_ref(),
            None,
        )
        .ok()?;
        if readonly
            || side != ClassPropertySide::Instance
            || method_owner.flags() != SymbolFlags::METHOD
            || method_owner.parent() != Some(owner)
            || method_owner.declarations() != Some(&[method])
            || method_owner.value_declaration() != Some(method)
            || method_owner.name().is_private_identifier()
            || store.get_merged_symbol(method_symbol) != Some(method_symbol)
            || store
                .symbol(owner)?
                .members()
                .and_then(|table| store.symbol_table(table))?
                .get(method_owner.name())
                != Some(method_symbol)
        {
            return None;
        }
        if let Some(parameter) = parameter {
            let symbol = bound_symbol(store, host, parameter)?;
            let record = store.symbol(symbol)?;
            if data
                .parameters
                .nodes
                .iter()
                .filter(|&&node| node == parameter.node)
                .count()
                != 1
                || record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                || record.declarations() != Some(&[parameter])
                || record.value_declaration() != Some(parameter)
                || record.parent().is_some()
                || store.get_merged_symbol(symbol) != Some(symbol)
                || host
                    .bound_file(method)?
                    .locals(method)
                    .and_then(|table| store.symbol_table(table))?
                    .get(record.name())
                    != Some(symbol)
            {
                return None;
            }
        }
        Some(method)
    })();
    let Some(method) = selected else {
        return Ok(None);
    };
    let NodeData::MethodDeclaration(data) = &super::preflight_node(store, host, method)?.data
    else {
        return Ok(None);
    };
    let planned = super::super::object_members::plan_declared_signature_type_parameters(
        store,
        host,
        method,
        data.type_parameters.as_ref(),
        &data.parameters,
        host.bound_file(method)
            .and_then(|bound| bound.locals(method))
            .and_then(|table| store.symbol_table(table)),
        SyntaxKind::MethodDeclaration,
    )
    .map_err(|_| invariant(ClassInvariant::InvalidProperty(method)))?;
    if !method_root
        && let Some(parent) = host.node(annotation).and_then(|record| record.parent)
        && host
            .node(NodeRef::new(annotation.arena, annotation.file, parent))
            .is_some_and(|record| record.kind == SyntaxKind::TypeParameter)
        && !planned
            .iter()
            .any(|parameter| parameter.declaration.node == parent)
    {
        return Ok(None);
    }
    Ok(Some(planned))
}

/// A nongeneric method parameter keeps its original inline-literal proof.
fn source_nongeneric_class_method_annotation_is_owned(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    annotation: NodeRef,
) -> bool {
    let owned = || {
        let annotation_record = host.node(annotation)?;
        if !matches!(
            (annotation_record.kind, &annotation_record.data),
            (SyntaxKind::TypeLiteral, NodeData::TypeLiteralNode(_))
                | (SyntaxKind::UnionType, NodeData::UnionTypeNode(_))
        )
        {
            return None;
        }
        let parameter = NodeRef::new(annotation.arena, annotation.file, annotation_record.parent?);
        let parameter_record = host.node(parameter)?;
        let NodeData::ParameterDeclaration(data) = &parameter_record.data else {
            return None;
        };
        let method = NodeRef::new(annotation.arena, annotation.file, parameter_record.parent?);
        let method_record = host.node(method)?;
        let NodeData::MethodDeclaration(method_data) = &method_record.data else {
            return None;
        };
        let declaration = NodeRef::new(annotation.arena, annotation.file, method_record.parent?);
        let class_record = host.node(declaration)?;
        let NodeData::ClassDeclaration(class) = &class_record.data else {
            return None;
        };
        if data.type_ != Some(annotation.node)
            || data.dot_dot_dot_token.is_some()
            || data.question_token.is_some()
            || data.initializer.is_some()
            || data.modifiers.is_some()
            || method_record.kind != SyntaxKind::MethodDeclaration
            || method_data.type_parameters.is_some()
            || method_data
                .parameters
                .nodes
                .iter()
                .filter(|&&node| node == parameter.node)
                .count()
                != 1
            || class_record.kind != SyntaxKind::ClassDeclaration
            || class.type_parameters.is_some()
            || class
                .members
                .nodes
                .iter()
                .filter(|&&node| node == method.node)
                .count()
                != 1
            || bound_symbol(store, host, declaration) != Some(owner)
            || preflight_class_or_interface_reference(store, host, owner, SymbolFlags::CLASS)
                != Ok(0)
        {
            return None;
        }
        let method_symbol = bound_symbol(store, host, method)?;
        let method_owner = store.symbol(method_symbol)?;
        let (side, readonly) = class_property_modifiers(
            store,
            host,
            method,
            NodeRef::new(method.arena, method.file, method_data.name),
            method_data.modifiers.as_ref(),
            None,
        )
        .ok()?;
        let class_owner = store.symbol(owner)?;
        let table = match side {
            ClassPropertySide::Instance => class_owner.members(),
            ClassPropertySide::Static => class_owner.exports(),
        }?;
        let symbol = bound_symbol(store, host, parameter)?;
        let parameter_owner = store.symbol(symbol)?;
        let bound = host.bound_file(parameter)?;
        if readonly
            || method_owner.flags() != SymbolFlags::METHOD
            || method_owner.parent() != Some(owner)
            || store.get_merged_symbol(method_symbol) != Some(method_symbol)
            || !method_owner.declarations()?.contains(&method)
            || store.symbol_table(table)?.get(method_owner.name()) != Some(method_symbol)
            || parameter_owner.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            || parameter_owner.declarations() != Some(&[parameter])
            || parameter_owner.value_declaration() != Some(parameter)
            || parameter_owner.parent().is_some()
            || store.get_merged_symbol(symbol) != Some(symbol)
            || store
                .symbol_table(bound.locals(method)?)?
                .get(parameter_owner.name())
                != Some(symbol)
        {
            return None;
        }
        Some(())
    };
    owned().is_some()
}

pub(in crate::semantic) fn completed_class_symbol(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
) -> bool {
    if let Some(provenance) = store.source_class_provenance_for_symbol(owner) {
        return provenance.symbol() == owner
            && provenance.complete
            && validate_source_class_stored_header(store, provenance).is_ok();
    }
    store
        .declared_type_links(owner)
        .and_then(|links| links.declared_type)
        .is_some_and(|instance| {
            exact_class_instance_identity(store, owner, instance).is_some()
                && validate_class_heritage_members(store, instance)
                    == ClassHeritageMembersValidation::Valid
        })
}

/// Completed instance fields remain visible to the canonical array-capability walk.
pub(in crate::semantic) fn class_instance_type_edges(
    store: &CanonicalTypeMapperStore,
    instance: TypeId,
) -> Result<Option<Vec<TypeId>>, ClassError> {
    let owner = if let Some(provenance) = store.source_class_provenance(instance) {
        validate_source_class_stored_header(store, provenance)?;
        if !provenance.complete || provenance.instance_type() != instance {
            return Err(invariant(ClassInvariant::InvalidInstanceMembers(
                provenance.symbol(),
            )));
        }
        provenance.symbol()
    } else if let Some(owner) = store.type_payload(instance).and_then(TypeRecord::symbol)
        && validate_class_heritage_members(store, instance) == ClassHeritageMembersValidation::Valid
    {
        owner
    } else {
        return Ok(None);
    };
    let invalid = || invariant(ClassInvariant::InvalidInstanceMembers(owner));
    let record = store.type_payload(instance).ok_or_else(invalid)?;
    if matches!(record.data(), TypeData::TypeReference(_)) {
        let reference = validate_direct_generic_reference(store, instance).map_err(|_| invalid())?;
        let mut edges = Vec::with_capacity(reference.type_arguments.len() + 1);
        edges.push(reference.target);
        edges.extend(reference.type_arguments);
        return Ok(Some(edges));
    }
    let TypeData::Interface(interface) = record.data() else {
        return Err(invalid());
    };
    let structured = &interface.reference.object.structured;
    let mut edges = structured
        .properties
        .as_deref()
        .unwrap_or_default()
        .iter()
        .map(|property| {
            store
                .value_symbol_links(*property)
                .and_then(|links| links.resolved_type)
                .ok_or_else(invalid)
        })
        .collect::<Result<Vec<_>, _>>()?;
    edges.extend(interface.resolved_base_types.iter().flatten().copied());
    for &index in structured.index_infos.as_deref().unwrap_or_default() {
        let info = store.index_info(index).ok_or_else(invalid)?;
        edges.extend([info.key_type(), info.value_type()]);
    }
    Ok(Some(edges))
}

pub(super) fn validate_source_annotation_value_cache(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    context: &ClassTypeQueryContext,
    owner: SemanticSymbolId,
    annotation: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<(), ClassError> {
    let expected = preflight_source_class_annotation(
        store,
        host,
        &context.global_types,
        context.options,
        annotation,
        owner,
    )?
    .cached_type(store, host, Some(&context.global_types))?;
    let expected =
        if let Some(SourceClassAnnotationRole::ConstructorParameter { parameter, .. }) =
            source_class_annotation_role(store, host, owner, annotation)?
            && host.node(parameter).is_some_and(|record| {
                matches!(&record.data, NodeData::ParameterDeclaration(data)
                if data.question_token.is_some())
            })
        {
            expected
                .map(|annotation_type| {
                    super::optional_constructor_parameter_type_with_context(
                        store,
                        annotation_type,
                        true,
                        parameter,
                        Some(context),
                    )
                })
                .transpose()?
                .flatten()
        } else {
            expected
        };
    if store.value_symbol_links(symbol).is_some_and(|links| {
        links != &ValueSymbolLinks::default()
            && expected.is_none_or(|type_| {
                links
                    != &ValueSymbolLinks {
                        resolved_type: Some(type_),
                        ..ValueSymbolLinks::default()
                    }
            })
    }) {
        return Err(invariant(ClassInvariant::InvalidPropertyValueCache(symbol)));
    }
    Ok(())
}

pub(in crate::semantic) fn begin_source_class_annotations(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    plan: &SourceClassPlan,
) -> Result<Option<TypeId>, ClassError> {
    let Some(context) = &plan.type_query_context else {
        return Ok(None);
    };
    if context.global_types != *globals {
        return Err(invariant(ClassInvariant::InvalidPlan(plan.declaration())));
    }
    if plan.annotation_nodes().is_empty() {
        return Ok(None);
    }
    let invalid = || invariant(ClassInvariant::InvalidPlan(plan.declaration()));
    let targets = CanonicalArrayTargets::from_global_types(globals);
    if let Some(instance) = store
        .declared_type_links(plan.symbol())
        .and_then(|links| links.declared_type)
        && let Some(scope) = store.source_class_annotation_scope(instance)
    {
        if scope.plan != *plan
            || source_class_annotation_scope_targets(store, instance) != Some(targets)
            || !source_class_plan_is_current(store, host, plan)?
        {
            return Err(invalid());
        }
        if let Some(provenance) = store.source_class_provenance_for_symbol(plan.symbol()) {
            validate_source_class_header(store, host, provenance)?;
        }
        return Ok(None);
    }
    if let Some(provenance) = store.source_class_provenance_for_symbol(plan.symbol()) {
        if provenance.complete {
            if !source_class_plan_is_current(store, host, plan)? {
                return Err(invalid());
            }
            validate_source_class_header(store, host, provenance)?;
            return Ok(None);
        }
        if provenance.prepared.plan != *plan {
            return Err(invalid());
        }
        validate_source_class_stored_header(store, provenance)?;
        // A retained self annotation needs its proved owner before source replay.
        // The stored header is checked first. Source and annotation checks follow
        // inside the scope, before the caller can use the pending header.
        let instance = provenance.instance_type();
        let scope = SourceClassAnnotationScope {
            plan: plan.clone(),
            instance,
            targets,
        };
        if !store.begin_source_class_annotation_scope(instance, scope) {
            return Err(invalid());
        }
        let result = if source_class_annotation_scope_targets(store, instance) == Some(targets) {
            validate_source_class_header(
                store,
                host,
                store
                    .source_class_provenance(instance)
                    .expect("the retained source class was checked before opening its scope"),
            )
        } else {
            Err(invalid())
        };
        if let Err(error) = result {
            if !store.end_source_class_annotation_scope(instance) {
                return Err(invalid());
            }
            return Err(error);
        }
        return Ok(Some(instance));
    }
    if !source_class_plan_is_current(store, host, plan)? {
        return Err(invalid());
    }
    let instance = store.get_declared_type_of_symbol(host, plan.symbol())?;
    let scope = SourceClassAnnotationScope {
        plan: plan.clone(),
        instance,
        targets,
    };
    if !store.begin_source_class_annotation_scope(instance, scope) {
        return Err(invalid());
    }
    Ok(Some(instance))
}

/// Reopens only an existing pending header with the same source-query options.
pub(in crate::semantic) fn begin_retained_source_class_annotations(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    context: &ClassTypeQueryContext,
    symbol: SemanticSymbolId,
) -> Result<Option<TypeId>, ClassError> {
    let Some(provenance) = store.source_class_provenance_for_symbol(symbol) else {
        return Ok(None);
    };
    if provenance.complete || provenance.prepared.plan.annotation_nodes().is_empty() {
        return Ok(None);
    }
    let plan = &provenance.prepared.plan;
    if plan.symbol() != symbol || plan.type_query_context.as_ref() != Some(context) {
        return Err(invariant(ClassInvariant::InvalidPlan(plan.declaration())));
    }
    let plan = plan.clone();
    begin_source_class_annotations(store, host, &context.global_types, &plan)
}

/// Keeps same-source pending headers valid during a member query's union-cache scan.
pub(in crate::semantic) fn with_retained_source_class_annotation_scopes<T>(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    context: &ClassTypeQueryContext,
    symbol: SemanticSymbolId,
    query: impl FnOnce(&mut CanonicalTypeMapperStore) -> Result<T, ClassError>,
) -> Result<T, ClassError> {
    // Other routes keep the original requested-owner scope without gaining peers.
    let peers = (|| {
        let declaration = store.symbol(symbol)?.value_declaration()?;
        let (_, bound) = host.source(declaration)?;
        let root = bound.source_file();
        let record = host.node(declaration)?;
        let source = host.node(root)?;
        let NodeData::SourceFile(data) = &source.data else {
            return None;
        };
        if record.kind != SyntaxKind::ClassDeclaration
            || record.parent != Some(root.node)
            || source.kind != SyntaxKind::SourceFile
            || source.parent.is_some()
            || !store.contains_node_ref(root)
            || bound_symbol(store, host, declaration) != Some(symbol)
            || !data.statements.nodes.contains(&declaration.node)
        {
            return None;
        }
        Some((root, &data.statements.nodes))
    })();
    let mut owners = Vec::new();
    owners
        .try_reserve(peers.map_or(1, |(_, statements)| statements.len()))
        .map_err(|_| invariant(ClassInvariant::InvalidInstanceMembers(symbol)))?;
    if let Some((root, statements)) = peers {
        for &node in statements {
            let declaration = NodeRef::new(root.arena, root.file, node);
            let Some(record) = host.node(declaration) else {
                continue;
            };
            if record.kind != SyntaxKind::ClassDeclaration || record.parent != Some(root.node) {
                continue;
            }
            if let Some(owner) = bound_symbol(store, host, declaration)
                && store
                    .symbol(owner)
                    .and_then(|owner| owner.value_declaration())
                    == Some(declaration)
            {
                owners.push(owner);
            }
        }
    } else {
        owners.push(symbol);
    }
    let mut scopes = Vec::new();
    let result = (|| {
        for owner in owners {
            scopes
                .try_reserve(1)
                .map_err(|_| invariant(ClassInvariant::InvalidInstanceMembers(owner)))?;
            if let Some(instance) =
                begin_retained_source_class_annotations(store, host, context, owner)?
            {
                scopes.push((owner, instance));
            }
        }
        query(store)
    })();
    let mut cleanup_error = None;
    for (owner, instance) in scopes.into_iter().rev() {
        if !store.end_source_class_annotation_scope(instance) {
            cleanup_error
                .get_or_insert_with(|| invariant(ClassInvariant::InvalidConstructSignature(owner)));
        }
    }
    cleanup_error.map_or(result, Err)
}

pub(in crate::semantic) fn source_class_annotation_scope_targets(
    store: &CanonicalTypeMapperStore,
    instance: TypeId,
) -> Option<CanonicalArrayTargets> {
    let scope = store.source_class_annotation_scope(instance)?;
    let plan = &scope.plan;
    if scope.instance != instance
        || store.declared_type_links(plan.symbol())?.declared_type != Some(instance)
        || !store.source_symbol_declarations_match(plan.symbol())
        || plan.bindings.iter().any(|expected| {
            let Ok(mut actual) = source_class_binding(store, expected.symbol) else {
                return true;
            };
            if expected.check_flags == CheckFlags::READONLY
                && actual.check_flags == CheckFlags::NONE
                && plan
                    .sources
                    .iter()
                    .any(|source| source.symbol == expected.symbol && source.readonly)
            {
                actual.check_flags = CheckFlags::READONLY;
            }
            &actual != expected
        })
        || exact_class_instance_identity(store, plan.symbol(), instance).is_none()
    {
        return None;
    }
    if let Some(provenance) = store.source_class_provenance(instance) {
        if provenance.prepared.plan != *plan
            || validate_source_class_stored_header(store, provenance).is_err()
        {
            return None;
        }
    } else {
        let record = store.type_payload(instance)?;
        let TypeData::Interface(interface) = record.data() else {
            return None;
        };
        if record.object_flags() != (ObjectFlags::CLASS | ObjectFlags::REFERENCE)
            || interface.declared_members_resolved
            || interface.base_types_resolved
            || interface.resolved_base_constructor_type.is_some()
            || interface.declared_members.is_some()
            || interface.declared_call_signatures.is_some()
            || interface.declared_construct_signatures.is_some()
            || interface.declared_index_infos.is_some()
            || interface.resolved_base_types.is_some()
            || interface.reference.object.structured != StructuredTypeData::default()
            || store
                .value_symbol_links(plan.symbol())
                .is_some_and(|links| links != &ValueSymbolLinks::default())
        {
            return None;
        }
    }
    Some(scope.targets)
}

#[cfg(test)]
mod tests {
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::super::{
        ClassBodyParameterType, SourceClassProvenance, plan_source_class_members_with_type_context,
    };
    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
        DeclaredTypeError, IntrinsicBootstrapOptions, SourceFileLinks, SymbolNodeLinks,
        TypeNodeLinks, TypeNodeUnavailable, bootstrap::LiteralTypeCacheError,
        production::GlobalMergeCompletion,
    };

    const LIBRARY_FILE: FileId = FileId::new(202_452);
    const FILE: FileId = FileId::new(202_453);

    fn context<'a>(
        library: &'a ParseResult,
        source: &'a ParseResult,
    ) -> CanonicalCheckerContext<'a> {
        let mut binder = CanonicalBinder::new();
        for (parsed, file, path, library) in [
            (library, LIBRARY_FILE, "\"/lib.d.ts\"", true),
            (source, FILE, "\"/model.ts\"", false),
        ] {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        library,
                        library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![(LIBRARY_FILE, &library.arena), (FILE, &source.arena)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                strict_property_initialization: true,
                no_implicit_any: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn method_context(source: &ParseResult) -> CanonicalCheckerContext<'_> {
        assert!(source.diagnostics.is_empty(), "{:?}", source.diagnostics);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &source.arena,
                source.source_file,
                FILE,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/methods.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&source.arena, FILE)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![(FILE, &source.arena)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                no_implicit_any: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn method_snapshot(
        context: &CanonicalCheckerContext<'_>,
    ) -> (String, CanonicalCheckerDiagnostics) {
        (
            format!("{:?}", context.store()),
            context.diagnostics().clone(),
        )
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep each damaged proof beside its exact restore.
    fn named_method_return_annotations_keep_owner_and_cache_proofs() {
        for warm in [false, true] {
            let source = parse_source_file(concat!(
                "type Text = string; ",
                "class Model { ",
                "read(value: string): Text { return value; } ",
                "static copy(value: string): Text { return value; } ",
                "} class Other {}",
            ));
            let mut context = method_context(&source);
            let (_, owner) = self_class_owner(&context, &source);
            let other = context
                .store()
                .symbol_table(context.globals())
                .unwrap()
                .get_source("Other")
                .unwrap();
            let options = context.options();
            let globals = context.global_types().clone();
            let query_context = ClassTypeQueryContext::new(&globals, options);
            let bound = context.file(FILE).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&source.arena, &bound)],
                GlobalMergeCompletion::for_test(options.name_resolution),
            )
            .unwrap();
            let cold = method_snapshot(&context);
            let plan = plan_source_class_members_with_type_context(
                context.store(),
                &host,
                owner,
                Some(&query_context),
            )
            .unwrap();
            assert_eq!(plan.annotation_nodes().len(), 2);
            for method in &plan.methods {
                let annotation = method.method.return_type_node.unwrap();
                assert_eq!(
                    method.return_type,
                    Some(ClassBodyParameterType::Annotation(annotation))
                );
                assert!(plan.annotation_nodes().contains(&annotation));
                assert!(source_class_method_return_annotation_is_owned(
                    context.store(),
                    &host,
                    owner,
                    annotation
                ));
                assert!(!source_class_method_return_annotation_is_owned(
                    context.store(),
                    &host,
                    other,
                    annotation
                ));
                assert_eq!(
                    preflight_source_class_annotation(
                        context.store(),
                        &host,
                        &globals,
                        options.into(),
                        annotation,
                        other
                    )
                    .err(),
                    Some(DeclaredTypeError::TypeNodeUnavailable(
                        TypeNodeUnavailable::InvalidTypeReference(annotation)
                    ))
                );
                assert_eq!(
                    preflight_source_class_annotation(
                        context.store(),
                        &host,
                        &globals,
                        options.into(),
                        annotation,
                        owner
                    )
                    .unwrap()
                    .cached_type(context.store(), &host, Some(&globals)),
                    Ok(None)
                );
                assert_eq!(
                    super::super::source_class_method_return_type(context.store(), method),
                    Err(invariant(ClassInvariant::InvalidPropertyTypeCache(
                        annotation
                    )))
                );
            }
            assert_eq!(method_snapshot(&context), cold);
            if warm {
                context.check_source_file(FILE).unwrap();
                assert!(context.diagnostics().is_empty());
            }
            let method = &plan.methods[0].method;
            let annotation = method.return_type_node.unwrap();
            let annotation_links = context
                .store()
                .type_node_links(annotation)
                .cloned()
                .unwrap_or_default();
            let reference_links = context
                .store()
                .symbol_node_links(annotation)
                .cloned()
                .unwrap_or_default();
            let member = context.store().symbol(method.symbol).unwrap().clone();
            let wrong = context.store().intrinsic_bootstrap().unwrap().number_type;
            for damage in ["annotation", "reference", "owner"] {
                match damage {
                    "annotation" => assert!(context.store_mut_for_test().set_type_node_links(
                        annotation,
                        TypeNodeLinks {
                            resolved_type: Some(wrong),
                            ..annotation_links.clone()
                        }
                    )),
                    "reference" => assert!(context.store_mut_for_test().set_symbol_node_links(
                        annotation,
                        SymbolNodeLinks {
                            resolved_symbol: Some(other)
                        }
                    )),
                    "owner" => assert!(context.store_mut_for_test().set_symbol_relationships(
                        method.symbol,
                        member.members(),
                        member.exports(),
                        Some(other),
                        member.export_symbol()
                    )),
                    _ => unreachable!(),
                }
                let changed = method_snapshot(&context);
                for _ in 0..2 {
                    let error = preflight_source_class_annotation(
                        context.store(),
                        &host,
                        &globals,
                        options.into(),
                        annotation,
                        owner,
                    )
                    .err()
                    .expect("a changed return proof must fail");
                    assert!(
                        matches!(
                            error,
                            DeclaredTypeError::TypeNodeUnavailable(TypeNodeUnavailable::InvalidTypeReference(node)
                                | TypeNodeUnavailable::InvalidCachedSymbol { node, .. }) if node == annotation
                        ),
                        "warm={warm}, damage={damage}: {error:?}"
                    );
                    assert!(
                        plan_source_class_members_with_type_context(
                            context.store(),
                            &host,
                            owner,
                            Some(&query_context)
                        )
                        .is_err()
                    );
                    assert_eq!(method_snapshot(&context), changed);
                }
                let store = context.store_mut_for_test();
                assert!(store.set_type_node_links(annotation, annotation_links.clone()));
                assert!(store.set_symbol_node_links(annotation, reference_links.clone()));
                assert!(store.set_symbol_relationships(
                    method.symbol,
                    member.members(),
                    member.exports(),
                    member.parent(),
                    member.export_symbol()
                ));
                let restored = method_snapshot(&context);
                assert_eq!(
                    plan_source_class_members_with_type_context(
                        context.store(),
                        &host,
                        owner,
                        Some(&query_context)
                    ),
                    Ok(plan.clone())
                );
                assert_eq!(method_snapshot(&context), restored);
            }
            context.check_source_file(FILE).unwrap();
            let returned = context.store().intrinsic_bootstrap().unwrap().string_type;
            let signature = context
                .store()
                .signature_links(method.declaration)
                .unwrap()
                .resolved_signature
                .signature()
                .unwrap();
            for damaged_return in [None, Some(wrong)] {
                assert!(
                    context
                        .store_mut_for_test()
                        .set_signature_resolved_return_type(signature, damaged_return)
                );
                let changed = method_snapshot(&context);
                assert_eq!(
                    context.get_return_type_of_signature(signature),
                    Err(DeclaredTypeError::TypeNodeUnavailable(
                        TypeNodeUnavailable::InvalidFunctionSignature(signature)
                    ))
                );
                assert!(context.get_class_query_member_type(method.symbol).is_err());
                assert_eq!(method_snapshot(&context), changed);
                assert!(
                    context
                        .store_mut_for_test()
                        .set_signature_resolved_return_type(signature, Some(returned))
                );
            }
            let completed = method_snapshot(&context);
            for method in &plan.methods {
                assert_eq!(
                    super::super::source_class_method_return_type(context.store(), method),
                    Ok(Some(returned))
                );
            }
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(method_snapshot(&context), completed);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Follow the same header through pending calls and completed readers.
    fn named_method_returns_keep_pending_calls_self_identity_and_caller_arrays() {
        use super::super::{
            class_body_method_callable_with_query_context,
            completed_source_class_method_signature_return_type,
            completed_source_class_method_type, prepare_source_class_constructor_header,
        };
        use crate::semantic::instantiate::{InstantiationLimits, InstantiationSession};

        let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parse_source_file(concat!(
            "type Names = string[]; ",
            "class Model { ",
            "names: Names; ",
            "constructor(names: Names) { this.names = names; } ",
            "first(): Names { return this.second(); } ",
            "second(): Names { return this.names; } ",
            "self(): Model { return this; } ",
            "}",
        ));
        let mut context = context(&library, &source);
        let (_, owner) = self_class_owner(&context, &source);
        let globals = context.global_types().clone();
        let options = context.options();
        let query_context = ClassTypeQueryContext::new(&globals, options);
        let library_bound = context.file(LIBRARY_FILE).unwrap().1.clone();
        let bound = context.file(FILE).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&library.arena, &library_bound), (&source.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let plan = plan_source_class_members_with_type_context(
            context.store(),
            &host,
            owner,
            Some(&query_context),
        )
        .unwrap();
        assert_eq!(plan.methods.len(), 3);
        assert!(
            plan.methods
                .iter()
                .all(|method| method.method.parameters.is_empty())
        );
        let mut caller = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let members = prepare_source_class_constructor_header(
            context.store_mut_for_test(),
            &host,
            &globals,
            options,
            &mut caller,
            &mut diagnostics,
            &plan,
        )
        .unwrap();
        assert!(diagnostics.is_empty());
        let prepared = context
            .store()
            .source_class_provenance_for_symbol(owner)
            .unwrap()
            .prepared
            .clone();
        let instance = prepared.instance_type;
        assert_eq!(members.shells().instance_type(), instance);
        assert!(
            !context
                .store()
                .source_class_provenance(instance)
                .unwrap()
                .complete
        );
        let scope = begin_retained_source_class_annotations(
            context.store_mut_for_test(),
            &host,
            &query_context,
            owner,
        )
        .unwrap();
        assert_eq!(scope, Some(instance));
        let first = &prepared.plan.methods[0].method;
        let second = &prepared.plan.methods[1].method;
        let self_method = &prepared.plan.methods[2].method;
        let body = prepared
            .plan
            .bodies
            .iter()
            .find(|body| body.declaration == first.declaration)
            .unwrap();
        let access = prepared.body_access(context.store(), &host, body).unwrap();
        let returned = context
            .store()
            .signature(prepared.methods[1].1)
            .unwrap()
            .resolved_return_type()
            .unwrap();
        let targets = CanonicalArrayTargets::from_global_types(&globals);
        let array = context
            .store()
            .canonical_array_reference_with_targets(targets, returned)
            .unwrap()
            .unwrap();
        assert_eq!(
            array.element_type,
            context.store().intrinsic_bootstrap().unwrap().string_type
        );
        assert!(!array.readonly);
        let pending = method_snapshot(&context);
        let target = class_body_method_callable_with_query_context(
            context.store(),
            &host,
            &access,
            instance,
            second.symbol,
            &query_context,
        )
        .unwrap();
        assert_eq!(target.class_symbol(), owner);
        assert_eq!(target.declaration(), Some(second.declaration));
        assert_eq!(target.callable().signature, prepared.methods[1].1);
        assert_eq!(target.callable().return_type, Some(returned));
        assert_eq!(target.pending_return_body(), None);
        let self_target = class_body_method_callable_with_query_context(
            context.store(),
            &host,
            &access,
            instance,
            self_method.symbol,
            &query_context,
        )
        .unwrap();
        assert_eq!(self_target.callable().return_type, Some(instance));
        assert_eq!(self_target.pending_return_body(), None);
        assert_eq!(
            completed_source_class_method_type(
                context.store(),
                &host,
                second.symbol,
                &query_context
            ),
            Err(invariant(ClassInvariant::InvalidPropertyValueCache(
                second.symbol
            )))
        );
        assert_eq!(
            context.get_return_type_of_signature(prepared.methods[1].1),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidFunctionSignature(prepared.methods[1].1)
            ))
        );
        assert_eq!(method_snapshot(&context), pending);
        let mut wrong_options = query_context.clone();
        wrong_options.options.no_implicit_any = !wrong_options.options.no_implicit_any;
        let mut wrong_array = query_context.clone();
        wrong_array.global_types.array_type = globals.readonly_array_type;
        let mut missing_array = query_context.clone();
        missing_array.global_types.array_type = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .empty_generic_type;
        for wrong in [&wrong_options, &wrong_array, &missing_array] {
            for _ in 0..2 {
                assert_eq!(
                    class_body_method_callable_with_query_context(
                        context.store(),
                        &host,
                        &access,
                        instance,
                        second.symbol,
                        wrong
                    ),
                    Err(invariant(ClassInvariant::InvalidPropertyValueCache(
                        second.symbol
                    )))
                );
                assert_eq!(method_snapshot(&context), pending);
            }
        }
        assert!(
            context
                .store_mut_for_test()
                .end_source_class_annotation_scope(instance)
        );
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        assert!(
            context
                .store()
                .source_class_provenance(instance)
                .unwrap()
                .complete
        );
        for (method, &(callable, signature), expected) in [
            (first, &prepared.methods[0], returned),
            (second, &prepared.methods[1], returned),
            (self_method, &prepared.methods[2], instance),
        ] {
            assert_eq!(
                context.get_class_query_member_type(method.symbol),
                Ok(callable)
            );
            assert_eq!(
                context.get_return_type_of_signature(signature),
                Ok(expected)
            );
            assert_eq!(
                context.get_type_from_type_node(method.return_type_node.unwrap()),
                Ok(expected)
            );
        }
        let completed = method_snapshot(&context);
        for wrong in [&wrong_options, &wrong_array, &missing_array] {
            assert_eq!(
                completed_source_class_method_type(context.store(), &host, second.symbol, wrong),
                Err(invariant(ClassInvariant::InvalidPropertyTypeCache(
                    second.declaration
                )))
            );
            assert_eq!(method_snapshot(&context), completed);
        }
        assert_eq!(
            completed_source_class_method_signature_return_type(
                context.store(),
                &host,
                second.declaration,
                prepared.methods[1].1,
                None,
                options.into()
            ),
            Err(invariant(ClassInvariant::InvalidPropertyTypeCache(
                second.declaration
            )))
        );
        assert_eq!(method_snapshot(&context), completed);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(method_snapshot(&context), completed);
    }

    #[test]
    fn method_type_literal_annotations_reject_changed_nested_caches_and_parameter_owners() {
        for warm in [false, true] {
            for damage in 0..6 {
                let source = parse_source_file(concat!(
                    "class Model { ",
                    "read(source: { first: { value: number }; second: { value: string } }): void {} ",
                    "static read(source: { first: { value: number }; second: { value: string } }): void {} ",
                    "} class Other {}",
                ));
                let mut context = method_context(&source);
                let (_, owner) = self_class_owner(&context, &source);
                let other = context
                    .store()
                    .symbol_table(context.globals())
                    .unwrap()
                    .get_source("Other")
                    .unwrap();
                let options = context.options();
                let globals = context.global_types().clone();
                let query_context = ClassTypeQueryContext::new(&globals, options);
                let bound = context.file(FILE).unwrap().1.clone();
                let host = DeclaredTypeHost::new_after_global_merge(
                    [(&source.arena, &bound)],
                    GlobalMergeCompletion::for_test(options.name_resolution),
                )
                .unwrap();
                let plan = plan_source_class_members_with_type_context(
                    context.store(),
                    &host,
                    owner,
                    Some(&query_context),
                )
                .unwrap();
                assert_eq!(plan.annotation_nodes().len(), 2);
                let parameter = plan.methods[0].method.parameters[0];
                let root = parameter.type_node.unwrap();
                assert_eq!(parameter.type_, ClassBodyParameterType::Annotation(root));
                let object = crate::semantic::object_members::plan_type_literal(
                    context.store(),
                    &host,
                    root,
                    None,
                )
                .unwrap();
                let nested = object.properties[1].type_node;
                let nested_object = crate::semantic::object_members::plan_type_literal(
                    context.store(),
                    &host,
                    nested,
                    None,
                )
                .unwrap();
                let leaf = nested_object.properties[0].symbol;
                let before = method_snapshot(&context);
                assert!(source_class_method_annotation_is_owned(
                    context.store(),
                    &host,
                    owner,
                    root
                ));
                assert!(!source_class_method_annotation_is_owned(
                    context.store(),
                    &host,
                    other,
                    root
                ));
                assert_eq!(
                    preflight_source_class_annotation(
                        context.store(),
                        &host,
                        &globals,
                        options.into(),
                        root,
                        other
                    )
                    .err(),
                    Some(DeclaredTypeError::TypeNodeUnavailable(
                        TypeNodeUnavailable::InvalidTypeReference(root)
                    ))
                );
                assert_eq!(method_snapshot(&context), before);
                let members = warm.then(|| {
                    context.check_source_file(FILE).unwrap();
                    context.get_nongeneric_class_members(owner).unwrap()
                });
                let root_links = context
                    .store()
                    .type_node_links(root)
                    .cloned()
                    .unwrap_or_default();
                let nested_links = context
                    .store()
                    .type_node_links(nested)
                    .cloned()
                    .unwrap_or_default();
                let parameter_links = context
                    .store()
                    .value_symbol_links(parameter.symbol)
                    .cloned()
                    .unwrap_or_default();
                let leaf_links = context
                    .store()
                    .value_symbol_links(leaf)
                    .cloned()
                    .unwrap_or_default();
                let wrong = if damage == 5 {
                    context
                        .get_type_from_type_node(
                            plan.methods[1].method.parameters[0].type_node.unwrap(),
                        )
                        .unwrap()
                } else {
                    context.store().intrinsic_bootstrap().unwrap().number_type
                };
                let store = context.store_mut_for_test();
                match damage {
                    0 | 5 => {
                        assert!(store.set_type_node_links(
                            root,
                            TypeNodeLinks {
                                resolved_type: Some(wrong),
                                ..TypeNodeLinks::default()
                            }
                        ));
                        assert!(store.set_value_symbol_links(
                            parameter.symbol,
                            ValueSymbolLinks {
                                resolved_type: Some(wrong),
                                ..ValueSymbolLinks::default()
                            }
                        ));
                    }
                    1 => {
                        assert!(store.set_type_node_links(
                            nested,
                            TypeNodeLinks {
                                resolved_type: Some(wrong),
                                ..TypeNodeLinks::default()
                            }
                        ));
                    }
                    2 => {
                        assert!(store.set_value_symbol_links(
                            leaf,
                            ValueSymbolLinks {
                                resolved_type: Some(wrong),
                                ..ValueSymbolLinks::default()
                            }
                        ));
                    }
                    3 => {
                        assert!(store.set_value_symbol_links(
                            parameter.symbol,
                            ValueSymbolLinks {
                                resolved_type: Some(wrong),
                                ..ValueSymbolLinks::default()
                            }
                        ));
                    }
                    4 => {
                        assert!(store.set_symbol_relationships(
                            parameter.symbol,
                            None,
                            None,
                            Some(owner),
                            None
                        ));
                    }
                    _ => unreachable!(),
                }
                let expected = match damage {
                    0 | 1 | 5 => ClassError::DeclaredType(DeclaredTypeError::TypeNodeUnavailable(
                        TypeNodeUnavailable::InvalidLiteralType(if damage == 1 {
                            nested
                        } else {
                            root
                        }),
                    )),
                    2 => {
                        ClassError::DeclaredType(DeclaredTypeError::TypeNodeUnavailable(if warm {
                            TypeNodeUnavailable::InvalidLiteralType(nested)
                        } else {
                            TypeNodeUnavailable::InvalidTypeReference(nested)
                        }))
                    }
                    3 => invariant(ClassInvariant::InvalidPropertyValueCache(parameter.symbol)),
                    4 => invariant(ClassInvariant::InvalidPropertySymbol(parameter.declaration)),
                    _ => unreachable!(),
                };
                let poisoned = method_snapshot(&context);
                for _ in 0..2 {
                    assert_eq!(
                        plan_source_class_members_with_type_context(
                            context.store(),
                            &host,
                            owner,
                            Some(&query_context)
                        ),
                        Err(expected),
                        "warm={warm}, damage={damage}"
                    );
                    if warm {
                        assert_eq!(context.get_nongeneric_class_members(owner), Err(expected));
                        let provenance = context
                            .store()
                            .source_class_provenance_for_symbol(owner)
                            .unwrap();
                        assert!(
                            context
                                .store()
                                .source_class_annotation_scope(provenance.instance_type())
                                .is_none()
                        );
                        if damage == 0 || damage == 5 {
                            assert_eq!(
                                validate_source_class_stored_header(context.store(), provenance),
                                Err(invariant(ClassInvariant::InvalidInstanceMembers(owner)))
                            );
                        }
                    } else {
                        assert!(
                            context
                                .store()
                                .source_class_provenance_for_symbol(owner)
                                .is_none()
                        );
                        assert!(context.store().declared_type_links(owner).is_none());
                    }
                    assert_eq!(method_snapshot(&context), poisoned);
                }
                let store = context.store_mut_for_test();
                assert!(store.set_type_node_links(root, root_links));
                assert!(store.set_type_node_links(nested, nested_links));
                assert!(store.set_value_symbol_links(parameter.symbol, parameter_links));
                assert!(store.set_value_symbol_links(leaf, leaf_links));
                assert!(store.set_symbol_relationships(parameter.symbol, None, None, None, None));
                if let Some(members) = members {
                    assert_eq!(context.get_nongeneric_class_members(owner), Ok(members));
                } else {
                    // A valid nested query can precede the enclosing parameter query.
                    context.get_type_from_type_node(nested).unwrap();
                    assert_eq!(
                        plan_source_class_members_with_type_context(
                            context.store(),
                            &host,
                            owner,
                            Some(&query_context)
                        )
                        .unwrap(),
                        plan
                    );
                    context.check_source_file(FILE).unwrap();
                }
                assert!(
                    context.diagnostics().is_empty(),
                    "{:?}",
                    context.diagnostics()
                );
                let provenance = context
                    .store()
                    .source_class_provenance_for_symbol(owner)
                    .unwrap();
                assert!(provenance.complete);
                assert_eq!(provenance.prepared.plan, plan);
                assert_eq!(provenance.prepared.annotation_types.len(), 2);
                assert!(
                    context
                        .store()
                        .source_class_annotation_scope(provenance.instance_type())
                        .is_none()
                );
                let complete = method_snapshot(&context);
                context.recheck_source_file(FILE).unwrap();
                assert_eq!(method_snapshot(&context), complete);
            }
        }
    }

    const SELF_CLASS: &str = concat!(
        "class A { next: A | null = null; constructor(readonly children: (A | null)[]) {} }",
        "\nconst root = new A([]);\n",
    );

    fn self_class_owner(
        context: &CanonicalCheckerContext<'_>,
        source: &ParseResult,
    ) -> (NodeRef, SemanticSymbolId) {
        let (declaration, _) = source
            .arena
            .iter()
            .find(|(_, record)| record.kind == SyntaxKind::ClassDeclaration)
            .unwrap();
        let declaration = NodeRef::new(source.arena.id(), FILE, declaration);
        let owner = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
        (declaration, owner)
    }

    #[derive(Debug, Eq, PartialEq)]
    struct HeaderReplaySnapshot {
        lengths: [usize; 5],
        links: [usize; 26],
        provenance: SourceClassProvenance,
        annotations: Vec<(NodeRef, Option<TypeNodeLinks>, Option<SymbolNodeLinks>)>,
        values: Vec<(SemanticSymbolId, Option<ValueSymbolLinks>)>,
        source: Option<SourceFileLinks>,
        diagnostics: CanonicalCheckerDiagnostics,
    }

    fn header_replay_snapshot(
        context: &CanonicalCheckerContext<'_>,
        source: &ParseResult,
        owner: SemanticSymbolId,
    ) -> HeaderReplaySnapshot {
        let store = context.store();
        HeaderReplaySnapshot {
            lengths: [
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.symbol_store().symbol_table_len(),
            ],
            links: store.checker_link_allocated_lengths(),
            provenance: store
                .source_class_provenance_for_symbol(owner)
                .unwrap()
                .clone(),
            annotations: source
                .arena
                .iter()
                .map(|(node, _)| {
                    let node = NodeRef::new(source.arena.id(), FILE, node);
                    (
                        node,
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                    )
                })
                .collect(),
            values: store
                .symbol_store()
                .symbols()
                .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
                .collect(),
            source: store
                .source_file_links(context.source_file(FILE).unwrap())
                .cloned(),
            diagnostics: context.diagnostics().clone(),
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep both producer orders and exact cache damage with their restores.
    fn transparent_source_annotation_values_keep_child_and_owner_proofs() {
        let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parse_source_file(concat!(
            "interface Token { value: number; } ",
            "class Model { constructor(readonly token: (Token)) {} }",
        ));
        for source_first in [false, true] {
            let mut context = context(&library, &source);
            let (_, owner) = self_class_owner(&context, &source);
            let (parameter, syntax) = source
                .arena
                .iter()
                .find_map(|(node, record)| match &record.data {
                    NodeData::ParameterDeclaration(parameter) => {
                        Some((NodeRef::new(source.arena.id(), FILE, node), parameter))
                    }
                    _ => None,
                })
                .unwrap();
            let annotation = NodeRef::new(source.arena.id(), FILE, syntax.type_.unwrap());
            let NodeData::ParenthesizedTypeNode(parenthesized) =
                &source.arena.get(annotation.node).unwrap().data
            else {
                unreachable!()
            };
            let child = NodeRef::new(source.arena.id(), FILE, parenthesized.type_);
            let constructor = NodeRef::new(
                source.arena.id(),
                FILE,
                source.arena.get(parameter.node).unwrap().parent.unwrap(),
            );
            let library_bound = context.file(LIBRARY_FILE).unwrap().1.clone();
            let source_bound = context.file(FILE).unwrap().1.clone();
            let local = context
                .store()
                .symbol_table(source_bound.locals(constructor).unwrap())
                .unwrap()
                .get_source("token")
                .unwrap();
            let property = source_bound.symbol(parameter).unwrap();
            assert_ne!(local, property);
            let host = DeclaredTypeHost::new_after_global_merge(
                [
                    (&library.arena, &library_bound),
                    (&source.arena, &source_bound),
                ],
                GlobalMergeCompletion::for_test(context.options().name_resolution),
            )
            .unwrap();
            let query_context =
                ClassTypeQueryContext::new(context.global_types(), context.options());
            let snapshot = |context: &CanonicalCheckerContext<'_>| {
                let store = context.store();
                (
                    [
                        store.type_len(),
                        store.symbol_len(),
                        store.signature_len(),
                        store.mapper_len(),
                    ],
                    store.checker_link_allocated_lengths(),
                    [annotation, child].map(|node| {
                        (
                            store.type_node_links(node).cloned(),
                            store.symbol_node_links(node).cloned(),
                        )
                    }),
                    [local, property].map(|symbol| store.value_symbol_links(symbol).cloned()),
                    context.diagnostics().clone(),
                )
            };
            let cold = snapshot(&context);
            assert_eq!(
                validate_source_annotation_value_cache(
                    context.store(),
                    &host,
                    &query_context,
                    owner,
                    annotation,
                    local,
                ),
                Ok(())
            );
            assert_eq!(snapshot(&context), cold);
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            assert!(context.store_mut_for_test().set_value_symbol_links(
                local,
                ValueSymbolLinks {
                    resolved_type: Some(number),
                    ..ValueSymbolLinks::default()
                }
            ));
            let cold_damage = snapshot(&context);
            assert_eq!(
                validate_source_annotation_value_cache(
                    context.store(),
                    &host,
                    &query_context,
                    owner,
                    annotation,
                    local,
                ),
                Err(invariant(ClassInvariant::InvalidPropertyValueCache(local)))
            );
            assert_eq!(snapshot(&context), cold_damage);
            assert!(
                context
                    .store_mut_for_test()
                    .set_value_symbol_links(local, ValueSymbolLinks::default())
            );
            if source_first {
                context.check_source_file(FILE).unwrap();
            }
            let members = context.get_nongeneric_class_members(owner).unwrap();
            let value = context
                .store()
                .value_symbol_links(local)
                .unwrap()
                .resolved_type
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(property)
                    .unwrap()
                    .resolved_type,
                Some(value)
            );
            assert!(context.store().type_node_links(annotation).is_none());
            assert_eq!(
                context
                    .store()
                    .type_node_links(child)
                    .unwrap()
                    .resolved_type,
                Some(value)
            );
            let warm = snapshot(&context);
            for symbol in [local, property] {
                assert_eq!(
                    validate_source_annotation_value_cache(
                        context.store(),
                        &host,
                        &query_context,
                        owner,
                        annotation,
                        symbol,
                    ),
                    Ok(())
                );
            }
            assert_eq!(snapshot(&context), warm);
            for node in [child, annotation] {
                let original = context
                    .store()
                    .type_node_links(node)
                    .cloned()
                    .unwrap_or_default();
                assert!(context.store_mut_for_test().set_type_node_links(
                    node,
                    TypeNodeLinks {
                        resolved_type: Some(number),
                        ..TypeNodeLinks::default()
                    }
                ));
                let damaged = snapshot(&context);
                for _ in 0..2 {
                    assert!(matches!(
                        validate_source_annotation_value_cache(
                            context.store(),
                            &host,
                            &query_context,
                            owner,
                            annotation,
                            local,
                        ),
                        Err(ClassError::DeclaredType(_))
                    ));
                    assert_eq!(snapshot(&context), damaged);
                }
                assert!(
                    context
                        .store_mut_for_test()
                        .set_type_node_links(node, original)
                );
            }
            for symbol in [local, property] {
                let original = context.store().value_symbol_links(symbol).unwrap().clone();
                assert!(context.store_mut_for_test().set_value_symbol_links(
                    symbol,
                    ValueSymbolLinks {
                        resolved_type: Some(number),
                        ..ValueSymbolLinks::default()
                    }
                ));
                let damaged = snapshot(&context);
                assert_eq!(
                    validate_source_annotation_value_cache(
                        context.store(),
                        &host,
                        &query_context,
                        owner,
                        annotation,
                        symbol,
                    ),
                    Err(invariant(ClassInvariant::InvalidPropertyValueCache(symbol)))
                );
                assert_eq!(snapshot(&context), damaged);
                assert!(
                    context
                        .store_mut_for_test()
                        .set_value_symbol_links(symbol, original)
                );
            }
            let restored = snapshot(&context);
            assert_eq!(context.get_nongeneric_class_members(owner), Ok(members));
            assert_eq!(snapshot(&context), restored);
            assert!(context.store().type_resolution_is_empty());
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Both query orders share scope ownership, failure cleanup, and restore checks.
    fn member_queries_reopen_same_source_headers_and_close_only_owned_scopes() {
        let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parse_source_file(concat!(
            "class First { next: First | null = null; constructor(value: First | null) {} }\n",
            "class Second { next: Second | null = null; constructor(value: Second | null) {} }\n",
        ));
        for reverse in [false, true] {
            let mut context = context(&library, &source);
            let declarations = source
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    (record.kind == SyntaxKind::ClassDeclaration).then_some(NodeRef::new(
                        source.arena.id(),
                        FILE,
                        node,
                    ))
                })
                .collect::<Vec<_>>();
            let [first, second] = declarations.as_slice() else {
                unreachable!()
            };
            let owners =
                [*first, *second].map(|node| context.file(FILE).unwrap().1.symbol(node).unwrap());
            let order = if reverse { [1, 0] } else { [0, 1] };
            for index in order {
                context.get_nongeneric_class_members(owners[index]).unwrap();
            }
            let members = owners.map(|owner| context.get_nongeneric_class_members(owner).unwrap());
            let instances = members
                .each_ref()
                .map(|members| members.shells().instance_type());
            let before = owners.map(|owner| header_replay_snapshot(&context, &source, owner));
            for instance in instances {
                assert_eq!(
                    validate_class_heritage_members(context.store(), instance),
                    ClassHeritageMembersValidation::Malformed
                );
                assert!(
                    context
                        .store()
                        .source_class_annotation_scope(instance)
                        .is_none()
                );
            }
            let library_bound = context.file(LIBRARY_FILE).unwrap().1.clone();
            let source_bound = context.file(FILE).unwrap().1.clone();
            let globals = context.global_types().clone();
            let query_context = ClassTypeQueryContext::new(&globals, context.options());
            let host = DeclaredTypeHost::new_after_global_merge(
                [
                    (&library.arena, &library_bound),
                    (&source.arena, &source_bound),
                ],
                GlobalMergeCompletion::for_test(context.options().name_resolution),
            )
            .unwrap();
            let mut wrong = query_context.clone();
            wrong.options.strict_function_types = Some(!context.options().strict_function_types);
            let mut entered = false;
            assert_eq!(
                with_retained_source_class_annotation_scopes(
                    context.store_mut_for_test(),
                    &host,
                    &wrong,
                    owners[1],
                    |_| {
                        entered = true;
                        Ok(())
                    },
                ),
                Err(invariant(ClassInvariant::InvalidPlan(*first)))
            );
            assert!(!entered);
            assert_eq!(
                owners.map(|owner| header_replay_snapshot(&context, &source, owner)),
                before
            );

            assert_eq!(
                begin_retained_source_class_annotations(
                    context.store_mut_for_test(),
                    &host,
                    &query_context,
                    owners[0],
                ),
                Ok(Some(instances[0]))
            );
            assert_eq!(
                context.get_nongeneric_class_members(owners[1]),
                Ok(members[1].clone())
            );
            assert!(
                context
                    .store()
                    .source_class_annotation_scope(instances[0])
                    .is_some()
            );
            assert!(
                context
                    .store()
                    .source_class_annotation_scope(instances[1])
                    .is_none()
            );
            let failure = invariant(ClassInvariant::InvalidPlan(*second));
            assert_eq!(
                with_retained_source_class_annotation_scopes(
                    context.store_mut_for_test(),
                    &host,
                    &query_context,
                    owners[1],
                    |store| {
                        for instance in instances {
                            assert_eq!(
                                source_class_annotation_scope_targets(store, instance),
                                Some(CanonicalArrayTargets::from_global_types(&globals))
                            );
                        }
                        Err::<(), _>(failure)
                    },
                ),
                Err(failure)
            );
            assert!(
                context
                    .store()
                    .source_class_annotation_scope(instances[0])
                    .is_some()
            );
            assert!(
                context
                    .store()
                    .source_class_annotation_scope(instances[1])
                    .is_none()
            );
            assert!(
                context
                    .store_mut_for_test()
                    .end_source_class_annotation_scope(instances[0])
            );

            let annotation = context
                .store()
                .source_class_provenance_for_symbol(owners[1])
                .unwrap()
                .prepared
                .plan
                .initialized_properties[0]
                .type_node;
            let original = context.store().type_node_links(annotation).unwrap().clone();
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            assert!(context.store_mut_for_test().set_type_node_links(
                annotation,
                TypeNodeLinks {
                    resolved_type: Some(number),
                    ..TypeNodeLinks::default()
                }
            ));
            let damaged = owners.map(|owner| header_replay_snapshot(&context, &source, owner));
            for _ in 0..2 {
                assert!(context.get_nongeneric_class_members(owners[0]).is_err());
                for instance in instances {
                    assert!(
                        context
                            .store()
                            .source_class_annotation_scope(instance)
                            .is_none()
                    );
                }
                assert_eq!(
                    owners.map(|owner| header_replay_snapshot(&context, &source, owner)),
                    damaged
                );
            }
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_node_links(annotation, original)
            );
            for (owner, members) in owners.into_iter().zip(members) {
                assert_eq!(context.get_nongeneric_class_members(owner), Ok(members));
            }
            assert_eq!(
                owners.map(|owner| header_replay_snapshot(&context, &source, owner)),
                before
            );
            assert!(context.store().type_resolution_is_empty());
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the independently bound foreign source and both authority checks together.
    fn member_query_scopes_do_not_admit_pending_headers_from_other_sources() {
        let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parse_source_file(
            "class Local { next: Local | null = null; constructor(value: Local | null) {} }",
        );
        let foreign = parse_source_file(
            "class Foreign { next: Foreign | null = null; constructor(value: Foreign | null) {} }",
        );
        let foreign_file = FileId::new(202_454);
        let mut binder = CanonicalBinder::new();
        for (parsed, file, path, is_library) in [
            (&library, LIBRARY_FILE, "\"/lib.d.ts\"", true),
            (&source, FILE, "\"/local.ts\"", false),
            (&foreign, foreign_file, "\"/foreign.ts\"", false),
        ] {
            assert!(parsed.diagnostics.is_empty());
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        is_library,
                        is_library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_property_initialization: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        };
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![
                (LIBRARY_FILE, &library.arena),
                (FILE, &source.arena),
                (foreign_file, &foreign.arena),
            ],
            options,
        )
        .unwrap();
        let (_, local_owner) = self_class_owner(&context, &source);
        let foreign_declaration = foreign
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ClassDeclaration).then_some(NodeRef::new(
                    foreign.arena.id(),
                    foreign_file,
                    node,
                ))
            })
            .unwrap();
        let foreign_owner = context
            .file(foreign_file)
            .unwrap()
            .1
            .symbol(foreign_declaration)
            .unwrap();
        let members = context.get_nongeneric_class_members(foreign_owner).unwrap();
        let instance = members.shells().instance_type();
        let globals = context.global_types().clone();
        let query_context = ClassTypeQueryContext::new(&globals, options);
        let library_bound = context.file(LIBRARY_FILE).unwrap().1.clone();
        let source_bound = context.file(FILE).unwrap().1.clone();
        let foreign_bound = context.file(foreign_file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, &library_bound),
                (&source.arena, &source_bound),
                (&foreign.arena, &foreign_bound),
            ],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            let store = context.store();
            (
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.checker_link_allocated_lengths(),
                store
                    .source_class_provenance_for_symbol(foreign_owner)
                    .cloned(),
                store.declared_type_links(local_owner).cloned(),
                context.diagnostics().clone(),
            )
        };
        let before = snapshot(&context);
        let targets = CanonicalArrayTargets::from_global_types(&globals);
        for _ in 0..2 {
            assert_eq!(
                with_retained_source_class_annotation_scopes(
                    context.store_mut_for_test(),
                    &host,
                    &query_context,
                    local_owner,
                    |store| {
                        assert!(store.source_class_annotation_scope(instance).is_none());
                        assert_eq!(
                            validate_class_heritage_members(store, instance),
                            ClassHeritageMembersValidation::Malformed
                        );
                        assert_eq!(
                            store.validate_union_constituent_with_array_targets(targets, instance),
                            Err(LiteralTypeCacheError::InvalidCachedUnion(instance))
                        );
                        Ok(())
                    },
                ),
                Ok(())
            );
            assert_eq!(snapshot(&context), before);
            assert_eq!(
                with_retained_source_class_annotation_scopes(
                    context.store_mut_for_test(),
                    &host,
                    &query_context,
                    foreign_owner,
                    |store| {
                        assert_eq!(
                            source_class_annotation_scope_targets(store, instance),
                            Some(targets)
                        );
                        assert_eq!(
                            store.validate_union_constituent_with_array_targets(targets, instance),
                            Ok(())
                        );
                        Ok(())
                    },
                ),
                Ok(())
            );
            assert!(
                context
                    .store()
                    .source_class_annotation_scope(instance)
                    .is_none()
            );
            assert_eq!(snapshot(&context), before);
        }
    }

    #[test]
    fn source_class_header_retry_scopes_keep_exact_owner_and_caller_options() {
        let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parse_source_file(SELF_CLASS);
        let mut context = context(&library, &source);
        let (declaration, owner) = self_class_owner(&context, &source);
        let members = context.get_nongeneric_class_members(owner).unwrap();
        let instance = members.shells().instance_type();
        let plan = context
            .store()
            .source_class_provenance_for_symbol(owner)
            .unwrap()
            .prepared
            .plan
            .clone();
        let options = context.options();
        let globals = context.global_types().clone();
        let query_context = ClassTypeQueryContext::new(&globals, options);
        let library_bound = context.file(LIBRARY_FILE).unwrap().1.clone();
        let source_bound = context.file(FILE).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, &library_bound),
                (&source.arena, &source_bound),
            ],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let before = header_replay_snapshot(&context, &source, owner);
        assert!(!before.provenance.complete);
        assert!(
            before
                .provenance
                .completed_bodies
                .iter()
                .all(|complete| !complete)
        );
        assert_eq!(before.provenance.property_types, [None]);

        let mut wrong_options = query_context.clone();
        wrong_options.options.strict_function_types = Some(!options.strict_function_types);
        let mut wrong_globals = query_context.clone();
        wrong_globals.global_types.array_type =
            context.store().intrinsic_bootstrap().unwrap().string_type;
        for wrong in [wrong_options, wrong_globals] {
            assert_eq!(
                begin_retained_source_class_annotations(
                    context.store_mut_for_test(),
                    &host,
                    &wrong,
                    owner,
                ),
                Err(invariant(ClassInvariant::InvalidPlan(declaration)))
            );
            assert!(
                context
                    .store()
                    .source_class_annotation_scope(instance)
                    .is_none()
            );
            assert_eq!(header_replay_snapshot(&context, &source, owner), before);
        }
        assert_eq!(
            begin_retained_source_class_annotations(
                context.store_mut_for_test(),
                &host,
                &query_context,
                owner,
            ),
            Ok(Some(instance))
        );
        assert_eq!(
            source_class_annotation_scope_targets(context.store(), instance),
            Some(CanonicalArrayTargets::from_global_types(&globals))
        );
        assert_eq!(
            begin_source_class_annotations(context.store_mut_for_test(), &host, &globals, &plan),
            Ok(None)
        );
        assert_eq!(
            context.get_nongeneric_class_members(owner).unwrap(),
            members
        );
        assert!(
            context
                .store()
                .source_class_annotation_scope(instance)
                .is_some()
        );
        assert!(
            context
                .store_mut_for_test()
                .end_source_class_annotation_scope(instance)
        );
        assert!(
            context
                .store()
                .source_class_annotation_scope(instance)
                .is_none()
        );
        assert_eq!(header_replay_snapshot(&context, &source, owner), before);
        let next = plan.initialized_properties[0].type_node;
        assert_eq!(
            context.get_type_from_type_node(next),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::InvalidCachedUnionType(instance)
            ))
        );
        assert_eq!(header_replay_snapshot(&context, &source, owner), before);
    }

    #[test]
    fn source_class_header_retry_rejects_changed_pending_field_cache() {
        let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parse_source_file(SELF_CLASS);
        let mut context = context(&library, &source);
        let (declaration, owner) = self_class_owner(&context, &source);
        let members = context.get_nongeneric_class_members(owner).unwrap();
        let instance = members.shells().instance_type();
        let property = context
            .store()
            .symbol_table(members.instance_members().unwrap())
            .unwrap()
            .get_source("children")
            .unwrap();
        let original = context
            .store()
            .value_symbol_links(property)
            .cloned()
            .unwrap();
        assert!(original.resolved_type.is_some());
        let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(wrong),
                ..ValueSymbolLinks::default()
            }
        ));
        let poisoned = header_replay_snapshot(&context, &source, owner);
        for _ in 0..2 {
            assert_eq!(
                context.get_nongeneric_class_members(owner),
                Err(invariant(ClassInvariant::InvalidInstanceMembers(owner)))
            );
            assert_eq!(
                context.check_source_file(FILE),
                Err(crate::semantic::SourceCheckError::Class(declaration))
            );
            assert!(
                context
                    .store()
                    .source_class_annotation_scope(instance)
                    .is_none()
            );
            assert_eq!(header_replay_snapshot(&context, &source, owner), poisoned);
        }
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(property, original)
        );
        assert_eq!(
            context.get_nongeneric_class_members(owner).unwrap(),
            members
        );
        context.check_source_file(FILE).unwrap();
        assert!(context.diagnostics().is_empty());
        assert!(
            context
                .store()
                .source_class_annotation_scope(instance)
                .is_none()
        );
        let completed = header_replay_snapshot(&context, &source, owner);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(header_replay_snapshot(&context, &source, owner), completed);
    }

    #[test]
    fn source_class_header_retry_closes_scope_after_array_cache_failure() {
        let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parse_source_file(SELF_CLASS);
        let mut context = context(&library, &source);
        let (_, owner) = self_class_owner(&context, &source);
        let members = context.get_nongeneric_class_members(owner).unwrap();
        let instance = members.shells().instance_type();
        let provenance = context
            .store()
            .source_class_provenance_for_symbol(owner)
            .unwrap()
            .clone();
        let (annotation, array) = provenance
            .prepared
            .annotation_types
            .iter()
            .copied()
            .find(|(node, _)| source.arena.get(node.node).unwrap().kind == SyntaxKind::ArrayType)
            .unwrap();
        let TypeData::TypeReference(reference) =
            context.store().type_payload(array).unwrap().data()
        else {
            unreachable!()
        };
        let original = (reference.node, reference.resolved_type_arguments.clone());
        let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_type_reference_resolution(
            array,
            original.0,
            Some(vec![wrong])
        ));
        // The retained IDs still match. Only source replay can reject this array.
        assert_eq!(
            validate_source_class_stored_header(context.store(), &provenance),
            Ok(())
        );
        let poisoned = header_replay_snapshot(&context, &source, owner);
        let error = DeclaredTypeError::TypeNodeUnavailable(
            TypeNodeUnavailable::InvalidTypeReference(annotation),
        );
        for _ in 0..2 {
            assert_eq!(
                context.get_nongeneric_class_members(owner),
                Err(ClassError::DeclaredType(error))
            );
            assert_eq!(
                context.check_source_file(FILE),
                Err(crate::semantic::SourceCheckError::DeclaredType(error))
            );
            assert!(
                context
                    .store()
                    .source_class_annotation_scope(instance)
                    .is_none()
            );
            assert_eq!(header_replay_snapshot(&context, &source, owner), poisoned);
        }
        assert!(
            context
                .store_mut_for_test()
                .set_type_reference_resolution(array, original.0, original.1)
        );
        assert_eq!(
            context.get_nongeneric_class_members(owner).unwrap(),
            members
        );
        context.check_source_file(FILE).unwrap();
        assert!(context.diagnostics().is_empty());
        let completed = header_replay_snapshot(&context, &source, owner);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(header_replay_snapshot(&context, &source, owner), completed);
    }

    #[test]
    fn completed_class_annotations_reject_coherent_cached_type_replacement() {
        let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parse_source_file(concat!(
            "class Leaf {} ",
            "class Model { values!: number[]; others!: (Leaf | null)[]; next: Model | null = null; }",
        ));
        let mut context = context(&library, &source);
        let (declaration, _) = source
            .arena
            .iter()
            .find(|(_, record)| {
                matches!(&record.data, NodeData::ClassDeclaration(class)
                    if class.name.is_some_and(|name| matches!(&source.arena.get(name).unwrap().data,
                        NodeData::Identifier(identifier) if identifier.text == "Model")))
            })
            .unwrap();
        let declaration = NodeRef::new(source.arena.id(), FILE, declaration);
        let owner = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let provenance = context
            .store()
            .source_class_provenance_for_symbol(owner)
            .unwrap()
            .clone();
        let instance = provenance.instance_type();
        assert!(
            context
                .store()
                .source_class_annotation_scope(instance)
                .is_none()
        );
        assert_eq!(
            validate_class_heritage_members(context.store(), instance),
            ClassHeritageMembersValidation::Valid
        );
        let leaf = context
            .store()
            .symbol_table(context.globals())
            .unwrap()
            .get_source("Leaf")
            .unwrap();
        let leaf_type = context
            .store()
            .declared_type_links(leaf)
            .unwrap()
            .declared_type
            .unwrap();
        assert!(completed_class_symbol(context.store(), leaf));
        let others = context
            .store()
            .symbol_table(context.store().symbol(owner).unwrap().members().unwrap())
            .unwrap()
            .get_source("others")
            .unwrap();
        let others = context
            .store()
            .value_symbol_links(others)
            .unwrap()
            .resolved_type
            .unwrap();
        let TypeData::TypeReference(reference) =
            context.store().type_payload(others).unwrap().data()
        else {
            panic!("the prior class field uses the canonical array reference")
        };
        assert_eq!(
            reference.object.target,
            Some(context.global_types().array_type)
        );
        let [element] = reference.resolved_type_arguments.as_deref().unwrap() else {
            unreachable!()
        };
        let TypeData::Union(union) = context.store().type_payload(*element).unwrap().data() else {
            panic!("the prior class remains a member of the element union")
        };
        assert_eq!(
            union.union.types,
            [
                context.store().intrinsic_bootstrap().unwrap().null_type,
                leaf_type
            ]
        );
        let property = context
            .store()
            .symbol_table(context.store().symbol(owner).unwrap().members().unwrap())
            .unwrap()
            .get_source("values")
            .unwrap();
        let declaration = context
            .store()
            .symbol(property)
            .unwrap()
            .value_declaration()
            .unwrap();
        let NodeData::PropertyDeclaration(data) = &source.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let annotation = NodeRef::new(source.arena.id(), FILE, data.type_.unwrap());
        let original_node = context.store().type_node_links(annotation).unwrap().clone();
        let original_value = context
            .store()
            .value_symbol_links(property)
            .unwrap()
            .clone();
        let TypeData::TypeReference(reference) = context
            .store()
            .type_payload(original_node.resolved_type.unwrap())
            .unwrap()
            .data()
        else {
            panic!("the declared field uses the real array reference")
        };
        assert_eq!(
            reference.object.target,
            Some(context.global_types().array_type)
        );
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(&[context.store().intrinsic_bootstrap().unwrap().number_type][..])
        );
        let array_type = original_node.resolved_type.unwrap();
        let original_resolution = (reference.node, reference.resolved_type_arguments.clone());
        let targets = CanonicalArrayTargets::from_global_types(context.global_types());
        assert_eq!(
            context
                .store()
                .validate_union_constituent_with_array_targets(targets, instance),
            Ok(())
        );
        assert_eq!(
            context.store().validate_union_constituent(instance),
            Err(LiteralTypeCacheError::UnsupportedUnionConstituent(
                array_type
            ))
        );
        let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context
                    .store()
                    .source_file_links(context.source_file(FILE).unwrap())
                    .cloned(),
                context.diagnostics().clone(),
            )
        };
        let before = snapshot(&context);
        let leaf_links = context.store().declared_type_links(leaf).unwrap().clone();
        let mut foreign_owner = leaf_links.clone();
        foreign_owner.declared_type = Some(instance);
        assert!(
            context
                .store_mut_for_test()
                .set_declared_type_links(leaf, foreign_owner.clone())
        );
        for _ in 0..2 {
            assert!(!completed_class_symbol(context.store(), leaf));
            assert_eq!(
                context.store().declared_type_links(leaf),
                Some(&foreign_owner)
            );
            assert_eq!(snapshot(&context), before);
        }
        assert!(
            context
                .store_mut_for_test()
                .set_declared_type_links(leaf, leaf_links)
        );
        assert!(completed_class_symbol(context.store(), leaf));
        assert!(context.store_mut_for_test().set_type_reference_resolution(
            array_type,
            original_resolution.0,
            Some(vec![wrong])
        ));
        assert!(matches!(
            context.store().validate_union_constituent_with_array_targets(targets, instance),
            Err(LiteralTypeCacheError::ArrayType { type_, .. }) if type_ == array_type
        ));
        assert_eq!(snapshot(&context), before);
        assert!(context.store_mut_for_test().set_type_reference_resolution(
            array_type,
            original_resolution.0,
            original_resolution.1
        ));
        assert_eq!(
            context
                .store()
                .validate_union_constituent_with_array_targets(targets, instance),
            Ok(())
        );
        assert!(context.store_mut_for_test().set_type_node_links(
            annotation,
            TypeNodeLinks {
                resolved_type: Some(wrong),
                ..TypeNodeLinks::default()
            }
        ));
        assert!(context.store_mut_for_test().set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(wrong),
                ..ValueSymbolLinks::default()
            }
        ));
        for _ in 0..2 {
            assert_eq!(
                validate_source_class_stored_header(context.store(), &provenance),
                Err(invariant(ClassInvariant::InvalidInstanceMembers(owner)))
            );
            assert!(!completed_class_symbol(context.store(), owner));
            assert_eq!(
                validate_class_heritage_members(context.store(), instance),
                ClassHeritageMembersValidation::Malformed
            );
            assert_eq!(snapshot(&context), before);
        }
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(annotation, original_node)
        );
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(property, original_value)
        );
        assert_eq!(
            validate_source_class_stored_header(context.store(), &provenance),
            Ok(())
        );
        assert!(completed_class_symbol(context.store(), owner));
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(snapshot(&context), before);
        assert!(
            context
                .store()
                .source_class_annotation_scope(instance)
                .is_none()
        );
    }
}
