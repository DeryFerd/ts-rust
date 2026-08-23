//! Exact source integration for one admitted class construction.
//!
//! This is the dependency-closed `new Model()`, `new Model`, and single-literal
//! constructor branch of pinned TypeScript-Go `checkCallExpression`,
//! `getResolvedSignature`, `resolveNewExpression`, and `resolveCall`. The
//! admitted constructor belongs to one preceding local class and has either no
//! parameters or one authenticated required `string` or `number` parameter.
//! Planning proves the syntax, resolver route, class provenance, and cold/warm
//! caches before source execution may publish class or expression state.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation,
    CheckFlags, SemanticSymbolId, SymbolFlags,
};
use ts_jsnum::Number;

use super::{
    CanonicalTypeMapperStore, ClassError, DeclaredTypeError, DeclaredTypeHost,
    ResolvedSignatureState, SignatureId, SignatureLinks, SymbolNodeLinks, TypeData, TypeId,
    TypeNodeLinks, ValueSymbolLinks,
    bootstrap::LiteralTypeCacheError,
    classes::{
        ClassConstructorVisibility, ClassMemberPlan, ClassMemberQueryPlan,
        execute_nongeneric_class_member_query, plan_nongeneric_class_member_query,
        preflight_nongeneric_class_member_query,
    },
    signatures::SignatureFlags,
    type_nodes::normalize_numeric_separators,
};

/// A valid construction form outside the exact default-class leaf.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceNewUnsupported {
    Expression(NodeRef),
    Constructor(NodeRef),
    MissingArgumentList(NodeRef),
    Arguments(NodeRef),
    TypeArguments(NodeRef),
    ConstructorClass {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    ConstructorNotPrior {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
}

/// Malformed AST, binder, class, or checker-cache provenance.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceNewInvariant {
    MissingNode(NodeRef),
    NameResolution {
        node: NodeRef,
        error: CanonicalNameResolutionError,
    },
    InvalidSymbol(SemanticSymbolId),
    DuplicatePlan(NodeRef),
    MergedSymbol {
        source: SemanticSymbolId,
        target: SemanticSymbolId,
    },
    InvalidClassPlan(NodeRef),
    InvalidConstructorCache(NodeRef),
    InvalidExpressionCache(NodeRef),
    InvalidClassValue(SemanticSymbolId),
    InvalidConstructSignature(SignatureId),
    Capacity(NodeRef),
}

/// Exact failure domain for direct default construction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceNewError {
    Unsupported(SourceNewUnsupported),
    Invariant(SourceNewInvariant),
    DeclaredType(DeclaredTypeError),
    Class(ClassError),
}

impl SourceNewError {
    pub(super) const fn node(self) -> Option<NodeRef> {
        match self {
            Self::Unsupported(unsupported) => Some(match unsupported {
                SourceNewUnsupported::Expression(node)
                | SourceNewUnsupported::Constructor(node)
                | SourceNewUnsupported::MissingArgumentList(node)
                | SourceNewUnsupported::Arguments(node)
                | SourceNewUnsupported::TypeArguments(node)
                | SourceNewUnsupported::ConstructorClass { node, .. }
                | SourceNewUnsupported::ConstructorNotPrior { node, .. } => node,
            }),
            Self::Invariant(invariant) => match invariant {
                SourceNewInvariant::MissingNode(node)
                | SourceNewInvariant::DuplicatePlan(node)
                | SourceNewInvariant::NameResolution { node, .. }
                | SourceNewInvariant::InvalidClassPlan(node)
                | SourceNewInvariant::InvalidConstructorCache(node)
                | SourceNewInvariant::InvalidExpressionCache(node)
                | SourceNewInvariant::Capacity(node) => Some(node),
                SourceNewInvariant::InvalidSymbol(_)
                | SourceNewInvariant::MergedSymbol { .. }
                | SourceNewInvariant::InvalidClassValue(_)
                | SourceNewInvariant::InvalidConstructSignature(_) => None,
            },
            Self::Class(error) => error.node(),
            Self::DeclaredType(_) => None,
        }
    }
}

impl From<DeclaredTypeError> for SourceNewError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<ClassError> for SourceNewError {
    fn from(error: ClassError) -> Self {
        Self::Class(error)
    }
}

const fn unsupported(reason: SourceNewUnsupported) -> SourceNewError {
    SourceNewError::Unsupported(reason)
}

const fn invariant(reason: SourceNewInvariant) -> SourceNewError {
    SourceNewError::Invariant(reason)
}

/// Opaque syntax, resolver, and class proof for one default construction.
#[derive(Clone, Debug)]
pub(super) struct SourceDefaultNewPlan {
    node: NodeRef,
    constructor: NodeRef,
    resolved_symbol: SemanticSymbolId,
    class: ClassMemberQueryPlan,
    argument: Option<SourceNewArgument>,
    parameter: Option<SourceNewParameter>,
}

#[derive(Clone, Debug)]
struct SourceNewArgument {
    node: NodeRef,
    value: SourceNewArgumentValue,
}

#[derive(Clone, Debug)]
enum SourceNewArgumentValue {
    String(String),
    Number(Number),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SourceNewParameter {
    symbol: SemanticSymbolId,
    type_: TypeId,
}

impl SourceDefaultNewPlan {
    pub(super) const fn node(&self) -> NodeRef {
        self.node
    }

    pub(super) const fn constructor(&self) -> NodeRef {
        self.constructor
    }

    pub(super) const fn resolved_symbol(&self) -> SemanticSymbolId {
        self.resolved_symbol
    }
}

/// Exact selected signature and result of one default construction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CheckedSourceDefaultNew {
    pub(super) value_type: TypeId,
    pub(super) instance_type: TypeId,
    pub(super) signature: SignatureId,
}

/// Proves the complete direct-new syntax and its preceding local class.
#[allow(clippy::too_many_arguments)]
pub(super) fn plan_direct_default_new(
    arena: &NodeArena,
    bound: &BoundFile,
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    prior_classes: &HashMap<SemanticSymbolId, ClassMemberPlan>,
    node: NodeRef,
) -> Result<SourceDefaultNewPlan, SourceNewError> {
    let record = arena
        .get(node.node)
        .ok_or_else(|| invariant(SourceNewInvariant::MissingNode(node)))?;
    let NodeData::NewExpression(new_expression) = &record.data else {
        return Err(unsupported(SourceNewUnsupported::Expression(node)));
    };
    if record.kind != SyntaxKind::NewExpression || record.flags.0 != 0 || new_expression.facts != 0
    {
        return Err(unsupported(SourceNewUnsupported::Expression(node)));
    }
    if new_expression.type_arguments.is_some() {
        return Err(unsupported(SourceNewUnsupported::TypeArguments(node)));
    }
    let mut argument = None;
    let argument_start = match new_expression.arguments.as_ref() {
        Some(arguments) => {
            if arguments.nodes.len() > 1
                || arguments.has_trailing_comma
                || arguments.range.start < record.range.start
                || arguments.range.end != record.range.end
                || arguments.range.end.get() < arguments.range.start.get().saturating_add(2)
                || arena.source_text().is_some_and(|source| {
                    let open = usize::try_from(arguments.range.start.get()).ok();
                    let close = usize::try_from(arguments.range.end.get().saturating_sub(1)).ok();
                    open.is_none_or(|open| source.as_bytes().get(open) != Some(&b'('))
                        || close.is_none_or(|close| source.as_bytes().get(close) != Some(&b')'))
                })
            {
                return Err(unsupported(SourceNewUnsupported::Arguments(node)));
            }
            if let Some(&argument_node) = arguments.nodes.first() {
                let argument_node = NodeRef::new(node.arena, node.file, argument_node);
                let argument_record = arena
                    .get(argument_node.node)
                    .ok_or_else(|| invariant(SourceNewInvariant::MissingNode(argument_node)))?;
                let value = match &argument_record.data {
                    NodeData::StringLiteral(literal)
                        if argument_record.kind == SyntaxKind::StringLiteral
                            && literal.token_flags.0 == 0 =>
                    {
                        SourceNewArgumentValue::String(literal.text.clone())
                    }
                    NodeData::NumericLiteral(literal)
                        if argument_record.kind == SyntaxKind::NumericLiteral
                            && literal.token_flags.0 == 0 =>
                    {
                        let value = ts_jsnum::from_string(&literal.text);
                        let spelling_valid = arena.source_text().is_none_or(|source| {
                            let start = usize::try_from(argument_record.range.start.get()).ok();
                            let end = usize::try_from(argument_record.range.end.get()).ok();
                            start
                                .zip(end)
                                .and_then(|(start, end)| source.get(start..end))
                                .and_then(normalize_numeric_separators)
                                .is_some_and(|spelling| {
                                    let source_value = ts_jsnum::from_string(&spelling);
                                    !source_value.is_nan() && source_value == value
                                })
                        });
                        if value.is_nan() || !spelling_valid {
                            return Err(unsupported(SourceNewUnsupported::Arguments(node)));
                        }
                        SourceNewArgumentValue::Number(value)
                    }
                    _ => return Err(unsupported(SourceNewUnsupported::Arguments(node))),
                };
                if argument_record.flags.0 != 0
                    || argument_record.parent != Some(node.node)
                    || argument_record.range.start <= arguments.range.start
                    || argument_record.range.end >= arguments.range.end
                    || !bound.contains(argument_node)
                {
                    return Err(unsupported(SourceNewUnsupported::Arguments(node)));
                }
                argument = Some(SourceNewArgument {
                    node: argument_node,
                    value,
                });
            }
            arguments.range.start
        }
        None => record.range.end,
    };

    let constructor = NodeRef::new(node.arena, node.file, new_expression.expression);
    let constructor_record = arena
        .get(constructor.node)
        .ok_or_else(|| invariant(SourceNewInvariant::MissingNode(constructor)))?;
    let NodeData::Identifier(identifier) = &constructor_record.data else {
        return Err(unsupported(SourceNewUnsupported::Constructor(constructor)));
    };
    if constructor_record.kind != SyntaxKind::Identifier
        || constructor_record.flags.0 != 0
        || constructor_record.parent != Some(node.node)
        || constructor_record.range.start < record.range.start
        || constructor_record.range.end > argument_start
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(unsupported(SourceNewUnsupported::Constructor(constructor)));
    }
    if new_expression.arguments.is_none() && constructor_record.range.end != record.range.end {
        return Err(unsupported(SourceNewUnsupported::MissingArgumentList(node)));
    }

    let mut callback_host = host.name_resolver_host(store)?;
    let mut resolver =
        CanonicalNameResolver::new(arena, bound, store.symbol_store(), &mut callback_host)
            .map_err(|error| {
                invariant(SourceNewInvariant::NameResolution {
                    node: constructor,
                    error,
                })
            })?;
    let resolved_symbol = match resolver.resolve(
        Some(CanonicalResolutionLocation::Bound(constructor)),
        &identifier.text,
        SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
        None,
        false,
        false,
    ) {
        Ok(Some(symbol)) => symbol,
        Ok(None) | Err(CanonicalNameResolutionError::AliasResolutionUnavailable(_)) => {
            return Err(unsupported(SourceNewUnsupported::Constructor(constructor)));
        }
        Err(error) => {
            return Err(invariant(SourceNewInvariant::NameResolution {
                node: constructor,
                error,
            }));
        }
    };
    let symbol = store
        .get_merged_symbol(resolved_symbol)
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidSymbol(resolved_symbol)))?;
    if symbol != resolved_symbol {
        return Err(invariant(SourceNewInvariant::MergedSymbol {
            source: resolved_symbol,
            target: symbol,
        }));
    }
    let symbol_record = store
        .symbol(symbol)
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidSymbol(symbol)))?;
    if symbol_record.flags() != SymbolFlags::CLASS
        || symbol_record.check_flags() != CheckFlags::NONE
    {
        return Err(unsupported(SourceNewUnsupported::ConstructorClass {
            node: constructor,
            symbol,
        }));
    }
    let class = if let Some(class) = prior_classes.get(&symbol) {
        ClassMemberQueryPlan::Direct(class.clone())
    } else {
        let class = plan_nongeneric_class_member_query(store, host, symbol)?;
        let ClassMemberQueryPlan::Derived {
            class: derived,
            base,
        } = &class
        else {
            return Err(unsupported(SourceNewUnsupported::ConstructorNotPrior {
                node: constructor,
                symbol,
            }));
        };
        let declaration = derived.declaration();
        if !declaration.is_for(node.arena, node.file) {
            return Err(unsupported(SourceNewUnsupported::ConstructorNotPrior {
                node: constructor,
                symbol,
            }));
        }
        let declaration_record = arena
            .get(declaration.node)
            .ok_or_else(|| invariant(SourceNewInvariant::MissingNode(declaration)))?;
        if declaration_record.range.end > record.range.start
            || prior_classes.get(&base.symbol()) != Some(base.as_ref())
        {
            return Err(unsupported(SourceNewUnsupported::ConstructorNotPrior {
                node: constructor,
                symbol,
            }));
        }
        class
    };
    if class.symbol() != symbol {
        return Err(invariant(SourceNewInvariant::InvalidClassPlan(
            class.declaration(),
        )));
    }
    if class.constructor_visibility() != ClassConstructorVisibility::Public {
        return Err(unsupported(SourceNewUnsupported::ConstructorClass {
            node: constructor,
            symbol,
        }));
    }
    preflight_nongeneric_class_member_query(store, host, &class)?;
    let parameter = constructor_parameter(store, host, &class)?;
    if argument.is_some() != parameter.is_some()
        || argument.is_some() && class.direct_plan().is_none()
        || argument
            .as_ref()
            .zip(parameter)
            .is_some_and(|(argument, parameter)| {
                !argument_matches_parameter(store, argument, parameter)
            })
    {
        return Err(unsupported(SourceNewUnsupported::Arguments(node)));
    }

    let plan = SourceDefaultNewPlan {
        node,
        constructor,
        resolved_symbol,
        class,
        argument,
        parameter,
    };
    preflight_default_new_cache(store, &plan)?;
    Ok(plan)
}

fn constructor_parameter(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    class: &ClassMemberQueryPlan,
) -> Result<Option<SourceNewParameter>, SourceNewError> {
    let Some(declaration) = class.constructor_declaration() else {
        return Ok(None);
    };
    let invalid = || invariant(SourceNewInvariant::InvalidClassPlan(declaration));
    let constructor = host.node(declaration).ok_or_else(invalid)?;
    let NodeData::ConstructorDeclaration(constructor_data) = &constructor.data else {
        return Err(invalid());
    };
    let parameter = match constructor_data.parameters.nodes.as_slice() {
        [] => return Ok(None),
        [parameter] => NodeRef::new(declaration.arena, declaration.file, *parameter),
        _ => return Err(invalid()),
    };
    let parameter_record = host.node(parameter).ok_or_else(invalid)?;
    let NodeData::ParameterDeclaration(parameter_data) = &parameter_record.data else {
        return Err(invalid());
    };
    let type_node = parameter_data
        .type_
        .map(|node| NodeRef::new(parameter.arena, parameter.file, node))
        .ok_or_else(invalid)?;
    let type_record = host.node(type_node).ok_or_else(invalid)?;
    let raw = host
        .bound_file(parameter)
        .and_then(|bound| bound.symbol(parameter))
        .ok_or_else(invalid)?;
    let symbol = store.get_merged_symbol(raw).ok_or_else(invalid)?;
    let symbol_record = store.symbol(symbol).ok_or_else(invalid)?;
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    let type_ = match type_record.kind {
        SyntaxKind::StringKeyword => bootstrap.string_type,
        SyntaxKind::NumberKeyword => bootstrap.number_type,
        _ => return Err(invalid()),
    };
    if constructor.kind != SyntaxKind::Constructor
        || parameter_record.kind != SyntaxKind::Parameter
        || parameter_record.parent != Some(declaration.node)
        || type_record.parent != Some(parameter.node)
        || !matches!(type_record.data, NodeData::KeywordTypeNode(_))
        || raw != symbol
        || symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.declarations() != Some(&[parameter])
        || symbol_record.value_declaration() != Some(parameter)
    {
        return Err(invalid());
    }
    Ok(Some(SourceNewParameter { symbol, type_ }))
}

fn argument_matches_parameter(
    store: &CanonicalTypeMapperStore,
    argument: &SourceNewArgument,
    parameter: SourceNewParameter,
) -> bool {
    store.intrinsic_bootstrap().is_some_and(|bootstrap| {
        parameter.type_
            == match &argument.value {
                SourceNewArgumentValue::String(_) => bootstrap.string_type,
                SourceNewArgumentValue::Number(_) => bootstrap.number_type,
            }
    })
}

/// Revalidates the class and all observable cold/warm construction caches.
pub(super) fn preflight_direct_default_new(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
) -> Result<(), SourceNewError> {
    preflight_nongeneric_class_member_query(store, host, &plan.class)?;
    if constructor_parameter(store, host, &plan.class)? != plan.parameter {
        return Err(invariant(SourceNewInvariant::InvalidClassPlan(
            plan.class.declaration(),
        )));
    }
    preflight_default_new_cache(store, plan)
}

/// Revalidates every retained construction before reserving any sparse link
/// capacity, then installs only empty default slots. No class execution may
/// begin until this whole-file phase succeeds for every plan.
pub(super) fn prepare_direct_default_news(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plans: &[SourceDefaultNewPlan],
) -> Result<(), SourceNewError> {
    let Some(capacity_node) = plans.first().map(|plan| plan.node) else {
        return Ok(());
    };
    let mut seen = HashSet::new();
    seen.try_reserve(plans.len())
        .map_err(|_| invariant(SourceNewInvariant::Capacity(capacity_node)))?;
    for plan in plans {
        if !seen.insert(plan.node) {
            return Err(invariant(SourceNewInvariant::DuplicatePlan(plan.node)));
        }
        preflight_direct_default_new(store, host, plan)?;
    }

    let mut strings = Vec::new();
    let mut numbers = Vec::new();
    strings
        .try_reserve(plans.len())
        .map_err(|_| invariant(SourceNewInvariant::Capacity(capacity_node)))?;
    numbers
        .try_reserve(plans.len())
        .map_err(|_| invariant(SourceNewInvariant::Capacity(capacity_node)))?;
    for argument in plans.iter().filter_map(|plan| plan.argument.as_ref()) {
        match &argument.value {
            SourceNewArgumentValue::String(value) => strings.push(value.clone()),
            SourceNewArgumentValue::Number(value) => numbers.push(*value),
        }
    }
    if !strings.is_empty() || !numbers.is_empty() {
        store
            .prepare_regular_literal_types(&strings, &numbers, &[])
            .map_err(|error| literal_cache_error(capacity_node, error))?;
    }

    let mut symbol_nodes = 0usize;
    let mut constructor_type_nodes = 0usize;
    let mut expression_type_nodes = 0usize;
    let mut argument_type_nodes = 0usize;
    let mut signatures = 0usize;
    for plan in plans {
        symbol_nodes = symbol_nodes
            .checked_add(usize::from(
                store.symbol_node_links(plan.constructor).is_none(),
            ))
            .ok_or_else(|| invariant(SourceNewInvariant::Capacity(plan.node)))?;
        constructor_type_nodes = constructor_type_nodes
            .checked_add(usize::from(
                store.type_node_links(plan.constructor).is_none(),
            ))
            .ok_or_else(|| invariant(SourceNewInvariant::Capacity(plan.node)))?;
        expression_type_nodes = expression_type_nodes
            .checked_add(usize::from(store.type_node_links(plan.node).is_none()))
            .ok_or_else(|| invariant(SourceNewInvariant::Capacity(plan.node)))?;
        argument_type_nodes = argument_type_nodes
            .checked_add(usize::from(plan.argument.as_ref().is_some_and(
                |argument| store.type_node_links(argument.node).is_none(),
            )))
            .ok_or_else(|| invariant(SourceNewInvariant::Capacity(plan.node)))?;
        signatures = signatures
            .checked_add(usize::from(store.signature_links(plan.node).is_none()))
            .ok_or_else(|| invariant(SourceNewInvariant::Capacity(plan.node)))?;
    }
    let type_nodes = constructor_type_nodes
        .checked_add(expression_type_nodes)
        .and_then(|count| count.checked_add(argument_type_nodes))
        .ok_or_else(|| invariant(SourceNewInvariant::Capacity(capacity_node)))?;
    let symbol_capacity = store.try_reserve_symbol_node_links(symbol_nodes);
    let type_capacity = store.try_reserve_type_node_links(type_nodes);
    let signature_capacity = store.try_reserve_signature_links(signatures);
    if !(symbol_capacity && type_capacity && signature_capacity) {
        return Err(invariant(SourceNewInvariant::Capacity(capacity_node)));
    }

    for plan in plans {
        if store.symbol_node_links(plan.constructor).is_none() {
            assert!(store.ensure_symbol_node_links(plan.constructor));
        }
        if store.type_node_links(plan.constructor).is_none() {
            assert!(store.ensure_type_node_links(plan.constructor));
        }
        if store.signature_links(plan.node).is_none() {
            assert!(store.ensure_signature_links(plan.node));
        }
        if store.type_node_links(plan.node).is_none() {
            assert!(store.ensure_type_node_links(plan.node));
        }
        if let Some(argument) = plan.argument.as_ref()
            && store.type_node_links(argument.node).is_none()
        {
            assert!(store.ensure_type_node_links(argument.node));
        }
    }
    Ok(())
}

/// Selects the exact default construct signature and publishes the constructor,
/// signature, and result caches as one prevalidated suffix.
pub(super) fn check_direct_default_new(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
) -> Result<CheckedSourceDefaultNew, SourceNewError> {
    preflight_direct_default_new(store, host, plan)?;
    preflight_prepared_default_new_cache(store, plan)?;
    let members = execute_nongeneric_class_member_query(store, host, &plan.class)?;
    let value_type = members.shells().value_type();
    let instance_type = members.shells().instance_type();
    let signature = members.default_construct_signature();
    validate_selected_default_signature(store, plan, value_type, instance_type, signature)?;
    let argument_type = plan
        .argument
        .as_ref()
        .map(|argument| {
            let regular = match &argument.value {
                SourceNewArgumentValue::String(value) => {
                    store.regular_string_literal_type(value.clone())
                }
                SourceNewArgumentValue::Number(value) => store.regular_number_literal_type(*value),
            }
            .map_err(|error| literal_cache_error(argument.node, error))?;
            store
                .fresh_type_of_literal_type(regular)
                .map_err(|error| literal_cache_error(argument.node, error))
        })
        .transpose()?;
    preflight_publication_cache(
        store,
        plan,
        value_type,
        instance_type,
        signature,
        argument_type,
    )?;

    let symbol_links = SymbolNodeLinks {
        resolved_symbol: Some(plan.resolved_symbol),
    };
    let constructor_links = TypeNodeLinks {
        resolved_type: Some(value_type),
        ..TypeNodeLinks::default()
    };
    let expression_links = TypeNodeLinks {
        resolved_type: Some(instance_type),
        ..TypeNodeLinks::default()
    };
    let signature_links = SignatureLinks {
        resolved_signature: ResolvedSignatureState::Resolved(signature),
        ..SignatureLinks::default()
    };
    assert!(store.set_symbol_node_links(plan.constructor, symbol_links));
    assert!(store.set_type_node_links(plan.constructor, constructor_links));
    assert!(store.set_signature_links(plan.node, signature_links));
    assert!(store.set_type_node_links(plan.node, expression_links));
    if let Some((argument, argument_type)) = plan.argument.as_ref().zip(argument_type) {
        assert!(store.set_type_node_links(
            argument.node,
            TypeNodeLinks {
                resolved_type: Some(argument_type),
                ..TypeNodeLinks::default()
            },
        ));
    }
    Ok(CheckedSourceDefaultNew {
        value_type,
        instance_type,
        signature,
    })
}

fn preflight_prepared_default_new_cache(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
) -> Result<(), SourceNewError> {
    if store.symbol_node_links(plan.constructor).is_none()
        || store.type_node_links(plan.constructor).is_none()
        || store.signature_links(plan.node).is_none()
        || store.type_node_links(plan.node).is_none()
        || plan
            .argument
            .as_ref()
            .is_some_and(|argument| store.type_node_links(argument.node).is_none())
    {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    preflight_default_new_cache(store, plan)
}

fn preflight_default_new_cache(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
) -> Result<(), SourceNewError> {
    let constructor_symbol = exact_symbol_cache(store, plan.constructor).map_err(|()| {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    })?;
    if constructor_symbol.is_some_and(|symbol| symbol != plan.resolved_symbol) {
        return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        )));
    }
    let constructor_type = exact_type_cache(store, plan.constructor).map_err(|()| {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    })?;
    let result_type = exact_type_cache(store, plan.node)
        .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(plan.node)))?;
    let signature = exact_signature_cache(store, plan.node)
        .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(plan.node)))?;
    if result_type.is_some() != signature.is_some() {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    if let Some(argument) = plan.argument.as_ref() {
        let cached = exact_type_cache(store, argument.node)
            .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(argument.node)))?;
        let expected = cached_argument_type(store, argument)?;
        if cached.is_some_and(|cached| Some(cached) != expected) {
            return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                argument.node,
            )));
        }
    }

    let instance = store
        .declared_type_links(plan.class.symbol())
        .and_then(|links| links.declared_type);
    let value = exact_class_value_type(store, plan.class.symbol())?;
    if constructor_type.is_some_and(|constructor| Some(constructor) != value)
        || result_type.is_some_and(|result| Some(result) != instance)
    {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    if let (Some(value), Some(instance), Some(signature)) = (value, instance, signature) {
        validate_selected_default_signature(store, plan, value, instance, signature)?;
    } else if signature.is_some() {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    Ok(())
}

fn preflight_publication_cache(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
    value_type: TypeId,
    instance_type: TypeId,
    signature: SignatureId,
    argument_type: Option<TypeId>,
) -> Result<(), SourceNewError> {
    preflight_prepared_default_new_cache(store, plan)?;
    let constructor_symbol = exact_symbol_cache(store, plan.constructor).map_err(|()| {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    })?;
    let constructor = exact_type_cache(store, plan.constructor).map_err(|()| {
        invariant(SourceNewInvariant::InvalidConstructorCache(
            plan.constructor,
        ))
    })?;
    let result = exact_type_cache(store, plan.node)
        .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(plan.node)))?;
    let selected = exact_signature_cache(store, plan.node)
        .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(plan.node)))?;
    if plan.argument.is_some() != argument_type.is_some() {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    if let Some(argument) = plan.argument.as_ref() {
        let cached = exact_type_cache(store, argument.node)
            .map_err(|()| invariant(SourceNewInvariant::InvalidExpressionCache(argument.node)))?;
        if cached.is_some_and(|cached| Some(cached) != argument_type)
            || cached_argument_type(store, argument)? != argument_type
        {
            return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
                argument.node,
            )));
        }
    }
    if constructor_symbol.is_some_and(|symbol| symbol != plan.resolved_symbol)
        || constructor.is_some_and(|type_| type_ != value_type)
        || result.is_some_and(|type_| type_ != instance_type)
        || selected.is_some_and(|selected| selected != signature)
        || result.is_some() != selected.is_some()
    {
        return Err(invariant(SourceNewInvariant::InvalidExpressionCache(
            plan.node,
        )));
    }
    Ok(())
}

fn cached_argument_type(
    store: &CanonicalTypeMapperStore,
    argument: &SourceNewArgument,
) -> Result<Option<TypeId>, SourceNewError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidExpressionCache(argument.node)))?;
    let regular = match &argument.value {
        SourceNewArgumentValue::String(value) => bootstrap.cached_string_literal_type(value),
        SourceNewArgumentValue::Number(value) => bootstrap.cached_number_literal_type(*value),
    };
    regular
        .map(|regular| {
            store
                .fresh_type_of_literal_type(regular)
                .map_err(|error| literal_cache_error(argument.node, error))
        })
        .transpose()
}

fn literal_cache_error(node: NodeRef, error: LiteralTypeCacheError) -> SourceNewError {
    if error == LiteralTypeCacheError::Capacity {
        invariant(SourceNewInvariant::Capacity(node))
    } else {
        invariant(SourceNewInvariant::InvalidExpressionCache(node))
    }
}

fn exact_symbol_cache(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<Option<SemanticSymbolId>, ()> {
    match store.symbol_node_links(node) {
        None => Ok(None),
        Some(links) if links == &SymbolNodeLinks::default() => Ok(None),
        Some(links) => {
            let symbol = links.resolved_symbol.ok_or(())?;
            (links
                == &(SymbolNodeLinks {
                    resolved_symbol: Some(symbol),
                })
                && store.symbol(symbol).is_some())
            .then_some(Some(symbol))
            .ok_or(())
        }
    }
}

fn exact_type_cache(store: &CanonicalTypeMapperStore, node: NodeRef) -> Result<Option<TypeId>, ()> {
    match store.type_node_links(node) {
        None => Ok(None),
        Some(links) if links == &TypeNodeLinks::default() => Ok(None),
        Some(links) => {
            let type_ = links.resolved_type.ok_or(())?;
            (links
                == &(TypeNodeLinks {
                    resolved_type: Some(type_),
                    ..TypeNodeLinks::default()
                })
                && store.type_payload(type_).is_some())
            .then_some(Some(type_))
            .ok_or(())
        }
    }
}

fn exact_signature_cache(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<Option<SignatureId>, ()> {
    match store.signature_links(node) {
        None => Ok(None),
        Some(links) if links == &SignatureLinks::default() => Ok(None),
        Some(links) => {
            let ResolvedSignatureState::Resolved(signature) = links.resolved_signature else {
                return Err(());
            };
            (links
                == &(SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(signature),
                    ..SignatureLinks::default()
                })
                && store.signature(signature).is_some())
            .then_some(Some(signature))
            .ok_or(())
        }
    }
}

fn exact_class_value_type(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
) -> Result<Option<TypeId>, SourceNewError> {
    match store.value_symbol_links(symbol) {
        None => Ok(None),
        Some(links) if links == &ValueSymbolLinks::default() => Ok(None),
        Some(links) => {
            let type_ = links
                .resolved_type
                .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassValue(symbol)))?;
            (links
                == &(ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
                && store.type_payload(type_).is_some())
            .then_some(Some(type_))
            .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassValue(symbol)))
        }
    }
}

fn validate_selected_default_signature(
    store: &CanonicalTypeMapperStore,
    plan: &SourceDefaultNewPlan,
    value_type: TypeId,
    instance_type: TypeId,
    signature: SignatureId,
) -> Result<(), SourceNewError> {
    let value = store
        .type_payload(value_type)
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassValue(plan.class.symbol())))?;
    let Some(structured) = value.data().structured() else {
        return Err(invariant(SourceNewInvariant::InvalidClassValue(
            plan.class.symbol(),
        )));
    };
    if structured.call_signature_count != 0
        || structured.signatures.as_deref() != Some(&[signature])
    {
        return Err(invariant(SourceNewInvariant::InvalidConstructSignature(
            signature,
        )));
    }
    let signature_record = store
        .signature(signature)
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidConstructSignature(signature)))?;
    if signature_record.flags() != SignatureFlags::CONSTRUCT
        || signature_record
            .flags()
            .intersects(SignatureFlags::ABSTRACT)
        || signature_record.declaration() != plan.class.constructor_declaration()
        || !signature_record.type_parameters().is_empty()
        || signature_record.parameters()
            != plan.parameter.map(|parameter| parameter.symbol).as_slice()
        || signature_record.this_parameter().is_some()
        || signature_record.min_argument_count() != i32::from(plan.parameter.is_some())
        || signature_record.resolved_min_argument_count() != -1
        || signature_record.resolved_return_type() != Some(instance_type)
        || signature_record.resolved_type_predicate().is_some()
        || signature_record.target().is_some()
        || signature_record.mapper().is_some()
        || signature_record.isolated_signature_type().is_some()
        || signature_record.composite().is_some()
    {
        return Err(invariant(SourceNewInvariant::InvalidConstructSignature(
            signature,
        )));
    }
    if let Some(parameter) = plan.parameter
        && store.value_symbol_links(parameter.symbol)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(parameter.type_),
                ..ValueSymbolLinks::default()
            })
    {
        return Err(invariant(SourceNewInvariant::InvalidConstructSignature(
            signature,
        )));
    }
    let TypeData::Interface(instance) = store
        .type_payload(instance_type)
        .map(super::type_records::TypeRecord::data)
        .ok_or_else(|| invariant(SourceNewInvariant::InvalidClassValue(plan.class.symbol())))?
    else {
        return Err(invariant(SourceNewInvariant::InvalidClassValue(
            plan.class.symbol(),
        )));
    };
    if instance.reference.object.target != Some(instance_type) {
        return Err(invariant(SourceNewInvariant::InvalidClassValue(
            plan.class.symbol(),
        )));
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
        CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError, UnsupportedSourceSyntax,
    };

    fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/class-default-new-poison.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn class_symbol(
        parsed: &ParseResult,
        file: FileId,
        context: &CanonicalCheckerContext<'_>,
        expected: &str,
    ) -> SemanticSymbolId {
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ClassDeclaration(class) = &record.data else {
                    return None;
                };
                let name = class.name.and_then(|name| parsed.arena.get(name))?;
                let NodeData::Identifier(name) = &name.data else {
                    return None;
                };
                (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap_or_else(|| panic!("missing class {expected}"));
        let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
        context.store().get_merged_symbol(raw).unwrap()
    }

    fn variable_new(parsed: &ParseResult, file: FileId, expected: &str) -> (NodeRef, NodeRef) {
        let construction = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                    return None;
                };
                (name.text == expected).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    variable.initializer?,
                ))
            })
            .unwrap_or_else(|| panic!("missing variable {expected}"));
        let NodeData::NewExpression(new_expression) =
            &parsed.arena.get(construction.node).unwrap().data
        else {
            panic!("variable initializer is not a new expression")
        };
        (
            construction,
            NodeRef::new(
                construction.arena,
                construction.file,
                new_expression.expression,
            ),
        )
    }

    fn constructor_argument(parsed: &ParseResult, construction: NodeRef) -> NodeRef {
        let NodeData::NewExpression(new_expression) =
            &parsed.arena.get(construction.node).unwrap().data
        else {
            panic!("variable initializer is not a new expression")
        };
        NodeRef::new(
            construction.arena,
            construction.file,
            new_expression.arguments.as_ref().unwrap().nodes[0],
        )
    }

    #[test]
    fn required_primitive_constructor_argument_publishes_fresh_literal_and_replays_warm() {
        for (source, numeric) in [
            (
                "class Model { constructor(value: string) {} } const model = new Model(\"ready\");",
                false,
            ),
            (
                "class Model { constructor(value: number) {} } const model = new Model(1);",
                true,
            ),
            (
                concat!(
                    "declare function decorate(",
                    "target: any, key: string | symbol | undefined, index: number",
                    "): void; ",
                    "class Model { constructor(@decorate value: string) {} } ",
                    "const model = new Model(\"ready\");",
                ),
                false,
            ),
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(1_807);
            let mut context = context(&parsed, file);
            let owner = class_symbol(&parsed, file, &context, "Model");
            let (construction, constructor) = variable_new(&parsed, file, "model");
            let argument = constructor_argument(&parsed, construction);

            context.check_source_file(file).unwrap();

            let store = context.store();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let regular = if numeric {
                bootstrap
                    .cached_number_literal_type(ts_jsnum::from_string("1"))
                    .unwrap()
            } else {
                bootstrap.cached_string_literal_type("ready").unwrap()
            };
            let fresh = store.fresh_type_of_literal_type(regular).unwrap();
            let signature = store
                .signature_links(construction)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let signature_record = store.signature(signature).unwrap();
            let [parameter] = signature_record.parameters() else {
                panic!("the selected constructor has exactly one parameter")
            };
            let expected_parameter = if numeric {
                bootstrap.number_type
            } else {
                bootstrap.string_type
            };
            assert_eq!(signature_record.min_argument_count(), 1);
            assert_eq!(
                store.value_symbol_links(*parameter),
                Some(&ValueSymbolLinks {
                    resolved_type: Some(expected_parameter),
                    ..ValueSymbolLinks::default()
                }),
            );
            assert_eq!(
                store.type_node_links(argument),
                Some(&TypeNodeLinks {
                    resolved_type: Some(fresh),
                    ..TypeNodeLinks::default()
                }),
            );
            assert_eq!(
                store
                    .symbol_node_links(constructor)
                    .and_then(|links| links.resolved_symbol),
                Some(owner),
            );
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
            let warm = (
                store.type_len(),
                store.signature_len(),
                store.checker_link_allocated_lengths(),
            );

            context.recheck_source_file(file).unwrap();

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn incompatible_constructor_arguments_reject_before_class_publication() {
        for source in [
            "class Model { constructor(value: string) {} } const model = new Model(1);",
            "class Model { constructor(value: number) {} } const model = new Model(\"ready\");",
            "class Model { constructor(value: string) {} } const model = new Model();",
            "class Model {} const model = new Model(\"ready\");",
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(1_808);
            let mut context = context(&parsed, file);
            let owner = class_symbol(&parsed, file, &context, "Model");
            let (construction, _) = variable_new(&parsed, file, "model");
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );

            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(
                    construction,
                ))),
                "{source}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
            assert!(context.store().declared_type_links(owner).is_none());
            assert!(context.store().value_symbol_links(owner).is_none());
        }
    }

    #[test]
    fn poisoned_constructor_argument_rejects_before_class_publication() {
        let parsed = parse_source_file(
            "class Model { constructor(value: string) {} } const model = new Model(\"ready\");",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_809);
        let mut context = context(&parsed, file);
        let owner = class_symbol(&parsed, file, &context, "Model");
        let (construction, _) = variable_new(&parsed, file, "model");
        let argument = constructor_argument(&parsed, construction);
        let poison = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(context.store_mut_for_test().set_type_node_links(
            argument,
            TypeNodeLinks {
                resolved_type: Some(poison),
                ..TypeNodeLinks::default()
            },
        ));
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );

        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Call(argument)),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            before,
        );
        assert!(context.store().declared_type_links(owner).is_none());
        assert!(context.store().value_symbol_links(owner).is_none());
    }

    #[test]
    fn poisoned_later_new_rejects_before_earlier_class_or_link_publication() {
        let parsed = parse_source_file(concat!(
            "class Early { value!: string; }\n",
            "const early = new Early();\n",
            "class Later { value!: string; }\n",
            "const later = new Later();\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1_806);
        let mut context = context(&parsed, file);
        let early_class = class_symbol(&parsed, file, &context, "Early");
        let (early_new, early_constructor) = variable_new(&parsed, file, "early");
        let (later_new, _) = variable_new(&parsed, file, "later");
        let poison = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_type_node_links(
            later_new,
            TypeNodeLinks {
                resolved_type: Some(poison),
                ..TypeNodeLinks::default()
            },
        ));
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
            context.store().relation_state_snapshot(),
        );

        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Call(later_new))
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().relation_state_snapshot(),
            ),
            before
        );
        assert!(context.store().declared_type_links(early_class).is_none());
        assert!(context.store().value_symbol_links(early_class).is_none());
        assert!(
            context
                .store()
                .symbol_node_links(early_constructor)
                .is_none()
        );
        assert!(context.store().type_node_links(early_constructor).is_none());
        assert!(context.store().signature_links(early_new).is_none());
        assert!(context.store().type_node_links(early_new).is_none());
        assert_eq!(
            context.store().type_node_links(later_new),
            Some(&TypeNodeLinks {
                resolved_type: Some(poison),
                ..TypeNodeLinks::default()
            })
        );
        assert!(context.diagnostics().is_empty());
    }
}
