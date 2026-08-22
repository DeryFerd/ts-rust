//! Exact source integration for one default class construction.
//!
//! This is the dependency-closed `new Model()` and `new Model` branch of pinned
//! TypeScript-Go `checkCallExpression`, `getResolvedSignature`,
//! `resolveNewExpression`, and `resolveCall`. The admitted constructor is one
//! preceding local class whose primitive member transaction owns exactly one
//! non-abstract, zero-parameter construct signature. Direct local inheritance
//! reuses the existing completed class graph. Planning proves the complete
//! syntax, resolver route, class provenance, and cold/warm cache shape before
//! source execution may publish any class or expression state.

use std::collections::{HashMap, HashSet};

use ts_ast::{NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation,
    CheckFlags, SemanticSymbolId, SymbolFlags,
};

use super::{
    CanonicalTypeMapperStore, ClassError, DeclaredTypeError, DeclaredTypeHost,
    ResolvedSignatureState, SignatureId, SignatureLinks, SymbolNodeLinks, TypeData, TypeId,
    TypeNodeLinks, ValueSymbolLinks,
    classes::{
        ClassMemberPlan, ClassMemberQueryPlan, execute_nongeneric_class_member_query,
        plan_nongeneric_class_member_query, preflight_nongeneric_class_member_query,
    },
    signatures::SignatureFlags,
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
    let argument_start = match new_expression.arguments.as_ref() {
        Some(arguments) => {
            if !arguments.nodes.is_empty()
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
            || prior_classes.get(&base.symbol()) != Some(base)
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
    preflight_nongeneric_class_member_query(store, host, &class)?;

    let plan = SourceDefaultNewPlan {
        node,
        constructor,
        resolved_symbol,
        class,
    };
    preflight_default_new_cache(store, &plan)?;
    Ok(plan)
}

/// Revalidates the class and all observable cold/warm construction caches.
pub(super) fn preflight_direct_default_new(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
) -> Result<(), SourceNewError> {
    preflight_nongeneric_class_member_query(store, host, &plan.class)?;
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

    let mut symbol_nodes = 0usize;
    let mut constructor_type_nodes = 0usize;
    let mut expression_type_nodes = 0usize;
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
        signatures = signatures
            .checked_add(usize::from(store.signature_links(plan.node).is_none()))
            .ok_or_else(|| invariant(SourceNewInvariant::Capacity(plan.node)))?;
    }
    let type_nodes = constructor_type_nodes
        .checked_add(expression_type_nodes)
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
    preflight_publication_cache(store, plan, value_type, instance_type, signature)?;

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
        || signature_record.declaration().is_some()
        || !signature_record.type_parameters().is_empty()
        || !signature_record.parameters().is_empty()
        || signature_record.this_parameter().is_some()
        || signature_record.min_argument_count() != 0
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
    use crate::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError};

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
