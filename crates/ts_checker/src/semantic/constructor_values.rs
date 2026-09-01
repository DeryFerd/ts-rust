//! Source-owned identities for declared constructor values.
//!
//! A value, its constructor object, and each construct signature's return have
//! separate identities. Consumers own overload selection and heritage checks.
//! The named-interface path prepares one signature and keeps other members lazy.
//! Its generic annotations require complete explicit arguments and a stored proof.
//! The global `TypeLiteral` path uses the full canonical annotation query.
//! Generic global constructors keep the full named interface publication.

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, SemanticSymbolId, SymbolFlags};

#[cfg(test)]
mod tests;

use super::{
    CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, SignatureId, SymbolNodeLinks,
    TypeId, TypeNodeLinks, ValueSymbolLinks,
    array_types::CanonicalArrayTargets,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set_with_array_targets},
    declared::preflight_class_or_interface_reference,
    declared_values::{
        plan_global_named_constructor_value, plan_global_type_literal_value, publish_declared_value,
    },
    instantiate::InstantiationSession,
    object_members::{
        self, PlannedCallSignature, PropertyObjectError, PropertyObjectPlan, PropertyObjectState,
        ResolvedCallSignatureTypes, interface_state, plan_interface,
    },
    signatures::SignatureFlags,
    type_nodes::{CanonicalTypeQuery, validate_cached_merged_global_value_annotation},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DeclaredConstructorValuePlan {
    value_symbol: SemanticSymbolId,
    value_declaration: NodeRef,
    value_annotation: NodeRef,
    owner: PropertyObjectPlan,
    construct_indexes: Box<[usize]>,
}

impl DeclaredConstructorValuePlan {
    pub(super) const fn value_symbol(&self) -> SemanticSymbolId {
        self.value_symbol
    }

    pub(super) const fn value_declaration(&self) -> NodeRef {
        self.value_declaration
    }

    pub(super) const fn value_annotation(&self) -> NodeRef {
        self.value_annotation
    }

    pub(super) const fn owner_symbol(&self) -> SemanticSymbolId {
        self.owner.symbol
    }

    pub(super) fn construct_declarations(&self) -> impl ExactSizeIterator<Item = NodeRef> + '_ {
        self.construct_indexes
            .iter()
            .map(|&index| self.owner.call_signatures[index].declaration)
    }

    fn signature(&self, declaration: NodeRef) -> Option<&PlannedCallSignature> {
        self.construct_indexes
            .iter()
            .map(|&index| &self.owner.call_signatures[index])
            .find(|signature| signature.declaration == declaration)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DeclaredConstructorValue {
    value_symbol: SemanticSymbolId,
    constructor_type: TypeId,
}

impl DeclaredConstructorValue {
    pub(super) const fn value_symbol(self) -> SemanticSymbolId {
        self.value_symbol
    }

    pub(super) const fn constructor_type(self) -> TypeId {
        self.constructor_type
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DeclaredConstructSignature {
    value: DeclaredConstructorValue,
    declaration: NodeRef,
    signature: SignatureId,
    return_type: TypeId,
}

impl DeclaredConstructSignature {
    pub(super) const fn value(self) -> DeclaredConstructorValue {
        self.value
    }

    pub(super) const fn declaration(self) -> NodeRef {
        self.declaration
    }

    pub(super) const fn signature(self) -> SignatureId {
        self.signature
    }

    pub(super) const fn return_type(self) -> TypeId {
        self.return_type
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DeclaredConstructorValueError {
    Unsupported { node: NodeRef, kind: SyntaxKind },
    InvalidValue(SemanticSymbolId),
    InvalidSignature(NodeRef),
    Capacity(NodeRef),
    DeclaredType(DeclaredTypeError),
    Members(PropertyObjectError),
}

impl From<DeclaredTypeError> for DeclaredConstructorValueError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<PropertyObjectError> for DeclaredConstructorValueError {
    fn from(error: PropertyObjectError) -> Self {
        Self::Members(error)
    }
}

fn unsupported(node: NodeRef, kind: SyntaxKind) -> DeclaredConstructorValueError {
    DeclaredConstructorValueError::Unsupported { node, kind }
}

/// A current global binding and its actual, fully queried literal owner.
/// This request proof does not publish a value or replace a source declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct GlobalConstructorValuePlan {
    value_symbol: SemanticSymbolId,
    value_declaration: NodeRef,
    value_annotation: NodeRef,
    owner: PropertyObjectPlan,
    construct_indexes: Box<[usize]>,
    options: CanonicalCheckerOptions,
    array_targets: CanonicalArrayTargets,
    named_interface: bool,
}

impl GlobalConstructorValuePlan {
    pub(super) const fn is_named_generic(&self) -> bool {
        self.named_interface
    }

    pub(super) const fn value_symbol(&self) -> SemanticSymbolId {
        self.value_symbol
    }

    pub(super) const fn value_declaration(&self) -> NodeRef {
        self.value_declaration
    }

    pub(super) const fn value_annotation(&self) -> NodeRef {
        self.value_annotation
    }

    pub(super) const fn owner_symbol(&self) -> SemanticSymbolId {
        self.owner.symbol
    }

    pub(super) fn construct_declarations(&self) -> impl ExactSizeIterator<Item = NodeRef> + '_ {
        self.construct_indexes
            .iter()
            .map(|&index| self.owner.call_signatures[index].declaration)
    }
}

/// All original construct signatures, in source order, with separate returns.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct GlobalConstructorCandidates {
    value: DeclaredConstructorValue,
    signatures: Box<[DeclaredConstructSignature]>,
}

impl GlobalConstructorCandidates {
    pub(super) const fn value(&self) -> DeclaredConstructorValue {
        self.value
    }

    pub(super) fn signatures(&self) -> &[DeclaredConstructSignature] {
        &self.signatures
    }
}

/// Selects this route from the real global receipt, never from an old route's error.
pub(super) fn plan_global_constructor_value(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    value_symbol: SemanticSymbolId,
) -> Result<Option<GlobalConstructorValuePlan>, DeclaredConstructorValueError> {
    let Some(value) = plan_global_type_literal_value(store, host, value_symbol)? else {
        return Ok(None);
    };
    let invalid = || DeclaredConstructorValueError::InvalidValue(value_symbol);
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    if options.intrinsic != bootstrap.options
        || store.claimed_strict_builtin_iterator_return()
            != Some(options.strict_builtin_iterator_return)
        || store
            .claimed_strict_function_types()
            .is_some_and(|established| established != options.strict_function_types)
        || store
            .value_symbol_links(bootstrap.global_this_symbol)
            .and_then(|links| links.resolved_type)
            != Some(globals.global_this_value_type)
    {
        return Err(invalid());
    }
    let owner = object_members::plan_type_literal(store, host, value.annotation, None)?;
    let mut construct_indexes = Vec::new();
    for (index, signature) in owner.call_signatures.iter().enumerate() {
        if signature.is_construct() {
            if !signature.type_parameters.is_empty()
                || signature.implicit_any_return
                || signature.type_predicate.is_some()
                || signature.flags.contains(SignatureFlags::HAS_REST_PARAMETER)
                || signature
                    .parameters
                    .iter()
                    .any(|parameter| parameter.implicit_any_rest)
            {
                return Err(unsupported(
                    signature.declaration,
                    SyntaxKind::ConstructSignature,
                ));
            }
            construct_indexes.push(index);
        }
    }
    if construct_indexes.is_empty() {
        return Ok(None);
    }
    let plan = GlobalConstructorValuePlan {
        value_symbol,
        value_declaration: store
            .symbol(value_symbol)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            .ok_or_else(invalid)?,
        value_annotation: value.annotation,
        owner,
        construct_indexes: construct_indexes.into_boxed_slice(),
        options,
        array_targets: CanonicalArrayTargets::from_global_types(globals),
        named_interface: false,
    };
    validate_global_annotation_caches(store, host, &plan)?;
    let ready = read_global_constructor_literal(store, &plan)?;
    if value.cached_type.is_some_and(|cached| {
        ready
            .as_ref()
            .is_none_or(|ready| ready.value.constructor_type != cached)
    }) {
        return Err(invalid());
    }
    Ok(Some(plan))
}

/// Keeps the global value owner separate from its named constructor interface.
pub(super) fn plan_global_generic_constructor_value(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    value_symbol: SemanticSymbolId,
) -> Result<Option<GlobalConstructorValuePlan>, DeclaredConstructorValueError> {
    let Some(value) = plan_global_named_constructor_value(store, host, value_symbol)? else {
        return Ok(None);
    };
    let declared = plan_declared_constructor_value_worker(store, host, value_symbol, true)?;
    if !declared
        .owner
        .call_signatures
        .iter()
        .any(|signature| signature.is_construct() && !signature.type_parameters.is_empty())
    {
        return Ok(None);
    }
    let invalid = || DeclaredConstructorValueError::InvalidValue(value_symbol);
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    if value.annotation != declared.value_annotation
        || options.intrinsic != bootstrap.options
        || store.claimed_strict_builtin_iterator_return()
            != Some(options.strict_builtin_iterator_return)
        || store
            .claimed_strict_function_types()
            .is_some_and(|claimed| claimed != options.strict_function_types)
        || store
            .value_symbol_links(bootstrap.global_this_symbol)
            .and_then(|links| links.resolved_type)
            != Some(globals.global_this_value_type)
    {
        return Err(invalid());
    }
    let plan = GlobalConstructorValuePlan {
        value_symbol,
        value_declaration: declared.value_declaration,
        value_annotation: declared.value_annotation,
        owner: declared.owner,
        construct_indexes: declared.construct_indexes,
        options,
        array_targets: CanonicalArrayTargets::from_global_types(globals),
        named_interface: true,
    };
    validate_global_annotation_caches(store, host, &plan)?;
    let ready = read_global_named_constructor(store, &plan)?;
    if value.cached_type.is_some_and(|cached| {
        ready
            .as_ref()
            .is_none_or(|ready| ready.value.constructor_type != cached)
    }) {
        return Err(invalid());
    }
    Ok(Some(plan))
}

fn validate_global_plan(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &GlobalConstructorValuePlan,
) -> Result<(), DeclaredConstructorValueError> {
    let current = if plan.named_interface {
        plan_global_generic_constructor_value(store, host, globals, options, plan.value_symbol())?
    } else {
        plan_global_constructor_value(store, host, globals, options, plan.value_symbol())?
    };
    if current.as_ref() != Some(plan) {
        return Err(DeclaredConstructorValueError::InvalidValue(
            plan.value_symbol,
        ));
    }
    Ok(())
}

/// A cold unselected annotation stays cold. Populated proofs use the ordinary reader.
fn validate_global_annotation_caches(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &GlobalConstructorValuePlan,
) -> Result<(), DeclaredConstructorValueError> {
    let invalid = || DeclaredConstructorValueError::InvalidValue(plan.value_symbol);
    let declarations = store
        .symbol(plan.value_symbol)
        .and_then(ts_binder::semantic::Symbol::declarations)
        .ok_or_else(invalid)?;
    for &declaration in declarations {
        if store.source_node_kind(declaration) != Some(SyntaxKind::VariableDeclaration) {
            continue;
        }
        let annotation = store
            .source_direct_type_annotation(declaration)
            .ok_or_else(invalid)?;
        let mut pending = vec![annotation];
        let mut seen = std::collections::HashSet::new();
        let mut populated = false;
        while let Some(node) = pending.pop() {
            if !seen.insert(node) {
                return Err(invalid());
            }
            populated |= store
                .type_node_links(node)
                .is_some_and(|links| links != &TypeNodeLinks::default())
                || store
                    .symbol_node_links(node)
                    .is_some_and(|links| links != &SymbolNodeLinks::default());
            pending.extend(store.source_direct_children(node).ok_or_else(invalid)?);
        }
        if populated {
            validate_cached_merged_global_value_annotation(
                store,
                host,
                Some(plan.array_targets),
                annotation,
            )?;
        }
    }
    Ok(())
}

/// The full member and signature readers also check every later overload.
#[allow(clippy::too_many_lines)] // Source signatures, member state and Array authority form one read.
fn read_global_constructor_literal(
    store: &CanonicalTypeMapperStore,
    plan: &GlobalConstructorValuePlan,
) -> Result<Option<GlobalConstructorCandidates>, DeclaredConstructorValueError> {
    if plan.named_interface {
        return read_global_named_constructor(store, plan);
    }
    let invalid = || DeclaredConstructorValueError::InvalidValue(plan.value_symbol);
    if store
        .symbol_node_links(plan.value_annotation)
        .is_some_and(|links| links != &SymbolNodeLinks::default())
        || store
            .type_node_links(plan.value_annotation)
            .is_some_and(|links| links.outer_type_parameters.is_some())
    {
        return Err(invalid());
    }
    let state = object_members::type_literal_state(store, &plan.owner)?;
    let Some(PropertyObjectState::Resolved(constructor_type)) = state else {
        // A literal cannot borrow the named-interface partial signature publisher.
        if plan.owner.call_signatures.iter().any(|signature| {
            store
                .signature_links(signature.declaration)
                .is_some_and(|links| links != &super::SignatureLinks::default())
                || signature.parameters.iter().any(|parameter| {
                    store
                        .value_symbol_links(parameter.symbol)
                        .is_some_and(|links| links != &ValueSymbolLinks::default())
                })
        }) || state.is_none()
            && plan.owner.properties.iter().any(|property| {
                store
                    .value_symbol_links(property.symbol)
                    .is_some_and(|links| links != &ValueSymbolLinks::default())
            })
        {
            return Err(invalid());
        }
        return Ok(None);
    };
    if store
        .type_payload(constructor_type)
        .and_then(|record| record.symbol())
        != Some(plan.owner_symbol())
        || !store.source_direct_type_annotation_is_exact(plan.value_annotation, constructor_type)
    {
        return Err(invalid());
    }
    let StoredCallableSetValidation::Valid { projection, .. } =
        validate_stored_callable_set_with_array_targets(
            store,
            constructor_type,
            Some(plan.array_targets),
        )
    else {
        return Err(invalid());
    };
    store
        .validate_cached_array_capability_with_array_targets(plan.array_targets, constructor_type)
        .map_err(|_| invalid())?;
    if projection.owner != constructor_type
        || projection.construct_signatures.len() != plan.construct_indexes.len()
    {
        return Err(invalid());
    }
    let value = DeclaredConstructorValue {
        value_symbol: plan.value_symbol,
        constructor_type,
    };
    let mut signatures = Vec::with_capacity(plan.construct_indexes.len());
    for (&index, &signature) in plan
        .construct_indexes
        .iter()
        .zip(&projection.construct_signatures)
    {
        let planned = &plan.owner.call_signatures[index];
        let invalid = || DeclaredConstructorValueError::InvalidSignature(planned.declaration);
        if object_members::validate_resolved_call_signature(store, planned) != Some(signature) {
            return Err(invalid());
        }
        let return_type = store
            .signature(signature)
            .and_then(super::signatures::Signature::resolved_return_type)
            .ok_or_else(invalid)?;
        signatures.push(DeclaredConstructSignature {
            value,
            declaration: planned.declaration,
            signature,
            return_type,
        });
    }
    Ok(Some(GlobalConstructorCandidates {
        value,
        signatures: signatures.into_boxed_slice(),
    }))
}

/// A named value uses its interface's full member and signature publication.
fn read_global_named_constructor(
    store: &CanonicalTypeMapperStore,
    plan: &GlobalConstructorValuePlan,
) -> Result<Option<GlobalConstructorCandidates>, DeclaredConstructorValueError> {
    let invalid = || DeclaredConstructorValueError::InvalidValue(plan.value_symbol);
    let Some(constructor_type) = store
        .declared_type_links(plan.owner_symbol())
        .and_then(|links| links.declared_type)
    else {
        return Ok(None);
    };
    let state = interface_state(store, &plan.owner, constructor_type)?;
    if matches!(state, PropertyObjectState::EmptyBootstrap(_)) {
        return Err(invalid());
    }
    if !matches!(state, PropertyObjectState::Resolved(actual) if actual == constructor_type) {
        return Ok(None);
    }
    let Some(annotation_type) = store
        .type_node_links(plan.value_annotation)
        .and_then(|links| links.resolved_type)
    else {
        return Ok(None);
    };
    if annotation_type != constructor_type
        || store
            .type_payload(constructor_type)
            .and_then(super::TypeRecord::symbol)
            != Some(plan.owner_symbol())
        || !store.source_direct_type_annotation_is_exact(plan.value_annotation, constructor_type)
    {
        return Err(invalid());
    }
    let StoredCallableSetValidation::Valid { projection, .. } =
        validate_stored_callable_set_with_array_targets(
            store,
            constructor_type,
            Some(plan.array_targets),
        )
    else {
        return Err(invalid());
    };
    if projection.owner != constructor_type
        || projection.construct_signatures.len() != plan.construct_indexes.len()
    {
        return Err(invalid());
    }
    let value = DeclaredConstructorValue {
        value_symbol: plan.value_symbol,
        constructor_type,
    };
    let mut signatures = Vec::with_capacity(plan.construct_indexes.len());
    for (&index, &signature) in plan
        .construct_indexes
        .iter()
        .zip(&projection.construct_signatures)
    {
        let planned = &plan.owner.call_signatures[index];
        if object_members::validate_resolved_call_signature(store, planned) != Some(signature) {
            return Err(DeclaredConstructorValueError::InvalidSignature(
                planned.declaration,
            ));
        }
        let return_type = store
            .signature(signature)
            .and_then(|record| record.resolved_return_type())
            .ok_or(DeclaredConstructorValueError::InvalidSignature(
                planned.declaration,
            ))?;
        signatures.push(DeclaredConstructSignature {
            value,
            declaration: planned.declaration,
            signature,
            return_type,
        });
    }
    Ok(Some(GlobalConstructorCandidates {
        value,
        signatures: signatures.into_boxed_slice(),
    }))
}

/// Reads complete candidates only after the ordinary value publication is current.
pub(super) fn resolve_global_constructor_candidates(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &GlobalConstructorValuePlan,
) -> Result<Option<GlobalConstructorCandidates>, DeclaredConstructorValueError> {
    validate_global_plan(store, host, globals, options, plan)?;
    let ready = read_global_constructor_literal(store, plan)?;
    let Some(ready) = ready else {
        return Ok(None);
    };
    let Some(provenance) = store.declared_value_provenance(plan.value_symbol) else {
        return Ok(None);
    };
    if provenance.annotation != plan.value_annotation
        || provenance.type_ != ready.value.constructor_type
        || provenance.readonly.is_some()
        || !provenance.is_current(store, plan.value_symbol)
    {
        return Err(DeclaredConstructorValueError::InvalidValue(
            plan.value_symbol,
        ));
    }
    Ok(Some(ready))
}

/// Uses the full declared query and the caller's existing instantiation session.
#[allow(clippy::too_many_arguments)] // The provider must retain the complete caller context.
pub(super) fn prepare_global_constructor_candidates(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &GlobalConstructorValuePlan,
) -> Result<GlobalConstructorCandidates, DeclaredConstructorValueError> {
    if let Some(ready) = resolve_global_constructor_candidates(store, host, globals, options, plan)?
    {
        return Ok(ready);
    }
    if read_global_constructor_literal(store, plan)?.is_none() {
        let mut query = CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            globals,
            options,
            session,
            diagnostics,
        )?;
        if plan.named_interface {
            query.get_declared_interface_for_source_check(plan.owner_symbol())?;
        }
        query.get_type_from_type_node(plan.value_annotation())?;
    }
    validate_global_plan(store, host, globals, options, plan)?;
    let invalid = || DeclaredConstructorValueError::InvalidValue(plan.value_symbol);
    let ready = read_global_constructor_literal(store, plan)?.ok_or_else(invalid)?;
    let value = if plan.named_interface {
        plan_global_named_constructor_value(store, host, plan.value_symbol)?
    } else {
        plan_global_type_literal_value(store, host, plan.value_symbol)?
    }
    .ok_or_else(invalid)?;
    if !store.try_reserve_value_symbol_links(1) || !store.try_reserve_declared_value_provenance(1) {
        return Err(DeclaredConstructorValueError::Capacity(
            plan.value_declaration(),
        ));
    }
    publish_declared_value(store, value, ready.value.constructor_type)?;
    resolve_global_constructor_candidates(store, host, globals, options, plan)?.ok_or_else(invalid)
}

/// Plans the declaration, not an expression that happens to use its value.
pub(super) fn plan_declared_constructor_value(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    value_symbol: SemanticSymbolId,
) -> Result<DeclaredConstructorValuePlan, DeclaredConstructorValueError> {
    plan_declared_constructor_value_worker(store, host, value_symbol, false)
}

fn plan_declared_constructor_value_worker(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    value_symbol: SemanticSymbolId,
    allow_generic: bool,
) -> Result<DeclaredConstructorValuePlan, DeclaredConstructorValueError> {
    let invalid = || DeclaredConstructorValueError::InvalidValue(value_symbol);
    let value = store.symbol(value_symbol).ok_or_else(invalid)?;
    let declaration = value.value_declaration().ok_or_else(invalid)?;
    let record = host.node(declaration).ok_or_else(invalid)?;
    let NodeData::VariableDeclaration(variable) = &record.data else {
        return Err(unsupported(declaration, record.kind));
    };
    let bound = host.bound_file(declaration).ok_or_else(invalid)?;
    let list = record
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(invalid)?;
    let list_record = host.node(list).ok_or_else(invalid)?;
    let NodeData::VariableDeclarationList(declarations) = &list_record.data else {
        return Err(invalid());
    };
    let statement = list_record
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(invalid)?;
    let statement_record = host.node(statement).ok_or_else(invalid)?;
    let NodeData::VariableStatement(statement_data) = &statement_record.data else {
        return Err(invalid());
    };
    let name = NodeRef::new(declaration.arena, declaration.file, variable.name);
    let name_record = host.node(name).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(name, name_record.kind));
    };
    let annotation = variable
        .type_
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| unsupported(declaration, record.kind))?;
    let annotation_record = host.node(annotation).ok_or_else(invalid)?;
    let ambient_file = bound
        .source_facts()
        .is_some_and(|facts| facts.is_declaration_file() && !facts.is_javascript_file());
    let declared = match statement_data.modifiers.as_ref() {
        None => false,
        Some(modifiers) => {
            let [modifier] = modifiers.list.nodes.as_slice() else {
                return Err(unsupported(statement, statement_record.kind));
            };
            let modifier = NodeRef::new(statement.arena, statement.file, *modifier);
            if modifiers.flags.0 != 0
                || modifiers.list.has_trailing_comma
                || host.node(modifier).is_none_or(|record| {
                    record.kind != SyntaxKind::DeclareKeyword
                        || record.flags.0 != 0
                        || record.parent != Some(statement.node)
                        || !matches!(record.data, NodeData::Token(_))
                })
            {
                return Err(unsupported(statement, statement_record.kind));
            }
            true
        }
    };
    if !ambient_file && !declared {
        return Err(unsupported(declaration, record.kind));
    }
    let variable_flags = if list_record.flags.0 == 0 {
        SymbolFlags::FUNCTION_SCOPED_VARIABLE
    } else {
        SymbolFlags::BLOCK_SCOPED_VARIABLE
    };
    let expected_flags = variable_flags | (value.flags() & SymbolFlags::INTERFACE);
    if store.get_merged_symbol(value_symbol) != Some(value_symbol)
        || !store.source_merged_symbol_declarations_match(value_symbol)
        || value.flags().without(SymbolFlags::TRANSIENT) != expected_flags
        || value.check_flags() != CheckFlags::NONE
        || value.name().as_utf8() != Some(identifier.text.as_str())
        || value.parent().is_some()
        || value.exports().is_some()
        || value.export_symbol().is_some()
        || !value.flags().contains(SymbolFlags::INTERFACE) && value.members().is_some()
        || value.declarations().is_none_or(|declarations| {
            declarations
                .iter()
                .filter(|&&node| node == declaration)
                .count()
                != 1
                || declarations.iter().any(|&node| {
                    node != declaration
                        && store.source_node_kind(node) != Some(SyntaxKind::InterfaceDeclaration)
                })
        })
        || !host.symbol_matches(store, declaration, value_symbol)
        || record.kind != SyntaxKind::VariableDeclaration
        || record.flags.0 != 0
        || variable.initializer.is_some()
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.facts != 0
        || list_record.kind != SyntaxKind::VariableDeclarationList
        || !matches!(list_record.flags.0, 0..=2)
        || declarations.declarations.has_trailing_comma
        || !declarations.declarations.nodes.contains(&declaration.node)
        || statement_record.kind != SyntaxKind::VariableStatement
        || statement_record.flags.0 != 0
        || statement_record.parent != Some(bound.source_file().node)
        || statement_data.declaration_list != list.node
        || statement_data.flow_node.is_some()
        || statement_data.facts != 0
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || annotation_record.flags.0 != 0
        || annotation_record.parent != Some(declaration.node)
    {
        return Err(invalid());
    }

    let NodeData::TypeReferenceNode(reference) = &annotation_record.data else {
        return Err(unsupported(annotation, annotation_record.kind));
    };
    if reference.type_arguments.is_some() {
        return Err(unsupported(annotation, annotation_record.kind));
    }
    let type_name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
    let type_name_record = host.node(type_name).ok_or_else(invalid)?;
    let NodeData::Identifier(type_identifier) = &type_name_record.data else {
        return Err(unsupported(type_name, type_name_record.kind));
    };
    if type_name_record.flags.0 != 0
        || type_name_record.parent != Some(annotation.node)
        || type_identifier.flow_node.is_some()
        || type_identifier.text.is_empty()
    {
        return Err(invalid());
    }
    let owner_symbol = host
        .name_resolver_host(store)?
        .resolve_entity_name(type_name, SymbolFlags::TYPE)
        .map_err(|_| invalid())?
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(|| unsupported(annotation, annotation_record.kind))?;
    let owner_record = store.symbol(owner_symbol).ok_or_else(invalid)?;
    if !owner_record.flags().contains(SymbolFlags::INTERFACE)
        || owner_record
            .flags()
            .intersects(SymbolFlags::CLASS | SymbolFlags::TYPE_ALIAS)
    {
        return Err(unsupported(annotation, annotation_record.kind));
    }
    if preflight_class_or_interface_reference(store, host, owner_symbol, owner_record.flags())? != 0
    {
        return Err(unsupported(annotation, annotation_record.kind));
    }
    let owner = plan_interface(store, host, owner_symbol)?;
    if owner.heritage.is_some() {
        return Err(unsupported(owner.node, SyntaxKind::InterfaceDeclaration));
    }
    let mut construct_indexes = Vec::new();
    for (index, signature) in owner.call_signatures.iter().enumerate() {
        if signature.is_construct() {
            if !allow_generic && !signature.type_parameters.is_empty()
                || signature.implicit_any_return
                || signature.type_predicate.is_some()
                || signature.parameters.iter().any(|parameter| parameter.implicit_any_rest)
                || host.node(signature.declaration).is_none_or(|record| {
                    !matches!(&record.data, NodeData::ConstructSignatureDeclaration(data)
                        if data.parameters.nodes.iter().all(|&node| {
                            let parameter = NodeRef::new(signature.declaration.arena, signature.declaration.file, node);
                            matches!(host.node(parameter).map(|record| &record.data), Some(NodeData::ParameterDeclaration(data)) if data.dot_dot_dot_token.is_none())
                        }))
                })
            {
                return Err(unsupported(signature.declaration, SyntaxKind::ConstructSignature));
            }
            construct_indexes.push(index);
        }
    }
    Ok(DeclaredConstructorValuePlan {
        value_symbol,
        value_declaration: declaration,
        value_annotation: annotation,
        owner,
        construct_indexes: construct_indexes.into_boxed_slice(),
    })
}

fn validate_plan(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &DeclaredConstructorValuePlan,
) -> Result<(), DeclaredConstructorValueError> {
    if plan_declared_constructor_value(store, host, plan.value_symbol())? == *plan {
        Ok(())
    } else {
        Err(DeclaredConstructorValueError::InvalidValue(
            plan.value_symbol,
        ))
    }
}

fn validate_ready_annotation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<(), DeclaredConstructorValueError> {
    let invalid = || DeclaredConstructorValueError::InvalidSignature(node);
    let record = host.node(node).ok_or_else(invalid)?;
    object_members::cached_constructor_interface_annotation(store, node).ok_or_else(invalid)?;
    if let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data {
        return validate_ready_annotation(
            store,
            host,
            NodeRef::new(node.arena, node.file, parenthesized.type_),
        );
    }
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return Ok(());
    };
    let name = NodeRef::new(node.arena, node.file, reference.type_name);
    let symbol = host
        .name_resolver_host(store)?
        .resolve_entity_name(name, SymbolFlags::TYPE)
        .map_err(|_| invalid())?
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(invalid)?;
    validate_reference_name_cache(store, host, node, symbol)?;
    let type_ = store
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .ok_or_else(invalid)?;
    if store
        .symbol_node_links(node)
        .and_then(|links| links.resolved_symbol)
        != Some(symbol)
        || !store.source_direct_type_annotation_is_exact(node, type_)
    {
        return Err(invalid());
    }
    let owner = store.symbol(symbol).ok_or_else(invalid)?;
    if reference.type_arguments.is_none()
        && owner
            .flags()
            .intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE)
        && preflight_class_or_interface_reference(store, host, symbol, owner.flags())? == 0
        && store
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            != Some(type_)
    {
        return Err(invalid());
    }
    Ok(())
}

fn validate_reference_name_cache(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    annotation: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<(), DeclaredConstructorValueError> {
    let invalid = || DeclaredConstructorValueError::InvalidSignature(annotation);
    let Some(NodeData::TypeReferenceNode(reference)) = host.node(annotation).map(|node| &node.data)
    else {
        return Err(invalid());
    };
    let name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
    if store
        .symbol_node_links(name)
        .and_then(|links| links.resolved_symbol)
        .is_some_and(|cached| cached != symbol)
    {
        return Err(invalid());
    }
    Ok(())
}

fn validate_partial_annotation_admission(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<(), DeclaredConstructorValueError> {
    let invalid = || DeclaredConstructorValueError::InvalidSignature(node);
    let record = host.node(node).ok_or_else(invalid)?;
    if let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data {
        return validate_partial_annotation_admission(
            store,
            host,
            NodeRef::new(node.arena, node.file, parenthesized.type_),
        );
    }
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return Ok(());
    };
    let name = NodeRef::new(node.arena, node.file, reference.type_name);
    if host
        .node(name)
        .is_none_or(|name| name.kind != SyntaxKind::Identifier)
    {
        return Err(unsupported(node, record.kind));
    }
    let symbol = host
        .name_resolver_host(store)?
        .resolve_entity_name(name, SymbolFlags::TYPE)
        .map_err(|_| invalid())?
        .and_then(|symbol| store.get_merged_symbol(symbol));
    if let Some(symbol) = symbol {
        let owner = store.symbol(symbol).ok_or_else(invalid)?;
        let declarations = owner.declarations().ok_or_else(invalid)?;
        let provided = reference
            .type_arguments
            .as_ref()
            .map_or(0, |arguments| arguments.nodes.len());
        for &declaration in declarations {
            if !host.symbol_matches(store, declaration, symbol) {
                return Err(invalid());
            }
            let parameters = match host.node(declaration).map(|node| &node.data) {
                Some(NodeData::TypeAliasDeclaration(alias)) => alias.type_parameters.as_ref(),
                Some(NodeData::InterfaceDeclaration(interface)) => {
                    interface.type_parameters.as_ref()
                }
                Some(NodeData::ClassDeclaration(class)) => class.type_parameters.as_ref(),
                _ => continue,
            };
            if parameters.is_some_and(|parameters| {
                provided < parameters.nodes.len()
                    && parameters.nodes[provided..].iter().all(|&parameter| {
                        matches!(host.node(NodeRef::new(declaration.arena, declaration.file, parameter)).map(|node| &node.data),
                            Some(NodeData::TypeParameterDeclaration(parameter)) if parameter.default_type.is_some())
                    })
            }) {
                return Err(unsupported(node, record.kind));
            }
        }
    }
    for &argument in reference
        .type_arguments
        .as_ref()
        .map_or(&[][..], |arguments| arguments.nodes.as_slice())
    {
        validate_partial_annotation_admission(
            store,
            host,
            NodeRef::new(node.arena, node.file, argument),
        )?;
    }
    Ok(())
}

/// Reads a complete value binding. An interface may still have lazy members.
pub(super) fn resolve_declared_constructor_value(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &DeclaredConstructorValuePlan,
) -> Result<Option<DeclaredConstructorValue>, DeclaredConstructorValueError> {
    validate_plan(store, host, plan)?;
    let invalid = || DeclaredConstructorValueError::InvalidValue(plan.value_symbol);
    validate_reference_name_cache(store, host, plan.value_annotation, plan.owner.symbol)
        .map_err(|_| invalid())?;
    let owner = store
        .declared_type_links(plan.owner_symbol())
        .and_then(|links| links.declared_type);
    if let Some(type_) = owner {
        interface_state(store, &plan.owner, type_)?;
    }
    let value = store
        .value_symbol_links(plan.value_symbol)
        .and_then(|links| links.resolved_type);
    let annotation = store
        .type_node_links(plan.value_annotation())
        .and_then(|links| links.resolved_type);
    let resolved_symbol = store
        .symbol_node_links(plan.value_annotation)
        .and_then(|links| links.resolved_symbol);
    if store
        .value_symbol_links(plan.value_symbol)
        .is_some_and(|links| {
            links
                != &ValueSymbolLinks {
                    resolved_type: value,
                    ..ValueSymbolLinks::default()
                }
        })
        || store
            .type_node_links(plan.value_annotation)
            .is_some_and(|links| {
                links
                    != &TypeNodeLinks {
                        resolved_type: annotation,
                        ..TypeNodeLinks::default()
                    }
            })
        || value.is_some_and(|type_| Some(type_) != owner)
        || annotation.is_some_and(|type_| Some(type_) != owner)
        || resolved_symbol.is_some_and(|symbol| symbol != plan.owner.symbol)
    {
        return Err(invalid());
    }
    Ok(match (owner, value, annotation, resolved_symbol) {
        (Some(constructor_type), Some(_), Some(_), Some(_)) => Some(DeclaredConstructorValue {
            value_symbol: plan.value_symbol,
            constructor_type,
        }),
        _ => None,
    })
}

/// Publishes only the declared value's type identity and annotation links.
#[allow(clippy::too_many_arguments)] // Both preparation operations keep the caller's query context.
pub(super) fn prepare_declared_constructor_value(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    _globals: &CanonicalGlobalTypes,
    _options: CanonicalCheckerOptions,
    _session: &mut InstantiationSession,
    _diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &DeclaredConstructorValuePlan,
) -> Result<DeclaredConstructorValue, DeclaredConstructorValueError> {
    if let Some(value) = resolve_declared_constructor_value(store, host, plan)? {
        return Ok(value);
    }
    if !store.try_reserve_value_symbol_links(1)
        || !store.try_reserve_type_node_links(1)
        || !store.try_reserve_symbol_node_links(1)
    {
        return Err(DeclaredConstructorValueError::Capacity(
            plan.value_declaration(),
        ));
    }
    let type_ = store.get_declared_type_of_symbol(host, plan.owner.symbol)?;
    interface_state(store, &plan.owner, type_)?;
    assert!(store.set_value_symbol_links(
        plan.value_symbol,
        ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        }
    ));
    assert!(store.set_type_node_links(
        plan.value_annotation,
        TypeNodeLinks {
            resolved_type: Some(type_),
            ..TypeNodeLinks::default()
        }
    ));
    assert!(store.set_symbol_node_links(
        plan.value_annotation,
        SymbolNodeLinks {
            resolved_symbol: Some(plan.owner.symbol),
        }
    ));
    resolve_declared_constructor_value(store, host, plan)?.ok_or(
        DeclaredConstructorValueError::InvalidValue(plan.value_symbol),
    )
}

/// Reads one original overload without resolving any other overload.
pub(super) fn resolve_declared_construct_signature(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &DeclaredConstructorValuePlan,
    declaration: NodeRef,
) -> Result<Option<DeclaredConstructSignature>, DeclaredConstructorValueError> {
    validate_plan(store, host, plan)?;
    let planned = plan
        .signature(declaration)
        .ok_or(DeclaredConstructorValueError::InvalidSignature(declaration))?;
    validate_partial_annotation_admission(store, host, planned.return_type)?;
    for parameter in &planned.parameters {
        validate_partial_annotation_admission(store, host, parameter.type_node)?;
    }
    let value = resolve_declared_constructor_value(store, host, plan)?;
    let Some(signature) =
        object_members::resolve_single_construct_signature(store, &plan.owner, planned)?
    else {
        return Ok(None);
    };
    let Some(value) = value else {
        return Ok(None);
    };
    let return_type = store
        .signature(signature)
        .and_then(super::signatures::Signature::resolved_return_type)
        .ok_or(DeclaredConstructorValueError::InvalidSignature(declaration))?;
    validate_ready_annotation(store, host, planned.return_type)?;
    for parameter in &planned.parameters {
        validate_ready_annotation(store, host, parameter.type_node)?;
    }
    Ok(Some(DeclaredConstructSignature {
        value,
        declaration,
        signature,
        return_type,
    }))
}

/// Resolves the requested annotations in the caller's session, then publishes
/// one original construct signature. No overload result is replaced or merged.
#[allow(clippy::too_many_arguments)] // The retained overload and caller query context are independent.
pub(super) fn prepare_declared_construct_signature(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &DeclaredConstructorValuePlan,
    declaration: NodeRef,
) -> Result<DeclaredConstructSignature, DeclaredConstructorValueError> {
    if let Some(signature) = resolve_declared_construct_signature(store, host, plan, declaration)? {
        return Ok(signature);
    }
    let planned = plan
        .signature(declaration)
        .ok_or(DeclaredConstructorValueError::InvalidSignature(declaration))?;
    prepare_declared_constructor_value(store, host, globals, options, session, diagnostics, plan)?;
    let mut parameter_types = Vec::with_capacity(planned.parameters.len());
    for parameter in &planned.parameters {
        let annotation = CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            globals,
            options,
            session,
            diagnostics,
        )?
        .get_type_from_type_node(parameter.type_node)?;
        parameter_types.push(object_members::prepare_declared_construct_parameter_type(
            store, planned, parameter, annotation,
        )?);
    }
    let return_type = CanonicalTypeQuery::new_with_global_types_and_session(
        store,
        host,
        globals,
        options,
        session,
        diagnostics,
    )?
    .get_type_from_type_node(planned.return_type)?;
    if object_members::cached_constructor_interface_annotation(store, planned.return_type)
        != Some(return_type)
    {
        return Err(unsupported(
            planned.return_type,
            host.node(planned.return_type)
                .map_or(SyntaxKind::Unknown, |node| node.kind),
        ));
    }
    validate_ready_annotation(store, host, planned.return_type)?;
    object_members::publish_single_construct_signature(
        store,
        &plan.owner,
        planned,
        &ResolvedCallSignatureTypes {
            parameter_types,
            return_type,
        },
    )?;
    resolve_declared_construct_signature(store, host, plan, declaration)?
        .ok_or(DeclaredConstructorValueError::InvalidSignature(declaration))
}

#[cfg(test)]
mod global_tests {
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, IntrinsicBootstrapOptions,
        instantiate::{InstantiationLimits, instantiate_type_with_session},
        production::GlobalMergeCompletion,
    };

    const LIBRARY: &str = "interface Array<T> {} interface ReadonlyArray<T> {}\n\
        interface NumberResult { value: number; } interface TextResult { value: string; }\n\
        interface Creator { marker: number; }\n\
        declare var Creator: { prototype: NumberResult; values: number[];\n\
        new(value?: number): NumberResult; new(value?: string): TextResult;\n\
        make(value?: number): NumberResult; };";
    const AUGMENTATION: &str = "export {}; declare global {\n\
        interface Creator { extension: string; }\n\
        var Creator: typeof globalThis extends { onmessage: any; Creator: infer T } ? T : never;\n\
        }";

    fn context<'arena>(
        sources: &[(&'arena ParseResult, FileId, bool, bool)],
        options: CanonicalCheckerOptions,
    ) -> CanonicalCheckerContext<'arena> {
        let mut binder = CanonicalBinder::new();
        for (index, &(parsed, file, library, external)) in sources.iter().enumerate() {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!("\"/global-constructor-{index}.d.ts\"")),
                        CanonicalSourceLanguage::TypeScript,
                        true,
                        library,
                        if external {
                            CanonicalModuleState::External
                        } else {
                            CanonicalModuleState::Script
                        },
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            sources
                .iter()
                .map(|&(parsed, file, _, _)| (file, &parsed.arena))
                .collect(),
            options,
        )
        .unwrap()
    }

    fn global(store: &CanonicalTypeMapperStore, name: &str) -> SemanticSymbolId {
        store
            .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
            .and_then(|table| table.get_source(name))
            .and_then(|symbol| store.get_merged_symbol(symbol))
            .unwrap()
    }

    fn nodes(sources: &[(&ParseResult, FileId)]) -> Vec<NodeRef> {
        sources
            .iter()
            .flat_map(|&(parsed, file)| {
                parsed
                    .arena
                    .iter()
                    .map(move |(node, _)| NodeRef::new(parsed.arena.id(), file, node))
            })
            .collect()
    }

    fn snapshot(
        store: &CanonicalTypeMapperStore,
        nodes: &[NodeRef],
    ) -> impl std::fmt::Debug + PartialEq + use<> {
        (
            [
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.index_info_len(),
                store.type_alias_len(),
                store.conditional_root_len(),
                store.callable_signature_parameter_types_len(),
                store.symbol_store().symbol_table_len(),
            ],
            store.checker_link_allocated_lengths(),
            store.relation_state_snapshot(),
            format!("{:?}", store.types().collect::<Vec<_>>()),
            format!("{:?}", store.signatures().collect::<Vec<_>>()),
            nodes
                .iter()
                .map(|&node| {
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            store
                .symbol_store()
                .symbols()
                .map(|(symbol, record)| {
                    (
                        format!("{record:?}"),
                        store.value_symbol_links(symbol).cloned(),
                        store.declared_type_links(symbol).cloned(),
                        store.type_alias_links(symbol).cloned(),
                        store.declared_value_provenance(symbol),
                    )
                })
                .collect::<Vec<_>>(),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn rejected_without_writes(
        store: &mut CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        globals: &CanonicalGlobalTypes,
        options: CanonicalCheckerOptions,
        plan: &GlobalConstructorValuePlan,
        nodes: &[NodeRef],
        session: &mut InstantiationSession,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) {
        let before = (
            snapshot(store, nodes),
            session.query_count(),
            session.total_count(),
            session.limit_event_count(),
            diagnostics.clone(),
        );
        for _ in 0..2 {
            assert!(
                resolve_global_constructor_candidates(store, host, globals, options, plan).is_err()
            );
            assert!(
                prepare_global_constructor_candidates(
                    store,
                    host,
                    globals,
                    options,
                    session,
                    diagnostics,
                    plan,
                )
                .is_err()
            );
            assert_eq!(
                (
                    snapshot(store, nodes),
                    session.query_count(),
                    session.total_count(),
                    session.limit_event_count(),
                    diagnostics.clone()
                ),
                before
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn global_constructor_rejects_changed_merge_and_later_cached_members_then_restores() {
        let library = parse_source_file(LIBRARY);
        let augmentation = parse_source_file(AUGMENTATION);
        let library_file = FileId::new(9_780);
        let augmentation_file = FileId::new(9_781);
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: true,
            },
            ..CanonicalCheckerOptions::default()
        };
        let mut context = context(
            &[
                (&library, library_file, true, false),
                (&augmentation, augmentation_file, false, true),
            ],
            options,
        );
        let library_bound = context.file(library_file).unwrap().1.clone();
        let augmentation_bound = context.file(augmentation_file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [
                (&library.arena, &library_bound),
                (&augmentation.arena, &augmentation_bound),
            ],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let globals = context.global_types().clone();
        let nodes = nodes(&[(&library, library_file), (&augmentation, augmentation_file)]);
        let store = context.store_mut_for_test();
        let owner = global(store, "Creator");
        let cold = snapshot(store, &nodes);
        let plan = plan_global_constructor_value(store, &host, &globals, options, owner)
            .unwrap()
            .unwrap();
        assert_eq!(
            resolve_global_constructor_candidates(store, &host, &globals, options, &plan),
            Ok(None)
        );
        assert_eq!(snapshot(store, &nodes), cold);
        let declarations = store
            .symbol(owner)
            .unwrap()
            .declarations()
            .unwrap()
            .to_vec();
        assert_eq!(declarations.len(), 4);
        let augmentation_value = declarations
            .iter()
            .copied()
            .find(|&node| {
                node.file == augmentation_file
                    && store.source_node_kind(node) == Some(SyntaxKind::VariableDeclaration)
            })
            .unwrap();
        let conditional = store
            .source_direct_type_annotation(augmentation_value)
            .unwrap();
        assert!(store.type_node_links(conditional).is_none());
        let mut session = InstantiationSession::new(InstantiationLimits::default());
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let ready = prepare_global_constructor_candidates(
            store,
            &host,
            &globals,
            options,
            &mut session,
            &mut diagnostics,
            &plan,
        )
        .unwrap();
        assert_eq!(ready.signatures().len(), 2);
        assert_ne!(
            ready.signatures()[0].return_type(),
            ready.signatures()[1].return_type()
        );
        assert_ne!(
            ready.value().constructor_type(),
            ready.signatures()[0].return_type()
        );
        assert_eq!(ready.value().value_symbol(), owner);
        assert!(plan.owner.properties.iter().all(|property| {
            store
                .value_symbol_links(property.symbol)
                .is_some_and(|links| links.resolved_type.is_some())
        }));
        assert!(store.type_node_links(conditional).is_none());
        let value_type = ready.value().constructor_type();
        assert!(store.validate_cached_array_capability(value_type).is_err());
        let warm = (
            snapshot(store, &nodes),
            session.query_count(),
            session.total_count(),
            diagnostics.clone(),
        );
        assert_eq!(
            prepare_global_constructor_candidates(
                store,
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                &plan,
            ),
            Ok(ready.clone())
        );
        assert_eq!(
            (
                snapshot(store, &nodes),
                session.query_count(),
                session.total_count(),
                diagnostics.clone()
            ),
            warm
        );

        let globals_table = store.intrinsic_bootstrap().unwrap().globals;
        let table_symbol = store
            .symbol_table(globals_table)
            .unwrap()
            .get_source("Creator")
            .unwrap();
        let other = global(store, "NumberResult");
        assert_eq!(
            store.insert_symbol(globals_table, EscapedName::source("Creator"), other),
            Some(Some(table_symbol))
        );
        rejected_without_writes(
            store,
            &host,
            &globals,
            options,
            &plan,
            &nodes,
            &mut session,
            &mut diagnostics,
        );
        assert_eq!(
            store.insert_symbol(globals_table, EscapedName::source("Creator"), table_symbol),
            Some(Some(other))
        );
        for (changed, selector) in [
            (
                declarations.iter().rev().copied().collect(),
                plan.value_declaration(),
            ),
            (
                declarations
                    .iter()
                    .copied()
                    .filter(|&node| node != augmentation_value)
                    .collect(),
                plan.value_declaration(),
            ),
            (declarations.clone(), augmentation_value),
        ] {
            assert!(store.set_symbol_declarations(owner, Some(changed), Some(selector)));
            rejected_without_writes(
                store,
                &host,
                &globals,
                options,
                &plan,
                &nodes,
                &mut session,
                &mut diagnostics,
            );
            assert!(store.set_symbol_declarations(
                owner,
                Some(declarations.clone()),
                Some(plan.value_declaration())
            ));
        }
        let raw = augmentation_bound.symbol(augmentation_value).unwrap();
        let raw_record = store.symbol(raw).unwrap();
        let relationships = (
            raw_record.members(),
            raw_record.exports(),
            raw_record.parent(),
            raw_record.export_symbol(),
        );
        assert!(store.set_symbol_relationships(
            raw,
            relationships.0,
            relationships.1,
            None,
            relationships.3,
        ));
        rejected_without_writes(
            store,
            &host,
            &globals,
            options,
            &plan,
            &nodes,
            &mut session,
            &mut diagnostics,
        );
        assert!(store.set_symbol_relationships(
            raw,
            relationships.0,
            relationships.1,
            relationships.2,
            relationships.3,
        ));

        let mut no_array = globals.clone();
        no_array.array_type = globals.readonly_array_type;
        rejected_without_writes(
            store,
            &host,
            &no_array,
            options,
            &plan,
            &nodes,
            &mut session,
            &mut diagnostics,
        );
        let foreign_library =
            parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let foreign = self::context(
            &[(&foreign_library, FileId::new(9_782), true, false)],
            options,
        );
        let mut foreign_arrays = globals.clone();
        foreign_arrays.array_type = foreign.global_types().array_type;
        foreign_arrays.readonly_array_type = foreign.global_types().readonly_array_type;
        rejected_without_writes(
            store,
            &host,
            &foreign_arrays,
            options,
            &plan,
            &nodes,
            &mut session,
            &mut diagnostics,
        );
        rejected_without_writes(
            store,
            &host,
            &globals,
            CanonicalCheckerOptions {
                no_emit: !options.no_emit,
                ..options
            },
            &plan,
            &nodes,
            &mut session,
            &mut diagnostics,
        );

        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let later = ready.signatures()[1];
        let later_plan = &plan.owner.call_signatures[plan.construct_indexes[1]];
        let original_return = store
            .type_node_links(later_plan.return_type)
            .cloned()
            .unwrap();
        assert!(store.set_type_node_links(
            later_plan.return_type,
            TypeNodeLinks {
                resolved_type: Some(ready.signatures()[0].return_type()),
                ..TypeNodeLinks::default()
            }
        ));
        assert!(store.set_signature_resolved_return_type(
            later.signature(),
            Some(ready.signatures()[0].return_type())
        ));
        rejected_without_writes(
            store,
            &host,
            &globals,
            options,
            &plan,
            &nodes,
            &mut session,
            &mut diagnostics,
        );
        assert!(store.set_type_node_links(later_plan.return_type, original_return));
        assert!(
            store.set_signature_resolved_return_type(later.signature(), Some(later.return_type()))
        );

        let method = plan.owner.methods[0].symbol;
        for symbol in [owner, method, later_plan.parameters[0].symbol] {
            let original = store.value_symbol_links(symbol).cloned().unwrap();
            assert!(store.set_value_symbol_links(
                symbol,
                ValueSymbolLinks {
                    resolved_type: Some(number),
                    ..ValueSymbolLinks::default()
                }
            ));
            rejected_without_writes(
                store,
                &host,
                &globals,
                options,
                &plan,
                &nodes,
                &mut session,
                &mut diagnostics,
            );
            assert!(store.set_value_symbol_links(symbol, original));
        }
        let original = store
            .type_node_links(plan.value_annotation())
            .cloned()
            .unwrap();
        assert!(store.set_type_node_links(
            plan.value_annotation(),
            TypeNodeLinks {
                resolved_type: Some(later.return_type()),
                ..TypeNodeLinks::default()
            }
        ));
        rejected_without_writes(
            store,
            &host,
            &globals,
            options,
            &plan,
            &nodes,
            &mut session,
            &mut diagnostics,
        );
        assert!(store.set_type_node_links(plan.value_annotation(), original));

        let members = plan.owner.members.unwrap();
        let prototype = store
            .symbol_table(members)
            .unwrap()
            .get_source("prototype")
            .unwrap();
        assert_eq!(
            store.insert_symbol(members, EscapedName::source("prototype"), method),
            Some(Some(prototype))
        );
        rejected_without_writes(
            store,
            &host,
            &globals,
            options,
            &plan,
            &nodes,
            &mut session,
            &mut diagnostics,
        );
        assert_eq!(
            store.insert_symbol(members, EscapedName::source("prototype"), prototype),
            Some(Some(method))
        );
        assert!(store.set_type_node_links(
            conditional,
            TypeNodeLinks {
                resolved_type: Some(number),
                ..TypeNodeLinks::default()
            }
        ));
        rejected_without_writes(
            store,
            &host,
            &globals,
            options,
            &plan,
            &nodes,
            &mut session,
            &mut diagnostics,
        );
        assert!(store.set_type_node_links(conditional, TypeNodeLinks::default()));

        let restored = snapshot(store, &nodes);
        assert_eq!(
            resolve_global_constructor_candidates(store, &host, &globals, options, &plan),
            Ok(Some(ready.clone()))
        );
        assert_eq!(
            prepare_global_constructor_candidates(
                store,
                &host,
                &globals,
                options,
                &mut session,
                &mut diagnostics,
                &plan,
            ),
            Ok(ready)
        );
        assert_eq!(snapshot(store, &nodes), restored);
        assert!(diagnostics.is_empty());
        assert_eq!(session.limit_event_count(), 0);
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn global_constructor_full_query_keeps_the_spent_caller_and_annotation_diagnostic() {
        let library = parse_source_file(
            "interface Budget<T> {} type Choice<L, R> = L | R;\n\
            type NeedsNumber<T extends number> = T;\n\
            declare var Factory: { new(value: Choice<string, number>): NeedsNumber<string>; };",
        );
        let file = FileId::new(9_783);
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&[(&library, file, true, false)], options);
        let bound = context.file(file).unwrap().1.clone();
        let host = DeclaredTypeHost::new_after_global_merge(
            [(&library.arena, &bound)],
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let globals = context.global_types().clone();
        let store = context.store_mut_for_test();
        let owner = global(store, "Factory");
        let plan = plan_global_constructor_value(store, &host, &globals, options, owner)
            .unwrap()
            .unwrap();
        let budget = store
            .symbol(global(store, "Budget"))
            .unwrap()
            .declarations()
            .unwrap()[0];
        let NodeData::InterfaceDeclaration(interface) = &host.node(budget).unwrap().data else {
            unreachable!()
        };
        let parameter = NodeRef::new(
            budget.arena,
            file,
            interface.type_parameters.as_ref().unwrap().nodes[0],
        );
        let parameter_symbol = bound.symbol(parameter).unwrap();
        let parameter_type = store
            .get_declared_type_of_symbol(&host, parameter_symbol)
            .unwrap();
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let mapper = store
            .new_type_mapper(vec![parameter_type], vec![number])
            .unwrap();
        let mut spent = InstantiationSession::new(InstantiationLimits {
            max_depth: 100,
            max_count: 1,
        });
        assert_eq!(
            instantiate_type_with_session(
                store,
                parameter_type,
                mapper,
                Some(CanonicalArrayTargets::from_global_types(&globals)),
                &mut spent
            ),
            Ok(number)
        );
        assert_eq!(
            (
                spent.query_count(),
                spent.total_count(),
                spent.limit_event_count()
            ),
            (1, 1, 0)
        );
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(matches!(
            prepare_global_constructor_candidates(
                store,
                &host,
                &globals,
                options,
                &mut spent,
                &mut diagnostics,
                &plan,
            ),
            Err(DeclaredConstructorValueError::DeclaredType(_))
        ));
        assert_eq!(
            (
                spent.query_count(),
                spent.total_count(),
                spent.limit_event_count()
            ),
            (1, 1, 1)
        );
        assert!(
            store
                .value_symbol_links(owner)
                .is_none_or(|links| links.resolved_type.is_none())
        );
        assert!(store.declared_value_provenance(owner).is_none());
        assert!(diagnostics.is_empty());

        let mut fresh = InstantiationSession::new(InstantiationLimits::default());
        let ready = prepare_global_constructor_candidates(
            store,
            &host,
            &globals,
            options,
            &mut fresh,
            &mut diagnostics,
            &plan,
        )
        .unwrap();
        assert_eq!(
            (
                fresh.query_count(),
                fresh.total_count(),
                fresh.limit_event_count()
            ),
            (2, 2, 0)
        );
        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|entry| entry.diagnostic.code())
                .collect::<Vec<_>>(),
            [2344]
        );
        let nodes = nodes(&[(&library, file)]);
        let warm = (
            snapshot(store, &nodes),
            diagnostics.clone(),
            spent.limit_event_count(),
        );
        assert_eq!(
            prepare_global_constructor_candidates(
                store,
                &host,
                &globals,
                options,
                &mut spent,
                &mut diagnostics,
                &plan,
            ),
            Ok(ready)
        );
        assert_eq!(
            (
                snapshot(store, &nodes),
                diagnostics.clone(),
                spent.limit_event_count()
            ),
            warm
        );
        assert_eq!((spent.query_count(), spent.total_count()), (1, 1));
    }

    #[test]
    fn global_constructor_route_keeps_local_named_conditional_and_generic_boundaries() {
        for (source, library, generic) in [
            (
                "declare var Build: { new(value: number): string };",
                false,
                false,
            ),
            (
                "interface Maker { new(): string } declare var Build: Maker;",
                true,
                false,
            ),
            ("declare var Build: { prototype: string };", true, false),
            (
                "declare var Build: true extends true ? { new(): string } : never;",
                true,
                false,
            ),
            ("declare var Build: { new<T>(value: T): T };", true, true),
        ] {
            let parsed = parse_source_file(source);
            let file = FileId::new(9_784);
            let options = CanonicalCheckerOptions::default();
            let context = context(&[(&parsed, file, library, false)], options);
            let bound = context.file(file).unwrap().1.clone();
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&parsed.arena, &bound)],
                GlobalMergeCompletion::for_test(options.name_resolution),
            )
            .unwrap();
            let store = context.store();
            let nodes = nodes(&[(&parsed, file)]);
            let before = snapshot(store, &nodes);
            let planned = plan_global_constructor_value(
                store,
                &host,
                context.global_types(),
                options,
                global(store, "Build"),
            );
            if generic {
                assert!(planned.is_err());
            } else {
                assert_eq!(planned, Ok(None));
            }
            assert_eq!(snapshot(store, &nodes), before);
        }
    }
}
