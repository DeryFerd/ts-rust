//! Source evidence for an alias request. The mapped object keeps a separate
//! physical construction proof and does not own this reference's binding.

use super::*;

impl TypeQueryPlan {
    pub(super) fn cached_mapped_alias_arguments(&self, store: &CanonicalTypeMapperStore,
        reference: &PlannedTypeReference, header: &TypeAliasPlan, parameters: &[TypeId],
        provided: &[TypeId], arrays: Option<CanonicalArrayTargets>,
        source: Option<(&CanonicalGlobalTypes, &dyn ConditionalBranchSource)>,
    ) -> Result<Vec<TypeId>, DeclaredTypeError> {
        let invalid = || type_node_unavailable(TypeNodeUnavailable::InvalidGenericAliasInstantiationCache(reference.symbol));
        if provided.len() != reference.type_arguments.len() || parameters.len() != header.type_parameters.len() || provided.len() > parameters.len() { return Err(invalid()); }
        let mut arguments = provided.to_vec();
        for parameter in header.type_parameters.iter().skip(arguments.len()) {
            let node = parameter.default_type.ok_or_else(invalid)?;
            let raw = self.cached_type_query_result_with_source(store, arrays, None, &[], node,
                SourceCallableTypeReplay::Operational, &mut HashSet::new(), source)?.ok_or_else(invalid)?;
            let result = if let Some(operand) = self.source_alias_operands.get(&node) {
                let graph = store.source_alias_default_graph(node).ok_or_else(invalid)?;
                if !graph.matches_operand(&operand.source, node, raw) { return Err(invalid()); }
                super::super::instantiate::cached_source_alias_operand_instantiation(store, graph, raw,
                    &parameters[..arguments.len()], &arguments, arrays)
            } else if let Some((globals, source)) = source {
                super::super::instantiate::cached_instantiation_with_vector_and_source(store, raw,
                    &parameters[..arguments.len()], &arguments, globals, source)
            } else {
                super::super::instantiate::cached_instantiation_with_vector(store, raw,
                    &parameters[..arguments.len()], &arguments, arrays, None)
            }.map_err(|error| match error {
                super::super::instantiate::InstantiationError::Declared(error) => error,
                _ => invalid(),
            })?.ok_or_else(invalid)?;
            arguments.push(result);
        }
        Ok(arguments)
    }
}

pub(in crate::semantic) struct SourceMappedAliasRequestInput<'a> {
    pub(super) node: NodeRef,
    pub(super) reference: &'a PlannedTypeReference,
    pub(super) declared_type: TypeId,
    pub(super) parameters: &'a [TypeId],
    pub(super) arguments: &'a [TypeId],
    pub(super) requested_alias: Option<(SemanticSymbolId, &'a [TypeId])>,
    pub(super) plan: &'a TypeQueryPlan,
}

impl SourceMappedAliasRequestInput<'_> {
    pub(super) fn prove(self, store: &CanonicalTypeMapperStore, context: &SourceTypeQueryContext<'_, '_>) -> Result<SourceMappedAliasRequestProof, DeclaredTypeError> {
        context.prove_mapped_alias_request(store, self.node, self.reference, self.declared_type,
            self.parameters, self.arguments, self.requested_alias, self.plan)
    }
}

impl TypeQueryPlanner<'_, '_, '_, '_> {
    pub(super) fn prove_cached_mapped_alias_owner_request(
        &self,
        node: NodeRef,
        owner: SemanticSymbolId,
        declared_type: TypeId,
    ) -> Result<Option<SourceMappedAliasRequestProof>, DeclaredTypeError> {
        if self.source_context.is_none()
            || !matches!(self.store.type_payload(declared_type).map(TypeRecord::data), Some(TypeData::Mapped(_)))
        {
            return Ok(None);
        }
        let reference = self.mapped_alias_reference_header(node, Some(owner))?;
        let invalid = || type_node_unavailable(TypeNodeUnavailable::InvalidCachedTypeAlias(owner));
        let parameters = self.store.type_alias_links(reference.symbol)
            .and_then(|links| links.type_parameters.as_deref()).ok_or_else(invalid)?;
        let arguments = reference.type_arguments.iter().map(|argument| self.cached_type_node_identity(owner, *argument))
            .collect::<Result<Vec<_>, _>>()?;
        let owner_arguments = self.store.type_alias_links(owner)
            .and_then(|links| links.type_parameters.as_deref()).unwrap_or_default();
        self.prove_cached_mapped_alias_request(node, declared_type, parameters, &arguments,
            reference.alias_owner.map(|owner| (owner, owner_arguments)))
    }

    /// Rechecks a source alias binding without planning its pending RHS.
    fn mapped_alias_reference_header(&self, node: NodeRef, alias_owner: Option<SemanticSymbolId>) -> Result<PlannedTypeReference, DeclaredTypeError> {
        let invalid = || type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node));
        let record = preflight_node(self.store, self.host, node)?;
        let (name_id, heritage) = match &record.data {
            NodeData::TypeReferenceNode(reference) if record.kind == SyntaxKind::TypeReference => (reference.type_name, false),
            NodeData::ExpressionWithTypeArguments(reference) if record.kind == SyntaxKind::ExpressionWithTypeArguments && reference.facts == 0 => (reference.expression, true),
            _ => return Err(invalid()),
        };
        let name = NodeRef::new(node.arena, node.file, name_id);
        let name_record = preflight_node(self.store, self.host, name)?;
        if name_record.parent != Some(node.node) || name_record.flags.0 & NODE_FLAG_JSDOC != 0 { return Err(invalid()); }
        let (name_text, qualified) = match &name_record.data {
            NodeData::Identifier(identifier) => (identifier.text.as_str(), false),
            NodeData::QualifiedName(qualified) => {
                let right = NodeRef::new(node.arena, node.file, qualified.right);
                let right_record = preflight_node(self.store, self.host, right)?;
                let NodeData::Identifier(identifier) = &right_record.data else { return Err(invalid()); };
                if right_record.parent != Some(name.node) { return Err(invalid()); }
                (identifier.text.as_str(), true)
            }
            _ => return Err(invalid()),
        };
        let type_arguments = self.type_reference_argument_nodes(node)?;
        let exact = self.type_reference_alias_targets.get(&node).copied();
        let exact = if exact.is_none() && !qualified && !heritage { self.cached_source_annotation_type_import(node)? } else { exact };
        if qualified && exact.is_some() { return Err(invalid()); }
        let property_import = if qualified || heritage { None } else {
            source_imports::plan_source_property_type_import(self.store, self.host, node).map_err(|error| property_type_import_error(node, error))?
        };
        let class_annotation_import = if qualified || heritage || property_import.is_some() { None } else {
            source_imports::plan_source_class_annotation_type_import(self.store, self.host, node).map_err(|error| property_type_import_error(node, error))?
        };
        let implementation_import = if heritage && self.source_class_heritage == Some(node) {
            plan_source_class_heritage_import(self.store, self.host, node)?
        } else { None };
        let interface_heritage_import = if heritage && self.source_class_heritage != Some(node) {
            source_imports::plan_source_interface_alias_heritage_import(self.store, self.host, node).map_err(|error| property_type_import_error(node, error))?
        } else { None };
        let alias_body_import = if qualified || heritage || property_import.is_some() || class_annotation_import.is_some() { None } else {
            source_imports::probe_source_alias_body_type_import(self.store, self.host, node).map_err(|error| property_type_import_error(node, error))?.plan
        };
        let cached = self.store.symbol_node_links(node).and_then(|links| links.resolved_symbol);
        let symbol = if let Some(import) = &interface_heritage_import {
            if exact.is_some() || property_import.is_some() || alias_body_import.is_some() || class_annotation_import.is_some() || implementation_import.is_some() { return Err(invalid()); }
            import.validate_alias_reference(self.store, node, Some(import.alias_symbol()), import.target_symbol(), &type_arguments)
                .map_err(|error| property_type_import_error(node, error))?;
            import.target_symbol()
        } else if let Some(import) = &implementation_import {
            if exact.is_some() || property_import.is_some() || alias_body_import.is_some() || class_annotation_import.is_some() { return Err(invalid()); }
            import.target()
        } else if let Some(import) = &class_annotation_import {
            if import.reference() != node || import.arguments() != type_arguments
                || self.source_class_annotation.zip(import.class_owner()).is_some_and(|(owner, actual)| owner != actual)
                || exact.is_some_and(|capability| !import.matches_capability(&capability)) { return Err(invalid()); }
            import.target_symbol()
        } else if let Some(import) = &alias_body_import {
            if import.reference() != node || import.arguments() != type_arguments || exact.is_some_and(|capability| !import.matches_capability(&capability)) { return Err(invalid()); }
            import.target_symbol()
        } else if let Some(import) = &property_import {
            if import.annotation() != node || exact.is_some_and(|capability| !import.matches_capability(&capability)) { return Err(invalid()); }
            import.target_symbol()
        } else if let Some(capability) = exact {
            self.resolve_type_reference_alias_target(node, name, name_text, capability, cached)?
        } else {
            self.resolve_uncached_type_reference_symbol(node)?
        };
        let symbol = self.store.get_merged_symbol(symbol).ok_or_else(invalid)?;
        if cached.is_some_and(|cached| cached != symbol)
            || self.store.symbol(symbol).is_none_or(|record| record.flags() != SymbolFlags::TYPE_ALIAS)
        { return Err(invalid()); }
        let (_, header) = plan_type_alias_header(self.store, self.host, symbol)?;
        let count = header.type_parameters.len();
        let minimum = header.type_parameters.iter().enumerate().filter_map(|(index, parameter)| parameter.default_type.is_none().then_some(index + 1)).max().unwrap_or(0);
        let arity = if count == 0 && !type_arguments.is_empty() { PlannedTypeReferenceArity::NotGeneric }
            else if (minimum..=count).contains(&type_arguments.len()) { PlannedTypeReferenceArity::Valid }
            else { PlannedTypeReferenceArity::InvalidGeneric { minimum, maximum: count } };
        let alias_owner = match alias_owner {
            Some(owner) if count != 0 && !self.is_local_type_alias(symbol)? && self.is_local_type_alias(owner)? => None,
            owner => owner,
        };
        Ok(PlannedTypeReference {
            symbol, import_alias: property_import.as_ref().map(SourcePropertyTypeImportPlan::alias_symbol)
                .or_else(|| alias_body_import.as_ref().map(SourceAliasBodyTypeImportPlan::alias_symbol))
                .or_else(|| class_annotation_import.as_ref().map(|import| import.alias_symbol()))
                .or_else(|| exact.map(|capability| capability.alias))
                .or_else(|| implementation_import.as_ref().and_then(|chain| chain.steps.first()).map(|step| step.source.alias()))
                .or_else(|| interface_heritage_import.as_ref().map(|import| import.alias_symbol())),
            interface_heritage_import, implementation_import, class_annotation_import, property_import, alias_body_import,
            type_arguments, alias_owner, arity, global_array_target: None, direct_generic: false,
            direct_generic_constraints: Vec::new(), direct_generic_defaults: Vec::new(),
        })
    }

    pub(super) fn prove_cached_mapped_alias_request(&self, node: NodeRef, declared_type: TypeId,
        parameters: &[TypeId], arguments: &[TypeId], identity: Option<(SemanticSymbolId, &[TypeId])>,
    ) -> Result<Option<SourceMappedAliasRequestProof>, DeclaredTypeError> {
        let Some(context) = &self.source_context else { return Ok(None); };
        let reference = self.mapped_alias_reference_header(node, identity.map(|(owner, _)| owner))?;
        let role = SourceMappedRequestRole::capture(self, node)?;
        let mut plan = TypeQueryPlan::default();
        plan.references.insert(node, reference.clone());
        plan.reference_roles.insert(node, role);
        context.prove_mapped_alias_request(self.store, node, &reference, declared_type, parameters, arguments, identity, &plan).map(Some)
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct SourceMappedRequestRole {
    class: Option<SourceMappedClassRole>,
    callable: Option<Box<SourceCallablePlan>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceMappedClassRole {
    Annotation { owner: SemanticSymbolId, root: NodeRef },
    Heritage { owner: SemanticSymbolId, root: NodeRef },
}

impl SourceMappedRequestRole {
    pub(super) fn capture(planner: &TypeQueryPlanner<'_, '_, '_, '_>, node: NodeRef) -> Result<Self, DeclaredTypeError> {
        let mut role = Self { class: None, callable: planner.source_callable_scope.clone() };
        if let Some(owner) = planner.source_class_annotation {
            let mut current = node;
            let mut seen = HashSet::new();
            loop {
                if !seen.insert(current) {
                    return Err(type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node)));
                }
                if planner.source_class_heritage == Some(current) {
                    preflight_source_class_heritage_owner(planner.store, planner.host, current, owner)?;
                    role.class = Some(SourceMappedClassRole::Heritage { owner, root: current });
                    break;
                }
                if super::super::classes::source_class_annotation_is_owned(planner.store, planner.host, owner, current) {
                    role.class = Some(SourceMappedClassRole::Annotation { owner, root: current });
                    break;
                }
                let Some(parent) = preflight_node(planner.store, planner.host, current)?.parent else {
                    break;
                };
                current = NodeRef::new(current.arena, current.file, parent);
            }
        }
        Ok(role)
    }

    fn validate(&self, store: &CanonicalTypeMapperStore, host: &DeclaredTypeHost<'_>, node: NodeRef) -> Result<(), DeclaredTypeError> {
        let invalid = || type_node_unavailable(TypeNodeUnavailable::InvalidTypeReference(node));
        if let Some(class) = self.class {
            match class {
                SourceMappedClassRole::Annotation { owner, root } => {
                    if !super::super::classes::source_class_annotation_is_owned(store, host, owner, root) {
                        return Err(invalid());
                    }
                    validate_type_annotation_child(store, host, root, node)?;
                }
                SourceMappedClassRole::Heritage { owner, root } => {
                    preflight_source_class_heritage_owner(store, host, root, owner)?;
                    if root != node {
                        let mut current = node;
                        let mut seen = HashSet::new();
                        while current != root {
                            if !seen.insert(current) { return Err(invalid()); }
                            let record = preflight_node(store, host, current)?;
                            let parent = record.parent.map(|parent| NodeRef::new(current.arena, current.file, parent)).ok_or_else(invalid)?;
                            let mut present = false;
                            preflight_node(store, host, parent)?.for_each_child(|child| present |= child == current.node);
                            if !present { return Err(invalid()); }
                            current = parent;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn apply<'store, 'host, 'arena, 'aliases>(
        &self,
        mut planner: TypeQueryPlanner<'store, 'host, 'arena, 'aliases>,
    ) -> Result<TypeQueryPlanner<'store, 'host, 'arena, 'aliases>, DeclaredTypeError> {
        if let Some(class) = self.class {
            match class {
                SourceMappedClassRole::Annotation { owner, .. } => planner.source_class_annotation = Some(owner),
                SourceMappedClassRole::Heritage { owner, root } => {
                    planner.source_class_annotation = Some(owner);
                    planner.source_class_heritage = Some(root);
                }
            }
        }
        if let Some(callable) = &self.callable {
            planner = planner.with_source_callable_scope(callable)?;
        }
        Ok(planner)
    }
}

#[derive(Debug)]
pub(in crate::semantic) struct SourceMappedAliasRequestProof {
    node: NodeRef,
    reference: PlannedTypeReference,
    declared_type: TypeId,
    declaration: NodeRef,
    header: TypeAliasPlan,
    parameters: Vec<TypeId>,
    arguments: Vec<TypeId>,
    requested_alias: Option<(SemanticSymbolId, Vec<TypeId>)>,
    owner: Option<(NodeRef, TypeAliasPlan)>,
    argument_roots: Vec<NodeRef>,
    argument_plan: TypeQueryPlan,
    role: SourceMappedRequestRole,
    defaults: BTreeMap<NodeRef, (TypeId, Option<SourceAliasOperandGraph>)>,
    globals: CanonicalGlobalTypes,
    options: CanonicalTypeQueryOptions,
    aliases: HashMap<NodeRef, CanonicalTypeReferenceAliasTarget>,
    jsdoc: Option<CanonicalJsDocImportTypeTarget>,
}

impl SourceMappedAliasRequestProof {
    pub(super) fn scoped_context<'host, 'arena>(&self, store: &CanonicalTypeMapperStore,
        mut context: SourceTypeQueryContext<'host, 'arena>) -> Result<SourceTypeQueryContext<'host, 'arena>, DeclaredTypeError> {
        self.role.validate(store, context.host, self.node)?;
        context.source_callable_scope = self.role.callable.clone();
        match self.role.class {
            Some(SourceMappedClassRole::Annotation { owner, .. }) => {
                context.source_class_annotation = Some(owner);
                context.source_class_heritage = None;
            }
            Some(SourceMappedClassRole::Heritage { owner, root }) => {
                context.source_class_annotation = Some(owner);
                context.source_class_heritage = Some(root);
            }
            None => {
                context.source_class_annotation = None;
                context.source_class_heritage = None;
            }
        }
        Ok(context)
    }

    pub(super) fn request_matches(&self, alias: SemanticSymbolId, type_: TypeId,
        parameters: &[TypeId], arguments: &[TypeId], requested: Option<(SemanticSymbolId, &[TypeId])>,
    ) -> bool {
        self.reference.symbol == alias && self.mapping_matches(type_, parameters, arguments)
            && self.requested_alias() == requested
    }

    pub(super) fn arguments(&self) -> &[TypeId] { &self.arguments }

    pub(super) fn cache_key(&self, store: &CanonicalTypeMapperStore) -> Result<CacheHashKey, DeclaredTypeError> {
        let identity = self.requested_alias.as_ref().map(|(alias, arguments)| {
            store.symbol_store().assigned_global_symbol_id(*alias)
                .map(|global| (global, arguments.as_slice())).ok_or_else(|| self.invalid())
        }).transpose()?;
        Ok(type_alias_instantiation_cache_key(&self.arguments, identity))
    }

    pub(in crate::semantic) fn mapping_matches(
        &self,
        type_: TypeId,
        parameters: &[TypeId],
        arguments: &[TypeId],
    ) -> bool {
        self.declared_type == type_ && self.parameters == parameters && self.arguments == arguments
    }

    pub(in crate::semantic) fn requested_alias(&self) -> Option<(SemanticSymbolId, &[TypeId])> {
        self.requested_alias.as_ref().map(|(symbol, arguments)| (*symbol, arguments.as_slice()))
    }

    /// Replays only the completed canonical-any request from registered source facts.
    pub(in crate::semantic) fn validate_completed_any_metadata(
        &self,
        store: &CanonicalTypeMapperStore,
        result: TypeId,
        host: Option<&DeclaredTypeHost<'_>>,
        globals: Option<&CanonicalGlobalTypes>,
        options: Option<CanonicalTypeQueryOptions>,
    ) -> Result<CanonicalArrayTargets, DeclaredTypeError> {
        let invalid = || self.invalid();
        let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
        if self.arguments != [bootstrap.any_type]
            || self.parameters.len() != 1 || self.argument_roots != self.reference.type_arguments
            || self.argument_roots.len() != 1 || !self.defaults.is_empty()
            || self.reference.arity != PlannedTypeReferenceArity::Valid
            || self.reference.global_array_target.is_some() || self.reference.direct_generic
            || store.validate_union_constituent(bootstrap.any_type).is_err()
            || self.reference.alias_owner != self.requested_alias.as_ref().map(|(owner, _)| *owner)
            || globals.is_some_and(|globals| *globals != self.globals)
            || options.is_some_and(|options| options != self.options)
            || store.source_node_kind(self.node) != Some(SyntaxKind::TypeReference)
            || store.source_node_kind(self.argument_roots[0]) != Some(SyntaxKind::AnyKeyword)
            || store.type_node_links(self.node).is_none_or(|links| {
                links.resolved_type != Some(result) || links.outer_type_parameters.is_some()
            })
            || store.symbol_node_links(self.node).is_none_or(|links| {
                links.resolved_symbol != Some(self.reference.symbol)
            })
        { return Err(invalid()); }
        fn header_matches(store: &CanonicalTypeMapperStore, declaration: NodeRef,
            alias: SemanticSymbolId, header: &TypeAliasPlan) -> bool {
            super::super::object_aliases::validate_source_alias_binding(store, declaration, alias).is_ok()
                && store.source_symbol_declarations_match(alias)
                && store.source_node_kind(declaration) == Some(SyntaxKind::TypeAliasDeclaration)
                && store.source_direct_type_annotation(declaration) == Some(header.type_node)
                && store.source_node_parent(header.name) == Some(SourceNodeParent::Parent(declaration))
                && store.source_identifier_text(header.name) == Some(header.name_text.as_str())
                && header.type_parameters.iter().all(|parameter| {
                    store.source_node_parent(parameter.declaration) == Some(SourceNodeParent::Parent(declaration))
                        && store.source_declaration_belongs_to_symbol(parameter.declaration, parameter.symbol)
                        && store.source_alias_type_parameter_annotations(parameter.declaration).is_some_and(|facts| {
                            facts.constraint == parameter.constraint && facts.default_type == parameter.default_type
                        })
                })
        }
        if !header_matches(store, self.declaration, self.reference.symbol, &self.header)
            || self.header.type_parameters.len() != self.parameters.len()
            || self.header.type_parameters.iter().zip(&self.parameters).any(|(parameter, type_)| {
                cached_ordinary_type_parameter_owner(store, *type_) != Some(parameter.symbol)
            })
            || store.type_alias_links(self.reference.symbol).is_none_or(|links| {
                links.declared_type != Some(self.declared_type)
                    || links.type_parameters.as_deref() != Some(self.parameters.as_slice())
                    || links.is_constructor_declared_property
            })
        { return Err(invalid()); }
        let children = store.source_direct_children(self.node).ok_or_else(invalid)?;
        let [name, argument] = children.as_slice() else { return Err(invalid()); };
        if *argument != self.argument_roots[0]
            || store.type_node_links(*name).is_some_and(|links| links != &TypeNodeLinks::default())
            || store.symbol_node_links(*name).is_some_and(|links| {
                links.resolved_symbol.is_some_and(|symbol| symbol != self.reference.symbol
                    && Some(symbol) != self.reference.import_alias)
            })
            || store.type_node_links(*argument).is_some_and(|links| {
                links.resolved_type.is_some_and(|type_| type_ != bootstrap.any_type)
                    || links.outer_type_parameters.is_some()
            })
        { return Err(invalid()); }
        if let Some(host) = host {
            self.role.validate(store, host, self.node)?;
            if plan_type_alias_header(store, host, self.reference.symbol)? != (self.declaration, self.header.clone()) {
                return Err(invalid());
            }
        }
        let contains = |root: NodeRef| {
            let mut current = self.node;
            let mut seen = HashSet::new();
            while current != root {
                if !seen.insert(current) { return false; }
                let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(current) else { return false; };
                if !store.source_direct_children(parent).is_some_and(|children| children.contains(&current)) { return false; }
                current = parent;
            }
            true
        };
        if let Some(class) = self.role.class {
            let (owner, root) = match class {
                SourceMappedClassRole::Annotation { owner, root } | SourceMappedClassRole::Heritage { owner, root } => (owner, root),
            };
            let class = store.symbol(owner).ok_or_else(invalid)?;
            if !contains(root) || !class.flags().contains(SymbolFlags::CLASS)
                || !store.source_symbol_declarations_match(owner)
                || !class.declarations().is_some_and(|declarations| declarations.iter().any(|declaration| {
                    matches!(store.source_node_kind(*declaration), Some(SyntaxKind::ClassDeclaration | SyntaxKind::ClassExpression))
                        && contains(*declaration)
                        && store.source_declaration_belongs_to_symbol(*declaration, owner)
                }))
            { return Err(invalid()); }
        }
        if let Some(callable) = &self.role.callable {
            if !contains(callable.declaration)
                || !store.source_declaration_belongs_to_symbol(callable.declaration, callable.owner_symbol)
                || !store.source_symbol_declarations_match(callable.owner_symbol)
                || store.source_node_kind(callable.declaration) == Some(SyntaxKind::FunctionDeclaration)
                    && store.symbol(callable.owner_symbol).is_none_or(|symbol| !symbol.flags().contains(SymbolFlags::FUNCTION))
                || callable.type_parameters.iter().any(|parameter| {
                    !store.source_declaration_belongs_to_symbol(parameter.declaration, parameter.symbol)
                        || store.source_node_parent(parameter.declaration) != Some(SourceNodeParent::Parent(callable.declaration))
                })
            { return Err(invalid()); }
        }
        if let Some((owner, arguments)) = &self.requested_alias {
            let (declaration, header) = self.owner.as_ref().ok_or_else(invalid)?;
            if !header_matches(store, *declaration, *owner, header)
                || header.type_parameters.len() != arguments.len()
                || header.type_parameters.iter().zip(arguments).any(|(parameter, type_)| {
                    cached_ordinary_type_parameter_owner(store, *type_) != Some(parameter.symbol)
                })
                || store.type_alias_links(*owner).is_none_or(|links| {
                    links.declared_type != Some(result) || links.is_constructor_declared_property
                        || links.type_parameters.as_deref().unwrap_or_default() != arguments
                })
            { return Err(invalid()); }
            let mut rhs = header.type_node;
            let mut seen = HashSet::new();
            while rhs != self.node {
                if !seen.insert(rhs) || store.source_node_kind(rhs) != Some(SyntaxKind::ParenthesizedType)
                    || store.type_node_links(rhs).is_some_and(|links| {
                        links.resolved_type.is_some_and(|type_| type_ != result) || links.outer_type_parameters.is_some()
                    })
                { return Err(invalid()); }
                let children = store.source_direct_children(rhs).ok_or_else(invalid)?;
                let [inner] = children.as_slice() else { return Err(invalid()); };
                rhs = *inner;
            }
        } else if self.owner.is_some() { return Err(invalid()); }
        if let Some(import) = &self.reference.alias_body_import { import.validate_retained(store).map_err(|_| invalid())?; }
        if let Some(import) = &self.reference.class_annotation_import { import.validate_current(store).map_err(|_| invalid())?; }
        if let Some(import) = &self.reference.property_import { import.validate_current(store).map_err(|_| invalid())?; }
        if let Some(import) = &self.reference.interface_heritage_import {
            import.validate_alias_reference(store, self.node, self.reference.import_alias,
                self.reference.symbol, &self.reference.type_arguments).map_err(|_| invalid())?;
        }
        if let Some(import) = &self.reference.implementation_import {
            validate_ordinary_import_alias_links(store, self.node, import, true)?;
        }
        for (node, capability) in &self.aliases {
            if *node != capability.reference
                || store.source_node_kind(*node) != Some(SyntaxKind::TypeReference)
                || !store.source_declaration_belongs_to_symbol(capability.binding_declaration, capability.alias)
                || !store.source_symbol_declarations_match(capability.alias)
                || store.symbol(capability.alias).is_none_or(|symbol| !symbol.flags().contains(SymbolFlags::ALIAS))
                || store.get_merged_symbol(capability.alias) != Some(capability.alias)
                || store.get_merged_symbol(capability.immediate_target) != Some(capability.immediate_target)
                || store.get_merged_symbol(capability.target) != Some(capability.target)
                || store.alias_symbol_links(capability.alias).is_some_and(|links| {
                    links.immediate_target.is_some_and(|target| target != capability.immediate_target)
                })
                || store.symbol_node_links(*node).is_some_and(|links| {
                    links.resolved_symbol.is_some_and(|symbol| symbol != capability.target)
                })
            { return Err(invalid()); }
        }
        if let Some(capability) = self.jsdoc {
            if let Some(host) = host {
                validate_jsdoc_import_type_target(store, host, capability)?;
            } else {
                let exports = store.symbol(capability.module_symbol).and_then(|symbol| symbol.exports())
                    .and_then(|table| store.symbol_table(table)).ok_or_else(invalid)?;
                let name = store.source_identifier_text(capability.imported_name).ok_or_else(invalid)?;
                if !store.source_declaration_belongs_to_symbol(capability.local_declaration, capability.local_symbol)
                    || !store.source_declaration_belongs_to_symbol(capability.target_declaration, capability.target_symbol)
                    || store.source_node_kind(capability.import_type) != Some(SyntaxKind::ImportType)
                    || exports.get_source(name) != Some(capability.target_symbol)
                    || store.get_parent_of_symbol(capability.target_symbol) != Some(capability.module_symbol)
                { return Err(invalid()); }
            }
        }
        let arrays = CanonicalArrayTargets::from_global_types(&self.globals);
        for (name, target) in [("Array", arrays.array_type()), ("ReadonlyArray", arrays.readonly_array_type())] {
            let global = store.symbol_table(bootstrap.globals).ok_or_else(invalid)?.get_source(name);
            if let Some(global) = global {
                let global = store.get_merged_symbol(global).ok_or_else(invalid)?;
                if store.declared_type_links(global).and_then(|links| links.declared_type) != Some(target)
                    || store.symbol(global).is_none_or(|symbol| symbol.name().as_utf8() != Some(name))
                    || !store.source_symbol_declarations_match(global)
                    || store.type_payload(target).and_then(TypeRecord::symbol)
                        .and_then(|symbol| store.get_merged_symbol(symbol)) != Some(global)
                {
                    return Err(invalid());
                }
            } else if target != bootstrap.empty_generic_type { return Err(invalid()); }
            let checked = if store.relation_read_observation_is_active() {
                super::super::global_types::preflight_relation_generic_global_type_target(store, target)
            } else { super::super::global_types::preflight_generic_global_type_target(store, target) };
            checked.map_err(|_| invalid())?;
        }
        Ok(arrays)
    }

    fn invalid(&self) -> DeclaredTypeError {
        type_node_unavailable(TypeNodeUnavailable::InvalidGenericAliasInstantiationCache(self.reference.symbol))
    }

    fn validate_source(
        &self,
        store: &CanonicalTypeMapperStore,
        context: &SourceTypeQueryContext<'_, '_>,
    ) -> Result<(), DeclaredTypeError> {
        let invalid = || self.invalid();
        self.role.validate(store, context.host, self.node)?;
        super::super::object_aliases::validate_source_alias_binding(
            store, self.declaration, self.reference.symbol,
        ).map_err(|_| invalid())?;
        if self.globals != context.globals || self.options != context.options
            || self.aliases != context.aliases || self.jsdoc != context.jsdoc
            || plan_type_alias_header(store, context.host, self.reference.symbol)?
                != (self.declaration, self.header.clone())
            || self.reference.arity != PlannedTypeReferenceArity::Valid
            || self.reference.alias_owner != self.requested_alias.as_ref().map(|(owner, _)| *owner)
            || self.header.type_parameters.len() != self.parameters.len()
            || self.arguments.len() != self.parameters.len()
            || self.header.type_parameters.iter().zip(&self.parameters).any(|(parameter, type_)| {
                cached_ordinary_type_parameter_owner(store, *type_) != Some(parameter.symbol)
            })
        {
            return Err(invalid());
        }
        let links = store.type_alias_links(self.reference.symbol).ok_or_else(invalid)?;
        if links.declared_type != Some(self.declared_type)
            || links.type_parameters.as_deref() != Some(self.parameters.as_slice())
            || links.is_constructor_declared_property
        {
            return Err(invalid());
        }
        let mut planner = self.role.apply(context.planner(store))?;
        if planner.mapped_alias_reference_header(self.node, self.reference.alias_owner)? != self.reference
            || store.symbol_node_links(self.node).is_some_and(|links| {
                links.resolved_symbol.is_some_and(|symbol| symbol != self.reference.symbol)
            })
        {
            return Err(invalid());
        }
        let record = preflight_node(store, context.host, self.node)?;
        let (name, written) = match &record.data {
            NodeData::TypeReferenceNode(reference) => (reference.type_name, reference.type_arguments.as_ref()),
            NodeData::ExpressionWithTypeArguments(reference) => {
                let owner = source_class_implementation_owner(store, context.host, self.node)?.ok_or_else(invalid)?;
                if self.role.class != Some(SourceMappedClassRole::Heritage { owner, root: self.node })
                    || self.requested_alias.is_some()
                { return Err(invalid()); }
                (reference.expression, reference.type_arguments.as_ref())
            }
            _ => return Err(invalid()),
        };
        let name = NodeRef::new(self.node.arena, self.node.file, name);
        let import_count = usize::from(self.reference.alias_body_import.is_some())
            + usize::from(self.reference.implementation_import.is_some())
            + usize::from(self.reference.class_annotation_import.is_some())
            + usize::from(self.reference.interface_heritage_import.is_some())
            + usize::from(self.reference.property_import.is_some());
        if preflight_node(store, context.host, name)?.parent != Some(self.node.node)
            || import_count > 1
            || self.reference.import_alias.is_some() && import_count == 0
                && planner.type_reference_alias_targets.get(&self.node).is_none()
                && planner.cached_source_annotation_type_import(self.node)?.is_none()
            || self.reference.global_array_target.is_some() || self.reference.direct_generic
            || store.type_node_links(self.node).is_some_and(|links| links.outer_type_parameters.is_some())
            || store.type_node_links(name).is_some_and(|links| links != &TypeNodeLinks::default())
            || store.symbol_node_links(name).is_some_and(|links| links.resolved_symbol.is_some_and(|symbol| {
                symbol != self.reference.symbol && Some(symbol) != self.reference.import_alias
            }))
        { return Err(invalid()); }
        if let Some(import) = &self.reference.alias_body_import {
            if import.reference() != self.node || import.target_symbol() != self.reference.symbol
                || Some(import.alias_symbol()) != self.reference.import_alias
                || import.arguments() != self.reference.type_arguments
                || source_imports::plan_source_alias_body_type_import(store, context.host, self.node)
                    .map_err(|error| property_type_import_error(self.node, error))?.as_ref() != Some(import)
            { return Err(invalid()); }
            import.validate_retained(store).map_err(|error| property_type_import_error(self.node, error))?;
        }
        if let Some(import) = &self.reference.implementation_import {
            if plan_source_class_implementation_import(store, context.host, self.node)?.as_ref() != Some(import)
                || import.target() != self.reference.symbol
            { return Err(invalid()); }
            validate_ordinary_import_alias_links(store, self.node, import,
                store.type_node_links(self.node).and_then(|links| links.resolved_type).is_some())?;
        }
        if let Some(import) = &self.reference.class_annotation_import {
            if import.reference() != self.node || import.target_symbol() != self.reference.symbol
                || Some(import.alias_symbol()) != self.reference.import_alias || import.arguments() != self.reference.type_arguments
            { return Err(invalid()); }
            import.validate_current(store).map_err(|error| property_type_import_error(self.node, error))?;
        }
        if let Some(import) = &self.reference.interface_heritage_import {
            import.validate_alias_reference(store, self.node, self.reference.import_alias, self.reference.symbol, &self.reference.type_arguments)
                .map_err(|error| property_type_import_error(self.node, error))?;
        }
        if let Some(import) = &self.reference.property_import {
            if import.annotation() != self.node || import.target_symbol() != self.reference.symbol
                || Some(import.alias_symbol()) != self.reference.import_alias || !self.reference.type_arguments.is_empty()
            { return Err(invalid()); }
            import.validate_current(store).map_err(|error| property_type_import_error(self.node, error))?;
        }
        let written = written.map_or_else(Vec::new, |arguments| arguments.nodes.iter()
            .map(|node| NodeRef::new(self.node.arena, self.node.file, *node)).collect::<Vec<_>>());
        if written != self.reference.type_arguments
            || written.len() > self.argument_roots.len()
            || self.argument_roots[..written.len()] != written
        {
            return Err(invalid());
        }
        if let Some((owner, arguments)) = &self.requested_alias {
            let expected = self.owner.as_ref().ok_or_else(invalid)?;
            super::super::object_aliases::validate_source_alias_binding(store, expected.0, *owner)
                .map_err(|_| invalid())?;
            if plan_type_alias_header(store, context.host, *owner)? != *expected
                || planner.direct_type_alias_owner(self.node)? != Some(*owner)
                || expected.1.type_parameters.len() != arguments.len()
                || expected.1.type_parameters.iter().zip(arguments).any(|(parameter, type_)| {
                    cached_ordinary_type_parameter_owner(store, *type_) != Some(parameter.symbol)
                })
                || store.type_alias_links(*owner).is_some_and(|links| {
                    links.is_constructor_declared_property
                        || links.type_parameters.as_ref().is_some_and(|types| types != arguments)
                })
            {
                return Err(invalid());
            }
            let cached = store.type_node_links(self.node).and_then(|links| links.resolved_type);
            if store.type_alias_links(*owner).and_then(|links| links.declared_type)
                .is_some_and(|type_| Some(type_) != cached)
            {
                return Err(invalid());
            }
            let mut rhs = expected.1.type_node;
            let mut seen = HashSet::new();
            while rhs != self.node {
                if !seen.insert(rhs)
                    || store.type_node_links(rhs).is_some_and(|links| {
                        links.outer_type_parameters.is_some()
                            || links.resolved_type.is_some() && links.resolved_type != cached
                    })
                    || store.symbol_node_links(rhs).is_some_and(|links| links != &SymbolNodeLinks::default())
                {
                    return Err(invalid());
                }
                let NodeData::ParenthesizedTypeNode(parenthesis) = &preflight_node(store, context.host, rhs)?.data else {
                    return Err(invalid());
                };
                let inner = NodeRef::new(rhs.arena, rhs.file, parenthesis.type_);
                if preflight_node(store, context.host, inner)?.parent != Some(rhs.node) {
                    return Err(invalid());
                }
                rhs = inner;
            }
        } else if self.owner.is_some() {
            return Err(invalid());
        }
        for (index, root) in self.argument_roots.iter().enumerate().skip(written.len()) {
            if self.header.type_parameters[index].default_type != Some(*root) {
                return Err(invalid());
            }
        }
        Ok(())
    }

    fn replay_arguments(
        &self,
        store: &CanonicalTypeMapperStore,
        context: &SourceTypeQueryContext<'_, '_>,
        plan: &TypeQueryPlan,
    ) -> Result<(), DeclaredTypeError> {
        let arrays = Some(CanonicalArrayTargets::from_global_types(&context.globals));
        for (index, node) in self.argument_roots.iter().enumerate() {
            let value = plan.cached_type_query_result_with_source(
                store, arrays, self.role.callable.as_deref(), &[], *node, SourceCallableTypeReplay::Operational,
                &mut HashSet::new(), Some((&context.globals, context)),
            )?.ok_or_else(|| self.invalid())?;
            let value = if index < self.reference.type_arguments.len() {
                value
            } else if let Some(operand) = plan.source_alias_operands.get(node) {
                let (raw, retained) = self.defaults.get(node).ok_or_else(|| self.invalid())?;
                let retained = retained.as_ref().ok_or_else(|| self.invalid())?;
                let published = store.source_alias_default_graph(*node).ok_or_else(|| self.invalid())?;
                let current = plan.source_alias_operand_graph(store, context.host, &operand.source, *node, value, arrays)?;
                if *raw != value { return Err(self.invalid()); }
                let mut expected = None;
                for graph in [retained, published, &current] {
                    if !graph.matches_operand(&operand.source, *node, value) { return Err(self.invalid()); }
                    let result = super::super::instantiate::cached_source_alias_operand_instantiation(
                        store, graph, value, &self.parameters[..index], &self.arguments[..index], arrays,
                    ).map_err(|error| match error {
                        super::super::instantiate::InstantiationError::Declared(error) => error,
                        _ => self.invalid(),
                    })?.ok_or_else(|| self.invalid())?;
                    if expected.is_some_and(|expected| expected != result) { return Err(self.invalid()); }
                    expected = Some(result);
                }
                expected.ok_or_else(|| self.invalid())?
            } else {
                if self.defaults.get(node).is_none_or(|(raw, graph)| *raw != value || graph.is_some()) {
                    return Err(self.invalid());
                }
                super::super::instantiate::cached_instantiation_with_vector_and_source(
                    store, value, &self.parameters[..index], &self.arguments[..index],
                    &context.globals, context,
                ).map_err(|error| match error {
                    super::super::instantiate::InstantiationError::Declared(error) => error,
                    _ => self.invalid(),
                })?.ok_or_else(|| self.invalid())?
            };
            if self.arguments.get(index) != Some(&value) {
                return Err(self.invalid());
            }
        }
        Ok(())
    }

    pub(super) fn validate(
        &self,
        store: &CanonicalTypeMapperStore,
        context: &SourceTypeQueryContext<'_, '_>,
    ) -> Result<(), DeclaredTypeError> {
        self.validate_source(store, context)?;
        let mut planner = self.role.apply(context.planner(store))?;
        for (index, node) in self.argument_roots.iter().enumerate() {
            if index < self.reference.type_arguments.len() {
                planner.plan_type_node_in_context(*node, None, false)?;
            } else {
                planner.plan_generic_alias_default(self.reference.symbol, *node, index, &self.header.type_parameters)?;
            }
        }
        let current = planner.finish();
        if self.argument_plan.references != current.references
            || self.argument_plan.nodes != current.nodes
            || self.argument_plan.literals != current.literals
            || self.argument_plan.source_alias_operands != current.source_alias_operands
            || self.argument_plan.reference_roles != current.reference_roles
        {
            return Err(self.invalid());
        }
        self.replay_arguments(store, context, &self.argument_plan)?;
        self.replay_arguments(store, context, &current)
    }
}

impl SourceTypeQueryContext<'_, '_> {
    pub(super) fn prove_mapped_alias_request(
        &self,
        store: &CanonicalTypeMapperStore,
        node: NodeRef,
        reference: &PlannedTypeReference,
        declared_type: TypeId,
        parameters: &[TypeId],
        arguments: &[TypeId],
        requested_alias: Option<(SemanticSymbolId, &[TypeId])>,
        plan: &TypeQueryPlan,
    ) -> Result<SourceMappedAliasRequestProof, DeclaredTypeError> {
        let invalid = || type_node_unavailable(TypeNodeUnavailable::InvalidGenericAliasInstantiationCache(reference.symbol));
        let (declaration, header) = plan_type_alias_header(store, self.host, reference.symbol)?;
        if reference.type_arguments.len() > arguments.len() || arguments.len() > parameters.len()
            || header.type_parameters.len() != parameters.len()
        {
            return Err(invalid());
        }
        let mut argument_roots = reference.type_arguments.clone();
        for parameter in header.type_parameters.iter().skip(argument_roots.len()) {
            argument_roots.push(parameter.default_type.ok_or_else(invalid)?);
        }
        let owner = requested_alias.map(|(owner, _)| plan_type_alias_header(store, self.host, owner)).transpose()?;
        if plan.references.get(&node) != Some(reference) { return Err(invalid()); }
        let role = plan.reference_roles.get(&node).cloned().ok_or_else(invalid)?;
        role.validate(store, self.host, node)?;
        let mut planner = role.apply(self.planner(store))?;
        for (index, node) in argument_roots.iter().enumerate() {
            if index < reference.type_arguments.len() {
                planner.plan_type_node_in_context(*node, None, false)?;
            } else {
                planner.plan_generic_alias_default(reference.symbol, *node, index, &header.type_parameters)?;
            }
        }
        let argument_plan = planner.finish();
        let arrays = Some(CanonicalArrayTargets::from_global_types(&self.globals));
        let effective = argument_plan.cached_mapped_alias_arguments(store, reference, &header, parameters,
            &arguments[..reference.type_arguments.len()], arrays, Some((&self.globals, self)))?;
        if effective.get(..arguments.len()) != Some(arguments) { return Err(invalid()); }
        let mut defaults = BTreeMap::new();
        for root in argument_roots.iter().skip(reference.type_arguments.len()) {
            let raw = argument_plan.cached_type_query_result_with_source(store, arrays, role.callable.as_deref(), &[], *root,
                SourceCallableTypeReplay::Operational, &mut HashSet::new(), Some((&self.globals, self)))?.ok_or_else(invalid)?;
            let graph = argument_plan.source_alias_operands.get(root).map(|operand| {
                argument_plan.source_alias_operand_graph(store, self.host, &operand.source, *root, raw, arrays)
            }).transpose()?;
            defaults.insert(*root, (raw, graph));
        }
        let proof = SourceMappedAliasRequestProof {
            node, reference: reference.clone(), declared_type, declaration, header,
            parameters: parameters.to_vec(), arguments: effective,
            requested_alias: requested_alias.map(|(symbol, types)| (symbol, types.to_vec())),
            owner, argument_roots, argument_plan, role, defaults, globals: self.globals.clone(),
            options: self.options, aliases: self.aliases.clone(), jsdoc: self.jsdoc,
        };
        proof.validate_source(store, self)?;
        proof.replay_arguments(store, self, &proof.argument_plan)?;
        Ok(proof)
    }
}
