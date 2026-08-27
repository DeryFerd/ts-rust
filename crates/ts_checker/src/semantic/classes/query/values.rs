//! Class value queries compose the existing annotation and expression kernels.

use super::*;
use crate::semantic::{
    instantiate::InstantiationSession,
    logical_operators::{LogicalBinaryError, LogicalBinaryRequest, check_logical_binary},
    source::{
        PlannedExpression, PlannedExpressionKind, PlannedIdentifierRead, PlannedIdentifierReadKind,
        widened_fresh_literal_type,
    },
    source_properties::{
        SourcePropertyError, check_direct_source_property_with_session,
        finish_direct_source_property_plan, plan_direct_source_property_syntax,
    },
};

#[derive(Clone, Debug, Eq, PartialEq)]
struct AnnotatedMemberPlan {
    class: ClassQueryPlan,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    annotation: NodeRef,
    method: bool,
    readonly: bool,
}

fn annotation_type_if_ready(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    annotation: NodeRef,
) -> Result<Option<TypeId>, ClassError> {
    let record = preflight_node(store, host, annotation)?;
    if record.flags.0 != 0 {
        return Err(invariant(ClassInvariant::InvalidPropertyTypeCache(
            annotation,
        )));
    }
    let expected = match &record.data {
        NodeData::KeywordTypeNode(_) => {
            Some(primitive_keyword_type(store, annotation, record.kind)?)
        }
        NodeData::TypeReferenceNode(reference)
            if record.kind == SyntaxKind::TypeReference && reference.type_arguments.is_none() =>
        {
            let name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
            if preflight_node(store, host, name)?.parent != Some(annotation.node) {
                return Err(invariant(ClassInvariant::InvalidName(name)));
            }
            let symbol = lexical_class_query_symbol(
                store,
                host,
                name,
                SymbolFlags::TYPE | SymbolFlags::ALIAS,
            )?;
            validate_query_reference_cache(store, annotation, symbol)?;
            validate_query_reference_cache(store, name, symbol)?;
            let owner = store
                .symbol(symbol)
                .ok_or_else(|| invariant(ClassInvariant::InvalidOwnerSymbol(symbol)))?;
            if owner.flags().intersects(SymbolFlags::ENUM) {
                crate::semantic::enums::preflight_enum(store, host, symbol)
                    .map_err(DeclaredTypeError::from)?;
                store
                    .declared_type_links(symbol)
                    .and_then(|links| links.declared_type)
            } else if owner.flags() == SymbolFlags::CLASS {
                let class = plan_class_query(store, host, symbol)?;
                class_query_shell_state(store, &class)?.instance
            } else if owner.flags() == SymbolFlags::INTERFACE
                && preflight_class_or_interface_reference(
                    store,
                    host,
                    symbol,
                    SymbolFlags::INTERFACE,
                )? == 0
            {
                crate::semantic::declared::cached_interface_type(store, symbol)?
            } else {
                return Err(unsupported(ClassUnsupported::PropertyType {
                    node: annotation,
                    kind: record.kind,
                }));
            }
        }
        _ => {
            return Err(unsupported(ClassUnsupported::PropertyType {
                node: annotation,
                kind: record.kind,
            }));
        }
    };
    if store.type_node_links(annotation).is_some_and(|links| {
        links != &TypeNodeLinks::default()
            && expected.is_none_or(|expected| {
                links
                    != &(TypeNodeLinks {
                        resolved_type: Some(expected),
                        ..TypeNodeLinks::default()
                    })
            })
    }) {
        return Err(invariant(ClassInvariant::InvalidPropertyTypeCache(
            annotation,
        )));
    }
    Ok(expected)
}

fn member_binding(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<(ClassQueryPlan, NodeRef), ClassError> {
    let invalid = || invariant(ClassInvariant::InvalidPropertyValueCache(symbol));
    let record = store.symbol(symbol).ok_or_else(invalid)?;
    let class = plan_class_query(store, host, record.parent().ok_or_else(invalid)?)?;
    class_query_shell_state(store, &class)?;
    let [declaration] = record.declarations().unwrap_or_default() else {
        let declaration = record.value_declaration().unwrap_or(class.declaration);
        return Err(unsupported(ClassUnsupported::Member {
            node: declaration,
            kind: preflight_node(store, host, declaration)?.kind,
        }));
    };
    let declaration = *declaration;
    if preflight_node(store, host, declaration)?.kind == SyntaxKind::Parameter {
        return Err(unsupported(ClassUnsupported::Member {
            node: declaration,
            kind: SyntaxKind::Parameter,
        }));
    }
    if record.value_declaration() != Some(declaration)
        || !declaration.is_for(class.declaration.arena, class.declaration.file)
        || !class.members.contains(&declaration.node)
        || !host.symbol_matches(store, declaration, symbol)
        || preflight_node(store, host, declaration)?.parent != Some(class.declaration.node)
    {
        return Err(invalid());
    }
    Ok((class, declaration))
}

fn plan_annotated_member(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<AnnotatedMemberPlan, ClassError> {
    let (class, declaration) = member_binding(store, host, symbol)?;
    let record = preflight_node(store, host, declaration)?;
    let reject = || {
        unsupported(ClassUnsupported::Member {
            node: declaration,
            kind: record.kind,
        })
    };
    let (name, annotation, modifiers, method) = match &record.data {
        NodeData::PropertyDeclaration(property)
            if record.kind == SyntaxKind::PropertyDeclaration
                && property.symbol.is_none()
                && property.facts == 0
                && property.postfix_token.is_none() =>
        {
            (
                property.name,
                property.type_.ok_or_else(reject)?,
                property.modifiers.as_ref(),
                false,
            )
        }
        NodeData::MethodDeclaration(method)
            if record.kind == SyntaxKind::MethodDeclaration
                && method.parameters.nodes.is_empty()
                && !method.parameters.has_trailing_comma
                && method.asterisk_token.is_none()
                && method.postfix_token.is_none()
                && method.type_parameters.is_none()
                && method.full_signature.is_none()
                && method.symbol.is_none()
                && method.flow_node.is_none()
                && method.end_flow_node.is_none()
                && method.next_container.is_none()
                && method.facts == 0 =>
        {
            (
                method.name,
                method.type_.ok_or_else(reject)?,
                method.modifiers.as_ref(),
                true,
            )
        }
        _ => return Err(reject()),
    };
    if record.flags.0 != 0 {
        return Err(reject());
    }
    let name = NodeRef::new(declaration.arena, declaration.file, name);
    let name_record = preflight_node(store, host, name)?;
    let (text, private) = match &name_record.data {
        NodeData::Identifier(name)
            if name_record.kind == SyntaxKind::Identifier && name.flow_node.is_none() =>
        {
            (name.text.as_str(), false)
        }
        NodeData::PrivateIdentifier(name) if name_record.kind == SyntaxKind::PrivateIdentifier => {
            (name.text.as_str(), true)
        }
        _ => return Err(invariant(ClassInvariant::InvalidName(name))),
    };
    if name_record.parent != Some(declaration.node)
        || name_record.flags.0 != 0
        || !class_member_symbol_name_matches(store, class.symbol, symbol, text, private)
    {
        return Err(invariant(ClassInvariant::InvalidName(name)));
    }
    let (_, readonly) = class_property_modifiers(store, host, declaration, name, modifiers, None)?;
    if method && readonly {
        return Err(reject());
    }
    let annotation = NodeRef::new(declaration.arena, declaration.file, annotation);
    let annotation_record = preflight_node(store, host, annotation)?;
    if annotation_record.parent != Some(declaration.node)
        || annotation_record.range.start < name_record.range.end
        || annotation_record.range.end > record.range.end
    {
        return Err(invariant(ClassInvariant::InvalidPropertyTypeCache(
            annotation,
        )));
    }
    annotation_type_if_ready(store, host, annotation)?;
    Ok(AnnotatedMemberPlan {
        class,
        declaration,
        symbol,
        annotation,
        method,
        readonly,
    })
}

fn initialized_type_if_ready(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<Option<TypeId>, ClassError> {
    let record = preflight_node(store, host, node)?;
    let symbol = match &record.data {
        NodeData::NewExpression(_) => {
            let plan = default_new_query_plan(store, host, node)?;
            return Ok(class_query_shell_state(store, &plan)?.instance);
        }
        NodeData::PropertyAccessExpression(_) => {
            class_query_reference_symbol(store, host, node)?
                .ok_or_else(|| unsupported(ClassUnsupported::PropertyInitializer(node)))?
        }
        NodeData::Identifier(_) => lexical_class_query_symbol(
            store,
            host,
            node,
            SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE | SymbolFlags::ALIAS,
        )?,
        _ => return Err(unsupported(ClassUnsupported::PropertyInitializer(node))),
    };
    let binding = store
        .symbol(symbol)
        .ok_or_else(|| invariant(ClassInvariant::InvalidOwnerSymbol(symbol)))?;
    if let Some(type_) = store
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
    {
        return Ok(Some(type_));
    }
    if binding.flags() == SymbolFlags::ENUM_MEMBER {
        return Ok(store
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type));
    }
    if let Some(annotation) = binding
        .value_declaration()
        .and_then(|declaration| store.source_direct_type_annotation(declaration))
    {
        return annotation_type_if_ready(store, host, annotation);
    }
    if binding
        .parent()
        .and_then(|owner| store.symbol(owner))
        .is_some_and(|owner| owner.flags() == SymbolFlags::CLASS)
    {
        return match plan_selected_class_member(store, host, symbol) {
            Ok(plan) if matches!(plan.member, SelectedMember::Property(_)) => Ok(Some(plan.type_)),
            Ok(_) | Err(ClassError::Unsupported(_)) => Ok(None),
            Err(error) => Err(error),
        };
    }
    Ok(None)
}

fn default_new_query_plan(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<ClassQueryPlan, ClassError> {
    let reject = || unsupported(ClassUnsupported::PropertyInitializer(node));
    let record = preflight_node(store, host, node)?;
    let NodeData::NewExpression(new_) = &record.data else {
        return Err(reject());
    };
    if record.kind != SyntaxKind::NewExpression
        || record.flags.0 != 0
        || new_.facts != 0
        || new_.type_arguments.is_some()
    {
        return Err(reject());
    }
    let constructor = NodeRef::new(node.arena, node.file, new_.expression);
    let constructor_record = preflight_node(store, host, constructor)?;
    let argument_start = if let Some(arguments) = &new_.arguments {
        if !arguments.nodes.is_empty()
            || arguments.has_trailing_comma
            || arguments.range.start < record.range.start
            || arguments.range.end != record.range.end
            || arguments.range.end.get() < arguments.range.start.get().saturating_add(2)
            || host
                .source(node)
                .and_then(|(arena, _)| arena.source_text())
                .is_some_and(|source| {
                    source.as_bytes().get(arguments.range.start.get() as usize) != Some(&b'(')
                        || source
                            .as_bytes()
                            .get(arguments.range.end.get().saturating_sub(1) as usize)
                            != Some(&b')')
                })
        {
            return Err(reject());
        }
        arguments.range.start
    } else {
        if constructor_record.range.end != record.range.end {
            return Err(reject());
        }
        record.range.end
    };
    if constructor_record.parent != Some(node.node)
        || constructor_record.range.start < record.range.start
        || constructor_record.range.end > argument_start
    {
        return Err(reject());
    }
    let symbol = lexical_class_query_symbol(
        store,
        host,
        constructor,
        SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE | SymbolFlags::ALIAS,
    )?;
    validate_query_reference_cache(store, constructor, symbol)?;
    let plan = plan_class_query(store, host, symbol)?;
    if plan.abstract_class
        || plan.members.iter().any(|member| {
            host.node(NodeRef::new(
                plan.declaration.arena,
                plan.declaration.file,
                *member,
            ))
            .is_some_and(|member| member.kind == SyntaxKind::Constructor)
        })
    {
        return Err(reject());
    }
    class_query_shell_state(store, &plan)?;
    Ok(plan)
}

pub(super) fn annotated_method_return_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_: TypeId,
) -> Result<Option<TypeId>, ClassError> {
    let Some(symbol) = store.type_payload(type_).and_then(TypeRecord::symbol) else {
        return Ok(None);
    };
    let plan = match plan_annotated_member(store, host, symbol) {
        Ok(plan) if plan.method => plan,
        Ok(_) | Err(ClassError::Unsupported(_)) => return Ok(None),
        Err(error) => return Err(error),
    };
    let return_type = annotation_type_if_ready(store, host, plan.annotation)?
        .ok_or_else(|| invariant(ClassInvariant::InvalidPropertyValueCache(symbol)))?;
    if exact_method_value(store, symbol, plan.declaration, return_type, &[], None)
        .map(|(value, _)| value)
        != Some(type_)
    {
        return Err(invariant(ClassInvariant::InvalidPropertyValueCache(symbol)));
    }
    Ok(Some(return_type))
}

pub(in crate::semantic) struct ClassValueQuery<'store, 'host, 'arena> {
    pub store: &'store mut CanonicalTypeMapperStore,
    pub host: &'host DeclaredTypeHost<'arena>,
    pub global_types: &'store CanonicalGlobalTypes,
    pub options: CanonicalCheckerOptions,
    pub session: &'store mut InstantiationSession,
    pub diagnostics: &'store mut CanonicalCheckerDiagnostics,
}

impl ClassValueQuery<'_, '_, '_> {
    fn annotation_type(&mut self, node: NodeRef) -> Result<TypeId, ClassError> {
        Ok(CanonicalTypeQuery::new_with_global_types_and_session(
            self.store,
            self.host,
            self.global_types,
            self.options,
            self.session,
            self.diagnostics,
        )?
        .get_type_from_type_node(node)?)
    }

    fn value_type(
        &mut self,
        symbol: SemanticSymbolId,
        active: &mut HashSet<SemanticSymbolId>,
    ) -> Result<TypeId, ClassError> {
        let record = self
            .store
            .symbol(symbol)
            .ok_or_else(|| invariant(ClassInvariant::InvalidOwnerSymbol(symbol)))?;
        if record.flags() == SymbolFlags::CLASS {
            let plan = plan_class_query(self.store, self.host, symbol)?;
            return Ok(execute_class_query_shells(self.store, self.host, &plan)?.value_type());
        }
        if record
            .parent()
            .and_then(|owner| self.store.symbol(owner))
            .is_some_and(|owner| owner.flags() == SymbolFlags::CLASS)
        {
            let type_ = self.member_type_inner(symbol, active)?;
            return self.read_type(symbol, type_);
        }
        let flags = record.flags();
        let mut query = CanonicalTypeQuery::new_with_global_types_and_session(
            self.store,
            self.host,
            self.global_types,
            self.options,
            self.session,
            self.diagnostics,
        )?;
        let type_ = if flags.intersects(SymbolFlags::ENUM) {
            query.get_enum_semantics(symbol)?.value_type
        } else if flags == SymbolFlags::ENUM_MEMBER {
            query.get_declared_type_of_symbol(symbol)?
        } else {
            query.get_type_of_declared_value(symbol)?
        };
        self.read_type(symbol, type_)
    }

    fn read_type(&mut self, symbol: SemanticSymbolId, type_: TypeId) -> Result<TypeId, ClassError> {
        if !self.options.intrinsic.strict_null_checks
            || self.store.symbol(symbol).is_none_or(|symbol| {
                !symbol
                    .flags()
                    .contains(SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL)
            })
        {
            return Ok(type_);
        }
        let undefined = self
            .store
            .intrinsic_bootstrap()
            .ok_or_else(|| invariant(ClassInvariant::InvalidPropertyValueCache(symbol)))?
            .undefined_or_missing_type;
        self.store
            .expression_union_type_with_global_types(
                self.global_types,
                &[type_, undefined],
                crate::semantic::bootstrap::UnionReduction::Literal,
            )
            .map_err(|_| invariant(ClassInvariant::InvalidPropertyValueCache(symbol)))
    }

    pub(in crate::semantic) fn member_type(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<TypeId, ClassError> {
        self.member_type_inner(symbol, &mut HashSet::new())
    }

    fn member_type_inner(
        &mut self,
        symbol: SemanticSymbolId,
        active: &mut HashSet<SemanticSymbolId>,
    ) -> Result<TypeId, ClassError> {
        if !active.insert(symbol) {
            let declaration = self
                .store
                .symbol(symbol)
                .and_then(Symbol::value_declaration)
                .ok_or_else(|| invariant(ClassInvariant::InvalidPropertyValueCache(symbol)))?;
            return Err(unsupported(ClassUnsupported::PropertyInitializer(
                declaration,
            )));
        }
        let result = self.member_type_worker(symbol, active);
        active.remove(&symbol);
        result
    }

    fn member_type_worker(
        &mut self,
        symbol: SemanticSymbolId,
        active: &mut HashSet<SemanticSymbolId>,
    ) -> Result<TypeId, ClassError> {
        match plan_selected_class_member(self.store, self.host, symbol) {
            Ok(plan) => return execute_selected_class_member(self.store, self.host, &plan),
            Err(ClassError::Unsupported(_)) => {}
            Err(error) => return Err(error),
        }
        match plan_annotated_member(self.store, self.host, symbol) {
            Ok(plan) => return self.annotated_member_type(&plan),
            Err(ClassError::Unsupported(_)) => {}
            Err(error) => return Err(error),
        }
        self.initialized_property_type(symbol, active)
    }

    fn annotated_member_type(&mut self, plan: &AnnotatedMemberPlan) -> Result<TypeId, ClassError> {
        let invalid = || invariant(ClassInvariant::InvalidPropertyValueCache(plan.symbol));
        if plan_annotated_member(self.store, self.host, plan.symbol)? != *plan {
            return Err(invariant(ClassInvariant::InvalidPlan(plan.declaration)));
        }
        let ready = annotation_type_if_ready(self.store, self.host, plan.annotation)?;
        if let Some(links) = self.store.value_symbol_links(plan.symbol)
            && links != &ValueSymbolLinks::default()
        {
            let expected = ready.ok_or_else(invalid)?;
            if plan.method {
                if exact_method_value(
                    self.store,
                    plan.symbol,
                    plan.declaration,
                    expected,
                    &[],
                    None,
                )
                .is_none()
                {
                    return Err(invalid());
                }
            } else if links
                != &(ValueSymbolLinks {
                    resolved_type: Some(expected),
                    ..ValueSymbolLinks::default()
                })
            {
                return Err(invalid());
            }
        } else if plan.method
            && self
                .store
                .signature_links(plan.declaration)
                .is_some_and(|links| links != &SignatureLinks::default())
        {
            return Err(invalid());
        }
        let expected_checks = if plan.readonly {
            CheckFlags::READONLY
        } else {
            CheckFlags::NONE
        };
        let checks = self
            .store
            .symbol(plan.symbol)
            .ok_or_else(invalid)?
            .check_flags();
        let has_value = self
            .store
            .value_symbol_links(plan.symbol)
            .is_some_and(|links| links.resolved_type.is_some());
        if checks
            != if has_value {
                expected_checks
            } else {
                CheckFlags::NONE
            }
        {
            return Err(invalid());
        }
        let type_ = self.annotation_type(plan.annotation)?;
        if annotation_type_if_ready(self.store, self.host, plan.annotation)? != Some(type_) {
            return Err(invariant(ClassInvariant::InvalidPropertyTypeCache(
                plan.annotation,
            )));
        }
        if plan.method {
            if let Some((value, _)) =
                exact_method_value(self.store, plan.symbol, plan.declaration, type_, &[], None)
            {
                return Ok(value);
            }
            let mut signatures = Vec::new();
            signatures
                .try_reserve_exact(1)
                .map_err(|_| invariant(ClassInvariant::Capacity(plan.declaration)))?;
            if !self.store.try_reserve_types(1)
                || !self.store.try_reserve_signatures(1)
                || !self.store.try_reserve_signature_links(1)
                || !self.store.try_reserve_value_symbol_links(1)
            {
                return Err(invariant(ClassInvariant::Capacity(plan.declaration)));
            }
            Ok(publish_class_method_identity(
                self.store,
                plan.symbol,
                plan.declaration,
                type_,
                SignatureFlags::NONE,
                0,
                PreparedClassMethodSignatures {
                    signatures,
                    parameters: Vec::new(),
                },
            ))
        } else {
            if !self.store.try_reserve_value_symbol_links(1) {
                return Err(invariant(ClassInvariant::Capacity(plan.declaration)));
            }
            assert!(
                self.store
                    .set_source_property_readonly(plan.symbol, plan.readonly)
            );
            assert!(self.store.set_value_symbol_links(
                plan.symbol,
                ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                }
            ));
            Ok(type_)
        }
    }

    fn initialized_property_type(
        &mut self,
        symbol: SemanticSymbolId,
        active: &mut HashSet<SemanticSymbolId>,
    ) -> Result<TypeId, ClassError> {
        let (class, declaration) = member_binding(self.store, self.host, symbol)?;
        let record = preflight_node(self.store, self.host, declaration)?;
        let NodeData::PropertyDeclaration(property) = &record.data else {
            return Err(unsupported(ClassUnsupported::Member {
                node: declaration,
                kind: record.kind,
            }));
        };
        let property = property.clone();
        let reject = || unsupported(ClassUnsupported::PropertyInitializer(declaration));
        if record.kind != SyntaxKind::PropertyDeclaration
            || record.flags.0 != 0
            || property.type_.is_some()
            || property.postfix_token.is_some()
            || property.symbol.is_some()
            || property.facts != 0
        {
            return Err(reject());
        }
        let name = NodeRef::new(declaration.arena, declaration.file, property.name);
        let name_record = preflight_node(self.store, self.host, name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(reject());
        };
        if name_record.parent != Some(declaration.node)
            || name_record.flags.0 != 0
            || identifier.flow_node.is_some()
            || !class_member_symbol_name_matches(
                self.store,
                class.symbol,
                symbol,
                &identifier.text,
                false,
            )
        {
            return Err(reject());
        }
        let (_, readonly) = class_property_modifiers(
            self.store,
            self.host,
            declaration,
            name,
            property.modifiers.as_ref(),
            None,
        )?;
        if readonly {
            return Err(reject());
        }
        let initializer = NodeRef::new(
            declaration.arena,
            declaration.file,
            property.initializer.ok_or_else(reject)?,
        );
        let initializer_record = preflight_node(self.store, self.host, initializer)?;
        if initializer_record.parent != Some(declaration.node)
            || !matches!(
                initializer_record.kind,
                SyntaxKind::NewExpression
                    | SyntaxKind::PropertyAccessExpression
                    | SyntaxKind::Identifier
            )
        {
            return Err(reject());
        }
        let ready = initialized_type_if_ready(self.store, self.host, initializer)?;
        if self
            .store
            .type_node_links(initializer)
            .is_some_and(|links| {
                links != &TypeNodeLinks::default()
                    && ready.is_none_or(|ready| {
                        links
                            != &(TypeNodeLinks {
                                resolved_type: Some(ready),
                                ..TypeNodeLinks::default()
                            })
                    })
            })
        {
            return Err(invariant(ClassInvariant::InvalidPropertyTypeCache(
                initializer,
            )));
        }
        if let Some(links) = self.store.value_symbol_links(symbol)
            && links != &ValueSymbolLinks::default()
        {
            let expected = ready
                .ok_or_else(|| invariant(ClassInvariant::InvalidPropertyValueCache(symbol)))?;
            let expected = widened_fresh_literal_type(self.store, expected)
                .map_err(|_| invariant(ClassInvariant::InvalidPropertyTypeCache(initializer)))?;
            if links
                != &(ValueSymbolLinks {
                    resolved_type: Some(expected),
                    ..ValueSymbolLinks::default()
                })
            {
                return Err(invariant(ClassInvariant::InvalidPropertyValueCache(symbol)));
            }
        }
        if self
            .store
            .symbol(symbol)
            .is_none_or(|symbol| symbol.check_flags() != CheckFlags::NONE)
        {
            return Err(invariant(ClassInvariant::InvalidPropertyValueCache(symbol)));
        }
        let raw = self.expression_type(initializer, &class, declaration, active)?;
        let type_ = widened_fresh_literal_type(self.store, raw)
            .map_err(|_| invariant(ClassInvariant::InvalidPropertyTypeCache(initializer)))?;
        if self.store.value_symbol_links(symbol).is_some_and(|links| {
            links != &ValueSymbolLinks::default()
                && links
                    != &(ValueSymbolLinks {
                        resolved_type: Some(type_),
                        ..ValueSymbolLinks::default()
                    })
        }) {
            return Err(invariant(ClassInvariant::InvalidPropertyValueCache(symbol)));
        }
        if !self.store.try_reserve_value_symbol_links(1) {
            return Err(invariant(ClassInvariant::Capacity(declaration)));
        }
        assert!(self.store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            }
        ));
        Ok(type_)
    }

    fn expression_type(
        &mut self,
        node: NodeRef,
        class: &ClassQueryPlan,
        member: NodeRef,
        active: &mut HashSet<SemanticSymbolId>,
    ) -> Result<TypeId, ClassError> {
        self.expression_type_at_depth(node, class, member, active, 0)
    }

    fn expression_type_at_depth(
        &mut self,
        node: NodeRef,
        class: &ClassQueryPlan,
        member: NodeRef,
        active: &mut HashSet<SemanticSymbolId>,
        depth: usize,
    ) -> Result<TypeId, ClassError> {
        let record = preflight_node(self.store, self.host, node)?.clone();
        let reject = || unsupported(ClassUnsupported::PropertyInitializer(node));
        if depth >= 256 || record.flags.0 != 0 {
            return Err(reject());
        }
        let child = |id| NodeRef::new(node.arena, node.file, id);
        let type_ = match &record.data {
            NodeData::Identifier(_) if record.kind == SyntaxKind::Identifier => {
                let symbol = lexical_class_query_symbol(
                    self.store,
                    self.host,
                    node,
                    SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE | SymbolFlags::ALIAS,
                )?;
                validate_query_reference_cache(self.store, node, symbol)?;
                self.value_type(symbol, active)?
            }
            NodeData::PropertyAccessExpression(access)
                if record.kind == SyntaxKind::PropertyAccessExpression =>
            {
                let symbol = class_query_reference_symbol(self.store, self.host, node)?
                    .ok_or_else(reject)?;
                let receiver = child(access.expression);
                if preflight_node(self.store, self.host, receiver)?.kind == SyntaxKind::Identifier {
                    let receiver_symbol = lexical_class_query_symbol(
                        self.store,
                        self.host,
                        receiver,
                        SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE | SymbolFlags::ALIAS,
                    )?;
                    if self
                        .store
                        .symbol(receiver_symbol)
                        .is_some_and(|receiver| receiver.flags() == SymbolFlags::CLASS)
                    {
                        self.value_type(symbol, active)?
                    } else {
                        let (arena, _) = self.host.source(node).ok_or_else(reject)?;
                        let property_error = |error| match error {
                            SourcePropertyError::Unsupported(_) => reject(),
                            SourcePropertyError::Capacity(node) => {
                                invariant(ClassInvariant::Capacity(node))
                            }
                            _ => invariant(ClassInvariant::InvalidPropertyTypeCache(node)),
                        };
                        let syntax = plan_direct_source_property_syntax(arena, self.store, node)
                            .map_err(property_error)?;
                        let plan = finish_direct_source_property_plan(
                            &syntax,
                            PlannedExpression::new(
                                receiver,
                                PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                                    resolved_symbol: receiver_symbol,
                                    value_symbol: receiver_symbol,
                                    kind: PlannedIdentifierReadKind::DeclaredValue,
                                }),
                            ),
                        )
                        .map_err(property_error)?;
                        let receiver_type = self.value_type(receiver_symbol, active)?;
                        let checked = check_direct_source_property_with_session(
                            self.store,
                            Some(self.global_types),
                            &plan,
                            receiver_type,
                            self.session,
                        )
                        .map_err(property_error)?;
                        if checked.diagnostic.is_some() {
                            return Err(reject());
                        }
                        validate_query_reference_cache(self.store, node, symbol)?;
                        checked.type_
                    }
                } else {
                    self.value_type(symbol, active)?
                }
            }
            NodeData::NewExpression(_) if record.kind == SyntaxKind::NewExpression => {
                let plan = default_new_query_plan(self.store, self.host, node)?;
                execute_class_query_shells(self.store, self.host, &plan)?.instance_type()
            }
            NodeData::KeywordExpression(keyword)
                if record.kind == SyntaxKind::ThisKeyword && keyword.flow_node.is_none() =>
            {
                let (arena, _) = self.host.source(member).ok_or_else(reject)?;
                if ts_binder::canonical_has_syntactic_modifier(
                    arena,
                    member.node,
                    SyntaxKind::StaticKeyword,
                ) {
                    execute_class_query_shells(self.store, self.host, class)?.value_type()
                } else {
                    let instance = self
                        .store
                        .get_declared_type_of_symbol(self.host, class.symbol)?;
                    exact_class_instance_identity(self.store, class.symbol, instance)
                        .and_then(|interface| interface.this_type)
                        .ok_or_else(reject)?
                }
            }
            NodeData::BinaryExpression(binary) if record.kind == SyntaxKind::BinaryExpression => {
                if binary.facts != 0
                    || binary.symbol.is_some()
                    || binary.type_.is_some()
                    || binary.modifiers.is_some()
                {
                    return Err(reject());
                }
                let operator = preflight_node(self.store, self.host, child(binary.operator_token))?;
                if operator.parent != Some(node.node)
                    || operator.flags.0 != 0
                    || !matches!(
                        operator.kind,
                        SyntaxKind::BarBarToken
                            | SyntaxKind::AmpersandAmpersandToken
                            | SyntaxKind::QuestionQuestionToken
                    )
                    || !matches!(operator.data, NodeData::Token(_))
                    || [binary.left, binary.right].into_iter().any(|id| {
                        self.host
                            .node(child(id))
                            .is_none_or(|operand| operand.parent != Some(node.node))
                    })
                {
                    return Err(reject());
                }
                let operator = operator.kind;
                let left_type = self.expression_type_at_depth(
                    child(binary.left),
                    class,
                    member,
                    active,
                    depth + 1,
                )?;
                let right_type = self.expression_type_at_depth(
                    child(binary.right),
                    class,
                    member,
                    active,
                    depth + 1,
                )?;
                check_logical_binary(
                    self.store,
                    Some(self.global_types),
                    LogicalBinaryRequest {
                        operator,
                        left_type,
                        right_type,
                    },
                )
                .map_err(|error| match error {
                    LogicalBinaryError::Unsupported(_) => reject(),
                    LogicalBinaryError::Invariant(_) | LogicalBinaryError::Literal(_) => {
                        invariant(ClassInvariant::InvalidPropertyTypeCache(node))
                    }
                })?
                .result_type
            }
            NodeData::ParenthesizedExpression(parenthesized)
                if record.kind == SyntaxKind::ParenthesizedExpression =>
            {
                let inner = child(parenthesized.expression);
                if preflight_node(self.store, self.host, inner)?.parent != Some(node.node) {
                    return Err(reject());
                }
                self.expression_type_at_depth(inner, class, member, active, depth + 1)?
            }
            NodeData::NumericLiteral(literal)
                if record.kind == SyntaxKind::NumericLiteral && literal.token_flags.0 == 0 =>
            {
                let number = ts_jsnum::from_string(&literal.text);
                if number.is_nan() {
                    return Err(reject());
                }
                let regular = self
                    .store
                    .regular_number_literal_type(number)
                    .map_err(|_| invariant(ClassInvariant::InvalidPropertyTypeCache(node)))?;
                self.store
                    .fresh_type_of_literal_type(regular)
                    .map_err(|_| invariant(ClassInvariant::InvalidPropertyTypeCache(node)))?
            }
            NodeData::StringLiteral(literal)
                if record.kind == SyntaxKind::StringLiteral && literal.token_flags.0 == 0 =>
            {
                let regular = self
                    .store
                    .regular_string_literal_type(literal.text.clone())
                    .map_err(|_| invariant(ClassInvariant::InvalidPropertyTypeCache(node)))?;
                self.store
                    .fresh_type_of_literal_type(regular)
                    .map_err(|_| invariant(ClassInvariant::InvalidPropertyTypeCache(node)))?
            }
            _ => return Err(reject()),
        };
        if self.store.type_node_links(node).is_some_and(|links| {
            links != &TypeNodeLinks::default()
                && links
                    != &(TypeNodeLinks {
                        resolved_type: Some(type_),
                        ..TypeNodeLinks::default()
                    })
        }) {
            return Err(invariant(ClassInvariant::InvalidPropertyTypeCache(node)));
        }
        Ok(type_)
    }

    fn class_expression_variable_type(
        &mut self,
        declaration: NodeRef,
    ) -> Result<Option<TypeId>, ClassError> {
        let record = preflight_node(self.store, self.host, declaration)?;
        let NodeData::VariableDeclaration(variable) = &record.data else {
            return Ok(None);
        };
        let Some(initializer) = variable.initializer else {
            return Ok(None);
        };
        let initializer = NodeRef::new(declaration.arena, declaration.file, initializer);
        if preflight_node(self.store, self.host, initializer)?.kind != SyntaxKind::ClassExpression {
            return Ok(None);
        }
        let owner = bound_symbol(self.store, self.host, initializer)
            .ok_or_else(|| invariant(ClassInvariant::InvalidDeclaration(initializer)))?;
        let class = plan_class_query(self.store, self.host, owner)?;
        let state = class_query_shell_state(self.store, &class)?;
        let symbol = bound_symbol(self.store, self.host, declaration)
            .ok_or_else(|| invariant(ClassInvariant::InvalidDeclaration(declaration)))?;
        let invalid = || invariant(ClassInvariant::InvalidPropertyValueCache(symbol));
        let binding = self.store.symbol(symbol).ok_or_else(invalid)?;
        let name = NodeRef::new(declaration.arena, declaration.file, variable.name);
        let name_record = preflight_node(self.store, self.host, name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(invalid());
        };
        if record.kind != SyntaxKind::VariableDeclaration
            || record.flags.0 != 0
            || variable.type_.is_some()
            || variable.exclamation_token.is_some()
            || variable.symbol.is_some()
            || variable.local_symbol.is_some()
            || variable.facts != 0
            || name_record.kind != SyntaxKind::Identifier
            || name_record.parent != Some(declaration.node)
            || identifier.flow_node.is_some()
            || binding.name().as_utf8() != Some(identifier.text.as_str())
            || !matches!(
                binding.flags(),
                SymbolFlags::BLOCK_SCOPED_VARIABLE | SymbolFlags::FUNCTION_SCOPED_VARIABLE
            )
            || binding.check_flags() != CheckFlags::NONE
            || binding.declarations() != Some(&[declaration])
            || binding.value_declaration() != Some(declaration)
            || binding.export_symbol().is_some()
            || binding.members().is_some()
            || binding.exports().is_some()
        {
            return Err(invalid());
        }
        if let Some(links) = self.store.value_symbol_links(symbol)
            && links != &ValueSymbolLinks::default()
        {
            let expected = match state.value {
                StaticShellState::WarmShell(type_) | StaticShellState::WarmMembers(type_) => type_,
                StaticShellState::Cold => return Err(invalid()),
            };
            if links
                != &(ValueSymbolLinks {
                    resolved_type: Some(expected),
                    ..ValueSymbolLinks::default()
                })
            {
                return Err(invalid());
            }
        }
        if !self.store.try_reserve_value_symbol_links(1) {
            return Err(invariant(ClassInvariant::Capacity(declaration)));
        }
        let value = execute_class_query_shells(self.store, self.host, &class)?.value_type();
        assert!(self.store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(value),
                ..ValueSymbolLinks::default()
            }
        ));
        Ok(Some(value))
    }

    pub(in crate::semantic) fn type_at_location(
        &mut self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, ClassError> {
        let record = preflight_node(self.store, self.host, node)?.clone();
        if record.kind == SyntaxKind::ClassExpression {
            let symbol = bound_symbol(self.store, self.host, node)
                .ok_or_else(|| invariant(ClassInvariant::InvalidDeclaration(node)))?;
            return self.value_type(symbol, &mut HashSet::new()).map(Some);
        }
        let parent = record
            .parent
            .map(|parent| NodeRef::new(node.arena, node.file, parent));
        if let Some(parent) = parent {
            match &preflight_node(self.store, self.host, parent)?.data {
                NodeData::ClassExpression(class) if class.name == Some(node.node) => {
                    let symbol = bound_symbol(self.store, self.host, parent)
                        .ok_or_else(|| invariant(ClassInvariant::InvalidDeclaration(parent)))?;
                    return self.value_type(symbol, &mut HashSet::new()).map(Some);
                }
                NodeData::VariableDeclaration(variable) if variable.name == node.node => {
                    return self.class_expression_variable_type(parent);
                }
                NodeData::TypeReferenceNode(_)
                | NodeData::TypeQueryNode(_)
                | NodeData::QualifiedName(_) => return Ok(None),
                _ => {}
            }
        }
        if record.kind == SyntaxKind::VariableDeclaration {
            return self.class_expression_variable_type(node);
        }
        let Some((class, member)) = enclosing_query_class(self.store, self.host, node)? else {
            return Ok(None);
        };
        let member_record = preflight_node(self.store, self.host, member)?;
        let name = match &member_record.data {
            NodeData::PropertyDeclaration(property) => property.name,
            NodeData::MethodDeclaration(method) => method.name,
            _ => return Ok(None),
        };
        if node == member || node.node == name {
            let symbol = bound_symbol(self.store, self.host, member)
                .ok_or_else(|| invariant(ClassInvariant::InvalidPropertySymbol(member)))?;
            if self.options.intrinsic.strict_null_checks
                && self.store.symbol(symbol).is_some_and(|symbol| {
                    symbol
                        .flags()
                        .contains(SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL)
                })
            {
                return Ok(None);
            }
            return self.member_type(symbol).map(Some);
        }
        if let Some(parent) = parent
            && matches!(&preflight_node(self.store, self.host, parent)?.data,
                NodeData::PropertyAccessExpression(access) if access.name == node.node)
        {
            return self
                .expression_type(parent, &class, member, &mut HashSet::new())
                .map(Some);
        }
        match record.kind {
            SyntaxKind::Identifier
            | SyntaxKind::PrivateIdentifier
            | SyntaxKind::ThisKeyword
            | SyntaxKind::PropertyAccessExpression
            | SyntaxKind::NewExpression
            | SyntaxKind::BinaryExpression
            | SyntaxKind::ParenthesizedExpression
            | SyntaxKind::NumericLiteral
            | SyntaxKind::StringLiteral => self
                .expression_type(node, &class, member, &mut HashSet::new())
                .map(Some),
            _ => Ok(None),
        }
    }
}
