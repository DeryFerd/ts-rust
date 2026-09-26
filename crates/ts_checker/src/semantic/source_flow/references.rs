//! Property facts use the complete reference, not the shared member symbol.

use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ReferenceKey {
    root: ClassPropertyFlowReceiver,
    path: Vec<String>,
}

impl ReferenceKey {
    pub(super) fn class_property(reference: &ClassPropertyFlowReference) -> Self {
        Self {
            root: reference.receiver.clone(),
            path: vec![reference.name.clone()],
        }
    }

    fn contains(&self, other: &Self) -> bool {
        self.root == other.root && other.path.starts_with(&self.path)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ConditionSyntax {
    Equality {
        expression: NodeRef,
        operator_token: NodeRef,
        left: NodeRef,
        right: NodeRef,
        strict: bool,
        equal: bool,
    },
    Truthiness {
        operand: NodeRef,
        negated: bool,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CheckedOperand {
    node: NodeRef,
    reference: Option<ReferenceKey>,
    type_: TypeId,
    symbol: Option<SemanticSymbolId>,
    access: Option<(NodeRef, bool)>,
}

pub(super) struct CheckedReferenceCondition {
    expression: NodeRef,
    syntax: ConditionSyntax,
    operands: Vec<CheckedOperand>,
    result: TypeId,
}

fn reference_key(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    bound: &BoundFile,
    body: &ClassBodyPlan,
    mut node: NodeRef,
) -> Result<Option<ReferenceKey>, SourceFlowError> {
    let mut path = Vec::new();
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(node) || seen.len() > FLOW_DEPTH_LIMIT {
            return Err(SourceFlowInvariant::InvalidClassProperty(node).into());
        }
        let record = class_flow_source_node(store, host, node)?;
        let child = match &record.data {
            NodeData::ParenthesizedExpression(wrapper) => wrapper.expression,
            NodeData::NonNullExpression(wrapper) => wrapper.expression,
            NodeData::PropertyAccessExpression(property)
                if property.question_dot_token.is_none() && property.facts == 0 =>
            {
                let name = NodeRef::new(node.arena, node.file, property.name);
                let name_record = class_flow_source_node(store, host, name)?;
                if name_record.parent != Some(node.node) {
                    return Err(SourceFlowInvariant::InvalidClassProperty(node).into());
                }
                let text = match &name_record.data {
                    NodeData::Identifier(name) => name.text.clone(),
                    NodeData::PrivateIdentifier(name) => name.text.clone(),
                    _ => return Ok(None),
                };
                path.push(text);
                property.expression
            }
            NodeData::Identifier(_) => {
                let Some(symbol) = own_class_flow_reference_symbol(store, host, bound, node)?
                else {
                    return Ok(None);
                };
                path.reverse();
                return Ok(Some(ReferenceKey {
                    root: ClassPropertyFlowReceiver::Named(symbol),
                    path,
                }));
            }
            _ if record.kind == SyntaxKind::ThisKeyword
                || record.kind == SyntaxKind::SuperKeyword =>
            {
                if bound.flow_container(node) != Some(body.declaration) {
                    return Err(SourceFlowInvariant::InvalidClassProperty(node).into());
                }
                path.reverse();
                let root = if record.kind == SyntaxKind::ThisKeyword {
                    ClassPropertyFlowReceiver::This(body.class_declaration)
                } else {
                    ClassPropertyFlowReceiver::Super(body.class_declaration)
                };
                return Ok(Some(ReferenceKey { root, path }));
            }
            _ => return Ok(None),
        };
        let child = NodeRef::new(node.arena, node.file, child);
        let child_record = class_flow_source_node(store, host, child)?;
        if record.flags.0 != 0
            || child_record.parent != Some(node.node)
            || child_record.range.start < record.range.start
            || child_record.range.end > record.range.end
        {
            return Err(SourceFlowInvariant::InvalidClassProperty(node).into());
        }
        node = child;
    }
}

fn condition_syntax(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    mut expression: NodeRef,
) -> Result<ConditionSyntax, SourceFlowError> {
    let mut negated = false;
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(expression) || seen.len() > FLOW_DEPTH_LIMIT {
            return Err(SourceFlowInvariant::UnknownCondition(expression).into());
        }
        let record = class_flow_source_node(store, host, expression)?;
        let child = match &record.data {
            NodeData::ParenthesizedExpression(wrapper) => Some(wrapper.expression),
            NodeData::PrefixUnaryExpression(prefix)
                if prefix.operator == SyntaxKind::ExclamationToken =>
            {
                negated = !negated;
                Some(prefix.operand)
            }
            _ => None,
        };
        if let Some(child) = child {
            let child = NodeRef::new(expression.arena, expression.file, child);
            if record.flags.0 != 0
                || class_flow_source_node(store, host, child)?.parent != Some(expression.node)
            {
                return Err(SourceFlowInvariant::UnknownCondition(expression).into());
            }
            expression = child;
            continue;
        }
        if let NodeData::BinaryExpression(binary) = &record.data {
            let token = NodeRef::new(expression.arena, expression.file, binary.operator_token);
            let operator = class_flow_source_node(store, host, token)?;
            let (equal, strict) = match operator.kind {
                SyntaxKind::EqualsEqualsEqualsToken => (true, true),
                SyntaxKind::ExclamationEqualsEqualsToken => (false, true),
                SyntaxKind::EqualsEqualsToken => (true, false),
                SyntaxKind::ExclamationEqualsToken => (false, false),
                _ => return Err(SourceFlowUnsupported::IncompleteContainer(expression).into()),
            };
            let left = NodeRef::new(expression.arena, expression.file, binary.left);
            let right = NodeRef::new(expression.arena, expression.file, binary.right);
            if record.kind != SyntaxKind::BinaryExpression
                || record.flags.0 != 0
                || operator.parent != Some(expression.node)
                || operator.flags.0 != 0
                || !matches!(operator.data, NodeData::Token(_))
                || class_flow_source_node(store, host, left)?.parent != Some(expression.node)
                || class_flow_source_node(store, host, right)?.parent != Some(expression.node)
            {
                return Err(SourceFlowInvariant::UnknownCondition(expression).into());
            }
            return Ok(ConditionSyntax::Equality {
                expression,
                operator_token: token,
                left,
                right,
                strict,
                equal: equal != negated,
            });
        }
        return Ok(ConditionSyntax::Truthiness {
            operand: expression,
            negated,
        });
    }
}

fn operand_nodes(syntax: &ConditionSyntax) -> Vec<NodeRef> {
    match *syntax {
        ConditionSyntax::Equality { left, right, .. } => vec![left, right],
        ConditionSyntax::Truthiness { operand, .. } => vec![operand],
    }
}

pub(super) fn validate_condition_syntax(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    bound: &BoundFile,
    body: &ClassBodyPlan,
    expression: NodeRef,
) -> Result<(), SourceFlowError> {
    let syntax = condition_syntax(store, host, expression)?;
    let mut has_reference = false;
    for operand in operand_nodes(&syntax) {
        has_reference |= reference_key(store, host, bound, body, operand)?.is_some();
    }
    if !has_reference {
        return Err(SourceFlowUnsupported::IncompleteContainer(expression).into());
    }
    Ok(())
}

impl CheckedReferenceCondition {
    pub(super) fn validate(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        bound: &BoundFile,
        body: &ClassBodyPlan,
    ) -> Result<(), SourceFlowError> {
        if condition_syntax(store, host, self.expression)? != self.syntax
            || store
                .type_node_links(self.expression)
                .and_then(|links| links.resolved_type)
                != Some(self.result)
        {
            return Err(SourceFlowInvariant::UnknownCondition(self.expression).into());
        }
        for operand in &self.operands {
            if store
                .type_node_links(operand.node)
                .and_then(|links| links.resolved_type)
                != Some(operand.type_)
                || store
                    .symbol_node_links(operand.node)
                    .and_then(|links| links.resolved_symbol)
                    != operand.symbol
                || reference_key(store, host, bound, body, operand.node)? != operand.reference
                || discriminants::access_node(store, host, operand.node)? != operand.access
            {
                return Err(SourceFlowInvariant::UnknownCondition(self.expression).into());
            }
        }
        Ok(())
    }

    pub(super) fn narrow(
        &self,
        types: &mut ClassPropertyFlowTypes<'_, '_>,
        flow: FlowRef,
        flags: FlowFlags,
        reference: &ReferenceKey,
        declared: Option<TypeId>,
        mut current: TypeId,
        assume_true: bool,
    ) -> Result<TypeId, SourceFlowError> {
        let Some(ClassPropertyFlowReadTypes {
            store,
            globals: Some(globals),
            mut session,
            mut context,
        }) = types.read_types()
        else {
            return Err(SourceFlowUnsupported::FlowKind { flow, flags }.into());
        };
        if store.intrinsic_bootstrap().is_some_and(|bootstrap| current == bootstrap.never_type) {
            return Ok(current);
        }
        match self.syntax {
            ConditionSyntax::Truthiness { negated, .. } => {
                if self.operands[0].reference.as_ref() == Some(reference) {
                    let assumption = if assume_true != negated {
                        TruthinessAssumption::Truthy
                    } else {
                        TruthinessAssumption::Falsy
                    };
                    current = match session.as_deref_mut() {
                        Some(session) => narrow_by_truthiness_with_session(
                            store, globals, current, assumption, session,
                        ),
                        None => narrow_by_truthiness(store, Some(globals), current, assumption),
                    }
                    .map_err(|error| SourceFlowError::Narrowing {
                        condition: self.expression,
                        error,
                    })?;
                }
            }
            ConditionSyntax::Equality { strict, equal, .. } => {
                let direct = (0..2).find(|&index| {
                    self.operands[index].reference.as_ref() == Some(reference)
                });
                for index in 0..2 {
                    if direct.is_some_and(|direct| direct != index) {
                        continue;
                    }
                    let Some(operand) = self.operands[index].reference.as_ref() else {
                        continue;
                    };
                    let discriminant = if operand == reference {
                        None
                    } else if reference.contains(operand)
                        && operand.path.len() == reference.path.len() + 1
                    {
                        operand.path.last().map(String::as_str)
                    } else {
                        continue;
                    };
                    if let Some(name) = discriminant && context.is_some() {
                        let Some((access, _)) = self.operands[index].access else { continue; };
                        let declared = declared.ok_or(SourceFlowInvariant::InvalidClassProperty(
                            self.operands[index].node,
                        ))?;
                        let (Some(session), Some(context)) =
                            (session.as_deref_mut(), context.as_mut())
                        else {
                            return Err(SourceFlowUnsupported::FlowKind { flow, flags }.into());
                        };
                        if !context.discriminant_property_access(
                            store, session, access, declared, current, name,
                        ).map_err(SourceFlowError::Source)? {
                            continue;
                        }
                        return context.narrow_discriminant_equality(
                            store, session, access, current, name,
                            self.operands[1 - index].type_, strict, assume_true == equal,
                        ).map_err(|error| match error {
                            SourceEqualityNarrowingError::Source(error) => SourceFlowError::Source(error),
                            SourceEqualityNarrowingError::Union(error) => SourceFlowError::Join { flow, error },
                            error => SourceFlowInvariant::EqualityNarrowing(error).into(),
                        });
                    }
                    current = narrow_by_equality_worker(
                        store,
                        globals,
                        current,
                        self.operands[1 - index].type_,
                        strict,
                        assume_true == equal,
                        discriminant,
                        session.as_deref_mut(),
                        context.as_mut(),
                    )
                    .map_err(|error| match error {
                        SourceEqualityNarrowingError::Source(error) => SourceFlowError::Source(error),
                        SourceEqualityNarrowingError::Union(error) => {
                            SourceFlowError::Join { flow, error }
                        }
                        error => SourceFlowInvariant::EqualityNarrowing(error).into(),
                    })?;
                    break;
                }
            }
        }
        Ok(current)
    }

    pub(super) fn narrow_snapshot(
        &self,
        store: &mut CanonicalTypeMapperStore,
        globals: &CanonicalGlobalTypes,
        flow: FlowRef,
        flags: FlowFlags,
        mut snapshot: SourceFlowSnapshot,
        declared_types: &SourceFlowTypes,
        selected: Option<SemanticSymbolId>,
        assume_true: bool,
        caller: &mut Option<SourceFlowCaller<'_, '_>>,
    ) -> Result<SourceFlowSnapshot, SourceFlowError> {
        if !snapshot.reachable {
            return Ok(snapshot);
        }
        for (symbol, current) in snapshot.types().clone() {
            if selected.is_some_and(|selected| selected != symbol) {
                continue;
            }
            let reference = ReferenceKey {
                root: ClassPropertyFlowReceiver::Named(symbol),
                path: Vec::new(),
            };
            let (session, context) = match caller.as_mut() {
                Some(caller) => (Some(&mut *caller.session), Some(caller.context.reborrow())),
                None => (None, None),
            };
            let narrowed = self.narrow(
                &mut ClassPropertyFlowTypes::with_source(store, Some(globals), session, context),
                flow,
                flags,
                &reference,
                declared_types.get(&symbol).copied(),
                current,
                assume_true,
            )?;
            snapshot = snapshot.with_type(symbol, narrowed);
        }
        Ok(snapshot)
    }
}

impl ClassInitializationFrame<'_, '_> {
    /// Selects union preparation only for the exact prepared reference condition.
    pub(in crate::semantic) fn has_reference_equality_condition(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        request: &crate::semantic::primitive_operators::PrimitiveBinaryRequest,
    ) -> Result<bool, SourceFlowError> {
        if !self.has_reference_conditions() {
            return Ok(false);
        }
        class_body_identities(store, host, &self.access)
            .map_err(|_| SourceFlowInvariant::InvalidClassBody(self.body.declaration))?;
        for condition in self.flow.plan.conditions.values() {
            let SourceFlowCondition::Reference(root) = condition else {
                continue;
            };
            let invalid = || SourceFlowInvariant::UnknownCondition(*root);
            let proof = self.flow.plan.class_expression_conditions.get(root)
                .ok_or_else(invalid)?;
            let (arena, bound) = host.source(*root).ok_or_else(invalid)?;
            if bound.source_file() != self.flow.bound.source_file()
                || bound.node_arena_id() != self.flow.bound.node_arena_id()
                || bound.node_arena_revision() != self.flow.bound.node_arena_revision()
                || validate_class_expression_condition(
                    arena, bound, store, host, self.body, proof.source,
                )? != SourceFlowCondition::Reference(*root)
            {
                return Err(invalid().into());
            }
            let ConditionSyntax::Equality {
                expression, operator_token, left, right, ..
            } = condition_syntax(store, host, *root)? else {
                continue;
            };
            if expression != request.expression {
                continue;
            }
            if left != request.left
                || right != request.right
                || class_flow_source_node(store, host, operator_token)?.kind != request.operator
            {
                return Err(SourceFlowInvariant::UnknownCondition(*root).into());
            }
            return Ok(true);
        }
        Ok(false)
    }

    pub(in crate::semantic) fn has_reference_conditions(&self) -> bool {
        self.flow
            .plan
            .conditions
            .values()
            .any(|condition| matches!(condition, SourceFlowCondition::Reference(_)))
    }

    /// Records a condition only after the normal expression checker has checked it.
    pub(in crate::semantic) fn complete_reference_condition(
        &mut self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        expression: NodeRef,
        result: TypeId,
    ) -> Result<(), SourceFlowError> {
        if self.flow.plan.conditions.get(&expression)
            != Some(&SourceFlowCondition::Reference(expression))
        {
            return Ok(());
        }
        class_body_identities(store, host, &self.access)
            .map_err(|_| SourceFlowInvariant::InvalidClassBody(self.body.declaration))?;
        let syntax = condition_syntax(store, host, expression)?;
        let mut operands = Vec::new();
        for node in operand_nodes(&syntax) {
            let type_ = store
                .type_node_links(node)
                .and_then(|links| links.resolved_type)
                .ok_or(SourceFlowInvariant::UnreachedCondition(expression))?;
            operands.push(CheckedOperand {
                node,
                type_,
                reference: reference_key(store, host, self.flow.bound, self.body, node)?,
                symbol: store
                    .symbol_node_links(node)
                    .and_then(|links| links.resolved_symbol),
                access: discriminants::access_node(store, host, node)?,
            });
        }
        let checked = CheckedReferenceCondition {
            expression,
            syntax,
            operands,
            result,
        };
        checked.validate(store, host, self.flow.bound, self.body)?;
        if let Some(prior) = self.flow.reference_conditions.get(&expression) {
            if prior.syntax != checked.syntax
                || prior.operands != checked.operands
                || prior.result != result
            {
                return Err(SourceFlowInvariant::UnknownCondition(expression).into());
            }
            return Ok(());
        }
        self.flow.reference_conditions.insert(expression, checked);
        self.flow.memo.clear();
        Ok(())
    }

    pub(in crate::semantic) fn reference_read_type(
        &self,
        store: &mut CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        globals: &CanonicalGlobalTypes,
        session: &mut InstantiationSession,
        access: NodeRef,
        declared: TypeId,
    ) -> Result<TypeId, SourceFlowError> {
        self.reference_read_type_worker(store, host, globals, session, access, declared, None)
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::semantic) fn reference_read_type_with_source(
        &self,
        store: &mut CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        globals: &CanonicalGlobalTypes,
        session: &mut InstantiationSession,
        access: NodeRef,
        declared: TypeId,
        source_context: SourceFlowContext<'_, '_>,
    ) -> Result<TypeId, SourceFlowError> {
        self.reference_read_type_worker(store, host, globals, session, access, declared, Some(source_context))
    }

    #[allow(clippy::too_many_arguments)]
    fn reference_read_type_worker(
        &self,
        store: &mut CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        globals: &CanonicalGlobalTypes,
        session: &mut InstantiationSession,
        access: NodeRef,
        declared: TypeId,
        source_context: Option<SourceFlowContext<'_, '_>>,
    ) -> Result<TypeId, SourceFlowError> {
        let Some(reference) = reference_key(store, host, self.flow.bound, self.body, access)?
        else {
            return Ok(declared);
        };
        let flow = self
            .flow
            .plan
            .points
            .get(&access)
            .copied()
            .ok_or(SourceFlowInvariant::InvalidClassProperty(access))?;
        if self.flow.bound.flow_at(access) != Some(flow)
            || self.flow.bound.flow_container(access) != Some(self.flow.plan.container)
            || store.type_payload(declared).is_none()
        {
            return Err(SourceFlowInvariant::InvalidClassProperty(access).into());
        }
        self.reference_type_at(
            &mut ClassPropertyFlowTypes::with_source(store, Some(globals), Some(session), source_context),
            host,
            flow,
            &reference,
            declared,
            &mut HashSet::new(),
            0,
        )
    }

    fn reference_type_at(
        &self,
        types: &mut ClassPropertyFlowTypes<'_, '_>,
        host: &DeclaredTypeHost<'_>,
        flow: FlowRef,
        reference: &ReferenceKey,
        declared: TypeId,
        visiting: &mut HashSet<FlowRef>,
        depth: usize,
    ) -> Result<TypeId, SourceFlowError> {
        if depth > FLOW_DEPTH_LIMIT {
            return Err(SourceFlowInvariant::DepthLimit(flow).into());
        }
        if !visiting.insert(flow) {
            return Err(SourceFlowInvariant::Cycle(flow).into());
        }
        let node = flow_node(self.flow.graph, flow)?;
        let kind = source_flow_kind(flow, node.flags)?;
        let result = match kind {
            SourceFlowKind::Start => {
                validate_start_node(self.flow.plan, flow, &node)?;
                declared
            }
            SourceFlowKind::Unreachable => {
                validate_unreachable_node(self.flow.graph, flow, &node)?;
                types
                    .store()
                    .intrinsic_bootstrap()
                    .ok_or(SourceFlowInvariant::UnreachedCondition(
                        self.body.declaration,
                    ))?
                    .never_type
            }
            SourceFlowKind::Assignment | SourceFlowKind::ArrayMutation => {
                let target = ast_payload(flow, &node)?;
                let assigned =
                    reference_key(types.store(), host, self.flow.bound, self.body, target)?;
                if assigned
                    .as_ref()
                    .is_some_and(|assigned| assigned.contains(reference))
                {
                    if let Some(checked) = self.property_assignments.get(&target) {
                        if !checked.source_is_exact(types.store(), host, true)
                            || checked.target().access_token() != &self.access
                        {
                            return Err(SourceFlowInvariant::InvalidClassProperty(target).into());
                        }
                        if assigned.as_ref() == Some(reference) {
                            checked.flow_type()
                        } else {
                            declared
                        }
                    } else if let Some(SourceFlowAssignmentState::Resolved(type_)) =
                        self.flow.assignment_states.get(&target)
                    {
                        if assigned.as_ref() == Some(reference) {
                            *type_
                        } else {
                            declared
                        }
                    } else {
                        return Err(SourceFlowInvariant::PendingAssignment(target).into());
                    }
                } else {
                    self.reference_type_at(
                        types,
                        host,
                        linear_antecedent(flow, &node)?,
                        reference,
                        declared,
                        visiting,
                        depth + 1,
                    )?
                }
            }
            SourceFlowKind::Call => {
                let call = ast_payload(flow, &node)?;
                if let Some(completed) = self.ordinary_calls.get(&call) {
                    self.validate_non_effecting_call(types.store(), host, completed)?;
                } else if !self.completed_calls.contains(&call) {
                    return Err(SourceFlowInvariant::InvalidCallEffect(call).into());
                }
                self.reference_type_at(
                    types,
                    host,
                    linear_antecedent(flow, &node)?,
                    reference,
                    declared,
                    visiting,
                    depth + 1,
                )?
            }
            SourceFlowKind::TrueCondition | SourceFlowKind::FalseCondition => {
                let expression = ast_payload(flow, &node)?;
                let current = self.reference_type_at(
                    types,
                    host,
                    linear_antecedent(flow, &node)?,
                    reference,
                    declared,
                    visiting,
                    depth + 1,
                )?;
                match self.flow.plan.conditions.get(&expression) {
                    Some(SourceFlowCondition::Reference(_)) => {
                        let completed = self
                            .flow
                            .reference_conditions
                            .get(&expression)
                            .ok_or(SourceFlowInvariant::UnreachedCondition(expression))?;
                        completed.validate(types.store(), host, self.flow.bound, self.body)?;
                        completed.narrow(
                            types,
                            flow,
                            node.flags,
                            reference,
                            Some(declared),
                            current,
                            kind == SourceFlowKind::TrueCondition,
                        )?
                    }
                    Some(_) => current,
                    None => return Err(SourceFlowInvariant::UnknownCondition(expression).into()),
                }
            }
            SourceFlowKind::BranchLabel | SourceFlowKind::LoopLabel => {
                let mut values = Vec::new();
                for antecedent in label_antecedents(flow, &node)? {
                    values.push(self.reference_type_at(
                        types,
                        host,
                        *antecedent,
                        reference,
                        declared,
                        visiting,
                        depth + 1,
                    )?);
                }
                types.join(flow, node.flags, &values, declared)?
            }
        };
        visiting.remove(&flow);
        Ok(result)
    }
}
