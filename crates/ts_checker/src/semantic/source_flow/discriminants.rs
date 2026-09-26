use super::*;
use super::super::{member_resolution, type_nodes::CanonicalTypeQuery};

/// Keep the access node before reference matching removes non-null wrappers.
pub(super) fn access_node(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    mut node: NodeRef,
) -> Result<Option<(NodeRef, bool)>, SourceFlowError> {
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(node) || seen.len() > FLOW_DEPTH_LIMIT {
            return Err(SourceFlowInvariant::InvalidClassProperty(node).into());
        }
        let record = class_flow_source_node(store, host, node)?;
        match &record.data {
            NodeData::ParenthesizedExpression(wrapper) => {
                let child = NodeRef::new(node.arena, node.file, wrapper.expression);
                if class_flow_source_node(store, host, child)?.parent != Some(node.node) {
                    return Err(SourceFlowInvariant::InvalidClassProperty(node).into());
                }
                node = child;
            }
            NodeData::PropertyAccessExpression(property)
                if property.question_dot_token.is_none() && property.facts == 0 => {
                let receiver = NodeRef::new(node.arena, node.file, property.expression);
                let receiver = class_flow_source_node(store, host, receiver)?;
                if receiver.parent != Some(node.node) {
                    return Err(SourceFlowInvariant::InvalidClassProperty(node).into());
                }
                return Ok(Some((node, matches!(receiver.data, NodeData::NonNullExpression(_)))));
            }
            _ => return Ok(None),
        }
    }
}

impl SourceFlowContext<'_, '_> {
    pub(super) fn discriminant_property_access(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        session: &mut InstantiationSession,
        node: NodeRef,
        declared: TypeId,
        current: TypeId,
        name: &str,
    ) -> Result<bool, SourceCheckError> {
        let flags = |type_| store.type_payload(type_).map(TypeRecord::flags)
            .ok_or(SourceCheckError::Property(node));
        let declared_union = flags(declared)?.contains(TypeFlags::UNION);
        let current_union = flags(current)?.contains(TypeFlags::UNION);
        if !declared_union && !current_union { return Ok(false); }
        let selected = if declared_union && exact_subset(store, self.globals, current, declared)
            .map_err(|_| SourceCheckError::Property(node))? { declared } else { current };
        if !store.type_payload(selected).is_some_and(|record| record.flags().contains(TypeFlags::UNION)) {
            return Ok(false);
        }
        let Some(property) = member_resolution::resolve_source_union_property_raw(
            store, self.host, self.globals, self.options, session, self.diagnostics, node, selected, name,
        )? else { return Ok(false); };
        let required = CheckFlags::HAS_NON_UNIFORM_TYPE | CheckFlags::HAS_LITERAL_TYPE;
        if !property.check_flags.intersects(CheckFlags::SYNTHETIC_PROPERTY | CheckFlags::SYNTHETIC_METHOD)
            || !property.check_flags.contains(required) { return Ok(false); }
        let flags = CanonicalTypeQuery::new_with_global_types_and_session(
            store, self.host, self.globals, self.options, session, self.diagnostics,
        )?.get_generic_type_flags(property.property.type_id()).map_err(|error| {
            use super::super::generic_types::GenericTypeQueryError;
            match error {
                GenericTypeQueryError::Source(error)
                | GenericTypeQueryError::Instantiation(super::super::instantiate::InstantiationError::Declared(error))
                | GenericTypeQueryError::Mapped(super::super::mapped_types::MappedTypeError::Declared(error)) => SourceCheckError::DeclaredType(error),
                GenericTypeQueryError::Union(error) => super::super::source::source_union_property_error(
                    node, member_resolution::UnionPropertyError::TypeCache(error),
                ),
                _ => SourceCheckError::Property(node),
            }
        })?;
        Ok(flags == ObjectFlags::NONE)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn narrow_discriminant_equality(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        session: &mut InstantiationSession,
        node: NodeRef,
        current: TypeId,
        name: &str,
        value: TypeId,
        strict: bool,
        require_match: bool,
    ) -> Result<TypeId, SourceEqualityNarrowingError> {
        let bootstrap = store.intrinsic_bootstrap().ok_or(SourceEqualityNarrowingError::MissingBootstrap)?;
        let (never, unknown, strict_null_checks) = (bootstrap.never_type, bootstrap.unknown_type, bootstrap.options.strict_null_checks);
        if current == never { return Ok(current); }
        let Some((_, non_null)) = access_node(store, self.host, node)
            .map_err(|_| SourceEqualityNarrowingError::InvalidDiscriminant(node))? else {
            return Err(SourceEqualityNarrowingError::InvalidDiscriminant(node));
        };
        let original = match store.type_payload(current).ok_or(SourceEqualityNarrowingError::InvalidType(current))?.data() {
            TypeData::Union(union) => union.union.types.clone(),
            _ => vec![current],
        };
        let lookup = if strict_null_checks && non_null {
            let mut present = Vec::new();
            for type_ in &original {
                let flags = store.type_payload(*type_).ok_or(SourceEqualityNarrowingError::InvalidType(*type_))?.flags();
                if !flags.intersects(TypeFlags::NULL | TypeFlags::UNDEFINED) { present.push(*type_); }
            }
            filter_source_union_result(store, self.globals, current, &original, present, session)?
        } else { current };
        let Some(property_type) = self.named_property_type(store, session, node, lookup, name)? else {
            return Ok(current);
        };
        let narrowed = narrow_by_equality_worker(
            store, self.globals, property_type, value, strict, require_match, None, Some(session), Some(self),
        )?;
        let mut retained = Vec::new();
        for constituent in &original {
            let property = match self.named_property_type(store, session, node, *constituent, name)? {
                Some(property) => property,
                None => match member_resolution::resolve_source_union_constituent_index(
                    store, self.host, self.globals, self.options, session, self.diagnostics, node, *constituent, name,
                ).map_err(SourceEqualityNarrowingError::Source)? {
                    Some(index) => self.optional_property_type(store, session, index.value_type, true)?,
                    None => unknown,
                },
            };
            if property != never && narrowed != never
                && self.comparable(store, session, narrowed, property).map_err(SourceEqualityNarrowingError::Source)? {
                retained.push(*constituent);
            }
        }
        filter_source_union_result(store, self.globals, current, &original, retained, session)
    }

    fn named_property_type(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        session: &mut InstantiationSession,
        node: NodeRef,
        receiver: TypeId,
        name: &str,
    ) -> Result<Option<TypeId>, SourceEqualityNarrowingError> {
        if store.type_payload(receiver).is_some_and(|record| record.flags().contains(TypeFlags::UNION)) {
            return member_resolution::resolve_source_union_property(
                store, self.host, self.globals, self.options, session, self.diagnostics, node, receiver, name,
            ).map(|property| property.map(|property| property.type_id())).map_err(SourceEqualityNarrowingError::Source);
        }
        let Some(property) = member_resolution::resolve_source_union_constituent_property(
            store, self.host, self.globals, self.options, session, self.diagnostics, node, receiver, name,
        ).map_err(SourceEqualityNarrowingError::Source)? else { return Ok(None); };
        self.optional_property_type(store, session, property.type_, property.optional).map(Some)
    }

    fn optional_property_type(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        session: &mut InstantiationSession,
        type_: TypeId,
        optional: bool,
    ) -> Result<TypeId, SourceEqualityNarrowingError> {
        let bootstrap = store.intrinsic_bootstrap().ok_or(SourceEqualityNarrowingError::MissingBootstrap)?;
        if optional && bootstrap.options.strict_null_checks {
            self.union(store, session, &[type_, bootstrap.undefined_or_missing_type])
        } else { Ok(type_) }
    }

    fn union(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        session: &mut InstantiationSession,
        types: &[TypeId],
    ) -> Result<TypeId, SourceEqualityNarrowingError> {
        store.expression_union_type_with_global_types_and_session(self.globals, types, UnionReduction::Literal, session)
            .map_err(SourceEqualityNarrowingError::Union)
    }
}

fn exact_subset(
    store: &mut CanonicalTypeMapperStore,
    globals: &CanonicalGlobalTypes,
    source: TypeId,
    target: TypeId,
) -> Result<bool, SourceEqualityNarrowingError> {
    for type_ in [source, target] {
        if !store.type_record_header_is_valid(type_) {
            return Err(SourceEqualityNarrowingError::InvalidType(type_));
        }
        if matches!(store.type_payload(type_).map(TypeRecord::data), Some(TypeData::Union(_))) {
            store.validate_union_query_metadata(type_).map_err(SourceEqualityNarrowingError::Union)?;
        }
    }
    let source_record = store.type_payload(source).ok_or(SourceEqualityNarrowingError::InvalidType(source))?;
    if source == target || source_record.flags().contains(TypeFlags::NEVER) { return Ok(true); }
    let TypeData::Union(target_union) = store.type_payload(target).ok_or(SourceEqualityNarrowingError::InvalidType(target))?.data() else {
        return Ok(false);
    };
    if let TypeData::Union(source_union) = source_record.data() {
        return Ok(source_union.union.types.iter().all(|type_| target_union.union.types.contains(type_)));
    }
    let enum_like = source_record.flags().intersects(TypeFlags::ENUM_LIKE);
    let target_types = target_union.union.types.clone();
    if enum_like
        && base_type_of_literal_type(store, Some(globals), source).map_err(|_| SourceEqualityNarrowingError::InvalidType(source))? == target {
        return Ok(true);
    }
    Ok(target_types.contains(&source))
}
