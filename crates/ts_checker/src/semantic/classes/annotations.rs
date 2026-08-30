//! Class annotation queries retain the real owner while its members are checked.

use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::semantic) struct SourceClassAnnotationScope {
    plan: SourceClassPlan,
    instance: TypeId,
    targets: CanonicalArrayTargets,
}

pub(in crate::semantic) fn source_class_annotation_is_owned(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    annotation: NodeRef,
) -> bool {
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
    let TypeData::Interface(interface) = store.type_payload(instance).ok_or_else(invalid)?.data()
    else {
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
    annotation: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<(), ClassError> {
    let expected = store
        .type_node_links(annotation)
        .and_then(|links| links.resolved_type);
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
        let result = if source_class_annotation_scope_targets(store, instance) != Some(targets) {
            Err(invalid())
        } else {
            validate_source_class_header(
                store,
                host,
                store
                    .source_class_provenance(instance)
                    .expect("the retained source class was checked before opening its scope"),
            )
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
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, IntrinsicBootstrapOptions, SourceFileLinks,
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
