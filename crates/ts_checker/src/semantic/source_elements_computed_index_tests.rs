use super::*;
use crate::semantic::{CanonicalCheckerContext, IntrinsicBootstrapOptions};
use ts_ast::FileId;
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_parser::parse_source_file;

#[test]
fn computed_index_proof_precedes_absent_indexes_for_any_element_reads() {
    const FILE: FileId = FileId::new(20_242);
    let parsed = parse_source_file(concat!(
        "declare const key: string;\n",
        "declare const index: any;\n",
        "declare const input: number;\n",
        "const object = { [key]: input };\n",
        "const namedKey = 'value';\n",
        "const named = { [namedKey]: input };\n",
        "const ordinary = { value: input };\n",
        "const read = object[index];\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/computed-index-proof.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(FILE, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            no_implicit_any: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap();
    context.check_source_file(FILE).unwrap();
    assert!(context.diagnostics().is_empty());

    let node = |id| NodeRef::new(parsed.arena.id(), FILE, id);
    let variable = |name: &str| {
        parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data
                else {
                    return None;
                };
                (identifier.text == name).then(|| (node(id), variable.initializer.map(node)))
            })
            .unwrap()
    };
    let resolved = |location| {
        context
            .store()
            .type_node_links(location)
            .unwrap()
            .resolved_type
            .unwrap()
    };
    let object = variable("object").1.unwrap();
    let receiver_type = resolved(object);
    let named_type = resolved(variable("named").1.unwrap());
    let ordinary_type = resolved(variable("ordinary").1.unwrap());
    let access = variable("read").1.unwrap();
    let bound = context.file(FILE).unwrap().1.clone();
    let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
    let syntax = plan_direct_source_element_syntax(&parsed.arena, context.store(), access).unwrap();
    let prior = ["object", "index"]
        .map(|name| bound.symbol(variable(name).0).unwrap())
        .into_iter()
        .collect::<HashSet<_>>();
    let identifier = |location, name| {
        let read = super::super::variables::plan_identifier_read(
            &parsed.arena,
            &bound,
            context.store(),
            &host,
            &prior,
            &prior,
            location,
            name,
        )
        .unwrap();
        PlannedExpression::new(
            location,
            super::super::source::PlannedExpressionKind::Identifier(
                super::super::source::PlannedIdentifierRead {
                    resolved_symbol: read.resolved_symbol,
                    value_symbol: read.value_symbol,
                    kind: super::super::source::PlannedIdentifierReadKind::Variable,
                },
            ),
        )
    };
    let receiver = identifier(syntax.receiver, "object");
    let index = identifier(syntax.index, "index");
    let plan = finish_direct_source_element_plan(syntax, receiver, index).unwrap();
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let (any, error, number) = (
        bootstrap.any_type,
        bootstrap.error_type,
        bootstrap.number_type,
    );
    assert_eq!(resolved(plan.index.node), any);
    let index = classify_index(context.store(), any).unwrap();
    assert!(matches!(index.shape, IndexShape::Any));
    assert_eq!(index.property_name, None);
    assert!(object_members::source_object_requires_computed_proof(
        context.store(),
        receiver_type,
    ));
    assert!(object_members::source_computed_object_receiver_is_exact(
        context.store(),
        receiver_type,
    ));
    assert!(object_members::source_computed_object_receiver_is_exact(
        context.store(),
        named_type,
    ));
    assert!(matches!(
        resolved_index_signature_surface(context.store(), named_type),
        Ok(None)
    ));
    assert!(!object_members::source_object_requires_computed_proof(
        context.store(),
        ordinary_type,
    ));
    assert!(matches!(
        resolved_index_signature_surface(context.store(), ordinary_type),
        Ok(None)
    ));

    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            [
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.index_info_len(),
                store.type_alias_len(),
                store.symbol_store().symbol_table_len(),
            ],
            parsed
                .arena
                .iter()
                .map(|(id, _)| {
                    let location = node(id);
                    (
                        store.type_node_links(location).cloned(),
                        store.symbol_node_links(location).cloned(),
                        store.signature_links(location).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            context.diagnostics().clone(),
        )
    };
    let before = snapshot(&context);
    let resolve = |store: &mut CanonicalTypeMapperStore| {
        resolve_object_element::<SourceElementError, _>(
            store,
            &host,
            None,
            &plan,
            receiver_type,
            &index,
            any,
            error,
            &mut |_, _, _| panic!("an Any index has no named property lookup"),
        )
    };

    let original = context.store().type_payload(receiver_type).unwrap();
    let original_payload = format!("{original:?}");
    let TypeData::Object(object_type) = original.data() else {
        panic!("the receiver must be the checked computed object");
    };
    let members = object_type.structured.members;
    let properties = object_type.structured.properties.clone();
    assert_eq!(object_type.structured.signatures, None);
    assert_eq!(object_type.structured.call_signature_count, 0);
    let indexes = object_type.structured.index_infos.clone().unwrap();
    assert_eq!(indexes.len(), 1);
    assert_eq!(
        context.store().index_info(indexes[0]).unwrap().value_type(),
        number
    );

    // Keep the actual owner and computed-key proof. Remove only the index list.
    assert!(context.store_mut_for_test().set_structured_type_members(
        receiver_type,
        members,
        properties.clone(),
        None,
        None,
        None,
    ));
    let damaged_payload = format!("{:?}", context.store().type_payload(receiver_type).unwrap());
    assert!(!object_members::source_computed_object_receiver_is_exact(
        context.store(),
        receiver_type,
    ));
    for _ in 0..2 {
        match resolve(context.store_mut_for_test()) {
            Err(error) => assert_eq!(
                error,
                SourceElementError::Unsupported(SourceElementUnsupported::IndexSignatureSurface(
                    receiver_type
                ))
            ),
            Ok(_) => panic!("a missing computed index list must not return any"),
        }
        assert_eq!(snapshot(&context), before);
        assert_eq!(
            format!("{:?}", context.store().type_payload(receiver_type).unwrap()),
            damaged_payload
        );
    }

    assert!(context.store_mut_for_test().set_structured_type_members(
        receiver_type,
        members,
        properties,
        None,
        None,
        Some(indexes),
    ));
    assert_eq!(
        format!("{:?}", context.store().type_payload(receiver_type).unwrap()),
        original_payload
    );
    assert!(object_members::source_computed_object_receiver_is_exact(
        context.store(),
        receiver_type,
    ));
    for _ in 0..2 {
        let result = resolve(context.store_mut_for_test()).unwrap();
        assert_eq!(result.type_, number);
        assert_eq!(result.property, None);
        assert!(result.diagnostic.is_none());
        assert!(result.from_index_signature);
        assert_eq!(snapshot(&context), before);
        context.check_source_file(FILE).unwrap();
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(snapshot(&context), before);
        assert_eq!(
            format!("{:?}", context.store().type_payload(receiver_type).unwrap()),
            original_payload
        );
    }
}
