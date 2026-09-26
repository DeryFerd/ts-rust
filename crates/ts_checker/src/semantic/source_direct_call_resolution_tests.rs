use super::*;
use crate::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
};
use ts_ast::FileId;
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_903);
const SOURCE: &str = r#"const run = (fn: (value: string) => string): void => {};
const within = (fn: (run: (fn: (value: number) => number) => void) => void): void => {};
within(run => { run(value => value); });
run(value => value);
"#;

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/direct-call-resolution.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            no_implicit_any: true,
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn callbacks(parsed: &ParseResult) -> Vec<NodeRef> {
    let mut callbacks = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::ArrowFunction(_) = &record.data else {
                return None;
            };
            matches!(
                &parsed.arena.get(record.parent?).unwrap().data,
                NodeData::CallExpression(_)
            )
            .then_some(NodeRef::new(parsed.arena.id(), FILE, id))
        })
        .collect::<Vec<_>>();
    callbacks.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    assert_eq!(callbacks.len(), 3);
    callbacks
}

fn counts(store: &CanonicalTypeMapperStore) -> [usize; 7] {
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.type_alias_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn proofs(
    checker: &CanonicalCheckerContext<'_>,
    callbacks: &[NodeRef],
) -> Vec<Arc<SourceDirectCallResolution>> {
    callbacks
        .iter()
        .map(|&callback| {
            assert!(
                checker
                    .store()
                    .source_direct_call_resolution_is_published(callback)
            );
            checker
                .store()
                .source_direct_call_resolution(callback)
                .unwrap()
                .clone()
        })
        .collect()
}

fn assert_rejected(store: &mut CanonicalTypeMapperStore, proof: SourceDirectCallResolution) {
    let before = counts(store);
    let callback = proof.callback();
    let existing = store.source_direct_call_resolution(callback).cloned();
    let published = store.source_direct_call_resolution_is_published(callback);
    assert!(!proof.stored_is_exact(store));
    assert_eq!(
        store.begin_source_direct_call_resolution(Arc::new(proof)),
        None
    );
    assert_eq!(
        store.source_direct_call_resolution(callback),
        existing.as_ref()
    );
    assert_eq!(
        store.source_direct_call_resolution_is_published(callback),
        published
    );
    assert_eq!(counts(store), before);
}

#[test]
fn direct_call_resolution_rejects_changed_owner_target_and_call_cold_and_warm() {
    let parsed = parse_source_file(SOURCE);
    let callbacks = callbacks(&parsed);
    let mut checker = context(&parsed);
    assert!(callbacks.iter().all(|&callback| {
        !checker
            .store()
            .source_direct_call_resolution_was_registered(callback)
    }));
    checker.check_source_file(FILE).unwrap();
    assert!(checker.diagnostics().is_empty());
    let proofs = proofs(&checker, &callbacks);
    let [outer, nested, top] = proofs.as_slice() else {
        unreachable!()
    };
    let (parent, position) = nested.parent.as_ref().unwrap();
    assert_eq!(parent.as_ref(), outer.as_ref());
    assert_eq!(*position, 0);
    assert_eq!(
        checker
            .store()
            .source_identifier_text(nested.reference.receiver),
        Some("run")
    );
    assert_eq!(
        checker
            .store()
            .source_identifier_text(top.reference.receiver),
        Some("run")
    );
    assert_ne!(nested.reference.symbol, top.reference.symbol);
    assert_ne!(nested.receiver_type, top.receiver_type);
    for proof in &proofs {
        assert!(proof.canonical_is_exact(checker.store()));
    }
    let mut wrong_callee_type = nested.as_ref().clone();
    wrong_callee_type.callee_type = top.callee_type;
    assert!(!wrong_callee_type.canonical_is_exact(checker.store()));
    let before = counts(checker.store());
    for _ in 0..2 {
        let host = checker.declared_type_host().unwrap();
        for proof in &proofs {
            let prepared = prepare_source_direct_call_resolution(
                checker.store(),
                &host,
                checker.source_file(FILE).unwrap(),
                proof.callback(),
                proof.target(),
                &std::collections::HashMap::new(),
            )
            .unwrap()
            .unwrap();
            assert_eq!(prepared, *proof);
        }
        assert_eq!(counts(checker.store()), before);
    }

    // Test both an invalidated entry and an already published entry.
    checker
        .store_mut_for_test()
        .fail_source_direct_call_resolution(nested.callback());
    for published in [false, true] {
        let store = checker.store_mut_for_test();
        assert_eq!(
            store.source_direct_call_resolution_is_published(nested.callback()),
            published
        );
        let mut wrong_owner = nested.as_ref().clone();
        wrong_owner.reference.symbol = top.reference.symbol;
        wrong_owner.reference.declaration = top.reference.declaration;
        assert_rejected(store, wrong_owner);
        let mut wrong_call = nested.as_ref().clone();
        wrong_call.reference.call = top.reference.call;
        assert_rejected(store, wrong_call);
        let mut wrong_callee = nested.as_ref().clone();
        wrong_callee.reference.callee = top.reference.callee;
        assert_rejected(store, wrong_callee);
        let mut wrong_argument = nested.as_ref().clone();
        wrong_argument.reference.argument = usize::MAX;
        assert_rejected(store, wrong_argument);
        let mut wrong_signature = nested.as_ref().clone();
        wrong_signature.callee_signature = top.callee_signature;
        assert_rejected(store, wrong_signature);
        let mut wrong_target = nested.as_ref().clone();
        wrong_target.target = top.target;
        assert_rejected(store, wrong_target);
        let mut wrong_parent = nested.as_ref().clone();
        wrong_parent.parent = Some((top.clone(), 0));
        assert_rejected(store, wrong_parent);
        if !published {
            assert_eq!(
                store.begin_source_direct_call_resolution(nested.clone()),
                Some(true)
            );
            assert!(!store.source_direct_call_resolution_is_published(nested.callback()));
            assert!(store.begin_source_direct_call_publication(nested.callback()));
            assert!(store.finish_source_direct_call_resolution(nested.callback()));
        }
    }
    assert_eq!(counts(checker.store()), before);
    assert!(checker.store().type_resolution_is_empty());
}

#[test]
fn direct_call_resolution_failure_invalidates_nested_receipts_only() {
    let parsed = parse_source_file(SOURCE);
    let callbacks = callbacks(&parsed);
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    let proofs = proofs(&checker, &callbacks);
    let [outer, nested, top] = proofs.as_slice() else {
        unreachable!()
    };
    let store = checker.store_mut_for_test();
    let before = counts(store);
    store.fail_source_direct_call_resolution(outer.callback());
    assert_eq!(
        store.begin_source_direct_call_resolution(nested.clone()),
        None
    );
    assert_eq!(counts(store), before);
    assert_eq!(
        store.begin_source_direct_call_resolution(outer.clone()),
        Some(true)
    );
    assert_eq!(
        store.begin_source_direct_call_resolution(nested.clone()),
        Some(true)
    );
    for proof in [outer, nested] {
        assert_eq!(
            store.source_direct_call_resolution(proof.callback()),
            Some(proof)
        );
        assert!(!store.source_direct_call_resolution_is_published(proof.callback()));
        assert_eq!(
            store.begin_source_direct_call_resolution(proof.clone()),
            Some(false)
        );
    }
    assert!(store.begin_source_direct_call_publication(nested.callback()));
    assert!(store.source_direct_call_resolution_is_published(nested.callback()));
    assert!(store.finish_source_direct_call_resolution(nested.callback()));

    let signature = store
        .signature_links(outer.callback())
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let signature = store.signature(signature).unwrap();
    let mut prepared = PreparedContextualDirectCallSourceCallable {
        declaration: outer.callback(),
        owner_symbol: store.source_declaration_symbol(outer.callback()).unwrap(),
        captured_assignment: None,
        contextual_target: outer.target(),
        parameters: signature
            .parameters()
            .iter()
            .map(|&symbol| ContextualSourceCallableParameter {
                declaration: store.symbol(symbol).unwrap().value_declaration().unwrap(),
                symbol,
                type_: store
                    .value_symbol_links(symbol)
                    .unwrap()
                    .resolved_type
                    .unwrap(),
            })
            .collect(),
        flags: signature.flags(),
        min_argument_count: signature.min_argument_count(),
        return_type: signature.resolved_return_type().unwrap(),
    };
    assert_eq!(
        prepared.return_type,
        store.intrinsic_bootstrap().unwrap().void_type
    );
    prepared.return_type = store.intrinsic_bootstrap().unwrap().string_type;
    assert!(outer.canonical_is_exact(store));
    assert!(nested.canonical_is_exact(store));
    let canonical_links = |store: &CanonicalTypeMapperStore| {
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = NodeRef::new(parsed.arena.id(), FILE, id);
                (
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                    store
                        .source_declaration_symbol(node)
                        .and_then(|symbol| store.value_symbol_links(symbol))
                        .cloned(),
                    store
                        .signature_links(node)
                        .and_then(|links| links.resolved_signature.signature())
                        .map(|id| {
                            let signature = store.signature(id).unwrap();
                            (
                                signature.declaration(),
                                signature.flags(),
                                signature.parameters().to_vec(),
                                signature.min_argument_count(),
                                signature.resolved_return_type(),
                            )
                        }),
                )
            })
            .collect::<Vec<_>>()
    };
    let links_before = canonical_links(store);
    assert!(
        publish_contextual_direct_call_source_callable_with_resolution(store, &prepared).is_err()
    );
    assert_eq!(canonical_links(store), links_before);
    assert_eq!(counts(store), before);
    for proof in [outer, nested] {
        assert!(store.source_direct_call_resolution_was_registered(proof.callback()));
        assert!(
            store
                .source_direct_call_resolution(proof.callback())
                .is_none()
        );
        assert!(!store.source_direct_call_resolution_is_published(proof.callback()));
        assert!(!store.begin_source_direct_call_publication(proof.callback()));
        assert!(!store.finish_source_direct_call_resolution(proof.callback()));
    }
    assert_eq!(
        store.source_direct_call_resolution(top.callback()),
        Some(top)
    );
    assert!(store.source_direct_call_resolution_is_published(top.callback()));
    assert_eq!(counts(store), before);
}

#[test]
fn direct_call_resolution_revision_change_rejects_old_receipts() {
    let mut parsed = parse_source_file(SOURCE);
    let callbacks = callbacks(&parsed);
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    let proofs = proofs(&checker, &callbacks);
    let source = checker.source_file(FILE).unwrap();
    let mut store = std::mem::take(checker.store_mut_for_test());
    drop(checker);
    let before = counts(&store);
    let arena_id = parsed.arena.id();
    let revision = parsed.arena.revision();
    let original = parsed.arena.get(callbacks[0].node).unwrap().clone();
    // Mutable access advances the revision even when the node bytes stay equal.
    *parsed.arena.get_mut(callbacks[0].node).unwrap() = original;
    assert_eq!(parsed.arena.id(), arena_id);
    assert_ne!(parsed.arena.revision(), revision);
    assert_eq!(
        store.register_source_file(&parsed.arena, parsed.source_file, FILE),
        Some(source)
    );
    for proof in proofs {
        assert_eq!(proof.revision(), revision);
        assert!(store.source_direct_call_resolution_was_registered(proof.callback()));
        assert!(
            store
                .source_direct_call_resolution(proof.callback())
                .is_none()
        );
        assert!(!store.source_direct_call_resolution_is_published(proof.callback()));
        assert_eq!(store.begin_source_direct_call_resolution(proof), None);
    }
    assert_eq!(counts(&store), before);
    assert!(store.type_resolution_is_empty());
}
