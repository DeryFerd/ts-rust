use ts_ast::{FileId, NodeData, NodeId, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, InternalSymbolName, SemanticSymbolId, SymbolFlags,
};
use ts_parser::{ParseResult, parse_source_file};

use super::DerivedTypeError;
use crate::semantic::bootstrap::UnionReduction;
use crate::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, ObjectFlags,
    TypeData, TypeFlags, TypeId,
};

const FILE: FileId = FileId::new(20_242);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/computed-contextual-widening.ts\""),
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
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn object(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| node(parsed, variable.initializer.unwrap()))
        })
        .unwrap_or_else(|| panic!("missing object {expected}"))
}

fn source(computed: bool) -> ParseResult {
    parse_source_file(&format!(
        "const key = 'zebra'; declare const input: number;\n\
         const first = {{ {}: input }};\n\
         const second = {{ alpha: input }};\n\
         const third = {{ middle: input }};\n",
        if computed { "[key]" } else { "zebra" },
    ))
}

fn fresh_objects(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    query_first: bool,
) -> [TypeId; 3] {
    if query_first {
        context
            .get_type_at_location(object(parsed, "first"))
            .unwrap();
    } else {
        context.check_source_file(FILE).unwrap();
    }
    let types = ["first", "second", "third"]
        .map(|name| context.get_type_at_location(object(parsed, name)).unwrap());
    context.check_source_file(FILE).unwrap();
    assert!(context.diagnostics().is_empty());
    for type_ in types {
        let record = context.store().type_payload(type_).unwrap();
        assert!(record.object_flags().contains(ObjectFlags::FRESH_LITERAL));
        assert!(
            record
                .object_flags()
                .intersects(ObjectFlags::REQUIRES_WIDENING)
        );
    }
    types
}

fn properties(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> Vec<SemanticSymbolId> {
    let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data() else {
        panic!("expected a checked object")
    };
    object.structured.properties.as_ref().unwrap().clone()
}

fn union(
    context: &mut CanonicalCheckerContext<'_>,
    first: TypeId,
    second: TypeId,
    reverse: bool,
) -> TypeId {
    let members = if reverse {
        [second, first]
    } else {
        [first, second]
    };
    let union = context
        .store_mut_for_test()
        .expression_union_type(&members, UnionReduction::None)
        .unwrap();
    let record = context.store().type_payload(union).unwrap();
    let TypeData::Union(data) = record.data() else {
        panic!("the actual source objects must form a union")
    };
    assert_ne!(first, second);
    assert_eq!(data.union.types.len(), 2);
    assert!(data.union.types.contains(&first));
    assert!(data.union.types.contains(&second));
    assert!(
        record
            .object_flags()
            .intersects(ObjectFlags::REQUIRES_WIDENING)
    );
    union
}

fn widen(context: &mut CanonicalCheckerContext<'_>, union: TypeId) -> TypeId {
    context
        .store_mut_for_test()
        .get_widened_type(union)
        .unwrap()
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 8] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.type_alias_len(),
        store.symbol_store().symbol_table_len(),
        store.union_cache_len(),
    ]
}

fn contextual_members(context: &CanonicalCheckerContext<'_>, union: TypeId) -> Vec<TypeId> {
    let TypeData::Union(union) = context.store().type_payload(union).unwrap().data() else {
        panic!("the distinct source objects must remain a union")
    };
    assert_eq!(union.union.types.len(), 2);
    union.union.types.clone()
}

fn assert_contextual_union(
    context: &CanonicalCheckerContext<'_>,
    union: TypeId,
    sources: [TypeId; 2],
    sibling_name: &str,
) -> SemanticSymbolId {
    let store = context.store();
    let number = store.intrinsic_bootstrap().unwrap().number_type;
    let members = contextual_members(context, union);
    let mut missing_computed = None;
    for (source_index, source) in sources.into_iter().enumerate() {
        let owner = store.type_payload(source).unwrap().symbol();
        let target = *members
            .iter()
            .find(|&&type_| store.type_payload(type_).unwrap().symbol() == owner)
            .unwrap();
        assert_ne!(target, source);
        assert!(
            !store
                .type_payload(target)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::FRESH_LITERAL)
        );
        let symbols = properties(context, target);
        assert_eq!(symbols.len(), 2);
        let names = symbols
            .iter()
            .map(|&symbol| store.symbol(symbol).unwrap().name().as_utf8().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(names, ["zebra", sibling_name]);
        let own = properties(context, source)[0];
        for (property_index, symbol) in symbols.into_iter().enumerate() {
            let record = store.symbol(symbol).unwrap();
            let type_ = store
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type
                .unwrap();
            if source_index == property_index {
                assert_eq!(symbol, own);
                assert_eq!(type_, number);
                assert!(!record.flags().contains(SymbolFlags::OPTIONAL));
            } else {
                assert!(record.flags().contains(SymbolFlags::OPTIONAL));
                assert!(
                    store
                        .type_payload(type_)
                        .unwrap()
                        .flags()
                        .contains(TypeFlags::UNDEFINED)
                );
                if property_index == 0 {
                    missing_computed = Some(symbol);
                }
            }
        }
    }
    missing_computed.unwrap()
}

fn assert_source_property(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    fresh: TypeId,
    computed: bool,
) -> SemanticSymbolId {
    let source_object = object(parsed, "first");
    let NodeData::ObjectLiteralExpression(object) =
        &parsed.arena.get(source_object.node).unwrap().data
    else {
        panic!("expected the actual source object")
    };
    let declaration = node(parsed, object.properties.nodes[0]);
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    let published = properties(context, fresh)[0];
    let record = context.store().symbol(published).unwrap();
    assert_eq!(record.name().as_utf8().unwrap(), "zebra");
    assert_eq!(record.declarations(), Some(&[declaration][..]));
    assert_eq!(record.value_declaration(), Some(declaration));
    if computed {
        assert_ne!(published, raw);
        assert_eq!(
            context.store().symbol(raw).unwrap().name(),
            InternalSymbolName::Computed.as_ref()
        );
        let links = context.store().value_symbol_links(published).unwrap();
        assert_eq!(links.target, Some(raw));
        assert!(links.name_type.is_some());
    }
    published
}

#[test]
fn computed_and_ordinary_contextual_unions_keep_order_missing_types_and_cached_symbols() {
    for computed in [true, false] {
        let parsed = source(computed);
        for query_first in [false, true] {
            for reverse in [false, true] {
                let mut context = context(&parsed);
                let [first, second, third] = fresh_objects(&mut context, &parsed, query_first);
                assert_source_property(&context, &parsed, first, computed);
                let first_union = union(&mut context, first, second, reverse);
                let first_widened = widen(&mut context, first_union);
                let missing =
                    assert_contextual_union(&context, first_widened, [first, second], "alpha");
                // A different union must reuse the first union's missing-property clone.
                let second_union = union(&mut context, first, third, !reverse);
                assert_ne!(first_union, second_union);
                let second_widened = widen(&mut context, second_union);
                assert_eq!(
                    assert_contextual_union(&context, second_widened, [first, third], "middle"),
                    missing
                );
                let before = counts(&context);
                let diagnostics = context.diagnostics().clone();
                let links = parsed
                    .arena
                    .iter()
                    .map(|(id, _)| {
                        let location = node(&parsed, id);
                        (
                            location,
                            context.store().type_node_links(location).cloned(),
                            context.store().symbol_node_links(location).cloned(),
                            context.store().signature_links(location).cloned(),
                        )
                    })
                    .collect::<Vec<_>>();
                for _ in 0..2 {
                    assert_eq!(widen(&mut context, first_union), first_widened);
                    assert_eq!(widen(&mut context, second_union), second_widened);
                    context.check_source_file(FILE).unwrap();
                    context.recheck_source_file(FILE).unwrap();
                    assert_eq!(
                        assert_contextual_union(&context, first_widened, [first, second], "alpha"),
                        missing
                    );
                    assert_eq!(
                        assert_contextual_union(&context, second_widened, [first, third], "middle"),
                        missing
                    );
                    for (location, type_links, symbol_links, signature_links) in &links {
                        assert_eq!(
                            context.store().type_node_links(*location),
                            type_links.as_ref()
                        );
                        assert_eq!(
                            context.store().symbol_node_links(*location),
                            symbol_links.as_ref()
                        );
                        assert_eq!(
                            context.store().signature_links(*location),
                            signature_links.as_ref()
                        );
                    }
                    assert_eq!(counts(&context), before);
                    assert_eq!(context.diagnostics(), &diagnostics);
                }
            }
        }
    }
}

#[test]
fn computed_contextual_name_proofs_reject_corruption_without_publication_and_recover() {
    let parsed = source(true);
    let mut context = context(&parsed);
    let [first, second, third] = fresh_objects(&mut context, &parsed, true);
    let computed = assert_source_property(&context, &parsed, first, true);
    let first_union = union(&mut context, first, second, false);
    let first_widened = widen(&mut context, first_union);
    let missing = assert_contextual_union(&context, first_widened, [first, second], "alpha");
    let second_union = union(&mut context, first, third, true);
    let second_widened = widen(&mut context, second_union);
    assert_eq!(
        assert_contextual_union(&context, second_widened, [first, third], "middle"),
        missing
    );

    for symbol in [computed, missing] {
        let original = context.store().value_symbol_links(symbol).unwrap().clone();
        let mut corrupt = original.clone();
        corrupt.name_type = Some(context.store().intrinsic_bootstrap().unwrap().number_type);
        assert_ne!(corrupt.name_type, original.name_type);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(symbol, corrupt.clone())
        );
        let before = counts(&context);
        let diagnostics = context.diagnostics().clone();
        assert_eq!(context.store().contextual_property_order_key(symbol), None);
        for (source, cached) in [(first_union, first_widened), (second_union, second_widened)] {
            assert!(matches!(
                context.store_mut_for_test().get_widened_type(source),
                Err(DerivedTypeError::InvalidWidenedTypeCache { source: actual_source, cached: actual_cached })
                    if actual_source == source && actual_cached == cached
            ));
            assert_eq!(context.store().value_symbol_links(symbol), Some(&corrupt));
            assert_eq!(counts(&context), before);
            assert_eq!(context.diagnostics(), &diagnostics);
        }
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(symbol, original)
        );
        assert!(
            context
                .store()
                .contextual_property_order_key(symbol)
                .is_some()
        );
        assert_eq!(widen(&mut context, first_union), first_widened);
        assert_eq!(widen(&mut context, second_union), second_widened);
        assert_eq!(
            assert_contextual_union(&context, first_widened, [first, second], "alpha"),
            missing
        );
        assert_eq!(
            assert_contextual_union(&context, second_widened, [first, third], "middle"),
            missing
        );
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(counts(&context), before);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

#[test]
fn computed_contextual_nested_values_keep_normal_clone_proofs_and_recover_after_corruption() {
    let parsed = parse_source_file(concat!(
        "const key = 'zebra'; declare const input: number;\n",
        "const first = { [key]: { inner: input } };\n",
        "const second = { alpha: input };\n",
        "const third = { middle: input };\n",
    ));
    for query_first in [false, true] {
        let mut context = context(&parsed);
        let [first, second, _] = fresh_objects(&mut context, &parsed, query_first);
        let computed = assert_source_property(&context, &parsed, first, true);
        let source_links = context
            .store()
            .value_symbol_links(computed)
            .unwrap()
            .clone();
        let source_nested = source_links.resolved_type.unwrap();
        assert!(
            context
                .store()
                .type_payload(source_nested)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::FRESH_LITERAL)
        );
        let source_union = union(&mut context, first, second, false);
        let widened_union = widen(&mut context, source_union);
        let owner = context.store().type_payload(first).unwrap().symbol();
        let target = contextual_members(&context, widened_union)
            .into_iter()
            .find(|&type_| context.store().type_payload(type_).unwrap().symbol() == owner)
            .unwrap();
        assert_ne!(target, first);
        let target_properties = properties(&context, target);
        assert_eq!(target_properties.len(), 2);
        let names = target_properties
            .iter()
            .map(|&symbol| {
                context
                    .store()
                    .symbol(symbol)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(names, ["zebra", "alpha"]);
        let clone = target_properties[0];
        assert_ne!(clone, computed);
        let original = context.store().value_symbol_links(clone).unwrap().clone();
        assert_eq!(original.target, Some(computed));
        assert_eq!(original.name_type, source_links.name_type);
        let widened_nested = original.resolved_type.unwrap();
        assert_ne!(widened_nested, source_nested);
        assert_eq!(widen(&mut context, source_nested), widened_nested);
        assert!(
            !context
                .store()
                .type_payload(widened_nested)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::FRESH_LITERAL)
        );
        let inner = properties(&context, widened_nested);
        assert_eq!(inner.len(), 1);
        assert_eq!(
            context
                .store()
                .symbol(inner[0])
                .unwrap()
                .name()
                .as_utf8()
                .unwrap(),
            "inner"
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(inner[0])
                .unwrap()
                .resolved_type,
            Some(context.store().intrinsic_bootstrap().unwrap().number_type)
        );
        assert!(
            context
                .store()
                .contextual_property_order_key(clone)
                .is_some()
        );

        let before = counts(&context);
        let diagnostics = context.diagnostics().clone();
        for _ in 0..2 {
            assert_eq!(widen(&mut context, source_union), widened_union);
            assert_eq!(properties(&context, target), target_properties);
            assert_eq!(context.store().value_symbol_links(clone), Some(&original));
            context.check_source_file(FILE).unwrap();
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(counts(&context), before);
            assert_eq!(context.diagnostics(), &diagnostics);
        }

        let mut corrupt = original.clone();
        corrupt.name_type = Some(context.store().intrinsic_bootstrap().unwrap().number_type);
        assert_ne!(corrupt.name_type, original.name_type);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(clone, corrupt.clone())
        );
        assert_eq!(context.store().contextual_property_order_key(clone), None);
        assert!(matches!(
            context.store_mut_for_test().get_widened_type(source_union),
            Err(DerivedTypeError::InvalidWidenedTypeCache { source, cached })
                if source == source_union && cached == widened_union
        ));
        assert_eq!(context.store().value_symbol_links(clone), Some(&corrupt));
        assert_eq!(counts(&context), before);
        assert_eq!(context.diagnostics(), &diagnostics);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(clone, original.clone())
        );
        assert!(
            context
                .store()
                .contextual_property_order_key(clone)
                .is_some()
        );
        assert_eq!(widen(&mut context, source_union), widened_union);
        assert_eq!(properties(&context, target), target_properties);
        assert_eq!(context.store().value_symbol_links(clone), Some(&original));
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(counts(&context), before);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}
