use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, TypeData, TypeId, TypeRecord, type_to_string,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "type A2 = keyof { a: 1; b: 2 };\n",
    "type A2R = keyof { b: 3; a: 4 };\n",
    "type A1 = keyof { a: 1 };\n",
    "type E = keyof {};\n",
    "type SI = keyof { [k: string]: unknown };\n",
    "type NI = keyof { [k: number]: unknown };\n",
    "type MN = keyof { fixed: 1; [k: number]: unknown };\n",
    "type MS = keyof { fixed: 1; [k: string]: unknown };\n",
    "type MSP = keyof ({ fixed: 1; [k: string]: unknown });\n",
    "interface I { a: 1; b: 2 }\n",
    "interface J { a: 1; b: 2 }\n",
    "interface One { only: 1 }\n",
    "interface Empty {}\n",
    "interface Table { [k: string]: unknown }\n",
    "interface Node { next: Node }\n",
    "type KI = keyof I;\n",
    "type KI2 = keyof I;\n",
    "type KJ = keyof J;\n",
    "type KO = keyof One;\n",
    "type KE = keyof Empty;\n",
    "type KT = keyof Table;\n",
    "type KN = keyof Node;\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/keyof-types.ts\""),
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

fn named_symbol(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    kind: SyntaxKind,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::TypeAliasDeclaration(declaration) => declaration.name,
                NodeData::InterfaceDeclaration(declaration) => declaration.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {expected}"));
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn alias_parts(
    parsed: &ParseResult,
    file: FileId,
    context: &CanonicalCheckerContext<'_>,
    expected: &str,
) -> (SemanticSymbolId, NodeRef) {
    let rhs = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, alias.type_))
        })
        .unwrap_or_else(|| panic!("missing alias {expected}"));
    (
        named_symbol(
            parsed,
            file,
            context,
            SyntaxKind::TypeAliasDeclaration,
            expected,
        ),
        rhs,
    )
}

fn alias_type(context: &CanonicalCheckerContext<'_>, alias: SemanticSymbolId) -> TypeId {
    context
        .store()
        .type_alias_links(alias)
        .and_then(|links| links.declared_type)
        .expect("source checking resolves the keyof alias")
}

fn interface_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
        .expect("source checking resolves the keyof operand")
}

fn union_parts(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> (Vec<TypeId>, Option<TypeId>) {
    let Some(TypeData::Union(union)) = context.store().type_payload(type_).map(TypeRecord::data)
    else {
        panic!("expected union type {type_:?}");
    };
    (union.union.types.clone(), union.origin)
}

#[test]
#[allow(clippy::too_many_lines)] // The complete keyof matrix shares one canonical source graph.
fn source_keyof_aliases_preserve_canonical_keys_origins_and_warm_caches() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);
    let aliases = [
        "A2", "A2R", "A1", "E", "SI", "NI", "MN", "MS", "MSP", "KI", "KI2", "KJ", "KO", "KE", "KT",
        "KN",
    ]
    .into_iter()
    .map(|name| (name, alias_parts(&parsed, file, &context, name)))
    .collect::<std::collections::BTreeMap<_, _>>();
    let interfaces = ["I", "J", "One", "Empty", "Table", "Node"]
        .into_iter()
        .map(|name| {
            (
                name,
                named_symbol(
                    &parsed,
                    file,
                    &context,
                    SyntaxKind::InterfaceDeclaration,
                    name,
                ),
            )
        })
        .collect::<std::collections::BTreeMap<_, _>>();

    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let type_of = |name: &str| alias_type(&context, aliases[name].0);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let a = bootstrap.cached_string_literal_type("a").unwrap();
    let b = bootstrap.cached_string_literal_type("b").unwrap();
    let fixed = bootstrap.cached_string_literal_type("fixed").unwrap();
    let only = bootstrap.cached_string_literal_type("only").unwrap();
    let next = bootstrap.cached_string_literal_type("next").unwrap();

    assert_eq!(type_of("A2"), type_of("A2R"));
    let (mut a2, a2_origin) = union_parts(&context, type_of("A2"));
    a2.sort_unstable();
    let mut expected_a2 = vec![a, b];
    expected_a2.sort_unstable();
    assert_eq!(a2, expected_a2);
    assert_eq!(a2_origin, None);
    assert_eq!(type_of("A1"), a);
    assert_eq!(type_of("E"), bootstrap.never_type);
    assert_eq!(type_of("SI"), bootstrap.string_or_number_type);
    assert_eq!(type_of("NI"), bootstrap.number_type);
    let (mut mn, mn_origin) = union_parts(&context, type_of("MN"));
    mn.sort_unstable();
    let mut expected_mn = vec![bootstrap.number_type, fixed];
    expected_mn.sort_unstable();
    assert_eq!(mn, expected_mn);
    assert_eq!(mn_origin, None);
    assert_eq!(type_of("MS"), bootstrap.string_or_number_type);
    assert_eq!(type_of("MSP"), bootstrap.string_or_number_type);

    let i = interface_type(&context, interfaces["I"]);
    let j = interface_type(&context, interfaces["J"]);
    let ki = type_of("KI");
    assert_eq!(type_of("KI2"), ki);
    assert_ne!(type_of("KJ"), ki);
    for (result, target, display) in [(ki, i, "keyof I"), (type_of("KJ"), j, "keyof J")] {
        let (keys, origin) = union_parts(&context, result);
        let mut keys = keys;
        keys.sort_unstable();
        assert_eq!(keys, expected_a2);
        let origin = origin.expect("named two-key keyof keeps its Index origin");
        let Some(TypeData::Index(index)) =
            context.store().type_payload(origin).map(TypeRecord::data)
        else {
            panic!("keyof origin must be an Index type");
        };
        assert_eq!(index.target, target);
        assert_eq!(type_to_string(context.store(), result).unwrap(), display);
    }
    assert_eq!(type_of("KO"), only);
    assert_eq!(type_of("KE"), bootstrap.never_type);
    assert_eq!(type_of("KT"), bootstrap.string_or_number_type);
    let table = interface_type(&context, interfaces["Table"]);
    let Some(TypeData::Interface(table)) =
        context.store().type_payload(table).map(TypeRecord::data)
    else {
        panic!("Table must resolve to an interface");
    };
    assert_eq!(
        table.declared_index_infos.as_deref(),
        table.reference.object.structured.index_infos.as_deref(),
    );
    assert_eq!(table.declared_index_infos.as_deref().unwrap().len(), 1);
    assert_eq!(type_of("KN"), next);

    for (alias, rhs) in aliases.values() {
        assert_eq!(
            context
                .store()
                .type_node_links(*rhs)
                .and_then(|links| links.resolved_type),
            Some(alias_type(&context, *alias)),
        );
    }

    let warm = (
        context.store().type_len(),
        context.store().type_alias_len(),
        context.store().index_info_len(),
        context.store().properties_type_cache_len(),
        context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .string_literal_cache_len(),
        context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .union_cache_len(),
        context.diagnostics().clone(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().type_alias_len(),
            context.store().index_info_len(),
            context.store().properties_type_cache_len(),
            context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .string_literal_cache_len(),
            context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .union_cache_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn source_keyof_distributes_over_object_unions_and_intersections() {
    let source = concat!(
        "interface Left { shared: string; left: number }\n",
        "interface Right { shared: string; right: boolean }\n",
        "type All = keyof (Left & Right);\n",
        "type Common = keyof (Left | Right);\n",
        "type Empty = keyof ({ first: string } | { second: number });\n",
        "type AnyKeys = keyof any;\n",
        "type UnknownKeys = keyof unknown;\n",
        "type NeverKeys = keyof never;\n",
        "type ImpossibleKeys = keyof ({ kind: 'left' } & { kind: 'right' });\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(9_021);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap_or_else(|error| {
        let aliases = [
            "All",
            "Common",
            "Empty",
            "AnyKeys",
            "UnknownKeys",
            "NeverKeys",
            "ImpossibleKeys",
        ]
        .map(|name| (name, alias_parts(&parsed, file, &context, name).1));
        panic!("source checking failed: {error:?}; aliases: {aliases:?}");
    });
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let type_of = |name| {
        let (alias, _) = alias_parts(&parsed, file, &context, name);
        alias_type(&context, alias)
    };
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let shared = bootstrap.cached_string_literal_type("shared").unwrap();
    let left = bootstrap.cached_string_literal_type("left").unwrap();
    let right = bootstrap.cached_string_literal_type("right").unwrap();
    let (all, _) = union_parts(&context, type_of("All"));
    assert_eq!(all.len(), 3);
    assert!(all.contains(&shared));
    assert!(all.contains(&left));
    assert!(all.contains(&right));
    assert_eq!(type_of("Common"), shared);
    assert_eq!(type_of("Empty"), bootstrap.never_type);
    assert_eq!(type_of("AnyKeys"), bootstrap.string_number_symbol_type);
    assert_eq!(type_of("UnknownKeys"), bootstrap.never_type);
    assert_eq!(type_of("NeverKeys"), bootstrap.string_number_symbol_type);
    assert_eq!(
        type_of("ImpossibleKeys"),
        bootstrap.string_number_symbol_type
    );

    let warm = (
        context.store().type_len(),
        context.store().properties_type_cache_len(),
        bootstrap.string_literal_cache_len(),
        bootstrap.union_cache_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().properties_type_cache_len(),
            bootstrap.string_literal_cache_len(),
            bootstrap.union_cache_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

const PROPERTY_KEYS: &str = concat!(
    "type Keys<T> = keyof T;\n",
    "type Box<T> = { value: T };\n",
    "type Result = Keys<Box<number>>;\n",
    "declare const key: Result;\n",
    "const exact: \"value\" = key;\n",
    "const check: Result = \"value\";\n",
);

const WRAPPED_PROPERTY_KEYS: &str = concat!(
    "type Keys<T> = keyof T;\n",
    "type Inner<T> = ({ value: T });\n",
    "type Outer<U> = (Inner<U>);\n",
    "type Result = Keys<Outer<number>>;\n",
    "declare const key: Result;\n",
    "const exact: \"value\" = key;\n",
    "const check: Result = \"value\";\n",
);

const SHAPE_KEYS: &str = concat!(
    "type Keys<T> = keyof T;\n",
    "type Shape<T> = {\n",
    "  first: T;\n",
    "  second: () => T;\n",
    "  readonly third: number;\n",
    "  fourth?: T;\n",
    "};\n",
    "type Result = Keys<Shape<string>>;\n",
    "declare const key: Result;\n",
    "const exact: \"first\" | \"second\" | \"third\" | \"fourth\" = key;\n",
    "declare const expected: \"first\" | \"second\" | \"third\" | \"fourth\";\n",
    "const complete: Result = expected;\n",
    "const check: Result = \"first\";\n",
);

const DIRECT_PROPERTY_KEYS: &str = concat!(
    "type Box<T> = { value: T };\n",
    "type Result = keyof Box<number>;\n",
    "declare const key: Result;\n",
    "const exact: \"value\" = key;\n",
    "const check: Result = \"value\";\n",
);

const UNION_PROPERTY_KEYS: &str = concat!(
    "type Keys<T> = keyof T;\n",
    "type Left<T> = { shared: T; left: number };\n",
    "type Right<T> = { shared: T; right: boolean };\n",
    "type Result = Keys<Left<string> | Right<number>>;\n",
    "declare const key: Result;\n",
    "const exact: \"shared\" = key;\n",
    "const check: Result = \"shared\";\n",
);

fn property_key_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/property-keys.ts\""),
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
        vec![(file, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: ts_checker::semantic::IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            strict_property_initialization: true,
            no_implicit_any: true,
            no_implicit_this: true,
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn property_key_snapshot(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    let bootstrap = store.intrinsic_bootstrap().unwrap();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.mapper_len(),
            store.signature_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.properties_type_cache_len(),
            bootstrap.string_literal_cache_len(),
            bootstrap.union_cache_len(),
        ],
        parsed
            .arena
            .iter()
            .map(|(node, _)| {
                let node = NodeRef::new(parsed.arena.id(), file, node);
                (
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        context.diagnostics().clone(),
    )
}

fn check_property_keys(source: &str, keys: &[&str], display: &str) {
    let valid_assignment = format!("const check: Result = {:?};", keys[0]);
    assert_eq!(source.matches(&valid_assignment).count(), 1);
    let invalid = source.replace(&valid_assignment, "const check: Result = \"missing\";");
    for (source, negative) in [(source, false), (invalid.as_str(), true)] {
        for query_first in [false, true] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(9_022);
            let mut context = property_key_context(&parsed, file);
            let (alias, rhs) = alias_parts(&parsed, file, &context, "Result");
            let cold = query_first.then(|| context.get_type_from_type_node(rhs).unwrap());
            context.check_source_file(file).unwrap();
            assert!(
                context
                    .store()
                    .source_file_links(context.source_file(file).unwrap())
                    .unwrap()
                    .type_checked
            );
            let result = alias_type(&context, alias);
            assert_eq!(context.get_type_from_type_node(rhs), Ok(result));
            if let Some(cold) = cold {
                assert_eq!(cold, result);
            }

            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let mut expected = keys
                .iter()
                .map(|key| bootstrap.cached_string_literal_type(key).unwrap())
                .collect::<Vec<_>>();
            expected.sort_unstable();
            if keys.len() == 1 {
                assert_eq!(result, expected[0]);
            } else {
                let (mut actual, origin) = union_parts(&context, result);
                actual.sort_unstable();
                assert_eq!(actual, expected);
                let NodeData::TypeReferenceNode(reference) =
                    &parsed.arena.get(rhs.node).unwrap().data
                else {
                    panic!("Result must reference Keys");
                };
                let [argument] = reference.type_arguments.as_ref().unwrap().nodes.as_slice() else {
                    panic!("Keys must have one argument");
                };
                let target = context
                    .get_type_from_type_node(NodeRef::new(parsed.arena.id(), file, *argument))
                    .unwrap();
                let Some(TypeData::Index(index)) = context
                    .store()
                    .type_payload(origin.expect("named keys retain their receiver origin"))
                    .map(TypeRecord::data)
                else {
                    panic!("key origin must be an Index type");
                };
                assert_eq!(index.target, target);
            }

            let errors = context.diagnostics().as_slice();
            assert_eq!(errors.len(), usize::from(negative), "{errors:?}");
            if negative {
                let error = &errors[0];
                assert_eq!(error.diagnostic.code(), 2322);
                assert_eq!(
                    error.diagnostic.arguments,
                    ["\"missing\"", display]
                );
                let record = parsed.arena.get(error.node.unwrap().node).unwrap();
                assert_eq!(record.kind, SyntaxKind::Identifier);
                assert_eq!(
                    record.range.start.get() as usize,
                    source.rfind("check:").unwrap()
                );
                assert_eq!(
                    &source[record.range.start.get() as usize..record.range.end.get() as usize],
                    "check"
                );
                assert!(error.range_override.is_none());
                assert!(error.related_information.is_empty());
            }

            let warm = property_key_snapshot(&context, &parsed, file);
            for _ in 0..2 {
                context.recheck_source_file(file).unwrap();
                assert_eq!(context.get_type_from_type_node(rhs), Ok(result));
                assert_eq!(alias_type(&context, alias), result);
                assert_eq!(property_key_snapshot(&context, &parsed, file), warm);
            }
        }
    }
}

#[test]
fn source_keyof_instantiated_property_alias_keeps_keys_and_cached_queries() {
    check_property_keys(PROPERTY_KEYS, &["value"], "\"value\"");
}

#[test]
fn source_keyof_wrapped_property_alias_keeps_keys_and_cached_queries() {
    check_property_keys(WRAPPED_PROPERTY_KEYS, &["value"], "\"value\"");
}

#[test]
fn source_keyof_instantiated_shape_keeps_all_keys_and_receiver_origin() {
    check_property_keys(
        SHAPE_KEYS,
        &["first", "second", "third", "fourth"],
        "keyof Shape<string>",
    );
}

#[test]
fn source_direct_keyof_instantiated_property_alias_keeps_cached_queries() {
    check_property_keys(DIRECT_PROPERTY_KEYS, &["value"], "\"value\"");
}

#[test]
fn source_keyof_property_alias_union_keeps_only_shared_keys() {
    check_property_keys(UNION_PROPERTY_KEYS, &["shared"], "\"shared\"");
}

#[test]
fn source_keyof_alias_default_maps_only_earlier_parameters() {
    let source = concat!(
        "type Keys<T, K = keyof T> = K;\n",
        "type Box<T> = { value: T };\n",
        "type Result = Keys<Box<number>>;\n",
        "declare const key: Result;\n",
        "const exact: \"value\" = key;\n",
        "const check: Result = \"value\";\n",
    );
    check_property_keys(source, &["value"], "\"value\"");
}

#[test]
fn source_keyof_keeps_array_context_through_preparation_and_replay() {
    let library = "interface IArguments {} interface Object {} interface Function {} interface String {} interface Number {} interface Boolean {} interface RegExp {} interface Array<T> { length: number; [index: number]: T; } interface ReadonlyArray<T> { readonly length: number; readonly [index: number]: T; } interface ThisType<T> {}\n";
    let consumer = concat!(
        "type Seed = Array<number> | undefined;\n",
        "type ReadonlySeed = ReadonlyArray<number> | undefined;\n",
        "type Keys<T> = keyof T;\n",
        "type Pair<T> = { first: T; second: T };\n",
        "type Result = Keys<Pair<number>>;\n",
        "type Plain = keyof { first: number; second: number };\n",
        "declare const result: Result;\n",
        "const exact: \"first\" | \"second\" = result;\n",
        "declare const expected: \"first\" | \"second\";\n",
        "const complete: Result = expected;\n",
    );
    for negative in [false, true] {
        let consumer = if negative {
            consumer.replace(
                "const complete: Result = expected;",
                "const complete: Result = \"missing\";",
            )
        } else {
            consumer.to_owned()
        };
        let source = format!("{library}{consumer}");
        for query_first in [false, true] {
            let parsed = parse_source_file(&source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(9_023);
            let mut context = property_key_context(&parsed, file);
            let mut targets = Vec::new();
            let mut seeds = Vec::new();
            for (name, seed) in [("Array", "Seed"), ("ReadonlyArray", "ReadonlySeed")] {
                let symbol = named_symbol(
                    &parsed,
                    file,
                    &context,
                    SyntaxKind::InterfaceDeclaration,
                    name,
                );
                let target = context.get_declared_type_of_symbol(symbol).unwrap();
                targets.push(target);
                let (_, rhs) = alias_parts(&parsed, file, &context, seed);
                let type_ = context.get_type_from_type_node(rhs).unwrap();
                let (members, _) = union_parts(&context, type_);
                let bootstrap = context.store().intrinsic_bootstrap().unwrap();
                assert_eq!(members.len(), 2);
                assert!(members.contains(&bootstrap.undefined_type));
                let reference = *members
                    .iter()
                    .find(|member| **member != bootstrap.undefined_type)
                    .unwrap();
                let Some(TypeData::TypeReference(reference)) = context
                    .store()
                    .type_payload(reference)
                    .map(TypeRecord::data)
                else {
                    panic!("the seed must retain its source array reference");
                };
                assert_eq!(reference.object.target, Some(target));
                assert_eq!(
                    reference.resolved_type_arguments.as_deref(),
                    Some(&[bootstrap.number_type][..])
                );
                assert_ne!(target, bootstrap.empty_generic_type);
                seeds.push((rhs, type_));
            }
            assert_ne!(targets[0], targets[1]);

            let (alias, rhs) = alias_parts(&parsed, file, &context, "Result");
            let (_, plain_rhs) = alias_parts(&parsed, file, &context, "Plain");
            let cold = query_first.then(|| {
                (
                    context.get_type_from_type_node(rhs).unwrap(),
                    context.get_type_from_type_node(plain_rhs).unwrap(),
                )
            });
            context.check_source_file(file).unwrap();
            let result = context.get_type_from_type_node(rhs).unwrap();
            let plain = context.get_type_from_type_node(plain_rhs).unwrap();
            assert_eq!(alias_type(&context, alias), result);
            if let Some(cold) = cold {
                assert_eq!(cold, (result, plain));
            }
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let mut expected =
                ["first", "second"].map(|name| bootstrap.cached_string_literal_type(name).unwrap());
            expected.sort_unstable();
            for type_ in [result, plain] {
                let (mut keys, _) = union_parts(&context, type_);
                keys.sort_unstable();
                assert_eq!(keys, expected);
            }
            assert!(union_parts(&context, plain).1.is_none());
            let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(rhs.node).unwrap().data
            else {
                panic!("Result must reference Keys");
            };
            let [argument] = reference.type_arguments.as_ref().unwrap().nodes.as_slice() else {
                panic!("Keys must have one argument");
            };
            let target = context
                .get_type_from_type_node(NodeRef::new(parsed.arena.id(), file, *argument))
                .unwrap();
            let origin = union_parts(&context, result)
                .1
                .expect("named keys retain their origin");
            let Some(TypeData::Index(index)) =
                context.store().type_payload(origin).map(TypeRecord::data)
            else {
                panic!("named keys must retain an Index origin");
            };
            assert_eq!(index.target, target);

            let errors = context.diagnostics().as_slice();
            assert_eq!(errors.len(), usize::from(negative), "{errors:?}");
            if negative {
                let error = &errors[0];
                assert_eq!(error.diagnostic.code(), 2322);
                assert_eq!(
                    error.diagnostic.arguments,
                    ["\"missing\"", "keyof Pair<number>"]
                );
                let node = parsed.arena.get(error.node.unwrap().node).unwrap();
                assert_eq!(node.kind, SyntaxKind::Identifier);
                assert_eq!(
                    node.range.start.get() as usize,
                    source.rfind("complete:").unwrap()
                );
                assert_eq!(
                    &source[node.range.start.get() as usize..node.range.end.get() as usize],
                    "complete"
                );
                assert!(error.range_override.is_none());
                assert!(error.related_information.is_empty());
            }
            let warm = property_key_snapshot(&context, &parsed, file);
            for _ in 0..2 {
                context.recheck_source_file(file).unwrap();
                assert_eq!(context.get_type_from_type_node(rhs), Ok(result));
                assert_eq!(context.get_type_from_type_node(plain_rhs), Ok(plain));
                for (node, type_) in &seeds {
                    assert_eq!(context.get_type_from_type_node(*node), Ok(*type_));
                }
                assert_eq!(property_key_snapshot(&context, &parsed, file), warm);
            }
        }
    }
}
