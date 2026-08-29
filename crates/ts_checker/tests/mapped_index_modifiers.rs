use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
    types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(5_184);

fn context(parsed: &ParseResult, strict: bool, exact: bool) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/mapped-index-modifiers.ts\""),
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
                strict_null_checks: strict,
                exact_optional_property_types: exact,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn alias_type(parsed: &ParseResult, context: &CanonicalCheckerContext<'_>, name: &str) -> TypeId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap_or_else(|| panic!("missing alias {name}"));
    let symbol = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context
        .store()
        .type_alias_links(symbol)
        .and_then(|links| links.declared_type)
        .unwrap_or_else(|| panic!("unresolved alias {name}"))
}

fn indexes(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> Vec<(TypeId, TypeId, bool)> {
    let TypeData::Mapped(mapped) = context.store().type_payload(type_).unwrap().data() else {
        panic!("the index owner must retain its mapped type")
    };
    mapped
        .object
        .structured
        .index_infos
        .as_deref()
        .unwrap_or_default()
        .iter()
        .map(|index| {
            let info = context.store().index_info(*index).unwrap();
            (info.key_type(), info.value_type(), info.is_readonly())
        })
        .collect()
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize, usize) {
    let store = context.store();
    (
        store.type_len(),
        store.symbol_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.intrinsic_bootstrap().unwrap().union_cache_len(),
    )
}

#[test]
fn homomorphic_any_has_one_string_index_and_keeps_general_keyof_any() {
    let parsed = parse_source_file(concat!(
        "interface Wrapper<Value> { value: Value } ",
        "type Cells<Model> = { readonly [Key in keyof Model]-?: Wrapper<Model[Key]> }; ",
        "type Concrete = Cells<any>; ",
        "type StringCells = { [key: string]: Wrapper<any> }; ",
        "type NumberCells = { [key: number]: Wrapper<any> }; ",
        "type Wrong = { [key: string]: number }; ",
        "type AnyKeys = keyof any;",
    ));
    let mut context = context(&parsed, true, true);
    context.check_source_file(FILE).unwrap();
    assert!(context.diagnostics().is_empty());
    let concrete = alias_type(&parsed, &context, "Concrete");
    let strings = alias_type(&parsed, &context, "StringCells");
    let numbers = alias_type(&parsed, &context, "NumberCells");
    let wrong = alias_type(&parsed, &context, "Wrong");
    assert!(context.is_type_assignable_to(concrete, strings).unwrap());
    assert!(context.is_type_assignable_to(concrete, numbers).unwrap());
    assert!(!context.is_type_assignable_to(concrete, wrong).unwrap());
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let actual = indexes(&context, concrete);
    let [(key, value, readonly)] = actual.as_slice() else {
        panic!("the mapped any source must publish one string index: {actual:?}")
    };
    assert_eq!(*key, bootstrap.string_type);
    assert!(*readonly);
    let TypeData::TypeReference(reference) = context.store().type_payload(*value).unwrap().data()
    else {
        panic!("the index value must keep its Wrapper reference")
    };
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[bootstrap.any_type][..])
    );
    let keys = alias_type(&parsed, &context, "AnyKeys");
    let TypeData::Union(union) = context.store().type_payload(keys).unwrap().data() else {
        panic!("general keyof any must remain a union")
    };
    assert_eq!(union.union.types.len(), 3);
    for key in [
        bootstrap.string_type,
        bootstrap.number_type,
        bootstrap.es_symbol_type,
    ] {
        assert!(union.union.types.contains(&key));
    }
    let warm = counts(&context);
    context.recheck_source_file(FILE).unwrap();
    assert!(context.is_type_assignable_to(concrete, strings).unwrap());
    assert!(context.is_type_assignable_to(concrete, numbers).unwrap());
    assert!(!context.is_type_assignable_to(concrete, wrong).unwrap());
    assert_eq!(indexes(&context, concrete), actual);
    assert_eq!(counts(&context), warm);
}

#[test]
fn optional_any_indexes_use_the_strict_property_sentinel() {
    for (strict, exact) in [(false, false), (true, false), (true, true)] {
        let parsed = parse_source_file(concat!(
            "interface Wrapper<Value> { value: Value } ",
            "type Soft<Model> = { readonly [Key in keyof Model]?: Wrapper<Model[Key]> }; ",
            "type Concrete = Soft<any>; ",
            "type Required = { [key: string]: Wrapper<any> }; ",
            "type Optional = { [key: string]: Wrapper<any> | undefined }; ",
            "type Wrong = { [key: string]: number };",
        ));
        let mut context = context(&parsed, strict, exact);
        context.check_source_file(FILE).unwrap();
        assert!(context.diagnostics().is_empty());
        let concrete = alias_type(&parsed, &context, "Concrete");
        let required = alias_type(&parsed, &context, "Required");
        let optional = alias_type(&parsed, &context, "Optional");
        let wrong = alias_type(&parsed, &context, "Wrong");
        assert!(context.is_type_assignable_to(concrete, optional).unwrap());
        assert_eq!(
            context.is_type_assignable_to(concrete, required).unwrap(),
            !strict
        );
        assert!(!context.is_type_assignable_to(concrete, wrong).unwrap());
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let actual = indexes(&context, concrete);
        let [(key, value, readonly)] = actual.as_slice() else {
            panic!("the optional mapped any source must publish one index: {actual:?}")
        };
        assert_eq!(*key, bootstrap.string_type);
        assert!(*readonly);
        let wrapper = if strict {
            let TypeData::Union(union) = context.store().type_payload(*value).unwrap().data()
            else {
                panic!("an optional strict index must include undefined")
            };
            assert_eq!(union.union.types.len(), 2);
            assert!(
                union
                    .union
                    .types
                    .contains(&bootstrap.undefined_or_missing_type)
            );
            *union
                .union
                .types
                .iter()
                .find(|type_| **type_ != bootstrap.undefined_or_missing_type)
                .unwrap()
        } else {
            *value
        };
        let TypeData::TypeReference(reference) =
            context.store().type_payload(wrapper).unwrap().data()
        else {
            panic!("the optional index must keep its Wrapper reference")
        };
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(&[bootstrap.any_type][..])
        );
        let warm = counts(&context);
        context.recheck_source_file(FILE).unwrap();
        assert!(context.is_type_assignable_to(concrete, optional).unwrap());
        assert_eq!(
            context.is_type_assignable_to(concrete, required).unwrap(),
            !strict
        );
        assert!(!context.is_type_assignable_to(concrete, wrong).unwrap());
        assert_eq!(indexes(&context, concrete), actual);
        assert_eq!(counts(&context), warm, "strict={strict}, exact={exact}");
    }
}

#[test]
fn explicit_key_unions_keep_number_and_symbol_indexes() {
    let parsed = parse_source_file(concat!(
        "type Keys = string | number | symbol; ",
        "type Entries = { [Key in Keys]?: number }; ",
        "type Optional = { [key: string]: number | undefined }; ",
        "type Required = { [key: string]: number };",
    ));
    let mut context = context(&parsed, true, false);
    context.check_source_file(FILE).unwrap();
    assert!(context.diagnostics().is_empty());
    let entries = alias_type(&parsed, &context, "Entries");
    let optional = alias_type(&parsed, &context, "Optional");
    let required = alias_type(&parsed, &context, "Required");
    assert!(context.is_type_assignable_to(entries, optional).unwrap());
    assert!(!context.is_type_assignable_to(entries, required).unwrap());
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let actual = indexes(&context, entries);
    assert_eq!(actual.len(), 3);
    for key in [
        bootstrap.string_type,
        bootstrap.number_type,
        bootstrap.es_symbol_type,
    ] {
        assert!(
            actual
                .iter()
                .any(|(actual, _, readonly)| *actual == key && !readonly)
        );
    }
    let warm = counts(&context);
    context.recheck_source_file(FILE).unwrap();
    assert!(context.is_type_assignable_to(entries, optional).unwrap());
    assert!(!context.is_type_assignable_to(entries, required).unwrap());
    assert_eq!(indexes(&context, entries), actual);
    assert_eq!(counts(&context), warm);
}

#[test]
fn mapped_index_modifiers_preserve_source_readonly_and_explicit_undefined() {
    let parsed = parse_source_file(concat!(
        "interface Input { readonly [key: string]: number | undefined } ",
        "type Preserved = { [Key in keyof Input]+?: Input[Key] }; ",
        "type Mutable = { -readonly [Key in keyof Input]-?: Input[Key] }; ",
        "type Optional = { [key: number]: number | undefined }; ",
        "type Required = { [key: number]: number };",
    ));
    let mut context = context(&parsed, true, false);
    context.check_source_file(FILE).unwrap();
    assert!(context.diagnostics().is_empty());
    let optional = alias_type(&parsed, &context, "Optional");
    let required = alias_type(&parsed, &context, "Required");
    for (name, readonly) in [("Preserved", true), ("Mutable", false)] {
        let mapped = alias_type(&parsed, &context, name);
        assert!(context.is_type_assignable_to(mapped, optional).unwrap());
        assert!(!context.is_type_assignable_to(mapped, required).unwrap());
        let actual = indexes(&context, mapped);
        let [(key, _, actual_readonly)] = actual.as_slice() else {
            panic!("{name} must keep its source string index: {actual:?}")
        };
        assert_eq!(
            *key,
            context.store().intrinsic_bootstrap().unwrap().string_type
        );
        assert_eq!(*actual_readonly, readonly);
        let warm = counts(&context);
        assert!(context.is_type_assignable_to(mapped, optional).unwrap());
        assert!(!context.is_type_assignable_to(mapped, required).unwrap());
        assert_eq!(indexes(&context, mapped), actual);
        assert_eq!(counts(&context), warm);
    }
    let warm = counts(&context);
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(counts(&context), warm);
}

#[test]
fn explicit_optional_named_properties_add_undefined_to_void() {
    for (strict, exact) in [(false, false), (true, false), (true, true)] {
        let parsed = parse_source_file(concat!(
            "type Property = { [Key in 'value']?: void }; ",
            "type Expected = { value?: void }; ",
            "type Wrong = { value?: number };",
        ));
        let mut context = context(&parsed, strict, exact);
        context.check_source_file(FILE).unwrap();
        assert!(context.diagnostics().is_empty());
        let property = alias_type(&parsed, &context, "Property");
        let expected = alias_type(&parsed, &context, "Expected");
        let wrong = alias_type(&parsed, &context, "Wrong");
        assert!(context.is_type_assignable_to(property, expected).unwrap());
        assert!(!context.is_type_assignable_to(property, wrong).unwrap());
        let store = context.store();
        let TypeData::Mapped(mapped) = store.type_payload(property).unwrap().data() else {
            panic!("the optional property owner must retain its mapped type")
        };
        let members = mapped.object.structured.members.unwrap();
        let symbol = store
            .symbol_table(members)
            .unwrap()
            .get_source("value")
            .unwrap();
        let value = store
            .value_symbol_links(symbol)
            .unwrap()
            .resolved_type
            .unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        if strict {
            let TypeData::Union(union) = store.type_payload(value).unwrap().data() else {
                panic!("an explicit optional void template must include undefined")
            };
            assert_eq!(union.union.types.len(), 2);
            assert!(union.union.types.contains(&bootstrap.void_type));
            assert!(
                union
                    .union
                    .types
                    .contains(&bootstrap.undefined_or_missing_type)
            );
        } else {
            assert_eq!(value, bootstrap.void_type);
        }
        let warm = counts(&context);
        context.recheck_source_file(FILE).unwrap();
        assert!(context.is_type_assignable_to(property, expected).unwrap());
        assert!(!context.is_type_assignable_to(property, wrong).unwrap());
        assert_eq!(counts(&context), warm);
    }
}

#[test]
fn mapped_dictionary_values_support_repeated_public_relations() {
    let parsed = parse_source_file(concat!(
        "interface Wrapper<Value> { value: Value } ",
        "interface Dict { [key: string]: number } ",
        "type Cells<Model> = { [Key in keyof Model]: Wrapper<Model[Key]> }; ",
        "type Concrete = Cells<Dict>; ",
        "type Expected = { [key: string]: Wrapper<number> }; ",
        "type Wrong = { [key: string]: Wrapper<string> };",
    ));
    let mut context = context(&parsed, true, false);
    context.check_source_file(FILE).unwrap();
    assert!(context.diagnostics().is_empty());
    let concrete = alias_type(&parsed, &context, "Concrete");
    let expected = alias_type(&parsed, &context, "Expected");
    let wrong = alias_type(&parsed, &context, "Wrong");
    assert!(indexes(&context, concrete).is_empty());
    assert_eq!(context.is_type_assignable_to(concrete, expected), Ok(true));
    assert_eq!(context.is_type_assignable_to(concrete, wrong), Ok(false));
    let actual = indexes(&context, concrete);
    let [(key, value, readonly)] = actual.as_slice() else {
        panic!("the dictionary projection must publish one string index: {actual:?}")
    };
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(*key, bootstrap.string_type);
    assert!(!readonly);
    let TypeData::TypeReference(reference) = context.store().type_payload(*value).unwrap().data()
    else {
        panic!("the dictionary value must keep its Wrapper reference")
    };
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[bootstrap.number_type][..])
    );
    let warm = counts(&context);
    for _ in 0..2 {
        assert_eq!(context.is_type_assignable_to(concrete, expected), Ok(true));
        assert_eq!(context.is_type_assignable_to(concrete, wrong), Ok(false));
        assert_eq!(indexes(&context, concrete), actual);
        assert_eq!(counts(&context), warm);
    }
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(context.is_type_assignable_to(concrete, expected), Ok(true));
    assert_eq!(counts(&context), warm);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn generic_dictionary_relations_keep_published_indexes_and_lazy_properties() {
    for (declaration, has_property) in [
        ("interface Dict<Value> { [key: string]: Value }", false),
        (
            "interface Dict<Value> { [key: string]: Value; value: Value }",
            true,
        ),
        (
            "interface Base<Value> { [key: string]: Value } interface Dict<Value> extends Base<Value> { value: Value }",
            true,
        ),
    ] {
        let property = if has_property { "value: number;" } else { "" };
        let parsed = parse_source_file(&format!(
            "{declaration} type Concrete = Dict<number>; \
             interface Expected {{ [key: string]: number; {property} }} \
             type Wrong = {{ [key: string]: string }};"
        ));
        let mut context = context(&parsed, true, false);
        context.check_source_file(FILE).unwrap();
        assert!(context.diagnostics().is_empty());
        let concrete = alias_type(&parsed, &context, "Concrete");
        let expected_owner = context
            .store()
            .symbol_table(context.store().intrinsic_bootstrap().unwrap().globals)
            .unwrap()
            .get_source("Expected")
            .unwrap();
        let expected = context
            .store()
            .declared_type_links(expected_owner)
            .unwrap()
            .declared_type
            .unwrap();
        let wrong = alias_type(&parsed, &context, "Wrong");
        assert_eq!(
            context.is_type_assignable_to(concrete, expected),
            Ok(true),
            "{declaration}"
        );
        assert_eq!(
            context.is_type_assignable_to(concrete, wrong),
            Ok(false),
            "{declaration}"
        );
        let store = context.store();
        let record = store.type_payload(concrete).unwrap();
        assert!(
            record
                .object_flags()
                .contains(ObjectFlags::MEMBERS_RESOLVED)
        );
        let TypeData::TypeReference(reference) = record.data() else {
            panic!("the dictionary must keep its generic reference")
        };
        let structured = &reference.object.structured;
        let [index] = structured.index_infos.as_deref().unwrap() else {
            panic!("the generic dictionary must retain one published index")
        };
        let index = *index;
        let info = store.index_info(index).unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        assert_eq!(info.key_type(), bootstrap.string_type);
        assert_eq!(info.value_type(), bootstrap.number_type);
        assert!(!info.is_readonly());
        if has_property {
            let members = store.symbol_table(structured.members.unwrap()).unwrap();
            assert_eq!(members.len(), 1);
            let property = members.get_source("value").unwrap();
            assert_eq!(
                store.value_symbol_links(property).unwrap().resolved_type,
                Some(bootstrap.number_type)
            );
        } else {
            assert!(structured.members.is_none());
            assert!(structured.properties.is_none());
        }
        let warm = counts(&context);
        for _ in 0..2 {
            assert_eq!(context.is_type_assignable_to(concrete, expected), Ok(true));
            assert_eq!(context.is_type_assignable_to(concrete, wrong), Ok(false));
            assert_eq!(counts(&context), warm);
            let TypeData::TypeReference(reference) =
                context.store().type_payload(concrete).unwrap().data()
            else {
                panic!("the warm dictionary must keep its generic reference")
            };
            assert_eq!(
                reference.object.structured.index_infos.as_deref(),
                Some(&[index][..])
            );
        }
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(context.is_type_assignable_to(concrete, expected), Ok(true));
        assert_eq!(context.is_type_assignable_to(concrete, wrong), Ok(false));
        assert_eq!(counts(&context), warm);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn optional_mapped_templates_keep_chained_utility_properties() {
    let parsed = parse_source_file(concat!(
        "interface Shape { value: number } ",
        "type ReadonlyCopy<Model> = { readonly [Key in keyof Model]: Model[Key] }; ",
        "type Soft<Model> = { [Key in keyof Model]?: Model[Key] }; ",
        "type View = ReadonlyCopy<Shape>; ",
        "type Concrete = Soft<View>; ",
        "type Expected = { readonly value?: number }; ",
        "type Wrong = { readonly value?: string };",
    ));
    for (strict, exact) in [(false, false), (true, false), (true, true)] {
        let mut context = context(&parsed, strict, exact);
        context.check_source_file(FILE).unwrap();
        assert!(context.diagnostics().is_empty());
        let concrete = alias_type(&parsed, &context, "Concrete");
        let expected = alias_type(&parsed, &context, "Expected");
        let wrong = alias_type(&parsed, &context, "Wrong");
        assert_eq!(context.is_type_assignable_to(concrete, expected), Ok(true));
        assert_eq!(context.is_type_assignable_to(concrete, wrong), Ok(false));
        let store = context.store();
        let TypeData::Mapped(mapped) = store.type_payload(concrete).unwrap().data() else {
            panic!("the chained utility must keep its mapped type")
        };
        let members = mapped.object.structured.members.unwrap();
        let property = store
            .symbol_table(members)
            .unwrap()
            .get_source("value")
            .unwrap();
        let value = store
            .value_symbol_links(property)
            .unwrap()
            .resolved_type
            .unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        if strict {
            let TypeData::Union(union) = store.type_payload(value).unwrap().data() else {
                panic!("the outer optional mapping must keep its sentinel")
            };
            assert_eq!(union.union.types.len(), 2);
            assert!(union.union.types.contains(&bootstrap.number_type));
            assert!(
                union
                    .union
                    .types
                    .contains(&bootstrap.undefined_or_missing_type)
            );
        } else {
            assert_eq!(value, bootstrap.number_type);
        }
        let warm = counts(&context);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(context.is_type_assignable_to(concrete, expected), Ok(true));
        assert_eq!(context.is_type_assignable_to(concrete, wrong), Ok(false));
        assert_eq!(counts(&context), warm);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn deep_mapped_templates_stay_lazy_before_value_demand() {
    let template = format!("{}Model[Key]{}", "Wrapper<".repeat(101), ">".repeat(101));
    for tail in [
        "",
        "declare const source: Result; const target: { value: unknown } = source;",
    ] {
        let parsed = parse_source_file(&format!(
            "interface Wrapper<Value> {{ value: Value }} \
             interface Shape {{ value: number }} \
             type Deep<Model> = {{ [Key in keyof Model]: {template} }}; \
             type Result = Deep<Shape>; {tail}"
        ));
        let mut context = context(&parsed, true, false);
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let original = alias_type(&parsed, &context, "Deep");
        let result = alias_type(&parsed, &context, "Result");
        let store = context.store();
        let TypeData::Mapped(original_type) = store.type_payload(original).unwrap().data() else {
            panic!("the declaration must keep its mapped type")
        };
        let TypeData::Mapped(result_type) = store.type_payload(result).unwrap().data() else {
            panic!("the alias must keep a lazy mapped shell")
        };
        assert_eq!(result_type.object.target, Some(original));
        assert_eq!(result_type.template_type, original_type.template_type);
        for property in result_type
            .object
            .structured
            .properties
            .as_deref()
            .unwrap_or_default()
        {
            assert!(
                store
                    .value_symbol_links(*property)
                    .unwrap()
                    .resolved_type
                    .is_none()
            );
        }
        let warm = counts(&context);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(counts(&context), warm);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn lazy_mapped_properties_use_the_source_relation_recovery_policy() {
    for homomorphic in [false, true] {
        let value = if homomorphic { "Model[Key]" } else { "Key" };
        let template = format!("{}{value}{}", "Wrapper<".repeat(101), ">".repeat(101));
        let declaration = if homomorphic {
            format!(
                "interface Shape {{ value: number }} \
                 type Deep<Model> = {{ [Key in keyof Model]: {template} }}; \
                 type Mapped = Deep<Shape>;"
            )
        } else {
            format!("type Mapped = {{ [Key in 'value']: {template} }};")
        };
        let parsed = parse_source_file(&format!(
            "interface Wrapper<Value> {{ value: Value }} {declaration} \
             declare const source: Mapped; \
             const target: {{ value: Wrapper<unknown> }} = source;"
        ));
        let target_name = assignment_target_name(&parsed);
        let mut context = context(&parsed, true, false);
        context.check_source_file(FILE).unwrap();
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(diagnostics[0].diagnostic.code(), 2589);
        assert_eq!(diagnostics[0].node, Some(target_name));
        let mapped = alias_type(&parsed, &context, "Mapped");
        let store = context.store();
        let TypeData::Mapped(mapped_record) = store.type_payload(mapped).unwrap().data() else {
            panic!("the recovered property owner must retain its mapped type")
        };
        let members = mapped_record.object.structured.members.unwrap();
        let property = store
            .symbol_table(members)
            .unwrap()
            .get_source("value")
            .unwrap();
        let result = store
            .value_symbol_links(property)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_recovered_wrapper_graph(&context, result);
        let warm = counts(&context);
        let diagnostics = context.diagnostics().clone();
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(counts(&context), warm);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

#[test]
fn optional_mapped_templates_use_the_go_instantiation_depth_boundary() {
    for wrappers in [98, 99] {
        for optional in [false, true] {
            let modifier = if optional { "?" } else { "" };
            let template = format!("{}Key{}", "Wrapper<".repeat(wrappers), ">".repeat(wrappers));
            let parsed = parse_source_file(&format!(
                "interface Wrapper<Value> {{ value: Value }} \
                 type Mapped = {{ [Key in 'value']{modifier}: {template} }}; \
                 declare const source: Mapped; \
                 const target: {{ value?: Wrapper<unknown> }} = source;"
            ));
            let target_name = assignment_target_name(&parsed);
            let mut context = context(&parsed, true, false);
            context.check_source_file(FILE).unwrap();
            let diagnostics = context.diagnostics().as_slice();
            if optional && wrappers == 99 {
                assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
                assert_eq!(diagnostics[0].diagnostic.code(), 2589);
                assert_eq!(diagnostics[0].node, Some(target_name));
            } else {
                assert!(
                    diagnostics.is_empty(),
                    "{wrappers}, optional={optional}: {diagnostics:?}"
                );
            }
            let mapped = alias_type(&parsed, &context, "Mapped");
            let store = context.store();
            let TypeData::Mapped(mapped) = store.type_payload(mapped).unwrap().data() else {
                panic!("the depth fixture must keep its mapped type")
            };
            let members = mapped.object.structured.members.unwrap();
            let property = store
                .symbol_table(members)
                .unwrap()
                .get_source("value")
                .unwrap();
            let value = store
                .value_symbol_links(property)
                .unwrap()
                .resolved_type
                .unwrap();
            let mut leaf = if optional {
                let TypeData::Union(union) = store.type_payload(value).unwrap().data() else {
                    panic!("optional mapped values must keep their sentinel")
                };
                let sentinel = store
                    .intrinsic_bootstrap()
                    .unwrap()
                    .undefined_or_missing_type;
                assert_eq!(union.union.types.len(), 2);
                assert!(union.union.types.contains(&sentinel));
                *union
                    .union
                    .types
                    .iter()
                    .find(|type_| **type_ != sentinel)
                    .unwrap()
            } else {
                value
            };
            let mut depth = 0;
            while let TypeData::TypeReference(reference) = store.type_payload(leaf).unwrap().data()
            {
                let [argument] = reference.resolved_type_arguments.as_deref().unwrap() else {
                    panic!("each Wrapper must keep one argument")
                };
                depth += 1;
                leaf = *argument;
            }
            assert_eq!(depth, wrappers);
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            assert_eq!(
                leaf,
                if optional && wrappers == 99 {
                    bootstrap.error_type
                } else {
                    bootstrap.cached_string_literal_type("value").unwrap()
                }
            );
            let warm = counts(&context);
            let diagnostics = context.diagnostics().clone();
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(counts(&context), warm);
            assert_eq!(context.diagnostics(), &diagnostics);
        }
    }
}

#[test]
fn lazy_mapped_indexes_use_the_source_relation_recovery_policy() {
    let template = format!("{}Model[Key]{}", "Wrapper<".repeat(101), ">".repeat(101));
    let parsed = parse_source_file(&format!(
        "interface Wrapper<Value> {{ value: Value }} \
         type Deep<Model> = {{ [Key in keyof Model]: {template} }}; \
         type Mapped = Deep<any>; \
         declare const source: Mapped; \
         const target: {{ [key: string]: Wrapper<unknown> }} = source;"
    ));
    let target_name = assignment_target_name(&parsed);
    let mut context = context(&parsed, true, false);
    context.check_source_file(FILE).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0].diagnostic.code(), 2589);
    assert_eq!(diagnostics[0].node, Some(target_name));
    let mapped = alias_type(&parsed, &context, "Mapped");
    let actual = indexes(&context, mapped);
    let [(key, value, readonly)] = actual.as_slice() else {
        panic!("the recovered mapped any source must have one index: {actual:?}")
    };
    assert_eq!(
        *key,
        context.store().intrinsic_bootstrap().unwrap().string_type
    );
    assert!(!readonly);
    assert_recovered_wrapper_graph(&context, *value);
    let warm = counts(&context);
    let diagnostics = context.diagnostics().clone();
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(counts(&context), warm);
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(indexes(&context, mapped), actual);
}

fn assignment_target_name(parsed: &ParseResult) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            variable.initializer?;
            Some(NodeRef::new(parsed.arena.id(), FILE, variable.name))
        })
        .unwrap()
}

fn assert_recovered_wrapper_graph(context: &CanonicalCheckerContext<'_>, mut result: TypeId) {
    let store = context.store();
    let mut depth = 0;
    while let TypeData::TypeReference(reference) = store.type_payload(result).unwrap().data() {
        let [argument] = reference.resolved_type_arguments.as_deref().unwrap() else {
            panic!("each recovered Wrapper keeps one argument")
        };
        depth += 1;
        result = *argument;
    }
    assert_eq!(depth, 100);
    assert_eq!(result, store.intrinsic_bootstrap().unwrap().error_type);
}
