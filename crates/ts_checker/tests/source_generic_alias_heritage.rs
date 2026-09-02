use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
    type_records::StructuredTypeData,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_220);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic-alias-heritage.ts\""),
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
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn declaration(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name = match &record.data {
                NodeData::TypeAliasDeclaration(data) => data.name,
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::VariableDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap_or_else(|| panic!("missing declaration {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn declared_type(context: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    context
        .store()
        .declared_type_links(owner)
        .and_then(|links| links.declared_type)
        .unwrap_or_else(|| panic!("missing declared type for {owner:?}"))
}

fn formals(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    owner: NodeRef,
) -> Vec<TypeId> {
    let parameters = match &parsed.arena.get(owner.node).unwrap().data {
        NodeData::TypeAliasDeclaration(data) => data.type_parameters.as_ref(),
        NodeData::InterfaceDeclaration(data) => data.type_parameters.as_ref(),
        _ => panic!("type parameters must belong to their source declaration"),
    }
    .unwrap();
    parameters
        .nodes
        .iter()
        .map(|node| {
            let owner = symbol(context, NodeRef::new(parsed.arena.id(), FILE, *node));
            let type_ = declared_type(context, owner);
            let record = context.store().type_payload(type_).unwrap();
            assert!(matches!(record.data(), TypeData::TypeParameter(_)));
            assert_eq!(record.symbol(), Some(owner));
            type_
        })
        .collect()
}

fn node_text(parsed: &ParseResult, node: NodeRef) -> &str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &parsed.arena.source_text().unwrap()
        [usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn node_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing checked type for {node:?}"))
}

fn access_type(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    expression: &str,
) -> TypeId {
    let node = parsed
        .arena
        .iter()
        .filter(|(_, record)| record.kind == SyntaxKind::PropertyAccessExpression)
        .map(|(node, _)| NodeRef::new(parsed.arena.id(), FILE, node))
        .find(|node| node_text(parsed, *node) == expression)
        .unwrap_or_else(|| panic!("missing property read {expression}"));
    node_type(context, node)
}

fn variable_type(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
) -> TypeId {
    let owner = declaration(parsed, name);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(owner.node).unwrap().data else {
        panic!("the variable must retain its written annotation");
    };
    node_type(
        context,
        NodeRef::new(owner.arena, owner.file, data.type_.unwrap()),
    )
}

fn structured<'a>(
    context: &'a CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'a StructuredTypeData {
    match context.store().type_payload(type_).unwrap().data() {
        TypeData::Interface(data) => &data.reference.object.structured,
        TypeData::TypeReference(data) => &data.object.structured,
        TypeData::Mapped(data) => &data.object.structured,
        TypeData::Object(data) => &data.structured,
        TypeData::Intersection(data) => &data.intersection.structured,
        _ => panic!("expected a resolved object or intersection"),
    }
}

fn property(context: &CanonicalCheckerContext<'_>, type_: TypeId, name: &str) -> SemanticSymbolId {
    context
        .store()
        .symbol_table(structured(context, type_).members.unwrap())
        .unwrap()
        .get_source(name)
        .unwrap_or_else(|| panic!("missing inherited property {name}"))
}

fn assert_optional(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    name: &str,
    optional: bool,
) {
    let property = context
        .store()
        .symbol(property(context, type_, name))
        .unwrap();
    assert_eq!(
        property.flags().contains(SymbolFlags::OPTIONAL),
        optional,
        "{name}"
    );
}

fn assert_optional_read(context: &CanonicalCheckerContext<'_>, read: TypeId, value: TypeId) {
    let TypeData::Union(data) = context.store().type_payload(read).unwrap().data() else {
        panic!("an optional property read must retain undefined");
    };
    let undefined = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .undefined_type;
    assert_eq!(data.union.types.len(), 2);
    assert!(data.union.types.contains(&value));
    assert!(data.union.types.contains(&undefined));
}

fn assert_replay(context: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) {
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        let nodes = parsed
            .arena
            .iter()
            .map(|(node, _)| NodeRef::new(parsed.arena.id(), FILE, node))
            .collect::<Vec<_>>();
        (
            [
                store.type_len(),
                store.type_alias_len(),
                store.symbol_len(),
                store.mapper_len(),
                store.signature_len(),
                store.index_info_len(),
                store.symbol_store().symbol_table_len(),
            ],
            nodes
                .iter()
                .map(|node| store.type_node_links(*node).cloned())
                .collect::<Vec<_>>(),
            nodes
                .iter()
                .filter_map(|node| context.file(FILE).unwrap().1.symbol(*node))
                .map(|owner| {
                    (
                        owner,
                        store.declared_type_links(owner).cloned(),
                        store.type_alias_links(owner).cloned(),
                        store.value_symbol_links(owner).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            store.relation_state_snapshot(),
            context.diagnostics().clone(),
        )
    };
    let cold = snapshot(context);
    context.check_source_file(FILE).unwrap();
    assert_eq!(snapshot(context), cold);
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(snapshot(context), cold);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // The fixtures check source formals, mapped identity and reads.
fn generic_intersection_alias_bases_preserve_source_formals_and_member_types() {
    let parsed = parse_source_file(concat!(
        "type RequireKey<T, K extends keyof T> = T & { [P in K]-?: T[P] };\n",
        "interface Options<T> { queryKey?: string; payload: T; note?: number }\n",
        "interface Cached<T> extends RequireKey<Options<T>, 'queryKey'> { version: number }\n",
        "declare const numeric: Cached<number>;\n",
        "declare const textual: Cached<string>;\n",
        "const key: string = numeric.queryKey;\n",
        "const payload: number = numeric.payload;\n",
        "const note: number | undefined = numeric.note;\n",
        "const version: number = numeric.version;\n",
        "const textPayload: string = textual.payload;\n",
        "const valid: Cached<number> = { queryKey: 'key', payload: 1, version: 1 };\n",
        "type WithRequired<T, K extends keyof T> = T & { [P in K]: {} };\n",
        "interface RequiredOptions<T> extends WithRequired<Options<T>, 'queryKey'> { version: number }\n",
        "declare const query: RequiredOptions<number>;\n",
        "const queryKey: string = query.queryKey;\n",
        "const queryPayload: number = query.payload;\n",
        "const queryValid: RequiredOptions<number> = { queryKey: 'key', payload: 1, version: 1 };\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );

    let alias = declaration(&parsed, "RequireKey");
    let alias_owner = symbol(&context, alias);
    let alias_formals = formals(&context, &parsed, alias);
    assert_eq!(alias_formals.len(), 2);
    let alias_links = context.store().type_alias_links(alias_owner).unwrap();
    assert_eq!(
        alias_links.type_parameters.as_deref(),
        Some(alias_formals.as_slice())
    );
    let TypeData::Intersection(original) = context
        .store()
        .type_payload(alias_links.declared_type.unwrap())
        .unwrap()
        .data()
    else {
        panic!("the generic alias must retain its source intersection");
    };
    assert!(original.intersection.types.contains(&alias_formals[0]));
    let original_mapped = *original
        .intersection
        .types
        .iter()
        .find(|type_| {
            matches!(
                context.store().type_payload(**type_).unwrap().data(),
                TypeData::Mapped(_)
            )
        })
        .unwrap();
    let TypeData::Mapped(original_mapped_data) = context
        .store()
        .type_payload(original_mapped)
        .unwrap()
        .data()
    else {
        unreachable!();
    };
    let mapped_declaration = original_mapped_data.declaration.unwrap();
    let NodeData::MappedTypeNode(mapped_source) =
        &parsed.arena.get(mapped_declaration.node).unwrap().data
    else {
        panic!("the mapped type must keep its source declaration");
    };
    let key_owner = symbol(
        &context,
        NodeRef::new(alias.arena, FILE, mapped_source.type_parameter),
    );
    assert_eq!(
        context
            .store()
            .type_payload(original_mapped_data.type_parameter.unwrap())
            .unwrap()
            .symbol(),
        Some(key_owner)
    );

    let cached = declaration(&parsed, "Cached");
    let cached_formals = formals(&context, &parsed, cached);
    let options = declaration(&parsed, "Options");
    let options_formals = formals(&context, &parsed, options);
    assert_ne!(cached_formals, options_formals);
    assert!(!alias_formals.contains(&cached_formals[0]));
    let cached_type = declared_type(&context, symbol(&context, cached));
    let TypeData::Interface(cached_data) =
        context.store().type_payload(cached_type).unwrap().data()
    else {
        panic!("Cached must retain its interface target");
    };
    assert!(cached_data.base_types_resolved);
    let [base] = cached_data.resolved_base_types.as_deref().unwrap() else {
        panic!("Cached must have its one written intersection base");
    };
    let base_record = context.store().type_payload(*base).unwrap();
    let identity = context
        .store()
        .type_alias(base_record.alias().unwrap())
        .unwrap();
    assert_eq!(identity.symbol(), Some(alias_owner));
    let arguments = identity.type_arguments().unwrap();
    assert_eq!(arguments.len(), 2);
    let TypeData::TypeReference(options_instance) =
        context.store().type_payload(arguments[0]).unwrap().data()
    else {
        panic!("the base must use Options<Cached.T>");
    };
    assert_eq!(
        options_instance.object.target,
        Some(declared_type(&context, symbol(&context, options)))
    );
    assert_eq!(
        options_instance.resolved_type_arguments.as_deref(),
        Some(cached_formals.as_slice())
    );
    let TypeData::Intersection(base_data) = base_record.data() else {
        panic!("the instantiated base must remain an intersection");
    };
    assert!(base_data.intersection.types.contains(&arguments[0]));
    let mapped = base_data
        .intersection
        .types
        .iter()
        .find_map(|type_| {
            let TypeData::Mapped(data) = context.store().type_payload(*type_).unwrap().data()
            else {
                return None;
            };
            Some(data)
        })
        .unwrap();
    assert_eq!(mapped.declaration, Some(mapped_declaration));
    assert_eq!(mapped.object.target, Some(original_mapped));
    assert!(mapped.object.mapper.is_some());

    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let string = bootstrap.string_type;
    for expression in ["numeric.payload", "numeric.version", "query.payload"] {
        assert_eq!(access_type(&context, &parsed, expression), number);
    }
    for expression in ["numeric.queryKey", "textual.payload", "query.queryKey"] {
        assert_eq!(access_type(&context, &parsed, expression), string);
    }
    assert_optional_read(
        &context,
        access_type(&context, &parsed, "numeric.note"),
        number,
    );
    let numeric = variable_type(&context, &parsed, "numeric");
    let textual = variable_type(&context, &parsed, "textual");
    assert_ne!(numeric, textual);
    assert_optional(&context, numeric, "queryKey", false);
    assert_optional(&context, numeric, "payload", false);
    assert_optional(&context, numeric, "note", true);
    assert_optional(&context, textual, "payload", false);
    assert_optional(
        &context,
        variable_type(&context, &parsed, "query"),
        "queryKey",
        false,
    );
    assert_replay(&mut context, &parsed);
    assert_constrained_generic_key_base();
}

#[allow(clippy::too_many_lines)] // One fixture checks generic intersection and concrete read identities.
fn assert_constrained_generic_key_base() {
    let parsed = parse_source_file(concat!(
        "interface Key { tag: string }\n",
        "type WithRequired<T, P extends keyof T> = T & { [Q in P]: {} };\n",
        "interface Options<K extends Key> { queryKey?: K }\n",
        "interface Required<K extends Key> extends WithRequired<Options<K>, 'queryKey'> {}\n",
        "declare const query: Required<Key>;\n",
        "const key: Key = query.queryKey;\n",
        "const tag: string = query.queryKey.tag;\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let key = declared_type(&context, symbol(&context, declaration(&parsed, "Key")));
    let required = declaration(&parsed, "Required");
    let required_formals = formals(&context, &parsed, required);
    let [parameter] = required_formals.as_slice() else {
        panic!("Required must retain its one source key parameter");
    };
    let TypeData::TypeParameter(parameter_data) =
        context.store().type_payload(*parameter).unwrap().data()
    else {
        unreachable!();
    };
    assert_eq!(parameter_data.constraint, Some(key));
    assert_ne!(*parameter, key);
    let required_type = declared_type(&context, symbol(&context, required));
    let TypeData::Interface(required_data) =
        context.store().type_payload(required_type).unwrap().data()
    else {
        panic!("Required must retain its generic interface target");
    };
    let [base] = required_data.resolved_base_types.as_deref().unwrap() else {
        panic!("Required must retain its one written alias base");
    };
    let base_record = context.store().type_payload(*base).unwrap();
    let TypeData::Intersection(intersection) = base_record.data() else {
        panic!("the generic alias base must remain an intersection");
    };
    let identity = context
        .store()
        .type_alias(base_record.alias().unwrap())
        .unwrap();
    assert_eq!(
        identity.symbol(),
        Some(symbol(&context, declaration(&parsed, "WithRequired")))
    );
    let [options, _] = identity.type_arguments().unwrap() else {
        panic!("the base must retain both alias arguments");
    };
    assert!(intersection.intersection.types.contains(options));
    let TypeData::TypeReference(options_data) =
        context.store().type_payload(*options).unwrap().data()
    else {
        panic!("the base must use Options<Required.K>");
    };
    assert_eq!(
        options_data.object.target,
        Some(declared_type(
            &context,
            symbol(&context, declaration(&parsed, "Options"))
        ))
    );
    assert_eq!(
        options_data.resolved_type_arguments.as_deref(),
        Some(required_formals.as_slice())
    );
    assert_optional(&context, *options, "queryKey", true);
    assert_optional(&context, *base, "queryKey", false);
    let key_type = context
        .store()
        .value_symbol_links(property(&context, *base, "queryKey"))
        .and_then(|links| links.resolved_type)
        .unwrap();
    let key_record = context.store().type_payload(key_type).unwrap();
    let TypeData::Intersection(key_intersection) = key_record.data() else {
        panic!("a named object constraint must retain the key parameter intersected with {{}}");
    };
    let empty_type = intersection
        .intersection
        .types
        .iter()
        .find_map(
            |part| match context.store().type_payload(*part).unwrap().data() {
                TypeData::Mapped(mapped) => mapped.template_type,
                _ => None,
            },
        )
        .unwrap();
    assert_eq!(
        key_intersection.intersection.types.as_slice(),
        &[*parameter, empty_type]
    );
    assert!(key_record.alias().is_none());
    assert_eq!(access_type(&context, &parsed, "query.queryKey"), key);
    assert_eq!(
        access_type(&context, &parsed, "query.queryKey.tag"),
        context.store().intrinsic_bootstrap().unwrap().string_type
    );
    assert_optional(
        &context,
        variable_type(&context, &parsed, "query"),
        "queryKey",
        false,
    );
    assert_replay(&mut context, &parsed);
}

#[test]
fn generic_omit_alias_bases_preserve_optional_members_and_allow_replacement_fields() {
    let parsed = parse_source_file(concat!(
        "type ExcludeKeys<T, U> = T extends U ? never : T;\n",
        "type SelectFields<T, K extends keyof T> = { [P in K]: T[P] };\n",
        "type RemoveKeys<T, K extends keyof any> = SelectFields<T, ExcludeKeys<keyof T, K>>;\n",
        "interface WireRequest { method?: string; headers?: number; retries: number }\n",
        "interface ProxyRequest extends RemoveKeys<WireRequest, 'headers'> { headers: string }\n",
        "declare const proxy: ProxyRequest;\n",
        "const method: string | undefined = proxy.method;\n",
        "const headers: string = proxy.headers;\n",
        "const retries: number = proxy.retries;\n",
        "const valid: ProxyRequest = { headers: 'ready', retries: 1 };\n",
        "type Record<K extends keyof any, T> = { [P in K]: T };\n",
        "interface Dictionary extends Record<string, any> { own: number }\n",
        "declare const dictionary: Dictionary;\n",
        "const own: number = dictionary.own;\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let proxy = declared_type(
        &context,
        symbol(&context, declaration(&parsed, "ProxyRequest")),
    );
    let TypeData::Interface(data) = context.store().type_payload(proxy).unwrap().data() else {
        panic!("ProxyRequest must retain its interface target");
    };
    let [base] = data.resolved_base_types.as_deref().unwrap() else {
        panic!("ProxyRequest must have its written omit-style base");
    };
    let TypeData::Mapped(mapped) = context.store().type_payload(*base).unwrap().data() else {
        panic!("the omit-style base must use its canonical mapped type");
    };
    let select = declaration(&parsed, "SelectFields");
    let NodeData::TypeAliasDeclaration(select) = &parsed.arena.get(select.node).unwrap().data
    else {
        unreachable!();
    };
    assert_eq!(
        mapped.declaration,
        Some(NodeRef::new(parsed.arena.id(), FILE, select.type_))
    );
    let base_members = context
        .store()
        .symbol_table(mapped.object.structured.members.unwrap())
        .unwrap();
    assert!(base_members.get_source("headers").is_none());
    assert!(base_members.get_source("method").is_some());
    assert!(base_members.get_source("retries").is_some());
    assert_optional(&context, *base, "method", true);
    assert_optional(&context, proxy, "method", true);
    assert_optional(&context, proxy, "headers", false);
    assert_optional(&context, proxy, "retries", false);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let string = bootstrap.string_type;
    let number = bootstrap.number_type;
    assert_eq!(access_type(&context, &parsed, "proxy.headers"), string);
    assert_eq!(access_type(&context, &parsed, "proxy.retries"), number);
    assert_eq!(access_type(&context, &parsed, "dictionary.own"), number);
    assert_optional_read(
        &context,
        access_type(&context, &parsed, "proxy.method"),
        string,
    );
    assert_replay(&mut context, &parsed);
}

#[test]
fn generic_alias_bases_report_native_errors_for_open_keys_unions_and_incompatible_properties() {
    let cases = [
        (
            "type Open<K extends string> = { [P in K]: number };\ninterface Invalid<K extends string> extends Open<K> {}\n",
            2312,
            "Open<K>",
            "An interface can only extend an object type or intersection of object types with statically known members.",
        ),
        (
            "interface Left<T> { value: T }\ninterface Right<T> { other: T }\ntype Choice<T> = Left<T> | Right<T>;\ninterface Invalid extends Choice<number> {}\n",
            2312,
            "Choice<number>",
            "An interface can only extend an object type or intersection of object types with statically known members.",
        ),
        (
            "type Cell<T> = { value: T };\ninterface Invalid extends Cell<number> { value: string }\ndeclare const invalid: Invalid;\nconst value: string = invalid.value;\n",
            2430,
            "Invalid",
            "Interface 'Invalid' incorrectly extends interface 'Cell<number>'.\n  Types of property 'value' are incompatible.\n    Type 'string' is not assignable to type 'number'.",
        ),
    ];
    for (source, code, anchor, message) in cases {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed);
        context.check_source_file(FILE).unwrap_or_else(|error| {
            panic!("the invalid base must produce TS{code}, not a checker error: {error:?}")
        });
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!(
                "expected one native heritage diagnostic: {:?}",
                context.diagnostics()
            );
        };
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert_eq!(node_text(&parsed, diagnostic.node.unwrap()), anchor);
        assert!(diagnostic.related_information.is_empty());
        if code == 2430 {
            let string = context.store().intrinsic_bootstrap().unwrap().string_type;
            assert_eq!(access_type(&context, &parsed, "invalid.value"), string);
        }
        assert_replay(&mut context, &parsed);
    }
}
