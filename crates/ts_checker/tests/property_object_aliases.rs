use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags, canonical_has_syntactic_modifier,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
    type_records::{ObjectTypeData, TypeCacheState},
    types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const DECLARATIONS: FileId = FileId::new(45_280);
const FIRST_USE: FileId = FileId::new(45_281);
const SECOND_USE: FileId = FileId::new(45_282);

fn context<'arena>(
    sources: &[(FileId, &'arena ParseResult)],
    options: CanonicalCheckerOptions,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for (index, (file, parsed)) in sources.iter().enumerate() {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                *file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(format!("\"/project/property-object-aliases-{index}.ts\"")),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
    }
    for (file, parsed) in sources {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, *file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        sources
            .iter()
            .map(|(file, parsed)| (*file, &parsed.arena))
            .collect(),
        options,
    )
    .unwrap()
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize, usize, usize) {
    let store = context.store();
    (
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.type_alias_len(),
        store.symbol_store().symbol_table_len(),
    )
}

fn declaration(parsed: &ParseResult, file: FileId, kind: SyntaxKind, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name_node = match &record.data {
                NodeData::TypeAliasDeclaration(data) => data.name,
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::FunctionDeclaration(data) => data.name?,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {name}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let bound = context.file(declaration.file).unwrap().1;
    context
        .store()
        .get_merged_symbol(bound.symbol(declaration).unwrap())
        .unwrap()
}

struct Alias {
    declaration: NodeRef,
    literal: NodeRef,
    parameters: Vec<NodeRef>,
}

fn alias(parsed: &ParseResult, name: &str) -> Alias {
    let declaration = declaration(parsed, DECLARATIONS, SyntaxKind::TypeAliasDeclaration, name);
    let NodeData::TypeAliasDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let mut literal = data.type_;
    while let NodeData::ParenthesizedTypeNode(data) = &parsed.arena.get(literal).unwrap().data {
        literal = data.type_;
    }
    assert!(matches!(
        parsed.arena.get(literal).unwrap().data,
        NodeData::TypeLiteralNode(_)
    ));
    Alias {
        declaration,
        literal: NodeRef::new(parsed.arena.id(), DECLARATIONS, literal),
        parameters: data
            .type_parameters
            .as_ref()
            .unwrap()
            .nodes
            .iter()
            .map(|node| NodeRef::new(parsed.arena.id(), DECLARATIONS, *node))
            .collect(),
    }
}

#[derive(Clone, Copy)]
struct Property {
    declaration: NodeRef,
    annotation: NodeRef,
    readonly: bool,
}

fn source_property(parsed: &ParseResult, alias: &Alias, name: &str) -> Property {
    let NodeData::TypeLiteralNode(literal) = &parsed.arena.get(alias.literal.node).unwrap().data
    else {
        unreachable!()
    };
    literal
        .members
        .nodes
        .iter()
        .find_map(|node| {
            let (name_node, annotation) = match &parsed.arena.get(*node)?.data {
                NodeData::PropertyDeclaration(property) => (property.name, property.type_?),
                NodeData::PropertySignatureDeclaration(property) => (property.name, property.type_),
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(Property {
                declaration: NodeRef::new(parsed.arena.id(), DECLARATIONS, *node),
                annotation: NodeRef::new(parsed.arena.id(), DECLARATIONS, annotation),
                readonly: canonical_has_syntactic_modifier(
                    &parsed.arena,
                    *node,
                    SyntaxKind::ReadonlyKeyword,
                ),
            })
        })
        .unwrap_or_else(|| panic!("missing source property {name}"))
}

struct Variable {
    name: NodeRef,
    annotation: NodeRef,
    initializer: Option<NodeRef>,
}

fn variable(parsed: &ParseResult, file: FileId, name: &str) -> Variable {
    let declaration = declaration(parsed, file, SyntaxKind::VariableDeclaration, name);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    Variable {
        name: NodeRef::new(parsed.arena.id(), file, data.name),
        annotation: NodeRef::new(parsed.arena.id(), file, data.type_.unwrap()),
        initializer: data
            .initializer
            .map(|node| NodeRef::new(parsed.arena.id(), file, node)),
    }
}

fn object<'context>(
    context: &'context CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'context ObjectTypeData {
    let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data() else {
        panic!("an object alias must retain an anonymous object, not an interface reference")
    };
    object
}

fn value_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> Option<TypeId> {
    context
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
}

fn node_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> Option<TypeId> {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
}

fn member(context: &CanonicalCheckerContext<'_>, type_: TypeId, name: &str) -> SemanticSymbolId {
    let members = object(context, type_).structured.members.unwrap();
    context
        .store()
        .symbol_table(members)
        .unwrap()
        .get_source(name)
        .unwrap_or_else(|| panic!("missing instantiated property {name}"))
}

fn assert_cold_property(context: &CanonicalCheckerContext<'_>, property: Property) {
    assert_eq!(
        value_type(context, symbol(context, property.declaration)),
        None
    );
    assert_eq!(node_type(context, property.annotation), None);
}

fn assert_unchecked(context: &CanonicalCheckerContext<'_>, file: FileId) {
    assert!(
        context
            .source_file(file)
            .and_then(|source| context.store().source_file_links(source))
            .is_none_or(|links| !links.type_checked)
    );
}

fn assert_instance(
    context: &CanonicalCheckerContext<'_>,
    alias: &Alias,
    instance: TypeId,
    arguments: &[TypeId],
) -> TypeId {
    let store = context.store();
    let alias_symbol = symbol(context, alias.declaration);
    let source_symbol = symbol(context, alias.literal);
    assert_ne!(alias_symbol, source_symbol);
    let links = store.type_alias_links(alias_symbol).unwrap();
    let target = links.declared_type.unwrap();
    let parameters = links.type_parameters.as_deref().unwrap();
    assert_eq!(parameters.len(), arguments.len());
    assert_eq!(parameters.len(), alias.parameters.len());
    let record = store.type_payload(instance).unwrap();
    assert!(
        record
            .object_flags()
            .contains(ObjectFlags::ANONYMOUS | ObjectFlags::INSTANTIATED)
    );
    assert!(
        !record
            .object_flags()
            .intersects(ObjectFlags::CLASS | ObjectFlags::INTERFACE | ObjectFlags::REFERENCE)
    );
    assert_eq!(record.symbol(), Some(source_symbol));
    let metadata = store.type_alias(record.alias().unwrap()).unwrap();
    assert_eq!(metadata.symbol(), Some(alias_symbol));
    assert_eq!(metadata.type_arguments(), Some(arguments));
    let instance_data = object(context, instance);
    assert_eq!(instance_data.target, Some(target));
    let mapper = instance_data.mapper.unwrap();
    for ((parameter, argument), declaration) in
        parameters.iter().zip(arguments).zip(&alias.parameters)
    {
        assert_eq!(store.map_type(mapper, *parameter), Some(*argument));
        assert_eq!(
            store.type_payload(*parameter).unwrap().symbol(),
            Some(symbol(context, *declaration))
        );
    }
    let target_record = store.type_payload(target).unwrap();
    assert_eq!(target_record.symbol(), Some(source_symbol));
    let target_alias = store.type_alias(target_record.alias().unwrap()).unwrap();
    assert_eq!(target_alias.symbol(), Some(alias_symbol));
    assert_eq!(target_alias.type_arguments(), Some(parameters));
    let target_data = object(context, target);
    assert_eq!(target_data.target, None);
    assert_eq!(target_data.mapper, None);
    assert_eq!(node_type(context, alias.literal), Some(target));
    assert_eq!(
        store
            .type_node_links(alias.literal)
            .unwrap()
            .outer_type_parameters
            .as_deref(),
        Some(parameters)
    );
    let requests = links.instantiations.as_ref().unwrap();
    assert!(requests.values().any(|type_| *type_ == target));
    assert!(requests.values().any(|type_| *type_ == instance));
    let TypeCacheState::Allocated(instantiations) = &target_data.instantiations else {
        panic!("the source object must own its instance cache")
    };
    assert!(instantiations.values().any(|type_| *type_ == instance));
    target
}

fn assert_proxy(
    context: &CanonicalCheckerContext<'_>,
    receiver: TypeId,
    original: Property,
    proxy: SemanticSymbolId,
) {
    let original_symbol = symbol(context, original.declaration);
    assert_ne!(proxy, original_symbol);
    let store = context.store();
    let source = store.symbol(original_symbol).unwrap();
    let mapped = store.symbol(proxy).unwrap();
    assert!(mapped.flags().contains(SymbolFlags::TRANSIENT));
    assert!(mapped.check_flags().contains(CheckFlags::INSTANTIATED));
    assert_eq!(mapped.declarations(), source.declarations());
    assert_eq!(mapped.value_declaration(), source.value_declaration());
    assert_eq!(mapped.parent(), source.parent());
    assert_eq!(
        mapped.flags().contains(SymbolFlags::OPTIONAL),
        source.flags().contains(SymbolFlags::OPTIONAL)
    );
    assert_eq!(
        mapped.check_flags().contains(CheckFlags::READONLY),
        original.readonly
    );
    let links = store.value_symbol_links(proxy).unwrap();
    assert_eq!(links.target, Some(original_symbol));
    assert_eq!(links.mapper, object(context, receiver).mapper);
}

fn assert_query_replay(context: &mut CanonicalCheckerContext<'_>, queries: &[(NodeRef, TypeId)]) {
    let before = counts(context);
    let diagnostics = context.diagnostics().clone();
    for (node, expected) in queries.iter().rev().chain(queries) {
        assert_eq!(context.get_type_from_type_node(*node), Ok(*expected));
    }
    assert_eq!(counts(context), before);
    assert_eq!(context.diagnostics(), &diagnostics);
}

fn assert_source_replay(
    context: &mut CanonicalCheckerContext<'_>,
    files: &[FileId],
    queries: &[(NodeRef, TypeId)],
    instances: &[TypeId],
) {
    let before = counts(context);
    let diagnostics = context.diagnostics().clone();
    let objects = instances
        .iter()
        .map(|type_| object(context, *type_).clone())
        .collect::<Vec<_>>();
    let properties = objects
        .iter()
        .flat_map(|object| object.structured.properties.iter().flatten())
        .map(|property| {
            (
                *property,
                context.store().value_symbol_links(*property).cloned(),
            )
        })
        .collect::<Vec<_>>();
    let aliases = instances
        .iter()
        .map(|type_| {
            let record = context.store().type_payload(*type_).unwrap();
            let owner = context
                .store()
                .type_alias(record.alias().unwrap())
                .unwrap()
                .symbol()
                .unwrap();
            (owner, context.store().type_alias_links(owner).cloned())
        })
        .collect::<Vec<_>>();
    for file in files {
        context.recheck_source_file(*file).unwrap();
    }
    assert_query_replay(context, queries);
    for (type_, expected) in instances.iter().zip(&objects) {
        assert_eq!(object(context, *type_), expected);
    }
    for (property, expected) in properties {
        assert_eq!(
            context.store().value_symbol_links(property),
            expected.as_ref()
        );
    }
    for (owner, expected) in aliases {
        assert_eq!(context.store().type_alias_links(owner), expected.as_ref());
    }
    assert_eq!(counts(context), before);
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
fn concrete_box_queries_keep_source_identity_and_substitute_in_either_order() {
    for reverse in [false, true] {
        for body in ["{ value: T }", "({ value: T })"] {
            let declarations = parse_source_file(&format!("type Box<T> = {body};"));
            let usage = parse_source_file(concat!(
                "declare const text: Box<string>; declare const count: Box<number>; ",
                "const textValue: string = text.value; const numberValue: number = count.value;",
            ));
            let mut context = context(
                &[(DECLARATIONS, &declarations), (FIRST_USE, &usage)],
                CanonicalCheckerOptions::default(),
            );
            let box_ = alias(&declarations, "Box");
            let value = source_property(&declarations, &box_, "value");
            let annotations =
                ["text", "count"].map(|name| variable(&usage, FIRST_USE, name).annotation);
            let order = if reverse { [1, 0] } else { [0, 1] };
            let mut instances = [None, None];
            for index in order {
                instances[index] =
                    Some(context.get_type_from_type_node(annotations[index]).unwrap());
            }
            let instances = instances.map(Option::unwrap);
            assert_ne!(instances[0], instances[1]);
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let arguments = [bootstrap.string_type, bootstrap.number_type];
            let target = assert_instance(&context, &box_, instances[0], &[arguments[0]]);
            assert_eq!(
                assert_instance(&context, &box_, instances[1], &[arguments[1]]),
                target
            );
            for (instance, display) in instances.iter().zip(["Box<string>", "Box<number>"]) {
                assert_eq!(context.type_to_string(*instance).unwrap(), display);
                assert!(object(&context, *instance).structured.members.is_none());
                assert!(object(&context, *instance).structured.properties.is_none());
            }
            assert!(object(&context, target).structured.members.is_none());
            assert_cold_property(&context, value);
            assert_unchecked(&context, DECLARATIONS);
            assert_unchecked(&context, FIRST_USE);
            let queries = annotations.into_iter().zip(instances).collect::<Vec<_>>();
            assert_query_replay(&mut context, &queries);

            context.check_source_file(FIRST_USE).unwrap();
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
            assert_unchecked(&context, DECLARATIONS);
            let parameter = context
                .store()
                .type_alias_links(symbol(&context, box_.declaration))
                .unwrap()
                .type_parameters
                .as_ref()
                .unwrap()[0];
            assert_eq!(
                value_type(&context, symbol(&context, value.declaration)),
                Some(parameter)
            );
            for ((instance, argument), result) in instances
                .into_iter()
                .zip(arguments)
                .zip(["textValue", "numberValue"])
            {
                let proxy = member(&context, instance, "value");
                assert_proxy(&context, instance, value, proxy);
                assert_eq!(value_type(&context, proxy), Some(argument));
                assert_eq!(
                    node_type(
                        &context,
                        variable(&usage, FIRST_USE, result).initializer.unwrap()
                    ),
                    Some(argument)
                );
            }
            context.check_source_file(DECLARATIONS).unwrap();
            assert_source_replay(
                &mut context,
                &[DECLARATIONS, FIRST_USE],
                &queries,
                &instances,
            );
            assert_eq!(node_type(&context, box_.literal), Some(target));
        }
    }
}

#[test]
fn pair_aliases_keep_argument_order_in_mappers_and_properties() {
    let declarations = parse_source_file("type Pair<A, B> = { first: A; second: B };");
    let usage = parse_source_file(concat!(
        "declare const forward: Pair<string, number>; ",
        "declare const reverse: Pair<number, string>; ",
        "const firstText: string = forward.first; const secondNumber: number = forward.second; ",
        "const firstNumber: number = reverse.first; const secondText: string = reverse.second;",
    ));
    let mut context = context(
        &[(DECLARATIONS, &declarations), (FIRST_USE, &usage)],
        CanonicalCheckerOptions::default(),
    );
    let pair = alias(&declarations, "Pair");
    let nodes = ["forward", "reverse"].map(|name| variable(&usage, FIRST_USE, name).annotation);
    let instances = nodes.map(|node| context.get_type_from_type_node(node).unwrap());
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let arguments = [
        [bootstrap.string_type, bootstrap.number_type],
        [bootstrap.number_type, bootstrap.string_type],
    ];
    assert_ne!(instances[0], instances[1]);
    let target = assert_instance(&context, &pair, instances[0], &arguments[0]);
    assert_eq!(
        assert_instance(&context, &pair, instances[1], &arguments[1]),
        target
    );
    for name in ["first", "second"] {
        assert_cold_property(&context, source_property(&declarations, &pair, name));
    }
    context.check_source_file(FIRST_USE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    for (instance, arguments) in instances.into_iter().zip(arguments) {
        for (name, argument) in ["first", "second"].into_iter().zip(arguments) {
            let property = member(&context, instance, name);
            assert_proxy(
                &context,
                instance,
                source_property(&declarations, &pair, name),
                property,
            );
            assert_eq!(value_type(&context, property), Some(argument));
        }
    }
    context.check_source_file(DECLARATIONS).unwrap();
    let queries = nodes.into_iter().zip(instances).collect::<Vec<_>>();
    assert_source_replay(
        &mut context,
        &[DECLARATIONS, FIRST_USE],
        &queries,
        &instances,
    );
}

#[test]
fn phantom_alias_arguments_remain_part_of_instance_identity() {
    let declarations = parse_source_file("type Fixed<T> = { value: string };");
    let usage = parse_source_file(concat!(
        "declare const text: Fixed<string>; declare const count: Fixed<number>; ",
        "const left: string = text.value; const right: string = count.value;",
    ));
    let mut context = context(
        &[(DECLARATIONS, &declarations), (FIRST_USE, &usage)],
        CanonicalCheckerOptions::default(),
    );
    let fixed = alias(&declarations, "Fixed");
    let nodes = ["text", "count"].map(|name| variable(&usage, FIRST_USE, name).annotation);
    let instances = nodes.map(|node| context.get_type_from_type_node(node).unwrap());
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let (string, number) = (bootstrap.string_type, bootstrap.number_type);
    assert_ne!(instances[0], instances[1]);
    let target = assert_instance(&context, &fixed, instances[0], &[string]);
    assert_eq!(
        assert_instance(&context, &fixed, instances[1], &[number]),
        target
    );
    let value = source_property(&declarations, &fixed, "value");
    assert_cold_property(&context, value);
    context.check_source_file(FIRST_USE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    assert_eq!(
        value_type(&context, symbol(&context, value.declaration)),
        Some(string)
    );
    for instance in instances {
        assert_eq!(
            value_type(&context, member(&context, instance, "value")),
            Some(string)
        );
    }
    assert_eq!(
        context.type_to_string(instances[0]).unwrap(),
        "Fixed<string>"
    );
    assert_eq!(
        context.type_to_string(instances[1]).unwrap(),
        "Fixed<number>"
    );
    context.check_source_file(DECLARATIONS).unwrap();
    let queries = nodes.into_iter().zip(instances).collect::<Vec<_>>();
    assert_source_replay(
        &mut context,
        &[DECLARATIONS, FIRST_USE],
        &queries,
        &instances,
    );
}

#[test]
fn selected_property_demand_keeps_siblings_cold_and_reuses_a_constant_proxy() {
    let declarations =
        parse_source_file("type Box<T> = { value: T; readonly label: string; other: T };");
    let first = parse_source_file(
        "declare const input: Box<string>; const selected: string = input.value;",
    );
    let second = parse_source_file("const label: string = input.label;");
    let mut context = context(
        &[
            (DECLARATIONS, &declarations),
            (FIRST_USE, &first),
            (SECOND_USE, &second),
        ],
        CanonicalCheckerOptions::default(),
    );
    let box_ = alias(&declarations, "Box");
    let fields =
        ["value", "label", "other"].map(|name| source_property(&declarations, &box_, name));
    let annotation = variable(&first, FIRST_USE, "input").annotation;
    let instance = context.get_type_from_type_node(annotation).unwrap();
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let target = assert_instance(&context, &box_, instance, &[string]);
    assert!(object(&context, instance).structured.members.is_none());
    assert!(object(&context, target).structured.members.is_none());
    for field in fields {
        assert_cold_property(&context, field);
    }
    assert_query_replay(&mut context, &[(annotation, instance)]);

    context.check_source_file(FIRST_USE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    assert_unchecked(&context, DECLARATIONS);
    assert_unchecked(&context, SECOND_USE);
    let table = object(&context, instance).structured.members.unwrap();
    let proxies = ["value", "label", "other"].map(|name| member(&context, instance, name));
    for (field, proxy) in fields.into_iter().zip(proxies) {
        assert_proxy(&context, instance, field, proxy);
    }
    assert_eq!(value_type(&context, proxies[0]), Some(string));
    for index in [1, 2] {
        assert_cold_property(&context, fields[index]);
        assert_eq!(value_type(&context, proxies[index]), None);
    }
    assert!(
        context
            .store()
            .symbol(proxies[1])
            .unwrap()
            .check_flags()
            .contains(CheckFlags::READONLY)
    );
    assert_source_replay(
        &mut context,
        &[FIRST_USE],
        &[(annotation, instance)],
        &[instance],
    );

    context.check_source_file(SECOND_USE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    assert_eq!(object(&context, instance).structured.members, Some(table));
    assert_eq!(member(&context, instance, "label"), proxies[1]);
    assert_eq!(
        value_type(&context, symbol(&context, fields[1].declaration)),
        Some(string)
    );
    assert_eq!(value_type(&context, proxies[1]), Some(string));
    assert_proxy(&context, instance, fields[1], proxies[1]);
    assert_cold_property(&context, fields[2]);
    assert_eq!(value_type(&context, proxies[2]), None);
    assert_source_replay(
        &mut context,
        &[FIRST_USE, SECOND_USE],
        &[(annotation, instance)],
        &[instance],
    );
    assert_cold_property(&context, fields[2]);
    context.check_source_file(DECLARATIONS).unwrap();
    assert_source_replay(
        &mut context,
        &[DECLARATIONS, FIRST_USE, SECOND_USE],
        &[(annotation, instance)],
        &[instance],
    );
}

fn assert_optional_type(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    base: TypeId,
    sentinel: Option<TypeId>,
) {
    if let Some(sentinel) = sentinel {
        let TypeData::Union(union) = context.store().type_payload(type_).unwrap().data() else {
            panic!("a strict optional property read must keep its absence type")
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&base));
        assert!(union.union.types.contains(&sentinel));
    } else {
        assert_eq!(type_, base);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // One option matrix checks source, proxy, and read types.
fn optional_and_readonly_alias_properties_keep_flags_and_absence_types() {
    for (strict_null_checks, exact_optional_property_types) in
        [(false, false), (true, false), (true, true)]
    {
        let declarations =
            parse_source_file("type Fields<T> = { maybe?: T; readonly frozen: T; untouched: T };");
        let usage = parse_source_file(concat!(
            "declare const input: Fields<string>; ",
            "const maybe: string | undefined = input.maybe; const frozen: string = input.frozen;",
        ));
        let mut context = context(
            &[(DECLARATIONS, &declarations), (FIRST_USE, &usage)],
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks,
                    exact_optional_property_types,
                },
                ..CanonicalCheckerOptions::default()
            },
        );
        let fields = alias(&declarations, "Fields");
        let annotation = variable(&usage, FIRST_USE, "input").annotation;
        let instance = context.get_type_from_type_node(annotation).unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (string, absence) = (bootstrap.string_type, bootstrap.undefined_or_missing_type);
        if strict_null_checks && exact_optional_property_types {
            assert_ne!(absence, bootstrap.undefined_type);
        }
        assert_instance(&context, &fields, instance, &[string]);
        let original = ["maybe", "frozen", "untouched"]
            .map(|name| source_property(&declarations, &fields, name));
        for property in original {
            assert_cold_property(&context, property);
        }
        context.check_source_file(FIRST_USE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let proxies = ["maybe", "frozen", "untouched"].map(|name| member(&context, instance, name));
        for (property, proxy) in original.into_iter().zip(proxies) {
            assert_proxy(&context, instance, property, proxy);
        }
        assert!(
            context
                .store()
                .symbol(proxies[0])
                .unwrap()
                .flags()
                .contains(SymbolFlags::OPTIONAL)
        );
        assert!(
            context
                .store()
                .symbol(proxies[1])
                .unwrap()
                .check_flags()
                .contains(CheckFlags::READONLY)
        );
        let parameter = context
            .store()
            .type_alias_links(symbol(&context, fields.declaration))
            .unwrap()
            .type_parameters
            .as_ref()
            .unwrap()[0];
        assert_eq!(
            value_type(&context, symbol(&context, original[0].declaration)),
            Some(parameter)
        );
        assert_eq!(value_type(&context, proxies[0]), Some(string));
        assert_optional_type(
            &context,
            node_type(
                &context,
                variable(&usage, FIRST_USE, "maybe").initializer.unwrap(),
            )
            .unwrap(),
            string,
            strict_null_checks.then_some(absence),
        );
        assert_eq!(value_type(&context, proxies[1]), Some(string));
        assert_cold_property(&context, original[2]);
        assert_eq!(value_type(&context, proxies[2]), None);
        context.check_source_file(DECLARATIONS).unwrap();
        assert_source_replay(
            &mut context,
            &[DECLARATIONS, FIRST_USE],
            &[(annotation, instance)],
            &[instance],
        );
    }
}

#[test]
fn wrong_alias_property_and_object_assignments_keep_diagnostic_types_and_locations() {
    let declarations = parse_source_file("type Box<T> = { value: T };");
    let usage = parse_source_file(concat!(
        "declare const input: Box<string>; ",
        "const wrong: number = input.value; const mismatch: Box<number> = input;",
    ));
    let mut context = context(
        &[(DECLARATIONS, &declarations), (FIRST_USE, &usage)],
        CanonicalCheckerOptions::default(),
    );
    let input = variable(&usage, FIRST_USE, "input");
    let wrong = variable(&usage, FIRST_USE, "wrong");
    let mismatch = variable(&usage, FIRST_USE, "mismatch");
    let text = context.get_type_from_type_node(input.annotation).unwrap();
    let number = context
        .get_type_from_type_node(mismatch.annotation)
        .unwrap();
    context.check_source_file(FIRST_USE).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2);
    for (diagnostic, node, arguments) in [
        (&diagnostics[0], wrong.name, ["string", "number"]),
        (
            &diagnostics[1],
            mismatch.name,
            ["Box<string>", "Box<number>"],
        ),
    ] {
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.node, Some(node));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.arguments, arguments);
    }
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(
        node_type(&context, wrong.initializer.unwrap()),
        Some(string)
    );
    assert_eq!(context.is_type_assignable_to(text, number), Ok(false));
    context.check_source_file(DECLARATIONS).unwrap();
    assert_source_replay(
        &mut context,
        &[DECLARATIONS, FIRST_USE],
        &[(input.annotation, text), (mismatch.annotation, number)],
        &[text, number],
    );
}

#[test]
fn alias_constraint_diagnostics_keep_the_real_recovery_instance() {
    let declarations = parse_source_file("type Bounded<T extends string> = { value: T };");
    let usage = parse_source_file(
        "declare const input: Bounded<number>; const value: number = input.value;",
    );
    let mut context = context(
        &[(DECLARATIONS, &declarations), (FIRST_USE, &usage)],
        CanonicalCheckerOptions::default(),
    );
    let bounded = alias(&declarations, "Bounded");
    let annotation = variable(&usage, FIRST_USE, "input").annotation;
    let NodeData::TypeReferenceNode(reference) = &usage.arena.get(annotation.node).unwrap().data
    else {
        unreachable!()
    };
    let argument = NodeRef::new(
        usage.arena.id(),
        FIRST_USE,
        reference.type_arguments.as_ref().unwrap().nodes[0],
    );
    let instance = context.get_type_from_type_node(annotation).unwrap();
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert_instance(&context, &bounded, instance, &[number]);
    assert_query_replay(&mut context, &[(annotation, instance)]);
    context.check_source_file(FIRST_USE).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the invalid argument must retain exactly one constraint diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2344);
    assert_eq!(diagnostic.node, Some(argument));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'number' does not satisfy the constraint 'string'."
    );
    assert_eq!(
        value_type(&context, member(&context, instance, "value")),
        Some(number)
    );
    assert_eq!(
        node_type(
            &context,
            variable(&usage, FIRST_USE, "value").initializer.unwrap()
        ),
        Some(number)
    );
    context.check_source_file(DECLARATIONS).unwrap();
    assert_source_replay(
        &mut context,
        &[DECLARATIONS, FIRST_USE],
        &[(annotation, instance)],
        &[instance],
    );
}

fn signature(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

// These source-body tests also require the generic source-signature changes.
#[test]
fn unchanged_keep_body_keeps_alias_and_function_parameters_distinct() {
    let parsed = parse_source_file(
        "type Box<T> = { value:T }; function keep<T>(value:Box<T>):Box<T>{return value;}",
    );
    let mut context = context(
        &[(DECLARATIONS, &parsed)],
        CanonicalCheckerOptions::default(),
    );
    let box_ = alias(&parsed, "Box");
    let keep = declaration(
        &parsed,
        DECLARATIONS,
        SyntaxKind::FunctionDeclaration,
        "keep",
    );
    context.check_source_file(DECLARATIONS).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let signature = signature(&context, keep);
    let record = context.store().signature(signature).unwrap();
    let function_parameter = record.type_parameters()[0];
    let parameter = record.parameters()[0];
    let result = context.get_return_type_of_signature(signature).unwrap();
    assert_eq!(value_type(&context, parameter), Some(result));
    let target = assert_instance(&context, &box_, result, &[function_parameter]);
    let alias_parameter = context
        .store()
        .type_alias_links(symbol(&context, box_.declaration))
        .unwrap()
        .type_parameters
        .as_ref()
        .unwrap()[0];
    assert_ne!(alias_parameter, function_parameter);
    assert_ne!(target, result);
    let NodeData::FunctionDeclaration(function) = &parsed.arena.get(keep.node).unwrap().data else {
        unreachable!()
    };
    let function_parameter_node = NodeRef::new(
        parsed.arena.id(),
        DECLARATIONS,
        function.type_parameters.as_ref().unwrap().nodes[0],
    );
    assert_eq!(
        context
            .store()
            .type_payload(function_parameter)
            .unwrap()
            .symbol(),
        Some(symbol(&context, function_parameter_node))
    );
    let annotation = NodeRef::new(parsed.arena.id(), DECLARATIONS, function.type_.unwrap());
    assert_source_replay(
        &mut context,
        &[DECLARATIONS],
        &[(annotation, result)],
        &[result],
    );
    assert_eq!(context.get_return_type_of_signature(signature), Ok(result));
    assert_eq!(value_type(&context, parameter), Some(result));
}

#[test]
fn symbolic_property_reads_and_composed_calls_reuse_the_concrete_alias_instance() {
    let declarations = parse_source_file("type Box<T> = { value: T };");
    let usage = parse_source_file(concat!(
        "function read<U>(value: Box<U>): U { return value.value; } ",
        "declare function copy<U>(value: Box<U>): Box<U>; ",
        "declare const input: Box<string>; ",
        "const copied: Box<string> = copy<string>(input); const value: string = read<string>(input);",
    ));
    let mut context = context(
        &[(DECLARATIONS, &declarations), (FIRST_USE, &usage)],
        CanonicalCheckerOptions::default(),
    );
    let box_ = alias(&declarations, "Box");
    let input = variable(&usage, FIRST_USE, "input").annotation;
    let concrete = context.get_type_from_type_node(input).unwrap();
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let target = assert_instance(&context, &box_, concrete, &[string]);
    context.check_source_file(FIRST_USE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let read = declaration(&usage, FIRST_USE, SyntaxKind::FunctionDeclaration, "read");
    let copy = declaration(&usage, FIRST_USE, SyntaxKind::FunctionDeclaration, "copy");
    let read_signature = signature(&context, read);
    let copy_signature = signature(&context, copy);
    let read_record = context.store().signature(read_signature).unwrap();
    let read_parameter = read_record.type_parameters()[0];
    let symbolic_read = value_type(&context, read_record.parameters()[0]).unwrap();
    let copy_record = context.store().signature(copy_signature).unwrap();
    let copy_parameter = copy_record.type_parameters()[0];
    let symbolic_copy = value_type(&context, copy_record.parameters()[0]).unwrap();
    assert_ne!(read_parameter, copy_parameter);
    assert_ne!(symbolic_read, symbolic_copy);
    assert_eq!(
        assert_instance(&context, &box_, symbolic_read, &[read_parameter]),
        target
    );
    assert_eq!(
        assert_instance(&context, &box_, symbolic_copy, &[copy_parameter]),
        target
    );
    assert_eq!(
        context.get_return_type_of_signature(read_signature),
        Ok(read_parameter)
    );
    assert_eq!(
        context.get_return_type_of_signature(copy_signature),
        Ok(symbolic_copy)
    );
    assert_eq!(
        value_type(&context, member(&context, symbolic_read, "value")),
        Some(read_parameter)
    );
    let copied = variable(&usage, FIRST_USE, "copied");
    assert_eq!(
        node_type(&context, copied.initializer.unwrap()),
        Some(concrete)
    );
    assert_eq!(
        context.get_type_from_type_node(copied.annotation),
        Ok(concrete)
    );
    assert_eq!(object(&context, concrete).target, Some(target));
    assert_eq!(
        node_type(
            &context,
            variable(&usage, FIRST_USE, "value").initializer.unwrap()
        ),
        Some(string)
    );
    let original = source_property(&declarations, &box_, "value");
    let alias_parameter = context
        .store()
        .type_alias_links(symbol(&context, box_.declaration))
        .unwrap()
        .type_parameters
        .as_ref()
        .unwrap()[0];
    assert_ne!(alias_parameter, read_parameter);
    assert_ne!(alias_parameter, copy_parameter);
    assert_eq!(
        value_type(&context, symbol(&context, original.declaration)),
        Some(alias_parameter)
    );
    context.check_source_file(DECLARATIONS).unwrap();
    assert_source_replay(
        &mut context,
        &[DECLARATIONS, FIRST_USE],
        &[(input, concrete), (copied.annotation, concrete)],
        &[concrete, symbolic_read, symbolic_copy],
    );
}

fn visible_alias_cache_key(
    arguments: &[TypeId],
    identity: Option<(u64, &[TypeId])>,
) -> ts_checker::semantic::type_records::CacheHashKey {
    let mut hasher = xxhash_rust::xxh3::Xxh3::new();
    let write_list = |hasher: &mut xxhash_rust::xxh3::Xxh3, types: &[TypeId]| {
        hasher.update(&u64::try_from(types.len()).unwrap().to_le_bytes());
        for type_ in types {
            hasher.update(&type_.get().to_le_bytes());
        }
    };
    write_list(&mut hasher, arguments);
    if let Some((symbol, arguments)) = identity {
        hasher.update(&[1]);
        hasher.update(&symbol.to_le_bytes());
        write_list(&mut hasher, arguments);
    } else {
        hasher.update(&[0]);
    }
    ts_checker::semantic::type_records::CacheHashKey::new(hasher.digest128())
}

#[allow(clippy::too_many_lines)] // The visible alias and property mapper have separate source owners.
fn assert_visible_alias_instance(
    context: &CanonicalCheckerContext<'_>,
    original: &Alias,
    visible_declaration: NodeRef,
    instance: TypeId,
    property_arguments: &[TypeId],
    visible_arguments: &[TypeId],
) -> TypeId {
    let store = context.store();
    let original_owner = symbol(context, original.declaration);
    let source_symbol = symbol(context, original.literal);
    let original_links = store.type_alias_links(original_owner).unwrap();
    let target = original_links.declared_type.unwrap();
    let original_parameters = original_links.type_parameters.as_deref().unwrap();
    assert_eq!(original_parameters.len(), property_arguments.len());
    let visible_owner = symbol(context, visible_declaration);
    if visible_owner == original_owner {
        assert_eq!(property_arguments, visible_arguments);
        assert_eq!(
            assert_instance(context, original, instance, property_arguments),
            target
        );
    }
    let record = store.type_payload(instance).unwrap();
    assert_eq!(record.symbol(), Some(source_symbol));
    assert!(
        record
            .object_flags()
            .contains(ObjectFlags::ANONYMOUS | ObjectFlags::INSTANTIATED)
    );
    assert!(
        !record
            .object_flags()
            .intersects(ObjectFlags::CLASS | ObjectFlags::INTERFACE | ObjectFlags::REFERENCE)
    );
    let instance_data = object(context, instance);
    assert_eq!(instance_data.target, Some(target));
    let mapper = instance_data.mapper.unwrap();
    for (parameter, expected) in original_parameters.iter().zip(property_arguments) {
        assert_eq!(store.map_type(mapper, *parameter), Some(*expected));
    }
    let metadata = store.type_alias(record.alias().unwrap()).unwrap();
    assert_eq!(metadata.symbol(), Some(visible_owner));
    let visible_links = store.type_alias_links(visible_owner).unwrap();
    let visible_declared = visible_links.declared_type.unwrap();
    let (arena, bound) = context.file(visible_declaration.file).unwrap();
    let NodeData::TypeAliasDeclaration(declaration) =
        &arena.get(visible_declaration.node).unwrap().data
    else {
        panic!("the visible identity must have a real alias declaration")
    };
    let visible_parameters = if let Some(parameters) = &declaration.type_parameters {
        assert!(!parameters.nodes.is_empty());
        let types = visible_links.type_parameters.as_deref().unwrap();
        assert_eq!(types.len(), parameters.nodes.len());
        assert_eq!(types.len(), visible_arguments.len());
        for (node, type_) in parameters.nodes.iter().zip(types) {
            let declaration = NodeRef::new(arena.id(), visible_declaration.file, *node);
            let owner = bound.symbol(declaration).unwrap();
            assert_eq!(store.type_payload(*type_).unwrap().symbol(), Some(owner));
            assert_eq!(
                store.declared_type_links(owner).unwrap().declared_type,
                Some(*type_)
            );
        }
        assert_eq!(metadata.type_arguments(), Some(visible_arguments));
        let requests = visible_links.instantiations.as_ref().unwrap();
        assert_eq!(
            requests.get(&visible_alias_cache_key(visible_arguments, None)),
            Some(&instance)
        );
        assert!(requests.values().any(|type_| *type_ == visible_declared));
        types
    } else {
        assert!(visible_arguments.is_empty());
        assert_eq!(visible_links.type_parameters, None);
        assert_eq!(visible_links.instantiations, None);
        assert_eq!(metadata.type_arguments(), None);
        assert_eq!(visible_declared, instance);
        &[]
    };
    let declared_record = store.type_payload(visible_declared).unwrap();
    assert_eq!(declared_record.symbol(), Some(source_symbol));
    let declared_metadata = store.type_alias(declared_record.alias().unwrap()).unwrap();
    assert_eq!(declared_metadata.symbol(), Some(visible_owner));
    assert_eq!(
        declared_metadata.type_arguments(),
        declaration
            .type_parameters
            .as_ref()
            .map(|_| visible_parameters)
    );
    let declared_arguments = if visible_owner == original_owner {
        assert_eq!(visible_declared, target);
        original_parameters.to_vec()
    } else {
        assert_ne!(visible_declared, target);
        let declared_data = object(context, visible_declared);
        assert_eq!(declared_data.target, Some(target));
        let declared_mapper = declared_data.mapper.unwrap();
        original_parameters
            .iter()
            .map(|parameter| store.map_type(declared_mapper, *parameter).unwrap())
            .collect()
    };
    let identity = store
        .symbol_store()
        .assigned_global_symbol_id(visible_owner)
        .unwrap();
    let TypeCacheState::Allocated(instantiations) = &object(context, target).instantiations else {
        panic!("the original object must retain native and wrapped cache entries")
    };
    assert_eq!(
        instantiations.get(&visible_alias_cache_key(
            property_arguments,
            Some((identity, visible_arguments))
        )),
        Some(&instance)
    );
    assert_eq!(
        instantiations.get(&visible_alias_cache_key(
            &declared_arguments,
            Some((identity, visible_parameters))
        )),
        Some(&visible_declared)
    );
    assert_eq!(node_type(context, original.literal), Some(target));
    target
}

#[test]
#[allow(clippy::too_many_lines)] // Both query orders exercise one shared source and separate lazy aliases.
fn visible_alias_chains_keep_distinct_identities_and_lazy_properties() {
    let declarations = parse_source_file(concat!(
        "type Box<T> = { value: T; readonly label: string; other: T }; ",
        "type Wrapped<U> = Box<U>; type Twice<U> = Wrapped<U>;",
    ));
    let first = parse_source_file(concat!(
        "declare const native: Box<string>; declare const wrapped: Wrapped<string>; ",
        "declare const twice: Twice<string>; const nativeValue: string = native.value; ",
        "const wrappedValue: string = wrapped.value; const twiceValue: string = twice.value;",
    ));
    let second = parse_source_file("const visibleLabel: string = wrapped.label;");
    for reverse in [false, true] {
        let mut context = context(
            &[
                (DECLARATIONS, &declarations),
                (FIRST_USE, &first),
                (SECOND_USE, &second),
            ],
            CanonicalCheckerOptions::default(),
        );
        let original = alias(&declarations, "Box");
        let identities = ["Box", "Wrapped", "Twice"].map(|name| {
            declaration(
                &declarations,
                DECLARATIONS,
                SyntaxKind::TypeAliasDeclaration,
                name,
            )
        });
        let nodes =
            ["native", "wrapped", "twice"].map(|name| variable(&first, FIRST_USE, name).annotation);
        let mut instances = nodes.map(|_| None);
        for index in if reverse { [2, 1, 0] } else { [0, 1, 2] } {
            instances[index] = Some(context.get_type_from_type_node(nodes[index]).unwrap());
        }
        let instances = instances.map(Option::unwrap);
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let target = assert_visible_alias_instance(
            &context,
            &original,
            identities[0],
            instances[0],
            &[string],
            &[string],
        );
        let alias_ids = instances.map(|type_| {
            context
                .store()
                .type_payload(type_)
                .unwrap()
                .alias()
                .unwrap()
        });
        for (index, instance) in instances.iter().copied().enumerate() {
            for (earlier, alias) in instances[..index].iter().zip(&alias_ids[..index]) {
                assert_ne!(instance, *earlier);
                assert_ne!(alias_ids[index], *alias);
            }
            assert_eq!(
                assert_visible_alias_instance(
                    &context,
                    &original,
                    identities[index],
                    instance,
                    &[string],
                    &[string]
                ),
                target
            );
            assert!(object(&context, instance).structured.members.is_none());
            assert_eq!(
                context.type_to_string(instance).unwrap(),
                ["Box<string>", "Wrapped<string>", "Twice<string>"][index]
            );
        }
        let declared = identities.map(|identity| {
            context
                .store()
                .type_alias_links(symbol(&context, identity))
                .unwrap()
                .declared_type
                .unwrap()
        });
        for type_ in declared {
            assert!(object(&context, type_).structured.members.is_none());
        }
        let fields =
            ["value", "label", "other"].map(|name| source_property(&declarations, &original, name));
        for field in fields {
            assert_cold_property(&context, field);
        }
        assert_unchecked(&context, DECLARATIONS);
        assert_unchecked(&context, FIRST_USE);
        let queries = nodes.into_iter().zip(instances).collect::<Vec<_>>();
        assert_query_replay(&mut context, &queries);
        context.check_source_file(FIRST_USE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        assert_unchecked(&context, DECLARATIONS);
        let parameter = context
            .store()
            .type_alias_links(symbol(&context, original.declaration))
            .unwrap()
            .type_parameters
            .as_ref()
            .unwrap()[0];
        assert_eq!(
            value_type(&context, symbol(&context, fields[0].declaration)),
            Some(parameter)
        );
        let proxies = instances.map(|instance| {
            ["value", "label", "other"].map(|name| member(&context, instance, name))
        });
        for (instance, properties) in instances.into_iter().zip(proxies) {
            for (field, property) in fields.into_iter().zip(properties) {
                assert_proxy(&context, instance, field, property);
            }
            assert_eq!(value_type(&context, properties[0]), Some(string));
            assert_eq!(value_type(&context, properties[1]), None);
            assert_eq!(value_type(&context, properties[2]), None);
        }
        for field in [fields[1], fields[2]] {
            assert_cold_property(&context, field);
        }
        let wrapped_members = object(&context, instances[1]).structured.members;
        context.check_source_file(SECOND_USE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        assert_eq!(
            object(&context, instances[1]).structured.members,
            wrapped_members
        );
        assert_eq!(member(&context, instances[1], "label"), proxies[1][1]);
        assert_eq!(value_type(&context, proxies[1][1]), Some(string));
        assert_eq!(value_type(&context, proxies[0][1]), None);
        assert_eq!(value_type(&context, proxies[2][1]), None);
        assert_cold_property(&context, fields[2]);
        for properties in proxies {
            assert_eq!(value_type(&context, properties[2]), None);
        }
        context.check_source_file(DECLARATIONS).unwrap();
        let tracked = instances.into_iter().chain(declared).collect::<Vec<_>>();
        assert_source_replay(
            &mut context,
            &[DECLARATIONS, FIRST_USE, SECOND_USE],
            &queries,
            &tracked,
        );
        assert_eq!(
            instances.map(|type_| context
                .store()
                .type_payload(type_)
                .unwrap()
                .alias()
                .unwrap()),
            alias_ids
        );
        for (instance, display) in
            instances
                .into_iter()
                .zip(["Box<string>", "Wrapped<string>", "Twice<string>"])
        {
            assert_eq!(context.type_to_string(instance).unwrap(), display);
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Reordered, repeated, and unused arguments need separate visible vectors.
fn visible_alias_arguments_preserve_order_repetition_and_arity() {
    let declarations = parse_source_file(concat!(
        "type Pair<A, B> = { first: A; second: B; untouched: A }; ",
        "type Flip<A, B> = Pair<B, A>; type Repeat<U> = Pair<U, U>; ",
        "type WithUnused<A, B, Extra> = Pair<B, A>;",
    ));
    let usage = parse_source_file(concat!(
        "declare const native: Pair<string, number>; declare const flipped: Flip<number, string>; ",
        "declare const swapped: Flip<string, number>; declare const repeated: Repeat<string>; ",
        "declare const unusedBool: WithUnused<number, string, boolean>; ",
        "declare const unusedNumber: WithUnused<number, string, number>; ",
        "const nativeFirst: string = native.first; const nativeSecond: number = native.second; ",
        "const flippedFirst: string = flipped.first; const flippedSecond: number = flipped.second; ",
        "const swappedFirst: number = swapped.first; const swappedSecond: string = swapped.second; ",
        "const repeatedFirst: string = repeated.first; const repeatedSecond: string = repeated.second; ",
        "const unusedBoolFirst: string = unusedBool.first; const unusedBoolSecond: number = unusedBool.second; ",
        "const unusedNumberFirst: string = unusedNumber.first; const unusedNumberSecond: number = unusedNumber.second;",
    ));
    let mut context = context(
        &[(DECLARATIONS, &declarations), (FIRST_USE, &usage)],
        CanonicalCheckerOptions::default(),
    );
    let original = alias(&declarations, "Pair");
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let (string, number, boolean) = (
        bootstrap.string_type,
        bootstrap.number_type,
        bootstrap.boolean_type,
    );
    let cases = [
        (
            "native",
            "Pair",
            [string, number],
            vec![string, number],
            "Pair<string, number>",
        ),
        (
            "flipped",
            "Flip",
            [string, number],
            vec![number, string],
            "Flip<number, string>",
        ),
        (
            "swapped",
            "Flip",
            [number, string],
            vec![string, number],
            "Flip<string, number>",
        ),
        (
            "repeated",
            "Repeat",
            [string, string],
            vec![string],
            "Repeat<string>",
        ),
        (
            "unusedBool",
            "WithUnused",
            [string, number],
            vec![number, string, boolean],
            "WithUnused<number, string, boolean>",
        ),
        (
            "unusedNumber",
            "WithUnused",
            [string, number],
            vec![number, string, number],
            "WithUnused<number, string, number>",
        ),
    ];
    let nodes = cases
        .each_ref()
        .map(|(name, ..)| variable(&usage, FIRST_USE, name).annotation);
    let instances = nodes.map(|node| context.get_type_from_type_node(node).unwrap());
    let target = context
        .store()
        .type_alias_links(symbol(&context, original.declaration))
        .unwrap()
        .declared_type
        .unwrap();
    let alias_ids = instances.map(|type_| {
        context
            .store()
            .type_payload(type_)
            .unwrap()
            .alias()
            .unwrap()
    });
    for (index, (_, visible, property_arguments, visible_arguments, display)) in
        cases.iter().enumerate()
    {
        for (earlier, alias) in instances[..index].iter().zip(&alias_ids[..index]) {
            assert_ne!(instances[index], *earlier);
            assert_ne!(alias_ids[index], *alias);
        }
        let identity = declaration(
            &declarations,
            DECLARATIONS,
            SyntaxKind::TypeAliasDeclaration,
            visible,
        );
        assert_eq!(
            assert_visible_alias_instance(
                &context,
                &original,
                identity,
                instances[index],
                property_arguments,
                visible_arguments
            ),
            target
        );
        assert_eq!(context.type_to_string(instances[index]).unwrap(), *display);
        assert!(
            object(&context, instances[index])
                .structured
                .members
                .is_none()
        );
    }
    let fields = ["first", "second", "untouched"]
        .map(|name| source_property(&declarations, &original, name));
    for field in fields {
        assert_cold_property(&context, field);
    }
    assert_unchecked(&context, DECLARATIONS);
    let queries = nodes.into_iter().zip(instances).collect::<Vec<_>>();
    assert_query_replay(&mut context, &queries);
    context.check_source_file(FIRST_USE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    assert_unchecked(&context, DECLARATIONS);
    for (instance, (_, _, arguments, _, _)) in instances.into_iter().zip(&cases) {
        for ((name, original), expected) in
            ["first", "second"].into_iter().zip(fields).zip(arguments)
        {
            let property = member(&context, instance, name);
            assert_proxy(&context, instance, original, property);
            assert_eq!(value_type(&context, property), Some(*expected));
        }
        let untouched = member(&context, instance, "untouched");
        assert_proxy(&context, instance, fields[2], untouched);
        assert_eq!(value_type(&context, untouched), None);
    }
    let parameters = context
        .store()
        .type_alias_links(symbol(&context, original.declaration))
        .unwrap()
        .type_parameters
        .as_ref()
        .unwrap();
    for (field, parameter) in fields[..2].iter().zip(parameters) {
        assert_eq!(
            value_type(&context, symbol(&context, field.declaration)),
            Some(*parameter)
        );
    }
    assert_cold_property(&context, fields[2]);
    context.check_source_file(DECLARATIONS).unwrap();
    let tracked = instances.into_iter().chain([target]).collect::<Vec<_>>();
    assert_source_replay(&mut context, &[DECLARATIONS, FIRST_USE], &queries, &tracked);
    assert_eq!(
        instances.map(|type_| context
            .store()
            .type_payload(type_)
            .unwrap()
            .alias()
            .unwrap()),
        alias_ids
    );
    for (instance, (_, _, _, _, display)) in instances.into_iter().zip(&cases) {
        assert_eq!(context.type_to_string(instance).unwrap(), *display);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Fixed property arguments must not erase generic or zero-arity visible aliases.
fn fixed_property_arguments_keep_visible_alias_identity_in_either_query_order() {
    let declarations = parse_source_file(concat!(
        "type Box<T> = { value: T; other: T }; type Fixed<U> = Box<string>; ",
        "type FixedPair<A, B> = Box<string>; type Chained<U> = Fixed<U>; ",
        "type StringBox = Box<string>;",
    ));
    let usage = parse_source_file(concat!(
        "declare const native: Box<string>; declare const count: Fixed<number>; ",
        "declare const truth: Fixed<boolean>; declare const ordered: FixedPair<number, boolean>; ",
        "declare const reversed: FixedPair<boolean, number>; declare const chain: Chained<number>; ",
        "declare const plain: StringBox; const nativeValue: string = native.value; ",
        "const countValue: string = count.value; const truthValue: string = truth.value; ",
        "const orderedValue: string = ordered.value; const reversedValue: string = reversed.value; ",
        "const chainValue: string = chain.value; const plainValue: string = plain.value;",
    ));
    for reverse in [false, true] {
        let mut context = context(
            &[(DECLARATIONS, &declarations), (FIRST_USE, &usage)],
            CanonicalCheckerOptions::default(),
        );
        let original = alias(&declarations, "Box");
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (string, number, boolean) = (
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.boolean_type,
        );
        let cases = [
            ("native", "Box", vec![string], "Box<string>"),
            ("count", "Fixed", vec![number], "Fixed<number>"),
            ("truth", "Fixed", vec![boolean], "Fixed<boolean>"),
            (
                "ordered",
                "FixedPair",
                vec![number, boolean],
                "FixedPair<number, boolean>",
            ),
            (
                "reversed",
                "FixedPair",
                vec![boolean, number],
                "FixedPair<boolean, number>",
            ),
            ("chain", "Chained", vec![number], "Chained<number>"),
            ("plain", "StringBox", vec![], "StringBox"),
        ];
        let nodes = cases
            .each_ref()
            .map(|(name, ..)| variable(&usage, FIRST_USE, name).annotation);
        let mut order = (0..nodes.len()).collect::<Vec<_>>();
        if reverse {
            order.reverse();
        }
        let mut instances = nodes.map(|_| None);
        for index in order {
            instances[index] = Some(context.get_type_from_type_node(nodes[index]).unwrap());
        }
        let instances = instances.map(Option::unwrap);
        let target = context
            .store()
            .type_alias_links(symbol(&context, original.declaration))
            .unwrap()
            .declared_type
            .unwrap();
        let alias_ids = instances.map(|type_| {
            context
                .store()
                .type_payload(type_)
                .unwrap()
                .alias()
                .unwrap()
        });
        for (index, (_, visible, arguments, display)) in cases.iter().enumerate() {
            for (earlier, alias) in instances[..index].iter().zip(&alias_ids[..index]) {
                assert_ne!(instances[index], *earlier);
                assert_ne!(alias_ids[index], *alias);
            }
            let identity = declaration(
                &declarations,
                DECLARATIONS,
                SyntaxKind::TypeAliasDeclaration,
                visible,
            );
            assert_eq!(
                assert_visible_alias_instance(
                    &context,
                    &original,
                    identity,
                    instances[index],
                    &[string],
                    arguments
                ),
                target
            );
            assert_eq!(context.type_to_string(instances[index]).unwrap(), *display);
            assert!(
                object(&context, instances[index])
                    .structured
                    .members
                    .is_none()
            );
        }
        let fields = ["value", "other"].map(|name| source_property(&declarations, &original, name));
        for field in fields {
            assert_cold_property(&context, field);
        }
        assert_unchecked(&context, DECLARATIONS);
        assert_unchecked(&context, FIRST_USE);
        let queries = nodes.into_iter().zip(instances).collect::<Vec<_>>();
        assert_query_replay(&mut context, &queries);
        context.check_source_file(FIRST_USE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        assert_unchecked(&context, DECLARATIONS);
        for instance in instances {
            let value = member(&context, instance, "value");
            assert_proxy(&context, instance, fields[0], value);
            assert_eq!(value_type(&context, value), Some(string));
            let other = member(&context, instance, "other");
            assert_proxy(&context, instance, fields[1], other);
            assert_eq!(value_type(&context, other), None);
        }
        let parameter = context
            .store()
            .type_alias_links(symbol(&context, original.declaration))
            .unwrap()
            .type_parameters
            .as_ref()
            .unwrap()[0];
        assert_eq!(
            value_type(&context, symbol(&context, fields[0].declaration)),
            Some(parameter)
        );
        assert_cold_property(&context, fields[1]);
        context.check_source_file(DECLARATIONS).unwrap();
        let tracked = instances.into_iter().chain([target]).collect::<Vec<_>>();
        assert_source_replay(&mut context, &[DECLARATIONS, FIRST_USE], &queries, &tracked);
        assert_eq!(
            instances.map(|type_| context
                .store()
                .type_payload(type_)
                .unwrap()
                .alias()
                .unwrap()),
            alias_ids
        );
        for (instance, (_, _, _, display)) in instances.into_iter().zip(&cases) {
            assert_eq!(context.type_to_string(instance).unwrap(), *display);
        }
    }
}
