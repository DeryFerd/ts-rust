use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, ClassMembers, IntrinsicBootstrapOptions,
    SignatureId, TypeData, TypeId, signatures::SignatureFlags,
};
use ts_options::{ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(272_100);
const PROVIDER: FileId = FileId::new(272_101);

macro_rules! library_sources {
    ($($name:literal),+ $(,)?) => {
        &[$((
            concat!("\"/lib/lib.", $name, ".d.ts\""),
            include_str!(concat!("../../ts_bundled/libs/lib.", $name, ".d.ts")),
        )),+]
    };
}

// Keep the full ES2022 default-library closure and its source order.
const LIBRARIES: &[(&str, &str)] = library_sources![
    "es5",
    "es2015",
    "es2016",
    "es2017",
    "es2018",
    "es2019",
    "es2020",
    "es2021",
    "es2022",
    "dom",
    "dom.iterable",
    "dom.asynciterable",
    "webworker.importscripts",
    "scripthost",
    "es2015.core",
    "es2015.collection",
    "es2015.generator",
    "es2015.iterable",
    "es2015.promise",
    "es2015.proxy",
    "es2015.reflect",
    "es2015.symbol",
    "es2015.symbol.wellknown",
    "es2016.array.include",
    "es2016.intl",
    "es2017.arraybuffer",
    "es2017.date",
    "es2017.object",
    "es2017.sharedmemory",
    "es2017.string",
    "es2017.intl",
    "es2017.typedarrays",
    "es2018.asyncgenerator",
    "es2018.asynciterable",
    "es2018.intl",
    "es2018.promise",
    "es2018.regexp",
    "es2019.array",
    "es2019.object",
    "es2019.string",
    "es2019.symbol",
    "es2019.intl",
    "es2020.bigint",
    "es2020.date",
    "es2020.promise",
    "es2020.sharedmemory",
    "es2020.string",
    "es2020.symbol.wellknown",
    "es2020.intl",
    "es2020.number",
    "es2021.promise",
    "es2021.string",
    "es2021.weakref",
    "es2021.intl",
    "es2022.array",
    "es2022.error",
    "es2022.intl",
    "es2022.object",
    "es2022.string",
    "es2022.regexp",
    "decorators",
    "decorators.legacy",
    "es2022.full",
];

const ITEM_PROVIDER: &str = concat!(
    "interface Item { serial: number; }\n",
    "interface ItemFactory { new(serial: number): Item; readonly prototype: Item; readonly tag: string; }\n",
    "declare var CreateItem: ItemFactory;\n",
);

struct Input {
    file: FileId,
    path: &'static str,
    parsed: ParseResult,
    library: bool,
}

fn inputs(source: &str, provider: Option<&str>) -> Vec<Input> {
    let mut files = LIBRARIES
        .iter()
        .enumerate()
        .map(|(index, &(path, text))| Input {
            file: FileId::new(272_000 + u32::try_from(index).unwrap()),
            path,
            parsed: parse_source_file(text),
            library: true,
        })
        .collect::<Vec<_>>();
    if let Some(provider) = provider {
        files.push(Input {
            file: PROVIDER,
            path: "\"/project/provider.d.ts\"",
            parsed: parse_source_file(provider),
            library: false,
        });
    }
    files.push(Input {
        file: SOURCE,
        path: "\"/project/empty-derived.ts\"",
        parsed: parse_source_file(source),
        library: false,
    });
    files
}

fn context(files: &[Input]) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    for input in files {
        assert!(
            input.parsed.diagnostics.is_empty(),
            "{:?}",
            input.parsed.diagnostics
        );
        binder
            .bind_source_file_with_facts(
                &input.parsed.arena,
                input.parsed.source_file,
                input.file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(input.path),
                    CanonicalSourceLanguage::TypeScript,
                    input.file != SOURCE,
                    input.library,
                    if input.file == SOURCE {
                        CanonicalModuleState::External
                    } else {
                        CanonicalModuleState::Script
                    },
                )
                .with_always_strict(true),
            )
            .unwrap();
    }
    for input in files {
        binder
            .bind_typescript_declaration_slice(&input.parsed.arena, input.file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .iter()
            .map(|input| (input.file, &input.parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_bind_call_apply: true,
            strict_builtin_iterator_return: true,
            strict_function_types: true,
            strict_property_initialization: true,
            use_unknown_in_catch_variables: true,
            no_implicit_any: true,
            no_implicit_this: true,
            module_kind: ModuleKind::Es2020,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn reference(context: &CanonicalCheckerContext<'_>, file: FileId, node: NodeId) -> NodeRef {
    NodeRef::new(context.file(file).unwrap().0.id(), file, node)
}

fn named_class(context: &CanonicalCheckerContext<'_>, name: &str) -> NodeRef {
    let arena = context.file(SOURCE).unwrap().0;
    arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ClassDeclaration(class) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &arena.get(class.name?)?.data else {
                return None;
            };
            (identifier.text == name).then_some(reference(context, SOURCE, node))
        })
        .unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn global(context: &CanonicalCheckerContext<'_>, name: &str) -> SemanticSymbolId {
    let raw = context
        .store()
        .symbol_table(context.globals())
        .unwrap()
        .get_source(name)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn cached_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn signature_at(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn source_nodes(context: &CanonicalCheckerContext<'_>, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut nodes = context
        .file(SOURCE)
        .unwrap()
        .0
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind)
                .then_some((record.range.start, reference(context, SOURCE, node)))
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|&(start, _)| start);
    nodes.into_iter().map(|(_, node)| node).collect()
}

fn construct_signatures(context: &CanonicalCheckerContext<'_>, value: TypeId) -> Vec<SignatureId> {
    let TypeData::Object(object) = context.store().type_payload(value).unwrap().data() else {
        panic!("a class value must keep its own object type")
    };
    assert_eq!(object.structured.call_signature_count, 0);
    object.structured.signatures.clone().unwrap()
}

fn construct_declarations(
    context: &CanonicalCheckerContext<'_>,
    owner: SemanticSymbolId,
) -> Vec<NodeRef> {
    context
        .store()
        .symbol(owner)
        .unwrap()
        .declarations()
        .unwrap()
        .iter()
        .flat_map(|&declaration| {
            let arena = context.file(declaration.file).unwrap().0;
            let NodeData::InterfaceDeclaration(interface) =
                &arena.get(declaration.node).unwrap().data
            else {
                panic!("the constructor owner must be an interface")
            };
            interface
                .members
                .nodes
                .iter()
                .filter_map(|&node| {
                    (arena.get(node).unwrap().kind == SyntaxKind::ConstructSignature)
                        .then_some(reference(context, declaration.file, node))
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

fn assert_base(
    context: &CanonicalCheckerContext<'_>,
    members: &ClassMembers,
    value_owner: SemanticSymbolId,
    constructor_owner: SemanticSymbolId,
    instance_owner: SemanticSymbolId,
) {
    let store = context.store();
    let shells = members.shells();
    let base = members.base().unwrap();
    assert_eq!(base.symbol(), value_owner);
    assert_eq!(base.applied_instance_type(), base.instance_type());
    assert_ne!(base.instance_type(), shells.instance_type());
    assert_ne!(base.value_type(), shells.value_type());
    assert_eq!(
        store.type_payload(base.value_type()).unwrap().symbol(),
        Some(constructor_owner)
    );
    assert_eq!(
        store.type_payload(base.instance_type()).unwrap().symbol(),
        Some(instance_owner)
    );
    assert_eq!(
        store.value_symbol_links(value_owner).unwrap().resolved_type,
        Some(base.value_type())
    );
    assert_eq!(
        store.declared_type_links(constructor_owner).unwrap().declared_type,
        Some(base.value_type())
    );
    let TypeData::Interface(instance) = store.type_payload(shells.instance_type()).unwrap().data()
    else {
        panic!("the derived class must keep its real instance type")
    };
    assert_eq!(
        store.type_payload(shells.instance_type()).unwrap().symbol(),
        Some(shells.symbol())
    );
    assert_eq!(
        instance.resolved_base_constructor_type,
        Some(base.value_type())
    );
    assert_eq!(
        instance.resolved_base_types.as_deref(),
        Some(&[base.instance_type()][..])
    );
    let arena = context.file(SOURCE).unwrap().0;
    let NodeData::ClassDeclaration(class) = &arena.get(shells.declaration().node).unwrap().data
    else {
        unreachable!()
    };
    assert!(class.members.nodes.is_empty());
    assert!(class.type_parameters.is_none());
    let clause = class.heritage_clauses.as_ref().unwrap().nodes[0];
    let NodeData::HeritageClause(clause) = &arena.get(clause).unwrap().data else {
        unreachable!()
    };
    let NodeData::ExpressionWithTypeArguments(heritage) =
        &arena.get(clause.types.nodes[0]).unwrap().data
    else {
        unreachable!()
    };
    let heritage = reference(context, SOURCE, heritage.expression);
    assert_eq!(cached_type(context, heritage), base.value_type());
    assert_eq!(
        store.symbol_node_links(heritage).unwrap().resolved_symbol,
        Some(value_owner)
    );
    let local = context
        .file(SOURCE)
        .unwrap()
        .1
        .local_symbol(shells.declaration())
        .unwrap();
    assert_eq!(
        store.symbol(local).unwrap().export_symbol(),
        Some(shells.symbol())
    );
    assert_eq!(
        store.value_symbol_links(local).unwrap().resolved_type,
        Some(shells.value_type())
    );
}

fn assert_inherited_signatures(
    context: &CanonicalCheckerContext<'_>,
    members: &ClassMembers,
    constructor_owner: SemanticSymbolId,
) -> Vec<SignatureId> {
    let signatures = construct_signatures(context, members.shells().value_type());
    let declarations = construct_declarations(context, constructor_owner);
    assert_eq!(signatures.len(), declarations.len());
    assert_eq!(members.default_construct_signature(), signatures[0]);
    for (&signature, declaration) in signatures.iter().zip(declarations) {
        let original = signature_at(context, declaration);
        assert_ne!(signature, original);
        let inherited = context.store().signature(signature).unwrap();
        let original = context.store().signature(original).unwrap();
        assert_eq!(original.declaration(), Some(declaration));
        assert_eq!(
            original.resolved_return_type(),
            Some(members.base().unwrap().instance_type())
        );
        assert_eq!(inherited.declaration(), original.declaration());
        assert_eq!(inherited.parameters(), original.parameters());
        assert_eq!(
            inherited.min_argument_count(),
            original.min_argument_count()
        );
        assert_eq!(inherited.flags(), SignatureFlags::CONSTRUCT);
        assert_eq!(inherited.flags(), original.flags());
        assert!(inherited.type_parameters().is_empty());
        assert!(inherited.this_parameter().is_none());
        assert!(inherited.target().is_none());
        assert!(inherited.mapper().is_none());
        assert_eq!(
            inherited.resolved_return_type(),
            Some(members.shells().instance_type())
        );
        let arena = context.file(declaration.file).unwrap().0;
        let NodeData::ConstructSignatureDeclaration(source) =
            &arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let parameters = source
            .parameters
            .nodes
            .iter()
            .map(|&node| symbol(context, reference(context, declaration.file, node)))
            .collect::<Vec<_>>();
        assert_eq!(inherited.parameters(), parameters.as_slice());
    }
    signatures
}

fn assert_member(
    context: &CanonicalCheckerContext<'_>,
    members: &ClassMembers,
    owner: SemanticSymbolId,
    name: &str,
    expected_type: TypeId,
    static_member: bool,
) {
    let store = context.store();
    let property = store
        .symbol_table(store.symbol(owner).unwrap().members().unwrap())
        .unwrap()
        .get_source(name)
        .unwrap();
    assert_eq!(store.get_parent_of_symbol(property), Some(owner));
    let table = if static_member {
        members.static_members()
    } else {
        members.instance_members().unwrap()
    };
    assert_eq!(store.symbol_table(table).unwrap().get_source(name), Some(property));
    assert!(!members.declared_instance_properties().contains(&property));
    assert!(!members.declared_static_properties().contains(&property));
    assert_eq!(
        store.value_symbol_links(property).unwrap().resolved_type,
        Some(expected_type)
    );
    let arena = context.file(SOURCE).unwrap().0;
    let accesses = source_nodes(context, SyntaxKind::PropertyAccessExpression)
        .into_iter()
        .filter(|node| {
            let NodeData::PropertyAccessExpression(access) = &arena.get(node.node).unwrap().data
            else {
                unreachable!()
            };
            matches!(
                &arena.get(access.name).unwrap().data,
                NodeData::Identifier(identifier) if identifier.text == name
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(accesses.len(), 1);
    assert_eq!(cached_type(context, accesses[0]), expected_type);
    assert_eq!(
        store.symbol_node_links(accesses[0]).unwrap().resolved_symbol,
        Some(property)
    );
}

fn snapshot(context: &CanonicalCheckerContext<'_>) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.signature_len(),
            store.symbol_len(),
            store.mapper_len(),
            store.symbol_store().symbol_table_len(),
            store.index_info_len(),
            store.type_predicate_len(),
            store.type_alias_len(),
            store.type_resolution_len(),
        ],
        context.diagnostics().as_slice().to_vec(),
        store
            .source_file_links(context.source_file(SOURCE).unwrap())
            .cloned(),
        context
            .file(SOURCE)
            .unwrap()
            .0
            .iter()
            .map(|(node, _)| {
                let node = reference(context, SOURCE, node);
                (
                    node,
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .signatures()
            .map(|(id, signature)| {
                (
                    id,
                    signature.flags(),
                    signature.declaration(),
                    signature.parameters().to_vec(),
                    signature.type_parameters().to_vec(),
                    signature.min_argument_count(),
                    signature.resolved_min_argument_count(),
                    signature.resolved_return_type(),
                    signature.target(),
                    signature.mapper(),
                )
            })
            .collect::<Vec<_>>(),
        store.relation_state_snapshot(),
    )
}

fn replay(context: &mut CanonicalCheckerContext<'_>) {
    assert!(
        context
            .store()
            .source_file_links(context.source_file(SOURCE).unwrap())
            .is_some_and(|links| links.type_checked)
    );
    let before = snapshot(context);
    for _ in 0..2 {
        context.check_source_file(SOURCE).unwrap();
        context.recheck_source_file(SOURCE).unwrap();
        assert_eq!(snapshot(context), before);
    }
}

fn assert_error_parameters(context: &CanonicalCheckerContext<'_>, signatures: &[SignatureId]) {
    let store = context.store();
    let intrinsic = store.intrinsic_bootstrap().unwrap();
    let options_owner = global(context, "ErrorOptions");
    let options = store
        .declared_type_links(options_owner)
        .unwrap()
        .declared_type
        .unwrap();
    assert_eq!(store.type_payload(options).unwrap().symbol(), Some(options_owner));
    for (&signature, count) in signatures.iter().zip([1, 2]) {
        let signature = store.signature(signature).unwrap();
        assert_eq!(signature.parameters().len(), count);
        assert_eq!(signature.min_argument_count(), 0);
        for (&parameter, annotation) in signature
            .parameters()
            .iter()
            .zip([intrinsic.string_type, options])
        {
            let parameter_type = store.value_symbol_links(parameter).unwrap().resolved_type.unwrap();
            let TypeData::Union(union) = store.type_payload(parameter_type).unwrap().data() else {
                panic!("each optional Error parameter must retain its actual type and undefined")
            };
            let mut expected = [intrinsic.undefined_type, annotation];
            expected.sort_unstable();
            assert_eq!(union.union.types, expected);
        }
    }
}

#[test]
fn exported_empty_error_class_keeps_both_library_constructors_and_instance_members() {
    let files = inputs(
        concat!(
            "export class UnsupportedPathError extends Error {}\n",
            "declare const options: ErrorOptions;\n",
            "export const empty = new UnsupportedPathError();\n",
            "export const caused = new UnsupportedPathError('route', options);\n",
            "export const message: string = caused.message;\n",
        ),
        None,
    );
    let mut context = context(&files);
    let class = named_class(&context, "UnsupportedPathError");
    let owner = symbol(&context, class);
    context.check_source_file(SOURCE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let error = global(&context, "Error");
    let constructor = global(&context, "ErrorConstructor");
    assert_base(&context, &members, error, constructor, error);
    let declarations = construct_declarations(&context, constructor);
    assert_eq!(declarations.len(), 2);
    for (declaration, expected_path) in declarations
        .iter()
        .zip(["\"/lib/lib.es5.d.ts\"", "\"/lib/lib.es2022.error.d.ts\""])
    {
        let input = files
            .iter()
            .find(|input| input.file == declaration.file)
            .unwrap();
        assert_eq!(input.path, expected_path);
        assert!(
            context
                .file(input.file)
                .unwrap()
                .1
                .source_facts()
                .unwrap()
                .is_default_library()
        );
    }
    let signatures = assert_inherited_signatures(&context, &members, constructor);
    assert_eq!(signatures.len(), 2);
    assert_error_parameters(&context, &signatures);
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    assert_member(&context, &members, error, "message", string, false);
    let calls = source_nodes(&context, SyntaxKind::NewExpression);
    assert_eq!(calls.len(), 2);
    for call in calls {
        assert_eq!(signature_at(&context, call), signatures[1]);
        assert_eq!(
            context.get_type_at_location(call).unwrap(),
            members.shells().instance_type()
        );
    }
    replay(&mut context);
    assert_eq!(
        context.get_nongeneric_class_members(owner).unwrap(),
        members
    );
    assert_eq!(
        assert_inherited_signatures(&context, &members, constructor),
        signatures
    );
    for input in files.iter().filter(|input| input.library) {
        assert!(
            !context
                .store()
                .source_file_links(context.source_file(input.file).unwrap())
                .is_some_and(|links| links.type_checked)
        );
    }
}

#[test]
fn exported_empty_class_uses_an_unrelated_constructor_owner() {
    let files = inputs(
        concat!(
            "export class NumberedItem extends CreateItem {}\n",
            "export const item = new NumberedItem(7);\n",
            "export const serial: number = item.serial;\n",
            "export const tag: string = NumberedItem.tag;\n",
        ),
        Some(ITEM_PROVIDER),
    );
    let mut context = context(&files);
    let owner = symbol(&context, named_class(&context, "NumberedItem"));
    context.check_source_file(SOURCE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let factory = global(&context, "ItemFactory");
    let item = global(&context, "Item");
    assert_base(
        &context,
        &members,
        global(&context, "CreateItem"),
        factory,
        item,
    );
    let signatures = assert_inherited_signatures(&context, &members, factory);
    assert_eq!(signatures.len(), 1);
    let constructor = context.store().signature(signatures[0]).unwrap();
    assert_eq!(constructor.min_argument_count(), 1);
    assert_eq!(constructor.parameters().len(), 1);
    let intrinsic = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(
        context
            .store()
            .value_symbol_links(constructor.parameters()[0])
            .unwrap()
            .resolved_type,
        Some(intrinsic.number_type)
    );
    assert_member(
        &context,
        &members,
        item,
        "serial",
        intrinsic.number_type,
        false,
    );
    assert_member(
        &context,
        &members,
        factory,
        "tag",
        intrinsic.string_type,
        true,
    );
    let calls = source_nodes(&context, SyntaxKind::NewExpression);
    assert_eq!(calls.len(), 1);
    assert_eq!(signature_at(&context, calls[0]), signatures[0]);
    assert_eq!(
        context.get_type_at_location(calls[0]).unwrap(),
        members.shells().instance_type()
    );
    replay(&mut context);
}

#[test]
fn inherited_constructor_errors_keep_argument_and_parameter_owners() {
    let files = inputs(
        concat!(
            "export class NumberedItem extends CreateItem {}\n",
            "declare const text: string;\n",
            "export const wrong = new NumberedItem(text);\n",
            "export const missing = new NumberedItem();\n",
        ),
        Some(ITEM_PROVIDER),
    );
    let mut context = context(&files);
    let owner = symbol(&context, named_class(&context, "NumberedItem"));
    context.check_source_file(SOURCE).unwrap();
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let signatures =
        assert_inherited_signatures(&context, &members, global(&context, "ItemFactory"));
    let calls = source_nodes(&context, SyntaxKind::NewExpression);
    assert_eq!(calls.len(), 2);
    let arena = context.file(SOURCE).unwrap().0;
    let NodeData::NewExpression(wrong) = &arena.get(calls[0].node).unwrap().data else {
        unreachable!()
    };
    let argument_node = reference(&context, SOURCE, wrong.arguments.as_ref().unwrap().nodes[0]);
    let [argument, arity] = context.diagnostics().as_slice() else {
        panic!("the inherited number parameter must reject the wrong and missing arguments")
    };
    assert_eq!(argument.diagnostic.code(), 2345);
    assert_eq!(
        argument.diagnostic.render().unwrap(),
        "Argument of type 'string' is not assignable to parameter of type 'number'."
    );
    assert_eq!(argument.node, Some(argument_node));
    assert_eq!(argument.range_override, None);
    assert!(argument.related_information.is_empty());
    assert_eq!(arity.diagnostic.code(), 2554);
    assert_eq!(
        arity.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 0."
    );
    assert_eq!(arity.node, Some(calls[1]));
    assert_eq!(arity.range_override, None);
    let [related] = arity.related_information.as_slice() else {
        panic!("the missing argument must identify its inherited parameter")
    };
    assert_eq!(related.diagnostic.code(), 6210);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument for 'serial' was not provided."
    );
    let parameter = context.store().signature(signatures[0]).unwrap().parameters()[0];
    let [declaration] = context
        .store()
        .symbol(parameter)
        .unwrap()
        .declarations()
        .unwrap()
    else {
        panic!("the inherited parameter must keep its one source declaration")
    };
    assert_eq!(declaration.file, PROVIDER);
    assert_eq!(related.node, Some(*declaration));
    for call in calls {
        assert_eq!(signature_at(&context, call), signatures[0]);
        assert_eq!(
            context.get_type_at_location(call).unwrap(),
            members.shells().instance_type()
        );
    }
    replay(&mut context);
}

#[test]
fn exported_empty_class_without_heritage_keeps_its_default_constructor() {
    let files = inputs("export class Empty {}\n", None);
    let mut context = context(&files);
    let owner = symbol(&context, named_class(&context, "Empty"));
    context.check_source_file(SOURCE).unwrap();
    assert!(context.diagnostics().is_empty());
    let store = context.store();
    let instance = store
        .declared_type_links(owner)
        .unwrap()
        .declared_type
        .unwrap();
    let value = store.value_symbol_links(owner).unwrap().resolved_type.unwrap();
    assert_ne!(instance, value);
    assert_eq!(store.type_payload(instance).unwrap().symbol(), Some(owner));
    let TypeData::Interface(instance_record) = store.type_payload(instance).unwrap().data() else {
        panic!("the empty class must keep its class instance")
    };
    assert!(instance_record.base_types_resolved);
    assert!(instance_record.resolved_base_types.is_none());
    assert_eq!(
        instance_record.resolved_base_constructor_type,
        Some(store.intrinsic_bootstrap().unwrap().undefined_type)
    );
    let signatures = construct_signatures(&context, value);
    assert_eq!(signatures.len(), 1);
    let constructor = store.signature(signatures[0]).unwrap();
    assert_eq!(constructor.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(constructor.declaration(), None);
    assert!(constructor.parameters().is_empty());
    assert_eq!(constructor.min_argument_count(), 0);
    assert_eq!(constructor.resolved_return_type(), Some(instance));
    replay(&mut context);
}
