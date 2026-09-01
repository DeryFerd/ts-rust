use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    DeclaredTypeLinks, IntrinsicBootstrapOptions, SignatureLinks, SourceFileLinks, SymbolNodeLinks,
    TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
    types::{ObjectFlags, TypeFlags},
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(68_420);
const FILE: FileId = FileId::new(68_421);
const LIBRARY: &str = "interface Array<T> {} interface ReadonlyArray<T> {}";

fn context<'a>(library: &'a ParseResult, source: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (parsed, file, path, declaration) in [
        (library, LIBRARY_FILE, "\"/project/lib.d.ts\"", true),
        (source, FILE, "\"/project/typed-fields.ts\"", false),
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
                    declaration,
                    declaration,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let context = CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY_FILE, &library.arena), (FILE, &source.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_property_initialization: true,
            no_implicit_any: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap();
    for (name, target) in [
        ("Array", context.global_types().array_type),
        ("ReadonlyArray", context.global_types().readonly_array_type),
    ] {
        let owner = context
            .store()
            .symbol_table(context.globals())
            .unwrap()
            .get_source(name)
            .unwrap();
        let record = context.store().symbol(owner).unwrap();
        assert_eq!(record.flags(), SymbolFlags::INTERFACE);
        let [declaration] = record.declarations().unwrap() else {
            panic!("each array target has one real library declaration")
        };
        assert!(declaration.is_for(library.arena.id(), LIBRARY_FILE));
        assert_eq!(
            context.file(LIBRARY_FILE).unwrap().1.symbol(*declaration),
            Some(owner)
        );
        assert_eq!(
            context
                .store()
                .declared_type_links(owner)
                .unwrap()
                .declared_type,
            Some(target)
        );
        assert_eq!(
            context.store().type_payload(target).unwrap().symbol(),
            Some(owner)
        );
    }
    context
}

fn reference(parsed: &ParseResult, node: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, node)
}

fn named(parsed: &ParseResult, kind: SyntaxKind, expected: &str) -> NodeRef {
    parsed.arena.iter().find_map(|(node, record)| {
        if record.kind != kind { return None; }
        let name = match &record.data {
            NodeData::ClassDeclaration(data) => data.name?,
            NodeData::InterfaceDeclaration(data) => data.name,
            NodeData::VariableDeclaration(data) => data.name,
            _ => return None,
        };
        matches!(&parsed.arena.get(name)?.data, NodeData::Identifier(name) if name.text == expected)
            .then_some(reference(parsed, node))
    }).unwrap_or_else(|| panic!("missing {kind:?} {expected}"))
}

#[derive(Clone, Copy)]
struct Field {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
    initializer: Option<NodeRef>,
}

fn field(parsed: &ParseResult, class: NodeRef, expected: &str) -> Field {
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        unreachable!()
    };
    data.members
        .nodes
        .iter()
        .find_map(|&node| {
            let NodeData::PropertyDeclaration(property) = &parsed.arena.get(node)?.data else {
                return None;
            };
            let name = match &parsed.arena.get(property.name)?.data {
                NodeData::Identifier(name) => &name.text,
                NodeData::PrivateIdentifier(name) => &name.text,
                _ => return None,
            };
            (name == expected).then(|| Field {
                declaration: reference(parsed, node),
                name: reference(parsed, property.name),
                annotation: reference(parsed, property.type_.unwrap()),
                initializer: property.initializer.map(|node| reference(parsed, node)),
            })
        })
        .unwrap_or_else(|| panic!("missing field {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn node_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing checked type at {node:?}"))
}

fn field_type(
    context: &mut CanonicalCheckerContext<'_>,
    owner: SemanticSymbolId,
    field: Field,
) -> TypeId {
    let property = symbol(context, field.declaration);
    let record = context.store().symbol(property).unwrap();
    assert_eq!(record.parent(), Some(owner));
    assert_eq!(record.declarations(), Some(&[field.declaration][..]));
    assert_eq!(record.value_declaration(), Some(field.declaration));
    assert_eq!(record.flags(), SymbolFlags::PROPERTY);
    assert_eq!(
        context
            .store()
            .symbol(owner)
            .unwrap()
            .members()
            .and_then(|table| context.store().symbol_table(table))
            .and_then(|table| table.get(record.name())),
        Some(property)
    );
    let type_ = context
        .store()
        .value_symbol_links(property)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_eq!(
        context.get_type_from_type_node(field.annotation).unwrap(),
        type_
    );
    type_
}

fn array_element(context: &CanonicalCheckerContext<'_>, type_: TypeId, readonly: bool) -> TypeId {
    let TypeData::TypeReference(data) = context.store().type_payload(type_).unwrap().data() else {
        panic!("the array must retain a canonical reference")
    };
    assert_eq!(
        data.object.target,
        Some(if readonly {
            context.global_types().readonly_array_type
        } else {
            context.global_types().array_type
        })
    );
    let [element] = data.resolved_type_arguments.as_deref().unwrap() else {
        panic!("the array has one real element type")
    };
    *element
}

fn assert_empty_initializer(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    node: NodeRef,
) -> TypeId {
    let record = parsed.arena.get(node.node).unwrap();
    let NodeData::ArrayLiteralExpression(array) = &record.data else {
        panic!("the original initializer must remain an array")
    };
    assert!(array.elements.nodes.is_empty());
    let type_ = node_type(context, node);
    assert_eq!(context.get_type_at_location(node).unwrap(), type_);
    assert_eq!(
        array_element(context, type_, false),
        context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .implicit_never_type
    );
    assert!(
        context
            .store()
            .type_payload(type_)
            .unwrap()
            .object_flags()
            .contains(ObjectFlags::ARRAY_LITERAL)
    );
    type_
}

fn object_property(parsed: &ParseResult, object: NodeRef, expected: &str) -> (NodeRef, NodeRef) {
    let NodeData::ObjectLiteralExpression(data) = &parsed.arena.get(object.node).unwrap().data
    else {
        panic!("the value must retain its written object")
    };
    data.properties.nodes.iter().find_map(|&node| {
        let NodeData::PropertyAssignment(property) = &parsed.arena.get(node)?.data else { return None; };
        matches!(&parsed.arena.get(property.name)?.data, NodeData::Identifier(name) if name.text == expected)
            .then_some((reference(parsed, property.name), reference(parsed, property.initializer)))
    }).unwrap_or_else(|| panic!("missing object property {expected}"))
}

fn object_property_type(
    context: &CanonicalCheckerContext<'_>,
    object: TypeId,
    name: &str,
) -> TypeId {
    let members = match context.store().type_payload(object).unwrap().data() {
        TypeData::Object(data) => data.structured.members,
        TypeData::Interface(data) => data.reference.object.structured.members,
        _ => panic!("the checked object must retain its member table"),
    };
    let property = context
        .store()
        .symbol_table(members.unwrap())
        .unwrap()
        .get_source(name)
        .unwrap();
    context
        .store()
        .value_symbol_links(property)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn check_source(context: &mut CanonicalCheckerContext<'_>, fields: &[Field], query_first: bool) {
    let early = query_first.then(|| {
        fields
            .iter()
            .map(|field| context.get_type_from_type_node(field.annotation).unwrap())
            .collect::<Vec<_>>()
    });
    assert!(
        context
            .store()
            .source_file_links(context.source_file(FILE).unwrap())
            .is_none_or(|links| !links.type_checked)
    );
    for field in fields {
        if let Some(initializer) = field.initializer {
            assert!(
                context
                    .store()
                    .type_node_links(initializer)
                    .and_then(|links| links.resolved_type)
                    .is_none()
            );
        }
    }
    context.check_source_file(FILE).unwrap();
    let checked = fields
        .iter()
        .map(|field| context.get_type_from_type_node(field.annotation).unwrap())
        .collect::<Vec<_>>();
    if let Some(early) = early {
        assert_eq!(checked, early);
    }
}

type NodePublication = (
    NodeRef,
    Option<TypeNodeLinks>,
    Option<SymbolNodeLinks>,
    Option<SignatureLinks>,
);
type SymbolPublication = (
    SemanticSymbolId,
    Option<DeclaredTypeLinks>,
    Option<ValueSymbolLinks>,
);

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 7],
    nodes: Vec<NodePublication>,
    symbols: Vec<SymbolPublication>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn publication(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Publication {
    let store = context.store();
    Publication {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        nodes: parsed
            .arena
            .iter()
            .map(|(node, _)| {
                let node = reference(parsed, node);
                (
                    node,
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.declared_type_links(symbol).cloned(),
                    store.value_symbol_links(symbol).cloned(),
                )
            })
            .collect(),
        source: store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    fields: &[Field],
) {
    let annotations = fields
        .iter()
        .map(|field| {
            (
                field.annotation,
                context.get_type_from_type_node(field.annotation).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    let initializers = fields
        .iter()
        .filter_map(|field| field.initializer)
        .map(|node| (node, context.get_type_at_location(node).unwrap()))
        .collect::<Vec<_>>();
    let warm = publication(context, parsed);
    context.check_source_file(FILE).unwrap();
    assert_eq!(publication(context, parsed), warm);
    context.recheck_source_file(FILE).unwrap();
    for (node, type_) in annotations {
        assert_eq!(context.get_type_from_type_node(node).unwrap(), type_);
    }
    for (node, type_) in initializers {
        assert_eq!(context.get_type_at_location(node).unwrap(), type_);
    }
    assert_eq!(publication(context, parsed), warm);
}

#[test]
#[allow(clippy::too_many_lines)] // Array declarations and initializer results share one source check.
fn typed_empty_arrays_keep_declared_elements_and_real_initializer_types() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(concat!(
        "class Arrays {\n",
        "  values: number[] = [];\n",
        "  private callbacks: (() => void)[] = [];\n",
        "  #hidden: string[] = [];\n",
        "  readonly frozen: readonly number[] = [];\n",
        "  optional?: number;\n",
        "  definite!: number;\n",
        "}\n",
    ));
    let class = named(&parsed, SyntaxKind::ClassDeclaration, "Arrays");
    let fields =
        ["values", "callbacks", "#hidden", "frozen"].map(|name| field(&parsed, class, name));
    for query_first in [false, true] {
        let mut context = context(&library, &parsed);
        let owner = symbol(&context, class);
        check_source(&mut context, &fields, query_first);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let declared = fields.map(|field| field_type(&mut context, owner, field));
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (number, string, void, undefined) = (
            bootstrap.number_type,
            bootstrap.string_type,
            bootstrap.void_type,
            bootstrap.undefined_type,
        );
        assert_eq!(array_element(&context, declared[0], false), number);
        assert_eq!(array_element(&context, declared[2], false), string);
        assert_eq!(array_element(&context, declared[3], true), number);
        let callback = array_element(&context, declared[1], false);
        let TypeData::Object(callable) = context.store().type_payload(callback).unwrap().data()
        else {
            panic!("the array element must retain its written function type")
        };
        assert_eq!(callable.structured.call_signature_count, 1);
        let [signature] = callable.structured.signatures.as_deref().unwrap() else {
            panic!("the callback has one signature")
        };
        assert_eq!(
            context
                .store()
                .signature(*signature)
                .unwrap()
                .resolved_return_type(),
            Some(void)
        );
        for (field, declared) in fields.iter().zip(declared) {
            let initializer = field.initializer.unwrap();
            assert_eq!(
                parsed.arena.get(initializer.node).unwrap().parent,
                Some(field.declaration.node)
            );
            assert_ne!(
                assert_empty_initializer(&mut context, &parsed, initializer),
                declared
            );
        }
        let private = context
            .store()
            .symbol(symbol(&context, fields[2].declaration))
            .unwrap();
        assert!(private.name().is_private_identifier());
        assert!(
            context
                .store()
                .symbol(symbol(&context, fields[3].declaration))
                .unwrap()
                .check_flags()
                .contains(CheckFlags::READONLY)
        );
        let optional = field(&parsed, class, "optional");
        let optional_symbol = symbol(&context, optional.declaration);
        assert_eq!(
            context.store().symbol(optional_symbol).unwrap().flags(),
            SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL
        );
        let optional_type = context
            .store()
            .value_symbol_links(optional_symbol)
            .unwrap()
            .resolved_type
            .unwrap();
        let TypeData::Union(union) = context.store().type_payload(optional_type).unwrap().data()
        else {
            panic!("an optional number keeps undefined under strict null checking")
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&number) && union.union.types.contains(&undefined));
        assert!(optional.initializer.is_none());
        let definite = field(&parsed, class, "definite");
        assert!(definite.initializer.is_none());
        assert_eq!(field_type(&mut context, owner, definite), number);
        assert_replay(&mut context, &parsed, &fields);
    }
}

#[test]
fn typed_objects_and_identifiers_keep_context_and_original_bindings() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(concat!(
        "type State = { kind: 'ready' | 'busy'; index: number };\n",
        "declare const initial: State;\n",
        "declare const text: string;\n",
        "class Values {\n",
        "  #context: State = { kind: 'ready', index: 0 };\n",
        "  state: State = initial;\n",
        "  private label: string = text;\n",
        "  maybe: string | undefined = undefined;\n",
        "}\n",
    ));
    let class = named(&parsed, SyntaxKind::ClassDeclaration, "Values");
    let fields = ["#context", "state", "label", "maybe"].map(|name| field(&parsed, class, name));
    for query_first in [false, true] {
        let mut context = context(&library, &parsed);
        let owner = symbol(&context, class);
        check_source(&mut context, &fields, query_first);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let declared = fields.map(|field| field_type(&mut context, owner, field));
        assert_eq!(declared[0], declared[1]);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (number, string, undefined, ready) = (
            bootstrap.number_type,
            bootstrap.string_type,
            bootstrap.undefined_type,
            bootstrap.cached_string_literal_type("ready").unwrap(),
        );
        let object = fields[0].initializer.unwrap();
        let object_type = node_type(&context, object);
        assert_ne!(object_type, declared[0]);
        assert!(
            context
                .store()
                .type_payload(object_type)
                .unwrap()
                .object_flags()
                .contains(ObjectFlags::FRESH_LITERAL)
        );
        assert_eq!(object_property_type(&context, object_type, "kind"), ready);
        assert_eq!(object_property_type(&context, object_type, "index"), number);
        let kind = object_property_type(&context, declared[0], "kind");
        let TypeData::Union(union) = context.store().type_payload(kind).unwrap().data() else {
            panic!("the field keeps its declared kind union")
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&ready));
        for (field, name, type_) in [
            (fields[1], "initial", declared[1]),
            (fields[2], "text", string),
        ] {
            let initializer = field.initializer.unwrap();
            let binding = symbol(
                &context,
                named(&parsed, SyntaxKind::VariableDeclaration, name),
            );
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(initializer)
                    .unwrap()
                    .resolved_symbol,
                Some(binding)
            );
            assert_eq!(node_type(&context, initializer), type_);
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(binding)
                    .unwrap()
                    .resolved_type,
                Some(type_)
            );
        }
        assert_eq!(declared[2], string);
        assert_eq!(
            node_type(&context, fields[3].initializer.unwrap()),
            undefined
        );
        let TypeData::Union(union) = context.store().type_payload(declared[3]).unwrap().data()
        else {
            panic!("the annotated field keeps string and undefined")
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&string) && union.union.types.contains(&undefined));
        assert_replay(&mut context, &parsed, &fields);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // The two same-named formals must retain separate class owners.
fn generic_typed_fields_keep_each_real_class_formal() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(concat!(
        "class Box<T> {\n",
        "  values: T[] = [];\n",
        "  #hidden: T[] = [];\n",
        "  state: { values: T[] } = { values: [] };\n",
        "  maybe: T | undefined = undefined;\n",
        "}\n",
        "class Other<T> { values: T[] = []; }\n",
    ));
    let class = named(&parsed, SyntaxKind::ClassDeclaration, "Box");
    let other = named(&parsed, SyntaxKind::ClassDeclaration, "Other");
    let fields = [
        field(&parsed, class, "values"),
        field(&parsed, class, "#hidden"),
        field(&parsed, class, "state"),
        field(&parsed, class, "maybe"),
        field(&parsed, other, "values"),
    ];
    for query_first in [false, true] {
        let mut context = context(&library, &parsed);
        check_source(&mut context, &fields, query_first);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let mut formals = Vec::new();
        for class in [class, other] {
            let owner = symbol(&context, class);
            let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data
            else {
                unreachable!()
            };
            let [parameter] = data.type_parameters.as_ref().unwrap().nodes.as_slice() else {
                panic!("the class keeps one written formal")
            };
            let parameter = reference(&parsed, *parameter);
            let parameter_owner = symbol(&context, parameter);
            let formal = context
                .get_declared_type_of_symbol(parameter_owner)
                .unwrap();
            assert_eq!(
                context.store().symbol(parameter_owner).unwrap().parent(),
                Some(owner)
            );
            assert_eq!(
                context
                    .store()
                    .symbol(parameter_owner)
                    .unwrap()
                    .declarations(),
                Some(&[parameter][..])
            );
            let record = context.store().type_payload(formal).unwrap();
            assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
            assert_eq!(record.symbol(), Some(parameter_owner));
            let TypeData::TypeParameter(data) = record.data() else {
                unreachable!()
            };
            assert!(!data.is_this_type);
            assert!(data.target.is_none() && data.mapper.is_none());
            let instance = context.get_declared_type_of_symbol(owner).unwrap();
            let members = context.get_nongeneric_class_members(owner).unwrap();
            assert_eq!(members.shells().instance_type(), instance);
            let TypeData::Interface(data) = context.store().type_payload(instance).unwrap().data()
            else {
                panic!("the generic class retains its real origin")
            };
            assert_eq!(
                data.reference.resolved_type_arguments.as_deref(),
                Some(&[formal][..])
            );
            let this = data.this_type.unwrap();
            assert_ne!(this, formal);
            assert_eq!(
                data.all_type_parameters.as_deref(),
                Some(&[formal, this][..])
            );
            formals.push(formal);
        }
        assert_ne!(formals[0], formals[1]);
        let owner = symbol(&context, class);
        let declared = fields[..4]
            .iter()
            .map(|&field| field_type(&mut context, owner, field))
            .collect::<Vec<_>>();
        assert_eq!(array_element(&context, declared[0], false), formals[0]);
        assert_eq!(declared[0], declared[1]);
        assert_eq!(
            array_element(
                &context,
                object_property_type(&context, declared[2], "values"),
                false
            ),
            formals[0]
        );
        let other_owner = symbol(&context, other);
        let other_type = field_type(&mut context, other_owner, fields[4]);
        assert_eq!(array_element(&context, other_type, false), formals[1]);
        assert_ne!(declared[0], other_type);
        for field in [fields[0], fields[1], fields[4]] {
            assert_empty_initializer(&mut context, &parsed, field.initializer.unwrap());
        }
        let object = fields[2].initializer.unwrap();
        let nested = object_property(&parsed, object, "values").1;
        let nested_type = assert_empty_initializer(&mut context, &parsed, nested);
        assert_eq!(
            object_property_type(&context, node_type(&context, object), "values"),
            nested_type
        );
        let undefined = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_type;
        let TypeData::Union(union) = context.store().type_payload(declared[3]).unwrap().data()
        else {
            panic!("the generic field keeps its formal and undefined")
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&formals[0]) && union.union.types.contains(&undefined));
        assert_eq!(
            node_type(&context, fields[3].initializer.unwrap()),
            undefined
        );
        assert_replay(&mut context, &parsed, &fields);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Each initializer error retains its type, source node and replay state.
fn invalid_typed_initializers_keep_exact_errors_and_declared_types() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(concat!(
        "interface State { index: number }\n",
        "declare const text: string;\n",
        "class Bad {\n",
        "  count: number = text;\n",
        "  notArray: number = [];\n",
        "  state: State = { index: text };\n",
        "  missing: number;\n",
        "  optional?: number;\n",
        "  definite!: number;\n",
        "}\n",
    ));
    let class = named(&parsed, SyntaxKind::ClassDeclaration, "Bad");
    let fields = ["count", "notArray", "state", "missing", "definite"]
        .map(|name| field(&parsed, class, name));
    let object_name = object_property(&parsed, fields[2].initializer.unwrap(), "index").0;
    let interface = named(&parsed, SyntaxKind::InterfaceDeclaration, "State");
    let NodeData::InterfaceDeclaration(data) = &parsed.arena.get(interface.node).unwrap().data
    else {
        unreachable!()
    };
    let NodeData::PropertyDeclaration(property) =
        &parsed.arena.get(data.members.nodes[0]).unwrap().data
    else {
        unreachable!()
    };
    let expected_name = reference(&parsed, property.name);
    for query_first in [false, true] {
        let mut context = context(&library, &parsed);
        check_source(&mut context, &fields, query_first);
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 4, "{diagnostics:?}");
        for (node, source, target) in [
            (fields[0].name, "string", "number"),
            (fields[1].name, "never[]", "number"),
            (object_name, "string", "number"),
        ] {
            let diagnostic = diagnostics
                .iter()
                .find(|diagnostic| diagnostic.node == Some(node))
                .unwrap();
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(diagnostic.diagnostic.arguments, [source, target]);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                format!("Type '{source}' is not assignable to type '{target}'.")
            );
            assert!(diagnostic.range_override.is_none());
            if node == object_name {
                let [related] = diagnostic.related_information.as_slice() else {
                    panic!("the member error keeps its real expected-property declaration")
                };
                assert_eq!(related.node, Some(expected_name));
                assert_eq!(related.diagnostic.code(), 6500);
                assert_eq!(related.diagnostic.arguments, ["index", "State"]);
                assert_eq!(
                    related.diagnostic.render().unwrap(),
                    "The expected type comes from property 'index' which is declared here on type 'State'"
                );
            } else {
                assert!(diagnostic.related_information.is_empty());
            }
        }
        let missing = diagnostics
            .iter()
            .find(|diagnostic| diagnostic.node == Some(fields[3].name))
            .unwrap();
        assert_eq!(missing.diagnostic.code(), 2564);
        assert_eq!(missing.diagnostic.arguments, ["missing"]);
        assert_eq!(
            missing.diagnostic.render().unwrap(),
            "Property 'missing' has no initializer and is not definitely assigned in the constructor."
        );
        assert!(missing.range_override.is_none() && missing.related_information.is_empty());
        let owner = symbol(&context, class);
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        for field in [fields[0], fields[1], fields[3], fields[4]] {
            assert_eq!(field_type(&mut context, owner, field), number);
        }
        let target = field_type(&mut context, owner, fields[2]);
        assert_eq!(
            context.store().type_payload(target).unwrap().symbol(),
            Some(symbol(&context, interface))
        );
        assert_eq!(object_property_type(&context, target, "index"), number);
        assert_empty_initializer(&mut context, &parsed, fields[1].initializer.unwrap());
        let text = symbol(
            &context,
            named(&parsed, SyntaxKind::VariableDeclaration, "text"),
        );
        for initializer in [
            fields[0].initializer.unwrap(),
            object_property(&parsed, fields[2].initializer.unwrap(), "index").1,
        ] {
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(initializer)
                    .unwrap()
                    .resolved_symbol,
                Some(text)
            );
            assert_eq!(
                node_type(&context, initializer),
                context.store().intrinsic_bootstrap().unwrap().string_type
            );
        }
        assert_replay(&mut context, &parsed, &fields);
    }
}
