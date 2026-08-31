use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    DeclaredTypeError, DeclaredTypeLinks, IntrinsicBootstrapOptions, SignatureId, SignatureLinks,
    SourceCheckError, SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeMapperId,
    TypeNodeLinks, TypeNodeUnavailable, UnsupportedSourceSyntax, ValueSymbolLinks,
    signatures::SignatureFlags, types::TypeFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_101);

// These local controls do not execute Query's imports or generic construction.
fn context(parsed: &ParseResult, module: CanonicalModuleState) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic-class-bodies.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                module,
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
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_function_types: true,
            strict_property_initialization: true,
            no_implicit_any: true,
            no_implicit_this: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn reference(parsed: &ParseResult, node: ts_ast::NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, node)
}

fn named(parsed: &ParseResult, kind: SyntaxKind, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::ClassDeclaration(data) => data.name?,
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::VariableDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(reference(parsed, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {expected}"))
}

fn class_parameters(parsed: &ParseResult, class: NodeRef) -> Vec<NodeRef> {
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        panic!("expected the actual class declaration")
    };
    data.type_parameters
        .as_ref()
        .map(|parameters| {
            parameters
                .nodes
                .iter()
                .map(|&node| reference(parsed, node))
                .collect()
        })
        .unwrap_or_default()
}

fn member(parsed: &ParseResult, class: NodeRef, expected: &str) -> NodeRef {
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        panic!("expected the actual class declaration")
    };
    data.members
        .nodes
        .iter()
        .find_map(|&node| {
            let name = match &parsed.arena.get(node)?.data {
                NodeData::MethodDeclaration(data) => data.name,
                NodeData::PropertyDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(reference(parsed, node))
        })
        .unwrap_or_else(|| panic!("missing class member {expected}"))
}

fn constructor(parsed: &ParseResult, class: NodeRef) -> NodeRef {
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        panic!("expected the actual class declaration")
    };
    let constructors = data
        .members
        .nodes
        .iter()
        .filter(|&&node| parsed.arena.get(node).unwrap().kind == SyntaxKind::Constructor)
        .map(|&node| reference(parsed, node))
        .collect::<Vec<_>>();
    let [constructor] = constructors.as_slice() else {
        panic!("the class must retain one written constructor")
    };
    *constructor
}

fn parameters(parsed: &ParseResult, declaration: NodeRef) -> Vec<NodeRef> {
    let parameters = match &parsed.arena.get(declaration.node).unwrap().data {
        NodeData::ConstructorDeclaration(data) => &data.parameters,
        NodeData::MethodDeclaration(data) => &data.parameters,
        _ => panic!("expected a constructor or ordinary method"),
    };
    parameters
        .nodes
        .iter()
        .map(|&node| reference(parsed, node))
        .collect()
}

fn annotation(parsed: &ParseResult, declaration: NodeRef) -> NodeRef {
    let type_ = match &parsed.arena.get(declaration.node).unwrap().data {
        NodeData::PropertyDeclaration(data) => data.type_,
        NodeData::ParameterDeclaration(data) => data.type_,
        NodeData::MethodDeclaration(data) => data.type_,
        NodeData::VariableDeclaration(data) => data.type_,
        _ => panic!("expected an actual annotated declaration"),
    };
    reference(
        parsed,
        type_.expect("the declaration must keep its written annotation"),
    )
}

fn initializer(parsed: &ParseResult, expected: &str) -> NodeRef {
    let variable = named(parsed, SyntaxKind::VariableDeclaration, expected);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(variable.node).unwrap().data else {
        unreachable!()
    };
    reference(parsed, data.initializer.unwrap())
}

fn returned(parsed: &ParseResult, method: NodeRef) -> (NodeRef, NodeRef) {
    let NodeData::MethodDeclaration(data) = &parsed.arena.get(method.node).unwrap().data else {
        panic!("expected an ordinary method")
    };
    let NodeData::Block(body) = &parsed.arena.get(data.body.unwrap()).unwrap().data else {
        panic!("the method must retain its written body")
    };
    body.statements
        .nodes
        .iter()
        .find_map(|&node| {
            let NodeData::ReturnStatement(data) = &parsed.arena.get(node)?.data else {
                return None;
            };
            Some((reference(parsed, node), reference(parsed, data.expression?)))
        })
        .expect("the method must retain its actual return")
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the declaration or call must retain its exact signature")
}

fn value_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn query_annotations(
    context: &mut CanonicalCheckerContext<'_>,
    annotations: &[NodeRef],
) -> Vec<(NodeRef, TypeId)> {
    annotations
        .iter()
        .map(|&node| (node, context.get_type_from_type_node(node).unwrap()))
        .collect()
}

fn check_source(
    context: &mut CanonicalCheckerContext<'_>,
    annotations: &[NodeRef],
    query_first: bool,
) -> Vec<(NodeRef, TypeId)> {
    let early = query_first.then(|| query_annotations(context, annotations));
    assert!(
        context
            .store()
            .source_file_links(context.source_file(FILE).unwrap())
            .is_none_or(|links| !links.type_checked)
    );
    context.check_source_file(FILE).unwrap();
    let checked = query_annotations(context, annotations);
    if let Some(early) = early {
        assert_eq!(checked, early);
    }
    checked
}

struct Origin {
    owner: SemanticSymbolId,
    instance: TypeId,
    value: TypeId,
    parameters: Vec<TypeId>,
    this: TypeId,
    constructor: SignatureId,
}

fn assert_origin(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    class: NodeRef,
) -> Origin {
    let owner = symbol(context, class);
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let instance = context.get_declared_type_of_symbol(owner).unwrap();
    assert_eq!(members.shells().declaration(), class);
    assert_eq!(members.shells().symbol(), owner);
    assert_eq!(members.shells().instance_type(), instance);
    assert_eq!(value_type(context, owner), members.shells().value_type());
    let mut formals = Vec::new();
    for parameter in class_parameters(parsed, class) {
        assert_eq!(
            parsed.arena.get(parameter.node).unwrap().parent,
            Some(class.node)
        );
        let owner_parameter = symbol(context, parameter);
        let type_ = context
            .get_declared_type_of_symbol(owner_parameter)
            .unwrap();
        let store = context.store();
        assert_eq!(store.symbol(owner_parameter).unwrap().parent(), Some(owner));
        assert_eq!(
            store.symbol(owner_parameter).unwrap().declarations(),
            Some(&[parameter][..])
        );
        let record = store.type_payload(type_).unwrap();
        assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
        assert_eq!(record.symbol(), Some(owner_parameter));
        let TypeData::TypeParameter(data) = record.data() else {
            panic!("the source formal must keep its declared type")
        };
        assert!(!data.is_this_type);
        assert_eq!(data.target, None);
        assert_eq!(data.mapper, None);
        formals.push(type_);
    }
    let store = context.store();
    let TypeData::Interface(data) = store.type_payload(instance).unwrap().data() else {
        panic!("the class origin must retain interface storage")
    };
    assert_eq!(data.outer_type_parameter_count, 0);
    assert_eq!(data.reference.object.target, Some(instance));
    assert_eq!(
        data.reference.resolved_type_arguments.as_deref(),
        Some(formals.as_slice())
    );
    let this = data.this_type.unwrap();
    let mut all = formals.clone();
    all.push(this);
    assert_eq!(data.all_type_parameters.as_deref(), Some(all.as_slice()));
    let TypeData::TypeParameter(this_data) = store.type_payload(this).unwrap().data() else {
        panic!("the class must keep its separate synthetic this")
    };
    assert!(this_data.is_this_type);
    assert_eq!(this_data.constraint, Some(instance));
    let declaration = constructor(parsed, class);
    let constructor = signature(context, declaration);
    assert_eq!(constructor, members.default_construct_signature());
    let record = store.signature(constructor).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(record.type_parameters(), formals.as_slice());
    assert_eq!(record.resolved_return_type(), Some(instance));
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(
        record.parameters(),
        parameters(parsed, declaration)
            .into_iter()
            .map(|parameter| symbol(context, parameter))
            .collect::<Vec<_>>()
    );
    Origin {
        owner,
        instance,
        value: members.shells().value_type(),
        parameters: formals,
        this,
        constructor,
    }
}

fn assert_method(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    origin: &Origin,
    method: NodeRef,
    expected_parameters: &[TypeId],
    expected_return: TypeId,
) -> (TypeId, SignatureId) {
    let owner = symbol(context, method);
    let source_parameters = parameters(parsed, method);
    let parameter_symbols = source_parameters
        .iter()
        .map(|&parameter| symbol(context, parameter))
        .collect::<Vec<_>>();
    for (&parameter, &expected) in source_parameters.iter().zip(expected_parameters) {
        assert_eq!(
            context.get_type_from_type_node(annotation(parsed, parameter)),
            Ok(expected)
        );
        assert_eq!(value_type(context, symbol(context, parameter)), expected);
    }
    let callable = value_type(context, owner);
    let declared = signature(context, method);
    assert_eq!(context.get_type_at_location(method), Ok(callable));
    assert_eq!(
        context.get_return_type_of_signature(declared),
        Ok(expected_return)
    );
    let store = context.store();
    let member = store.symbol(owner).unwrap();
    assert_eq!(member.flags(), SymbolFlags::METHOD);
    assert_eq!(member.parent(), Some(origin.owner));
    assert_eq!(member.declarations(), Some(&[method][..]));
    assert_eq!(member.value_declaration(), Some(method));
    let record = store.signature(declared).unwrap();
    assert_eq!(record.declaration(), Some(method));
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.parameters(), parameter_symbols);
    assert_eq!(record.parameters().len(), expected_parameters.len());
    assert_eq!(
        record.min_argument_count(),
        i32::try_from(expected_parameters.len()).unwrap()
    );
    assert_eq!(record.resolved_return_type(), Some(expected_return));
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    let TypeData::Object(data) = store.type_payload(callable).unwrap().data() else {
        panic!("the original method must retain its callable object")
    };
    assert_eq!(data.target, None);
    assert_eq!(data.mapper, None);
    assert_eq!(data.structured.call_signature_count, 1);
    assert_eq!(data.structured.signatures.as_deref(), Some(&[declared][..]));
    (callable, declared)
}

fn reference_arguments(
    context: &CanonicalCheckerContext<'_>,
    reference: TypeId,
    target: TypeId,
) -> Vec<TypeId> {
    let TypeData::TypeReference(data) = context.store().type_payload(reference).unwrap().data()
    else {
        panic!("the actual annotation must keep its applied reference")
    };
    assert_eq!(data.object.target, Some(target));
    data.resolved_type_arguments.clone().unwrap()
}

fn assert_field_copy(
    context: &CanonicalCheckerContext<'_>,
    origin: &Origin,
    field: SemanticSymbolId,
    receiver: TypeId,
    argument: TypeId,
) -> (SemanticSymbolId, TypeMapperId) {
    let store = context.store();
    let TypeData::TypeReference(data) = store.type_payload(receiver).unwrap().data() else {
        panic!("the concrete receiver must remain a class reference")
    };
    assert_eq!(data.object.target, Some(origin.instance));
    assert_eq!(
        data.resolved_type_arguments.as_deref(),
        Some(&[argument][..])
    );
    let original = store.symbol(field).unwrap();
    let copied = store
        .symbol_table(data.object.structured.members.unwrap())
        .unwrap()
        .get_source(original.name().as_utf8().unwrap())
        .unwrap();
    assert_ne!(copied, field);
    let record = store.symbol(copied).unwrap();
    assert_eq!(record.flags(), original.flags() | SymbolFlags::TRANSIENT);
    assert_eq!(
        record.check_flags(),
        original.check_flags() | CheckFlags::INSTANTIATED
    );
    assert_eq!(record.parent(), original.parent());
    assert_eq!(record.declarations(), original.declarations());
    let links = store.value_symbol_links(copied).unwrap();
    assert_eq!(links.target, Some(field));
    assert_eq!(links.resolved_type, Some(argument));
    let mapper = links.mapper.unwrap();
    assert_eq!(store.map_type(mapper, origin.parameters[0]), Some(argument));
    assert_eq!(store.map_type(mapper, origin.this), Some(receiver));
    assert_eq!(value_type(context, field), origin.parameters[0]);
    (copied, mapper)
}

#[derive(Debug, Eq, PartialEq)]
struct CopiedMethod {
    member: SemanticSymbolId,
    callable: TypeId,
    signature: SignatureId,
    mapper: TypeMapperId,
}

#[allow(clippy::too_many_arguments)] // One receiver call proves its source and copied signature together.
fn assert_receiver_method(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    origin: &Origin,
    method: NodeRef,
    call: NodeRef,
    receiver: TypeId,
    argument: TypeId,
    expected_return: TypeId,
) -> CopiedMethod {
    let NodeData::CallExpression(invocation) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("the source must keep its actual method call")
    };
    let access = reference(parsed, invocation.expression);
    let NodeData::PropertyAccessExpression(access_data) =
        &parsed.arena.get(access.node).unwrap().data
    else {
        panic!("the call must use its written receiver")
    };
    assert_eq!(
        context.get_type_at_location(reference(parsed, access_data.expression)),
        Ok(receiver)
    );
    let callable = context.get_type_at_location(access).unwrap();
    let copied_member = context
        .get_symbol_at_location(reference(parsed, access_data.name))
        .unwrap()
        .unwrap();
    assert_eq!(context.get_type_at_location(call), Ok(expected_return));
    let original_member = symbol(context, method);
    let original_type = value_type(context, original_member);
    let original_signature = signature(context, method);
    let store = context.store();
    let TypeData::Object(data) = store.type_payload(callable).unwrap().data() else {
        panic!("the selected member must retain its copied callable")
    };
    assert_ne!(callable, original_type);
    assert_eq!(data.target, Some(original_type));
    let mapper = data.mapper.unwrap();
    assert_eq!(store.map_type(mapper, origin.parameters[0]), Some(argument));
    assert_eq!(store.map_type(mapper, origin.this), Some(receiver));
    let copied_links = store.value_symbol_links(copied_member).unwrap();
    assert_ne!(copied_member, original_member);
    assert_eq!(copied_links.target, Some(original_member));
    assert_eq!(copied_links.mapper, Some(mapper));
    assert_eq!(copied_links.resolved_type, Some(callable));
    assert_eq!(data.structured.call_signature_count, 1);
    let [copied] = data.structured.signatures.as_deref().unwrap() else {
        panic!("an ordinary method must keep its single copied signature")
    };
    let copied = *copied;
    assert_eq!(signature(context, call), copied);
    let record = store.signature(copied).unwrap();
    assert_ne!(copied, original_signature);
    assert_eq!(record.target(), Some(original_signature));
    assert_eq!(record.mapper(), Some(mapper));
    assert_eq!(record.declaration(), Some(method));
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert_eq!(record.resolved_return_type(), Some(expected_return));
    let original = store.signature(original_signature).unwrap();
    assert_eq!(record.min_argument_count(), original.min_argument_count());
    assert_eq!(record.parameters().len(), original.parameters().len());
    for (&parameter, &source) in record.parameters().iter().zip(original.parameters()) {
        assert_ne!(parameter, source);
        let links = store.value_symbol_links(parameter).unwrap();
        assert_eq!(links.target, Some(source));
        assert_eq!(links.mapper, Some(mapper));
        assert_eq!(links.resolved_type, Some(argument));
        assert_eq!(value_type(context, source), origin.parameters[0]);
    }
    CopiedMethod {
        member: copied_member,
        callable,
        signature: copied,
        mapper,
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
    annotations: &[(NodeRef, TypeId)],
    locations: &[(NodeRef, TypeId)],
) {
    for &(node, expected) in locations {
        assert_eq!(context.get_type_at_location(node), Ok(expected));
    }
    let warm = publication(context, parsed);
    for _ in 0..2 {
        context.check_source_file(FILE).unwrap();
        assert_eq!(publication(context, parsed), warm);
        context.recheck_source_file(FILE).unwrap();
        for &(node, expected) in annotations {
            assert_eq!(context.get_type_from_type_node(node), Ok(expected));
        }
        for &(node, expected) in locations {
            assert_eq!(context.get_type_at_location(node), Ok(expected));
        }
        assert_eq!(publication(context, parsed), warm);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Both query orders retain one exported class's complete formal and signature rows.
fn generic_class_bodies_keep_exported_formals_defaults_and_constructor_identity() {
    let parsed = parse_source_file(concat!(
        "interface Packet<T> { value: T; }\n",
        "export class RecordBox<\n",
        "  TValue = number, TError = string, TData = TValue,\n",
        "  TKey extends string = string, TExtra = Packet<TValue>,\n",
        "> {\n",
        "  value: TValue;\n",
        "  constructor(value: TValue) { this.value = value; }\n",
        "  read(): TValue { return this.value; }\n",
        "  replace(next: TValue): TValue { this.value = next; return this.value; }\n",
        "}\n",
        "declare const defaulted: RecordBox;\n",
        "declare const specialized: RecordBox<string>;\n",
    ));
    let class = named(&parsed, SyntaxKind::ClassDeclaration, "RecordBox");
    let field = member(&parsed, class, "value");
    let read = member(&parsed, class, "read");
    let replace = member(&parsed, class, "replace");
    let annotations = [
        annotation(&parsed, field),
        annotation(&parsed, parameters(&parsed, constructor(&parsed, class))[0]),
        annotation(&parsed, read),
        annotation(&parsed, parameters(&parsed, replace)[0]),
        annotation(
            &parsed,
            named(&parsed, SyntaxKind::VariableDeclaration, "defaulted"),
        ),
        annotation(
            &parsed,
            named(&parsed, SyntaxKind::VariableDeclaration, "specialized"),
        ),
    ];
    for query_first in [false, true] {
        let mut context = context(&parsed, CanonicalModuleState::External);
        let mut queried = check_source(&mut context, &annotations, query_first);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let origin = assert_origin(&mut context, &parsed, class);
        assert_eq!(origin.parameters.len(), 5);
        let bound = context.file(FILE).unwrap().1;
        let local = context
            .store()
            .get_merged_symbol(bound.local_symbol(class).unwrap())
            .unwrap();
        let module = bound.symbol(bound.source_file()).unwrap();
        assert_ne!(local, origin.owner);
        assert_eq!(
            context.store().symbol(local).unwrap().export_symbol(),
            Some(origin.owner)
        );
        assert_eq!(
            context.store().symbol(local).unwrap().flags(),
            SymbolFlags::EXPORT_VALUE
        );
        assert_eq!(
            context.store().symbol(origin.owner).unwrap().parent(),
            Some(module)
        );
        assert_eq!(
            context
                .store()
                .symbol(module)
                .unwrap()
                .exports()
                .and_then(|table| context.store().symbol_table(table))
                .and_then(|table| table.get_source("RecordBox")),
            Some(origin.owner)
        );
        let first = origin.parameters[0];
        assert_eq!(
            queried[..4]
                .iter()
                .map(|(_, type_)| *type_)
                .collect::<Vec<_>>(),
            vec![first; 4]
        );
        assert_eq!(value_type(&context, symbol(&context, field)), first);
        assert_method(&mut context, &parsed, &origin, read, &[], first);
        assert_method(&mut context, &parsed, &origin, replace, &[first], first);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let packet_owner = symbol(
            &context,
            named(&parsed, SyntaxKind::InterfaceDeclaration, "Packet"),
        );
        let packet = context.get_declared_type_of_symbol(packet_owner).unwrap();
        let formal_nodes = class_parameters(&parsed, class);
        let defaults = formal_nodes
            .iter()
            .map(|parameter| {
                let NodeData::TypeParameterDeclaration(data) =
                    &parsed.arena.get(parameter.node).unwrap().data
                else {
                    panic!("the class list must retain actual type parameter declarations")
                };
                let node = reference(&parsed, data.default_type.unwrap());
                let type_ = context.get_type_from_type_node(node).unwrap();
                queried.push((node, type_));
                type_
            })
            .collect::<Vec<_>>();
        assert_eq!(&defaults[..4], &[number, string, first, string]);
        assert_eq!(reference_arguments(&context, defaults[4], packet), [first]);
        for (&formal, &default) in origin.parameters.iter().zip(&defaults) {
            let TypeData::TypeParameter(data) =
                context.store().type_payload(formal).unwrap().data()
            else {
                unreachable!()
            };
            assert_eq!(data.resolved_default_type, Some(default));
        }
        let TypeData::TypeParameter(key) = context
            .store()
            .type_payload(origin.parameters[3])
            .unwrap()
            .data()
        else {
            unreachable!()
        };
        assert_eq!(key.constraint, Some(string));
        let defaulted = reference_arguments(&context, queried[4].1, origin.instance);
        let specialized = reference_arguments(&context, queried[5].1, origin.instance);
        assert_eq!(&defaulted[..4], &[number, string, number, string]);
        assert_eq!(&specialized[..4], &[string, string, string, string]);
        assert_eq!(defaulted.len(), 5);
        assert_eq!(specialized.len(), 5);
        assert_eq!(
            reference_arguments(&context, defaulted[4], packet),
            [number]
        );
        assert_eq!(
            reference_arguments(&context, specialized[4], packet),
            [string]
        );
        assert_ne!(defaulted[4], specialized[4]);
        assert_replay(
            &mut context,
            &parsed,
            &queried,
            &[
                (returned(&parsed, read).1, first),
                (returned(&parsed, replace).1, first),
            ],
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Real calls compare both receiver maps with their unchanged origin.
fn generic_class_receiver_calls_keep_two_maps_and_ordinary_method_signatures() {
    let parsed = parse_source_file(concat!(
        "class Box<T> {\n",
        "  value: T;\n",
        "  constructor(value: T) { this.value = value; }\n",
        "  read(): T { return this.value; }\n",
        "  replace(next: T): T { this.value = next; return next; }\n",
        "  self() { return this; }\n",
        "}\n",
        "declare const text: Box<string>;\n",
        "declare const numeric: Box<number>;\n",
        "declare const textValue: string;\n",
        "declare const numberValue: number;\n",
        "const textField: string = text.value;\n",
        "const numberField: number = numeric.value;\n",
        "const textResult: string = text.replace(textValue);\n",
        "const numberResult: number = numeric.replace(numberValue);\n",
        "const textRead: string = text.read();\n",
        "const numberRead: number = numeric.read();\n",
        "const textSelf: Box<string> = text.self();\n",
        "const numberSelf: Box<number> = numeric.self();\n",
    ));
    let class = named(&parsed, SyntaxKind::ClassDeclaration, "Box");
    let field = member(&parsed, class, "value");
    let annotations = [
        annotation(&parsed, field),
        annotation(
            &parsed,
            named(&parsed, SyntaxKind::VariableDeclaration, "text"),
        ),
        annotation(
            &parsed,
            named(&parsed, SyntaxKind::VariableDeclaration, "numeric"),
        ),
    ];
    for query_first in [false, true] {
        let mut context = context(&parsed, CanonicalModuleState::Script);
        let queried = check_source(&mut context, &annotations, query_first);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let origin = assert_origin(&mut context, &parsed, class);
        assert_eq!(origin.parameters, [queried[0].1]);
        let original_parameter = origin.parameters[0];
        let read = member(&parsed, class, "read");
        let replace = member(&parsed, class, "replace");
        let self_method = member(&parsed, class, "self");
        assert_method(
            &mut context,
            &parsed,
            &origin,
            read,
            &[],
            original_parameter,
        );
        assert_method(
            &mut context,
            &parsed,
            &origin,
            replace,
            &[original_parameter],
            original_parameter,
        );
        assert_method(
            &mut context,
            &parsed,
            &origin,
            self_method,
            &[],
            origin.this,
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let text = queried[1].1;
        let numeric = queried[2].1;
        assert_ne!(text, numeric);
        assert_eq!(
            reference_arguments(&context, text, origin.instance),
            [string]
        );
        assert_eq!(
            reference_arguments(&context, numeric, origin.instance),
            [number]
        );
        let original_field = symbol(&context, field);
        let text_field = assert_field_copy(&context, &origin, original_field, text, string);
        let numeric_field = assert_field_copy(&context, &origin, original_field, numeric, number);
        assert_ne!(text_field.0, numeric_field.0);
        assert_ne!(text_field.1, numeric_field.1);
        let text_method = assert_receiver_method(
            &mut context,
            &parsed,
            &origin,
            replace,
            initializer(&parsed, "textResult"),
            text,
            string,
            string,
        );
        let numeric_method = assert_receiver_method(
            &mut context,
            &parsed,
            &origin,
            replace,
            initializer(&parsed, "numberResult"),
            numeric,
            number,
            number,
        );
        assert_ne!(text_method.member, numeric_method.member);
        assert_ne!(text_method.callable, numeric_method.callable);
        assert_ne!(text_method.signature, numeric_method.signature);
        assert_ne!(text_method.mapper, numeric_method.mapper);
        for (name, method, receiver, argument, expected) in [
            ("textRead", read, text, string, string),
            ("numberRead", read, numeric, number, number),
            ("textSelf", self_method, text, string, text),
            ("numberSelf", self_method, numeric, number, numeric),
        ] {
            assert_receiver_method(
                &mut context,
                &parsed,
                &origin,
                method,
                initializer(&parsed, name),
                receiver,
                argument,
                expected,
            );
        }
        let locations = [
            (initializer(&parsed, "textField"), string),
            (initializer(&parsed, "numberField"), number),
            (initializer(&parsed, "textResult"), string),
            (initializer(&parsed, "numberResult"), number),
            (initializer(&parsed, "textRead"), string),
            (initializer(&parsed, "numberRead"), number),
            (initializer(&parsed, "textSelf"), text),
            (initializer(&parsed, "numberSelf"), numeric),
        ];
        for (name, expected) in [
            ("textField", text_field.0),
            ("numberField", numeric_field.0),
        ] {
            let access = initializer(&parsed, name);
            let NodeData::PropertyAccessExpression(data) =
                &parsed.arena.get(access.node).unwrap().data
            else {
                unreachable!()
            };
            assert_eq!(
                context.get_symbol_at_location(reference(&parsed, data.name)),
                Ok(Some(expected))
            );
        }
        assert_replay(&mut context, &parsed, &queried, &locations);
        assert_eq!(value_type(&context, original_field), original_parameter);
        assert_eq!(
            context
                .store()
                .signature(signature(&context, replace))
                .unwrap()
                .type_parameters(),
            []
        );
        assert_eq!(
            context
                .store()
                .signature(origin.constructor)
                .unwrap()
                .type_parameters(),
            [original_parameter]
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the body, call, and visibility errors in their actual source order.
fn generic_class_bodies_keep_exact_body_and_mapped_argument_diagnostics() {
    let parsed = parse_source_file(concat!(
        "class Box<T> {\n",
        "  value: T;\n",
        "  private hidden: T;\n",
        "  protected saved: T;\n",
        "  constructor(value: T) { this.value = value; this.hidden = value; this.saved = value; }\n",
        "  read(value: T): T { return value; }\n",
        "  wrong(value: string): number { return value; }\n",
        "}\n",
        "declare const numeric: Box<number>;\n",
        "declare const text: string;\n",
        "const result: number = numeric.read(text);\n",
        "const hidden: number = numeric.hidden;\n",
        "const saved: number = numeric.saved;\n",
    ));
    let class = named(&parsed, SyntaxKind::ClassDeclaration, "Box");
    let read = member(&parsed, class, "read");
    let wrong = member(&parsed, class, "wrong");
    let call = initializer(&parsed, "result");
    let NodeData::CallExpression(invocation) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    let [argument] = invocation.arguments.nodes.as_slice() else {
        panic!("the call must keep its one declared string argument")
    };
    let argument = reference(&parsed, *argument);
    let visibility_nodes = ["hidden", "saved"].map(|name| {
        let access = initializer(&parsed, name);
        let NodeData::PropertyAccessExpression(data) = &parsed.arena.get(access.node).unwrap().data
        else {
            panic!("the visibility error must keep its real property access")
        };
        reference(&parsed, data.name)
    });
    let annotations = [
        annotation(&parsed, parameters(&parsed, read)[0]),
        annotation(
            &parsed,
            named(&parsed, SyntaxKind::VariableDeclaration, "numeric"),
        ),
    ];
    for query_first in [false, true] {
        let mut context = context(&parsed, CanonicalModuleState::Script);
        let queried = check_source(&mut context, &annotations, query_first);
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 4, "{diagnostics:?}");
        for (diagnostic, code, node, message) in [
            (
                &diagnostics[0],
                2322,
                returned(&parsed, wrong).0,
                "Type 'string' is not assignable to type 'number'.",
            ),
            (
                &diagnostics[1],
                2345,
                argument,
                "Argument of type 'string' is not assignable to parameter of type 'number'.",
            ),
            (
                &diagnostics[2],
                2341,
                visibility_nodes[0],
                "Property 'hidden' is private and only accessible within class 'Box<T>'.",
            ),
            (
                &diagnostics[3],
                2445,
                visibility_nodes[1],
                "Property 'saved' is protected and only accessible within class 'Box<T>' and its subclasses.",
            ),
        ] {
            assert_eq!(diagnostic.diagnostic.code(), code);
            assert_eq!(diagnostic.node, Some(node));
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
            assert!(diagnostic.diagnostic.details.is_empty());
            assert!(diagnostic.related_information.is_empty());
        }
        let origin = assert_origin(&mut context, &parsed, class);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        assert_method(
            &mut context,
            &parsed,
            &origin,
            read,
            &origin.parameters,
            origin.parameters[0],
        );
        assert_method(&mut context, &parsed, &origin, wrong, &[string], number);
        assert_receiver_method(
            &mut context,
            &parsed,
            &origin,
            read,
            call,
            queried[1].1,
            number,
            number,
        );
        assert_replay(
            &mut context,
            &parsed,
            &queried,
            &[
                (call, number),
                (argument, string),
                (returned(&parsed, wrong).1, string),
                (initializer(&parsed, "hidden"), number),
                (initializer(&parsed, "saved"), number),
            ],
        );
    }
    assert_static_class_parameter_stays_unavailable();
}

fn assert_static_class_parameter_stays_unavailable() {
    let parsed = parse_source_file("class Static<T> { static invalid(value: T): void {} }");
    let class = named(&parsed, SyntaxKind::ClassDeclaration, "Static");
    let method = member(&parsed, class, "invalid");
    let parameter = parameters(&parsed, method)[0];
    let type_node = annotation(&parsed, parameter);
    assert_eq!(
        parsed.arena.get(type_node.node).unwrap().kind,
        SyntaxKind::TypeReference
    );
    assert_eq!(
        parsed.arena.get(type_node.node).unwrap().parent,
        Some(parameter.node)
    );
    let type_error = DeclaredTypeError::TypeNodeUnavailable(
        TypeNodeUnavailable::MissingTypeReference(type_node),
    );
    let source_error = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Class(method));
    for query_first in [false, true] {
        let mut context = context(&parsed, CanonicalModuleState::Script);
        let owner = symbol(&context, class);
        let cold = publication(&context, &parsed);
        if query_first {
            assert_eq!(context.get_type_from_type_node(type_node), Err(type_error));
            assert_eq!(publication(&context, &parsed), cold);
        }
        for _ in 0..2 {
            assert_eq!(context.check_source_file(FILE), Err(source_error));
            assert_eq!(publication(&context, &parsed), cold);
            assert_eq!(context.get_type_from_type_node(type_node), Err(type_error));
            assert_eq!(publication(&context, &parsed), cold);
            assert_eq!(context.recheck_source_file(FILE), Err(source_error));
            assert_eq!(publication(&context, &parsed), cold);
            assert!(context.store().declared_type_links(owner).is_none());
            assert!(context.store().value_symbol_links(owner).is_none());
            assert!(context.diagnostics().is_empty());
        }
    }
}

#[allow(clippy::too_many_lines)] // The constructor and instance-super views share one applied base proof.
fn assert_applied_base(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    base: &Origin,
    derived_class: NodeRef,
    derived: &Origin,
    argument: TypeId,
) -> Vec<(NodeRef, TypeId)> {
    let TypeData::Interface(data) = context
        .store()
        .type_payload(derived.instance)
        .unwrap()
        .data()
    else {
        panic!("the derived class must keep its actual origin")
    };
    let [applied] = data.resolved_base_types.as_deref().unwrap() else {
        panic!("the class must keep its one written base")
    };
    let applied = *applied;
    assert_ne!(applied, base.instance);
    assert_eq!(
        reference_arguments(context, applied, base.instance),
        [argument]
    );
    let declaration = constructor(parsed, derived_class);
    let NodeData::ConstructorDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let NodeData::Block(body) = &parsed.arena.get(data.body.unwrap()).unwrap().data else {
        panic!("the derived constructor must retain its written body")
    };
    let [statement] = body.statements.nodes.as_slice() else {
        panic!("the constructor must retain its one super call")
    };
    let NodeData::ExpressionStatement(statement) = &parsed.arena.get(*statement).unwrap().data
    else {
        panic!("the constructor statement must remain an expression")
    };
    let call = reference(parsed, statement.expression);
    let NodeData::CallExpression(invocation) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("the expression must remain the original super call")
    };
    let callee = reference(parsed, invocation.expression);
    assert_eq!(
        parsed.arena.get(callee.node).unwrap().kind,
        SyntaxKind::SuperKeyword
    );
    let selected = signature(context, call);
    let store = context.store();
    let original = store.signature(base.constructor).unwrap();
    let copied = store.signature(selected).unwrap();
    assert_ne!(selected, base.constructor);
    assert_eq!(copied.target(), Some(base.constructor));
    assert_eq!(copied.declaration(), original.declaration());
    assert_eq!(copied.flags(), SignatureFlags::CONSTRUCT);
    assert!(copied.type_parameters().is_empty());
    assert_eq!(copied.resolved_return_type(), Some(applied));
    assert_eq!(original.resolved_return_type(), Some(base.instance));
    assert_eq!(original.type_parameters(), base.parameters.as_slice());
    let mapper = copied.mapper().unwrap();
    assert_eq!(store.map_type(mapper, base.parameters[0]), Some(argument));
    let [parameter] = copied.parameters() else {
        panic!("the applied constructor must retain its one copied parameter")
    };
    let [source] = original.parameters() else {
        panic!("the base constructor must retain its original parameter")
    };
    assert_ne!(parameter, source);
    let links = store.value_symbol_links(*parameter).unwrap();
    assert_eq!(links.target, Some(*source));
    assert_eq!(links.mapper, Some(mapper));
    assert_eq!(links.resolved_type, Some(argument));
    assert_eq!(value_type(context, *source), base.parameters[0]);
    let void = store.intrinsic_bootstrap().unwrap().void_type;
    assert_eq!(context.get_type_at_location(callee), Ok(base.value));
    assert_eq!(context.get_type_at_location(call), Ok(void));
    let mut locations = vec![(callee, base.value), (call, void)];
    let base_class = context
        .store()
        .symbol(base.owner)
        .unwrap()
        .value_declaration()
        .unwrap();
    for (own_name, base_name, result) in [
        ("fromBase", "read", argument),
        ("fromSelf", "self", derived.this),
    ] {
        let method = member(parsed, derived_class, own_name);
        assert_method(context, parsed, derived, method, &[], result);
        let call = returned(parsed, method).1;
        let NodeData::CallExpression(invocation) = &parsed.arena.get(call.node).unwrap().data
        else {
            panic!("the return must keep its real super method call")
        };
        let access = reference(parsed, invocation.expression);
        let NodeData::PropertyAccessExpression(property) =
            &parsed.arena.get(access.node).unwrap().data
        else {
            panic!("the call must keep its super receiver")
        };
        let receiver = reference(parsed, property.expression);
        assert_eq!(
            parsed.arena.get(receiver.node).unwrap().kind,
            SyntaxKind::SuperKeyword
        );
        let receiver_type = context.get_type_at_location(receiver).unwrap();
        assert_eq!(
            reference_arguments(context, receiver_type, base.instance),
            [argument, derived.this]
        );
        let base_method = member(parsed, base_class, base_name);
        let original_member = symbol(context, base_method);
        let original_type = value_type(context, original_member);
        let original_signature = signature(context, base_method);
        let callable = context.get_type_at_location(access).unwrap();
        assert_eq!(
            context.get_symbol_at_location(reference(parsed, property.name)),
            Ok(Some(original_member))
        );
        let TypeData::Object(data) = context.store().type_payload(callable).unwrap().data() else {
            panic!("super must retain its actual mapped callable")
        };
        assert_eq!(data.target, Some(original_type));
        let mapper = data.mapper.unwrap();
        assert_eq!(
            context.store().map_type(mapper, base.parameters[0]),
            Some(argument)
        );
        assert_eq!(
            context.store().map_type(mapper, base.this),
            Some(derived.this)
        );
        let selected = signature(context, call);
        assert_eq!(data.structured.signatures.as_deref(), Some(&[selected][..]));
        let record = context.store().signature(selected).unwrap();
        assert_eq!(record.target(), Some(original_signature));
        assert_eq!(record.mapper(), Some(mapper));
        assert_eq!(record.declaration(), Some(base_method));
        assert!(record.type_parameters().is_empty());
        assert_eq!(record.resolved_return_type(), Some(result));
        assert_eq!(context.get_type_at_location(call), Ok(result));
        locations.extend([
            (receiver, receiver_type),
            (access, callable),
            (call, result),
        ]);
    }
    locations
}

#[test]
#[allow(clippy::too_many_lines)] // Both child arities share the original base, calls, and receiver proofs.
fn generic_class_applied_bases_keep_nested_arguments_and_zero_formal_children() {
    let parsed = parse_source_file(concat!(
        "interface Packet<T> { value: T; }\n",
        "class Base<T> {\n",
        "  value: T;\n",
        "  constructor(value: T) { this.value = value; }\n",
        "  read(): T { return this.value; }\n",
        "  self() { return this; }\n",
        "}\n",
        "class Wrapped<\n",
        "  A = number, B = string, C = A, D extends string = string, E = boolean,\n",
        "> extends Base<Packet<C>> {\n",
        "  constructor(value: Packet<C>) { super(value); }\n",
        "  fromBase(): Packet<C> { return super.read(); }\n",
        "  fromSelf() { return super.self(); }\n",
        "}\n",
        "class TextBox extends Base<string> {\n",
        "  constructor(value: string) { super(value); }\n",
        "  fromBase(): string { return super.read(); }\n",
        "  fromSelf() { return super.self(); }\n",
        "}\n",
        "declare const nested: Wrapped<number>;\n",
        "declare const plain: TextBox;\n",
        "const nestedValue: Packet<number> = nested.fromBase();\n",
        "const plainValue: string = plain.fromBase();\n",
        "const inheritedNested: Packet<number> = nested.read();\n",
        "const inheritedPlain: string = plain.read();\n",
        "const nestedSelf: Wrapped<number> = nested.fromSelf();\n",
        "const plainSelf: TextBox = plain.fromSelf();\n",
        "const nestedField: Packet<number> = nested.value;\n",
        "const plainField: string = plain.value;\n",
    ));
    let base_class = named(&parsed, SyntaxKind::ClassDeclaration, "Base");
    let wrapped_class = named(&parsed, SyntaxKind::ClassDeclaration, "Wrapped");
    let plain_class = named(&parsed, SyntaxKind::ClassDeclaration, "TextBox");
    let base_field = member(&parsed, base_class, "value");
    let annotations = [
        annotation(&parsed, base_field),
        annotation(
            &parsed,
            parameters(&parsed, constructor(&parsed, wrapped_class))[0],
        ),
        annotation(
            &parsed,
            named(&parsed, SyntaxKind::VariableDeclaration, "nested"),
        ),
        annotation(
            &parsed,
            named(&parsed, SyntaxKind::VariableDeclaration, "plain"),
        ),
        annotation(
            &parsed,
            named(&parsed, SyntaxKind::VariableDeclaration, "nestedValue"),
        ),
    ];
    for query_first in [false, true] {
        let mut context = context(&parsed, CanonicalModuleState::Script);
        let queried = check_source(&mut context, &annotations, query_first);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let base = assert_origin(&mut context, &parsed, base_class);
        let wrapped = assert_origin(&mut context, &parsed, wrapped_class);
        let plain = assert_origin(&mut context, &parsed, plain_class);
        assert_eq!(base.parameters, [queried[0].1]);
        assert_eq!(wrapped.parameters.len(), 5);
        assert!(plain.parameters.is_empty());
        let original_parameter = base.parameters[0];
        assert_method(
            &mut context,
            &parsed,
            &base,
            member(&parsed, base_class, "read"),
            &[],
            original_parameter,
        );
        assert_method(
            &mut context,
            &parsed,
            &base,
            member(&parsed, base_class, "self"),
            &[],
            base.this,
        );
        let packet_symbol = symbol(
            &context,
            named(&parsed, SyntaxKind::InterfaceDeclaration, "Packet"),
        );
        let packet = context.get_declared_type_of_symbol(packet_symbol).unwrap();
        let packet_of_formal = queried[1].1;
        assert_eq!(
            reference_arguments(&context, packet_of_formal, packet),
            [wrapped.parameters[2]]
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let boolean = bootstrap.boolean_type;
        let nested = queried[2].1;
        assert_eq!(
            reference_arguments(&context, nested, wrapped.instance),
            [number, string, number, string, boolean]
        );
        assert_eq!(queried[3].1, plain.instance);
        let packet_of_number = queried[4].1;
        assert_eq!(
            reference_arguments(&context, packet_of_number, packet),
            [number]
        );
        assert_ne!(packet_of_formal, packet_of_number);
        let mut locations = assert_applied_base(
            &mut context,
            &parsed,
            &base,
            wrapped_class,
            &wrapped,
            packet_of_formal,
        );
        locations.extend(assert_applied_base(
            &mut context,
            &parsed,
            &base,
            plain_class,
            &plain,
            string,
        ));
        for (name, declaring_class, method_name, expected) in [
            ("nestedValue", wrapped_class, "fromBase", packet_of_number),
            ("plainValue", plain_class, "fromBase", string),
            ("inheritedNested", base_class, "read", packet_of_number),
            ("inheritedPlain", base_class, "read", string),
            ("nestedSelf", wrapped_class, "fromSelf", nested),
            ("plainSelf", plain_class, "fromSelf", plain.instance),
        ] {
            let call = initializer(&parsed, name);
            assert_eq!(context.get_type_at_location(call), Ok(expected));
            let selected = signature(&context, call);
            assert_eq!(context.get_return_type_of_signature(selected), Ok(expected));
            let record = context.store().signature(selected).unwrap();
            assert_eq!(
                record.declaration(),
                Some(member(&parsed, declaring_class, method_name))
            );
            assert!(record.type_parameters().is_empty());
            locations.push((call, expected));
        }
        locations.extend([
            (initializer(&parsed, "nestedField"), packet_of_number),
            (initializer(&parsed, "plainField"), string),
        ]);
        assert_eq!(
            value_type(&context, symbol(&context, base_field)),
            original_parameter
        );
        assert_replay(&mut context, &parsed, &queried, &locations);
        assert_eq!(
            value_type(&context, symbol(&context, base_field)),
            original_parameter
        );
        assert_eq!(
            context
                .store()
                .signature(base.constructor)
                .unwrap()
                .resolved_return_type(),
            Some(base.instance)
        );
    }
}
