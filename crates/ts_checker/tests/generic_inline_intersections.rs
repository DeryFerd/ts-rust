use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, TypeData, TypeId,
    type_records::{IntersectionTypeData, ObjectTypeData},
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(99_140);
const SOURCE_FILE: FileId = FileId::new(99_141);
// The local Noop declaration isolates mapping from the separate property-import provider.
const SOURCE: &str = concat!(
    "export type Noop = () => void;\n",
    "export type Observer<T> = { next: (value: T) => void; };\n",
    "export type Subscription = { unsubscribe: Noop; };\n",
    "export type Subject<T> = {\n",
    "  readonly observers: Observer<T>[];\n",
    "  subscribe: (value: Observer<T>) => Subscription;\n",
    "  unsubscribe: Noop;\n",
    "} & Observer<T>;\n",
    "export type Wrapped<U> = Subject<U>;\n",
    "declare const text: Subject<string>;\n",
    "declare const count: Wrapped<number>;\n",
    "export declare function preserve<T>(value: Subject<T>): Subject<T>;\n",
);

fn context<'a>(library: &'a ParseResult, source: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (parsed, file, path, declaration, module_state) in [
        (
            library,
            LIBRARY,
            "\"/project/lib.d.ts\"",
            true,
            CanonicalModuleState::Script,
        ),
        (
            source,
            SOURCE_FILE,
            "\"/project/inline-intersections.ts\"",
            false,
            CanonicalModuleState::External,
        ),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY, &library.arena), (SOURCE_FILE, &source.arena)],
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn declaration(source: &ParseResult, name: &str) -> NodeRef {
    source
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name_node = match &record.data {
                NodeData::TypeAliasDeclaration(data) => data.name,
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::FunctionDeclaration(data) => data.name?,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &source.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(source.arena.id(), SOURCE_FILE, node))
        })
        .unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    context
        .store()
        .get_merged_symbol(context.file(node.file).unwrap().1.symbol(node).unwrap())
        .unwrap()
}

fn annotation(source: &ParseResult, name: &str) -> NodeRef {
    let node = declaration(source, name);
    let NodeData::VariableDeclaration(variable) = &source.arena.get(node.node).unwrap().data else {
        panic!("expected a typed variable")
    };
    NodeRef::new(node.arena, node.file, variable.type_.unwrap())
}

fn object<'store>(
    context: &'store CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'store ObjectTypeData {
    let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data() else {
        panic!("expected a source object")
    };
    object
}

fn intersection<'store>(
    context: &'store CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'store IntersectionTypeData {
    let TypeData::Intersection(intersection) = context.store().type_payload(type_).unwrap().data()
    else {
        panic!("expected the original intersection")
    };
    intersection
}

fn parameter(context: &CanonicalCheckerContext<'_>, alias: SemanticSymbolId) -> TypeId {
    let [parameter] = context
        .store()
        .type_alias_links(alias)
        .unwrap()
        .type_parameters
        .as_deref()
        .unwrap()
    else {
        panic!("expected one alias-owned parameter")
    };
    *parameter
}

fn assert_alias(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    owner: SemanticSymbolId,
    argument: TypeId,
) {
    let alias = context
        .store()
        .type_payload(type_)
        .unwrap()
        .alias()
        .and_then(|alias| context.store().type_alias(alias))
        .unwrap();
    assert_eq!(alias.symbol(), Some(owner));
    assert_eq!(alias.type_arguments(), Some([argument].as_slice()));
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 6] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.type_alias_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

#[test]
#[allow(clippy::too_many_lines)] // The original and mapped objects must keep separate owners and display arguments.
fn inline_intersection_queries_keep_literal_owner_and_visible_alias_arguments() {
    let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
    let source = parse_source_file(SOURCE);
    let mut context = context(&library, &source);
    let subject_owner = symbol(&context, declaration(&source, "Subject"));
    let observer_owner = symbol(&context, declaration(&source, "Observer"));
    let wrapped_owner = symbol(&context, declaration(&source, "Wrapped"));
    let subject = context.get_declared_type_of_symbol(subject_owner).unwrap();
    let observer = context.get_declared_type_of_symbol(observer_owner).unwrap();
    let subject_parameter = parameter(&context, subject_owner);
    let observer_parameter = parameter(&context, observer_owner);
    assert_ne!(subject_parameter, observer_parameter);
    assert_alias(&context, subject, subject_owner, subject_parameter);
    let [inline, inherited] = intersection(&context, subject)
        .intersection
        .types
        .as_slice()
    else {
        panic!("Subject has an inline literal and an Observer reference")
    };
    let (inline, inherited) = (*inline, *inherited);
    let subject_node = declaration(&source, "Subject");
    let NodeData::TypeAliasDeclaration(alias) = &source.arena.get(subject_node.node).unwrap().data
    else {
        unreachable!()
    };
    let NodeData::IntersectionTypeNode(intersection_node) =
        &source.arena.get(alias.type_).unwrap().data
    else {
        unreachable!()
    };
    let literal = NodeRef::new(
        subject_node.arena,
        subject_node.file,
        intersection_node.types.nodes[0],
    );
    assert_eq!(
        context.store().type_payload(inline).unwrap().symbol(),
        Some(symbol(&context, literal))
    );
    assert!(
        context
            .store()
            .type_payload(inline)
            .unwrap()
            .alias()
            .is_none()
    );
    assert_eq!(object(&context, inline).target, None);
    assert_eq!(object(&context, inline).mapper, None);
    assert!(object(&context, inline).structured.properties.is_none());
    assert_eq!(
        context
            .store()
            .type_node_links(literal)
            .unwrap()
            .outer_type_parameters
            .as_deref(),
        Some([subject_parameter].as_slice())
    );
    assert_eq!(object(&context, inherited).target, Some(observer));
    assert_eq!(
        context.store().map_type(
            object(&context, inherited).mapper.unwrap(),
            observer_parameter
        ),
        Some(subject_parameter)
    );

    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let mut resolved = Vec::new();
    for (name, owner, argument) in [
        ("text", subject_owner, string),
        ("count", wrapped_owner, number),
    ] {
        let node = annotation(&source, name);
        let result = context.get_type_from_type_node(node).unwrap();
        assert_alias(&context, result, owner, argument);
        let [mapped_inline, mapped_observer] =
            intersection(&context, result).intersection.types.as_slice()
        else {
            panic!("mapping keeps both original constituents")
        };
        assert_eq!(object(&context, *mapped_inline).target, Some(inline));
        assert!(
            context
                .store()
                .type_payload(*mapped_inline)
                .unwrap()
                .alias()
                .is_none()
        );
        assert_eq!(
            context.store().map_type(
                object(&context, *mapped_inline).mapper.unwrap(),
                subject_parameter
            ),
            Some(argument)
        );
        assert_eq!(object(&context, *mapped_observer).target, Some(observer));
        assert_eq!(
            context.store().map_type(
                object(&context, *mapped_observer).mapper.unwrap(),
                observer_parameter
            ),
            Some(argument)
        );
        assert!(
            intersection(&context, result)
                .intersection
                .structured
                .properties
                .is_none()
        );
        resolved.push((node, result));
    }
    let NodeData::TypeLiteralNode(literal_node) = &source.arena.get(literal.node).unwrap().data
    else {
        unreachable!()
    };
    for property in &literal_node.members.nodes {
        let node = NodeRef::new(literal.arena, literal.file, *property);
        let NodeData::PropertyDeclaration(property) = &source.arena.get(*property).unwrap().data
        else {
            panic!("the source uses property signatures")
        };
        assert!(
            context
                .store()
                .value_symbol_links(symbol(&context, node))
                .is_none()
        );
        assert!(
            context
                .store()
                .type_node_links(NodeRef::new(node.arena, node.file, property.type_.unwrap()))
                .is_none()
        );
    }
    let warm = counts(&context);
    for _ in 0..2 {
        assert_eq!(
            context.get_declared_type_of_symbol(subject_owner).unwrap(),
            subject
        );
        for &(node, result) in &resolved {
            assert_eq!(context.get_type_from_type_node(node).unwrap(), result);
        }
        assert_eq!(counts(&context), warm);
    }
    assert!(context.diagnostics().is_empty());
}

#[test]
fn generic_callable_intersection_queries_keep_separate_parameter_owners() {
    for source_first in [false, true] {
        let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        let source = parse_source_file(SOURCE);
        let mut context = context(&library, &source);
        if source_first {
            context.check_source_file(SOURCE_FILE).unwrap();
        }
        let function = declaration(&source, "preserve");
        let callable = context.get_type_at_location(function).unwrap();
        let [signature] = object(&context, callable)
            .structured
            .signatures
            .as_deref()
            .unwrap()
        else {
            panic!("the function has one source-owned signature")
        };
        let signature = *signature;
        let callable_parameter = context
            .store()
            .signature(signature)
            .unwrap()
            .type_parameters()[0];
        let value = context.store().signature(signature).unwrap().parameters()[0];
        let argument = context
            .store()
            .value_symbol_links(value)
            .unwrap()
            .resolved_type
            .unwrap();
        let subject_owner = symbol(&context, declaration(&source, "Subject"));
        let observer_owner = symbol(&context, declaration(&source, "Observer"));
        assert_ne!(callable_parameter, parameter(&context, subject_owner));
        assert_ne!(callable_parameter, parameter(&context, observer_owner));
        assert_alias(&context, argument, subject_owner, callable_parameter);
        assert_eq!(
            context.get_return_type_of_signature(signature).unwrap(),
            argument
        );
        context.check_source_file(SOURCE_FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let warm = counts(&context);
        for _ in 0..2 {
            assert_eq!(context.get_type_at_location(function).unwrap(), callable);
            assert_eq!(
                context.get_return_type_of_signature(signature).unwrap(),
                argument
            );
            context.recheck_source_file(SOURCE_FILE).unwrap();
            assert_eq!(counts(&context), warm);
            assert!(context.diagnostics().is_empty());
        }
    }
}
