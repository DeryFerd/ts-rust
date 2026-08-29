use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SignatureId, TypeData, TypeId,
    type_records::ObjectTypeData,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(45_290);
const OBSERVER: &str = "export type Observer<T> = { next: (value: T) => void; }; ";

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/property-alias-callables.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::External,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(FILE, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn declaration(parsed: &ParseResult, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name_node = match &record.data {
                NodeData::TypeAliasDeclaration(data) => data.name,
                NodeData::VariableDeclaration(data) => data.name,
                NodeData::FunctionDeclaration(data) => data.name?,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap()
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    context
        .store()
        .get_merged_symbol(context.file(FILE).unwrap().1.symbol(node).unwrap())
        .unwrap()
}

fn object<'context>(
    context: &'context CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'context ObjectTypeData {
    let TypeData::Object(object) = context.store().type_payload(type_).unwrap().data() else {
        panic!("expected the real anonymous object")
    };
    object
}

fn value_type(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let object = object(context, type_);
    assert_eq!(object.structured.call_signature_count, 1);
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected one source-owned call signature")
    };
    *signature
}

fn member(context: &CanonicalCheckerContext<'_>, receiver: TypeId) -> SemanticSymbolId {
    context
        .store()
        .symbol_table(object(context, receiver).structured.members.unwrap())
        .unwrap()
        .get_source("next")
        .unwrap()
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

fn assert_mapped_next(
    context: &CanonicalCheckerContext<'_>,
    target: TypeId,
    receiver: TypeId,
    argument: TypeId,
) -> TypeId {
    let source_property = context
        .store()
        .type_payload(target)
        .unwrap()
        .symbol()
        .and_then(|owner| context.store().symbol(owner))
        .and_then(ts_binder::semantic::Symbol::members)
        .and_then(|members| context.store().symbol_table(members))
        .and_then(|members| members.get_source("next"))
        .unwrap();
    let source = value_type(context, source_property);
    let proxy = member(context, receiver);
    let actual = value_type(context, proxy);
    let mapper = object(context, receiver).mapper.unwrap();
    let source_signature = signature(context, source);
    let actual_signature = signature(context, actual);
    let copied = context.store().signature(actual_signature).unwrap();
    assert_ne!(proxy, source_property);
    assert_ne!(actual, source);
    assert_eq!(
        context.store().symbol(proxy).unwrap().flags(),
        SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
    );
    assert_eq!(object(context, actual).target, Some(source));
    assert_eq!(object(context, actual).mapper, Some(mapper));
    assert_eq!(copied.target(), Some(source_signature));
    assert_eq!(copied.mapper(), Some(mapper));
    assert_eq!(
        copied.declaration(),
        context
            .store()
            .signature(source_signature)
            .unwrap()
            .declaration(),
    );
    assert!(copied.type_parameters().is_empty());
    assert_eq!(copied.parameters().len(), 1);
    assert_eq!(value_type(context, copied.parameters()[0]), argument);
    assert_eq!(
        copied.resolved_return_type(),
        Some(context.store().intrinsic_bootstrap().unwrap().void_type),
    );
    actual
}

#[test]
fn observer_next_maps_each_alias_instance_and_replays_without_growth() {
    for reverse in [false, true] {
        let parsed = parse_source_file(&format!(
            "{OBSERVER} declare const text: Observer<string>; \
             declare const count: Observer<number>; text.next('ok'); count.next(1);",
        ));
        let mut context = context(&parsed);
        let alias = symbol(&context, declaration(&parsed, "Observer"));
        let target = context.get_declared_type_of_symbol(alias).unwrap();
        let parameters = context
            .store()
            .type_alias_links(alias)
            .unwrap()
            .type_parameters
            .clone()
            .unwrap();
        let annotations = ["text", "count"].map(|name| {
            let node = declaration(&parsed, name);
            let NodeData::VariableDeclaration(variable) =
                &parsed.arena.get(node.node).unwrap().data
            else {
                unreachable!()
            };
            NodeRef::new(parsed.arena.id(), FILE, variable.type_.unwrap())
        });
        let mut receivers = [None, None];
        for index in if reverse { [1, 0] } else { [0, 1] } {
            receivers[index] = Some(context.get_type_from_type_node(annotations[index]).unwrap());
        }
        let receivers = receivers.map(Option::unwrap);
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let arguments = [bootstrap.string_type, bootstrap.number_type];
        let actual = [0, 1]
            .map(|index| assert_mapped_next(&context, target, receivers[index], arguments[index]));
        assert_ne!(actual[0], actual[1]);
        let source = object(&context, actual[0]).target.unwrap();
        let source_signature = signature(&context, source);
        let source_parameter = context
            .store()
            .signature(source_signature)
            .unwrap()
            .parameters()[0];
        assert_eq!(value_type(&context, source_parameter), parameters[0]);
        assert_eq!(
            context.type_to_string(actual[0]).unwrap(),
            "(value: string) => void"
        );
        assert_eq!(
            context.type_to_string(actual[1]).unwrap(),
            "(value: number) => void"
        );
        let before = counts(&context);
        context.recheck_source_file(FILE).unwrap();
        for index in [0, 1] {
            assert_eq!(
                context.get_type_from_type_node(annotations[index]),
                Ok(receivers[index]),
            );
            assert_eq!(
                assert_mapped_next(&context, target, receivers[index], arguments[index]),
                actual[index],
            );
        }
        assert_eq!(counts(&context), before);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn observer_next_keeps_the_enclosing_function_type_parameter() {
    let parsed = parse_source_file(&format!(
        "{OBSERVER} export function emit<T>(observer: Observer<T>, value: T): void {{ \
         observer.next && observer.next(value); }}",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let alias = symbol(&context, declaration(&parsed, "Observer"));
    let alias_links = context.store().type_alias_links(alias).unwrap();
    let target = alias_links.declared_type.unwrap();
    let alias_parameter = alias_links.type_parameters.as_ref().unwrap()[0];
    let emit = declaration(&parsed, "emit");
    let signature = context
        .store()
        .signature_links(emit)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let emit = context.store().signature(signature).unwrap();
    let outer_parameter = emit.type_parameters()[0];
    let receiver = value_type(&context, emit.parameters()[0]);
    assert_ne!(alias_parameter, outer_parameter);
    let callable = assert_mapped_next(&context, target, receiver, outer_parameter);
    let before = counts(&context);
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(
        assert_mapped_next(&context, target, receiver, outer_parameter),
        callable,
    );
    assert_eq!(counts(&context), before);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn observer_next_reports_the_mapped_parameter_type() {
    let parsed = parse_source_file(&format!(
        "{OBSERVER} declare const observer: Observer<string>; \
         declare const value: number; observer.next(value);",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the mapped string parameter must reject the number argument")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
    let before = counts(&context);
    let diagnostics = context.diagnostics().clone();
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(counts(&context), before);
}
