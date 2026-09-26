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

const FILE: FileId = FileId::new(203_280);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/query-interface-references.ts\""),
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
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::TypeAliasDeclaration(data) => data.name,
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

fn written_node(parsed: &ParseResult, kind: SyntaxKind, text: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let range = record.range;
            let source = parsed.arena.source_text().unwrap();
            (record.kind == kind
                && &source[usize::try_from(range.start.get()).unwrap()
                    ..usize::try_from(range.end.get()).unwrap()]
                    == text)
                .then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {text}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn declared_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .declared_type_links(symbol(context, node))
        .unwrap()
        .declared_type
        .unwrap()
}

fn node_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn formals(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    declaration: NodeRef,
) -> Vec<TypeId> {
    let NodeData::InterfaceDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected an interface declaration")
    };
    data.type_parameters
        .as_ref()
        .unwrap()
        .nodes
        .iter()
        .map(|node| {
            let node = NodeRef::new(parsed.arena.id(), FILE, *node);
            assert_eq!(
                parsed.arena.get(node.node).unwrap().parent,
                Some(declaration.node)
            );
            let type_ = declared_type(context, node);
            let record = context.store().type_payload(type_).unwrap();
            let TypeData::TypeParameter(data) = record.data() else {
                panic!("the written formal must retain its own type")
            };
            assert_eq!(record.symbol(), Some(symbol(context, node)));
            assert!(!data.is_this_type);
            assert_eq!(data.target, None);
            assert_eq!(data.mapper, None);
            type_
        })
        .collect()
}

fn reference_arguments(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    target: TypeId,
) -> Vec<TypeId> {
    let TypeData::TypeReference(data) = context.store().type_payload(type_).unwrap().data() else {
        panic!("expected a canonical interface reference")
    };
    assert_eq!(data.object.target, Some(target));
    assert_eq!(data.object.mapper, None);
    data.resolved_type_arguments.clone().unwrap()
}

fn structured<'a>(
    context: &'a CanonicalCheckerContext<'_>,
    type_: TypeId,
) -> &'a StructuredTypeData {
    match context.store().type_payload(type_).unwrap().data() {
        TypeData::Interface(data) => &data.reference.object.structured,
        TypeData::TypeReference(data) => &data.object.structured,
        _ => panic!("expected resolved interface members"),
    }
}

fn assert_property(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    name: &str,
    expected: TypeId,
    optional: bool,
) {
    let owner = context
        .store()
        .symbol_table(structured(context, type_).members.unwrap())
        .unwrap()
        .get_source(name)
        .unwrap();
    assert_eq!(
        context
            .store()
            .symbol(owner)
            .unwrap()
            .flags()
            .contains(SymbolFlags::OPTIONAL),
        optional,
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type,
        Some(expected),
    );
}

fn assert_diagnostic(
    context: &CanonicalCheckerContext<'_>,
    node: NodeRef,
    code: u32,
    message: &str,
) {
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "expected one native diagnostic: {:?}",
            context.diagnostics()
        )
    };
    assert_eq!(diagnostic.node, Some(node));
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    queries: &[(NodeRef, TypeId)],
) {
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            [
                store.type_len(),
                store.symbol_len(),
                store.mapper_len(),
                store.type_alias_len(),
                store.signature_len(),
                store.index_info_len(),
                store.symbol_store().symbol_table_len(),
            ],
            parsed
                .arena
                .iter()
                .map(|(node, _)| {
                    store
                        .type_node_links(NodeRef::new(parsed.arena.id(), FILE, node))
                        .cloned()
                })
                .collect::<Vec<_>>(),
            context.diagnostics().clone(),
        )
    };
    for &(node, expected) in queries {
        assert_eq!(context.get_type_from_type_node(node), Ok(expected));
    }
    let warm = snapshot(context);
    context.check_source_file(FILE).unwrap();
    assert_eq!(snapshot(context), warm);
    context.recheck_source_file(FILE).unwrap();
    for &(node, expected) in queries {
        assert_eq!(context.get_type_from_type_node(node), Ok(expected));
    }
    assert_eq!(snapshot(context), warm);
}

#[test]
fn conditional_alias_interface_defaults_keep_the_selected_type_and_replay() {
    let parsed = parse_source_file(
        r#"
interface Payload { message: string }
type Fallback = string extends string ? Payload : never;
interface Options<T = Fallback> { error: T }
interface Config { options: Options }
declare const config: Config;
declare const explicit: Options<Payload>;
const message: string = config.options.error.message;
const invalid: number = config.options.error.message;
"#,
    );
    let bare = written_node(&parsed, SyntaxKind::TypeReference, "Options");
    let explicit = written_node(&parsed, SyntaxKind::TypeReference, "Options<Payload>");
    for query_first in [false, true] {
        let mut context = context(&parsed);
        let queried = query_first.then(|| context.get_type_from_type_node(bare).unwrap());
        context.check_source_file(FILE).unwrap();
        assert_diagnostic(
            &context,
            declaration(&parsed, "invalid"),
            2322,
            "Type 'string' is not assignable to type 'number'.",
        );

        let payload = declared_type(&context, declaration(&parsed, "Payload"));
        let options = declaration(&parsed, "Options");
        let target = declared_type(&context, options);
        let arguments = formals(&context, &parsed, options);
        let [parameter] = arguments.as_slice() else {
            panic!("expected one formal")
        };
        let TypeData::TypeParameter(data) =
            context.store().type_payload(*parameter).unwrap().data()
        else {
            unreachable!()
        };
        assert_eq!(data.constraint, None);
        assert_eq!(data.resolved_default_type, Some(payload));
        let fallback = declaration(&parsed, "Fallback");
        let NodeData::TypeAliasDeclaration(alias) = &parsed.arena.get(fallback.node).unwrap().data
        else {
            unreachable!()
        };
        let rhs = NodeRef::new(parsed.arena.id(), FILE, alias.type_);
        assert_eq!(
            parsed.arena.get(rhs.node).unwrap().kind,
            SyntaxKind::ConditionalType
        );
        let alias_links = context
            .store()
            .type_alias_links(symbol(&context, fallback))
            .unwrap();
        assert_eq!(alias_links.declared_type, Some(payload));
        assert_eq!(alias_links.type_parameters, None);
        assert_eq!(alias_links.instantiations, None);
        assert_eq!(node_type(&context, rhs), payload);
        let default = written_node(&parsed, SyntaxKind::TypeReference, "Fallback");
        assert_eq!(node_type(&context, default), payload);
        let instance = node_type(&context, bare);
        assert_eq!(node_type(&context, explicit), instance);
        if let Some(queried) = queried {
            assert_eq!(queried, instance);
        }
        assert_eq!(reference_arguments(&context, instance, target), [payload]);
        assert_property(&context, instance, "error", payload, false);
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let read = written_node(
            &parsed,
            SyntaxKind::PropertyAccessExpression,
            "config.options.error.message",
        );
        assert_eq!(node_type(&context, read), string);
        assert_replay(
            &mut context,
            &parsed,
            &[
                (bare, instance),
                (explicit, instance),
                (default, payload),
                (rhs, payload),
            ],
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Compare both base identities, inherited members and the invalid actual argument.
fn generic_interface_bases_keep_constraints_nested_arguments_and_both_member_sets() {
    let parsed = parse_source_file(
        r#"
interface Key { label: string }
interface Data<T, P> { value: T; page: P }
interface Page<T, P extends Key = Key,> { data: T; key: P; optional?: T }
interface Extra<T,> { extra: T }
interface Combined<T, P extends Key = Key,>
  extends Page<Data<T, P>, P>, Extra<T> {}
declare const combined: Combined<string, Key>;
const text: string = combined.data.value;
const page: Key = combined.data.page;
const key: Key = combined.key;
const extra: string = combined.extra;
const note = combined.optional;
declare const invalid: Combined<string, number>;
"#,
    );
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert_diagnostic(
        &context,
        written_node(&parsed, SyntaxKind::NumberKeyword, "number"),
        2344,
        "Type 'number' does not satisfy the constraint 'Key'.",
    );
    let key = declared_type(&context, declaration(&parsed, "Key"));
    let combined = declaration(&parsed, "Combined");
    let combined_type = declared_type(&context, combined);
    let combined_formals = formals(&context, &parsed, combined);
    let page = declaration(&parsed, "Page");
    let page_type = declared_type(&context, page);
    let page_formals = formals(&context, &parsed, page);
    assert_ne!(combined_formals, page_formals);
    for parameter in [combined_formals[1], page_formals[1]] {
        let TypeData::TypeParameter(data) = context.store().type_payload(parameter).unwrap().data()
        else {
            unreachable!()
        };
        assert_eq!(data.constraint, Some(key));
    }
    for declaration in [combined, page, declaration(&parsed, "Extra")] {
        let NodeData::InterfaceDeclaration(data) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        assert!(data.type_parameters.as_ref().unwrap().has_trailing_comma);
    }
    let TypeData::Interface(data) = context.store().type_payload(combined_type).unwrap().data()
    else {
        unreachable!()
    };
    assert!(data.base_types_resolved);
    let [first, second] = data.resolved_base_types.as_deref().unwrap() else {
        panic!("both written bases must be retained in order")
    };
    let (first, second) = (*first, *second);
    let first_arguments = reference_arguments(&context, first, page_type);
    assert_eq!(first_arguments.len(), 2);
    assert_eq!(first_arguments[1], combined_formals[1]);
    let data_target = declared_type(&context, declaration(&parsed, "Data"));
    assert_eq!(
        reference_arguments(&context, first_arguments[0], data_target),
        combined_formals
    );
    assert_eq!(
        reference_arguments(
            &context,
            second,
            declared_type(&context, declaration(&parsed, "Extra"))
        ),
        [combined_formals[0]]
    );
    let base_node = written_node(
        &parsed,
        SyntaxKind::ExpressionWithTypeArguments,
        "Page<Data<T, P>, P>",
    );
    let extra_node = written_node(&parsed, SyntaxKind::ExpressionWithTypeArguments, "Extra<T>");
    assert_eq!(node_type(&context, base_node), first);
    assert_eq!(node_type(&context, extra_node), second);

    let instance_node = written_node(&parsed, SyntaxKind::TypeReference, "Combined<string, Key>");
    let instance = node_type(&context, instance_node);
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(
        reference_arguments(&context, instance, combined_type),
        [string, key]
    );
    let read = |text| {
        node_type(
            &context,
            written_node(&parsed, SyntaxKind::PropertyAccessExpression, text),
        )
    };
    assert_eq!(read("combined.data.value"), string);
    assert_eq!(read("combined.data.page"), key);
    assert_eq!(read("combined.key"), key);
    assert_eq!(read("combined.extra"), string);
    let nested = read("combined.data");
    assert_eq!(
        reference_arguments(&context, nested, data_target),
        [string, key]
    );
    assert_property(&context, instance, "data", nested, false);
    assert_property(&context, instance, "key", key, false);
    assert_property(&context, instance, "extra", string, false);
    let optional = read("combined.optional");
    let TypeData::Union(data) = context.store().type_payload(optional).unwrap().data() else {
        panic!("the optional inherited property must include undefined")
    };
    assert_eq!(data.union.types.len(), 2);
    assert!(data.union.types.contains(&nested));
    assert!(
        data.union.types.contains(
            &context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .undefined_type
        )
    );
    assert_property(&context, instance, "optional", optional, true);
    assert_replay(
        &mut context,
        &parsed,
        &[
            (base_node, first),
            (extra_node, second),
            (instance_node, instance),
        ],
    );
}
