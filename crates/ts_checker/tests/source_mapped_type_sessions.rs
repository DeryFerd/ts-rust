use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, MappedSymbolLinks, SignatureId, SignatureLinks, SourceFileLinks,
    TypeAliasLinks, TypeData, TypeId, TypeNodeLinks, ValueSymbolLinks,
    type_records::MappedTypeData,
};
use ts_parser::{ParseResult, parse_source_file};

const DECLARATIONS: FileId = FileId::new(202_860);
const SOURCE: FileId = FileId::new(202_861);

fn context<'a>(
    declarations: &'a ParseResult,
    source: &'a ParseResult,
    exact: bool,
) -> CanonicalCheckerContext<'a> {
    let files = [(DECLARATIONS, declarations), (SOURCE, source)];
    let mut binder = CanonicalBinder::new();
    for (file, parsed) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let path = if file == DECLARATIONS {
            "\"/project/mapped-method-returns.d.ts\""
        } else {
            "\"/project/main.ts\""
        };
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    file == DECLARATIONS,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
    }
    for (file, parsed) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            no_implicit_any: true,
            strict_function_types: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: exact,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn nodes(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|(start, _)| *start);
    nodes.into_iter().map(|(_, node)| node).collect()
}

fn declaration(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let identifier = match &record.data {
                NodeData::TypeAliasDeclaration(data) => data.name,
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::VariableDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(identifier)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing declaration {name}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn alias_type(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
) -> TypeId {
    let owner = symbol(context, declaration(parsed, DECLARATIONS, name));
    context
        .get_declared_type_of_symbol(owner)
        .unwrap_or_else(|error| panic!("unresolved alias {name}: {error:?}"))
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap_or_else(|| panic!("missing signature for {node:?}"))
}

fn mapped<'a>(context: &'a CanonicalCheckerContext<'_>, type_: TypeId) -> &'a MappedTypeData {
    let TypeData::Mapped(mapped) = context.store().type_payload(type_).unwrap().data() else {
        panic!("the source alias must retain its mapped type");
    };
    mapped
}

fn assert_mapped_alias(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    type_: TypeId,
    name: &str,
    argument: TypeId,
) {
    let store = context.store();
    let owner = declaration(parsed, DECLARATIONS, name);
    let alias = symbol(context, owner);
    let links = store.type_alias_links(alias).unwrap();
    let target = links.declared_type.unwrap();
    let record = store.type_payload(type_).unwrap();
    let identity = store.type_alias(record.alias().unwrap()).unwrap();
    assert_eq!(identity.symbol(), Some(alias));
    assert_eq!(identity.type_arguments(), Some(&[argument][..]));
    assert!(
        links
            .instantiations
            .as_ref()
            .unwrap()
            .values()
            .any(|cached| *cached == type_)
    );
    let actual = mapped(context, type_);
    let original = mapped(context, target);
    let NodeData::TypeAliasDeclaration(alias_node) = &parsed.arena.get(owner.node).unwrap().data
    else {
        unreachable!();
    };
    let mapped_node = NodeRef::new(owner.arena, owner.file, alias_node.type_);
    assert_eq!(original.declaration, Some(mapped_node));
    assert_eq!(actual.declaration, original.declaration);
    assert_eq!(actual.object.target, Some(target));
    assert!(actual.object.mapper.is_some());
    assert_eq!(actual.template_type, original.template_type);
    assert_eq!(actual.modifiers_type, Some(argument));
    assert_eq!(actual.name_type, None);
    let NodeData::MappedTypeNode(mapped_node) = &parsed.arena.get(mapped_node.node).unwrap().data
    else {
        panic!("the alias must own a written mapped type");
    };
    let key = NodeRef::new(owner.arena, owner.file, mapped_node.type_parameter);
    let key_owner = symbol(context, key);
    for key_type in [
        original.type_parameter.unwrap(),
        actual.type_parameter.unwrap(),
    ] {
        assert_eq!(
            store.type_payload(key_type).unwrap().symbol(),
            Some(key_owner)
        );
    }
}

fn assert_generic_call(
    context: &mut CanonicalCheckerContext<'_>,
    call: NodeRef,
    method: NodeRef,
    argument: TypeId,
) -> (SignatureId, TypeId) {
    let result = context.get_type_at_location(call).unwrap();
    let selected = signature(context, call);
    let target = signature(context, method);
    let store = context.store();
    let original = store.signature(target).unwrap();
    let [parameter] = original.type_parameters() else {
        panic!("the written method must retain its one type parameter");
    };
    let owner = store.type_payload(*parameter).unwrap().symbol().unwrap();
    let [declaration] = store.symbol(owner).unwrap().declarations().unwrap() else {
        panic!("the method type parameter must keep its one source declaration");
    };
    assert_eq!(declaration.file, method.file);
    let parameter_node = context
        .file(method.file)
        .unwrap()
        .0
        .get(declaration.node)
        .unwrap();
    assert_eq!(parameter_node.kind, SyntaxKind::TypeParameter);
    assert_eq!(parameter_node.parent, Some(method.node));
    let instantiated = store.signature(selected).unwrap();
    assert_eq!(instantiated.target(), Some(target));
    assert_eq!(instantiated.declaration(), Some(method));
    assert!(instantiated.type_parameters().is_empty());
    assert_eq!(
        store.map_type(instantiated.mapper().unwrap(), *parameter),
        Some(argument)
    );
    let [value] = instantiated.parameters() else {
        panic!("the selected method must retain its value parameter");
    };
    assert_eq!(
        store.value_symbol_links(*value).unwrap().resolved_type,
        Some(argument)
    );
    assert_eq!(context.get_return_type_of_signature(selected), Ok(result));
    (selected, result)
}

fn property(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    name: &str,
) -> (SemanticSymbolId, TypeId) {
    let store = context.store();
    let table = mapped(context, type_).object.structured.members.unwrap();
    let property = store.symbol_table(table).unwrap().get_source(name).unwrap();
    let links = store.value_symbol_links(property).unwrap();
    assert_eq!(links.containing_type, Some(type_));
    assert!(
        store
            .symbol(property)
            .unwrap()
            .check_flags()
            .contains(CheckFlags::MAPPED)
    );
    (property, links.resolved_type.unwrap())
}

fn assert_union(context: &CanonicalCheckerContext<'_>, type_: TypeId, expected: &[TypeId]) {
    let TypeData::Union(union) = context.store().type_payload(type_).unwrap().data() else {
        panic!("the optional value must retain its union");
    };
    assert_eq!(union.union.types.len(), expected.len());
    for expected in expected {
        assert!(union.union.types.contains(expected));
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 8],
    types: Vec<Option<TypeNodeLinks>>,
    signatures: Vec<Option<SignatureLinks>>,
    values: Vec<Option<ValueSymbolLinks>>,
    aliases: Vec<Option<TypeAliasLinks>>,
    mapped: Vec<MappedTypeData>,
    properties: Vec<Option<MappedSymbolLinks>>,
    sources: Vec<Option<SourceFileLinks>>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    declarations: &ParseResult,
    source: &ParseResult,
    mapped_types: &[TypeId],
) -> Snapshot {
    let store = context.store();
    let files = [(DECLARATIONS, declarations), (SOURCE, source)];
    let nodes = files
        .iter()
        .flat_map(|(file, parsed)| {
            parsed
                .arena
                .iter()
                .map(move |(node, _)| NodeRef::new(parsed.arena.id(), *file, node))
        })
        .collect::<Vec<_>>();
    let mut symbols = nodes
        .iter()
        .filter_map(|node| context.file(node.file).unwrap().1.symbol(*node))
        .map(|raw| store.get_merged_symbol(raw).unwrap())
        .collect::<Vec<_>>();
    let mapped = mapped_types
        .iter()
        .map(|type_| mapped(context, *type_).clone())
        .collect::<Vec<_>>();
    for mapped in &mapped {
        symbols.extend(
            mapped
                .object
                .structured
                .properties
                .as_deref()
                .unwrap_or_default(),
        );
    }
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
            store.index_info_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        ],
        types: nodes
            .iter()
            .map(|node| store.type_node_links(*node).cloned())
            .collect(),
        signatures: nodes
            .iter()
            .map(|node| store.signature_links(*node).cloned())
            .collect(),
        values: symbols
            .iter()
            .map(|symbol| store.value_symbol_links(*symbol).cloned())
            .collect(),
        aliases: symbols
            .iter()
            .map(|symbol| store.type_alias_links(*symbol).cloned())
            .collect(),
        mapped,
        properties: symbols
            .iter()
            .map(|symbol| store.mapped_symbol_links(*symbol).cloned())
            .collect(),
        sources: files
            .iter()
            .map(|(file, _)| {
                store
                    .source_file_links(context.source_file(*file).unwrap())
                    .cloned()
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    declarations: &ParseResult,
    source: &ParseResult,
    mapped_types: &[TypeId],
    relations: &[(TypeId, TypeId, bool)],
) {
    let mut queries = Vec::new();
    let mut returns = Vec::new();
    for (parsed, file, kind) in [
        (declarations, DECLARATIONS, SyntaxKind::MethodSignature),
        (source, SOURCE, SyntaxKind::CallExpression),
        (source, SOURCE, SyntaxKind::PropertyAccessExpression),
    ] {
        for node in nodes(parsed, file, kind) {
            queries.push((node, context.get_type_at_location(node).unwrap()));
            if kind != SyntaxKind::PropertyAccessExpression {
                let signature = signature(context, node);
                returns.push((
                    signature,
                    context.get_return_type_of_signature(signature).unwrap(),
                ));
            }
        }
    }
    let warm = snapshot(context, declarations, source, mapped_types);
    for _ in 0..2 {
        context.recheck_source_file(SOURCE).unwrap();
        for &(node, expected) in &queries {
            assert_eq!(context.get_type_at_location(node), Ok(expected));
        }
        for &(signature, expected) in &returns {
            assert_eq!(
                context.get_return_type_of_signature(signature),
                Ok(expected)
            );
        }
        for &(source, target, expected) in relations {
            assert_eq!(context.is_type_assignable_to(source, target), Ok(expected));
        }
        assert_eq!(snapshot(context, declarations, source, mapped_types), warm);
        assert!(context.store().type_resolution_is_empty());
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the source owner and replay checks together.
fn generic_method_mapped_returns_keep_named_values_and_source_identity_on_replay() {
    let declarations = parse_source_file(concat!(
        "type DeclaredValue = number | undefined;\n",
        "interface Wrapper<Value> { value: Value }\n",
        "interface Shape { readonly item?: DeclaredValue; label: string }\n",
        "type Cells<Model> = { readonly [Key in keyof Model]: Wrapper<Model[Key]> };\n",
        "type Expected = { readonly item?: Wrapper<DeclaredValue>; readonly label: Wrapper<string> };\n",
        "type Wrong = { readonly item?: Wrapper<string>; readonly label: Wrapper<string> };\n",
        "interface Api { cells<Model>(value: Model): Cells<Model>; cells(a: number, b: number): number; }\n",
    ));
    let source = parse_source_file(concat!(
        "declare const api: Api; declare const shape: Shape;\n",
        "const first = api.cells<Shape>(shape);\n",
        "const inferred = api.cells(shape);\n",
        "const repeated = api.cells<Shape>(shape);\n",
        "const scalar = api.cells(1, 2);\n",
    ));
    let methods = nodes(&declarations, DECLARATIONS, SyntaxKind::MethodSignature);
    let calls = nodes(&source, SOURCE, SyntaxKind::CallExpression);
    assert_eq!(methods.len(), 2);
    assert_eq!(calls.len(), 4);
    for query_first in [false, true] {
        let mut context = context(&declarations, &source, false);
        if query_first {
            context.get_type_at_location(methods[0]).unwrap();
            let original = signature(&context, methods[0]);
            let parameter = context
                .store()
                .signature(original)
                .unwrap()
                .type_parameters()[0];
            let returned = context.get_return_type_of_signature(original).unwrap();
            assert_mapped_alias(&context, &declarations, returned, "Cells", parameter);
            assert!(
                context
                    .store()
                    .source_file_links(context.source_file(SOURCE).unwrap())
                    .is_none_or(|links| !links.type_checked)
            );
            for call in &calls {
                assert!(context.store().type_node_links(*call).is_none());
                assert!(context.store().signature_links(*call).is_none());
            }
        }
        context.check_source_file(SOURCE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let shape = context
            .get_type_at_location(declaration(&source, SOURCE, "shape"))
            .unwrap();
        let first = assert_generic_call(&mut context, calls[0], methods[0], shape);
        for call in &calls[1..3] {
            assert_eq!(
                assert_generic_call(&mut context, *call, methods[0], shape),
                first
            );
        }
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(context.get_type_at_location(calls[3]), Ok(number));
        assert_eq!(
            signature(&context, calls[3]),
            signature(&context, methods[1])
        );
        assert_mapped_alias(&context, &declarations, first.1, "Cells", shape);
        let expected = alias_type(&mut context, &declarations, "Expected");
        let wrong = alias_type(&mut context, &declarations, "Wrong");
        let relations = [(first.1, expected, true), (first.1, wrong, false)];
        for &(source, target, expected) in &relations {
            assert_eq!(context.is_type_assignable_to(source, target), Ok(expected));
        }
        let declared = alias_type(&mut context, &declarations, "DeclaredValue");
        let (item, value) = property(&context, first.1, "item");
        let store = context.store();
        assert!(
            store
                .symbol(item)
                .unwrap()
                .flags()
                .contains(SymbolFlags::OPTIONAL)
        );
        assert!(
            store
                .symbol(item)
                .unwrap()
                .check_flags()
                .contains(CheckFlags::READONLY)
        );
        let TypeData::Union(union) = store.type_payload(value).unwrap().data() else {
            panic!("an optional Wrapper property must retain its sentinel");
        };
        let undefined = store.intrinsic_bootstrap().unwrap().undefined_type;
        let wrapper = *union
            .union
            .types
            .iter()
            .find(|type_| **type_ != undefined)
            .unwrap();
        assert_union(&context, value, &[wrapper, undefined]);
        let TypeData::TypeReference(reference) = store.type_payload(wrapper).unwrap().data() else {
            panic!("the optional property must contain its Wrapper reference");
        };
        assert!(store.type_payload(declared).unwrap().alias().is_some());
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(&[declared][..])
        );
        assert_eq!(
            store
                .type_payload(reference.object.target.unwrap())
                .unwrap()
                .symbol(),
            Some(symbol(
                &context,
                declaration(&declarations, DECLARATIONS, "Wrapper")
            ))
        );
        let origin = store
            .mapped_symbol_links(item)
            .unwrap()
            .synthetic_origin
            .unwrap();
        let TypeData::Interface(shape_data) = store.type_payload(shape).unwrap().data() else {
            panic!("the method argument must retain the declared Shape");
        };
        assert_eq!(
            store
                .symbol_table(shape_data.reference.object.structured.members.unwrap())
                .unwrap()
                .get_source("item"),
            Some(origin)
        );
        assert_eq!(
            store.symbol(item).unwrap().declarations(),
            store.symbol(origin).unwrap().declarations()
        );
        assert_replay(&mut context, &declarations, &source, &[first.1], &relations);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Check each strict optional mode through the same source calls.
fn generic_method_mapped_returns_preserve_chained_optional_and_required_values() {
    let declarations = parse_source_file(concat!(
        "interface Shape { value: number }\n",
        "type ReadonlyCopy<Model> = { readonly [Key in keyof Model]: Model[Key] };\n",
        "type Soft<Model> = { [Key in keyof Model]?: Model[Key] };\n",
        "type Firm<Model> = { -readonly [Key in keyof Model]-?: Model[Key] };\n",
        "type ExpectedSoft = { readonly value?: number }; type WrongSoft = { readonly value?: string };\n",
        "type ExpectedFirm = { value: number }; type WrongFirm = { value: string };\n",
        "interface Api {\n",
        "soft<Model>(value: Model): Soft<Model>; soft(a: number, b: number): number;\n",
        "firm<Model>(value: Model): Firm<Model>; firm(a: number, b: number): number; }\n",
    ));
    let source = parse_source_file(concat!(
        "declare const api: Api; declare const view: ReadonlyCopy<Shape>;\n",
        "const soft = api.soft(view);\n",
        "const repeatedSoft = api.soft<ReadonlyCopy<Shape>>(view);\n",
        "const firm = api.firm(soft);\n",
        "const repeatedFirm = api.firm<Soft<ReadonlyCopy<Shape>>>(soft);\n",
    ));
    let methods = nodes(&declarations, DECLARATIONS, SyntaxKind::MethodSignature);
    let calls = nodes(&source, SOURCE, SyntaxKind::CallExpression);
    assert_eq!(methods.len(), 4);
    assert_eq!(calls.len(), 4);
    for exact in [false, true] {
        let mut context = context(&declarations, &source, exact);
        context.check_source_file(SOURCE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "exact={exact}: {:?}",
            context.diagnostics()
        );
        let view = context
            .get_type_at_location(declaration(&source, SOURCE, "view"))
            .unwrap();
        let soft = assert_generic_call(&mut context, calls[0], methods[0], view);
        assert_eq!(
            assert_generic_call(&mut context, calls[1], methods[0], view),
            soft
        );
        let firm = assert_generic_call(&mut context, calls[2], methods[2], soft.1);
        assert_eq!(
            assert_generic_call(&mut context, calls[3], methods[2], soft.1),
            firm
        );
        assert_mapped_alias(&context, &declarations, soft.1, "Soft", view);
        assert_mapped_alias(&context, &declarations, firm.1, "Firm", soft.1);
        let relations = [
            (
                soft.1,
                alias_type(&mut context, &declarations, "ExpectedSoft"),
                true,
            ),
            (
                soft.1,
                alias_type(&mut context, &declarations, "WrongSoft"),
                false,
            ),
            (
                firm.1,
                alias_type(&mut context, &declarations, "ExpectedFirm"),
                true,
            ),
            (
                firm.1,
                alias_type(&mut context, &declarations, "WrongFirm"),
                false,
            ),
        ];
        for &(source, target, expected) in &relations {
            assert_eq!(
                context.is_type_assignable_to(source, target),
                Ok(expected),
                "exact={exact}"
            );
        }
        let (soft_property, soft_value) = property(&context, soft.1, "value");
        let (firm_property, firm_value) = property(&context, firm.1, "value");
        let store = context.store();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let sentinel = if exact {
            bootstrap.missing_type
        } else {
            bootstrap.undefined_type
        };
        assert_union(&context, soft_value, &[bootstrap.number_type, sentinel]);
        assert_eq!(firm_value, bootstrap.number_type);
        assert!(
            store
                .symbol(soft_property)
                .unwrap()
                .flags()
                .contains(SymbolFlags::OPTIONAL)
        );
        assert!(
            store
                .symbol(soft_property)
                .unwrap()
                .check_flags()
                .contains(CheckFlags::READONLY)
        );
        assert!(
            !store
                .symbol(firm_property)
                .unwrap()
                .flags()
                .contains(SymbolFlags::OPTIONAL)
        );
        assert!(
            !store
                .symbol(firm_property)
                .unwrap()
                .check_flags()
                .contains(CheckFlags::READONLY)
        );
        assert!(
            store
                .symbol(firm_property)
                .unwrap()
                .check_flags()
                .contains(CheckFlags::STRIP_OPTIONAL)
        );
        assert_eq!(
            store
                .mapped_symbol_links(firm_property)
                .unwrap()
                .synthetic_origin,
            Some(soft_property)
        );
        let (view_property, view_value) = property(&context, view, "value");
        assert_eq!(view_value, bootstrap.number_type);
        assert_eq!(
            store
                .mapped_symbol_links(soft_property)
                .unwrap()
                .synthetic_origin,
            Some(view_property)
        );
        assert_replay(
            &mut context,
            &declarations,
            &source,
            &[view, soft.1, firm.1],
            &relations,
        );
    }
}
