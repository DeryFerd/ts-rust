use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, IntrinsicBootstrapOptions,
    SignatureId, TypeData, TypeId, types::TypeFlags,
};
use ts_options::{ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(497_200);
const PROVIDER: FileId = FileId::new(497_201);
const BASE: &str = "export class Base<L> { listener!: L; }";
const OBSERVER: &str = concat!(
    "import { Base } from './base';\n",
    "type Listener<T> = (value: T) => T;\n",
    "export class Observer<T> extends Base<Listener<T>> {}\n",
    "declare const numbers: Observer<number>;\n",
    "declare const strings: Observer<string>;\n",
    "const numberListener = numbers.listener;\n",
    "const stringListener = strings.listener;\n",
);

fn context<'a>(source: &'a ParseResult, provider: &'a ParseResult) -> CanonicalCheckerContext<'a> {
    let files = [
        (SOURCE, source, "\"/project/source.ts\""),
        (PROVIDER, provider, "\"/project/base.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for (file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let specifier = source
        .arena
        .iter()
        .find_map(|(_, record)| match &record.data {
            NodeData::ImportDeclaration(data) => Some(node(source, SOURCE, data.module_specifier)),
            _ => None,
        })
        .unwrap();
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed, _)| (*file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_function_types: true,
            strict_property_initialization: true,
            no_implicit_any: true,
            no_implicit_this: true,
            module_kind: ModuleKind::EsNext,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            specifier,
            CanonicalResolvedModuleInput::new(
                PROVIDER,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap()
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn name_node(parsed: &ParseResult, declaration: NodeRef) -> NodeRef {
    let name = match &parsed.arena.get(declaration.node).unwrap().data {
        NodeData::ClassDeclaration(data) => data.name.unwrap(),
        NodeData::TypeAliasDeclaration(data) => data.name,
        NodeData::VariableDeclaration(data) => data.name,
        NodeData::PropertyDeclaration(data) => data.name,
        NodeData::ImportSpecifier(data) => data.name,
        _ => panic!("expected a named source declaration"),
    };
    node(parsed, declaration.file, name)
}

fn named(parsed: &ParseResult, file: FileId, kind: SyntaxKind, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .filter(|(_, record)| record.kind == kind)
        .map(|(id, _)| node(parsed, file, id))
        .find(|&declaration| {
            let name = name_node(parsed, declaration);
            matches!(&parsed.arena.get(name.node).unwrap().data,
                NodeData::Identifier(data) if data.text == expected)
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn formal(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    owner: NodeRef,
) -> TypeId {
    let parameters = match &parsed.arena.get(owner.node).unwrap().data {
        NodeData::ClassDeclaration(data) => data.type_parameters.as_ref().unwrap(),
        NodeData::TypeAliasDeclaration(data) => data.type_parameters.as_ref().unwrap(),
        _ => panic!("expected the real generic declaration"),
    };
    let [parameter] = parameters.nodes.as_slice() else {
        panic!("expected one source formal")
    };
    let parameter = node(parsed, owner.file, *parameter);
    let owner_symbol = symbol(context, owner);
    let parameter_symbol = symbol(context, parameter);
    assert_eq!(
        parsed.arena.get(parameter.node).unwrap().parent,
        Some(owner.node)
    );
    assert_eq!(
        context.store().symbol(parameter_symbol).unwrap().parent(),
        Some(owner_symbol)
    );
    let type_ = context
        .get_declared_type_of_symbol(parameter_symbol)
        .unwrap();
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
    assert_eq!(record.symbol(), Some(parameter_symbol));
    let TypeData::TypeParameter(data) = record.data() else {
        panic!("the source formal must keep its declared identity")
    };
    assert_eq!(data.target, None);
    assert_eq!(data.mapper, None);
    type_
}

fn variable_part(parsed: &ParseResult, name: &str, annotation: bool) -> NodeRef {
    let declaration = named(parsed, SOURCE, SyntaxKind::VariableDeclaration, name);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    node(
        parsed,
        SOURCE,
        if annotation {
            data.type_
        } else {
            data.initializer
        }
        .unwrap(),
    )
}

fn heritage(parsed: &ParseResult, class: NodeRef) -> (NodeRef, NodeRef) {
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        unreachable!()
    };
    let [clause] = data.heritage_clauses.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected one extends clause")
    };
    let clause_record = parsed.arena.get(*clause).unwrap();
    assert_eq!(clause_record.parent, Some(class.node));
    let NodeData::HeritageClause(data) = &clause_record.data else {
        unreachable!()
    };
    assert_eq!(data.token, SyntaxKind::ExtendsKeyword);
    let [wrapper] = data.types.nodes.as_slice() else {
        panic!("expected one applied base")
    };
    let wrapper_record = parsed.arena.get(*wrapper).unwrap();
    assert_eq!(wrapper_record.parent, Some(*clause));
    let NodeData::ExpressionWithTypeArguments(data) = &wrapper_record.data else {
        panic!("expected the actual Base<Listener<T>> node")
    };
    let expression_record = parsed.arena.get(data.expression).unwrap();
    assert_eq!(expression_record.parent, Some(*wrapper));
    assert!(matches!(&expression_record.data, NodeData::Identifier(data) if data.text == "Base"));
    (
        node(parsed, class.file, *wrapper),
        node(parsed, class.file, data.expression),
    )
}

fn assert_reference(
    context: &CanonicalCheckerContext<'_>,
    actual: TypeId,
    target: TypeId,
    argument: TypeId,
) {
    let TypeData::TypeReference(data) = context.store().type_payload(actual).unwrap().data() else {
        panic!("expected the actual applied class type")
    };
    assert_eq!(data.object.target, Some(target));
    assert_eq!(
        data.resolved_type_arguments.as_deref(),
        Some(&[argument][..])
    );
}

fn assert_listener(
    context: &mut CanonicalCheckerContext<'_>,
    actual: TypeId,
    alias: SemanticSymbolId,
    argument: TypeId,
) -> SignatureId {
    let record = context.store().type_payload(actual).unwrap();
    let metadata = context.store().type_alias(record.alias().unwrap()).unwrap();
    assert_eq!(metadata.symbol(), Some(alias));
    assert_eq!(metadata.type_arguments(), Some(&[argument][..]));
    let TypeData::Object(data) = record.data() else {
        panic!("Listener must retain its actual callable type")
    };
    assert_eq!(data.structured.call_signature_count, 1);
    let [signature] = data.structured.signatures.as_deref().unwrap() else {
        panic!("expected the source Listener call signature")
    };
    let signature = *signature;
    assert_eq!(
        context.get_return_type_of_signature(signature),
        Ok(argument)
    );
    let record = context.store().signature(signature).unwrap();
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.min_argument_count(), 1);
    let [parameter] = record.parameters() else {
        panic!("Listener must keep one value parameter")
    };
    assert_eq!(
        context
            .store()
            .value_symbol_links(*parameter)
            .unwrap()
            .resolved_type,
        Some(argument)
    );
    signature
}

fn assert_read(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    name: &str,
    original: SemanticSymbolId,
    alias: SemanticSymbolId,
    argument: TypeId,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let access = variable_part(source, name, false);
    let NodeData::PropertyAccessExpression(data) = &source.arena.get(access.node).unwrap().data
    else {
        panic!("expected the unchanged inherited property read")
    };
    let type_ = context.get_type_at_location(access).unwrap();
    let signature = assert_listener(context, type_, alias, argument);
    let copied = context
        .get_symbol_at_location(node(source, SOURCE, data.name))
        .unwrap()
        .unwrap();
    assert_ne!(copied, original);
    let links = context.store().value_symbol_links(copied).unwrap();
    assert_eq!(links.target, Some(original));
    assert_eq!(links.resolved_type, Some(type_));
    let mapper = links.mapper.unwrap();
    assert!(context.store().mapper_payload(mapper).is_some());
    let copied_record = context.store().symbol(copied).unwrap();
    let original_record = context.store().symbol(original).unwrap();
    assert!(
        copied_record
            .check_flags()
            .contains(CheckFlags::INSTANTIATED)
    );
    assert_eq!(copied_record.declarations(), original_record.declarations());
    (type_, signature, copied, mapper)
}

#[allow(clippy::too_many_lines)] // Keep the two inherited substitutions in one identity check.
fn assert_graph(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    provider: &ParseResult,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let base = named(provider, PROVIDER, SyntaxKind::ClassDeclaration, "Base");
    let observer = named(source, SOURCE, SyntaxKind::ClassDeclaration, "Observer");
    let listener = named(source, SOURCE, SyntaxKind::TypeAliasDeclaration, "Listener");
    let base_owner = symbol(context, base);
    let observer_owner = symbol(context, observer);
    let alias_owner = symbol(context, listener);
    let base_type = context.get_declared_type_of_symbol(base_owner).unwrap();
    let observer_type = context.get_declared_type_of_symbol(observer_owner).unwrap();
    let alias_type = context.get_declared_type_of_symbol(alias_owner).unwrap();
    let base_formal = formal(context, provider, base);
    let observer_formal = formal(context, source, observer);
    let alias_formal = formal(context, source, listener);
    assert_ne!(base_formal, observer_formal);
    assert_ne!(base_formal, alias_formal);
    assert_ne!(observer_formal, alias_formal);
    assert_listener(context, alias_type, alias_owner, alias_formal);

    let field = named(
        provider,
        PROVIDER,
        SyntaxKind::PropertyDeclaration,
        "listener",
    );
    assert_eq!(
        provider.arena.get(field.node).unwrap().parent,
        Some(base.node)
    );
    let field_owner = symbol(context, field);
    assert_eq!(
        context.store().symbol(field_owner).unwrap().parent(),
        Some(base_owner)
    );
    let original_links = context.store().value_symbol_links(field_owner).unwrap();
    assert_eq!(original_links.resolved_type, Some(base_formal));
    assert_eq!(original_links.target, None);
    assert_eq!(original_links.mapper, None);

    let members = context
        .get_nongeneric_class_members(observer_owner)
        .unwrap();
    assert_eq!(members.shells().instance_type(), observer_type);
    assert!(members.declared_instance_properties().is_empty());
    assert_eq!(members.instance_properties(), &[field_owner]);
    let inherited = members.base().unwrap();
    assert_eq!(inherited.symbol(), base_owner);
    assert_eq!(inherited.instance_type(), base_type);
    let applied_base = inherited.applied_instance_type();
    let base_value = inherited.value_type();
    let TypeData::TypeReference(data) = context.store().type_payload(applied_base).unwrap().data()
    else {
        panic!("the base must keep its actual Listener<T> argument")
    };
    let [listener_template] = data.resolved_type_arguments.as_deref().unwrap() else {
        panic!("expected one Listener<T> base argument")
    };
    let listener_template = *listener_template;
    assert_reference(context, applied_base, base_type, listener_template);
    assert_listener(context, listener_template, alias_owner, observer_formal);

    let imported = symbol(
        context,
        named(source, SOURCE, SyntaxKind::ImportSpecifier, "Base"),
    );
    assert_ne!(imported, base_owner);
    let import_links = context.store().alias_symbol_links(imported).unwrap();
    assert_eq!(
        import_links.alias_target,
        AliasTargetState::Resolved(base_owner)
    );
    assert_eq!(import_links.type_only_declaration, None);
    let (base_node, base_expression) = heritage(source, observer);
    assert_eq!(
        context
            .store()
            .type_node_links(base_expression)
            .and_then(|links| links.resolved_type),
        Some(base_value)
    );
    assert_eq!(
        context
            .store()
            .symbol_node_links(base_expression)
            .and_then(|links| links.resolved_symbol),
        Some(imported)
    );
    assert_eq!(
        context
            .store()
            .type_node_links(base_node)
            .and_then(|links| links.resolved_type),
        Some(applied_base)
    );
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let (number, string) = (bootstrap.number_type, bootstrap.string_type);
    let numbers = context
        .get_type_from_type_node(variable_part(source, "numbers", true))
        .unwrap();
    let strings = context
        .get_type_from_type_node(variable_part(source, "strings", true))
        .unwrap();
    assert_ne!(numbers, strings);
    assert_reference(context, numbers, observer_type, number);
    assert_reference(context, strings, observer_type, string);
    let reads = [
        assert_read(
            context,
            source,
            "numberListener",
            field_owner,
            alias_owner,
            number,
        ),
        assert_read(
            context,
            source,
            "stringListener",
            field_owner,
            alias_owner,
            string,
        ),
    ];
    assert_ne!(reads[0], reads[1]);
    (
        [
            base_type,
            observer_type,
            alias_type,
            base_formal,
            observer_formal,
            alias_formal,
            applied_base,
            listener_template,
            numbers,
            strings,
        ],
        reads,
    )
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 5] {
    let store = context.store();
    [
        store.type_len(),
        store.type_alias_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
    ]
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    provider: &ParseResult,
) {
    let graph = assert_graph(context, source, provider);
    let diagnostics = context.diagnostics().clone();
    let warm = counts(context);
    let relations = context.store().relation_state_snapshot();
    for _ in 0..2 {
        context.check_source_file(PROVIDER).unwrap();
        context.check_source_file(SOURCE).unwrap();
        context.recheck_source_file(SOURCE).unwrap();
        assert_eq!(assert_graph(context, source, provider), graph);
        assert_eq!(context.diagnostics(), &diagnostics);
        assert_eq!(counts(context), warm);
        assert_eq!(context.store().relation_state_snapshot(), relations);
    }
}

#[test]
fn generic_observers_keep_imported_listener_substitutions_and_replay() {
    let provider = parse_source_file(BASE);
    let source = parse_source_file(OBSERVER);
    for provider_query_first in [false, true] {
        let mut context = context(&source, &provider);
        let base = symbol(
            &context,
            named(&provider, PROVIDER, SyntaxKind::ClassDeclaration, "Base"),
        );
        let early =
            provider_query_first.then(|| context.get_declared_type_of_symbol(base).unwrap());
        context.check_source_file(SOURCE).unwrap();
        if let Some(early) = early {
            assert_eq!(context.get_declared_type_of_symbol(base), Ok(early));
        }
        assert_graph(&mut context, &source, &provider);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        assert_replay(&mut context, &source, &provider);
    }
}

#[test]
fn inherited_listener_assignment_keeps_the_native_type_error() {
    let provider = parse_source_file(BASE);
    let source = parse_source_file(&format!(
        "{OBSERVER}const wrong: string = numbers.listener;\n"
    ));
    let wrong = named(&source, SOURCE, SyntaxKind::VariableDeclaration, "wrong");
    let mut context = context(&source, &provider);
    context.check_source_file(SOURCE).unwrap();
    assert_graph(&mut context, &source, &provider);
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "expected one native assignment error: {:?}",
            context.diagnostics()
        )
    };
    assert_eq!(diagnostic.node, Some(name_node(&source, wrong)));
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.arguments,
        ["Listener<number>", "string"]
    );
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'Listener<number>' is not assignable to type 'string'."
    );
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    assert_replay(&mut context, &source, &provider);
}
