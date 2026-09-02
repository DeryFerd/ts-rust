use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, DeclaredTypeLinks, IntrinsicBootstrapOptions, NodeLinks,
    SignatureId, SignatureLinks, SourceFileLinks, SymbolNodeLinks, TypeAliasId, TypeData, TypeId,
    TypeMapperId, TypeNodeLinks, ValueSymbolLinks,
    signatures::SignatureFlags,
    type_records::{InterfaceTypeData, ObjectTypeData, TypeParameterData, TypeReferenceData},
    types::{ObjectFlags, TypeFlags},
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const PROVIDER: FileId = FileId::new(202_990);
const CONSUMER: FileId = FileId::new(202_991);
const BASE: &str = concat!(
    "export class Base<T> {\n",
    "  constructor() {}\n",
    "  read(value: T): T { return value; }\n",
    "}\n",
);

fn context<'arena>(
    provider: &'arena ParseResult,
    consumer: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path) in [
        (PROVIDER, provider, "\"/project/base.ts\""),
        (CONSUMER, consumer, "\"/project/consumer.ts\""),
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
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for (file, parsed) in [(PROVIDER, provider), (CONSUMER, consumer)] {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let import = only_node(consumer, CONSUMER, SyntaxKind::ImportDeclaration);
    let NodeData::ImportDeclaration(import) = &consumer.arena.get(import.node).unwrap().data else {
        unreachable!()
    };
    let module = NodeRef::new(consumer.arena.id(), CONSUMER, import.module_specifier);
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        vec![(PROVIDER, &provider.arena), (CONSUMER, &consumer.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_function_types: true,
            no_implicit_any: true,
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            module,
            CanonicalResolvedModuleInput::new(
                PROVIDER,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap()
}

fn only_node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(node, record)| {
        (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
    });
    let node = nodes.next().unwrap_or_else(|| panic!("missing {kind:?}"));
    assert!(nodes.next().is_none(), "expected one {kind:?}");
    node
}

fn declaration(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let name_node = match &record.data {
                NodeData::ClassDeclaration(class) => class.name?,
                NodeData::ImportSpecifier(import) => import.name,
                NodeData::TypeAliasDeclaration(alias) => alias.name,
                NodeData::VariableDeclaration(variable) => variable.name,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name_node)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("missing declaration {name}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(node.file).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn cached_type(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    checker
        .store()
        .type_node_links(node)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn checked(checker: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    checker
        .store()
        .source_file_links(checker.source_file(file).unwrap())
        .is_some_and(|links| links.type_checked)
}

#[derive(Debug, Eq, PartialEq)]
enum Payload {
    Interface(InterfaceTypeData),
    Object(ObjectTypeData),
    Parameter(TypeParameterData),
    Reference(TypeReferenceData),
}

#[derive(Debug, Eq, PartialEq)]
struct TypeSnapshot {
    id: TypeId,
    flags: TypeFlags,
    object_flags: ObjectFlags,
    symbol: Option<SemanticSymbolId>,
    alias: Option<TypeAliasId>,
    payload: Payload,
}

#[derive(Debug, Eq, PartialEq)]
struct SignatureSnapshot {
    id: SignatureId,
    flags: SignatureFlags,
    declaration: Option<NodeRef>,
    parameters: Vec<SemanticSymbolId>,
    type_parameters: Vec<TypeId>,
    this_parameter: Option<SemanticSymbolId>,
    return_type: Option<TypeId>,
    target: Option<SignatureId>,
    mapper: Option<TypeMapperId>,
    minimum: (i32, i32),
}

type NodeSnapshot = (
    NodeRef,
    Option<NodeLinks>,
    Option<TypeNodeLinks>,
    Option<SymbolNodeLinks>,
    Option<SignatureLinks>,
);
type SymbolSnapshot = (
    SemanticSymbolId,
    Option<DeclaredTypeLinks>,
    Option<ValueSymbolLinks>,
    Option<AliasSymbolLinks>,
);

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 9],
    nodes: Vec<NodeSnapshot>,
    symbols: Vec<SymbolSnapshot>,
    types: Vec<TypeSnapshot>,
    signatures: Vec<SignatureSnapshot>,
    sources: Vec<(FileId, Option<SourceFileLinks>)>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    provider: &ParseResult,
    consumer: &ParseResult,
) -> Snapshot {
    let store = checker.store();
    let sources = [(PROVIDER, provider), (CONSUMER, consumer)];
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
            store.merged_symbol_len(),
            store.type_resolution_len(),
        ],
        nodes: sources
            .iter()
            .flat_map(|&(file, parsed)| {
                parsed.arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(parsed.arena.id(), file, node);
                    (
                        node,
                        store.node_links(node).cloned(),
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
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
                    store.alias_symbol_links(symbol).cloned(),
                )
            })
            .collect(),
        types: store
            .types()
            .filter_map(|(id, record)| {
                let payload = match record.data() {
                    TypeData::Interface(data) => Payload::Interface(data.clone()),
                    TypeData::Object(data) => Payload::Object(data.clone()),
                    TypeData::TypeParameter(data) => Payload::Parameter(data.clone()),
                    TypeData::TypeReference(data) => Payload::Reference(data.clone()),
                    _ => return None,
                };
                Some(TypeSnapshot {
                    id,
                    flags: record.flags(),
                    object_flags: record.object_flags(),
                    symbol: record.symbol(),
                    alias: record.alias(),
                    payload,
                })
            })
            .collect(),
        signatures: store
            .signatures()
            .map(|(id, signature)| SignatureSnapshot {
                id,
                flags: signature.flags(),
                declaration: signature.declaration(),
                parameters: signature.parameters().to_vec(),
                type_parameters: signature.type_parameters().to_vec(),
                this_parameter: signature.this_parameter(),
                return_type: signature.resolved_return_type(),
                target: signature.target(),
                mapper: signature.mapper(),
                minimum: (
                    signature.min_argument_count(),
                    signature.resolved_min_argument_count(),
                ),
            })
            .collect(),
        sources: sources
            .iter()
            .map(|&(file, _)| {
                (
                    file,
                    store
                        .source_file_links(checker.source_file(file).unwrap())
                        .cloned(),
                )
            })
            .collect(),
        diagnostics: checker.diagnostics().clone(),
    }
}

#[allow(clippy::too_many_lines)] // Check the written base, provider, and inherited signature together.
fn assert_applied_base(
    checker: &mut CanonicalCheckerContext<'_>,
    provider: &ParseResult,
    consumer: &ParseResult,
    argument: TypeId,
) {
    assert!(checked(checker, PROVIDER));
    assert!(checked(checker, CONSUMER));
    let base_owner = symbol(checker, declaration(provider, PROVIDER, "Base"));
    let cache_owner = symbol(checker, declaration(consumer, CONSUMER, "Cache"));
    let import = symbol(checker, declaration(consumer, CONSUMER, "ImportedBase"));
    assert_ne!(import, base_owner);
    assert_eq!(
        checker.store().symbol(import).unwrap().flags(),
        SymbolFlags::ALIAS
    );
    let alias_links = checker.store().alias_symbol_links(import).unwrap();
    assert_eq!(alias_links.immediate_target, Some(base_owner));
    assert_eq!(
        alias_links.alias_target,
        AliasTargetState::Resolved(base_owner)
    );
    assert_eq!(alias_links.type_only_declaration, None);

    let base_instance = checker
        .store()
        .declared_type_links(base_owner)
        .unwrap()
        .declared_type
        .unwrap();
    let base_value = checker
        .store()
        .value_symbol_links(base_owner)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_ne!(base_instance, base_value);
    let TypeData::Interface(base) = checker.store().type_payload(base_instance).unwrap().data()
    else {
        panic!("the provider retains its declared class instance")
    };
    let [formal] = base.reference.resolved_type_arguments.as_deref().unwrap() else {
        panic!("the provider has one source type parameter")
    };
    let formal = *formal;
    let parameter = only_node(provider, PROVIDER, SyntaxKind::TypeParameter);
    assert_eq!(
        checker.store().type_payload(formal).unwrap().symbol(),
        Some(symbol(checker, parameter))
    );
    assert_ne!(formal, argument);

    let heritage = only_node(consumer, CONSUMER, SyntaxKind::ExpressionWithTypeArguments);
    let NodeData::ExpressionWithTypeArguments(written) =
        &consumer.arena.get(heritage.node).unwrap().data
    else {
        unreachable!()
    };
    let expression = NodeRef::new(consumer.arena.id(), CONSUMER, written.expression);
    let [argument_node] = written.type_arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("the base has one written type argument")
    };
    let argument_node = NodeRef::new(consumer.arena.id(), CONSUMER, *argument_node);
    let applied = cached_type(checker, heritage);
    assert_ne!(applied, base_instance);
    assert_eq!(cached_type(checker, argument_node), argument);
    assert_eq!(cached_type(checker, expression), base_value);
    assert_eq!(checker.get_symbol_at_location(expression), Ok(Some(import)));
    assert_eq!(checker.get_type_at_location(expression), Ok(base_value));
    let TypeData::TypeReference(reference) = checker.store().type_payload(applied).unwrap().data()
    else {
        panic!("the written generic base keeps its applied reference")
    };
    assert_eq!(reference.object.target, Some(base_instance));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[argument][..])
    );

    let members = checker.get_nongeneric_class_members(cache_owner).unwrap();
    let base = members.base().unwrap();
    assert_eq!(base.symbol(), base_owner);
    assert_eq!(base.instance_type(), base_instance);
    assert_eq!(base.applied_instance_type(), applied);
    assert_eq!(base.value_type(), base_value);
    let constructor = checker
        .store()
        .signature(members.default_construct_signature())
        .unwrap();
    assert!(constructor.parameters().is_empty());
    assert_eq!(
        constructor.resolved_return_type(),
        Some(members.shells().instance_type())
    );
    let TypeData::Interface(derived) = checker
        .store()
        .type_payload(members.shells().instance_type())
        .unwrap()
        .data()
    else {
        unreachable!()
    };
    assert_eq!(derived.resolved_base_types.as_deref(), Some(&[applied][..]));

    let method = only_node(provider, PROVIDER, SyntaxKind::MethodDeclaration);
    let original = checker
        .store()
        .signature_links(method)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    assert_eq!(
        checker
            .store()
            .signature(original)
            .unwrap()
            .resolved_return_type(),
        Some(formal)
    );
    let access = only_node(consumer, CONSUMER, SyntaxKind::PropertyAccessExpression);
    let callable = checker.get_type_at_location(access).unwrap();
    let TypeData::Object(object) = checker.store().type_payload(callable).unwrap().data() else {
        panic!("the inherited method has a callable object type")
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("the inherited method has one signature")
    };
    let signature = checker.store().signature(*signature).unwrap();
    assert_eq!(signature.declaration(), Some(method));
    assert_eq!(signature.target(), Some(original));
    assert!(signature.mapper().is_some());
    assert_eq!(signature.resolved_return_type(), Some(argument));
    let [parameter] = signature.parameters() else {
        panic!("read has one parameter")
    };
    assert_eq!(
        checker
            .store()
            .value_symbol_links(*parameter)
            .unwrap()
            .resolved_type,
        Some(argument)
    );
    let result = declaration(consumer, CONSUMER, "result");
    let NodeData::VariableDeclaration(result) = &consumer.arena.get(result.node).unwrap().data
    else {
        unreachable!()
    };
    let call = NodeRef::new(consumer.arena.id(), CONSUMER, result.initializer.unwrap());
    assert_eq!(checker.get_type_at_location(call), Ok(argument));
}

#[test]
fn imported_generic_class_base_preserves_listener_and_provider_identities() {
    let provider = parse_source_file(BASE);
    let consumer = parse_source_file(concat!(
        "import { Base as ImportedBase } from './base';\n",
        "type Listener = (event: string) => void;\n",
        "export class Cache extends ImportedBase<Listener> { constructor() { super(); } }\n",
        "declare const cache: Cache;\n",
        "declare const listener: Listener;\n",
        "const result: Listener = cache.read(listener);\n",
    ));
    let listener = declaration(&consumer, CONSUMER, "Listener");
    let NodeData::TypeAliasDeclaration(listener) = &consumer.arena.get(listener.node).unwrap().data
    else {
        unreachable!()
    };
    let listener = NodeRef::new(consumer.arena.id(), CONSUMER, listener.type_);
    for provider_first in [false, true] {
        let mut checker = context(&provider, &consumer);
        assert!(!checked(&checker, PROVIDER));
        if provider_first {
            checker.check_source_file(PROVIDER).unwrap();
        }
        checker.check_source_file(CONSUMER).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let argument = checker.get_type_from_type_node(listener).unwrap();
        assert_applied_base(&mut checker, &provider, &consumer, argument);
        let warm = snapshot(&checker, &provider, &consumer);
        for _ in 0..2 {
            checker.recheck_source_file(CONSUMER).unwrap();
            checker.recheck_source_file(PROVIDER).unwrap();
            assert_eq!(checker.get_type_from_type_node(listener), Ok(argument));
            assert_applied_base(&mut checker, &provider, &consumer, argument);
            assert_eq!(snapshot(&checker, &provider, &consumer), warm);
        }
    }
}

#[test]
fn imported_generic_class_base_keeps_native_argument_error() {
    let provider = parse_source_file(BASE);
    let consumer = parse_source_file(concat!(
        "import { Base as ImportedBase } from './base';\n",
        "export class Cache extends ImportedBase<string> { constructor() { super(); } }\n",
        "declare const cache: Cache;\n",
        "const result: string = cache.read(1);\n",
    ));
    let bad = only_node(&consumer, CONSUMER, SyntaxKind::NumericLiteral);
    for provider_first in [false, true] {
        let mut checker = context(&provider, &consumer);
        if provider_first {
            checker.check_source_file(PROVIDER).unwrap();
        }
        checker.check_source_file(CONSUMER).unwrap();
        let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
        assert_applied_base(&mut checker, &provider, &consumer, string);
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("one invalid call must retain one argument diagnostic")
        };
        assert_eq!(diagnostic.node, Some(bad));
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Argument of type 'number' is not assignable to parameter of type 'string'."
        );
        let range = consumer.arena.get(bad.node).unwrap().range;
        assert_eq!(
            diagnostic
                .range_override
                .map_or(range, |override_| override_.range()),
            range
        );
        assert!(diagnostic.related_information.is_empty());
        let warm = snapshot(&checker, &provider, &consumer);
        for _ in 0..2 {
            checker.recheck_source_file(CONSUMER).unwrap();
            checker.recheck_source_file(PROVIDER).unwrap();
            assert_applied_base(&mut checker, &provider, &consumer, string);
            assert_eq!(snapshot(&checker, &provider, &consumer), warm);
        }
    }
}
