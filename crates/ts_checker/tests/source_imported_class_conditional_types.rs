use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, ConditionalRootId, DeclaredTypeLinks, IntrinsicBootstrapOptions,
    SourceFileLinks, SymbolNodeLinks, TypeAliasLinks, TypeData, TypeId, TypeNodeLinks,
    type_records::{InterfaceTypeData, TypeCacheState},
    types::{ObjectFlags, TypeFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(205_710);
const PROVIDER: FileId = FileId::new(205_711);
const PROVIDER_TEXT: &str = concat!(
    "export class Container<E = number, S = string, P extends string = string> {\n",
    "  value: E;\n",
    "  constructor(value: E) { this.value = value; }\n",
    "}\n",
    "export class Other<E = number, S = string, P extends string = string> {\n",
    "  other: E;\n",
    "  constructor(other: E) { this.other = other; }\n",
    "}\n",
    "export interface Shape<E = number> { value: E; }\n",
    "export type RecordShape<E = number> = { value: E };\n",
);

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn child(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> NodeRef {
    let record = parsed.arena.get(id).unwrap();
    let owner = parsed.arena.get(parent.node).unwrap();
    assert_eq!(record.parent, Some(parent.node));
    assert!(owner.range.start <= record.range.start);
    assert!(record.range.end <= owner.range.end);
    node(parsed, parent.file, id)
}

fn named(parsed: &ParseResult, file: FileId, kind: SyntaxKind, name: &str) -> NodeRef {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        if record.kind != kind {
            return None;
        }
        let name_id = match &record.data {
            NodeData::TypeAliasDeclaration(data) => data.name,
            NodeData::ClassDeclaration(data) => data.name.unwrap(),
            NodeData::InterfaceDeclaration(data) => data.name,
            NodeData::ImportSpecifier(data) => data.name,
            NodeData::VariableDeclaration(data) => data.name,
            _ => panic!("the named node must be a declaration or import specifier"),
        };
        let NodeData::Identifier(identifier) = &parsed.arena.get(name_id).unwrap().data else {
            panic!("the fixture uses identifier names")
        };
        (identifier.text == name).then_some(node(parsed, file, id))
    });
    let result = matches.next().unwrap_or_else(|| panic!("missing {name}"));
    assert!(matches.next().is_none(), "duplicate {name}");
    result
}

fn alias_body(parsed: &ParseResult, name: &str) -> NodeRef {
    let declaration = named(parsed, SOURCE, SyntaxKind::TypeAliasDeclaration, name);
    let NodeData::TypeAliasDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    child(parsed, declaration, data.type_)
}

fn reference_arguments(parsed: &ParseResult, reference: NodeRef) -> Vec<NodeRef> {
    let NodeData::TypeReferenceNode(data) = &parsed.arena.get(reference.node).unwrap().data else {
        panic!("the fixture must keep its real type reference")
    };
    data.type_arguments
        .as_ref()
        .map(|arguments| {
            arguments
                .nodes
                .iter()
                .map(|&argument| child(parsed, reference, argument))
                .collect()
        })
        .unwrap_or_default()
}

fn context<'arena>(
    source: &'arena ParseResult,
    provider: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (SOURCE, source, "\"/project/consumer.ts\""),
        (PROVIDER, provider, "\"/project/provider.ts\""),
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
    let mut imports = source.arena.iter().filter_map(|(id, record)| {
        let NodeData::ImportDeclaration(data) = &record.data else {
            return None;
        };
        Some(child(
            source,
            node(source, SOURCE, id),
            data.module_specifier,
        ))
    });
    let specifier = imports.next().unwrap();
    assert!(imports.next().is_none());
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
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

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn query_alias(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
) -> TypeId {
    let declaration = named(parsed, SOURCE, SyntaxKind::TypeAliasDeclaration, name);
    let owner = symbol(context, declaration);
    let result = context.get_declared_type_of_symbol(owner).unwrap();
    let body = alias_body(parsed, name);
    assert_eq!(context.get_type_from_type_node(body), Ok(result));
    assert_eq!(context.get_type_at_location(body), Ok(result));
    result
}

fn assert_import(
    context: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
    local_name: &str,
    target: NodeRef,
) {
    let binding = named(source, SOURCE, SyntaxKind::ImportSpecifier, local_name);
    let imported = symbol(context, binding);
    let target = symbol(context, target);
    assert_ne!(imported, target);
    let links = context.store().alias_symbol_links(imported).unwrap();
    assert_eq!(links.immediate_target, Some(target));
    assert_eq!(links.alias_target, AliasTargetState::Resolved(target));
    assert_eq!(links.type_only_declaration, Some(binding));
}

fn class_target(
    context: &mut CanonicalCheckerContext<'_>,
    provider: &ParseResult,
    name: &str,
) -> TypeId {
    let declaration = named(provider, PROVIDER, SyntaxKind::ClassDeclaration, name);
    let owner = symbol(context, declaration);
    let target = context.get_declared_type_of_symbol(owner).unwrap();
    let record = context.store().type_payload(target).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    assert!(record.object_flags().contains(ObjectFlags::CLASS));
    let TypeData::Interface(data) = record.data() else {
        panic!("the source class must keep its declared instance target")
    };
    assert_eq!(data.outer_type_parameter_count, 0);
    assert_eq!(data.reference.object.target, Some(target));
    assert_eq!(
        data.reference
            .resolved_type_arguments
            .as_ref()
            .unwrap()
            .len(),
        3
    );
    target
}

fn assert_instance(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    target: TypeId,
    arguments: &[TypeId],
) {
    let record = context.store().type_payload(type_).unwrap();
    let TypeData::TypeReference(data) = record.data() else {
        panic!("the imported class must use the normal instance reference")
    };
    assert_eq!(data.object.target, Some(target));
    assert_eq!(data.resolved_type_arguments.as_deref(), Some(arguments));
    assert_eq!(
        record.symbol(),
        context.store().type_payload(target).unwrap().symbol()
    );
}

fn assert_infer_owner(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    alias: &str,
    class: TypeId,
) {
    let declaration = named(source, SOURCE, SyntaxKind::TypeAliasDeclaration, alias);
    let NodeData::TypeAliasDeclaration(data) = &source.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let [outer] = data.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("the conditional alias has one outer formal")
    };
    let outer = child(source, declaration, *outer);
    let body = alias_body(source, alias);
    let NodeData::ConditionalTypeNode(data) = &source.arena.get(body.node).unwrap().data else {
        panic!("the alias must retain its real conditional type")
    };
    let extends = child(source, body, data.extends_type);
    let arguments = reference_arguments(source, extends);
    assert_eq!(arguments.len(), 3);
    let NodeData::InferTypeNode(data) = &source.arena.get(arguments[0].node).unwrap().data else {
        panic!("the first imported class argument must be infer E")
    };
    let inferred = child(source, arguments[0], data.type_parameter);
    let inferred_symbol = symbol(context, inferred);
    let outer_symbol = symbol(context, outer);
    assert_ne!(inferred_symbol, outer_symbol);
    let inferred_type = context
        .get_declared_type_of_symbol(inferred_symbol)
        .unwrap();
    let outer_type = context.get_declared_type_of_symbol(outer_symbol).unwrap();
    assert_ne!(inferred_type, outer_type);
    let conditional = query_alias(context, source, alias);
    let TypeData::Conditional(data) = context.store().type_payload(conditional).unwrap().data()
    else {
        panic!("the generic conditional must retain its root")
    };
    let root = context.store().conditional_root(data.root).unwrap();
    assert_eq!(root.node(), body);
    assert_eq!(root.check_type(), outer_type);
    assert!(root.is_distributive());
    assert_eq!(root.outer_type_parameters(), Some([outer_type].as_slice()));
    assert_eq!(
        root.infer_type_parameters(),
        Some([inferred_type].as_slice())
    );
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    assert_instance(
        context,
        root.extends_type(),
        class,
        &[inferred_type, string, string],
    );
    let record = context.store().type_payload(inferred_type).unwrap();
    assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
    assert_eq!(record.symbol(), Some(inferred_symbol));
    let TypeData::TypeParameter(data) = record.data() else {
        unreachable!()
    };
    assert!(!data.is_this_type);
    assert_eq!(data.target, None);
    assert_eq!(data.mapper, None);
}

#[derive(Debug, PartialEq, Eq)]
struct State {
    counts: [usize; 6],
    sources: Vec<Option<SourceFileLinks>>,
    nodes: Vec<(NodeRef, Option<TypeNodeLinks>, Option<SymbolNodeLinks>)>,
    symbols: Vec<(
        SemanticSymbolId,
        Option<AliasSymbolLinks>,
        Option<DeclaredTypeLinks>,
        Option<TypeAliasLinks>,
    )>,
    classes: Vec<(TypeId, InterfaceTypeData)>,
    roots: Vec<(ConditionalRootId, TypeCacheState)>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn state(context: &CanonicalCheckerContext<'_>) -> State {
    let store = context.store();
    State {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.conditional_root_len(),
        ],
        sources: context
            .file_order()
            .iter()
            .map(|&file| {
                store
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned()
            })
            .collect(),
        nodes: context
            .file_order()
            .iter()
            .flat_map(|&file| {
                let arena = context.file(file).unwrap().0;
                arena.iter().map(move |(id, _)| {
                    let node = NodeRef::new(arena.id(), file, id);
                    (
                        node,
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
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
                    store.alias_symbol_links(symbol).cloned(),
                    store.declared_type_links(symbol).cloned(),
                    store.type_alias_links(symbol).cloned(),
                )
            })
            .collect(),
        classes: store
            .types()
            .filter_map(|(type_, record)| {
                let TypeData::Interface(data) = record.data() else {
                    return None;
                };
                Some((type_, data.clone()))
            })
            .collect(),
        roots: store
            .types()
            .filter_map(|(_, record)| {
                let TypeData::Conditional(data) = record.data() else {
                    return None;
                };
                let root = store.conditional_root(data.root).unwrap();
                Some((root.id(), root.instantiations().clone()))
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn replay(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    aliases: &[(&str, TypeId)],
    references: &[(NodeRef, TypeId)],
) {
    let before = state(context);
    for _ in 0..2 {
        context.check_source_file(SOURCE).unwrap();
        context.recheck_source_file(SOURCE).unwrap();
        context.recheck_source_file(PROVIDER).unwrap();
        for &(name, expected) in aliases {
            assert_eq!(query_alias(context, source, name), expected);
        }
        for &(node, expected) in references {
            assert_eq!(context.get_type_from_type_node(node), Ok(expected));
        }
        assert_eq!(state(context), before);
    }
}

#[test]
fn imported_class_infer_keeps_explicit_and_defaulted_instance_arguments() {
    let provider = parse_source_file(PROVIDER_TEXT);
    let source = parse_source_file(concat!(
        "import type { Container as Imported } from './provider';\n",
        "type Environment<T> = T extends Imported<infer E, string, string> ? E : never;\n",
        "type Text = Environment<Imported<string, string, string>>;\n",
        "type Defaulted = Environment<Imported>;\n",
        "type Expanded = Environment<Imported<number, string, string>>;\n",
        "const text: Text = 'ok';\n",
        "const number: Defaulted = 1;\n",
    ));
    for query_first in [false, true] {
        let mut context = context(&source, &provider);
        let early = query_first.then(|| {
            ["Text", "Defaulted", "Expanded"].map(|name| query_alias(&mut context, &source, name))
        });
        context.check_source_file(SOURCE).unwrap();
        context.check_source_file(PROVIDER).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let results = ["Text", "Defaulted", "Expanded"]
            .map(|name| (name, query_alias(&mut context, &source, name)));
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (number, string) = (bootstrap.number_type, bootstrap.string_type);
        assert_eq!(results.map(|(_, type_)| type_), [string, number, number]);
        if let Some(early) = early {
            assert_eq!(early, results.map(|(_, type_)| type_));
        }
        let target = class_target(&mut context, &provider, "Container");
        assert_import(
            &context,
            &source,
            "Imported",
            named(
                &provider,
                PROVIDER,
                SyntaxKind::ClassDeclaration,
                "Container",
            ),
        );
        assert_infer_owner(&mut context, &source, "Environment", target);
        let references = results.map(|(name, _)| {
            let arguments = reference_arguments(&source, alias_body(&source, name));
            assert_eq!(arguments.len(), 1);
            let reference = arguments[0];
            (
                reference,
                context.get_type_from_type_node(reference).unwrap(),
            )
        });
        let owner = symbol(
            &context,
            named(
                &provider,
                PROVIDER,
                SyntaxKind::ClassDeclaration,
                "Container",
            ),
        );
        for &(reference, _) in &references {
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(reference)
                    .and_then(|links| links.resolved_symbol),
                Some(owner),
            );
        }
        assert_eq!(reference_arguments(&source, references[0].0).len(), 3);
        assert!(reference_arguments(&source, references[1].0).is_empty());
        assert_eq!(reference_arguments(&source, references[2].0).len(), 3);
        assert_instance(&context, references[0].1, target, &[string, string, string]);
        assert_instance(&context, references[1].1, target, &[number, string, string]);
        assert_instance(&context, references[2].1, target, &[number, string, string]);
        assert_eq!(references[1].1, references[2].1);
        assert_ne!(references[0].1, references[1].1);
        replay(&mut context, &source, &results, &references);
    }
}

#[test]
fn imported_class_conditional_keeps_other_class_and_existing_type_import_owners() {
    let provider = parse_source_file(PROVIDER_TEXT);
    let source = parse_source_file(concat!(
        "import type { Container as Imported, Other, Shape, RecordShape } from './provider';\n",
        "type Environment<T> = T extends Imported<infer E, string, string> ? E : never;\n",
        "type OtherEnvironment<T> = T extends Other<infer E, string, string> ? E : never;\n",
        "type InterfaceEnvironment<T> = T extends Shape<infer E> ? E : never;\n",
        "type AliasEnvironment<T> = T extends RecordShape<infer E> ? E : never;\n",
        "type WrongOwner = Environment<Other<boolean>>;\n",
        "type OtherOwner = OtherEnvironment<Other<boolean>>;\n",
        "type InterfaceResult = InterfaceEnvironment<Shape<string>>;\n",
        "type AliasResult = AliasEnvironment<RecordShape<number>>;\n",
    ));
    let mut context = context(&source, &provider);
    let results = ["WrongOwner", "OtherOwner", "InterfaceResult", "AliasResult"]
        .map(|name| (name, query_alias(&mut context, &source, name)));
    context.check_source_file(SOURCE).unwrap();
    context.check_source_file(PROVIDER).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(
        results.map(|(_, type_)| type_),
        [
            bootstrap.never_type,
            bootstrap.boolean_type,
            bootstrap.string_type,
            bootstrap.number_type
        ],
    );
    let container = class_target(&mut context, &provider, "Container");
    let other = class_target(&mut context, &provider, "Other");
    assert_ne!(container, other);
    assert_infer_owner(&mut context, &source, "Environment", container);
    assert_infer_owner(&mut context, &source, "OtherEnvironment", other);
    for (local, name, kind) in [
        ("Imported", "Container", SyntaxKind::ClassDeclaration),
        ("Other", "Other", SyntaxKind::ClassDeclaration),
        ("Shape", "Shape", SyntaxKind::InterfaceDeclaration),
        (
            "RecordShape",
            "RecordShape",
            SyntaxKind::TypeAliasDeclaration,
        ),
    ] {
        assert_import(
            &context,
            &source,
            local,
            named(&provider, PROVIDER, kind, name),
        );
    }
    replay(&mut context, &source, &results, &[]);
}

#[test]
fn imported_class_conditional_results_keep_assignment_diagnostics() {
    let provider = parse_source_file(PROVIDER_TEXT);
    let source = parse_source_file(concat!(
        "import type { Container as Imported } from './provider';\n",
        "type Environment<T> = T extends Imported<infer E, string, string> ? E : never;\n",
        "type Text = Environment<Imported<string>>;\n",
        "type Number = Environment<Imported>;\n",
        "declare const text: string;\n",
        "declare const number: number;\n",
        "const wrongText: Text = number;\n",
        "const wrongNumber: Number = text;\n",
    ));
    let mut context = context(&source, &provider);
    context.check_source_file(SOURCE).unwrap();
    context.check_source_file(PROVIDER).unwrap();
    let results = ["Text", "Number"].map(|name| (name, query_alias(&mut context, &source, name)));
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(
        results.map(|(_, type_)| type_),
        [bootstrap.string_type, bootstrap.number_type]
    );
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
    for (diagnostic, name, message) in [
        (
            &diagnostics[0],
            "wrongText",
            "Type 'number' is not assignable to type 'string'.",
        ),
        (
            &diagnostics[1],
            "wrongNumber",
            "Type 'string' is not assignable to type 'number'.",
        ),
    ] {
        let declaration = named(&source, SOURCE, SyntaxKind::VariableDeclaration, name);
        let NodeData::VariableDeclaration(data) = &source.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.node,
            Some(child(&source, declaration, data.name))
        );
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert!(diagnostic.diagnostic.details.is_empty());
        assert!(diagnostic.related_information.is_empty());
    }
    replay(&mut context, &source, &results, &[]);
}
