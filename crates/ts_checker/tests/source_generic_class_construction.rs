use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, CheckFlags, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostic, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, DeclaredTypeLinks, IntrinsicBootstrapOptions, SignatureId,
    SignatureLinks, SourceCheckError, SourceFileLinks, SymbolNodeLinks, TypeData, TypeId,
    TypeMapperId, TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks,
    signatures::SignatureFlags, types::TypeFlags,
};
use ts_options::{ModuleKind, ScriptTarget};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(204_301);
const LIBRARIES: [(FileId, &str, &str); 3] = [
    (
        FileId::new(204_302),
        "\"/lib/lib.es5.d.ts\"",
        include_str!("../../ts_bundled/libs/lib.es5.d.ts"),
    ),
    (
        FileId::new(204_303),
        "\"/lib/lib.decorators.d.ts\"",
        include_str!("../../ts_bundled/libs/lib.decorators.d.ts"),
    ),
    (
        FileId::new(204_304),
        "\"/lib/lib.decorators.legacy.d.ts\"",
        include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
    ),
];

// These are local concrete constructions, not Query's config or import inference.
fn context<'arena>(
    parsed: &'arena ParseResult,
    libraries: &'arena [ParseResult; 3],
) -> CanonicalCheckerContext<'arena> {
    let mut files = LIBRARIES
        .iter()
        .zip(libraries)
        .map(|(&(file, path, _), parsed)| (file, path, parsed, true))
        .collect::<Vec<_>>();
    files.push((
        FILE,
        "\"/project/generic-class-construction.ts\"",
        parsed,
        false,
    ));
    let mut binder = CanonicalBinder::new();
    for &(file, path, parsed, library) in &files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    library,
                    library,
                    if library {
                        CanonicalModuleState::Script
                    } else {
                        CanonicalModuleState::External
                    },
                ),
            )
            .unwrap();
    }
    for &(file, _, parsed, _) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, _, parsed, _)| (file, &parsed.arena))
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
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn named(parsed: &ParseResult, kind: SyntaxKind, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::ClassDeclaration(data) => data.name?,
                NodeData::VariableDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(node(parsed, id))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {expected}"))
}

fn initializer(parsed: &ParseResult, name: &str) -> NodeRef {
    let declaration = named(parsed, SyntaxKind::VariableDeclaration, name);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    node(parsed, data.initializer.unwrap())
}

fn annotation(parsed: &ParseResult, name: &str) -> NodeRef {
    let declaration = named(parsed, SyntaxKind::VariableDeclaration, name);
    let NodeData::VariableDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    node(parsed, data.type_.unwrap())
}

fn constructor_declarations(parsed: &ParseResult, class: NodeRef) -> Vec<NodeRef> {
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        panic!("expected the actual class declaration")
    };
    data.members
        .nodes
        .iter()
        .filter(|&&id| parsed.arena.get(id).unwrap().kind == SyntaxKind::Constructor)
        .map(|&id| node(parsed, id))
        .collect()
}

fn member(parsed: &ParseResult, class: NodeRef, expected: &str) -> NodeRef {
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        unreachable!()
    };
    data.members
        .nodes
        .iter()
        .find_map(|&id| {
            let name = match &parsed.arena.get(id)?.data {
                NodeData::PropertyDeclaration(data) => data.name,
                NodeData::MethodDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(node(parsed, id))
        })
        .unwrap_or_else(|| panic!("missing class member {expected}"))
}

fn new_parts(parsed: &ParseResult, construction: NodeRef) -> (NodeRef, Vec<NodeRef>, Vec<NodeRef>) {
    let NodeData::NewExpression(data) = &parsed.arena.get(construction.node).unwrap().data else {
        panic!("expected the actual New expression")
    };
    (
        node(parsed, data.expression),
        data.arguments
            .as_ref()
            .map(|list| list.nodes.iter().map(|&id| node(parsed, id)).collect())
            .unwrap_or_default(),
        data.type_arguments
            .as_ref()
            .map(|list| list.nodes.iter().map(|&id| node(parsed, id)).collect())
            .unwrap_or_default(),
    )
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn value(context: &CanonicalCheckerContext<'_>, symbol: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(symbol)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

#[derive(Debug, Eq, PartialEq)]
struct Origin {
    declaration: NodeRef,
    owner: SemanticSymbolId,
    local: SemanticSymbolId,
    instance: TypeId,
    value: TypeId,
    formals: Vec<TypeId>,
    this_type: TypeId,
    constructors: Vec<SignatureId>,
    implementation: Option<SignatureId>,
}

#[allow(clippy::too_many_lines)] // The original constructor group and class formals share one owner.
fn origin(context: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult, name: &str) -> Origin {
    let declaration = named(parsed, SyntaxKind::ClassDeclaration, name);
    let owner = symbol(context, declaration);
    let local = context
        .file(FILE)
        .unwrap()
        .1
        .local_symbol(declaration)
        .unwrap_or(owner);
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let instance = context.get_declared_type_of_symbol(owner).unwrap();
    let class_value = value(context, owner);
    assert_eq!(members.shells().declaration(), declaration);
    assert_eq!(members.shells().symbol(), owner);
    assert_eq!(members.shells().instance_type(), instance);
    assert_eq!(members.shells().value_type(), class_value);
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data else {
        unreachable!()
    };
    let parameters = &data.type_parameters.as_ref().unwrap().nodes;
    let formals = parameters
        .iter()
        .map(|&id| {
            let parameter = node(parsed, id);
            assert_eq!(parsed.arena.get(id).unwrap().parent, Some(declaration.node));
            let formal_owner = symbol(context, parameter);
            let formal = context.get_declared_type_of_symbol(formal_owner).unwrap();
            let store = context.store();
            assert_eq!(store.symbol(formal_owner).unwrap().parent(), Some(owner));
            assert_eq!(
                store.symbol(formal_owner).unwrap().declarations(),
                Some(&[parameter][..])
            );
            let record = store.type_payload(formal).unwrap();
            assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
            assert_eq!(record.symbol(), Some(formal_owner));
            let TypeData::TypeParameter(data) = record.data() else {
                panic!("the original formal must remain a type parameter")
            };
            assert!(!data.is_this_type);
            assert_eq!(data.target, None);
            assert_eq!(data.mapper, None);
            formal
        })
        .collect::<Vec<_>>();
    let store = context.store();
    if local != owner {
        assert_eq!(
            store.symbol(local).unwrap().flags(),
            SymbolFlags::EXPORT_VALUE
        );
        assert_eq!(store.symbol(local).unwrap().export_symbol(), Some(owner));
    }
    let TypeData::Interface(data) = store.type_payload(instance).unwrap().data() else {
        panic!("the class origin must keep its generic interface storage")
    };
    assert_eq!(data.reference.object.target, Some(instance));
    assert_eq!(
        data.reference.resolved_type_arguments.as_deref(),
        Some(formals.as_slice())
    );
    let this_type = data.this_type.unwrap();
    let mut all = formals.clone();
    all.push(this_type);
    assert_eq!(data.all_type_parameters.as_deref(), Some(all.as_slice()));
    let TypeData::TypeParameter(this) = store.type_payload(this_type).unwrap().data() else {
        unreachable!()
    };
    assert!(this.is_this_type);
    assert_eq!(this.constraint, Some(instance));
    let TypeData::Object(data) = store.type_payload(class_value).unwrap().data() else {
        panic!("the class value must retain its construct-signature object")
    };
    assert_eq!(data.structured.call_signature_count, 0);
    let constructors = data.structured.signatures.clone().unwrap();
    let declarations = constructor_declarations(parsed, declaration);
    let public = declarations
        .iter()
        .copied()
        .filter(|declaration| {
            let NodeData::ConstructorDeclaration(data) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                unreachable!()
            };
            data.body.is_none()
        })
        .collect::<Vec<_>>();
    let implementation = if public.is_empty() {
        if let [written] = declarations.as_slice() {
            assert_eq!(constructors, [signature(context, *written)]);
        } else {
            assert!(declarations.is_empty());
            assert_eq!(constructors, [members.default_construct_signature()]);
        }
        None
    } else {
        assert_eq!(
            constructors,
            public
                .iter()
                .map(|&node| signature(context, node))
                .collect::<Vec<_>>()
        );
        let hidden = declarations
            .iter()
            .copied()
            .find(|node| !public.contains(node))
            .unwrap();
        let hidden = signature(context, hidden);
        assert!(!constructors.contains(&hidden));
        Some(hidden)
    };
    for &constructor in constructors.iter().chain(implementation.iter()) {
        let record = store.signature(constructor).unwrap();
        assert!(record.flags().contains(SignatureFlags::CONSTRUCT));
        assert_eq!(record.type_parameters(), formals);
        assert_eq!(record.this_parameter(), None);
        assert_eq!(record.target(), None);
        assert_eq!(record.mapper(), None);
        assert_eq!(record.resolved_return_type(), Some(instance));
        assert!(!record.type_parameters().contains(&this_type));
        if let Some(declaration) = record.declaration() {
            let NodeData::ConstructorDeclaration(data) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("the constructor must keep its actual declaration")
            };
            let parameters = data
                .parameters
                .nodes
                .iter()
                .map(|&id| symbol(context, node(parsed, id)))
                .collect::<Vec<_>>();
            assert_eq!(record.parameters(), parameters);
        }
    }
    Origin {
        declaration,
        owner,
        local,
        instance,
        value: class_value,
        formals,
        this_type,
        constructors,
        implementation,
    }
}

#[derive(Debug, Eq, PartialEq)]
struct Construction {
    node: NodeRef,
    instance: TypeId,
    signature: SignatureId,
    mapper: TypeMapperId,
}

fn assert_reference(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    target: TypeId,
    arguments: &[TypeId],
) {
    let TypeData::TypeReference(data) = context.store().type_payload(type_).unwrap().data() else {
        panic!("the result must remain the canonical applied class reference")
    };
    assert_eq!(data.object.target, Some(target));
    assert_eq!(data.resolved_type_arguments.as_deref(), Some(arguments));
}

fn construction(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
    origin: &Origin,
    arguments: &[TypeId],
    selected_index: usize,
) -> Construction {
    let new = initializer(parsed, name);
    let checked = construction_at(context, parsed, new, origin, arguments, selected_index);
    assert_eq!(
        value(
            context,
            symbol(
                context,
                named(parsed, SyntaxKind::VariableDeclaration, name)
            )
        ),
        checked.instance
    );
    checked
}

fn construction_at(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    new: NodeRef,
    origin: &Origin,
    arguments: &[TypeId],
    selected_index: usize,
) -> Construction {
    let (callee, _, written) = new_parts(parsed, new);
    assert_eq!(arguments.len(), origin.formals.len());
    let instance = context.get_type_at_location(new).unwrap();
    assert_reference(context, instance, origin.instance, arguments);
    assert_eq!(context.get_type_at_location(callee), Ok(origin.value));
    let selected = signature(context, new);
    assert_eq!(context.get_return_type_of_signature(selected), Ok(instance));
    for (&node, &expected) in written.iter().zip(arguments) {
        assert_eq!(context.get_type_from_type_node(node), Ok(expected));
    }
    let store = context.store();
    assert_eq!(
        store.symbol_node_links(callee),
        Some(&SymbolNodeLinks {
            resolved_symbol: Some(origin.local)
        })
    );
    let original = store
        .signature(origin.constructors[selected_index])
        .unwrap();
    let record = store.signature(selected).unwrap();
    assert_ne!(selected, original.id());
    assert_eq!(record.target(), Some(original.id()));
    assert_eq!(record.declaration(), original.declaration());
    assert_eq!(
        record.flags(),
        original.flags() & SignatureFlags::PROPAGATING_FLAGS
    );
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.this_parameter(), None);
    assert_eq!(record.min_argument_count(), original.min_argument_count());
    assert_eq!(record.parameters().len(), original.parameters().len());
    let mapper = record.mapper().unwrap();
    for (&formal, &argument) in origin.formals.iter().zip(arguments) {
        assert_eq!(store.map_type(mapper, formal), Some(argument));
    }
    for (&copied, &parameter) in record.parameters().iter().zip(original.parameters()) {
        assert_ne!(copied, parameter);
        let original_symbol = store.symbol(parameter).unwrap();
        let copied_symbol = store.symbol(copied).unwrap();
        assert_eq!(copied_symbol.declarations(), original_symbol.declarations());
        let links = store.value_symbol_links(copied).unwrap();
        assert_eq!(links.target, Some(parameter));
        assert_eq!(links.mapper, Some(mapper));
        let expected = store.map_type(mapper, value(context, parameter)).unwrap();
        assert_eq!(links.resolved_type, Some(expected));
    }
    Construction {
        node: new,
        instance,
        signature: selected,
        mapper,
    }
}

fn assert_field_read(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
    origin: &Origin,
    receiver: TypeId,
    expected: TypeId,
) {
    let access = initializer(parsed, name);
    let NodeData::PropertyAccessExpression(data) = &parsed.arena.get(access.node).unwrap().data
    else {
        panic!("the read must retain its real property access")
    };
    assert_eq!(
        context.get_type_at_location(node(parsed, data.expression)),
        Ok(receiver)
    );
    assert_eq!(context.get_type_at_location(access), Ok(expected));
    let copied = context
        .get_symbol_at_location(node(parsed, data.name))
        .unwrap()
        .unwrap();
    let NodeData::Identifier(name) = &parsed.arena.get(data.name).unwrap().data else {
        unreachable!()
    };
    let expected_member = symbol(context, member(parsed, origin.declaration, &name.text));
    let store = context.store();
    let links = store.value_symbol_links(copied).unwrap();
    let original = links.target.unwrap();
    assert_eq!(original, expected_member);
    assert_eq!(store.symbol(original).unwrap().parent(), Some(origin.owner));
    assert!(
        store
            .symbol(copied)
            .unwrap()
            .check_flags()
            .contains(CheckFlags::INSTANTIATED)
    );
    assert_eq!(links.resolved_type, Some(expected));
    let mapper = links.mapper.unwrap();
    assert_eq!(store.map_type(mapper, origin.this_type), Some(receiver));
    assert_eq!(
        store.map_type(mapper, value(context, original)),
        Some(expected)
    );
}

fn assert_method_call(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    name: &str,
    origin: &Origin,
    receiver: TypeId,
    expected: TypeId,
) {
    let call = initializer(parsed, name);
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        unreachable!()
    };
    let access = node(parsed, call_data.expression);
    let NodeData::PropertyAccessExpression(data) = &parsed.arena.get(access.node).unwrap().data
    else {
        unreachable!()
    };
    let NodeData::Identifier(name) = &parsed.arena.get(data.name).unwrap().data else {
        unreachable!()
    };
    let declaration = member(parsed, origin.declaration, &name.text);
    let original_member = symbol(context, declaration);
    let original_signature = signature(context, declaration);
    assert_eq!(
        context.get_type_at_location(node(parsed, data.expression)),
        Ok(receiver)
    );
    let callable = context.get_type_at_location(access).unwrap();
    let copied_member = context
        .get_symbol_at_location(node(parsed, data.name))
        .unwrap()
        .unwrap();
    assert_eq!(context.get_type_at_location(call), Ok(expected));
    let selected = signature(context, call);
    assert_eq!(context.get_return_type_of_signature(selected), Ok(expected));
    let store = context.store();
    let record = store.signature(selected).unwrap();
    assert_eq!(record.target(), Some(original_signature));
    assert_eq!(record.declaration(), Some(declaration));
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.flags(), SignatureFlags::NONE);
    let mapper = record.mapper().unwrap();
    assert_eq!(store.map_type(mapper, origin.this_type), Some(receiver));
    let links = store.value_symbol_links(copied_member).unwrap();
    assert_eq!(links.target, Some(original_member));
    assert_eq!(links.mapper, Some(mapper));
    assert_eq!(links.resolved_type, Some(callable));
    let TypeData::Object(object) = store.type_payload(callable).unwrap().data() else {
        unreachable!()
    };
    assert_eq!(object.target, Some(value(context, original_member)));
    assert_eq!(object.mapper, Some(mapper));
    assert_eq!(object.structured.call_signature_count, 1);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[selected][..])
    );
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
    signatures: Vec<(SignatureId, String)>,
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
            .map(|(id, _)| {
                let node = node(parsed, id);
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
        signatures: store
            .signatures()
            .map(|(id, record)| (id, format!("{record:?}")))
            .collect(),
        source: store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn check_source(context: &mut CanonicalCheckerContext<'_>, first: NodeRef, query_first: bool) {
    assert!(
        context
            .store()
            .source_file_links(context.source_file(FILE).unwrap())
            .is_none_or(|links| !links.type_checked)
    );
    // A normal artifact query can check the whole source file.
    let early = query_first.then(|| context.get_type_at_location(first).unwrap());
    context.check_source_file(FILE).unwrap();
    if let Some(early) = early {
        assert_eq!(context.get_type_at_location(first), Ok(early));
    }
}

fn replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    constructions: &[Construction],
    references: &[(NodeRef, TypeId)],
) {
    let warm = publication(context, parsed);
    for _ in 0..2 {
        context.check_source_file(FILE).unwrap();
        assert_eq!(publication(context, parsed), warm);
        context.recheck_source_file(FILE).unwrap();
        for construction in constructions {
            assert_eq!(
                context.get_type_at_location(construction.node),
                Ok(construction.instance)
            );
            assert_eq!(
                signature(context, construction.node),
                construction.signature
            );
            assert_eq!(
                context.get_return_type_of_signature(construction.signature),
                Ok(construction.instance)
            );
            assert_eq!(
                context
                    .store()
                    .signature(construction.signature)
                    .unwrap()
                    .mapper(),
                Some(construction.mapper)
            );
        }
        for &(node, expected) in references {
            assert_eq!(context.get_type_from_type_node(node), Ok(expected));
        }
        assert_eq!(publication(context, parsed), warm);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // One complete source compares written arguments, real defaults and omitted inference.
fn generic_construction_keeps_explicit_defaults_inference_and_canonical_instances() {
    let parsed = parse_source_file(concat!(
        "export class Pair<T, U = T> {\n",
        "  first: T; second: U;\n",
        "  constructor(first: T, second: U) { this.first = first; this.second = second; }\n",
        "  readFirst(): T { return this.first; }\n",
        "  readSecond(): U { return this.second; }\n",
        "}\n",
        "class Defaults<T = string, U = T[]> {}\n",
        "const full = new Pair<string, number>('left', 1);\n",
        "const prefix = new Pair<string>('left', 'right');\n",
        "const inferred = new Pair('left', 1);\n",
        "const defaults = new Defaults();\n",
        "const fullFirst = full.first;\n",
        "const fullSecond = full.second;\n",
        "const inferredFirst = inferred.readFirst();\n",
        "const inferredSecond = inferred.readSecond();\n",
        "declare const fullReference: Pair<string, number>;\n",
        "declare const prefixReference: Pair<string>;\n",
        "declare const defaultReference: Defaults;\n",
    ));
    let libraries = LIBRARIES.map(|(_, _, source)| parse_source_file(source));
    for query_first in [false, true] {
        let mut context = context(&parsed, &libraries);
        check_source(&mut context, initializer(&parsed, "full"), query_first);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let pair = origin(&mut context, &parsed, "Pair");
        assert_ne!(pair.local, pair.owner);
        let default = origin(&mut context, &parsed, "Defaults");
        for (name, written_count) in [
            ("full", Some(2)),
            ("prefix", Some(1)),
            ("inferred", None),
            ("defaults", None),
        ] {
            let construction = initializer(&parsed, name);
            let NodeData::NewExpression(data) = &parsed.arena.get(construction.node).unwrap().data
            else {
                unreachable!()
            };
            assert_eq!(
                data.type_arguments.as_ref().map(|list| list.nodes.len()),
                written_count
            );
        }
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let TypeData::TypeParameter(second) = context
            .store()
            .type_payload(pair.formals[1])
            .unwrap()
            .data()
        else {
            unreachable!()
        };
        assert_eq!(second.resolved_default_type, Some(pair.formals[0]));
        let NodeData::ClassDeclaration(default_data) =
            &parsed.arena.get(default.declaration.node).unwrap().data
        else {
            unreachable!()
        };
        for (index, &id) in default_data
            .type_parameters
            .as_ref()
            .unwrap()
            .nodes
            .iter()
            .enumerate()
        {
            let NodeData::TypeParameterDeclaration(parameter) = &parsed.arena.get(id).unwrap().data
            else {
                unreachable!()
            };
            let written_default = node(&parsed, parameter.default_type.unwrap());
            let default_type = context.get_type_from_type_node(written_default).unwrap();
            let TypeData::TypeParameter(parameter) = context
                .store()
                .type_payload(default.formals[index])
                .unwrap()
                .data()
            else {
                unreachable!()
            };
            assert_eq!(parameter.resolved_default_type, Some(default_type));
            if index == 0 {
                assert_eq!(default_type, string);
            } else {
                assert_reference(
                    &context,
                    default_type,
                    context.global_types().array_type,
                    &[default.formals[0]],
                );
            }
        }
        let default_reference = annotation(&parsed, "defaultReference");
        let expected_default = context.get_type_from_type_node(default_reference).unwrap();
        let TypeData::TypeReference(reference) = context
            .store()
            .type_payload(expected_default)
            .unwrap()
            .data()
        else {
            unreachable!()
        };
        let default_arguments = reference.resolved_type_arguments.clone().unwrap();
        assert_eq!(default_arguments.len(), 2);
        assert_eq!(default_arguments[0], string);
        assert_reference(
            &context,
            default_arguments[1],
            context.global_types().array_type,
            &[string],
        );
        assert_ne!(
            context.global_types().array_type,
            context.global_types().readonly_array_type
        );
        let full = construction(&mut context, &parsed, "full", &pair, &[string, number], 0);
        let prefix = construction(&mut context, &parsed, "prefix", &pair, &[string, string], 0);
        let inferred = construction(
            &mut context,
            &parsed,
            "inferred",
            &pair,
            &[string, number],
            0,
        );
        let defaults = construction(
            &mut context,
            &parsed,
            "defaults",
            &default,
            &default_arguments,
            0,
        );
        assert_eq!(full.instance, inferred.instance);
        assert_eq!(full.signature, inferred.signature);
        assert_eq!(full.mapper, inferred.mapper);
        assert_ne!(full.instance, prefix.instance);
        assert_ne!(full.signature, prefix.signature);
        assert_eq!(defaults.instance, expected_default);
        assert_eq!(
            context
                .store()
                .signature(default.constructors[0])
                .unwrap()
                .declaration(),
            None
        );
        assert_field_read(
            &mut context,
            &parsed,
            "fullFirst",
            &pair,
            full.instance,
            string,
        );
        assert_field_read(
            &mut context,
            &parsed,
            "fullSecond",
            &pair,
            full.instance,
            number,
        );
        for (name, expected) in [("inferredFirst", string), ("inferredSecond", number)] {
            assert_method_call(
                &mut context,
                &parsed,
                name,
                &pair,
                inferred.instance,
                expected,
            );
        }
        let references = [
            (annotation(&parsed, "fullReference"), full.instance),
            (annotation(&parsed, "prefixReference"), prefix.instance),
            (default_reference, defaults.instance),
        ];
        for &(node, expected) in &references {
            assert_eq!(context.get_type_from_type_node(node), Ok(expected));
        }
        for &signature in pair.constructors.iter().chain(&default.constructors) {
            let expected = if pair.constructors.contains(&signature) {
                pair.instance
            } else {
                default.instance
            };
            assert_eq!(
                context.get_return_type_of_signature(signature),
                Ok(expected)
            );
        }
        replay(
            &mut context,
            &parsed,
            &[full, prefix, inferred, defaults],
            &references,
        );
        assert_eq!(origin(&mut context, &parsed, "Pair"), pair);
        assert_eq!(origin(&mut context, &parsed, "Defaults"), default);
    }
}

#[test]
fn generic_constructor_overloads_keep_public_order_and_hide_the_implementation() {
    let parsed = parse_source_file(concat!(
        "export class Choice<T> {\n",
        "  value: T;\n",
        "  constructor(value: T);\n",
        "  constructor(value: T, marker: number);\n",
        "  constructor(value: T, marker?: number) { this.value = value; }\n",
        "}\n",
        "const first = new Choice<string>('left');\n",
        "const second = new Choice<number>(1, 2);\n",
        "const inferred = new Choice('right', 3);\n",
        "const selectedValue = second.value;\n",
    ));
    let libraries = LIBRARIES.map(|(_, _, source)| parse_source_file(source));
    for query_first in [false, true] {
        let mut context = context(&parsed, &libraries);
        check_source(&mut context, initializer(&parsed, "first"), query_first);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let choice = origin(&mut context, &parsed, "Choice");
        assert_eq!(choice.constructors.len(), 2);
        let implementation = choice.implementation.unwrap();
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let first = construction(&mut context, &parsed, "first", &choice, &[string], 0);
        let second = construction(&mut context, &parsed, "second", &choice, &[number], 1);
        let inferred = construction(&mut context, &parsed, "inferred", &choice, &[string], 1);
        assert_eq!(first.instance, inferred.instance);
        assert_ne!(first.signature, inferred.signature);
        assert_ne!(second.instance, first.instance);
        assert!(![first.signature, second.signature, inferred.signature].contains(&implementation));
        assert_eq!(
            context
                .store()
                .signature(choice.constructors[0])
                .unwrap()
                .min_argument_count(),
            1
        );
        assert_eq!(
            context
                .store()
                .signature(choice.constructors[1])
                .unwrap()
                .min_argument_count(),
            2
        );
        assert_eq!(
            context
                .store()
                .signature(implementation)
                .unwrap()
                .min_argument_count(),
            1
        );
        assert_field_read(
            &mut context,
            &parsed,
            "selectedValue",
            &choice,
            second.instance,
            number,
        );
        for &signature in choice
            .constructors
            .iter()
            .chain(choice.implementation.iter())
        {
            assert_eq!(
                context.get_return_type_of_signature(signature),
                Ok(choice.instance)
            );
        }
        replay(&mut context, &parsed, &[first, second, inferred], &[]);
        assert_eq!(origin(&mut context, &parsed, "Choice"), choice);
    }
}

fn assert_diagnostic(
    diagnostic: &CanonicalCheckerDiagnostic,
    code: u32,
    node: NodeRef,
    text: &str,
) {
    assert_eq!(diagnostic.diagnostic.code(), code);
    assert_eq!(diagnostic.node, Some(node));
    assert_eq!(diagnostic.diagnostic.render().unwrap(), text);
    assert!(diagnostic.diagnostic.details.is_empty());
}

#[test]
#[allow(clippy::too_many_lines)] // The complete error source keeps type and value diagnostics at different written nodes.
fn generic_construction_keeps_constraint_argument_and_arity_diagnostics() {
    let parsed = parse_source_file(concat!(
        "export class Bound<T extends string> { constructor(value: T) {} }\n",
        "class Pair<T, U = T> { constructor(first: T, second: U) {} }\n",
        "const constraint = new Bound<number>(1);\n",
        "const inferred = new Bound(1);\n",
        "const argument = new Bound<string>(1);\n",
        "const missing = new Bound<string>();\n",
        "const extra = new Bound<string>('ok', 2);\n",
        "const types = new Bound<string, number>('ok');\n",
        "const prefix = new Pair<string>('left', 1);\n",
    ));
    let libraries = LIBRARIES.map(|(_, _, source)| parse_source_file(source));
    for query_first in [false, true] {
        let mut context = context(&parsed, &libraries);
        check_source(
            &mut context,
            initializer(&parsed, "constraint"),
            query_first,
        );
        let constructions = [
            "constraint",
            "inferred",
            "argument",
            "missing",
            "extra",
            "types",
            "prefix",
        ]
        .map(|name| initializer(&parsed, name));
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 7, "{diagnostics:?}");
        let (_, _, written_constraint) = new_parts(&parsed, constructions[0]);
        assert_diagnostic(
            &diagnostics[0],
            2344,
            written_constraint[0],
            "Type 'number' does not satisfy the constraint 'string'.",
        );
        for index in [1, 2] {
            let (_, arguments, _) = new_parts(&parsed, constructions[index]);
            assert_diagnostic(
                &diagnostics[index],
                2345,
                arguments[0],
                "Argument of type 'number' is not assignable to parameter of type 'string'.",
            );
        }
        assert_diagnostic(
            &diagnostics[3],
            2554,
            constructions[3],
            "Expected 1 arguments, but got 0.",
        );
        let class = named(&parsed, SyntaxKind::ClassDeclaration, "Bound");
        let declarations = constructor_declarations(&parsed, class);
        let [constructor] = declarations.as_slice() else {
            unreachable!()
        };
        let NodeData::ConstructorDeclaration(data) =
            &parsed.arena.get(constructor.node).unwrap().data
        else {
            unreachable!()
        };
        let parameter = node(&parsed, data.parameters.nodes[0]);
        let [note] = diagnostics[3].related_information.as_slice() else {
            panic!("the missing value must retain its parameter note")
        };
        assert_eq!(note.node, Some(parameter));
        assert_eq!(note.diagnostic.code(), 6210);
        assert_eq!(
            note.diagnostic.render().unwrap(),
            "An argument for 'value' was not provided."
        );
        assert_diagnostic(
            &diagnostics[4],
            2554,
            constructions[4],
            "Expected 1 arguments, but got 2.",
        );
        let (_, extra, _) = new_parts(&parsed, constructions[4]);
        assert_eq!(
            diagnostics[4].range_override.unwrap().range(),
            parsed.arena.get(extra[1].node).unwrap().range
        );
        assert_diagnostic(
            &diagnostics[5],
            2558,
            constructions[5],
            "Expected 1 type arguments, but got 2.",
        );
        let (_, _, written) = new_parts(&parsed, constructions[5]);
        let range = diagnostics[5].range_override.unwrap().range();
        assert_eq!(
            range.start,
            parsed.arena.get(written[0].node).unwrap().range.start
        );
        assert_eq!(
            range.end,
            parsed.arena.get(written[1].node).unwrap().range.end
        );
        let (_, prefix_arguments, _) = new_parts(&parsed, constructions[6]);
        assert_diagnostic(
            &diagnostics[6],
            2345,
            prefix_arguments[1],
            "Argument of type 'number' is not assignable to parameter of type 'string'.",
        );
        for (index, diagnostic) in diagnostics.iter().enumerate() {
            if index != 3 {
                assert!(diagnostic.related_information.is_empty());
            }
            if ![4, 5].contains(&index) {
                assert_eq!(diagnostic.range_override, None);
            }
        }
        let locations = constructions.map(|node| {
            let type_ = context
                .store()
                .type_node_links(node)
                .unwrap()
                .resolved_type
                .unwrap();
            assert_eq!(context.get_type_at_location(node), Ok(type_));
            (node, type_, signature(&context, node))
        });
        let pair = origin(&mut context, &parsed, "Pair");
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        // Go's failed-overload recovery appends the original default T without remapping it.
        assert_reference(
            &context,
            locations[6].1,
            pair.instance,
            &[string, pair.formals[0]],
        );
        let recovered = context.store().signature(locations[6].2).unwrap();
        assert_eq!(recovered.target(), Some(pair.constructors[0]));
        let mapper = recovered.mapper().unwrap();
        assert_eq!(
            context.store().map_type(mapper, pair.formals[0]),
            Some(string)
        );
        assert_eq!(
            context.store().map_type(mapper, pair.formals[1]),
            Some(pair.formals[0])
        );
        assert_eq!(
            context.get_return_type_of_signature(locations[6].2),
            Ok(locations[6].1)
        );
        let checked = context
            .store()
            .signatures()
            .filter_map(|(signature, record)| {
                if record.target() != Some(pair.constructors[0]) {
                    return None;
                }
                let mapper = record.mapper()?;
                pair.formals
                    .iter()
                    .all(|&formal| context.store().map_type(mapper, formal) == Some(string))
                    .then_some((signature, mapper))
            })
            .collect::<Vec<_>>();
        let [(checked, checked_mapper)] = checked.as_slice() else {
            panic!("the failed prefix must retain exactly its checked string/string candidate")
        };
        assert_ne!(*checked, locations[6].2);
        let checked = context.store().signature(*checked).unwrap();
        assert_eq!(checked.flags(), SignatureFlags::CONSTRUCT);
        assert_eq!(checked.resolved_return_type(), None);
        let original = context.store().signature(pair.constructors[0]).unwrap();
        assert_eq!(checked.parameters().len(), original.parameters().len());
        for (&parameter, &source) in checked.parameters().iter().zip(original.parameters()) {
            let links = context.store().value_symbol_links(parameter).unwrap();
            assert_eq!(links.target, Some(source));
            assert_eq!(links.mapper, Some(*checked_mapper));
            assert_eq!(links.resolved_type, Some(string));
        }
        let warm = publication(&context, &parsed);
        for _ in 0..2 {
            context.check_source_file(FILE).unwrap();
            context.recheck_source_file(FILE).unwrap();
            for &(node, type_, selected) in &locations {
                assert_eq!(context.get_type_at_location(node), Ok(type_));
                assert_eq!(signature(&context, node), selected);
            }
            assert_eq!(publication(&context, &parsed), warm);
        }
    }
}

fn returned_new(parsed: &ParseResult, method: NodeRef) -> NodeRef {
    let NodeData::MethodDeclaration(data) = &parsed.arena.get(method.node).unwrap().data else {
        unreachable!()
    };
    let NodeData::Block(body) = &parsed.arena.get(data.body.unwrap()).unwrap().data else {
        unreachable!()
    };
    let [statement] = body.statements.nodes.as_slice() else {
        panic!("the method must retain its single direct return")
    };
    let NodeData::ReturnStatement(statement) = &parsed.arena.get(*statement).unwrap().data else {
        unreachable!()
    };
    let returned = node(parsed, statement.expression.unwrap());
    assert_eq!(
        parsed.arena.get(returned.node).unwrap().kind,
        SyntaxKind::NewExpression
    );
    returned
}

fn assert_incomplete_self_construction(libraries: &[ParseResult; 3]) {
    let parsed = parse_source_file(concat!(
        "export class Self<T> {\n",
        "  private constructor(value: T) {}\n",
        "  make(value: T): Self<T> { return new Self<T>(value); }\n",
        "}\n",
    ));
    let mut context = context(&parsed, libraries);
    let class = named(&parsed, SyntaxKind::ClassDeclaration, "Self");
    let construction = returned_new(&parsed, member(&parsed, class, "make"));
    let (callee, _, _) = new_parts(&parsed, construction);
    let NodeData::Identifier(name) = &parsed.arena.get(callee.node).unwrap().data else {
        unreachable!()
    };
    assert_eq!(name.text, "Self");
    let expected = SourceCheckError::Unsupported(UnsupportedSourceSyntax::New(callee));
    // The enclosing class is not complete. This stops before private-access checking.
    assert_eq!(context.check_source_file(FILE), Err(expected));
    assert!(context.diagnostics().is_empty());
    assert!(context.store().type_node_links(construction).is_none());
    assert!(context.store().signature_links(construction).is_none());
    assert!(context.store().type_node_links(callee).is_none());
    assert!(context.store().symbol_node_links(callee).is_none());
    assert!(
        context
            .store()
            .source_file_links(context.source_file(FILE).unwrap())
            .is_none_or(|links| !links.type_checked)
    );
    let stopped = publication(&context, &parsed);
    for _ in 0..2 {
        assert_eq!(context.check_source_file(FILE), Err(expected));
        assert_eq!(context.recheck_source_file(FILE), Err(expected));
        assert_eq!(publication(&context, &parsed), stopped);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // The same complete source separates outside errors from the real derived-class access scope.
fn generic_constructor_access_keeps_error_signatures_and_protected_scope() {
    let parsed = parse_source_file(concat!(
        "export class Secret<T> { private constructor(value: T) {} }\n",
        "export class ProtectedBase<T> {\n",
        "  value: T;\n",
        "  protected constructor(value: T) { this.value = value; }\n",
        "}\n",
        "class Child extends ProtectedBase<string> {\n",
        "  constructor() { super('child'); }\n",
        "  make(): ProtectedBase<string> { return new ProtectedBase<string>('made'); }\n",
        "}\n",
        "export abstract class AbstractBox<T> { constructor(value: T) {} }\n",
        "const hidden = new Secret<string>('outside');\n",
        "const protectedValue = new ProtectedBase<string>('outside');\n",
        "const abstractValue = new AbstractBox<string>('outside');\n",
        "declare const child: Child;\n",
        "const made = child.make();\n",
        "const madeValue = made.value;\n",
    ));
    let libraries = LIBRARIES.map(|(_, _, source)| parse_source_file(source));
    for query_first in [false, true] {
        let mut context = context(&parsed, &libraries);
        check_source(&mut context, initializer(&parsed, "hidden"), query_first);
        let secret = origin(&mut context, &parsed, "Secret");
        let protected = origin(&mut context, &parsed, "ProtectedBase");
        let abstract_class = origin(&mut context, &parsed, "AbstractBox");
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 3, "{diagnostics:?}");
        let errors = [
            (
                "hidden",
                &secret,
                2673,
                "Constructor of class 'Secret<T>' is private and only accessible within the class declaration.",
            ),
            (
                "protectedValue",
                &protected,
                2674,
                "Constructor of class 'ProtectedBase<T>' is protected and only accessible within the class declaration.",
            ),
            (
                "abstractValue",
                &abstract_class,
                2511,
                "Cannot create an instance of an abstract class.",
            ),
        ];
        let error_signature = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .unknown_signature;
        let error_type = context.store().intrinsic_bootstrap().unwrap().error_type;
        for (index, (name, origin, code, text)) in errors.iter().enumerate() {
            let new = initializer(&parsed, name);
            let (callee, _, _) = new_parts(&parsed, new);
            assert_diagnostic(&diagnostics[index], *code, new, text);
            assert_eq!(diagnostics[index].range_override, None);
            assert!(diagnostics[index].related_information.is_empty());
            assert_eq!(signature(&context, new), error_signature);
            assert_eq!(
                context.store().type_node_links(new).unwrap().resolved_type,
                Some(error_type)
            );
            assert_eq!(
                context
                    .store()
                    .type_node_links(callee)
                    .unwrap()
                    .resolved_type,
                Some(origin.value)
            );
            assert_eq!(
                context.store().symbol_node_links(callee),
                Some(&SymbolNodeLinks {
                    resolved_symbol: Some(origin.local)
                })
            );
        }
        assert_eq!(
            context
                .store()
                .signature(error_signature)
                .unwrap()
                .resolved_return_type(),
            Some(error_type)
        );
        assert_eq!(
            context.get_return_type_of_signature(error_signature),
            Ok(error_type)
        );
        for origin in [&secret, &abstract_class] {
            assert!(context.store().signatures().all(|(_, record)| {
                record
                    .target()
                    .is_none_or(|target| !origin.constructors.contains(&target))
            }));
            assert!(context.store().types().all(|(_, record)| {
                !matches!(record.data(), TypeData::TypeReference(reference)
                    if reference.object.target == Some(origin.instance))
            }));
        }
        let child = named(&parsed, SyntaxKind::ClassDeclaration, "Child");
        let make = member(&parsed, child, "make");
        let allowed = returned_new(&parsed, make);
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let allowed = construction_at(&mut context, &parsed, allowed, &protected, &[string], 0);
        assert_ne!(allowed.signature, error_signature);
        assert_eq!(
            context.get_return_type_of_signature(signature(&context, make)),
            Ok(allowed.instance)
        );
        assert_eq!(
            context.get_type_at_location(initializer(&parsed, "made")),
            Ok(allowed.instance)
        );
        assert_field_read(
            &mut context,
            &parsed,
            "madeValue",
            &protected,
            allowed.instance,
            string,
        );
        for (name, _, _, _) in &errors {
            assert_eq!(
                context.get_type_at_location(initializer(&parsed, name)),
                Ok(error_type)
            );
        }
        let warm = publication(&context, &parsed);
        replay(&mut context, &parsed, &[allowed], &[]);
        for (name, _, _, _) in &errors {
            let new = initializer(&parsed, name);
            assert_eq!(context.get_type_at_location(new), Ok(error_type));
            assert_eq!(signature(&context, new), error_signature);
        }
        assert_eq!(
            context.get_return_type_of_signature(error_signature),
            Ok(error_type)
        );
        assert_eq!(publication(&context, &parsed), warm);
    }
    assert_incomplete_self_construction(&libraries);
}
