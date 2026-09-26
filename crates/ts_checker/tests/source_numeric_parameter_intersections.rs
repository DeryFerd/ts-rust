use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalModuleResolutionEntry,
    CanonicalModuleResolutionManifestInput, CanonicalModuleResolutionMode,
    CanonicalResolvedModuleInput, IntrinsicBootstrapOptions, SourceFileLinks, SymbolNodeLinks,
    TypeAliasId, TypeAliasLinks, TypeData, TypeId, TypeNodeLinks,
    type_records::{
        ConditionalTypeData, IntersectionTypeData, LiteralTypeData, LiteralValue, TypeCacheState,
        TypeParameterData,
    },
    types::{ObjectFlags, TypeFlags},
};
use ts_jsnum::Number;
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(46_500);
const PROVIDER: FileId = FileId::new(46_501);
const LOCAL_TEXT: &str = concat!(
    "export type Cut<T> = 1 & T;\n",
    "export type Shift<U> = (7 & (U));\n",
    "export type Rebound<P> = Cut<P>;\n",
    "export type AnyValue = Cut<any>;\n",
    "export type UnknownValue = Cut<unknown>;\n",
    "export type NeverValue = Cut<never>;\n",
    "export type NumberValue = Cut<number>;\n",
    "export type StringValue = Cut<string>;\n",
    "export type SameValue = Cut<1>;\n",
    "export type DistinctValue = Cut<2>;\n",
    "export type ShiftUnknown = Shift<unknown>;\n",
    "export type ShiftSame = Shift<7>;\n",
    "export type ShiftDifferent = Shift<1>;\n",
);
const PROVIDER_TEXT: &str = concat!(
    "export type IsAny<T> = 0 extends 1 & T ? true : false;\n",
    "export type Detect<Value> = 0 extends 1 & Value ? true : false;\n",
);
const CONSUMER_TEXT: &str = concat!(
    "import type { IsAny, Detect as Neutral } from './provider';\n",
    "export type Pending<P> = IsAny<P> extends true ? P : never;\n",
    "export type Renamed<Q> = Neutral<Q> extends true ? Q : never;\n",
    "export type AnyResult = IsAny<any>;\n",
    "export type UnknownResult = IsAny<unknown>;\n",
    "export type NeverResult = IsAny<never>;\n",
    "export type NumberResult = IsAny<number>;\n",
    "export type StringResult = IsAny<string>;\n",
    "export type SameResult = IsAny<1>;\n",
    "export type DistinctResult = IsAny<2>;\n",
    "export type NeutralAny = Neutral<any>;\n",
    "export type NeutralUnknown = Neutral<unknown>;\n",
);

#[derive(Clone, Copy)]
struct Alias {
    declaration: NodeRef,
    body: NodeRef,
    parameter: Option<NodeRef>,
}

fn context<'arena>(
    files: &[(FileId, &'arena ParseResult, &str)],
    resolutions: &[(NodeRef, FileId)],
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path) in files {
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
    for &(file, parsed, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|&(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new(resolutions.iter().map(
            |&(specifier, target)| {
                CanonicalModuleResolutionEntry::resolved(
                    specifier,
                    CanonicalResolvedModuleInput::new(
                        target,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                )
            },
        )),
    )
    .unwrap()
}

fn alias(parsed: &ParseResult, file: FileId, expected: &str) -> Alias {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            if name.text != expected {
                return None;
            }
            let node_ref = |node| NodeRef::new(parsed.arena.id(), file, node);
            Some(Alias {
                declaration: node_ref(node),
                body: node_ref(alias.type_),
                parameter: alias.type_parameters.as_ref().map(|parameters| {
                    let [parameter] = parameters.nodes.as_slice() else {
                        panic!("the generic alias has one source parameter");
                    };
                    node_ref(*parameter)
                }),
            })
        })
        .unwrap_or_else(|| panic!("the source declares {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    context
        .file(node.file)
        .unwrap()
        .1
        .symbol(node)
        .and_then(|symbol| context.store().get_merged_symbol(symbol))
        .unwrap()
}

fn query_alias(context: &mut CanonicalCheckerContext<'_>, alias: Alias) -> TypeId {
    let owner = symbol(context, alias.declaration);
    let type_ = context.get_declared_type_of_symbol(owner).unwrap();
    assert_eq!(context.get_type_from_type_node(alias.body), Ok(type_));
    assert_eq!(
        context
            .store()
            .type_alias_links(owner)
            .unwrap()
            .declared_type,
        Some(type_),
    );
    assert_eq!(
        context
            .store()
            .type_node_links(alias.body)
            .unwrap()
            .resolved_type,
        Some(type_),
    );
    type_
}

fn parameter(context: &CanonicalCheckerContext<'_>, alias: Alias) -> TypeId {
    let declaration = alias.parameter.unwrap();
    let owner = symbol(context, declaration);
    assert_eq!(
        context.store().symbol(owner).unwrap().declarations(),
        Some([declaration].as_slice()),
    );
    let type_ = context
        .store()
        .declared_type_links(owner)
        .unwrap()
        .declared_type
        .unwrap();
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::TypeParameter(parameter) = record.data() else {
        panic!("the binder parameter must keep its own type");
    };
    assert_eq!(parameter.target, None);
    assert_eq!(parameter.mapper, None);
    assert!(!parameter.is_this_type);
    assert_eq!(
        context
            .store()
            .type_alias_links(symbol(context, alias.declaration))
            .unwrap()
            .type_parameters
            .as_deref(),
        Some([type_].as_slice()),
    );
    type_
}

fn assert_alias(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    declaration: NodeRef,
    argument: TypeId,
) {
    let record = context.store().type_payload(type_).unwrap();
    let alias = context.store().type_alias(record.alias().unwrap()).unwrap();
    assert_eq!(alias.symbol(), Some(symbol(context, declaration)));
    assert_eq!(alias.type_arguments(), Some([argument].as_slice()));
}

fn unparenthesized(parsed: &ParseResult, mut node: NodeRef) -> NodeRef {
    while let NodeData::ParenthesizedTypeNode(parenthesized) =
        &parsed.arena.get(node.node).unwrap().data
    {
        node = NodeRef::new(node.arena, node.file, parenthesized.type_);
    }
    node
}

fn intersection_nodes(parsed: &ParseResult, node: NodeRef) -> [NodeRef; 2] {
    let node = unparenthesized(parsed, node);
    let NodeData::IntersectionTypeNode(intersection) = &parsed.arena.get(node.node).unwrap().data
    else {
        panic!("the source has a numeric literal and a type parameter");
    };
    let [left, right] = intersection.types.nodes.as_slice() else {
        panic!("the intersection has two written operands");
    };
    [*left, *right].map(|child| NodeRef::new(node.arena, node.file, child))
}

fn conditional_nodes(parsed: &ParseResult, node: NodeRef) -> [NodeRef; 4] {
    let NodeData::ConditionalTypeNode(conditional) = &parsed.arena.get(node.node).unwrap().data
    else {
        panic!("the source has a conditional type");
    };
    [
        conditional.check_type,
        conditional.extends_type,
        conditional.true_type,
        conditional.false_type,
    ]
    .map(|child| NodeRef::new(node.arena, node.file, child))
}

fn reference_argument(parsed: &ParseResult, node: NodeRef) -> NodeRef {
    let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(node.node).unwrap().data else {
        panic!("the source applies a generic alias");
    };
    let [argument] = reference.type_arguments.as_ref().unwrap().nodes.as_slice() else {
        panic!("the reference has one source argument");
    };
    NodeRef::new(node.arena, node.file, *argument)
}

fn assert_intersection(
    context: &CanonicalCheckerContext<'_>,
    type_: TypeId,
    number: TypeId,
    parameter: TypeId,
) {
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.flags(), TypeFlags::INTERSECTION);
    let TypeData::Intersection(intersection) = record.data() else {
        panic!("the generic intersection must stay deferred");
    };
    assert_eq!(intersection.intersection.types, [number, parameter]);
    assert!(intersection.intersection.structured.members.is_none());
    assert!(intersection.intersection.structured.properties.is_none());
}

fn regular_number(context: &CanonicalCheckerContext<'_>, value: f64) -> TypeId {
    let store = context.store();
    let number = Number::new(value);
    let regular = store
        .intrinsic_bootstrap()
        .unwrap()
        .cached_number_literal_type(number)
        .unwrap();
    let record = store.type_payload(regular).unwrap();
    let TypeData::Literal(literal) = record.data() else {
        panic!("the number must use a canonical literal pair");
    };
    let fresh = literal.fresh_type.unwrap();
    assert_ne!(fresh, regular);
    assert_eq!(literal.value, LiteralValue::Number(number));
    assert_eq!(literal.regular_type, regular);
    for type_ in [regular, fresh] {
        let record = store.type_payload(type_).unwrap();
        assert_eq!(record.flags(), TypeFlags::NUMBER_LITERAL);
        assert_eq!(record.object_flags(), ObjectFlags::NONE);
        assert_eq!(record.symbol(), None);
        assert_eq!(record.alias(), None);
        let TypeData::Literal(pair) = record.data() else {
            panic!("both halves must retain the numeric literal");
        };
        assert_eq!(pair.value, LiteralValue::Number(number));
        assert_eq!(pair.regular_type, regular);
        assert_eq!(pair.fresh_type, Some(fresh));
    }
    regular
}

fn assert_unchecked(context: &CanonicalCheckerContext<'_>, file: FileId) {
    assert!(
        context
            .store()
            .source_file_links(context.source_file(file).unwrap())
            .is_none_or(|links| !links.type_checked),
    );
}

#[derive(Debug, PartialEq)]
struct TypeAliasState {
    type_: TypeId,
    alias: TypeAliasId,
    owner: Option<SemanticSymbolId>,
    arguments: Option<Vec<TypeId>>,
}

#[derive(Debug, PartialEq)]
struct Snapshot {
    counts: [usize; 8],
    nodes: Vec<(NodeRef, Option<TypeNodeLinks>, Option<SymbolNodeLinks>)>,
    aliases: Vec<(
        SemanticSymbolId,
        Option<TypeAliasLinks>,
        Option<AliasSymbolLinks>,
    )>,
    sources: Vec<Option<SourceFileLinks>>,
    intersections: Vec<(TypeId, IntersectionTypeData)>,
    conditionals: Vec<(TypeId, ConditionalTypeData, TypeCacheState)>,
    literals: Vec<(TypeId, LiteralTypeData)>,
    parameters: Vec<(TypeId, TypeParameterData)>,
    type_aliases: Vec<TypeAliasState>,
    diagnostics: CanonicalCheckerDiagnostics,
}

#[allow(clippy::too_many_lines)] // Keep the query identities and cache state in one snapshot.
fn snapshot(context: &CanonicalCheckerContext<'_>) -> Snapshot {
    let store = context.store();
    Snapshot {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.conditional_root_len(),
            store.symbol_store().symbol_table_len(),
        ],
        nodes: context
            .file_order()
            .iter()
            .flat_map(|&file| {
                let arena = context.file(file).unwrap().0;
                arena.iter().map(move |(node, _)| {
                    let node = NodeRef::new(arena.id(), file, node);
                    (
                        node,
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                    )
                })
            })
            .collect(),
        aliases: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.type_alias_links(symbol).cloned(),
                    store.alias_symbol_links(symbol).cloned(),
                )
            })
            .collect(),
        sources: context
            .file_order()
            .iter()
            .map(|&file| {
                store
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned()
            })
            .collect(),
        intersections: store
            .types()
            .filter_map(|(type_, record)| {
                let TypeData::Intersection(data) = record.data() else {
                    return None;
                };
                Some((type_, data.clone()))
            })
            .collect(),
        conditionals: store
            .types()
            .filter_map(|(type_, record)| {
                let TypeData::Conditional(data) = record.data() else {
                    return None;
                };
                Some((
                    type_,
                    data.clone(),
                    store
                        .conditional_root(data.root)
                        .unwrap()
                        .instantiations()
                        .clone(),
                ))
            })
            .collect(),
        literals: store
            .types()
            .filter_map(|(type_, record)| {
                let TypeData::Literal(data) = record.data() else {
                    return None;
                };
                Some((type_, data.clone()))
            })
            .collect(),
        parameters: store
            .types()
            .filter_map(|(type_, record)| {
                let TypeData::TypeParameter(data) = record.data() else {
                    return None;
                };
                Some((type_, data.clone()))
            })
            .collect(),
        type_aliases: store
            .types()
            .filter_map(|(type_, record)| {
                let alias = record.alias()?;
                let identity = store.type_alias(alias).unwrap();
                Some(TypeAliasState {
                    type_,
                    alias,
                    owner: identity.symbol(),
                    arguments: identity.type_arguments().map(<[TypeId]>::to_vec),
                })
            })
            .collect(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    aliases: &[(Alias, TypeId)],
    nodes: &[(NodeRef, TypeId)],
) {
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let before = snapshot(context);
    let files = context.file_order().to_vec();
    for _ in 0..2 {
        for &(alias, expected) in aliases {
            assert_eq!(query_alias(context, alias), expected);
        }
        for &(node, expected) in nodes {
            assert_eq!(context.get_type_from_type_node(node), Ok(expected));
        }
        for &file in &files {
            context.check_source_file(file).unwrap();
            context.recheck_source_file(file).unwrap();
        }
        assert_eq!(snapshot(context), before);
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn numeric_parameter_intersections_keep_deferred_identity_and_reduce_real_arguments() {
    for query_first in [true, false] {
        let source = parse_source_file(LOCAL_TEXT);
        let mut context = context(&[(SOURCE, &source, "\"/project/numeric.ts\"")], &[]);
        let cut = alias(&source, SOURCE, "Cut");
        let shift = alias(&source, SOURCE, "Shift");
        let rebound = alias(&source, SOURCE, "Rebound");
        let first = if query_first {
            let type_ = context.get_type_from_type_node(rebound.body).unwrap();
            assert_unchecked(&context, SOURCE);
            Some(type_)
        } else {
            context.check_source_file(SOURCE).unwrap();
            None
        };
        let mut queried = [cut, shift, rebound]
            .map(|alias| (alias, query_alias(&mut context, alias)))
            .to_vec();
        if let Some(first) = first {
            assert_eq!(queried[2].1, first);
        }
        let one = regular_number(&context, 1.0);
        let seven = regular_number(&context, 7.0);
        assert_ne!(one, seven);
        let cut_parameter = parameter(&context, cut);
        let shift_parameter = parameter(&context, shift);
        let rebound_parameter = parameter(&context, rebound);
        assert_ne!(cut_parameter, shift_parameter);
        assert_ne!(cut_parameter, rebound_parameter);
        let mut nodes = Vec::new();
        for ((alias, type_), number) in queried.iter().copied().zip([one, seven, one]) {
            let parameter = parameter(&context, alias);
            assert_intersection(&context, type_, number, parameter);
            assert_alias(&context, type_, alias.declaration, parameter);
            assert!(
                context
                    .store()
                    .type_alias_links(symbol(&context, alias.declaration))
                    .unwrap()
                    .instantiations
                    .as_ref()
                    .unwrap()
                    .values()
                    .any(|cached| *cached == type_)
            );
            let operands = if alias.declaration == rebound.declaration {
                vec![(reference_argument(&source, alias.body), parameter)]
            } else {
                let [left, right] = intersection_nodes(&source, alias.body);
                vec![(left, number), (right, parameter)]
            };
            for (node, expected) in operands {
                assert_eq!(context.get_type_from_type_node(node), Ok(expected));
                nodes.push((node, expected));
            }
        }
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let any = bootstrap.any_type;
        let never = bootstrap.never_type;
        for (name, expected) in [
            ("AnyValue", any),
            ("UnknownValue", one),
            ("NeverValue", never),
            ("NumberValue", one),
            ("StringValue", never),
            ("SameValue", one),
            ("DistinctValue", never),
            ("ShiftUnknown", seven),
            ("ShiftSame", seven),
            ("ShiftDifferent", never),
        ] {
            let alias = alias(&source, SOURCE, name);
            assert_eq!(query_alias(&mut context, alias), expected, "{name}");
            queried.push((alias, expected));
        }
        let two = regular_number(&context, 2.0);
        assert_ne!(two, one);
        let written_two = reference_argument(&source, alias(&source, SOURCE, "DistinctValue").body);
        assert_eq!(context.get_type_from_type_node(written_two), Ok(two));
        nodes.push((written_two, two));
        if query_first {
            assert_unchecked(&context, SOURCE);
        }
        context.check_source_file(SOURCE).unwrap();
        assert_replay(&mut context, &queried, &nodes);
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn imported_numeric_conditionals_keep_provider_owners_and_special_type_results() {
    for query_first in [true, false] {
        let source = parse_source_file(CONSUMER_TEXT);
        let provider = parse_source_file(PROVIDER_TEXT);
        let specifier = source
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::ImportDeclaration(import) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(
                    source.arena.id(),
                    SOURCE,
                    import.module_specifier,
                ))
            })
            .unwrap();
        let mut files = [
            (SOURCE, &source, "\"/project/numeric.ts\""),
            (PROVIDER, &provider, "\"/project/provider.ts\""),
        ];
        if !query_first {
            files.reverse();
        }
        let mut context = context(&files, &[(specifier, PROVIDER)]);
        let pending = alias(&source, SOURCE, "Pending");
        let first = if query_first {
            let type_ = context.get_type_from_type_node(pending.body).unwrap();
            assert_unchecked(&context, SOURCE);
            assert_unchecked(&context, PROVIDER);
            Some(type_)
        } else {
            context.check_source_file(SOURCE).unwrap();
            None
        };
        let mut queried = Vec::new();
        let mut nodes = Vec::new();
        let mut roots = Vec::new();
        for (local_name, imported_name, provider_name) in [
            ("Pending", "IsAny", "IsAny"),
            ("Renamed", "Neutral", "Detect"),
        ] {
            let consumer = alias(&source, SOURCE, local_name);
            let consumer_type = query_alias(&mut context, consumer);
            let consumer_parameter = parameter(&context, consumer);
            assert_alias(
                &context,
                consumer_type,
                consumer.declaration,
                consumer_parameter,
            );
            if local_name == "Pending"
                && let Some(first) = first
            {
                assert_eq!(consumer_type, first);
            }
            let reference = conditional_nodes(&source, consumer.body)[0];
            let argument = reference_argument(&source, reference);
            assert_eq!(
                context.get_type_from_type_node(argument),
                Ok(consumer_parameter)
            );
            let instance_type = context.get_type_from_type_node(reference).unwrap();
            let provider_alias = alias(&provider, PROVIDER, provider_name);
            let declared = query_alias(&mut context, provider_alias);
            let provider_parameter = parameter(&context, provider_alias);
            assert_ne!(consumer_parameter, provider_parameter);
            let owner = symbol(&context, provider_alias.declaration);
            assert_alias(
                &context,
                declared,
                provider_alias.declaration,
                provider_parameter,
            );
            assert_alias(
                &context,
                instance_type,
                provider_alias.declaration,
                consumer_parameter,
            );
            let TypeData::Conditional(outer) =
                context.store().type_payload(consumer_type).unwrap().data()
            else {
                panic!("the consumer must retain its own conditional");
            };
            assert_eq!(outer.check_type, instance_type);
            let TypeData::Conditional(original) =
                context.store().type_payload(declared).unwrap().data()
            else {
                panic!("the provider must retain its original conditional");
            };
            let TypeData::Conditional(instance) =
                context.store().type_payload(instance_type).unwrap().data()
            else {
                panic!("the imported argument must stay deferred");
            };
            assert_eq!(instance.root, original.root);
            assert_eq!(original.mapper, None);
            assert_eq!(
                context
                    .store()
                    .map_type(instance.mapper.unwrap(), provider_parameter),
                Some(consumer_parameter)
            );
            let zero = regular_number(&context, 0.0);
            let one = regular_number(&context, 1.0);
            assert_ne!(zero, one);
            assert_eq!(original.check_type, zero);
            assert_eq!(instance.check_type, zero);
            assert_intersection(&context, original.extends_type, one, provider_parameter);
            assert_intersection(&context, instance.extends_type, one, consumer_parameter);
            let root = context.store().conditional_root(original.root).unwrap();
            assert_eq!(root.node(), provider_alias.body);
            assert_eq!(root.check_type(), zero);
            assert_eq!(root.extends_type(), original.extends_type);
            assert_eq!(
                root.outer_type_parameters(),
                Some([provider_parameter].as_slice())
            );
            assert!(!root.is_distributive());
            roots.push(root.id());
            let binding = source
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::ImportSpecifier(import) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &source.arena.get(import.name)?.data else {
                        return None;
                    };
                    (name.text == imported_name).then_some(NodeRef::new(
                        source.arena.id(),
                        SOURCE,
                        node,
                    ))
                })
                .unwrap();
            let imported = symbol(&context, binding);
            assert_ne!(imported, owner);
            let links = context.store().alias_symbol_links(imported).unwrap();
            assert_eq!(links.immediate_target, Some(owner));
            assert_eq!(links.alias_target, AliasTargetState::Resolved(owner));
            assert_eq!(links.type_only_declaration, Some(binding));
            assert!(context.store().value_symbol_links(imported).is_none());
            assert!(context.store().value_symbol_links(owner).is_none());
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(reference)
                    .unwrap()
                    .resolved_symbol,
                Some(owner)
            );
            let bound = context.file(PROVIDER).unwrap().1;
            let module = bound.symbol(bound.source_file()).unwrap();
            let exports = context.store().symbol(module).unwrap().exports().unwrap();
            assert_eq!(
                context
                    .store()
                    .symbol_table(exports)
                    .unwrap()
                    .get_source(provider_name),
                Some(owner)
            );
            assert_eq!(
                context.store().symbol(owner).unwrap().declarations(),
                Some([provider_alias.declaration].as_slice())
            );
            let [check, extends, _, _] = conditional_nodes(&provider, provider_alias.body);
            let [literal, parameter_reference] = intersection_nodes(&provider, extends);
            for (node, expected) in [
                (check, zero),
                (extends, original.extends_type),
                (literal, one),
                (parameter_reference, provider_parameter),
            ] {
                assert_eq!(context.get_type_from_type_node(node), Ok(expected));
                nodes.push((node, expected));
            }
            queried.extend([(consumer, consumer_type), (provider_alias, declared)]);
            nodes.extend([(reference, instance_type), (argument, consumer_parameter)]);
        }
        assert_ne!(roots[0], roots[1]);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let yes = bootstrap.regular_true_type;
        let no = bootstrap.regular_false_type;
        assert_ne!(yes, bootstrap.true_type);
        assert_ne!(no, bootstrap.false_type);
        for (name, expected) in [
            ("AnyResult", yes),
            ("UnknownResult", no),
            ("NeverResult", no),
            ("NumberResult", no),
            ("StringResult", no),
            ("SameResult", no),
            ("DistinctResult", no),
            ("NeutralAny", yes),
            ("NeutralUnknown", no),
        ] {
            let alias = alias(&source, SOURCE, name);
            assert_eq!(query_alias(&mut context, alias), expected, "{name}");
            queried.push((alias, expected));
        }
        if query_first {
            assert_unchecked(&context, SOURCE);
        }
        assert_unchecked(&context, PROVIDER);
        context.check_source_file(SOURCE).unwrap();
        context.check_source_file(PROVIDER).unwrap();
        assert_replay(&mut context, &queried, &nodes);
    }
}
