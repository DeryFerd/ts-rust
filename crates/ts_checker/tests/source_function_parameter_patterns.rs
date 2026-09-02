use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, IntrinsicBootstrapOptions,
    SignatureId, SignatureLinks, SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: FileId = FileId::new(20_350);
const PROVIDER: FileId = FileId::new(20_351);
const BOX: &str = "export interface Box<T, U = string> { value: T; label: U; }\n";

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn import_nodes(parsed: &ParseResult) -> (NodeRef, NodeRef) {
    let mut imports = parsed.arena.iter().filter_map(|(_, record)| {
        let NodeData::ImportDeclaration(import) = &record.data else {
            return None;
        };
        let NodeData::ImportClause(clause) =
            &parsed.arena.get(import.import_clause.unwrap()).unwrap().data
        else {
            panic!("expected the real import clause")
        };
        let NodeData::NamedImports(named) =
            &parsed.arena.get(clause.named_bindings.unwrap()).unwrap().data
        else {
            panic!("expected a named import")
        };
        let [binding] = named.elements.nodes.as_slice() else {
            panic!("expected the Box import")
        };
        Some((
            node(parsed, SOURCE, import.module_specifier),
            node(parsed, SOURCE, *binding),
        ))
    });
    let result = imports.next().unwrap();
    assert!(imports.next().is_none());
    result
}

fn context<'a>(
    source: &'a ParseResult,
    provider: &'a ParseResult,
) -> CanonicalCheckerContext<'a> {
    let files = [
        (SOURCE, source, "\"/project/source.ts\""),
        (PROVIDER, provider, "\"/project/box.ts\""),
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
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed, _)| (*file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            no_implicit_any: true,
            strict_function_types: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            import_nodes(source).0,
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

fn value_type(context: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap()
}

struct Leaf {
    element: NodeRef,
    name: NodeRef,
    property: NodeRef,
    owner: SemanticSymbolId,
}

struct Function {
    declaration: NodeRef,
    name: NodeRef,
    parameter: NodeRef,
    annotation: NodeRef,
    reference_name: NodeRef,
    owner: SemanticSymbolId,
    leaves: Vec<Leaf>,
    read: NodeRef,
}

fn function(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    expected_name: &str,
) -> Function {
    let (declaration, data) = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::FunctionDeclaration(data) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(data.name?).unwrap().data else {
                return None;
            };
            (name.text == expected_name).then_some((node(parsed, SOURCE, id), data))
        })
        .unwrap();
    let [parameter] = data.parameters.nodes.as_slice() else {
        panic!("expected one binding parameter")
    };
    let parameter = node(parsed, SOURCE, *parameter);
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    let annotation = node(parsed, SOURCE, parameter_data.type_.unwrap());
    let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(annotation.node).unwrap().data
    else {
        panic!("expected the written generic reference")
    };
    assert!(reference.type_arguments.is_some());
    let NodeData::BindingPattern(pattern) = &parsed.arena.get(parameter_data.name).unwrap().data
    else {
        panic!("expected the written object pattern")
    };
    let leaves = pattern
        .elements
        .nodes
        .iter()
        .map(|id| {
            let NodeData::BindingElement(element) = &parsed.arena.get(*id).unwrap().data else {
                unreachable!()
            };
            let element_node = node(parsed, SOURCE, *id);
            let name = node(parsed, SOURCE, element.name.unwrap());
            Leaf {
                element: element_node,
                name,
                property: element
                    .property_name
                    .map_or(name, |id| node(parsed, SOURCE, id)),
                owner: symbol(context, element_node),
            }
        })
        .collect();
    let bound = context.file(SOURCE).unwrap().1;
    let read = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            if record.kind != SyntaxKind::Identifier
                || parsed.arena.get(record.parent?)?.kind != SyntaxKind::ReturnStatement
            {
                return None;
            }
            let node = node(parsed, SOURCE, id);
            (bound.container(node) == Some(declaration)).then_some(node)
        })
        .unwrap();
    Function {
        declaration,
        name: node(parsed, SOURCE, data.name.unwrap()),
        parameter,
        annotation,
        reference_name: node(parsed, SOURCE, reference.type_name),
        owner: symbol(context, parameter),
        leaves,
        read,
    }
}

#[derive(Default)]
struct Queries {
    types: Vec<(NodeRef, TypeId)>,
    symbols: Vec<(NodeRef, SemanticSymbolId)>,
    returns: Vec<(SignatureId, TypeId)>,
}

impl Queries {
    fn check(&self, context: &mut CanonicalCheckerContext<'_>) {
        for &(node, expected) in &self.types {
            assert_eq!(context.get_type_at_location(node), Ok(expected));
        }
        for &(node, expected) in &self.symbols {
            assert_eq!(context.get_symbol_at_location(node), Ok(Some(expected)));
        }
        for &(signature, expected) in &self.returns {
            assert_eq!(
                context.get_return_type_of_signature(signature),
                Ok(expected)
            );
            assert_eq!(
                context
                    .store()
                    .signature(signature)
                    .unwrap()
                    .resolved_return_type(),
                Some(expected),
            );
        }
    }
}

fn check_function(
    context: &mut CanonicalCheckerContext<'_>,
    function: &Function,
    target: TypeId,
    arguments: &[TypeId],
    leaf_types: &[TypeId],
    queries: &mut Queries,
) -> TypeId {
    assert_eq!(function.leaves.len(), leaf_types.len());
    let parent = context.get_type_from_type_node(function.annotation).unwrap();
    assert_eq!(value_type(context, function.owner), parent);
    let TypeData::TypeReference(reference) = context.store().type_payload(parent).unwrap().data()
    else {
        panic!("the parent must keep its canonical generic interface reference")
    };
    assert_eq!(reference.object.target, Some(target));
    assert_eq!(reference.resolved_type_arguments.as_deref(), Some(arguments));
    queries
        .types
        .extend([(function.parameter, parent), (function.annotation, parent)]);
    queries.symbols.push((function.parameter, function.owner));
    for (leaf, &expected) in function.leaves.iter().zip(leaf_types) {
        assert_ne!(leaf.owner, function.owner);
        let record = context.store().symbol(leaf.owner).unwrap();
        assert_eq!(record.declarations(), Some(&[leaf.element][..]));
        assert_eq!(record.value_declaration(), Some(leaf.element));
        assert_eq!(value_type(context, leaf.owner), expected);
        queries
            .types
            .extend([(leaf.element, expected), (leaf.name, expected)]);
        queries
            .symbols
            .extend([(leaf.element, leaf.owner), (leaf.name, leaf.owner)]);
    }
    let returned = leaf_types[0];
    queries.types.push((function.read, returned));
    queries.symbols.push((function.read, function.leaves[0].owner));
    let callable = context.get_type_at_location(function.name).unwrap();
    queries.types.push((function.name, callable));
    let signature = context
        .store()
        .signature_links(function.declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.parameters(), &[function.owner]);
    assert_eq!(record.min_argument_count(), 1);
    queries.returns.push((signature, returned));
    parent
}

fn imported_target(
    context: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
    provider: &ParseResult,
) -> (TypeId, SemanticSymbolId) {
    let declaration = provider
        .arena
        .iter()
        .find_map(|(id, record)| {
            (record.kind == SyntaxKind::InterfaceDeclaration)
                .then_some(node(provider, PROVIDER, id))
        })
        .unwrap();
    let owner = symbol(context, declaration);
    let imported = symbol(context, import_nodes(source).1);
    assert_ne!(imported, owner);
    assert_eq!(
        context
            .store()
            .alias_symbol_links(imported)
            .unwrap()
            .alias_target,
        AliasTargetState::Resolved(owner),
    );
    let target = context
        .store()
        .declared_type_links(owner)
        .unwrap()
        .declared_type
        .unwrap();
    assert_eq!(
        context.store().type_payload(target).unwrap().symbol(),
        Some(owner)
    );
    (target, imported)
}

fn calls(parsed: &ParseResult) -> Vec<NodeRef> {
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == SyntaxKind::CallExpression)
                .then_some((record.range.start, node(parsed, SOURCE, id)))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|(start, _)| *start);
    calls.into_iter().map(|(_, node)| node).collect()
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    type_: Option<TypeNodeLinks>,
    symbol: Option<SymbolNodeLinks>,
    signature: Option<SignatureLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Snapshot {
    counts: [usize; 7],
    nodes: Vec<NodeState>,
    values: Vec<(SemanticSymbolId, Option<TypeId>)>,
    files: Vec<Option<SourceFileLinks>>,
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    source: &ParseResult,
    provider: &ParseResult,
) -> Snapshot {
    let store = context.store();
    let mut snapshot = Snapshot {
        counts: [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        nodes: Vec::new(),
        values: Vec::new(),
        files: Vec::new(),
    };
    for (file, parsed) in [(SOURCE, source), (PROVIDER, provider)] {
        let bound = context.file(file).unwrap().1;
        for (id, _) in parsed.arena.iter() {
            let node = node(parsed, file, id);
            snapshot.nodes.push(NodeState {
                node,
                type_: store.type_node_links(node).cloned(),
                symbol: store.symbol_node_links(node).cloned(),
                signature: store.signature_links(node).cloned(),
            });
            if let Some(raw) = bound.symbol(node) {
                let owner = store.get_merged_symbol(raw).unwrap();
                snapshot.values.push((
                    owner,
                    store
                        .value_symbol_links(owner)
                        .and_then(|links| links.resolved_type),
                ));
            }
        }
        snapshot.files.push(
            store
                .source_file_links(context.source_file(file).unwrap())
                .cloned(),
        );
    }
    snapshot
}

fn replay(
    context: &mut CanonicalCheckerContext<'_>,
    source: &ParseResult,
    provider: &ParseResult,
    queries: &Queries,
) {
    queries.check(context);
    let before = snapshot(context, source, provider);
    assert!(before.files[0].as_ref().unwrap().type_checked);
    let diagnostics = context.diagnostics().as_slice().to_vec();
    for recheck in [false, true, true] {
        if recheck {
            context.recheck_source_file(SOURCE).unwrap();
        } else {
            context.check_source_file(SOURCE).unwrap();
        }
        queries.check(context);
        assert_eq!(context.diagnostics().as_slice(), diagnostics);
        assert_eq!(snapshot(context, source, provider), before);
    }
}

fn text<'a>(source: &'a str, parsed: &ParseResult, node: NodeRef) -> &'a str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

#[test]
fn imported_generic_object_parameters_keep_defaults_types_and_binding_owners() {
    let source = concat!(
        "import type { Box } from './box';\n",
        "export function readNumber({ value, label }: Box<number>): number { return value; }\n",
        "export function readText({ value: text, label: count }: Box<string, number>): string { return text; }\n",
        "const numberResult: number = readNumber({ value: 1, label: 'n' });\n",
        "const stringResult: string = readText({ value: 's', label: 2 });\n",
    );
    for query_first in [false, true] {
        let parsed = parse_source_file(source);
        let provider = parse_source_file(BOX);
        let mut context = context(&parsed, &provider);
        let number_fn = function(&context, &parsed, "readNumber");
        let text_fn = function(&context, &parsed, "readText");
        for function in [&number_fn, &text_fn] {
            assert!(context.store().type_node_links(function.annotation).is_none());
            for leaf in &function.leaves {
                assert!(context.store().value_symbol_links(leaf.owner).is_none());
            }
        }
        // The importer starts cold, including when a public query starts the check.
        if query_first {
            context.get_type_at_location(number_fn.name).unwrap();
        }
        context.check_source_file(SOURCE).unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let (target, imported) = imported_target(&context, &parsed, &provider);
        let mut queries = Queries::default();
        let number_parent = check_function(
            &mut context,
            &number_fn,
            target,
            &[number, string],
            &[number, string],
            &mut queries,
        );
        let text_parent = check_function(
            &mut context,
            &text_fn,
            target,
            &[string, number],
            &[string, number],
            &mut queries,
        );
        assert_ne!(number_parent, text_parent);
        assert_ne!(number_fn.owner, text_fn.owner);
        for (left, right) in number_fn.leaves.iter().zip(&text_fn.leaves) {
            assert_ne!(left.owner, right.owner);
        }
        for function in [&number_fn, &text_fn] {
            queries.symbols.push((function.reference_name, imported));
        }
        let calls = calls(&parsed);
        assert_eq!(calls.len(), 2);
        queries.types.extend([(calls[0], number), (calls[1], string)]);
        assert!(context.diagnostics().is_empty());
        replay(&mut context, &parsed, &provider, &queries);
    }
}

#[test]
fn generic_object_parameter_calls_keep_native_argument_and_arity_errors() {
    let source = concat!(
        "import type { Box } from './box';\n",
        "function read({ value, label }: Box<number>): number { return value; }\n",
        "const accepted: number = read({ value: 1, label: 'ok' });\n",
        "const omitted: number = read();\n",
        "const invalid: number = read('wrong');\n",
    );
    let parsed = parse_source_file(source);
    let provider = parse_source_file(BOX);
    let mut context = context(&parsed, &provider);
    let function = function(&context, &parsed, "read");
    context.check_source_file(SOURCE).unwrap();
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let (target, _) = imported_target(&context, &parsed, &provider);
    let mut queries = Queries::default();
    check_function(
        &mut context,
        &function,
        target,
        &[number, string],
        &[number, string],
        &mut queries,
    );
    let [missing, invalid] = context.diagnostics().as_slice() else {
        panic!("expected only the omitted and invalid argument errors")
    };
    assert_eq!(missing.diagnostic.code(), 2554);
    assert_eq!(
        missing.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 0."
    );
    assert_eq!(text(source, &parsed, missing.node.unwrap()), "read");
    assert_eq!(missing.range_override, None);
    let [related] = missing.related_information.as_slice() else {
        panic!("the omitted argument must refer to its real binding parameter")
    };
    assert_eq!(related.node, Some(function.parameter));
    assert_eq!(related.diagnostic.code(), 6211);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument matching this binding pattern was not provided.",
    );
    assert_eq!(invalid.diagnostic.code(), 2345);
    assert_eq!(text(source, &parsed, invalid.node.unwrap()), "'wrong'");
    assert_eq!(invalid.diagnostic.arguments, ["string", "Box<number, string>"]);
    assert_eq!(invalid.range_override, None);
    assert!(invalid.related_information.is_empty());
    let calls = calls(&parsed);
    assert_eq!(calls.len(), 3);
    queries.types.extend(calls.into_iter().map(|call| (call, number)));
    replay(&mut context, &parsed, &provider, &queries);
}

#[test]
fn missing_generic_object_binding_property_keeps_its_native_error_location() {
    let source = concat!(
        "import type { Box } from './box';\n",
        "function read({ value, missing: renamed }: Box<number>): number { return value; }\n",
    );
    let parsed = parse_source_file(source);
    let provider = parse_source_file(BOX);
    let mut context = context(&parsed, &provider);
    let function = function(&context, &parsed, "read");
    context.check_source_file(SOURCE).unwrap();
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one missing binding property error")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2339);
    assert_eq!(diagnostic.node, Some(function.leaves[1].property));
    assert_eq!(text(source, &parsed, diagnostic.node.unwrap()), "missing");
    assert_eq!(diagnostic.diagnostic.arguments, ["missing", "Box<number, string>"]);
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let recovery = value_type(&context, function.leaves[1].owner);
    let (target, _) = imported_target(&context, &parsed, &provider);
    let mut queries = Queries::default();
    check_function(
        &mut context,
        &function,
        target,
        &[number, string],
        &[number, recovery],
        &mut queries,
    );
    replay(&mut context, &parsed, &provider, &queries);
}
