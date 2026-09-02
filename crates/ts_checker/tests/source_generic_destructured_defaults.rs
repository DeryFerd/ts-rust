use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, types::TypeFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(205_180);
const TYPES: &str = r#"
type Base<TItem, TData> = {
  item: TItem;
  seed: TData;
  mode?: 'append' | 'reset' | 'replace';
};
type Params<TItem, TData> =
  | Base<TItem, TData> & { reducer?: never; initialValue?: never }
  | Base<TItem, TData> & {
      reducer: (acc: TData, chunk: TItem) => TData;
      initialValue: TData;
    };
"#;

fn source(mode: &str, calls: &str) -> String {
    format!(
        "{TYPES}\n\
         function collect<TItem = string, TData = TItem>({{\n\
           item, seed, mode = {mode},\n\
           reducer = (acc, chunk) => acc, initialValue = seed,\n\
         }}: Params<TItem, TData>): TData {{ return initialValue; }}\n\
         {calls}\n"
    )
}

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic-destructured-defaults.ts\""),
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
            no_implicit_any: true,
            strict_function_types: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn only_node(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(id, record)| {
        (record.kind == kind).then_some(node(parsed, id))
    });
    let result = nodes.next().unwrap();
    assert!(nodes.next().is_none(), "expected one {kind:?}");
    result
}

fn node_text<'a>(source: &'a str, parsed: &ParseResult, node: NodeRef) -> &'a str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

struct Leaf {
    declaration: NodeRef,
    name: NodeRef,
    initializer: Option<NodeRef>,
}

struct Parts {
    declaration: NodeRef,
    name: NodeRef,
    formals: Vec<NodeRef>,
    parameter: NodeRef,
    annotation: NodeRef,
    return_annotation: NodeRef,
    returned: NodeRef,
    leaves: Vec<Leaf>,
    arrow: NodeRef,
    arrow_parameters: Vec<(NodeRef, NodeRef)>,
    arrow_body: NodeRef,
}

fn parts(parsed: &ParseResult) -> Parts {
    let declaration = only_node(parsed, SyntaxKind::FunctionDeclaration);
    let NodeData::FunctionDeclaration(function) =
        &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!();
    };
    let [parameter] = function.parameters.nodes.as_slice() else {
        panic!("expected one required binding parameter");
    };
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(*parameter).unwrap().data
    else {
        unreachable!();
    };
    assert!(parameter_data.initializer.is_none());
    let pattern = parsed.arena.get(parameter_data.name).unwrap();
    assert_eq!(pattern.kind, SyntaxKind::ObjectBindingPattern);
    let NodeData::BindingPattern(pattern) = &pattern.data else {
        unreachable!();
    };
    let leaves = pattern
        .elements
        .nodes
        .iter()
        .map(|&id| {
            let NodeData::BindingElement(element) = &parsed.arena.get(id).unwrap().data else {
                unreachable!();
            };
            assert!(element.property_name.is_none());
            Leaf {
                declaration: node(parsed, id),
                name: node(parsed, element.name.unwrap()),
                initializer: element.initializer.map(|id| node(parsed, id)),
            }
        })
        .collect();
    let arrow = only_node(parsed, SyntaxKind::ArrowFunction);
    let NodeData::ArrowFunction(arrow_data) = &parsed.arena.get(arrow.node).unwrap().data else {
        unreachable!();
    };
    assert!(arrow_data.type_.is_none());
    let arrow_parameters = arrow_data
        .parameters
        .nodes
        .iter()
        .map(|&id| {
            let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(id).unwrap().data
            else {
                unreachable!();
            };
            assert!(parameter.type_.is_none());
            (node(parsed, id), node(parsed, parameter.name))
        })
        .collect();
    let returned = only_node(parsed, SyntaxKind::ReturnStatement);
    let NodeData::ReturnStatement(returned) = &parsed.arena.get(returned.node).unwrap().data
    else {
        unreachable!();
    };
    Parts {
        declaration,
        name: node(parsed, function.name.unwrap()),
        formals: function
            .type_parameters
            .as_ref()
            .unwrap()
            .nodes
            .iter()
            .map(|&id| node(parsed, id))
            .collect(),
        parameter: node(parsed, *parameter),
        annotation: node(parsed, parameter_data.type_.unwrap()),
        return_annotation: node(parsed, function.type_.unwrap()),
        returned: node(parsed, returned.expression.unwrap()),
        leaves,
        arrow,
        arrow_parameters,
        arrow_body: node(parsed, arrow_data.body),
    }
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn value_type(checker: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    checker
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap()
}

#[derive(Default)]
struct Queries {
    types: Vec<(NodeRef, TypeId)>,
    symbols: Vec<(NodeRef, SemanticSymbolId)>,
    returns: Vec<(SignatureId, TypeId)>,
}

impl Queries {
    fn check(&self, checker: &mut CanonicalCheckerContext<'_>) {
        for &(node, expected) in &self.types {
            assert_eq!(checker.get_type_at_location(node), Ok(expected));
        }
        for &(node, expected) in &self.symbols {
            assert_eq!(checker.get_symbol_at_location(node), Ok(Some(expected)));
        }
        for &(signature, expected) in &self.returns {
            assert_eq!(checker.get_return_type_of_signature(signature), Ok(expected));
        }
    }
}

#[allow(clippy::too_many_lines)] // Check the function, bindings, and callback identities together.
fn check_function(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    parts: &Parts,
) -> Queries {
    let mut queries = Queries::default();
    let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
    let mut formals = Vec::new();
    assert_eq!(parts.formals.len(), 2);
    for &declaration in &parts.formals {
        let owner = symbol(checker, declaration);
        let type_ = checker
            .store()
            .declared_type_links(owner)
            .unwrap()
            .declared_type
            .unwrap();
        let record = checker.store().type_payload(type_).unwrap();
        assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
        assert_eq!(record.symbol(), Some(owner));
        let TypeData::TypeParameter(parameter) = record.data() else {
            panic!("each formal must keep its own canonical type");
        };
        assert_eq!(parameter.target, None);
        assert_eq!(parameter.mapper, None);
        assert_eq!(
            parameter.constraint,
            Some(checker.store().intrinsic_bootstrap().unwrap().no_constraint_type),
        );
        assert_eq!(
            parameter.resolved_default_type,
            Some(formals.first().copied().unwrap_or(string)),
        );
        let NodeData::TypeParameterDeclaration(parameter) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!();
        };
        let name = node(parsed, parameter.name);
        queries.types.push((name, type_));
        queries.symbols.push((name, owner));
        formals.push(type_);
    }
    let [item_type, data_type] = formals.as_slice() else {
        unreachable!();
    };
    assert_ne!(item_type, data_type);
    let parameter_owner = symbol(checker, parts.parameter);
    let parent = value_type(checker, parameter_owner);
    let TypeData::Union(union) = checker.store().type_payload(parent).unwrap().data() else {
        panic!("the annotated parent must remain a union");
    };
    assert_eq!(union.union.types.len(), 2);
    for &arm in &union.union.types {
        let TypeData::Intersection(intersection) = checker.store().type_payload(arm).unwrap().data()
        else {
            panic!("each union arm must retain its intersection");
        };
        assert_eq!(intersection.intersection.types.len(), 2);
    }
    queries.types.extend([(parts.parameter, parent), (parts.annotation, parent)]);
    queries.symbols.push((parts.parameter, parameter_owner));
    let callable = value_type(checker, symbol(checker, parts.declaration));
    let function_signature = signature(checker, parts.declaration);
    let record = checker.store().signature(function_signature).unwrap();
    assert_eq!(record.declaration(), Some(parts.declaration));
    assert_eq!(record.type_parameters(), formals.as_slice());
    assert_eq!(record.parameters(), &[parameter_owner]);
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    queries.types.extend([(parts.declaration, callable), (parts.name, callable)]);
    queries.returns.push((function_signature, *data_type));

    let [item, seed, mode, reducer, initial] = parts.leaves.as_slice() else {
        panic!("expected the five written bindings");
    };
    assert_eq!(reducer.initializer, Some(parts.arrow));
    let mode_type = value_type(checker, symbol(checker, mode.declaration));
    assert_eq!(
        checker.type_to_string(mode_type).unwrap(),
        "\"append\" | \"replace\" | \"reset\"",
    );
    let reducer_type = value_type(checker, symbol(checker, reducer.declaration));
    for (leaf, expected) in [
        (item, *item_type),
        (seed, *data_type),
        (mode, mode_type),
        (reducer, reducer_type),
        (initial, *data_type),
    ] {
        let owner = symbol(checker, leaf.declaration);
        assert_ne!(owner, parameter_owner);
        let record = checker.store().symbol(owner).unwrap();
        assert_eq!(record.declarations(), Some(&[leaf.declaration][..]));
        assert_eq!(record.value_declaration(), Some(leaf.declaration));
        assert_eq!(value_type(checker, owner), expected);
        queries.types.extend([(leaf.declaration, expected), (leaf.name, expected)]);
        queries.symbols.extend([(leaf.declaration, owner), (leaf.name, owner)]);
    }
    queries.types.extend([
        (initial.initializer.unwrap(), *data_type),
        (parts.returned, *data_type),
        (parts.return_annotation, *data_type),
    ]);
    queries.symbols.extend([
        (initial.initializer.unwrap(), symbol(checker, seed.declaration)),
        (parts.returned, symbol(checker, initial.declaration)),
    ]);
    let arrow_type = value_type(checker, symbol(checker, parts.arrow));
    assert_ne!(arrow_type, reducer_type);
    queries.types.push((parts.arrow, arrow_type));
    let arrow_signature = signature(checker, parts.arrow);
    let owners = parts
        .arrow_parameters
        .iter()
        .map(|&(node, _)| symbol(checker, node))
        .collect::<Vec<_>>();
    let record = checker.store().signature(arrow_signature).unwrap();
    assert_eq!(record.declaration(), Some(parts.arrow));
    assert_eq!(record.parameters(), owners.as_slice());
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.min_argument_count(), 2);
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(parts.arrow_parameters.len(), 2);
    for ((&(declaration, name), &owner), expected) in parts
        .arrow_parameters
        .iter()
        .zip(&owners)
        .zip([*data_type, *item_type])
    {
        assert_eq!(value_type(checker, owner), expected);
        queries.types.extend([(declaration, expected), (name, expected)]);
        queries.symbols.extend([(declaration, owner), (name, owner)]);
    }
    queries.types.push((parts.arrow_body, *data_type));
    queries.symbols.push((parts.arrow_body, owners[0]));
    queries.returns.push((arrow_signature, *data_type));
    let TypeData::Object(target) = checker.store().type_payload(reducer_type).unwrap().data() else {
        panic!("the reducer must keep its declared callable property type");
    };
    assert_eq!(target.structured.call_signature_count, 1);
    let [target_signature] = target.structured.signatures.as_deref().unwrap() else {
        panic!("expected one contextual signature");
    };
    assert_ne!(*target_signature, arrow_signature);
    let target = checker.store().signature(*target_signature).unwrap();
    let target_parameters = target
        .parameters()
        .iter()
        .map(|&owner| value_type(checker, owner))
        .collect::<Vec<_>>();
    assert_eq!(target_parameters, [*data_type, *item_type]);
    queries.returns.push((*target_signature, *data_type));
    queries
}

fn add_calls(parsed: &ParseResult, expected: &[TypeId], queries: &mut Queries) {
    let mut calls = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == SyntaxKind::CallExpression)
                .then_some((record.range.start, node(parsed, id)))
        })
        .collect::<Vec<_>>();
    calls.sort_by_key(|&(start, _)| start);
    assert_eq!(calls.len(), expected.len());
    queries.types.extend(
        calls.into_iter().zip(expected).map(|((_, node), &type_)| (node, type_)),
    );
}

fn snapshot(
    checker: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl PartialEq + std::fmt::Debug + use<> {
    let store = checker.store();
    let nodes = parsed
        .arena
        .iter()
        .map(|(id, _)| {
            let node = node(parsed, id);
            let owner = checker.file(FILE).unwrap().1.symbol(node).map(|raw| {
                let owner = store.get_merged_symbol(raw).unwrap();
                (
                    owner,
                    store.value_symbol_links(owner).cloned(),
                    store.declared_type_links(owner).cloned(),
                )
            });
            (
                node,
                store.type_node_links(node).cloned(),
                store.symbol_node_links(node).cloned(),
                store.signature_links(node).cloned(),
                owner,
            )
        })
        .collect::<Vec<_>>();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
        ],
        nodes,
        store.source_file_links(checker.source_file(FILE).unwrap()).cloned(),
        checker.diagnostics().clone(),
    )
}

fn replay(checker: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult, queries: &Queries) {
    queries.check(checker);
    let before = snapshot(checker, parsed);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        queries.check(checker);
        assert_eq!(snapshot(checker, parsed), before);
        assert!(checker.store().type_resolution_is_empty());
    }
}

#[test]
fn generic_binding_defaults_keep_formals_context_and_cold_warm_identity() {
    let source = source(
        "'reset'",
        concat!(
            "const supplied: number = collect<string, number>({ item: 'chunk', seed: 1 });\n",
            "const defaulted: string = collect<string>({ item: 'chunk', seed: 'ready' });\n",
        ),
    );
    let parsed = parse_source_file(&source);
    let parts = parts(&parsed);
    for source_first in [false, true] {
        let mut checker = context(&parsed);
        assert!(checker.store().signature_links(parts.declaration).is_none());
        assert!(checker.store().signature_links(parts.arrow).is_none());
        if source_first {
            checker.check_source_file(FILE).unwrap();
        }
        let callable = checker.get_type_at_location(parts.name).unwrap();
        checker.check_source_file(FILE).unwrap();
        assert_eq!(checker.get_type_at_location(parts.name), Ok(callable));
        let mut queries = check_function(&mut checker, &parsed, &parts);
        let intrinsic = checker.store().intrinsic_bootstrap().unwrap();
        add_calls(&parsed, &[intrinsic.number_type, intrinsic.string_type], &mut queries);
        assert!(checker.diagnostics().is_empty());
        replay(&mut checker, &parsed, &queries);
    }
}

#[test]
fn bad_binding_default_keeps_the_property_type_and_native_error() {
    let source = source("1", "");
    let parsed = parse_source_file(&source);
    let parts = parts(&parsed);
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    let queries = check_function(&mut checker, &parsed, &parts);
    let [diagnostic] = checker.diagnostics().as_slice() else {
        panic!("expected only the incompatible mode default");
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.node, Some(parts.leaves[2].name));
    assert_eq!(node_text(&source, &parsed, diagnostic.node.unwrap()), "mode");
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'number' is not assignable to type '\"append\" | \"replace\" | \"reset\"'.",
    );
    assert!(diagnostic.related_information.is_empty());
    replay(&mut checker, &parsed, &queries);
}

#[test]
fn leaf_defaults_keep_the_whole_parameter_required_and_check_arguments() {
    let source = source(
        "'reset'",
        concat!(
            "const omitted: number = collect<string, number>();\n",
            "const invalid: number = collect<string, number>('wrong');\n",
        ),
    );
    let parsed = parse_source_file(&source);
    let parts = parts(&parsed);
    let mut checker = context(&parsed);
    checker.check_source_file(FILE).unwrap();
    let mut queries = check_function(&mut checker, &parsed, &parts);
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    add_calls(&parsed, &[number, number], &mut queries);
    let [missing, invalid] = checker.diagnostics().as_slice() else {
        panic!("expected the missing and invalid argument errors");
    };
    assert_eq!(missing.diagnostic.code(), 2554);
    assert_eq!(node_text(&source, &parsed, missing.node.unwrap()), "collect");
    assert_eq!(missing.range_override, None);
    assert_eq!(
        missing.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 0.",
    );
    let [related] = missing.related_information.as_slice() else {
        panic!("the missing argument must identify the real binding parameter");
    };
    assert_eq!(related.node, Some(parts.parameter));
    assert_eq!(related.diagnostic.code(), 6211);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument matching this binding pattern was not provided.",
    );
    assert_eq!(invalid.diagnostic.code(), 2345);
    assert_eq!(node_text(&source, &parsed, invalid.node.unwrap()), "'wrong'");
    assert_eq!(invalid.diagnostic.arguments, ["string", "Params<string, number>"]);
    assert_eq!(invalid.range_override, None);
    assert!(invalid.related_information.is_empty());
    replay(&mut checker, &parsed, &queries);
}
