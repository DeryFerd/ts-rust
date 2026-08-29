use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(8_198);
const ARRAY_LIBRARY: &str = "interface Array<T> {} interface ReadonlyArray<T> {}\n";

struct TypeParameterParts {
    declaration: NodeRef,
    name: NodeRef,
    constraint: Option<NodeRef>,
    default: Option<NodeRef>,
}

struct ParameterParts {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
}

struct FunctionParts {
    declaration: NodeRef,
    name: NodeRef,
    type_parameters: Vec<TypeParameterParts>,
    parameters: Vec<ParameterParts>,
    return_type: NodeRef,
}

impl FunctionParts {
    fn annotations(&self) -> Vec<NodeRef> {
        self.type_parameters
            .iter()
            .flat_map(|parameter| [parameter.constraint, parameter.default])
            .flatten()
            .chain(self.parameters.iter().map(|parameter| parameter.annotation))
            .chain([self.return_type])
            .collect()
    }
}

#[derive(Debug, Eq, PartialEq)]
struct TypeParameterState {
    type_: TypeId,
    symbol: SemanticSymbolId,
    constraint: Option<TypeId>,
    default: Option<TypeId>,
    base_constraint: Option<TypeId>,
}

#[derive(Debug, Eq, PartialEq)]
struct SignatureSnapshot {
    callable: TypeId,
    signature: SignatureId,
    owner: SemanticSymbolId,
    type_parameters: Vec<TypeParameterState>,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    return_type: TypeId,
    annotations: Vec<(NodeRef, TypeId)>,
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
                EscapedName::source("\"/project/generic-query-signatures.ts\""),
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
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn function_parts(parsed: &ParseResult, expected: &str) -> FunctionParts {
    let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            let name = function.name?;
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            if identifier.text != expected {
                return None;
            }
            Some(FunctionParts {
                declaration: node_ref(node),
                name: node_ref(name),
                type_parameters: function
                    .type_parameters
                    .as_ref()?
                    .nodes
                    .iter()
                    .map(|&node| {
                        let NodeData::TypeParameterDeclaration(parameter) =
                            &parsed.arena.get(node).unwrap().data
                        else {
                            panic!("expected a type parameter")
                        };
                        TypeParameterParts {
                            declaration: node_ref(node),
                            name: node_ref(parameter.name),
                            constraint: parameter.constraint.map(node_ref),
                            default: parameter.default_type.map(node_ref),
                        }
                    })
                    .collect(),
                parameters: function
                    .parameters
                    .nodes
                    .iter()
                    .map(|&node| {
                        let NodeData::ParameterDeclaration(parameter) =
                            &parsed.arena.get(node).unwrap().data
                        else {
                            panic!("expected a value parameter")
                        };
                        ParameterParts {
                            declaration: node_ref(node),
                            name: node_ref(parameter.name),
                            annotation: node_ref(parameter.type_.unwrap()),
                        }
                    })
                    .collect(),
                return_type: node_ref(function.type_?),
            })
        })
        .unwrap_or_else(|| panic!("missing function {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize) {
    let store = context.store();
    (
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
    )
}

#[allow(clippy::too_many_lines)] // Check one signature and its owned artifact graph together.
fn snapshot(
    context: &mut CanonicalCheckerContext<'_>,
    function: &FunctionParts,
) -> SignatureSnapshot {
    let owner = symbol(context, function.declaration);
    let callable = context.get_type_at_location(function.name).unwrap();
    assert_eq!(
        context.get_type_at_location(function.declaration).unwrap(),
        callable,
    );
    assert_eq!(
        context.get_symbol_at_location(function.name).unwrap(),
        Some(owner),
    );
    assert_eq!(
        context.get_symbol_declarations(owner).unwrap(),
        [function.declaration],
    );
    let signature = context
        .store()
        .signature_links(function.declaration)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the declaration must own its signature");
    let record = context.store().type_payload(callable).unwrap();
    let TypeData::Object(object) = record.data() else {
        panic!("the function must have a callable object")
    };
    assert_eq!(record.symbol(), Some(owner));
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..]),
    );
    assert_eq!(object.structured.call_signature_count, 1);

    // Demand the signature return before replaying individual annotation queries.
    let return_type = context.get_return_type_of_signature(signature).unwrap();
    let annotations = function
        .annotations()
        .into_iter()
        .map(|node| {
            let type_ = context.get_type_from_type_node(node).unwrap();
            assert_eq!(context.get_type_at_location(node).unwrap(), type_);
            (node, type_)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        context
            .get_type_from_type_node(function.return_type)
            .unwrap(),
        return_type,
    );

    let type_parameters = function
        .type_parameters
        .iter()
        .map(|parameter| {
            let symbol = symbol(context, parameter.declaration);
            let type_ = context
                .store()
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .expect("the binder-owned parameter must have a declared type");
            assert_eq!(context.get_type_at_location(parameter.name).unwrap(), type_);
            assert_eq!(
                context.get_symbol_at_location(parameter.name).unwrap(),
                Some(symbol),
            );
            assert_eq!(
                context.get_symbol_declarations(symbol).unwrap(),
                [parameter.declaration],
            );
            let record = context.store().type_payload(type_).unwrap();
            assert_eq!(record.symbol(), Some(symbol));
            let TypeData::TypeParameter(data) = record.data() else {
                panic!("expected a canonical type parameter")
            };
            assert_eq!(data.target, None);
            assert_eq!(data.mapper, None);
            TypeParameterState {
                type_,
                symbol,
                constraint: data.constraint,
                default: data.resolved_default_type,
                base_constraint: data.constrained.resolved_base_constraint,
            }
        })
        .collect::<Vec<_>>();
    let parameters = function
        .parameters
        .iter()
        .map(|parameter| {
            let symbol = symbol(context, parameter.declaration);
            let type_ = context
                .get_type_from_type_node(parameter.annotation)
                .unwrap();
            assert_eq!(context.get_type_at_location(parameter.name).unwrap(), type_);
            assert_eq!(
                context.get_symbol_at_location(parameter.name).unwrap(),
                Some(symbol),
            );
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .unwrap()
                    .resolved_type,
                Some(type_),
            );
            (symbol, type_)
        })
        .collect::<Vec<_>>();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(function.declaration));
    assert_eq!(
        record.type_parameters(),
        type_parameters
            .iter()
            .map(|parameter| parameter.type_)
            .collect::<Vec<_>>(),
    );
    assert_eq!(
        record.parameters(),
        parameters
            .iter()
            .map(|&(symbol, _)| symbol)
            .collect::<Vec<_>>(),
    );
    assert_eq!(record.resolved_return_type(), Some(return_type));
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    SignatureSnapshot {
        callable,
        signature,
        owner,
        type_parameters,
        parameters,
        return_type,
        annotations,
    }
}

fn check_orders(
    source: &str,
    name: &str,
    assert_case: impl Fn(
        &mut CanonicalCheckerContext<'_>,
        &ParseResult,
        &FunctionParts,
        &SignatureSnapshot,
    ),
) {
    let parsed = parse_source_file(source);
    let function = function_parts(&parsed, name);
    let mut first_queries = vec![
        None,
        Some(function.parameters[0].annotation),
        Some(function.return_type),
    ];
    first_queries.extend(function.type_parameters.iter().flat_map(|parameter| {
        [parameter.constraint, parameter.default]
            .into_iter()
            .flatten()
            .map(Some)
    }));
    for first in first_queries {
        let mut context = context(&parsed);
        assert!(
            context
                .store()
                .signature_links(function.declaration)
                .is_none()
        );
        let early = first.map(|node| {
            let type_ = context
                .get_type_from_type_node(node)
                .unwrap_or_else(|error| panic!("{name}, annotation-first {node:?}: {error:?}"));
            assert!(
                context
                    .store()
                    .signature_links(function.declaration)
                    .is_none()
            );
            (node, type_)
        });
        context
            .check_source_file(FILE)
            .unwrap_or_else(|error| panic!("{name}, first {first:?}: {error:?}"));
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics(),
        );
        let cold = snapshot(&mut context, &function);
        if let Some(early) = early {
            assert!(
                cold.annotations.contains(&early),
                "the early annotation changed identity",
            );
        }
        assert_case(&mut context, &parsed, &function, &cold);
        let before = counts(&context);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(snapshot(&mut context, &function), cold);
        assert_case(&mut context, &parsed, &function, &cold);
        assert_eq!(counts(&context), before);
        assert!(context.diagnostics().is_empty());
    }
}

fn assert_parameter_return(snapshot: &SignatureSnapshot, index: usize) {
    assert_eq!(
        snapshot.parameters[0].1,
        snapshot.type_parameters[index].type_,
    );
    assert_eq!(snapshot.return_type, snapshot.type_parameters[index].type_);
}

fn assert_array(context: &CanonicalCheckerContext<'_>, array: TypeId, element: TypeId) {
    let TypeData::TypeReference(reference) = context.store().type_payload(array).unwrap().data()
    else {
        panic!("expected a canonical array reference")
    };
    assert_eq!(
        reference.object.target,
        Some(context.global_types().array_type),
    );
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[element][..]),
    );
}

#[test]
fn forward_constraint_reuses_the_later_parameter_identity() {
    check_orders(
        "declare function forward<T extends U, U>(value: T): T;",
        "forward",
        |context, _, function, snapshot| {
            let [t, u] = snapshot.type_parameters.as_slice() else {
                panic!("expected T and U")
            };
            assert_ne!(t.type_, u.type_);
            assert_eq!(t.constraint, Some(u.type_));
            let absent = context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .no_constraint_type;
            assert_eq!(t.base_constraint, Some(absent));
            assert_eq!(u.constraint, Some(absent));
            assert_eq!(t.default, Some(absent));
            assert_eq!(u.default, Some(absent));
            let bound = function.type_parameters[0].constraint.unwrap();
            assert_eq!(context.get_type_from_type_node(bound).unwrap(), u.type_);
            assert_eq!(
                context.get_symbol_at_location(bound).unwrap(),
                Some(u.symbol),
            );
            assert_parameter_return(snapshot, 0);
        },
    );
}

#[test]
fn union_alias_constraint_retains_the_function_parameter() {
    check_orders(
        "type StringOr<T> = T | string; declare function union<B, T extends StringOr<B>>(value: T): T;",
        "union",
        |context, _, _, snapshot| {
            let [b, t] = snapshot.type_parameters.as_slice() else {
                panic!("expected B and T")
            };
            let TypeData::Union(union) = context
                .store()
                .type_payload(t.constraint.unwrap())
                .unwrap()
                .data()
            else {
                panic!("the constraint must be the queried union")
            };
            assert_eq!(union.union.types.len(), 2);
            assert!(union.union.types.contains(&b.type_));
            assert!(
                union
                    .union
                    .types
                    .contains(&context.store().intrinsic_bootstrap().unwrap().string_type)
            );
            assert_parameter_return(snapshot, 1);
        },
    );
}

#[test]
fn keyof_constraint_retains_its_target_parameter() {
    check_orders(
        "declare function key<O, K extends keyof O>(value: K): K;",
        "key",
        |context, _, _, snapshot| {
            let [o, k] = snapshot.type_parameters.as_slice() else {
                panic!("expected O and K")
            };
            let TypeData::Index(index) = context
                .store()
                .type_payload(k.constraint.unwrap())
                .unwrap()
                .data()
            else {
                panic!("the constraint must be the queried keyof type")
            };
            assert_eq!(index.target, o.type_);
            assert_eq!(
                k.base_constraint,
                Some(
                    context
                        .store()
                        .intrinsic_bootstrap()
                        .unwrap()
                        .string_number_symbol_type,
                ),
            );
            assert_parameter_return(snapshot, 1);
        },
    );
}

#[test]
fn object_alias_parameter_and_return_share_the_query_result() {
    check_orders(
        "type Box<T> = { value: T }; function keep<T>(value: Box<T>): Box<T> { return value; }",
        "keep",
        |context, parsed, _, snapshot| {
            assert_eq!(snapshot.parameters[0].1, snapshot.return_type);
            assert_ne!(snapshot.return_type, snapshot.type_parameters[0].type_);
            let returned = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::ReturnStatement(statement) = &record.data else {
                        return None;
                    };
                    statement
                        .expression
                        .map(|node| NodeRef::new(parsed.arena.id(), FILE, node))
                })
                .unwrap();
            assert_eq!(
                context.get_type_at_location(returned).unwrap(),
                snapshot.return_type,
            );
            assert_eq!(
                context.get_symbol_at_location(returned).unwrap(),
                Some(snapshot.parameters[0].0),
            );
        },
    );
}

#[test]
fn array_constraint_and_default_share_the_query_result() {
    let source =
        format!("{ARRAY_LIBRARY}declare function arrays<T, U extends T[] = T[]>(value: U): U;");
    check_orders(&source, "arrays", |context, _, _, snapshot| {
        let [t, u] = snapshot.type_parameters.as_slice() else {
            panic!("expected T and U")
        };
        assert_eq!(u.constraint, u.default);
        assert_array(context, u.constraint.unwrap(), t.type_);
        assert_parameter_return(snapshot, 1);
    });
}

#[test]
fn array_default_call_substitutes_the_completed_argument_prefix() {
    let source = format!(
        "{ARRAY_LIBRARY}declare function arrays<T, U extends T[] = T[]>(value: U): U;\n\
         const numbers: number[] = arrays<number>([1, 2]);"
    );
    check_orders(&source, "arrays", |context, parsed, _, snapshot| {
        let call = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(record.data, NodeData::CallExpression(_)).then_some(NodeRef::new(
                    parsed.arena.id(),
                    FILE,
                    node,
                ))
            })
            .unwrap();
        let (name, annotation) = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), FILE, variable.name),
                    NodeRef::new(parsed.arena.id(), FILE, variable.type_?),
                ))
            })
            .unwrap();
        let expected = context.get_type_from_type_node(annotation).unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_array(context, expected, number);
        assert_eq!(context.get_type_at_location(call).unwrap(), expected);
        assert_eq!(context.get_type_at_location(name).unwrap(), expected);
        let selected = context
            .store()
            .signature_links(call)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let selected = context.store().signature(selected).unwrap();
        assert!(selected.type_parameters().is_empty());
        assert_eq!(selected.target(), Some(snapshot.signature));
        assert!(selected.mapper().is_some());
        assert_eq!(selected.resolved_return_type(), Some(expected));
    });
}

#[test]
fn explicit_any_constraint_keeps_raw_and_effective_types_distinct() {
    check_orders(
        "declare function anyBound<T extends any>(value: T): T;",
        "anyBound",
        |context, _, function, snapshot| {
            let (any_type, unknown_type) = {
                let bootstrap = context.store().intrinsic_bootstrap().unwrap();
                (bootstrap.any_type, bootstrap.unknown_type)
            };
            assert_eq!(snapshot.type_parameters[0].constraint, Some(unknown_type));
            let constraint = function.type_parameters[0].constraint.unwrap();
            assert_eq!(
                context.get_type_from_type_node(constraint).unwrap(),
                any_type
            );
            assert_parameter_return(snapshot, 0);
        },
    );
}
