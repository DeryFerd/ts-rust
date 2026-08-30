use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, type_records::TypeCacheState,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY_FILE: FileId = FileId::new(96_020);
const FILE: FileId = FileId::new(96_021);
const LIBRARY: &str = "interface Array<T> {} interface ReadonlyArray<T> {}";

// Keep the upstream conditionalContextualReturnSubstitutionCache.ts source intact.
const CONTEXTUAL_CAST: &str = concat!(
    "// @strict: true\n",
    "// @noEmit: true\n",
    "\n",
    "// https://github.com/microsoft/typescript-go/issues/3488\n",
    "\n",
    "export function cast<T>(value: T): {\n",
    "    as: <K extends T>() => null extends T ? K | null : undefined extends T ? K | undefined : K;\n",
    "} {\n",
    "    return {\n",
    "        as: <K extends T>(): null extends T ? K | null : undefined extends T ? K | undefined : K => {\n",
    "            return value as K;\n",
    "        },\n",
    "    };\n",
    "}\n",
);

struct FunctionParts {
    node: NodeRef,
    parameter: NodeRef,
    constraint: NodeRef,
    return_type: NodeRef,
    true_type: NodeRef,
    false_type: NodeRef,
}

fn context<'a>(
    library: &'a ParseResult,
    source: &'a ParseResult,
    module_state: CanonicalModuleState,
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (parsed, file, path, declaration, module_state) in [
        (
            library,
            LIBRARY_FILE,
            "\"/lib/function-type-context.d.ts\"",
            true,
            CanonicalModuleState::Script,
        ),
        (
            source,
            FILE,
            "\"/project/function-type-context.ts\"",
            false,
            module_state,
        ),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration,
                    declaration,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY_FILE, &library.arena), (FILE, &source.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_function_types: true,
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn function_parts(parsed: &ParseResult) -> FunctionParts {
    let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::FunctionTypeNode(function) = &record.data else {
                return None;
            };
            assert!(function.parameters.nodes.is_empty());
            let [parameter] = function.type_parameters.as_ref()?.nodes.as_slice() else {
                panic!("expected one function type parameter")
            };
            let NodeData::TypeParameterDeclaration(data) = &parsed.arena.get(*parameter)?.data
            else {
                panic!("expected a type parameter declaration")
            };
            let return_type = function.type_?;
            let NodeData::ConditionalTypeNode(conditional) = &parsed.arena.get(return_type)?.data
            else {
                panic!("expected a conditional return annotation")
            };
            Some(FunctionParts {
                node: node_ref(node),
                parameter: node_ref(*parameter),
                constraint: node_ref(data.constraint?),
                return_type: node_ref(return_type),
                true_type: node_ref(conditional.true_type),
                false_type: node_ref(conditional.false_type),
            })
        })
        .expect("missing the generic function type")
}

fn parameter_node(parsed: &ParseResult, name: &str, owner: SyntaxKind) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeParameterDeclaration(parameter) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(parameter.name)?.data else {
                return None;
            };
            (identifier.text == name && parsed.arena.get(record.parent?)?.kind == owner)
                .then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap_or_else(|| panic!("missing {name} in {owner:?}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn parameter_type(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> TypeId {
    let owner = symbol(context, declaration);
    let type_ = context
        .store()
        .declared_type_links(owner)
        .and_then(|links| links.declared_type)
        .expect("the binder-owned type parameter must have a declared type");
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    assert_eq!(
        context.store().symbol(owner).unwrap().declarations(),
        Some(&[declaration][..]),
    );
    let TypeData::TypeParameter(parameter) = record.data() else {
        panic!("expected the canonical type parameter")
    };
    assert_eq!(parameter.target, None);
    assert_eq!(parameter.mapper, None);
    type_
}

fn function_signature(
    context: &mut CanonicalCheckerContext<'_>,
    function: &FunctionParts,
) -> (TypeId, SignatureId, TypeId) {
    let callable = context.get_type_from_type_node(function.node).unwrap();
    let record = context.store().type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(symbol(context, function.node)));
    let TypeData::Object(object) = record.data() else {
        panic!("the function type must retain its callable object")
    };
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected one call signature")
    };
    let signature = *signature;
    assert_eq!(object.structured.call_signature_count, 1);
    let parameter = parameter_type(context, function.parameter);
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(function.node));
    assert_eq!(record.type_parameters(), [parameter]);
    assert!(record.parameters().is_empty());
    assert_eq!(record.min_argument_count(), 0);
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    (callable, signature, parameter)
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 5] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.conditional_root_len(),
    ]
}

fn assert_cold(context: &CanonicalCheckerContext<'_>, nodes: &[NodeRef]) {
    for node in nodes {
        assert!(
            context.store().type_node_links(*node).is_none(),
            "the undemanded node {node:?} must stay cold",
        );
    }
}

fn assert_outer_conditional(
    context: &CanonicalCheckerContext<'_>,
    function: &FunctionParts,
    return_type: TypeId,
    outer: TypeId,
    inner: TypeId,
) {
    assert_ne!(outer, inner);
    let TypeData::TypeParameter(parameter) = context.store().type_payload(inner).unwrap().data()
    else {
        panic!("expected the inner signature parameter")
    };
    assert_eq!(parameter.constraint, Some(outer));
    let TypeData::Conditional(conditional) =
        context.store().type_payload(return_type).unwrap().data()
    else {
        panic!("the outer parameter must keep the return conditional deferred")
    };
    let null = context.store().intrinsic_bootstrap().unwrap().null_type;
    assert_eq!(conditional.check_type, null);
    assert_eq!(conditional.extends_type, outer);
    assert_eq!(conditional.mapper, None);
    assert_eq!(conditional.resolved_true_type, None);
    assert_eq!(conditional.resolved_false_type, None);
    let root = context.store().conditional_root(conditional.root).unwrap();
    assert_eq!(root.node(), function.return_type);
    assert_eq!(root.check_type(), null);
    assert_eq!(root.extends_type(), outer);
    assert_eq!(root.outer_type_parameters(), Some(&[outer, inner][..]));
    assert!(!root.is_distributive());
    assert!(root.infer_type_parameters().unwrap_or_default().is_empty());
    assert_eq!(root.alias(), None);
    let TypeCacheState::Allocated(cache) = root.instantiations() else {
        panic!("the source conditional must own its identity cache")
    };
    assert_eq!(cache.len(), 1);
    assert_eq!(cache.values().copied().collect::<Vec<_>>(), [return_type]);
    assert_cold(context, &[function.true_type, function.false_type]);
}

#[test]
fn contextual_cast_type_query_keeps_outer_and_inner_parameters_and_body_separate() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(CONTEXTUAL_CAST);
    let function = function_parts(&parsed);
    let outer_node = parameter_node(&parsed, "T", SyntaxKind::FunctionDeclaration);
    let arrow_node = parameter_node(&parsed, "K", SyntaxKind::ArrowFunction);
    let mut context = context(&library, &parsed, CanonicalModuleState::External);
    let arrow_symbol = symbol(&context, arrow_node);
    assert_ne!(arrow_symbol, symbol(&context, function.parameter));
    assert_ne!(arrow_symbol, symbol(&context, outer_node));

    let (callable, signature, inner) = function_signature(&mut context, &function);
    let outer = parameter_type(&context, outer_node);
    assert_eq!(
        context
            .store()
            .signature(signature)
            .unwrap()
            .resolved_return_type(),
        None,
    );
    assert_cold(
        &context,
        &[
            function.return_type,
            function.true_type,
            function.false_type,
        ],
    );
    let return_type = context.get_return_type_of_signature(signature).unwrap();
    assert_outer_conditional(&context, &function, return_type, outer, inner);
    assert_eq!(
        context
            .get_type_from_type_node(function.constraint)
            .unwrap(),
        outer,
    );
    assert_eq!(
        context
            .get_type_from_type_node(function.return_type)
            .unwrap(),
        return_type,
    );

    let warm = counts(&context);
    for _ in 0..2 {
        assert_eq!(
            function_signature(&mut context, &function),
            (callable, signature, inner),
        );
        assert_eq!(
            context.get_return_type_of_signature(signature).unwrap(),
            return_type,
        );
        assert_outer_conditional(&context, &function, return_type, outer, inner);
        assert_eq!(counts(&context), warm);
        assert!(context.store().declared_type_links(arrow_symbol).is_none());
        assert!(context.diagnostics().is_empty());
        assert!(
            !context
                .store()
                .source_file_links(context.source_file(FILE).unwrap())
                .is_some_and(|links| links.type_checked),
        );
    }
}

#[test]
fn outer_conditional_return_queries_agree_before_and_after_source_checking() {
    let library = parse_source_file(LIBRARY);
    let parsed = parse_source_file(concat!(
        "declare function cast<T>(value: T): {\n",
        "    as: <K extends T>() => null extends T ? K | null : undefined extends T ? K | undefined : K;\n",
        "};\n",
    ));
    let function = function_parts(&parsed);
    let outer_node = parameter_node(&parsed, "T", SyntaxKind::FunctionDeclaration);

    for order in ["source", "function", "return"] {
        let mut context = context(&library, &parsed, CanonicalModuleState::Script);
        if order == "source" {
            context.check_source_file(FILE).unwrap();
        }
        let early_return = (order == "return").then(|| {
            context
                .get_type_from_type_node(function.return_type)
                .unwrap()
        });
        if early_return.is_some() {
            assert!(context.store().signature_links(function.node).is_none());
        }
        let (callable, signature, inner) = function_signature(&mut context, &function);
        let outer = parameter_type(&context, outer_node);
        let return_type = context.get_return_type_of_signature(signature).unwrap();
        if let Some(early_return) = early_return {
            assert_eq!(return_type, early_return);
        }
        assert_outer_conditional(&context, &function, return_type, outer, inner);
        context.check_source_file(FILE).unwrap();
        assert!(context.diagnostics().is_empty());

        let warm = counts(&context);
        let diagnostics = context.diagnostics().clone();
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(
                function_signature(&mut context, &function),
                (callable, signature, inner),
                "{order}-first",
            );
            assert_eq!(
                context.get_return_type_of_signature(signature).unwrap(),
                return_type,
            );
            assert_eq!(
                context
                    .get_type_from_type_node(function.return_type)
                    .unwrap(),
                return_type,
            );
            assert_outer_conditional(&context, &function, return_type, outer, inner);
            assert_eq!(counts(&context), warm, "{order}-first");
            assert_eq!(context.diagnostics(), &diagnostics);
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep branch demand, its diagnostic, and replay on one source.
fn concrete_function_returns_keep_unselected_constraint_errors_cold_until_demand() {
    let library = parse_source_file(LIBRARY);
    for (annotation, select_inner) in [
        ("number extends number ? K : OnlyText<number>", true),
        ("string extends number ? OnlyText<number> : boolean", false),
    ] {
        let parsed = parse_source_file(&format!(
            "type OnlyText<T extends string> = T;\n\
             declare let callback: <K extends number>() => {annotation};\n",
        ));
        let function = function_parts(&parsed);
        let unselected = if select_inner {
            function.false_type
        } else {
            function.true_type
        };
        let NodeData::TypeReferenceNode(reference) =
            &parsed.arena.get(unselected.node).unwrap().data
        else {
            panic!("the unselected branch must reference OnlyText")
        };
        let argument = NodeRef::new(
            parsed.arena.id(),
            FILE,
            reference.type_arguments.as_ref().unwrap().nodes[0],
        );

        for annotation_first in [false, true] {
            let mut context = context(&library, &parsed, CanonicalModuleState::Script);
            let (callable, signature, inner) = function_signature(&mut context, &function);
            assert_eq!(
                context
                    .store()
                    .signature(signature)
                    .unwrap()
                    .resolved_return_type(),
                None,
            );
            assert_cold(
                &context,
                &[
                    function.return_type,
                    function.true_type,
                    function.false_type,
                ],
            );
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let number = bootstrap.number_type;
            let expected = if select_inner {
                inner
            } else {
                bootstrap.boolean_type
            };
            let early_return = annotation_first.then(|| {
                context
                    .get_type_from_type_node(function.return_type)
                    .unwrap()
            });
            let return_type = context.get_return_type_of_signature(signature).unwrap();
            assert_eq!(return_type, expected);
            if let Some(early_return) = early_return {
                assert_eq!(early_return, return_type);
            }
            let TypeData::TypeParameter(parameter) =
                context.store().type_payload(inner).unwrap().data()
            else {
                panic!("expected the constrained signature parameter")
            };
            assert_eq!(parameter.constraint, Some(number));
            assert_cold(&context, &[unselected, argument]);
            assert!(context.diagnostics().is_empty());

            let warm = counts(&context);
            for _ in 0..2 {
                assert_eq!(
                    function_signature(&mut context, &function),
                    (callable, signature, inner),
                );
                assert_eq!(
                    context.get_return_type_of_signature(signature).unwrap(),
                    expected,
                );
                assert_eq!(
                    context
                        .get_type_from_type_node(function.return_type)
                        .unwrap(),
                    expected,
                );
                assert_cold(&context, &[unselected, argument]);
                assert_eq!(counts(&context), warm);
                assert!(context.diagnostics().is_empty());
            }

            assert_eq!(context.get_type_from_type_node(unselected).unwrap(), number);
            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!("direct branch demand must report one constraint error")
            };
            assert_eq!(diagnostic.diagnostic.code(), 2344);
            assert_eq!(diagnostic.node, Some(argument));
            assert_eq!(diagnostic.range_override, None);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type 'number' does not satisfy the constraint 'string'.",
            );
            let warm = counts(&context);
            let diagnostics = context.diagnostics().clone();
            assert_eq!(context.get_type_from_type_node(unselected).unwrap(), number);
            assert_eq!(
                context.get_return_type_of_signature(signature).unwrap(),
                expected,
            );
            assert_eq!(counts(&context), warm);
            assert_eq!(context.diagnostics(), &diagnostics);
        }
    }
}
