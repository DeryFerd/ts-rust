use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, TypePredicateId, signatures::TypePredicateKind,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_200);

const BRANCHES: &str = concat!(
    "declare function isNumber(value: unknown): value is number;\n",
    "class Receiver {\n",
    "  value!: number | string;\n",
    "  read(): number | string {\n",
    "    if (isNumber(this.value)) {\n",
    "      const numberValue: number = this.value;\n",
    "      return numberValue;\n",
    "    } else {\n",
    "      const stringValue: string = this.value;\n",
    "      return stringValue;\n",
    "    }\n",
    "  }\n",
    "  readNegated(): number | string {\n",
    "    if (!isNumber(this.value)) {\n",
    "      const negatedString: string = this.value;\n",
    "      return negatedString;\n",
    "    } else {\n",
    "      const negatedNumber: number = this.value;\n",
    "      return negatedNumber;\n",
    "    }\n",
    "  }\n",
    "}\n",
);

const ERRORS: &str = concat!(
    "declare function isNumber(value: unknown): value is number;\n",
    "declare function isPositive(value: number): value is number;\n",
    "class Receiver {\n",
    "  value!: number | string;\n",
    "  text: string = 'x';\n",
    "  badArgument(): void {\n",
    "    if (isPositive(this.text)) {}\n",
    "  }\n",
    "  badReturn(): string {\n",
    "    if (isNumber(this.value)) {\n",
    "      return this.value;\n",
    "    } else {\n",
    "      return this.value;\n",
    "    }\n",
    "  }\n",
    "}\n",
);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-call-conditions.ts\""),
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
        [(FILE, &parsed.arena)].into_iter().collect(),
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
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn named(parsed: &ParseResult, kind: SyntaxKind, expected: &str) -> (NodeRef, NodeRef) {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        if record.kind != kind {
            return None;
        }
        let name = match &record.data {
            NodeData::ClassDeclaration(data) => data.name?,
            NodeData::FunctionDeclaration(data) => data.name?,
            NodeData::MethodDeclaration(data) => data.name,
            NodeData::PropertyDeclaration(data) => data.name,
            NodeData::VariableDeclaration(data) => data.name,
            _ => return None,
        };
        let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
            return None;
        };
        (identifier.text == expected).then(|| (node(parsed, id), node(parsed, name)))
    });
    let found = matches
        .next()
        .unwrap_or_else(|| panic!("missing {expected} declaration"));
    assert!(matches.next().is_none(), "duplicate {expected} declaration");
    found
}

fn owner(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn calls(parsed: &ParseResult, expected: &str) -> Vec<(NodeRef, NodeRef, NodeRef)> {
    parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::CallExpression(call) = &record.data else {
                return None;
            };
            let NodeData::Identifier(callee) = &parsed.arena.get(call.expression)?.data else {
                return None;
            };
            if callee.text != expected {
                return None;
            }
            let [argument] = call.arguments.nodes.as_slice() else {
                panic!("the predicate call has one real property argument");
            };
            assert!(call.type_arguments.is_none());
            assert!(matches!(
                parsed.arena.get(*argument).unwrap().data,
                NodeData::PropertyAccessExpression(_)
            ));
            Some((
                node(parsed, id),
                node(parsed, call.expression),
                node(parsed, *argument),
            ))
        })
        .collect()
}

fn predicate_signature(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    expected: &str,
    parameter_type: TypeId,
) -> (TypeId, SignatureId, TypePredicateId) {
    let (declaration, name) = named(parsed, SyntaxKind::FunctionDeclaration, expected);
    let symbol = owner(context, declaration);
    let NodeData::FunctionDeclaration(function) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let [parameter] = function.parameters.nodes.as_slice() else {
        panic!("the predicate has one declared parameter");
    };
    let parameter = node(parsed, *parameter);
    let parameter_symbol = owner(context, parameter);
    let annotation = node(parsed, function.type_.unwrap());
    let NodeData::TypePredicateNode(predicate_syntax) =
        &parsed.arena.get(annotation.node).unwrap().data
    else {
        panic!("the return annotation is a real type predicate");
    };
    let boolean = context.store().intrinsic_bootstrap().unwrap().boolean_type;
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let type_ = context.get_type_at_location(name).unwrap();
    let signature = context
        .store()
        .signature_links(declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    assert_eq!(context.get_return_type_of_signature(signature), Ok(boolean));
    assert_eq!(context.get_type_from_type_node(annotation), Ok(boolean));
    assert_eq!(
        context.get_type_from_type_node(node(parsed, predicate_syntax.type_.unwrap())),
        Ok(number)
    );
    assert_eq!(context.get_symbol_at_location(name), Ok(Some(symbol)));
    let store = context.store();
    let function_symbol = store.symbol(symbol).unwrap();
    assert_eq!(function_symbol.flags(), SymbolFlags::FUNCTION);
    assert_eq!(function_symbol.declarations(), Some(&[declaration][..]));
    assert_eq!(function_symbol.value_declaration(), Some(declaration));
    let TypeData::Object(callable) = store.type_payload(type_).unwrap().data() else {
        panic!("the predicate keeps its canonical function object");
    };
    assert_eq!(
        callable.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(callable.structured.call_signature_count, 1);
    let record = store.signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.parameters(), &[parameter_symbol]);
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(record.resolved_return_type(), Some(boolean));
    assert!(record.type_parameters().is_empty());
    assert!(record.this_parameter().is_none());
    assert!(!record.has_rest_parameter());
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
    assert_eq!(
        store
            .value_symbol_links(parameter_symbol)
            .unwrap()
            .resolved_type,
        Some(parameter_type)
    );
    let predicate = record.resolved_type_predicate().unwrap();
    let record = store.type_predicate(predicate).unwrap();
    assert_eq!(record.kind(), TypePredicateKind::Identifier);
    assert_eq!(record.parameter_name(), "value");
    assert_eq!(record.parameter_index(), 0);
    assert_eq!(record.type_id(), Some(number));
    assert_eq!(
        store
            .symbol_node_links(node(parsed, predicate_syntax.parameter_name))
            .unwrap()
            .resolved_symbol,
        Some(parameter_symbol)
    );
    (type_, signature, predicate)
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.type_predicate_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
            store.type_resolution_len(),
        ],
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = node(parsed, id);
                (
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect::<Vec<_>>(),
        store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        context.diagnostics().clone(),
    )
}

fn bad_return_site(parsed: &ParseResult) -> NodeRef {
    let (method, _) = named(parsed, SyntaxKind::MethodDeclaration, "badReturn");
    let NodeData::MethodDeclaration(method) = &parsed.arena.get(method.node).unwrap().data else {
        unreachable!()
    };
    let NodeData::Block(body) = &parsed.arena.get(method.body.unwrap()).unwrap().data else {
        unreachable!()
    };
    let [statement] = body.statements.nodes.as_slice() else {
        panic!("the method contains one conditional");
    };
    let NodeData::IfStatement(condition) = &parsed.arena.get(*statement).unwrap().data else {
        unreachable!()
    };
    let NodeData::Block(branch) = &parsed.arena.get(condition.then_statement).unwrap().data else {
        unreachable!()
    };
    let [returned] = branch.statements.nodes.as_slice() else {
        panic!("the true branch contains one return");
    };
    assert_eq!(
        parsed.arena.get(*returned).unwrap().kind,
        SyntaxKind::ReturnStatement
    );
    node(parsed, *returned)
}

fn check(source: &str, invalid: bool) {
    let parsed = parse_source_file(source);
    for query_first in [false, true] {
        let mut context = context(&parsed);
        let (class, class_name) = named(&parsed, SyntaxKind::ClassDeclaration, "Receiver");
        if query_first {
            context.get_type_at_location(class_name).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        assert!(
            context
                .store()
                .source_file_links(context.source_file(FILE).unwrap())
                .unwrap()
                .type_checked
        );
        let diagnostics = context.diagnostics().as_slice();
        if invalid {
            let bad_calls = calls(&parsed, "isPositive");
            let [(_, _, argument)] = bad_calls.as_slice() else {
                panic!("one invalid predicate call");
            };
            let expected = [
                (
                    2345,
                    *argument,
                    ["string", "number"],
                    "Argument of type 'string' is not assignable to parameter of type 'number'.",
                ),
                (
                    2322,
                    bad_return_site(&parsed),
                    ["number", "string"],
                    "Type 'number' is not assignable to type 'string'.",
                ),
            ];
            assert_eq!(diagnostics.len(), expected.len(), "{diagnostics:?}");
            for (diagnostic, (code, site, arguments, message)) in diagnostics.iter().zip(expected) {
                assert_eq!(diagnostic.diagnostic.code(), code);
                assert_eq!(diagnostic.node, Some(site));
                assert_eq!(
                    diagnostic.diagnostic.arguments,
                    arguments.map(str::to_owned)
                );
                assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
                assert!(diagnostic.diagnostic.details.is_empty());
                assert_eq!(diagnostic.range_override, None);
                assert!(diagnostic.related_information.is_empty());
            }
        } else {
            assert!(diagnostics.is_empty(), "{diagnostics:?}");
        }
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let unknown = context.store().intrinsic_bootstrap().unwrap().unknown_type;
        let field = owner(
            &context,
            named(&parsed, SyntaxKind::PropertyDeclaration, "value").0,
        );
        assert_eq!(
            context.store().symbol(field).unwrap().parent(),
            Some(owner(&context, class))
        );
        let field_type = context.get_class_query_member_type(field).unwrap();
        let TypeData::Union(union) = context.store().type_payload(field_type).unwrap().data()
        else {
            panic!("flow narrowing must not replace the declared field union");
        };
        let mut members = vec![number, string];
        members.sort_unstable();
        assert_eq!(union.union.types, members);
        let predicate = predicate_signature(&mut context, &parsed, "isNumber", unknown);
        let number_calls = calls(&parsed, "isNumber");
        assert_eq!(number_calls.len(), if invalid { 1 } else { 2 });
        for (call, callee, _) in &number_calls {
            assert_eq!(context.get_type_at_location(*callee), Ok(predicate.0));
            assert_eq!(
                context
                    .store()
                    .signature_links(*call)
                    .unwrap()
                    .resolved_signature
                    .signature(),
                Some(predicate.1)
            );
        }
        let positive =
            invalid.then(|| predicate_signature(&mut context, &parsed, "isPositive", number));
        if !invalid {
            for (name, expected) in [
                ("numberValue", number),
                ("stringValue", string),
                ("negatedString", string),
                ("negatedNumber", number),
            ] {
                let symbol = owner(
                    &context,
                    named(&parsed, SyntaxKind::VariableDeclaration, name).0,
                );
                assert_eq!(
                    context
                        .store()
                        .value_symbol_links(symbol)
                        .unwrap()
                        .resolved_type,
                    Some(expected)
                );
            }
        }
        let warm = snapshot(&context, &parsed);
        for _ in 0..2 {
            assert_eq!(
                predicate_signature(&mut context, &parsed, "isNumber", unknown),
                predicate
            );
            if let Some(expected) = positive {
                assert_eq!(
                    predicate_signature(&mut context, &parsed, "isPositive", number),
                    expected
                );
            }
            assert_eq!(context.get_class_query_member_type(field), Ok(field_type));
            context.check_source_file(FILE).unwrap();
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(snapshot(&context, &parsed), warm);
            assert!(context.store().type_resolution_is_empty());
        }
    }
}

#[test]
fn class_call_predicates_narrow_both_property_branches_and_negation() {
    check(BRANCHES, false);
}

#[test]
fn class_call_predicates_keep_native_argument_and_return_errors() {
    check(ERRORS, true);
}
