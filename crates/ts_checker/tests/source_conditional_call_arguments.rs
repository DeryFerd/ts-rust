use ts_ast::{FileId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_210);
const SOURCE: &str = concat!(
    "function choose(): boolean { return true; }\n",
    "function take(value: number): number { return value; }\n",
    "declare const input: number | undefined;\n",
    "declare const text: string;\n",
    "const accepted: number = take((input ?? (choose() ? 1 + 2 : 3 * 4)));\n",
    "const rejected: number = take(input ?? (choose() ? text : 5 * 6));\n",
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
                EscapedName::source("\"/project/conditional-call-arguments.ts\""),
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
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn nodes(parsed: &ParseResult, text: &str) -> Vec<NodeRef> {
    let mut found = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let range = record.range;
            (matches!(
                record.kind,
                SyntaxKind::CallExpression
                    | SyntaxKind::BinaryExpression
                    | SyntaxKind::ConditionalExpression
                    | SyntaxKind::ParenthesizedExpression
                    | SyntaxKind::FunctionDeclaration
            ) && &SOURCE[range.start.get() as usize..range.end.get() as usize] == text)
                .then_some((range.start, NodeRef::new(parsed.arena.id(), FILE, id)))
        })
        .collect::<Vec<_>>();
    found.sort_by_key(|(start, _)| *start);
    found.into_iter().map(|(_, node)| node).collect()
}

fn only(parsed: &ParseResult, text: &str) -> NodeRef {
    let found = nodes(parsed, text);
    let [node] = found.as_slice() else {
        panic!("expected one node for {text}");
    };
    *node
}

fn cached_type(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    checker
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, call: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(call)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

#[test]
fn conditional_call_arguments_check_both_branches_and_replay() {
    let parsed = parse_source_file(SOURCE);
    let mut checker = context(&parsed);
    let accepted_call = only(&parsed, "take((input ?? (choose() ? 1 + 2 : 3 * 4)))");
    let rejected_call = only(&parsed, "take(input ?? (choose() ? text : 5 * 6))");
    let rejected_argument = only(&parsed, "input ?? (choose() ? text : 5 * 6)");
    let rejected_conditional = only(&parsed, "choose() ? text : 5 * 6");
    let conditions: [NodeRef; 2] = nodes(&parsed, "choose()").try_into().unwrap();
    let choose = only(&parsed, "function choose(): boolean { return true; }");
    let take = only(&parsed, "function take(value: number): number { return value; }");
    let numeric = [
        "1 + 2",
        "3 * 4",
        "5 * 6",
        "choose() ? 1 + 2 : 3 * 4",
        "(choose() ? 1 + 2 : 3 * 4)",
        "input ?? (choose() ? 1 + 2 : 3 * 4)",
        "(input ?? (choose() ? 1 + 2 : 3 * 4))",
    ]
    .map(|text| only(&parsed, text));
    let tracked = [
        accepted_call,
        rejected_call,
        rejected_argument,
        rejected_conditional,
        conditions[0],
        conditions[1],
    ]
    .into_iter()
    .chain(numeric)
    .collect::<Vec<_>>();

    checker.check_source_file(FILE).unwrap();
    let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
    let (number, string, boolean) = (
        bootstrap.number_type,
        bootstrap.string_type,
        bootstrap.boolean_type,
    );
    let mut baseline = None;
    for pass in 0..3 {
        if pass != 0 {
            checker.recheck_source_file(FILE).unwrap();
        }
        for expression in numeric.into_iter().chain([accepted_call, rejected_call]) {
            assert_eq!(cached_type(&checker, expression), number);
        }
        for condition in conditions {
            assert_eq!(cached_type(&checker, condition), boolean);
        }
        let incompatible = cached_type(&checker, rejected_conditional);
        assert_eq!(cached_type(&checker, rejected_argument), incompatible);
        let TypeData::Union(union) = checker.store().type_payload(incompatible).unwrap().data()
        else {
            panic!("the incompatible branch must remain in the argument type");
        };
        assert_eq!(union.union.types.len(), 2);
        assert!(union.union.types.contains(&number));
        assert!(union.union.types.contains(&string));
        assert_eq!(
            checker.type_to_string(incompatible).unwrap(),
            "string | number",
        );

        let selected = [accepted_call, rejected_call].map(|call| signature(&checker, call));
        assert_eq!(selected[0], selected[1]);
        let target = checker.store().signature(selected[0]).unwrap();
        assert_eq!(target.declaration(), Some(take));
        assert_eq!(target.resolved_return_type(), Some(number));
        let [parameter] = target.parameters() else {
            panic!("take must keep one number parameter");
        };
        assert_eq!(
            checker
                .store()
                .value_symbol_links(*parameter)
                .unwrap()
                .resolved_type,
            Some(number),
        );
        let condition_signatures = conditions.map(|call| signature(&checker, call));
        assert_eq!(condition_signatures[0], condition_signatures[1]);
        let condition_target = checker.store().signature(condition_signatures[0]).unwrap();
        assert_eq!(condition_target.declaration(), Some(choose));
        assert!(condition_target.parameters().is_empty());
        assert_eq!(condition_target.resolved_return_type(), Some(boolean));

        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("expected one incompatible argument error");
        };
        assert_eq!(diagnostic.node, Some(rejected_argument));
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(diagnostic.diagnostic.arguments, ["string | number", "number"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            concat!(
                "Argument of type 'string | number' is not assignable to parameter of type 'number'.\n",
                "  Type 'string' is not assignable to type 'number'.",
            ),
        );
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());

        let store = checker.store();
        let source = store.source_file_links(checker.source_file(FILE).unwrap()).unwrap();
        assert!(source.type_checked);
        let state = (
            (
                store.type_len(),
                store.signature_len(),
                store.mapper_len(),
                store.symbol_len(),
            ),
            tracked
                .iter()
                .map(|&node| {
                    (
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                        store.signature_links(node).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            (selected, condition_signatures, incompatible),
            source.clone(),
            checker.diagnostics().clone(),
        );
        if let Some(previous) = &baseline {
            assert_eq!(&state, previous);
        } else {
            baseline = Some(state);
        }
    }
}
