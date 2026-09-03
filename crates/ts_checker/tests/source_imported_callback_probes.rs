use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SymbolFlags,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, SignatureId, TypeData, TypeId,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const CONSUMER: FileId = FileId::new(203_200);
const PROVIDER: FileId = FileId::new(203_201);

fn nodes(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut found = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == kind)
                .then_some((record.range.start, NodeRef::new(parsed.arena.id(), file, id)))
        })
        .collect::<Vec<_>>();
    found.sort_by_key(|(start, _)| *start);
    found.into_iter().map(|(_, node)| node).collect()
}

fn context<'arena>(
    consumer: &'arena ParseResult,
    provider: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (CONSUMER, consumer, "\"/project/consumer.ts\""),
        (PROVIDER, provider, "\"/project/target.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, name) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(name),
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
    let imports = nodes(consumer, CONSUMER, SyntaxKind::ImportDeclaration);
    let [import] = imports.as_slice() else {
        panic!("expected one import");
    };
    let NodeData::ImportDeclaration(import) = &consumer.arena.get(import.node).unwrap().data else {
        unreachable!()
    };
    let module = NodeRef::new(consumer.arena.id(), CONSUMER, import.module_specifier);
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .iter()
            .map(|(file, parsed, _)| (*file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions::default(),
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

fn signature(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

fn callable_signature(checker: &CanonicalCheckerContext<'_>, type_: TypeId) -> SignatureId {
    let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data() else {
        panic!("expected a callable object");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    let [signature] = object.structured.signatures.as_deref().unwrap() else {
        panic!("expected one call signature");
    };
    *signature
}

#[test]
fn cold_imported_callback_keeps_real_types_native_error_and_replay() {
    let provider = parse_source_file(
        "export function run(callback: () => number): number { return 1; }",
    );
    let consumer = parse_source_file(
        "import { run } from './target'; const accepted: number = run(() => 1); const rejected: string = run(() => 2);",
    );
    let mut checker = context(&consumer, &provider);
    let bindings = nodes(&consumer, CONSUMER, SyntaxKind::ImportSpecifier);
    let [binding] = bindings.as_slice() else {
        panic!("expected one imported binding");
    };
    let alias = checker.file(CONSUMER).unwrap().1.symbol(*binding).unwrap();
    assert_eq!(
        checker.store().symbol(alias).unwrap().flags(),
        SymbolFlags::ALIAS,
    );
    assert!(checker.store().alias_symbol_links(alias).is_none());
    assert!(
        checker
            .store()
            .value_symbol_links(alias)
            .and_then(|links| links.resolved_type)
            .is_none(),
    );

    let calls: [NodeRef; 2] = nodes(&consumer, CONSUMER, SyntaxKind::CallExpression)
        .try_into()
        .unwrap();
    let arrows: [NodeRef; 2] = nodes(&consumer, CONSUMER, SyntaxKind::ArrowFunction)
        .try_into()
        .unwrap();
    let functions = nodes(&provider, PROVIDER, SyntaxKind::FunctionDeclaration);
    let [function] = functions.as_slice() else {
        panic!("expected the exported run function");
    };
    let callback_types = nodes(&provider, PROVIDER, SyntaxKind::FunctionType);
    let [callback_type] = callback_types.as_slice() else {
        panic!("expected the written callback type");
    };
    let rejected = consumer
        .arena
        .iter()
        .find_map(|(id, record)| match &record.data {
            NodeData::Identifier(name) if name.text == "rejected" => {
                Some(NodeRef::new(consumer.arena.id(), CONSUMER, id))
            }
            _ => None,
        })
        .unwrap();

    checker.check_source_file(CONSUMER).unwrap();
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    let mut baseline = None;
    for pass in 0..3 {
        if pass != 0 {
            checker.recheck_source_file(CONSUMER).unwrap();
        }
        let alias_links = checker.store().alias_symbol_links(alias).unwrap().clone();
        let AliasTargetState::Resolved(target) = alias_links.alias_target else {
            panic!("the real import must resolve");
        };
        assert_eq!(alias_links.immediate_target, Some(target));
        assert!(alias_links.type_only_declaration.is_none());
        let owner = checker.store().symbol(target).unwrap();
        assert_eq!(owner.flags(), SymbolFlags::FUNCTION);
        assert_eq!(owner.declarations(), Some(&[*function][..]));
        assert_eq!(owner.value_declaration(), Some(*function));

        let selected = calls.map(|call| signature(&checker, call));
        assert_eq!(selected[0], selected[1]);
        let imported = checker
            .store()
            .value_symbol_links(alias)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(callable_signature(&checker, imported), selected[0]);
        assert_eq!(
            checker
                .store()
                .value_symbol_links(target)
                .unwrap()
                .resolved_type,
            Some(imported),
        );
        let run = checker.store().signature(selected[0]).unwrap();
        assert_eq!(run.declaration(), Some(*function));
        assert_eq!(run.resolved_return_type(), Some(number));
        let [parameter] = run.parameters() else {
            panic!("run must retain its callback parameter");
        };
        let expected = checker
            .store()
            .value_symbol_links(*parameter)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let expected_signature = callable_signature(&checker, expected);
        let expected_record = checker.store().signature(expected_signature).unwrap();
        assert_eq!(expected_record.declaration(), Some(*callback_type));
        assert!(expected_record.parameters().is_empty());
        assert_eq!(expected_record.resolved_return_type(), Some(number));

        let arrow_signatures = arrows.map(|arrow| signature(&checker, arrow));
        assert_ne!(arrow_signatures[0], arrow_signatures[1]);
        for (arrow, source_signature) in arrows.into_iter().zip(arrow_signatures) {
            let type_ = checker.get_type_at_location(arrow).unwrap();
            assert_eq!(callable_signature(&checker, type_), source_signature);
            assert_ne!(source_signature, expected_signature);
            let record = checker.store().signature(source_signature).unwrap();
            assert_eq!(record.declaration(), Some(arrow));
            assert!(record.parameters().is_empty());
            assert_eq!(record.resolved_return_type(), Some(number));
        }
        for call in calls {
            assert_eq!(checker.get_type_at_location(call).unwrap(), number);
        }
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("only the number-to-string assignment must fail");
        };
        assert_eq!(diagnostic.node, Some(rejected));
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.diagnostic.category(), Category::Error);
        assert_eq!(diagnostic.diagnostic.arguments, ["number", "string"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'.",
        );
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());

        let store = checker.store();
        let tracked = [
            calls[0],
            calls[1],
            arrows[0],
            arrows[1],
            *function,
            *callback_type,
        ];
        let state = (
            (
                store.type_len(),
                store.signature_len(),
                store.mapper_len(),
                store.symbol_len(),
            ),
            tracked.map(|node| {
                (
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            }),
            [alias, target].map(|symbol| store.value_symbol_links(symbol).cloned()),
            alias_links,
            (selected, arrow_signatures, expected, expected_signature),
            checker.diagnostics().clone(),
        );
        if let Some(previous) = &baseline {
            assert_eq!(&state, previous);
        } else {
            baseline = Some(state);
        }
    }
}
