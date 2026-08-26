use ts_ast::{FileId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions};
use ts_parser::parse_source_file;

#[test]
fn constructor_union_results_use_error_recovery_and_shared_composite_signatures() {
    let parsed = parse_source_file(concat!(
        "class First {} class Second {} ",
        "abstract class Abstract { value!: string; } ",
        "type Concrete = typeof First | typeof Second; ",
        "type Mixed = Concrete | typeof Abstract; ",
        "declare const concrete: Concrete; declare const mixed: Mixed; ",
        "new concrete(); new concrete(); new mixed();",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4_150);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/constructor-union.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions::default(),
    )
    .unwrap();
    let constructions = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                id,
            ))
        })
        .collect::<Vec<_>>();

    context.check_source_file(file).unwrap();

    let signatures = constructions
        .iter()
        .map(|node| {
            context
                .store()
                .signature_links(*node)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(signatures[0], signatures[1]);
    assert_eq!(
        signatures[2],
        context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .unknown_signature,
    );
    for (node, expected) in constructions
        .iter()
        .zip(["First | Second", "First | Second", "any"])
    {
        let type_ = context.get_type_at_location(*node).unwrap();
        assert_eq!(context.type_to_string(type_).unwrap(), expected);
    }
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the mixed constructor union must report one abstract-class error")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2511);
    assert_eq!(diagnostic.node, Some(constructions[2]));
    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );

    context.recheck_source_file(file).unwrap();

    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}
