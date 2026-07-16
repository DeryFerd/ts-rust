use ts_ast::FileId;
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError, UnsupportedSourceSyntax,
    VariableUnsupported,
};
use ts_parser::parse_source_file;

#[test]
fn generic_identity_body_parameter_read_remains_an_explicit_boundary() {
    let parsed = parse_source_file("function identity<T>(value: T): T { return value; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic.ts\""),
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

    assert!(matches!(
        context.check_source_file(file),
        Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Variable(VariableUnsupported::IdentifierNotPrior { .. })
        ))
    ));
    assert!(context.diagnostics().is_empty());
}
