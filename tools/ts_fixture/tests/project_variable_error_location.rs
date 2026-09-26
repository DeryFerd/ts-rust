use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, EscapedNameRef, SymbolFlags,
};
use ts_checker::semantic::{SourceCheckError, UnsupportedSourceSyntax, VariableUnsupported};
use ts_compiler::{CanonicalCensusPhase, CanonicalProgramCheckError, Program};
use ts_fixture::project::{ProjectCensusFailure, ProjectCensusLocation};
use ts_options::CompilerOptions;
use ts_vfs::{FileSystem, MemoryFileSystem};

const ROOT: &str = "/census/root.ts";
const DEPENDENCY: &str = "/census/dependency.ts";
const PREFIX: &str = "const prefix = \"\u{1f642}\";\r\nconst observed = ";

fn identifier_not_prior_error(
    program: &Program,
) -> (CanonicalBinder, NodeRef, CanonicalProgramCheckError) {
    let source = program.source_file(DEPENDENCY).unwrap();
    let (id, node) = source
        .parse
        .arena
        .iter()
        .filter(|(_, node)| {
            node.kind == SyntaxKind::Identifier
                && source
                    .source_text
                    .get(node.range.start.get() as usize..node.range.end.get() as usize)
                    == Some("later")
        })
        .min_by_key(|(_, node)| node.range.start.get())
        .unwrap();
    let reference = NodeRef::new(source.parse.arena.id(), source.id, id);
    assert_eq!(node.range.start.get(), u32::try_from(PREFIX.len()).unwrap());
    assert!(program.node(reference).is_some());

    // Construct a reporting input from an actual bound symbol and declaration.
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &source.parse.arena,
            source.parse.source_file,
            source.id,
            CanonicalSourceFileFacts::new(
                EscapedName::source(DEPENDENCY),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&source.parse.arena, source.id)
        .unwrap();
    let (symbol, data) = binder
        .symbol_store()
        .symbols()
        .find(|(_, data)| data.name() == EscapedNameRef::source("later"))
        .unwrap();
    let declaration = data.value_declaration().unwrap();
    assert!(data.flags().contains(SymbolFlags::BLOCK_SCOPED_VARIABLE));
    assert_eq!(data.declarations(), Some([declaration].as_slice()));
    assert_eq!(
        binder.file(source.id).unwrap().symbol(declaration),
        Some(symbol)
    );
    let declared_node = program.node(declaration).unwrap();
    assert_eq!(declared_node.kind, SyntaxKind::VariableDeclaration);
    assert!(node.range.start.get() < declared_node.range.start.get());
    let error = CanonicalProgramCheckError::SourceCheck {
        file_name: ROOT.to_owned(),
        error: SourceCheckError::Unsupported(UnsupportedSourceSyntax::Variable(
            VariableUnsupported::IdentifierNotPrior {
                node: reference,
                symbol,
                declaration,
            },
        )),
    };
    (binder, reference, error)
}

#[test]
fn census_variable_identifier_location_keeps_the_retained_read_and_full_error() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(ROOT, "const root = 1;\n").unwrap();
    fs.write_file(
        DEPENDENCY,
        &format!("{PREFIX}later;\r\nconst later = 1;\r\n"),
    )
    .unwrap();
    let program = Program::try_new_with_canonical_checker(
        &fs,
        "/census",
        &["root.ts".to_owned(), "dependency.ts".to_owned()],
        CompilerOptions {
            no_lib: true,
            no_check: true,
            ..Default::default()
        },
    )
    .unwrap();
    let (_binder, reference, error) = identifier_not_prior_error(&program);
    let source = program.source_file(DEPENDENCY).unwrap();
    let node = program.node(reference).unwrap();
    assert_ne!(PREFIX.len(), PREFIX.chars().count());
    assert_eq!(
        node.range.end.get(),
        u32::try_from(PREFIX.len() + "later".len()).unwrap()
    );
    let failure =
        ProjectCensusFailure::from_error(Some(&program), CanonicalCensusPhase::Source, &error);
    assert_eq!(
        failure,
        ProjectCensusFailure {
            phase: "source".to_owned(),
            class: "unsupported".to_owned(),
            code: "E00.SOURCE_SYNTAX".to_owned(),
            detail: error.to_string(),
            returned_error: format!("{error:?}"),
            reported_file_name: Some(ROOT.to_owned()),
            location: Some(ProjectCensusLocation {
                file_name: DEPENDENCY.to_owned(),
                file_id: source.id.index(),
                syntax_kind: "Identifier".to_owned(),
                start_byte: u32::try_from(PREFIX.len()).unwrap(),
                end_byte: u32::try_from(PREFIX.len() + "later".len()).unwrap(),
            }),
            location_unavailable: None,
        }
    );
}

#[test]
fn census_variable_identifier_location_rejects_foreign_nodes_and_missing_program() {
    let fs = MemoryFileSystem::new(true);
    fs.write_file(ROOT, "const root = 1;\n").unwrap();
    fs.write_file(
        DEPENDENCY,
        &format!("{PREFIX}later;\r\nconst later = 1;\r\n"),
    )
    .unwrap();
    let make = || {
        Program::try_new_with_canonical_checker(
            &fs,
            "/census",
            &["root.ts".to_owned(), "dependency.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                no_check: true,
                ..Default::default()
            },
        )
        .unwrap()
    };
    let retained = make();
    let other = make();
    let (_retained_binder, valid, valid_error) = identifier_not_prior_error(&retained);
    let (_foreign_binder, foreign, foreign_error) = identifier_not_prior_error(&other);
    assert_eq!(valid.file, foreign.file);
    assert!(retained.node(valid).is_some());
    assert!(other.node(foreign).is_some());
    assert!(retained.node(foreign).is_none());
    for (program, error, reason) in [
        (
            Some(&retained),
            &foreign_error,
            "The returned node does not have a valid retained Program range.",
        ),
        (
            None,
            &valid_error,
            "No loaded Program is available to validate a location.",
        ),
    ] {
        let failure =
            ProjectCensusFailure::from_error(program, CanonicalCensusPhase::Source, error);
        assert_eq!(
            failure,
            ProjectCensusFailure {
                phase: "source".to_owned(),
                class: "unsupported".to_owned(),
                code: "E00.SOURCE_SYNTAX".to_owned(),
                detail: error.to_string(),
                returned_error: format!("{error:?}"),
                reported_file_name: Some(ROOT.to_owned()),
                location: None,
                location_unavailable: Some(reason.to_owned()),
            }
        );
    }
}
