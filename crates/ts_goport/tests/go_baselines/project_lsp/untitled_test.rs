//! Port of Go `internal/project/untitled_test.go`.

use ts_goport::ls::lsconv;
use ts_goport::lsp::lsproto;

use super::projecttestutil::{self, TEST_TYPINGS_LOCATION, files};
use super::util::*;

const TEST_CONTENT: &str = "let x = 42;\n\nx\n\nx++;";

/// Go `languageService.ProvideReferences(ctx, &lsproto.ReferenceParams{...}, nil)`
/// at line 2, character 0 with IncludeDeclaration, as `*resp.Locations`.
fn references_at_line_2(
    language_service: &ts_goport::ls::LanguageService,
    ctx: &ts_goport::gostd::Context,
    u: &str,
) -> Vec<lsproto::Location> {
    let ref_params = lsproto::ReferenceParams {
        text_document: lsproto::TextDocumentIdentifier { uri: uri(u) },
        position: lsproto::Position {
            line: 2,
            character: 0,
        }, // Line 3, character 1 (0-indexed)
        context: Some(lsproto::ReferenceContext {
            include_declaration: true,
        }),
        ..Default::default()
    };
    let resp = language_service
        .provide_references(ctx, &ref_params, None)
        .unwrap_or_else(|err| panic!("ProvideReferences: {}", err.error()));
    resp.locations.expect("resp.Locations")
}

child_test! {
    // Go: untitled_test.go:15 TestUntitledReferences
    fn untitled_references() {
        // First test the URI conversion functions to understand the issue
        let untitled_uri = uri("untitled:Untitled-2");
        let converted_file_name = untitled_uri.file_name();

        let back_to_uri = lsconv::file_name_to_document_uri(&converted_file_name);
        assert_eq!(
            back_to_uri.0, untitled_uri.0,
            "Round-trip conversion failed: '{}' -> '{converted_file_name}' -> '{}'",
            untitled_uri.0, back_to_uri.0
        );

        let (session, _) = projecttestutil::setup(files(&[("/Untitled-2.ts", TEST_CONTENT)]));

        let ctx = projecttestutil::with_request_id(&bg());
        session.did_open_file(
            &ctx,
            &uri("file:///Untitled-2.ts"),
            1,
            TEST_CONTENT,
            &lsproto::LanguageKind::TYPE_SCRIPT,
        );

        // Get language service
        let language_service = session
            .get_language_service(&ctx, &uri("file:///Untitled-2.ts"))
            .unwrap_or_else(|err| panic!("{}", err.error()));

        // Test the filename that the source file reports
        let program = language_service.get_program();
        assert!(program.get_source_file("/Untitled-2.ts").is_some());

        // Call ProvideReferences using the LSP method
        let refs = references_at_line_2(&language_service, &ctx, "file:///Untitled-2.ts");

        // We expect to find 3 references
        assert!(refs.len() == 3, "Expected 3 references, got {}", refs.len());

        // Also test definition using ProvideDefinition
        let _definition = language_service
            .provide_definition(
                &ctx,
                &uri("file:///Untitled-2.ts"),
                lsproto::Position {
                    line: 2,
                    character: 0,
                },
            )
            .unwrap_or_else(|err| panic!("ProvideDefinition: {}", err.error()));
    }
}

child_test! {
    // Go: untitled_test.go:100 TestUntitledFileInInferredProject
    fn untitled_file_in_inferred_project() {
        let (session, _) = projecttestutil::setup(files(&[]));

        let ctx = projecttestutil::with_request_id(&bg());

        // Open untitled files - these should create an inferred project
        session.did_open_file(&ctx, &uri("untitled:Untitled-1"), 1, "x\n\n", &lsproto::LanguageKind::TYPE_SCRIPT);
        session.did_open_file(&ctx, &uri("untitled:Untitled-2"), 1, TEST_CONTENT, &lsproto::LanguageKind::TYPE_SCRIPT);

        // Should have an inferred project
        assert!(has_inferred_project(&session));

        // Get language service for the untitled file
        let language_service = session
            .get_language_service(&ctx, &uri("untitled:Untitled-2"))
            .unwrap_or_else(|err| panic!("{}", err.error()));

        let program = language_service.get_program();
        let untitled_file_name = uri("untitled:Untitled-2").file_name();
        assert!(has_file(program, &untitled_file_name));
        assert_eq!(text(program, &untitled_file_name), TEST_CONTENT);

        // Test references on 'x' at position 13 (line 3, after "let x = 42;\n\n")
        let refs = references_at_line_2(&language_service, &ctx, "untitled:Untitled-2");
        for r in &refs {
            // All URIs should be untitled: URIs, not file: URIs
            assert!(r.uri.0.starts_with("untitled:"), "Expected untitled: URI, got {}", r.uri.0);
        }

        // We expect to find 4 references
        assert!(refs.len() == 4, "Expected 4 references, got {}", refs.len());
    }
}

child_test! {
    // Go: untitled_test.go:162 TestImportsInUntitled
    fn imports_in_untitled() {
        let typings = format!("{TEST_TYPINGS_LOCATION}/node_modules/@types/somelib/index.d.ts");
        // Make sure typings directory exists so it would actually try to fetch typings from this location
        let (session, _) = projecttestutil::setup(files(&[(typings.as_str(), "export const x: number;")]));
        let content = "import \"https://deno.land/std@0.208.0/path/mod.ts\"\n\t\timport  \"./relative\"\n";
        open(&session, "untitled:Untitled-1", content);

        // 2) Wait for ATA/background tasks to finish, then get a language service for the first file
        session.wait_for_background_tasks();
        let _ = language_service(&session, "untitled:Untitled-1");
    }
}
