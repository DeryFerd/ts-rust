//! Port-only tests of the string literal ranges of `textDocument/references`
//! and `textDocument/documentHighlight` (Go `getRangeOfNode`,
//! ls/findallreferences.go:335). Go cuts an unterminated JSDoc comment at
//! the end of the file 2 bytes early (parser/jsdoc.go:163), so a literal in
//! it can end inside the file's last char. Each expected range is Go N's
//! answer (tsgo-oracle-673a5f17d713, a UTF-16 client).

use ts_goport::lsp::lsproto;
use ts_goport::project;
use ts_goport::scanner_util::go_string_from_bytes;

use super::projecttestutil::{self, files};
use super::util::*;

type Span = ((u32, u32), (u32, u32));

fn span(range: &lsproto::Range) -> Span {
    (
        (range.start.line, range.start.character),
        (range.end.line, range.end.character),
    )
}

/// Opens `text` as the only file of a JS project and checks that
/// references and documentHighlight at each of `chars` on line 0 give
/// the one range `want` in that file.
fn check_literal_range(text: &str, chars: std::ops::RangeInclusive<u32>, want: Span) {
    const FILE: &str = "/home/projects/p/a.js";
    let (session, _) = projecttestutil::setup_with_options(
        files(&[
            (
                "/home/projects/p/tsconfig.json",
                r#"{"compilerOptions":{"allowJs":true,"checkJs":true}}"#,
            ),
            (FILE, text),
        ]),
        project::SessionOptions {
            position_encoding: lsproto::PositionEncodingKind::UTF16,
            ..projecttestutil::default_session_options()
        },
    );
    let ctx = projecttestutil::with_request_id(&bg());
    let file_uri = uri("file:///home/projects/p/a.js");
    session.did_open_file(
        &ctx,
        &file_uri,
        1,
        text,
        &lsproto::LanguageKind::JAVA_SCRIPT,
    );
    let language_service = session
        .get_language_service(&ctx, &file_uri)
        .unwrap_or_else(|err| panic!("{}", err.error()));
    for character in chars {
        let position = lsproto::Position { line: 0, character };
        let references = language_service
            .provide_references(
                &ctx,
                &lsproto::ReferenceParams {
                    text_document: lsproto::TextDocumentIdentifier {
                        uri: file_uri.clone(),
                    },
                    position,
                    context: Some(lsproto::ReferenceContext {
                        include_declaration: true,
                    }),
                    ..Default::default()
                },
                None,
            )
            .unwrap_or_else(|err| panic!("ProvideReferences at {character}: {}", err.error()))
            .locations
            .expect("locations");
        let got: Vec<_> = references
            .iter()
            .map(|location| (location.uri.0.clone(), span(&location.range)))
            .collect();
        assert_eq!(
            got,
            [(file_uri.0.clone(), want)],
            "references at {character}"
        );
        let highlights = language_service
            .provide_document_highlights(&ctx, &file_uri, position)
            .unwrap_or_else(|err| {
                panic!("ProvideDocumentHighlights at {character}: {}", err.error())
            })
            .document_highlights
            .expect("document highlights");
        let got: Vec<_> = highlights.iter().map(|h| span(&h.range)).collect();
        assert_eq!(got, [want], "documentHighlight at {character}");
    }
    session.close();
}

child_test! {
    // R166 reviewer STOP: the literal `"ab` + the first byte of 日 ends
    // inside 日 (bytes 17..20), at byte 18. Go's range is bytes 15 to 17;
    // the port sliced the text at byte 18 and panicked.
    fn typedef_literal_that_ends_inside_a_char() {
        check_literal_range("/** @typedef {\"ab日", 14..=17, ((0, 15), (0, 17)));
    }
}

child_test! {
    // R166 reviewer STOP: an import type path that ends inside 日 (bytes
    // 21..24), at byte 22. Go's range is bytes 19 to 21.
    fn import_type_path_that_ends_inside_a_char() {
        check_literal_range("/** @type {import(\"ab日", 18..=21, ((0, 19), (0, 21)));
    }
}

child_test! {
    // The literal `"ab` + the first 2 bytes of a real U+FDD0 (bytes
    // 17..20) ends at byte 19. The port form holds the U+FDD0 as two
    // marker chars (see `scanner_util::GO_STRING_MARKER`), so the port
    // end is inside the first one. Go's range is bytes 15 to 18. Its end
    // is 1 byte into the U+FDD0, and Go counts that byte as 1 UTF-16
    // unit, so the range is (0,15)-(0,18).
    fn literal_that_ends_inside_a_marker_unit() {
        let text = go_string_from_bytes("/** @typedef {\"ab\u{FDD0}x".as_bytes().to_vec());
        check_literal_range(&text, 14..=17, ((0, 15), (0, 18)));
    }
}
