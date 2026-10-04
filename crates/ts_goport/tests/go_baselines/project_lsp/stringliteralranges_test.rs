//! Port-only tests of the string literal ranges of `textDocument/references`
//! and `textDocument/documentHighlight` (Go `getRangeOfNode`,
//! ls/findallreferences.go:335). Go cuts an unterminated JSDoc comment at
//! the end of the file 2 bytes early (parser/jsdoc.go:163), so a literal in
//! it can end inside the file's last char. Also prepareRename spans of
//! unterminated literals whose port form is longer than their Go bytes (see
//! `scanner_util::GO_STRING_MARKER`). Each expected answer is Go N's
//! (tsgo-oracle-673a5f17d713, a UTF-16 client).

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

/// A session on `entries` (a UTF-16 client, as VS Code is) with `open`
/// open, and the language service of `file`, which can stay closed: its
/// text is then the file's raw bytes (see `go_string_from_bytes`).
fn session_for(
    entries: &[(&str, &str)],
    open: &str,
    file: &str,
) -> (
    std::rc::Rc<project::Session>,
    ts_goport::ls::LanguageService,
    lsproto::DocumentUri,
) {
    let (session, _) = projecttestutil::setup_with_options(
        files(entries),
        project::SessionOptions {
            position_encoding: lsproto::PositionEncodingKind::UTF16,
            ..projecttestutil::default_session_options()
        },
    );
    let ctx = projecttestutil::with_request_id(&bg());
    let text = entries
        .iter()
        .find(|(name, _)| *name == open)
        .map(|(_, text)| *text)
        .expect("the open file");
    session.did_open_file(
        &ctx,
        &uri(&format!("file://{open}")),
        1,
        text,
        &lsproto::LanguageKind::TYPE_SCRIPT,
    );
    let file_uri = uri(&format!("file://{file}"));
    let language_service = session
        .get_language_service(&ctx, &file_uri)
        .unwrap_or_else(|err| panic!("{}", err.error()));
    (session, language_service, file_uri)
}

/// Checks that prepareRename (Go `GetRenameInfo`) at each of `chars` on
/// line 0 of `file` gives the trigger span `want`.
fn check_rename_span(
    entries: &[(&str, &str)],
    open: &str,
    file: &str,
    chars: std::ops::RangeInclusive<u32>,
    want: Span,
) {
    let (session, language_service, file_uri) = session_for(entries, open, file);
    let ctx = projecttestutil::with_request_id(&bg());
    for character in chars {
        let info = language_service.get_rename_info(
            &ctx,
            "", /*newName*/
            &file_uri,
            lsproto::Position { line: 0, character },
        );
        assert!(info.can_rename, "prepareRename at {character}");
        assert_eq!(
            span(&info.trigger_span),
            want,
            "prepareRename at {character}"
        );
    }
    session.close();
}

child_test! {
    // followups19 item 2: Go `getRenameInfoSuccess` steps the end of a
    // literal back one Go byte (rename.go:443 `end--`). The literal
    // `"ab` + a real U+FDD0 (3 Go bytes, two marker chars in the port
    // form) ends 2 bytes into the U+FDD0 there, and Go counts each of
    // those bytes as 1 UTF-16 unit: (0,8)-(0,12). `end -= 1` on port
    // offsets gave (0,8)-(0,15).
    fn rename_span_of_a_literal_that_ends_in_a_real_fdd0() {
        let text = go_string_from_bytes("let s: \"ab\u{FDD0}".as_bytes().to_vec());
        check_rename_span(
            &[
                ("/home/projects/p/tsconfig.json", "{}"),
                ("/home/projects/p/a.ts", &text),
            ],
            "/home/projects/p/a.ts",
            "/home/projects/p/a.ts",
            7..=12,
            ((0, 8), (0, 12)),
        );
    }
}

child_test! {
    // followups19 item 2: a closed file whose literal `"ab` ends in the
    // raw byte FF, one marker unit. Go's end is before the byte:
    // (0,8)-(0,10). `end -= 1` on port offsets gave (0,8)-(0,16).
    fn rename_span_of_a_closed_literal_that_ends_in_a_raw_byte() {
        let text = go_string_from_bytes(b"let s: \"ab\xff".to_vec());
        check_rename_span(
            &[
                ("/home/projects/p/tsconfig.json", "{}"),
                ("/home/projects/p/o.ts", "export {};\n"),
                ("/home/projects/p/a.ts", &text),
            ],
            "/home/projects/p/o.ts",
            "/home/projects/p/a.ts",
            7..=12,
            ((0, 8), (0, 10)),
        );
    }
}
