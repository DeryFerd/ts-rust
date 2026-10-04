//! Port-only tests of `textDocument/selectionRange` (Go
//! ls/selectionranges.go) on text whose port form is longer than its Go
//! bytes (see `scanner_util::GO_STRING_MARKER`). Each expected range is Go
//! N's answer.

use ts_goport::lsp::lsproto;
use ts_goport::project;
use ts_goport::scanner_util::go_string_from_bytes;

use super::projecttestutil::{self, files};
use super::util::*;

/// The ranges of `selection`, innermost first, as (line, character) pairs.
fn chain(selection: &lsproto::SelectionRange) -> Vec<((u32, u32), (u32, u32))> {
    let mut out = Vec::new();
    let mut next = Some(selection);
    while let Some(s) = next {
        let r = &s.range;
        out.push((
            (r.start.line, r.start.character),
            (r.end.line, r.end.character),
        ));
        next = s.parent.as_deref();
    }
    out
}

child_test! {
    // followups12 skeptic problem 4: the inner stop of an unterminated
    // template literal ends at Go `end-1` (selectionranges.go:358), one Go
    // byte before the literal's end. The literal ends after a real U+FDD0,
    // 3 Go bytes and 6 port bytes, so `end - 1` on port offsets ended 3
    // characters later, at (0,17), past the line end (0,15).
    fn inner_stop_of_a_literal_ends_one_go_byte_back() {
        const FILE: &str = "/home/projects/p/a.js";
        // The port form of the Go text: the real U+FDD0 is M + M.
        let text = &go_string_from_bytes("/** @type {`\u{FDD0}yz".as_bytes().to_vec());
        // A UTF-16 client, as VS Code is (the test default is UTF-8).
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
        let ctx = bg();
        let file_uri = uri("file:///home/projects/p/a.js");
        session.did_open_file(&ctx, &file_uri, 1, text, &lsproto::LanguageKind::JAVA_SCRIPT);
        let language_service = session
            .get_language_service(&ctx, &file_uri)
            .unwrap_or_else(|err| panic!("{}", err.error()));
        let response = language_service
            .provide_selection_ranges(
                &ctx,
                &lsproto::SelectionRangeParams {
                    text_document: lsproto::TextDocumentIdentifier { uri: file_uri },
                    positions: vec![lsproto::Position {
                        line: 0,
                        character: 12,
                    }],
                    ..Default::default()
                },
            )
            .unwrap_or_else(|err| panic!("ProvideSelectionRanges: {}", err.error()));
        let ranges = response.selection_ranges.expect("selection ranges");
        assert_eq!(
            chain(&ranges[0]),
            [
                ((0, 12), (0, 14)),
                ((0, 11), (0, 13)),
                ((0, 4), (0, 13)),
                ((0, 0), (0, 15)),
            ]
        );
        session.close();
    }
}
