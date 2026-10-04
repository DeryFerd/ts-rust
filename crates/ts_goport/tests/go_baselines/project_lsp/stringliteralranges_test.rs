//! Port-only tests of the string literal ranges of `textDocument/references`
//! and `textDocument/documentHighlight` (Go `getRangeOfNode`,
//! ls/findallreferences.go:335). Go cuts an unterminated JSDoc comment at
//! the end of the file 2 bytes early (parser/jsdoc.go:163), so a literal in
//! it can end inside the file's last char. Also prepareRename spans,
//! module name completions and file rename edits of unterminated literals
//! whose port form is longer than their Go bytes (see
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

/// The labels of the completion items at each of `chars` on line 0 of
/// `file`, which must be the same at each.
fn completion_labels(
    entries: &[(&str, &str)],
    open: &str,
    file: &str,
    chars: std::ops::RangeInclusive<u32>,
) -> Vec<String> {
    let (session, language_service, file_uri) = session_for(entries, open, file);
    let ctx = projecttestutil::with_request_id(&bg());
    let mut all: Option<Vec<String>> = None;
    for character in chars {
        let response = language_service
            .provide_completion(
                &ctx,
                &file_uri,
                lsproto::Position { line: 0, character },
                None,
            )
            .unwrap_or_else(|err| panic!("ProvideCompletion at {character}: {}", err.error()));
        let items = response
            .list
            .map(|list| list.items)
            .or(response.items)
            .unwrap_or_default();
        let mut labels: Vec<String> = items.into_iter().map(|item| item.label).collect();
        labels.sort();
        if let Some(all) = &all {
            assert_eq!(&labels, all, "completion at {character}");
        }
        all = Some(labels);
    }
    session.close();
    all.unwrap_or_default()
}

/// Ambient modules for the module name completions below.
const AMBIENT_MODULES: &str = "declare module \"ab\u{65E5}\" {}\n\
     declare module \"ab\u{65E5}x\" {}\n\
     declare module \"ab\u{1F600}\" {}\n\
     declare module \"abc\" {}\n";

child_test! {
    // followups19 item 3 (R165 repair skeptic): a closed JS file ends in
    // `require("ab` and the first 2 bytes of 日. Go's fragment is those
    // raw bytes, and `getAmbientModuleCompletions` matches the module
    // names by byte prefix (string_completions.go:909 `strings.HasPrefix`),
    // so "ab日" and "ab日x" are completions (Go N, positions 9 to 14).
    // The port form of a cut byte is a marker unit, and `starts_with` on
    // it found none.
    fn module_name_completion_after_a_cut_char_matches_go_bytes() {
        let text = go_string_from_bytes(b"require(\"ab\xe6\x97".to_vec());
        let labels = completion_labels(
            &[
                (
                    "/home/projects/p/tsconfig.json",
                    r#"{"compilerOptions":{"allowJs":true,"checkJs":true}}"#,
                ),
                ("/home/projects/p/m.d.ts", AMBIENT_MODULES),
                ("/home/projects/p/a.js", &text),
            ],
            "/home/projects/p/m.d.ts",
            "/home/projects/p/a.js",
            9..=14,
        );
        assert_eq!(labels, ["ab\u{65E5}", "ab\u{65E5}x"]);
    }
}

/// The completion items at each of `chars` on line 0 of `file`, one line
/// per item, sorted: label, kind, detail, sortText, the textEdit text and
/// range, and the data name and position.
fn completion_items(
    entries: &[(&str, &str)],
    open: &str,
    file: &str,
    chars: std::ops::RangeInclusive<u32>,
) -> Vec<Vec<String>> {
    let (session, language_service, file_uri) = session_for(entries, open, file);
    let ctx = projecttestutil::with_request_id(&bg());
    let mut all = Vec::new();
    for character in chars {
        let response = language_service
            .provide_completion(
                &ctx,
                &file_uri,
                lsproto::Position { line: 0, character },
                None,
            )
            .unwrap_or_else(|err| panic!("ProvideCompletion at {character}: {}", err.error()));
        let items = response
            .list
            .map(|list| list.items)
            .or(response.items)
            .unwrap_or_default();
        let mut lines: Vec<String> = items
            .into_iter()
            .map(|item| {
                let edit = item
                    .text_edit
                    .and_then(|edit| edit.text_edit)
                    .map(|edit| {
                        let ((a, b), (c, d)) = span(&edit.range);
                        format!("{:?}@{a}:{b}-{c}:{d}", edit.new_text)
                    })
                    .unwrap_or_default();
                let data = item
                    .data
                    .map(|data| format!("{:?}@{}", data.name, data.position))
                    .unwrap_or_default();
                format!(
                    "{:?} kind={} detail={:?} sort={:?} edit={edit} data={data}",
                    item.label,
                    item.kind.map_or(0, |kind| kind.0),
                    item.detail.unwrap_or_default(),
                    item.sort_text.unwrap_or_default(),
                )
            })
            .collect();
        lines.sort();
        all.push(lines);
    }
    session.close();
    all
}

/// The path mapping project of the `paths` completions below: `paths` keys
/// that start with "ab日", the files of `ab日` and `ab日y*`.
const PATHS_TSCONFIG: &str = r#"{"compilerOptions":{"allowJs":true,"checkJs":true,
    "module":"esnext","moduleResolution":"bundler",
    "paths":{"ab日":["./src/x.ts"],"ab日x/*":["./src/y/*"],"ab日y*":["./src/y/*"]}}}"#;

child_test! {
    // followups19 item 3: the `paths` keys match by Go byte prefix too
    // (string_completions.go:1515 `justPathMappingName` and :1546). Go N
    // gives "ab日" (a file), "ab日x" (the directory of `ab日x/*`) and
    // "ab日yz" (`ab日y*` with the files of src/y) at positions 9 to 14.
    // followups22 (R169 reviewer): each whole item is Go N's (lspcases.py
    // paths-cjkcut --width 5000, saved in the followups22 lane): the range
    // (0,9)-(0,13) counts each cut byte as 1 UTF-16 unit, and the data
    // position is the Go byte offset, at most 13 (the file end).
    fn path_mapping_completion_after_a_cut_char_matches_go_bytes() {
        let text = go_string_from_bytes(b"require(\"ab\xe6\x97".to_vec());
        let items = completion_items(
            &[
                ("/home/projects/p/tsconfig.json", PATHS_TSCONFIG),
                ("/home/projects/p/src/x.ts", "export {};\n"),
                ("/home/projects/p/src/y/z.ts", "export {};\n"),
                ("/home/projects/p/a.js", &text),
            ],
            "/home/projects/p/src/x.ts",
            "/home/projects/p/a.js",
            9..=14,
        );
        let want: Vec<Vec<String>> = (9..=14)
            .map(|character: i32| {
                let position = character.min(13);
                vec![
                    format!(
                        "\"ab日\" kind=17 detail=\"ab日.ts\" sort=\"11\" edit=\"ab日\"@0:9-0:13 data=\"ab日\"@{position}"
                    ),
                    format!(
                        "\"ab日x\" kind=19 detail=\"ab日x\" sort=\"11\" edit=\"ab日x\"@0:9-0:13 data=\"ab日x\"@{position}"
                    ),
                    format!(
                        "\"ab日yz\" kind=17 detail=\"ab日yz.ts\" sort=\"11\" edit=\"ab日yz\"@0:9-0:13 data=\"ab日yz\"@{position}"
                    ),
                ]
            })
            .collect();
        assert_eq!(items, want);
    }
}

child_test! {
    // followups22 (R169 reviewer): a `paths` key keeps the raw bytes of its
    // tsconfig text, here the first 2 bytes of 日, and the closed file's
    // fragment "ab日" has the whole char. Go compares and cuts Go bytes
    // (string_completions.go:1543 `strings.HasPrefix(fragment,
    // pathPrefix)`, :1575 `fragment[len(pathPrefix):]`), so `ab\xe6\x97*`
    // matches and gives "ab\xe6\x97z" from src/y/z.ts. Go N (lspcases.py
    // paths-rawkey, positions 9 to 12; its JSON writes each raw byte as
    // U+FFFD). Rust `starts_with` on the port forms found no item.
    fn path_mapping_completion_of_a_raw_byte_key_matches_go_bytes() {
        let tsconfig = go_string_from_bytes(
            b"{\"compilerOptions\":{\"allowJs\":true,\"checkJs\":true,\"noLib\":true,\"types\":[],\
              \"module\":\"esnext\",\"moduleResolution\":\"bundler\",\"paths\":{\"ab\xe6\x97*\":[\"./src/y/*\"],\
              \"ab\xe6\x97y*\":[\"./src/y/*\"]}}}"
                .to_vec(),
        );
        let text = go_string_from_bytes(b"require(\"ab\xe6\x97\xa5".to_vec());
        let items = completion_items(
            &[
                ("/home/projects/p/tsconfig.json", &tsconfig),
                ("/home/projects/p/src/y/z.ts", "export {};\n"),
                ("/home/projects/p/a.js", &text),
            ],
            "/home/projects/p/src/y/z.ts",
            "/home/projects/p/a.js",
            9..=12,
        );
        let name = go_string_from_bytes(b"ab\xe6\x97z".to_vec());
        let detail = go_string_from_bytes(b"ab\xe6\x97z.ts".to_vec());
        let want: Vec<Vec<String>> = [9, 10, 11, 14]
            .into_iter()
            .map(|position| {
                vec![format!(
                    "{name:?} kind=17 detail={detail:?} sort=\"11\" edit={name:?}@0:9-0:12 data={name:?}@{position}"
                )]
            })
            .collect();
        assert_eq!(items, want);
    }
}

/// The text edits of a rename of `old` to `new` (Go `GetEditsForFileRename`),
/// one line per edit: the file, the new text and the range.
fn file_rename_edits(entries: &[(&str, &str)], open: &str, old: &str, new: &str) -> Vec<String> {
    let (session, language_service, _) = session_for(entries, open, open);
    let ctx = projecttestutil::with_request_id(&bg());
    let changes = language_service.get_edits_for_file_rename(&ctx, &uri(old), &uri(new));
    let mut lines = Vec::new();
    for change in changes {
        let edit = change.text_document_edit.expect("a text document edit");
        for text_edit in edit.edits {
            let text_edit = text_edit.text_edit.expect("a text edit");
            let ((a, b), (c, d)) = span(&text_edit.range);
            lines.push(format!(
                "{} {:?}@{a}:{b}-{c}:{d}",
                edit.text_document.uri.0, text_edit.new_text
            ));
        }
    }
    session.close();
    lines
}

child_test! {
    // followups22 (R169 reviewer): the edit range of a file rename ends one
    // Go byte before the end of the literal (file_rename.go:202
    // tryUpdateConfigString and :362 createStringTextRange, `End()-1`). Here
    // both literals are unterminated at the end of their file and end in
    // the raw byte FF, one marker unit: a `paths` key that maps to a.ts,
    // which m.ts imports. Go N (renamecases.py import-paths-ff): the
    // tsconfig.json edit (0,60)-(0,66) and the m.ts edit (0,8)-(0,9), before
    // the byte. `End()-1` on port offsets gave (0,8)-(0,15).
    fn file_rename_of_an_import_that_ends_in_a_raw_byte() {
        let tsconfig = go_string_from_bytes(
            b"{\"compilerOptions\":{\"noLib\":true,\"types\":[],\"paths\":{\"x\xff\":[\"./a.ts\"]}}}"
                .to_vec(),
        );
        let text = go_string_from_bytes(b"import \"x\xff".to_vec());
        let edits = file_rename_edits(
            &[
                ("/home/projects/p/tsconfig.json", &tsconfig),
                ("/home/projects/p/a.ts", "export const a = 1;\n"),
                ("/home/projects/p/m.ts", &text),
            ],
            "/home/projects/p/m.ts",
            "file:///home/projects/p/a.ts",
            "file:///home/projects/p/b.ts",
        );
        assert_eq!(
            edits,
            [
                "file:///home/projects/p/tsconfig.json \"b.ts\"@0:60-0:66",
                "file:///home/projects/p/m.ts \"./b\"@0:8-0:9",
            ]
        );
    }
}

child_test! {
    // followups22: the tsconfig.json side (file_rename.go:202). An
    // unterminated `paths` element at the end of the file ends in the raw
    // byte FF and names the renamed file `a\xff`. Go N
    // (renamecases.py tsconfig-ff-noext): (0,59)-(0,62), before the byte.
    // `End()-1` on port offsets gave (0,59)-(0,63).
    fn file_rename_of_a_tsconfig_string_that_ends_in_a_raw_byte() {
        let tsconfig = go_string_from_bytes(
            b"{\"compilerOptions\":{\"noLib\":true,\"types\":[],\"paths\":{\"x\":[\"./a\xff".to_vec(),
        );
        let edits = file_rename_edits(
            &[
                ("/home/projects/p/tsconfig.json", &tsconfig),
                ("/home/projects/p/m.ts", "export {};\n"),
            ],
            "/home/projects/p/m.ts",
            "file:///home/projects/p/a%FF",
            "file:///home/projects/p/b",
        );
        assert_eq!(
            edits,
            ["file:///home/projects/p/tsconfig.json \"b\"@0:59-0:62"]
        );
    }
}
