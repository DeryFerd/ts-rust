//! Port-only test of an E5c Effect quick fix (`effect::ls::fixables`, lane
//! effectE5c) through the LSP code action path. The 14 E5c fixes run
//! against the Go baselines in `scripts/effect/ls-cases.mjs`; this test keeps
//! one of them in the protected set. `unnecessaryArrowBlock` needs no type
//! information, so the project needs no Effect package.

use super::projecttestutil::{self, files};
use super::util::*;
use ts_goport::lsp::lsproto;

const CONFIG: &str = "/home/projects/p/tsconfig.json";
const MAIN: &str = "/home/projects/p/main.ts";
const MAIN_URI: &str = "file:///home/projects/p/main.ts";
const CONFIG_TEXT: &str =
    r#"{"compilerOptions":{"strict":true,"plugins":[{"name":"@effect/language-service"}]}}"#;

// The block body is 0:42 to 2:1.
const MAIN_TEXT: &str = "export const f = (arg: string) => {\n\treturn arg.trim()\n}\n";

/// TS377084, the code of the `unnecessaryArrowBlock` rule.
const UNNECESSARY_ARROW_BLOCK: i32 = 377084;

fn position(line: u32, character: u32) -> lsproto::Position {
    lsproto::Position { line, character }
}

child_test! {
    // Go `unnecessary_arrow_block.go`: delete the block from its full start
    // (with the space after `=>`) and insert `(<returned expression>)` there,
    // so `=> {...}` becomes `=>(arg.trim())`, as in the Go baseline.
    fn unnecessary_arrow_block_fix_makes_a_concise_body() {
        let (session, _) = projecttestutil::setup(files(&[(CONFIG, CONFIG_TEXT), (MAIN, MAIN_TEXT)]));
        open(&session, MAIN_URI, MAIN_TEXT);
        let service = session
            .get_language_service(&projecttestutil::with_request_id(&bg()), &uri(MAIN_URI))
            .unwrap_or_else(|err| panic!("{}", err.error()));
        let range = lsproto::Range { start: position(0, 34), end: position(2, 1) };
        let diagnostic = lsproto::Diagnostic {
            range,
            code: Some(lsproto::IntegerOrString {
                integer: Some(UNNECESSARY_ARROW_BLOCK),
                string: None,
            }),
            message: lsproto::StringOrMarkupContent {
                string: Some("stand-in".to_string()),
                markup_content: None,
            },
            ..Default::default()
        };
        let response = service
            .provide_code_actions(
                &projecttestutil::with_request_id(&bg()),
                &lsproto::CodeActionParams {
                    text_document: lsproto::TextDocumentIdentifier { uri: uri(MAIN_URI) },
                    range,
                    context: Some(lsproto::CodeActionContext {
                        diagnostics: vec![Some(diagnostic)],
                        only: Some(vec![lsproto::CodeActionKind::QUICK_FIX]),
                        ..Default::default()
                    }),
                    ..Default::default()
                },
            )
            .unwrap_or_else(|err| panic!("{}", err.error()));
        let fixes: Vec<(String, Vec<(lsproto::Range, String)>)> = response
            .command_or_code_action_array
            .unwrap_or_default()
            .into_iter()
            .map(|action| {
                let action = action.code_action.expect("a code action");
                let edits = action
                    .edit
                    .and_then(|edit| edit.changes)
                    .and_then(|mut changes| changes.shift_remove(&uri(MAIN_URI)))
                    .unwrap_or_default()
                    .into_iter()
                    .map(|edit| {
                        let edit = edit.expect("an edit");
                        (edit.range, edit.new_text)
                    })
                    .collect();
                (action.title, edits)
            })
            .collect();
        let titles: Vec<&str> = fixes.iter().map(|(title, _)| title.as_str()).collect();
        assert_eq!(
            titles,
            [
                "Disable unnecessaryArrowBlock for this line",
                "Disable unnecessaryArrowBlock for entire file",
                "Use a concise arrow body",
            ]
        );
        assert_eq!(
            fixes[2].1,
            vec![
                (lsproto::Range { start: position(0, 33), end: position(0, 33) }, "(arg.trim())".to_string()),
                (lsproto::Range { start: position(0, 33), end: position(2, 1) }, String::new()),
            ]
        );
    }
}
