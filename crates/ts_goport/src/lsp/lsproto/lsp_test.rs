//! Port of internal/lsp/lsproto/lsp_test.go.
//!
//! PORT: Go `t.Parallel()` is dropped (cargo runs tests in parallel).

use crate::lsp::lsproto::prelude::*;

// Go: lsp_test.go:10 TestUnmarshalCompletionItem
#[test]
fn test_unmarshal_completion_item() {
    const MESSAGE: &str = r#"{
    "label": "pageXOffset",
    "insertTextFormat": 1,
    "textEdit": {
        "newText": "pageXOffset",
        "insert": {
            "start": {
                "line": 4,
                "character": 0
            },
            "end": {
                "line": 4,
                "character": 4
            }
        },
        "replace": {
            "start": {
                "line": 4,
                "character": 0
            },
            "end": {
                "line": 4,
                "character": 4
            }
        }
    },
    "kind": 6,
    "sortText": "15",
    "commitCharacters": [
        ".",
        ",",
        ";"
    ]
}"#;

    let mut result = CompletionItem::default();
    let err = json_unmarshal(MESSAGE.as_bytes(), &mut result, &[]);
    if let Err(err) = &err {
        panic!("expected no error, got {err}");
    }

    assert_eq!(
        result,
        CompletionItem {
            label: "pageXOffset".to_string(),
            insert_text_format: Some(InsertTextFormat::PLAIN_TEXT),
            text_edit: Some(TextEditOrInsertReplaceEdit {
                insert_replace_edit: Some(InsertReplaceEdit {
                    new_text: "pageXOffset".to_string(),
                    insert: Range {
                        start: Position {
                            line: 4,
                            character: 0,
                        },
                        end: Position {
                            line: 4,
                            character: 4,
                        },
                    },
                    replace: Range {
                        start: Position {
                            line: 4,
                            character: 0,
                        },
                        end: Position {
                            line: 4,
                            character: 4,
                        },
                    },
                }),
                ..Default::default()
            }),
            kind: Some(CompletionItemKind::VARIABLE),
            sort_text: Some("15".to_string()),
            commit_characters: Some(vec![".".to_string(), ",".to_string(), ";".to_string()]),
            ..Default::default()
        }
    );
}
