//! Port of internal/api/proto_test.go.

use super::Subtests;
use ts_goport::api::{DocumentIdentifier, new_diagnostic_response};
use ts_goport::ast::{TextRange, new_diagnostic, source_file_get_position_map};
use ts_goport::diag;
use ts_goport::flags::ScriptKind;
use ts_goport::frontend::json::json_unmarshal;
use ts_goport::frontend::parser::{SourceFileParseOptions, parse_source_file};

// Go: api/proto_test.go:16 TestDocumentIdentifierUnmarshalJSON
#[test]
fn test_document_identifier_unmarshal_json() {
    struct Test {
        name: &'static str,
        input: &'static str,
        file_name: &'static str,
        uri: &'static str,
        err: &'static str,
    }
    let tests = [
        Test {
            name: "plain string",
            input: r#""foo.ts""#,
            file_name: "foo.ts",
            uri: "",
            err: "",
        },
        Test {
            name: "uri object",
            input: r#"{"uri":"file:///foo.ts"}"#,
            file_name: "",
            uri: "file:///foo.ts",
            err: "",
        },
        Test {
            name: "uri object with unknown fields",
            input: r#"{"uri":"file:///foo.ts","extra":true}"#,
            file_name: "",
            uri: "file:///foo.ts",
            err: "",
        },
        Test {
            name: "empty object",
            input: "{}",
            file_name: "",
            uri: "",
            err: "",
        },
        Test {
            name: "invalid type",
            input: "42",
            file_name: "",
            uri: "",
            err: "expected string or object, got number",
        },
    ];

    let mut t = Subtests::new("TestDocumentIdentifierUnmarshalJSON");
    for tt in &tests {
        t.run(tt.name, || {
            let mut d = DocumentIdentifier::default();
            let err = json_unmarshal(tt.input.as_bytes(), &mut d, &[]);
            if !tt.err.is_empty() {
                // Go: assert.ErrorContains(t, err, tt.err)
                match err {
                    Ok(()) => {
                        return Err(format!(
                            "expected an error containing {:?}, got nil",
                            tt.err
                        ));
                    }
                    Err(err) if !err.message.contains(tt.err) => {
                        return Err(format!(
                            "expected error {:?} to contain {:?}",
                            err.message, tt.err
                        ));
                    }
                    Err(_) => return Ok(()),
                }
            }
            if let Err(err) = err {
                return Err(format!("assertion failed: error is not nil: {err}"));
            }
            assert_eq!(d.file_name, tt.file_name);
            assert_eq!(d.uri.0, tt.uri);
            Ok(())
        });
    }
    t.finish();
}

// Go: api/proto_test.go:67 TestNewDiagnosticResponseUsesUTF16Offsets
#[test]
fn test_new_diagnostic_response_uses_utf16_offsets() {
    let text = "const 💩 = 1;";
    let file = parse_source_file(
        &SourceFileParseOptions {
            file_name: "/unicode.ts".to_string(),
            ..Default::default()
        },
        text,
        ScriptKind::TS,
    )
    .root;
    // Go `strings.Index` is -1 when the text has no "=".
    let pos = text.find('=').map_or(-1, |i| i as i32);
    assert!(pos > 0);
    let end = pos + "=".len() as i32;

    let diag = new_diagnostic(
        file,
        TextRange::new(pos, end),
        diag::Expression_expected,
        Vec::new(),
    );
    let resp = new_diagnostic_response(&diag);

    assert_eq!(resp.pos, 9);
    assert_eq!(resp.end, 10);
    assert_eq!(
        resp.pos,
        source_file_get_position_map(file).utf8_to_utf16(pos)
    );
    assert_eq!(
        resp.end,
        source_file_get_position_map(file).utf8_to_utf16(end)
    );
}
