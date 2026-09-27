//! Ports of internal/scanner/scanner_test.go and
//! internal/parser/parser_test.go (TestJSDocImportTypeParentChain; the Go
//! benchmark and fuzz target are not ported).

use super::childprog::in_child;
use super::leak;
use ts_goport::ast::{get_reparsed_node_for_node, get_source_file_of_node};
use ts_goport::frontend::parser::{SourceFileParseOptions, parse_source_file};
use ts_goport::frontend::scanner::new_scanner;
use ts_goport::frontend::tspath::Path;
use ts_goport::prelude::*;
use ts_goport::program::{note_parsed_source_file, publish_parsed_files};

// Go: scanner/scanner_test.go:11 TestScanStringPreservesLoneSurrogates
// PORT: Go strings hold lone surrogates as WTF-8 bytes. The port keeps them
// in its Go string form (`scanner_util::GO_STRING_MARKER`), which
// `encode_js_string_rune` also writes.
#[test]
fn test_scan_string_preserves_lone_surrogates() {
    let mut s = new_scanner();
    s.set_text(r#""🦀퟿\ud800\ud801🦀""#);
    assert_eq!(s.scan(), SyntaxKind::StringLiteral);
    let expected = "🦀".to_string()
        + &encode_js_string_rune(0xD7FF)
        + &encode_js_string_rune(0xD800)
        + &encode_js_string_rune(0xD801)
        + "🦀";
    assert_eq!(s.token_value(), expected);
}

// Go: parser/parser_test.go:164 TestJSDocImportTypeParentChain
// PORT: `GetSourceFileOfNode` reads the Go file data of the file, which
// exists once its node store is published. Publishing is process-wide, so
// the test runs in a child process of its own.
#[test]
fn test_js_doc_import_type_parent_chain() {
    in_child(
        module_path!(),
        "test_js_doc_import_type_parent_chain",
        js_doc_import_type_parent_chain,
    );
}

fn js_doc_import_type_parent_chain() {
    let source_text = r#"test("", async function () {
  ;(/** @type {typeof import("a")} */ ({}))
})

test("", async function () {
  ;(/** @type {typeof import("a")} */ a)
})

test("", async function () {
  (/** @type {typeof import("a")} */ ({}))
  ;(/** @type {typeof import("a")} */ ({}))
})

test("", async function () {
  (/** @type {typeof import("a")} */ a)
  ;(/** @type {typeof import("a")} */ a)
})

test("", async function () {
  (/** @type {typeof import("a")} */ ({}))
  ;(/** @type {typeof import("a")} */ ({}))
})
"#;
    let opts = SourceFileParseOptions {
        file_name: "/index.js".to_string(),
        path: Path("/index.js".to_string()),
        ..Default::default()
    };

    let file = Rc::new(parse_source_file(&opts, leak(source_text), ScriptKind::JS));
    note_parsed_source_file(&file);
    publish_parsed_files("/");

    let mut errors = Vec::new();
    for i in 1..file.reparsed_clones.len() {
        let (a, b) = (file.reparsed_clones[i - 1], file.reparsed_clones[i]);
        if a.pos() == b.pos() && a.end() == b.end() && a.kind() == b.kind() {
            errors.push(format!(
                "duplicate ReparsedClones at [{}] and [{i}]: {:?} pos={} end={}",
                i - 1,
                a.kind(),
                a.pos(),
                a.end()
            ));
        }
    }
    for &imp in &file.imports {
        let reparsed = get_reparsed_node_for_node(imp);
        if get_source_file_of_node(reparsed).is_nil() {
            errors.push(format!(
                "reparsed import at pos={} has broken parent chain",
                imp.pos()
            ));
        }
    }
    assert!(errors.is_empty(), "{}", errors.join("\n"));
}
