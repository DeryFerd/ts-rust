//! Port of internal/astnav/tokens_test.go.
//!
//! Baselines: `astnav/<Test>.mapCode.ts.baseline.txt` (Go tokens against
//! TypeScript tokens from Node.js) and `astnav/<Test>.mapCode.ts.baseline.json`
//! (Go tokens only).
//!
//! PORT: Go `*tokenInfo` is `Option<TokenInfo>`. Go `*ast.SourceFile` is the
//! SourceFile `Node`. Go `strings.Builder` output is Go bytes (`Vec<u8>`),
//! turned into a port-form string for the baseline. Go `t.TempDir()` is
//! `jstest::TempDir`. Go positions are `int`; the port uses `i32` like the
//! astnav API.

use super::jstest::{self, TempDir};
use super::{Subtests, repo};
use crate::support::baseline;
use std::cell::Cell;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::PathBuf;
use std::sync::Once;
use ts_goport::ast::{source_file_ecma_line_map, source_file_text};
use ts_goport::astdata::SyntaxKind;
use ts_goport::astnav;
use ts_goport::core::Node;
use ts_goport::flags::ScriptKind;
use ts_goport::frontend::json::{
    JsonDecoder, JsonError, MarshalerTo, UnmarshalerFrom, json_marshal_indent,
    json_unmarshal_decode,
};
use ts_goport::frontend::json_ext::{
    marshal_field, unmarshal_struct_fields, write_object_end, write_object_start,
};
use ts_goport::frontend::parser::{SourceFileParseOptions, parse_source_file};
use ts_goport::frontend::tspath::Path;
use ts_goport::scanner_util::{go_string_bytes, go_string_from_bytes};

// Go: astnav/tokens_test.go:22 testFiles
fn test_files() -> Vec<PathBuf> {
    vec![repo::test_data_path().join("fixtures/services/mapCode.ts")]
}

/// Go `filepath.Base(fileName)`.
fn base_name(file_name: &std::path::Path) -> String {
    file_name
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_default()
}

/// Go `parser.ParseSourceFile(ast.SourceFileParseOptions{FileName: name,
/// Path: name}, text, kind)`.
// PORT: the parser takes `&'static str`; callers leak read file text.
fn parse(name: &str, text: &'static str, kind: ScriptKind) -> Node {
    parse_source_file(
        &SourceFileParseOptions {
            file_name: name.to_string(),
            path: Path(name.to_string()),
            ..Default::default()
        },
        text,
        kind,
    )
    .root
}

/// Go `string(fileText)` of `os.ReadFile`, leaked for the parser.
fn read_file_text(file_name: &std::path::Path) -> &'static str {
    let bytes = std::fs::read(file_name)
        .unwrap_or_else(|err| panic!("assertion failed: error is not nil: {err}"));
    go_string_from_bytes(bytes).leak()
}

// Go: astnav/tokens_test.go:26 TestGetTokenAtPosition
#[test]
fn test_get_token_at_position() {
    const TEST: &str = "TestGetTokenAtPosition";
    if jstest::skip_if_no_node_js(TEST) {
        return;
    }
    let mut t = Subtests::new(TEST);

    // t.Run("baseline", ...)
    baseline_tokens(
        &mut t,
        "baseline/",
        "GetTokenAtPosition",
        false, /*includeEOF*/
        &|file_text: &str, positions: &[i32]| ts_get_tokens_at_positions(file_text, positions),
        &|file: Node, pos: i32| to_token_info(astnav::get_token_at_position(file, pos)),
    );

    // t.Run("go baseline json", ...)
    baseline_go_tokens_json(
        &mut t,
        "go baseline json/",
        "GetTokenAtPosition",
        &|file: Node, pos: i32| to_token_info(astnav::get_token_at_position(file, pos)),
    );

    t.run("JSDoc type assertion", || {
        let file_text = "function foo(x) {
    const s = /**@type {string}*/(x)
}";
        let file = parse("/test.js", file_text, ScriptKind::JS);

        // Position of 'x' inside the parenthesized expression (position 52)
        let position = 52;

        // This should not panic - it previously panicked with:
        // "did not expect KindParenthesizedExpression to have KindIdentifier in its trivia"
        let token = astnav::get_touching_property_name(file, position);
        if token.is_nil() {
            return Err("Expected to get a token, got nil".to_string());
        }

        // The function may return either the identifier itself or the containing
        // parenthesized expression, depending on how the AST is structured
        if token.kind() != SyntaxKind::Identifier
            && token.kind() != SyntaxKind::ParenthesizedExpression
        {
            // PORT: Go `%s` of a Kind is "Kind" + the kind name.
            return Err(format!(
                "Expected identifier or parenthesized expression, got Kind{}",
                token.kind().as_str()
            ));
        }
        Ok(())
    });

    t.run("JSDoc type assertion with comment", || {
        // Exact code from the issue report
        let file_text = "function foo(x) {
    const s = /**@type {string}*/(x)  // Go-to-definition on x causes panic
}";
        let file = parse("/test.js", file_text, ScriptKind::JS);

        // Find position of 'x' in the type assertion
        let x_pos = 52; // Position of 'x' in (x)

        // This should not panic
        let token = astnav::get_touching_property_name(file, x_pos);
        assert!(token.is_some(), "Expected to get a token");
        Ok(())
    });

    t.run("pointer equality", || {
        let file_text = "\n\t\t\tfunction foo() {\n\t\t\t\treturn 0;\n\t\t\t}\n\t\t";
        let file = parse("/file.ts", file_text, ScriptKind::TS);
        assert_eq!(
            astnav::get_token_at_position(file, 0),
            astnav::get_token_at_position(file, 0)
        );
        Ok(())
    });

    t.finish();
}

// Go: astnav/tokens_test.go:113 TestGetTouchingPropertyName
#[test]
fn test_get_touching_property_name() {
    const TEST: &str = "TestGetTouchingPropertyName";
    if jstest::skip_if_no_node_js(TEST) {
        return;
    }
    let mut t = Subtests::new(TEST);

    baseline_tokens(
        &mut t,
        "",
        "GetTouchingPropertyName",
        false, /*includeEOF*/
        &|file_text: &str, positions: &[i32]| ts_get_touching_property_name(file_text, positions),
        &|file: Node, pos: i32| to_token_info(astnav::get_touching_property_name(file, pos)),
    );

    // t.Run("go baseline json", ...)
    baseline_go_tokens_json(
        &mut t,
        "go baseline json/",
        "GetTouchingPropertyName",
        &|file: Node, pos: i32| to_token_info(astnav::get_touching_property_name(file, pos)),
    );

    t.finish();
}

// Go: astnav/tokens_test.go:137 baselineTokens
// PORT: Go `t` is the subtest collector plus the name prefix of the Go
// subtest that calls this function ("" when the test calls it directly).
fn baseline_tokens(
    t: &mut Subtests,
    prefix: &str,
    test_name: &str,
    include_eof: bool,
    get_ts_tokens: &dyn Fn(&str, &[i32]) -> Vec<Option<TokenInfo>>,
    get_go_token: &dyn Fn(Node, i32) -> Option<TokenInfo>,
) {
    for file_name in test_files() {
        let base = base_name(&file_name);
        t.run(&format!("{prefix}{base}"), || {
            let file_text = read_file_text(&file_name);
            let text_len = go_string_bytes(file_text).len();

            let positions: Vec<i32> = (0..text_len + usize::from(include_eof))
                .map(|i| i as i32)
                .collect();
            let ts_tokens = get_ts_tokens(file_text, &positions);
            let file = parse("/file.ts", file_text, ScriptKind::TS);

            let mut output: Vec<u8> = Vec::new();
            let mut current_range: (i32, i32) = (0, 0);
            let mut current_diff = TokenDiff::default();

            for (pos, ts_token) in ts_tokens.iter().enumerate() {
                let pos = pos as i32;
                let go_token = get_go_token(file, pos);
                let diff = TokenDiff {
                    go_token,
                    ts_token: ts_token.clone(),
                };

                if !diff_equal(&current_diff, &diff) {
                    if !tokens_equal(&current_diff.go_token, &current_diff.ts_token) {
                        write_range_diff(&mut output, file, &current_diff, current_range, pos);
                    }
                    current_diff = diff;
                    current_range = (pos, pos);
                }
                // Go `currentRange.WithEnd(pos)`.
                current_range.1 = pos;
            }

            if !tokens_equal(&current_diff.go_token, &current_diff.ts_token) {
                write_range_diff(
                    &mut output,
                    file,
                    &current_diff,
                    current_range,
                    ts_tokens.len() as i32 - 1,
                );
            }

            let actual = if output.is_empty() {
                baseline::NO_CONTENT.to_string()
            } else {
                go_string_from_bytes(output)
            };
            baseline::run(
                &format!("{test_name}.{base}.baseline.txt"),
                &actual,
                &baseline::Options {
                    subfolder: "astnav".into(),
                    ..Default::default()
                },
            )
        });
    }
}

// Go: astnav/tokens_test.go:188 tokenRun
#[derive(Clone, Debug)]
struct TokenRun {
    start_pos: i32,
    end_pos: i32,
    kind: String,
    node_pos: i32,
    node_end: i32,
}

// PORT: Go marshals the struct through its json tags.
impl MarshalerTo for TokenRun {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        let mut first = true;
        marshal_field(enc, &mut first, "startPos", &self.start_pos)?;
        marshal_field(enc, &mut first, "endPos", &self.end_pos)?;
        marshal_field(enc, &mut first, "kind", &self.kind)?;
        marshal_field(enc, &mut first, "nodePos", &self.node_pos)?;
        marshal_field(enc, &mut first, "nodeEnd", &self.node_end)?;
        write_object_end(enc);
        Ok(())
    }
}

// Go: astnav/tokens_test.go:196 baselineGoTokensJSON
fn baseline_go_tokens_json(
    t: &mut Subtests,
    prefix: &str,
    test_name: &str,
    get_go_token: &dyn Fn(Node, i32) -> Option<TokenInfo>,
) {
    for file_name in test_files() {
        let base = base_name(&file_name);
        t.run(&format!("{prefix}{base}"), || {
            let file_text = read_file_text(&file_name);

            let file = parse("/file.ts", file_text, ScriptKind::TS);

            let max_pos = go_string_bytes(file_text).len() as i32;
            let mut runs: Vec<TokenRun> = Vec::new();
            let mut current: Option<TokenRun> = None;

            for pos in 0..max_pos {
                let token = get_go_token(file, pos);
                match (&mut current, &token) {
                    (Some(c), Some(token))
                        if c.kind == token.kind
                            && c.node_pos == token.pos
                            && c.node_end == token.end =>
                    {
                        c.end_pos = pos;
                    }
                    _ => {
                        if let Some(c) = current.take() {
                            runs.push(c);
                        }
                        current = token.map(|token| TokenRun {
                            start_pos: pos,
                            end_pos: pos,
                            kind: token.kind,
                            node_pos: token.pos,
                            node_end: token.end,
                        });
                    }
                }
            }
            if let Some(c) = current {
                runs.push(c);
            }

            // Go: core.Must(core.StringifyJson(runs, "", "  "))
            let output = json_marshal_indent(&runs, "", "  ")
                .unwrap_or_else(|err| panic!("core.Must: {err}"));

            baseline::run(
                &format!("{test_name}.{base}.baseline.json"),
                &output,
                &baseline::Options {
                    subfolder: "astnav".into(),
                    ..Default::default()
                },
            )
        });
    }
}

// Go: astnav/tokens_test.go:251 tokenDiff
#[derive(Clone, Debug, Default)]
struct TokenDiff {
    go_token: Option<TokenInfo>,
    ts_token: Option<TokenInfo>,
}

// Go: astnav/tokens_test.go:256 tokenInfo
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct TokenInfo {
    kind: String,
    pos: i32,
    end: i32,
}

// PORT: Go unmarshals the struct through its json tags (Go json v2 default
// struct unmarshal: exact names, unknown names skipped, null is the zero value).
impl UnmarshalerFrom for TokenInfo {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let is_object = unmarshal_struct_fields(dec, "astnav_test.tokenInfo", |name, dec| {
            match name {
                "kind" => json_unmarshal_decode(dec, &mut self.kind)?,
                "pos" => json_unmarshal_decode(dec, &mut self.pos)?,
                "end" => json_unmarshal_decode(dec, &mut self.end)?,
                _ => return Ok(false),
            }
            Ok(true)
        })?;
        if !is_object {
            *self = TokenInfo::default();
        }
        Ok(())
    }
}

// Go: astnav/tokens_test.go:262 toTokenInfo
fn to_token_info(node: Node) -> Option<TokenInfo> {
    if node.is_nil() {
        return None;
    }
    // PORT: Go `node.Kind.String()` is "Kind" + the kind name
    // (`SyntaxKind::as_str`).
    let mut kind = format!("Kind{}", node.kind().as_str()).replacen("Kind", "", 1);
    if kind == "EndOfFile" {
        kind = "EndOfFileToken".to_string();
    }
    Some(TokenInfo {
        kind,
        pos: node.pos(),
        end: node.end(),
    })
}

// Go: astnav/tokens_test.go:278 diffEqual
fn diff_equal(a: &TokenDiff, b: &TokenDiff) -> bool {
    tokens_equal(&a.go_token, &b.go_token) && tokens_equal(&a.ts_token, &b.ts_token)
}

// Go: astnav/tokens_test.go:282 tokensEqual
fn tokens_equal(t1: &Option<TokenInfo>, t2: &Option<TokenInfo>) -> bool {
    t1 == t2
}

/// The shared body of the Go `ts*` helpers: writes `file.ts` and
/// `positions.json` to a new temp directory and runs `script` there with the
/// TypeScript library.
fn eval_ts_tokens(file_text: &str, positions: &[i32], script: &str) -> Vec<Option<TokenInfo>> {
    let dir = TempDir::new();
    std::fs::write(dir.path().join("file.ts"), go_string_bytes(file_text))
        .unwrap_or_else(|err| panic!("assertion failed: error is not nil: {err}"));

    let positions_json = json_marshal_indent(&positions.to_vec(), "", "")
        .unwrap_or_else(|err| panic!("core.Must: {err}"));
    std::fs::write(dir.path().join("positions.json"), positions_json)
        .unwrap_or_else(|err| panic!("assertion failed: error is not nil: {err}"));

    jstest::eval_node_script_with_ts::<Vec<Option<TokenInfo>>>(script, Some(dir.path()), &[""])
        .unwrap_or_else(|err| panic!("assertion failed: error is not nil: {err}"))
}

// Go: astnav/tokens_test.go:289 tsGetTokensAtPositions
fn ts_get_tokens_at_positions(file_text: &str, positions: &[i32]) -> Vec<Option<TokenInfo>> {
    let script = r#"
		import fs from "fs";
		export default (ts) => {
			const positions = JSON.parse(fs.readFileSync("positions.json", "utf8"));
			const fileText = fs.readFileSync("file.ts", "utf8");
			const file = ts.createSourceFile(
				"file.ts",
				fileText,
				{ languageVersion: ts.ScriptTarget.Latest, jsDocParsingMode: ts.JSDocParsingMode.ParseAll },
				/*setParentNodes*/ true
			);
			return positions.map(position => {
				let token = ts.getTokenAtPosition(file, position);
				if (token.kind === ts.SyntaxKind.SyntaxList) {
					token = token.parent;
				}
				return {
					kind: ts.Debug.formatSyntaxKind(token.kind),
					pos: token.pos,
					end: token.end,
				};
			});
		};"#;
    eval_ts_tokens(file_text, positions, script)
}

// Go: astnav/tokens_test.go:326 tsGetTouchingPropertyName
fn ts_get_touching_property_name(file_text: &str, positions: &[i32]) -> Vec<Option<TokenInfo>> {
    let script = r#"
		import fs from "fs";
		export default (ts) => {
			const positions = JSON.parse(fs.readFileSync("positions.json", "utf8"));
			const fileText = fs.readFileSync("file.ts", "utf8");
			const file = ts.createSourceFile(
				"file.ts",
				fileText,
				{ languageVersion: ts.ScriptTarget.Latest, jsDocParsingMode: ts.JSDocParsingMode.ParseAll },
				/*setParentNodes*/ true
			);
			return positions.map(position => {
				let token = ts.getTouchingPropertyName(file, position);
				if (token.kind === ts.SyntaxKind.SyntaxList) {
					token = token.parent;
				}
				return {
					kind: ts.Debug.formatSyntaxKind(token.kind),
					pos: token.pos,
					end: token.end,
				};
			});
		};"#;
    eval_ts_tokens(file_text, positions, script)
}

// Go: core/core.go:472 PositionToLineAndByteOffset
fn position_to_line_and_byte_offset(position: i32, line_starts: &[i32]) -> (i32, i32) {
    let line = line_starts
        .partition_point(|&start| start <= position)
        .saturating_sub(1);
    (line as i32, position - line_starts[line])
}

// Go: astnav/tokens_test.go:363 writeRangeDiff
fn write_range_diff(
    output: &mut Vec<u8>,
    file: Node,
    diff: &TokenDiff,
    rng: (i32, i32),
    position: i32,
) {
    let lines = &*source_file_ecma_line_map(file);
    let file_text = source_file_text(file);
    let text = go_string_bytes(&file_text);
    let text_len = text.len() as i32;

    let mut ts_token_pos = position;
    let mut go_token_pos = position;
    let mut ts_token_end = position;
    let mut go_token_end = position;
    if let Some(ts_token) = &diff.ts_token {
        ts_token_pos = ts_token.pos;
        ts_token_end = ts_token.end;
    }
    if let Some(go_token) = &diff.go_token {
        go_token_pos = go_token.pos;
        go_token_end = go_token.end;
    }
    let (ts_start_line, _) = position_to_line_and_byte_offset(ts_token_pos, lines);
    let (ts_end_line, _) = position_to_line_and_byte_offset(ts_token_end, lines);
    let (go_start_line, _) = position_to_line_and_byte_offset(go_token_pos, lines);
    let (go_end_line, _) = position_to_line_and_byte_offset(go_token_end, lines);

    let context_lines = 2;
    let start_line = ts_start_line.min(go_start_line);
    let end_line = ts_end_line.max(go_end_line);
    let mut marker_lines = [ts_start_line, ts_end_line, go_start_line, go_end_line];
    marker_lines.sort_unstable();
    let context_start = (start_line - context_lines).max(0);
    let context_end = (lines.len() as i32 - 1).min(end_line + context_lines);
    let digits = context_end.to_string().len();

    let should_truncate = |line: i32| -> (bool, i32) {
        // Go `slices.BinarySearch(markerLines, line)`: the first index whose
        // value is not less than `line`.
        let index = marker_lines.partition_point(|&m| m < line);
        if index == 0 || index == marker_lines.len() {
            return (false, 0);
        }
        let low = marker_lines[index - 1];
        let high = marker_lines[index];
        if line - low > 5 && high - line > 5 {
            return (true, high - 5);
        }
        (false, 0)
    };

    if !output.is_empty() {
        output.extend_from_slice(b"\n\n");
    }

    output.extend_from_slice(format!("〚Positions: [{}, {}]〛\n", rng.0, rng.1).as_bytes());
    match &diff.ts_token {
        Some(ts_token) => output.extend_from_slice(
            format!(
                "【TS: {} [{ts_token_pos}, {ts_token_end})】\n",
                ts_token.kind
            )
            .as_bytes(),
        ),
        None => output.extend_from_slice("【TS: nil】\n".as_bytes()),
    }
    match &diff.go_token {
        Some(go_token) => output.extend_from_slice(
            format!(
                "《Go: {} [{go_token_pos}, {go_token_end})》\n",
                go_token.kind
            )
            .as_bytes(),
        ),
        None => output.extend_from_slice("《Go: nil》\n".as_bytes()),
    }
    let mut line = context_start;
    while line <= context_end {
        let (truncate, skip_to) = should_truncate(line);
        if truncate {
            output.extend_from_slice(
                format!(
                    "{} │........ {} lines omitted ........\n",
                    " ".repeat(digits),
                    skip_to - line + 1
                )
                .as_bytes(),
            );
            line = skip_to;
        }
        output.extend_from_slice(format!("{:>digits$} │", line + 1).as_bytes());
        let mut end = text_len + 1;
        if line < lines.len() as i32 - 1 {
            end = lines[(line + 1) as usize];
        }
        for pos in lines[line as usize]..end {
            if pos == rng.1 + 1 {
                output.extend_from_slice("〛".as_bytes());
            }
            if diff.ts_token.is_some() && pos == ts_token_end {
                output.extend_from_slice("】".as_bytes());
            }
            if diff.go_token.is_some() && pos == go_token_end {
                output.extend_from_slice("》".as_bytes());
            }

            if diff.go_token.is_some() && pos == go_token_pos {
                output.extend_from_slice("《".as_bytes());
            }
            if diff.ts_token.is_some() && pos == ts_token_pos {
                output.extend_from_slice("【".as_bytes());
            }
            if pos == rng.0 {
                output.extend_from_slice("〚".as_bytes());
            }

            if pos < text_len {
                output.push(text[pos as usize]);
            }
        }
        line += 1;
    }
}

// Go: astnav/tokens_test.go:458 TestFindPrecedingToken
#[test]
fn test_find_preceding_token() {
    const TEST: &str = "TestFindPrecedingToken";
    if jstest::skip_if_no_node_js(TEST) {
        return;
    }
    let mut t = Subtests::new(TEST);

    // t.Run("baseline", ...)
    baseline_tokens(
        &mut t,
        "baseline/",
        "FindPrecedingToken",
        true, /*includeEOF*/
        &|file_text: &str, positions: &[i32]| ts_find_preceding_tokens(file_text, positions),
        &|file: Node, pos: i32| to_token_info(astnav::find_preceding_token(file, pos)),
    );

    // t.Run("go baseline json", ...)
    baseline_go_tokens_json(
        &mut t,
        "go baseline json/",
        "FindPrecedingToken",
        &|file: Node, pos: i32| to_token_info(astnav::find_preceding_token(file, pos)),
    );

    t.finish();
}

// Go: astnav/tokens_test.go:485 TestFindNextToken
#[test]
fn test_find_next_token() {
    const TEST: &str = "TestFindNextToken";
    let mut t = Subtests::new(TEST);

    // t.Run("go baseline json", ...)
    baseline_go_tokens_json(
        &mut t,
        "go baseline json/",
        "FindNextToken",
        &|file: Node, pos: i32| {
            // FindNextToken panics (like Go's assert) when the scanner finds trivia between
            // previousToken.End() and the next syntactic token. Catch those to avoid crashing
            // the baseline generator; those positions will be absent from the baseline.
            recover_quietly(|| {
                let token = astnav::get_token_at_position(file, pos);
                let next = astnav::find_next_token(token, file, file);
                to_token_info(next)
            })
            .flatten()
        },
    );

    t.finish();
}

thread_local! {
    /// True while `recover_quietly` runs on this thread.
    static QUIET_PANICS: Cell<bool> = const { Cell::new(false) };
}

/// Go `defer func() { if r := recover(); r != nil { ... } }()` around `f`:
/// `None` when `f` panics.
// PORT: Go `recover` prints nothing. The Rust panic hook would print each
// caught panic, so a hook that stays quiet on this thread while `f` runs is
// installed once. It passes every other panic to the previous hook.
fn recover_quietly<T>(f: impl FnOnce() -> T) -> Option<T> {
    static HOOK: Once = Once::new();
    HOOK.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !QUIET_PANICS.with(Cell::get) {
                previous(info);
            }
        }));
    });
    QUIET_PANICS.with(|quiet| quiet.set(true));
    let result = catch_unwind(AssertUnwindSafe(f));
    QUIET_PANICS.with(|quiet| quiet.set(false));
    result.ok()
}

// Go: astnav/tokens_test.go:506 TestUnitFindPrecedingToken
#[test]
fn test_unit_find_preceding_token() {
    struct TestCase {
        name: &'static str,
        file_content: &'static str,
        position: i32,
        expected_kind: SyntaxKind,
    }
    let test_cases = [
        TestCase {
            name: "after dot in jsdoc",
            file_content: r#"import {
    CharacterCodes,
    compareStringsCaseInsensitive,
    compareStringsCaseSensitive,
    compareValues,
    Comparison,
    Debug,
    endsWith,
    equateStringsCaseInsensitive,
    equateStringsCaseSensitive,
    GetCanonicalFileName,
    getDeclarationFileExtension,
    getStringComparer,
    identity,
    lastOrUndefined,
    Path,
    some,
    startsWith,
} from "./_namespaces/ts.js";

/**
 * Internally, we represent paths as strings with '/' as the directory separator.
 * When we make system calls (eg: LanguageServiceHost.getDirectory()),
 * we expect the host to correctly handle paths in our specified format.
 *
 * @internal
 */
export const directorySeparator = "/";
/** @internal */
export const altDirectorySeparator = "\\";
const urlSchemeSeparator = "://";
const backslashRegExp = /\\/g;


backslashRegExp.

//Path Tests

/**
 * Determines whether a charCode corresponds to '/' or '\'.
 *
 * @internal
 */
export function isAnyDirectorySeparator(charCode: number): boolean {
    return charCode === CharacterCodes.slash || charCode === CharacterCodes.backslash;
}"#,
            position: 839,
            expected_kind: SyntaxKind::DotToken,
        },
        TestCase {
            name: "after comma in parameter list",
            file_content: "takesCb((n, s, ))",
            position: 15,
            expected_kind: SyntaxKind::CommaToken,
        },
    ];
    let mut t = Subtests::new("TestUnitFindPrecedingToken");
    for test_case in &test_cases {
        t.run(test_case.name, || {
            let file = parse("/file.ts", test_case.file_content, ScriptKind::TS);
            let token = astnav::find_preceding_token(file, test_case.position);
            assert_eq!(token.kind(), test_case.expected_kind);
            Ok(())
        });
    }
    t.finish();
}

// Go: astnav/tokens_test.go:585 tsFindPrecedingTokens
fn ts_find_preceding_tokens(file_text: &str, positions: &[i32]) -> Vec<Option<TokenInfo>> {
    let script = r#"
		import fs from "fs";
		export default (ts) => {
			const positions = JSON.parse(fs.readFileSync("positions.json", "utf8"));
			const fileText = fs.readFileSync("file.ts", "utf8");
			const file = ts.createSourceFile(
				"file.ts",
				fileText,
				{ languageVersion: ts.ScriptTarget.Latest, jsDocParsingMode: ts.JSDocParsingMode.ParseAll },
				/*setParentNodes*/ true
			);
			return positions.map(position => {
				let token = ts.findPrecedingToken(position, file);
				if (token === undefined) {
					return undefined;
				}
				if (token.kind === ts.SyntaxKind.SyntaxList) {
					token = token.parent;
				}
				return {
					kind: ts.Debug.formatSyntaxKind(token.kind),
					pos: token.pos,
					end: token.end,
				};
			});
		};"#;
    eval_ts_tokens(file_text, positions, script)
}
