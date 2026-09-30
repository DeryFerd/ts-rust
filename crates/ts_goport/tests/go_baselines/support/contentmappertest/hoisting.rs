//! Go: internal/testutil/contentmappertest/hoisting.go (ts#64042).

use super::prelude::*;

// Go: hoisting.go:15 hoistingHandler
pub(super) struct HoistingHandler;

impl MapperHandler for HoistingHandler {
    // Go: hoisting.go:17 hoistingHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let p: TransformParams = unmarshal_params(&params)?;
                let (text, mappings) = transform_hoisting(&p.content)?;
                reply(TransformResult {
                    mapped_output: MappedOutput {
                        text,
                        extension: ".ts".to_string(),
                        mappings,
                        ..MappedOutput::default()
                    },
                    ..TransformResult::default()
                })
            }
            _ => Err(unexpected_method(method)),
        }
    }
}

/// The virtual text and its segments that `transformHoisting` writes (Go:
/// the `virtual` builder and `segments` of its closure).
struct HoistingWriter<'a> {
    content: &'a str,
    virtual_: String,
    segments: Vec<Segment>,
}

impl HoistingWriter<'_> {
    // Go: hoisting.go:55 writeMapped
    fn write_mapped(&mut self, original_start: usize, original_end: usize) {
        let virtual_start = self.virtual_.len() as i32;
        self.virtual_
            .push_str(&self.content[original_start..original_end]);
        self.segments.push(Segment {
            virtual_start,
            virtual_end: self.virtual_.len() as i32,
            original_start: original_start as i32,
            original_end: original_end as i32,
            kind: Kind::VERBATIM,
            features: Feature::ALL,
        });
    }
}

// Go: hoisting.go:51 transformHoisting
// transformHoisting emits the script body inside a render function, but lifts the leading run of import
// declarations above it, so the virtual text is laid out as:
//
//	///<reference types="svelte" />
//	;
//	import { existing } from "./dep";      <- original [importsStart, importsEnd)
//	function $$render() {
//	<whitespace before the first import>   <- original [scriptStart, importsStart)
//	<script body after the last import>    <- original [importsEnd, scriptEnd)
//	}
//
// This mirrors the layout svelte2tsx produces for a component. Hoisting splits the script into segments
// that are contiguous in the original but disjoint in the virtual text, so the original position at a
// splice point (importsStart) lies on the boundary of two verbatim segments and projects to two distinct
// exact virtual positions.
fn transform_hoisting(content: &str) -> Result<(String, JsonValue), GoError> {
    let mut w = HoistingWriter {
        content,
        virtual_: String::new(),
        segments: Vec::new(),
    };

    let (script_start, script_end) = script_range(content)?;
    let (imports_start, imports_end) = leading_import_range(content, script_start, script_end);

    w.virtual_
        .push_str("///<reference types=\"svelte\" />\n;\n");
    w.write_mapped(imports_start, imports_end);
    w.virtual_.push_str("\nfunction $$render() {");
    w.write_mapped(script_start, imports_start);
    w.write_mapped(imports_end, script_end);
    w.virtual_
        .push_str("\n;\nreturn { props: {} as Record<string, never> }}\n");

    let mappings = spanmap::new(&w.segments).marshal()?;
    Ok((w.virtual_, JsonValue(mappings)))
}

// Go: hoisting.go:88 scriptRange
fn script_range(content: &str) -> Result<(usize, usize), GoError> {
    let Some(script_open) = content.find("<script") else {
        return Err(errors::new("contentmappertest: missing <script> tag"));
    };
    let Some(open_end_rel) = content[script_open..].find('>') else {
        return Err(errors::new("contentmappertest: unclosed <script> tag"));
    };
    let start = script_open + open_end_rel + 1;
    let Some(close_rel) = content[start..].find("</script>") else {
        return Err(errors::new("contentmappertest: missing </script> tag"));
    };
    Ok((start, start + close_rel))
}

// Go: hoisting.go:107 leadingImportRange
// leadingImportRange returns the range covering the run of import declarations at the top of the script
// body, skipping the whitespace that precedes them.
fn leading_import_range(content: &str, script_start: usize, script_end: usize) -> (usize, usize) {
    let bytes = content.as_bytes();
    let mut start = script_start;
    while start < script_end && is_space_byte(bytes[start]) {
        start += 1;
    }
    let mut end = start;
    while end < script_end && content[end..script_end].starts_with("import ") {
        let Some(line_end) = content[end..script_end].find('\n') else {
            end = script_end;
            break;
        };
        end += line_end;
        while end < script_end && is_space_byte(bytes[end]) {
            end += 1;
        }
    }
    while end > start && is_space_byte(bytes[end - 1]) {
        end -= 1;
    }
    (start, end)
}

// Go: hoisting.go:130 isSpaceByte
fn is_space_byte(ch: u8) -> bool {
    ch == b' ' || ch == b'\t' || ch == b'\r' || ch == b'\n'
}
