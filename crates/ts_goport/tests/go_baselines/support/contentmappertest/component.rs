//! Go: internal/testutil/contentmappertest/component.go (tsgo#4712).

use super::prelude::*;

// Go: component.go:15 componentHandler
pub(super) struct ComponentHandler;

impl MapperHandler for ComponentHandler {
    // Go: component.go:17 componentHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let p: TransformParams = unmarshal_params(&params)?;
                let (text, mappings) = transform_component(&p.content)?;
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

/// The virtual text and its segments that `transformComponent` writes (Go:
/// the `virtual` builder and `segments` of its closures).
#[derive(Default)]
struct ComponentWriter {
    virtual_: String,
    segments: Vec<Segment>,
}

impl ComponentWriter {
    // Go: component.go:40 writeSynthesized
    fn write_synthesized(&mut self, text: &str) {
        self.virtual_.push_str(text);
    }

    // Go: component.go:43 writeMapped
    fn write_mapped(&mut self, text: &str, original_start: usize, original_end: usize, kind: Kind) {
        let virtual_start = self.virtual_.len() as i32;
        self.virtual_.push_str(text);
        self.segments.push(Segment {
            virtual_start,
            virtual_end: self.virtual_.len() as i32,
            original_start: original_start as i32,
            original_end: original_end as i32,
            kind,
            features: Feature::ALL,
        });
    }

    // Go: component.go:55 writeAnchored
    fn write_anchored(&mut self, text: &str, original_position: usize, features: Feature) {
        let virtual_start = self.virtual_.len() as i32;
        self.virtual_.push_str(text);
        self.segments.push(Segment {
            virtual_start,
            virtual_end: self.virtual_.len() as i32,
            original_start: original_position as i32,
            original_end: original_position as i32,
            kind: Kind::ATOM,
            features,
        });
    }
}

// Go: component.go:36 transformComponent
fn transform_component(content: &str) -> Result<(String, JsonValue), GoError> {
    let mut w = ComponentWriter::default();
    let bytes = content.as_bytes();

    if let Some(script_open) = content.find("<script") {
        let Some(open_end_rel) = content[script_open..].find('>') else {
            return Err(errors::new("contentmappertest: unclosed <script> tag"));
        };
        let script_start = script_open + open_end_rel + 1;
        let Some(close_rel) = content[script_start..].find("</script>") else {
            return Err(errors::new("contentmappertest: missing </script> tag"));
        };
        let script_end = script_start + close_rel;
        w.write_mapped(
            &content[script_start..script_end],
            script_start,
            script_end,
            Kind::VERBATIM,
        );
    }

    w.write_synthesized("\nfunction __render() {\n");
    let mut search_start = 0usize;
    while search_start < content.len() {
        let Some(open_rel) = content[search_start..].find("{{") else {
            break;
        };
        let expr_start = search_start + open_rel + "{{".len();
        let Some(close_rel) = content[expr_start..].find("}}") else {
            return Err(errors::new(
                "contentmappertest: unclosed template expression",
            ));
        };
        let expr_end = expr_start + close_rel;
        w.write_synthesized("  void (");
        let mut pos = expr_start;
        while pos < expr_end {
            if !is_identifier_start(bytes[pos]) {
                // PORT: Go writes one byte at a time; the bytes of a
                // multi-byte char are never identifier bytes, so writing
                // the whole char gives the same text.
                let ch_len = content[pos..].chars().next().map_or(1, char::len_utf8);
                w.write_synthesized(&content[pos..pos + ch_len]);
                pos += ch_len;
                continue;
            }
            let mut end = pos + 1;
            while end < expr_end && is_identifier_part(bytes[end]) {
                end += 1;
            }
            w.write_mapped(&content[pos..end], pos, end, Kind::ATOM);
            pos = end;
        }
        w.write_synthesized(");\n");
        search_start = expr_end + "}}".len();
    }
    w.write_synthesized("}\n");
    if let Some((name_start, name_end)) = component_name_range(content) {
        w.write_synthesized("export class ");
        w.write_mapped(
            &content[name_start..name_end],
            name_start,
            name_end,
            Kind::ATOM,
        );
        w.write_synthesized(" {}\n");
    }
    w.write_anchored(
        "export default {};\n",
        0,
        Feature::DEFINITION | Feature::REFERENCES,
    );

    let mappings = spanmap::new(&w.segments).marshal()?;
    Ok((w.virtual_, JsonValue(mappings)))
}

// Go: component.go:127 componentNameRange
fn component_name_range(content: &str) -> Option<(usize, usize)> {
    let component_start = content.find("<component")?;
    let tag_end_rel = content[component_start..].find('>')?;
    let tag = &content[component_start..component_start + tag_end_rel];
    let name_rel = tag.find(r#"name=""#)?;
    let start = component_start + name_rel + r#"name=""#.len();
    let end_rel = content[start..].find('"')?;
    Some((start, start + end_rel))
}

// Go: component.go:149 isIdentifierStart
fn is_identifier_start(ch: u8) -> bool {
    ch == b'_' || ch == b'$' || ch.is_ascii_uppercase() || ch.is_ascii_lowercase()
}

// Go: component.go:153 isIdentifierPart
fn is_identifier_part(ch: u8) -> bool {
    is_identifier_start(ch) || ch.is_ascii_digit()
}
