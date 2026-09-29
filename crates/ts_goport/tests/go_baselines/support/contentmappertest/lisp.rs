//! Go: internal/testutil/contentmappertest/lisp.go (tsgo#4712).

use super::prelude::*;

// Go: lisp.go:13 lispHandler
pub(super) struct LispHandler;

/// A `spanmap.Segment` literal with all features.
fn segment(
    virtual_start: i32,
    virtual_end: i32,
    original_start: i32,
    original_end: i32,
    kind: Kind,
) -> Segment {
    Segment {
        virtual_start,
        virtual_end,
        original_start,
        original_end,
        kind,
        features: Feature::ALL,
    }
}

impl MapperHandler for LispHandler {
    // Go: lisp.go:15 lispHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("lisp")),
            contentmapper::METHOD_TRANSFORM => {
                let p: TransformParams = unmarshal_params(&params)?;
                let expression = p.content.strip_suffix('\n').unwrap_or(&p.content);
                if expression != r#"(+ 1 2 "oops")"# {
                    return Err(errors::new(format!(
                        "contentmappertest: unsupported Lisp expression {}",
                        strconv::quote(&p.content)
                    )));
                }
                let mappings = spanmap::new(&[
                    segment(0, 3, 1, 2, Kind::ALIAS),
                    segment(4, 5, 3, 4, Kind::VERBATIM),
                    segment(7, 8, 5, 6, Kind::VERBATIM),
                    segment(10, 16, 7, 13, Kind::VERBATIM),
                ])
                .marshal()?;
                reply(TransformResult {
                    mapped_output: MappedOutput {
                        text: r#"add(1, 2, "oops");"#.to_string(),
                        extension: ".ts".to_string(),
                        mappings: JsonValue(mappings),
                        ..MappedOutput::default()
                    },
                    ..TransformResult::default()
                })
            }
            _ => Err(unexpected_method(method)),
        }
    }
}
