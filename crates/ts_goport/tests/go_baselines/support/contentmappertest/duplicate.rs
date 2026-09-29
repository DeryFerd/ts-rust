//! Go: internal/testutil/contentmappertest/duplicate.go (tsgo#4712).

use super::prelude::*;

// Go: duplicate.go:14 duplicateHandler
pub(super) struct DuplicateHandler;

/// Go `strings.Index(s, substr)`: -1 when absent.
fn index(s: &str, substr: &str) -> i32 {
    s.find(substr).map_or(-1, |i| i as i32)
}

/// A verbatim `spanmap.Segment` of `length` bytes at `virtual_start` for the
/// original range `[0, length)`.
fn copy_segment(virtual_start: i32, length: i32, features: Feature) -> Segment {
    Segment {
        virtual_start,
        virtual_end: virtual_start + length,
        original_start: 0,
        original_end: length,
        kind: Kind::VERBATIM,
        features,
    }
}

impl MapperHandler for DuplicateHandler {
    // Go: duplicate.go:16 duplicateHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let p: TransformParams = unmarshal_params(&params)?;
                let content = p.content.as_str();
                let length = content.len() as i32;
                if p.file_name.contains("rename-conflict") {
                    let virtual_ = format!(
                        "export const {content} = 1;\nconst object = {{ {content} }};\n{content};\n"
                    );
                    let first = index(&virtual_, content);
                    let second =
                        index(&virtual_[(first + length) as usize..], content) + first + length;
                    let third =
                        index(&virtual_[(second + length) as usize..], content) + second + length;
                    let mappings = spanmap::new(&[
                        copy_segment(first, length, Feature::RENAME),
                        copy_segment(second, length, Feature::RENAME),
                        copy_segment(third, length, Feature::RENAME),
                    ])
                    .marshal()?;
                    return reply(TransformResult {
                        mapped_output: MappedOutput {
                            text: virtual_,
                            extension: ".ts".to_string(),
                            mappings: JsonValue(mappings),
                            ..MappedOutput::default()
                        },
                        ..TransformResult::default()
                    });
                }
                let virtual_ = format!("export const {content} = 1;\n{content};\n");
                let first = "export const ".len() as i32;
                let second = first + length + " = 1;\n".len() as i32;
                let disabled = p.file_name.contains("disabled");
                let mut semantic_features =
                    Feature::HOVER | Feature::DEFINITION | Feature::REFERENCES | Feature::RENAME;
                let mut navigation_features =
                    Feature::DEFINITION | Feature::REFERENCES | Feature::RENAME;
                if disabled {
                    semantic_features = Feature::NONE;
                    navigation_features = Feature::NONE;
                }
                let mappings = spanmap::new(&[
                    copy_segment(first, length, semantic_features),
                    copy_segment(second, length, navigation_features),
                ])
                .marshal()?;
                reply(TransformResult {
                    mapped_output: MappedOutput {
                        text: virtual_,
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
