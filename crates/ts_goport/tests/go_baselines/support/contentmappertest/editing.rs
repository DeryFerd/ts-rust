//! Go: internal/testutil/contentmappertest/editing.go (tsgo#4712).

use super::prelude::*;

// Go: editing.go:13 prefixedSupplementalHandler
pub(super) struct PrefixedSupplementalHandler;

impl MapperHandler for PrefixedSupplementalHandler {
    // Go: editing.go:15 prefixedSupplementalHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let p: TransformParams = unmarshal_params(&params)?;
                const PREFIX: &str = "/* generated */\n";
                let mappings = spanmap::new(&[Segment {
                    virtual_start: PREFIX.len() as i32,
                    virtual_end: (PREFIX.len() + p.content.len()) as i32,
                    original_start: 0,
                    original_end: p.content.len() as i32,
                    kind: Kind::VERBATIM,
                    features: Feature::ALL,
                }])
                .marshal()?;
                reply(TransformResult {
                    mapped_output: MappedOutput {
                        text: "export {};".to_string(),
                        extension: ".ts".to_string(),
                        ..MappedOutput::default()
                    },
                    supplemental: vec![SupplementalOutput {
                        mapped_output: MappedOutput {
                            text: format!("{PREFIX}{}", p.content),
                            extension: ".ts".to_string(),
                            mappings: JsonValue(mappings),
                            ..MappedOutput::default()
                        },
                    }],
                    ..TransformResult::default()
                })
            }
            _ => Err(unexpected_method(method)),
        }
    }
}

// Go: editing.go:49 unmappedFoldingHandler
pub(super) struct UnmappedFoldingHandler;

impl MapperHandler for UnmappedFoldingHandler {
    // Go: editing.go:51 unmappedFoldingHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, _params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let mappings = spanmap::new(&[]).marshal()?;
                reply(TransformResult {
                    mapped_output: MappedOutput {
                        text: "import \"a\";\nimport \"b\";\n/*\n * generated\n */\nexport {};"
                            .to_string(),
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
