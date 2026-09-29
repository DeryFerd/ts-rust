//! Go: internal/testutil/contentmappertest/supplemental.go (tsgo#4712).

use super::prelude::*;

// Go: supplemental.go:11 supplementalHandler
pub(super) struct SupplementalHandler;

impl MapperHandler for SupplementalHandler {
    // Go: supplemental.go:13 supplementalHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let p: TransformParams = unmarshal_params(&params)?;
                let mapped_output = identity_mapped_output(&p.content)?;
                reply(TransformResult {
                    mapped_output: MappedOutput {
                        text: "export {};".to_string(),
                        extension: ".ts".to_string(),
                        ..MappedOutput::default()
                    },
                    supplemental: vec![SupplementalOutput { mapped_output }],
                    ..TransformResult::default()
                })
            }
            _ => Err(unexpected_method(method)),
        }
    }
}
