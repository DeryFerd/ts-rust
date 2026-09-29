//! Go: internal/testutil/contentmappertest/verbatim.go (tsgo#4712).

use super::prelude::*;

// Go: verbatim.go:11 verbatimHandler
pub(super) struct VerbatimHandler;

// Go: verbatim.go:13 moduleVerbatimHandler
pub(super) struct ModuleVerbatimHandler;

impl MapperHandler for VerbatimHandler {
    // Go: verbatim.go:15 verbatimHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let p: TransformParams = unmarshal_params(&params)?;
                let mapped_output = identity_mapped_output(&p.content)?;
                reply(TransformResult {
                    mapped_output,
                    ..TransformResult::default()
                })
            }
            _ => Err(unexpected_method(method)),
        }
    }
}

impl MapperHandler for ModuleVerbatimHandler {
    // Go: verbatim.go:34 moduleVerbatimHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let p: TransformParams = unmarshal_params(&params)?;
                let mut mapped_output = identity_mapped_output(&p.content)?;
                mapped_output.extension = ".mts".to_string();
                reply(TransformResult {
                    mapped_output,
                    ..TransformResult::default()
                })
            }
            _ => Err(unexpected_method(method)),
        }
    }
}
