//! Go: internal/testutil/contentmappertest/failing.go (tsgo#4712).

use super::prelude::*;

// Go: failing.go:12 failingHandler
pub(super) struct FailingHandler;

impl MapperHandler for FailingHandler {
    // Go: failing.go:14 failingHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, _params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                Err(errors::new("content mapper failed to transform the file"))
            }
            _ => Err(unexpected_method(method)),
        }
    }
}
