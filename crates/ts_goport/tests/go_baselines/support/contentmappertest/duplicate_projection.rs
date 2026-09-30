//! Go: internal/testutil/contentmappertest/duplicate_projection.go (ts#64042).

use super::prelude::*;

// Go: duplicate_projection.go:14 duplicateProjectionHandler
// duplicateProjectionHandler emits the original content as both the canonical output and a supplemental
// one, so a single original span has an identical counterpart in two distinct virtual source files that
// share an OriginalFileName. An edit to that span is therefore recorded once per projection.
pub(super) struct DuplicateProjectionHandler;

impl MapperHandler for DuplicateProjectionHandler {
    // Go: duplicate_projection.go:16 duplicateProjectionHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let p: TransformParams = unmarshal_params(&params)?;
                let canonical = identity_mapped_output(&p.content)?;
                let supplemental = identity_mapped_output(&p.content)?;
                reply(TransformResult {
                    mapped_output: canonical,
                    supplemental: vec![SupplementalOutput {
                        mapped_output: supplemental,
                    }],
                    ..TransformResult::default()
                })
            }
            _ => Err(unexpected_method(method)),
        }
    }
}
