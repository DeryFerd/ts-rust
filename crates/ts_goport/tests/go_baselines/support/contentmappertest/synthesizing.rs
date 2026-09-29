//! Go: internal/testutil/contentmappertest/synthesizing.go (tsgo#4712).

use super::prelude::*;

// Go: synthesizing.go:12 synthesizedOutput
const SYNTHESIZED_OUTPUT: &str = "export const el = jsxRuntime(Widget);\n";

// Go: synthesizing.go:14 synthesizingHandler
pub(super) struct SynthesizingHandler;

impl MapperHandler for SynthesizingHandler {
    // Go: synthesizing.go:16 synthesizingHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let _p: TransformParams = unmarshal_params(&params)?;
                let mappings = spanmap::new(&[]).marshal()?;
                reply(TransformResult {
                    mapped_output: MappedOutput {
                        text: SYNTHESIZED_OUTPUT.to_string(),
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
