//! Go: internal/testutil/contentmappertest/supplemental_module.go (tsgo#4712).

use super::prelude::*;

// Go: supplemental_module.go:11 supplementalModuleHandler
pub(super) struct SupplementalModuleHandler;

impl MapperHandler for SupplementalModuleHandler {
    // Go: supplemental_module.go:13 supplementalModuleHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let _p: TransformParams = unmarshal_params(&params)?;
                reply(TransformResult {
                    mapped_output: MappedOutput {
                        text: "export default 1;".to_string(),
                        extension: ".ts".to_string(),
                        ..MappedOutput::default()
                    },
                    supplemental: vec![SupplementalOutput {
                        mapped_output: MappedOutput {
                            text: r#"export const privateValue: number = "wrong";"#.to_string(),
                            extension: ".ts".to_string(),
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
