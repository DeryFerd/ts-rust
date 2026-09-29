//! Go: internal/testutil/contentmappertest/supplemental_globals.go (tsgo#4712).

use super::prelude::*;

// Go: supplemental_globals.go:12 supplementalGlobalsHandler
pub(super) struct SupplementalGlobalsHandler;

impl MapperHandler for SupplementalGlobalsHandler {
    // Go: supplemental_globals.go:14 supplementalGlobalsHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let p: TransformParams = unmarshal_params(&params)?;
                let supplemental = if p.file_name.ends_with("/a.vue") {
                    "/// <reference path=\"./extra.d.ts\" />\ninterface Shared extends Extra { value: string }"
                } else if p.file_name.ends_with("/b.vue") {
                    "declare const shared: Shared;"
                } else {
                    return Err(errors::new(format!(
                        "contentmappertest: unexpected supplemental global input {}",
                        strconv::quote(&p.file_name)
                    )));
                };
                reply(TransformResult {
                    mapped_output: MappedOutput {
                        text: "export default shared.value;".to_string(),
                        extension: ".ts".to_string(),
                        ..MappedOutput::default()
                    },
                    supplemental: vec![SupplementalOutput {
                        mapped_output: MappedOutput {
                            text: supplemental.to_string(),
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
