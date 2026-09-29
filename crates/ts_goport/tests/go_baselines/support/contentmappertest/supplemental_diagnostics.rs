//! Go: internal/testutil/contentmappertest/supplemental_diagnostics.go (tsgo#4712).

use super::prelude::*;

// Go: supplemental_diagnostics.go:13 supplementalDiagnosticsHandler
pub(super) struct SupplementalDiagnosticsHandler;

impl MapperHandler for SupplementalDiagnosticsHandler {
    // Go: supplemental_diagnostics.go:15 supplementalDiagnosticsHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let p: TransformParams = unmarshal_params(&params)?;
                const PREFIX: &str = "missingSupplementalGlobal;\n";
                let mappings = spanmap::new(&[Segment {
                    virtual_start: PREFIX.len() as i32,
                    virtual_end: (PREFIX.len() + p.content.len()) as i32,
                    original_end: p.content.len() as i32,
                    kind: Kind::VERBATIM,
                    features: Feature::ALL,
                    ..Segment::default()
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
