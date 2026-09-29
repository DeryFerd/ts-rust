//! Go: internal/testutil/contentmappertest/diagnostic_code_collision.go (tsgo#4712).

use ts_goport::diag;

use super::prelude::*;

// Go: diagnostic_code_collision.go:13 diagnosticCodeCollisionHandler
pub(super) struct DiagnosticCodeCollisionHandler;

impl MapperHandler for DiagnosticCodeCollisionHandler {
    // Go: diagnostic_code_collision.go:15 diagnosticCodeCollisionHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let p: TransformParams = unmarshal_params(&params)?;
                let mapped_output = identity_mapped_output(&p.content)?;
                // Go `strings.Index`: -1 when absent.
                let start = p.content.find("foo").map_or(-1, |i| i as i32);
                reply(TransformResult {
                    mapped_output,
                    diagnostics: vec![contentmapper::Diagnostic {
                        message_text: "Mapper diagnostic with a colliding code.".to_string(),
                        start,
                        length: "foo".len() as i32,
                        code: diag::Function_must_have_an_explicit_return_type_annotation_with_isolatedDeclarations
                            .code() as i32,
                    }],
                    ..TransformResult::default()
                })
            }
            _ => Err(unexpected_method(method)),
        }
    }
}
