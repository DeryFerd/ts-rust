//! Go: internal/testutil/contentmappertest/dynamic_verbatim.go (tsgo#4712).

use std::sync::atomic::{AtomicI32, Ordering};

use ts_goport::frontend::tspath::{combine_paths, get_directory_path};

use super::prelude::*;
use super::verbatim::VerbatimHandler;

// Go: dynamic_verbatim.go:14 ProjectLifecycle
// ProjectLifecycle records mapper project protocol calls.
// PORT: Go `atomic.Int32` fields; share it as `Arc<ProjectLifecycle>`.
#[derive(Debug, Default)]
pub struct ProjectLifecycle {
    pub opens: AtomicI32,
    pub closes: AtomicI32,
}

// Go: dynamic_verbatim.go:19 dynamicVerbatimHandler
// PORT: Go embeds `verbatimHandler`; here it is the field
// `verbatim_handler`. Go `*ProjectLifecycle` is an `Option` (nil is `None`).
pub(super) struct DynamicVerbatimHandler {
    pub verbatim_handler: VerbatimHandler,
    pub lifecycle: Option<Arc<ProjectLifecycle>>,
}

impl MapperHandler for DynamicVerbatimHandler {
    // Go: dynamic_verbatim.go:24 dynamicVerbatimHandler.HandleRequest
    fn handle_request(&self, ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_OPEN_PROJECT => {
                if let Some(lifecycle) = &self.lifecycle {
                    lifecycle.opens.fetch_add(1, Ordering::SeqCst);
                }
                let p: OpenProjectParams = unmarshal_params(&params)?;
                let identity = format!(
                    "{}:{}",
                    p.config_file_name,
                    String::from_utf8_lossy(&p.options.0)
                );
                let mut diagnostics = Vec::new();
                if p.options.0 == br#"{"plugins":[{"name":1}]}"# {
                    diagnostics = vec![OptionDiagnosticResult {
                        path: vec![
                            JsonValue(br#""plugins""#.to_vec()),
                            JsonValue(b"0".to_vec()),
                            JsonValue(br#""name""#.to_vec()),
                        ],
                        message_text: "Option 'name' requires a string.".to_string(),
                        code: 123,
                    }];
                }
                let mut watch_directory = get_directory_path(&p.config_file_name);
                if watch_directory.is_empty() {
                    watch_directory = "/".to_string();
                }
                return reply(OpenProjectResult {
                    config_identity: identity,
                    watched_files: vec![combine_paths(&watch_directory, &["mapper.config.json"])],
                    option_diagnostics: diagnostics,
                });
            }
            contentmapper::METHOD_CLOSE_PROJECT => {
                if let Some(lifecycle) = &self.lifecycle {
                    lifecycle.closes.fetch_add(1, Ordering::SeqCst);
                }
                return Ok(None);
            }
            contentmapper::METHOD_TRANSFORM => {
                let p: TransformParams = unmarshal_params(&params)?;
                if p.project_handle.is_empty() {
                    return Err(errors::new(
                        "content mapper transform requires a project handle",
                    ));
                }
            }
            _ => {}
        }
        self.verbatim_handler.handle_request(ctx, method, params)
    }
}
