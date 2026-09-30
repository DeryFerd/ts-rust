//! Go: internal/testutil/contentmappertest/protocol.go (tsgo#4712).

use super::prelude::*;

/// Go `(any, error)` of `ipc.Handler.HandleRequest`.
pub type HandlerResult = Result<Option<Box<dyn AnyValue>>, GoError>;

/// A test mapper: the Go `ipc.Handler` values of this package.
///
/// PORT: every Go handler here embeds `noNotifications` (or wraps a handler
/// that does), so `ServerHandler` answers each notification with nil. Go
/// checks a wrapped handler for `projectLifecycleHandler` with a type
/// assertion; here that is `project_lifecycle`. A handler is `Send`,
/// because it moves to the thread that serves its connection.
pub trait MapperHandler: Send {
    fn handle_request(&self, ctx: &Context, method: &str, params: JsonValue) -> HandlerResult;

    /// Go `h.(projectLifecycleHandler)`: `None` when the handler has no
    /// project lifecycle methods.
    fn project_lifecycle(&self) -> Option<&dyn ProjectLifecycleHandler> {
        None
    }
}

// Go: protocol.go:14 noNotifications
/// The `ipc.Handler` of a mapper connection: the mapper handler, with no
/// notifications.
pub(super) struct ServerHandler(pub Box<dyn MapperHandler>);

impl ipc::Handler for ServerHandler {
    fn handle_request(&self, ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        self.0.handle_request(ctx, method, params)
    }

    // Go: protocol.go:16 noNotifications.HandleNotification
    fn handle_notification(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: JsonValue,
    ) -> Result<(), GoError> {
        Ok(())
    }
}

/// Go `return result, nil`.
pub fn reply(result: impl AnyValue) -> HandlerResult {
    Ok(Some(Box::new(result)))
}

/// Go `var p T; json.Unmarshal(params, &p)`.
pub fn unmarshal_params<T: ts_goport::frontend::json::UnmarshalerFrom + Default>(
    params: &JsonValue,
) -> Result<T, GoError> {
    let mut p = T::default();
    json_unmarshal(&params.0, &mut p, &[]).map_err(errors::from_value)?;
    Ok(p)
}

/// Go `fmt.Errorf("contentmappertest: unexpected method %q", method)`.
pub fn unexpected_method(method: &str) -> GoError {
    errors::new(format!(
        "contentmappertest: unexpected method {}",
        strconv::quote(method)
    ))
}

// Go: protocol.go:20 initializeResult
pub fn initialize_result(source: &str) -> InitializeResult {
    InitializeResult {
        position_encoding: PositionEncoding::UTF8,
        diagnostic_source: source.to_string(),
    }
}

// Go: protocol.go:27 identityMappedOutput
pub fn identity_mapped_output(content: &str) -> Result<MappedOutput, GoError> {
    let length = content.len() as i32;
    let mappings = spanmap::new(&[Segment {
        virtual_end: length,
        original_end: length,
        kind: Kind::VERBATIM,
        features: Feature::ALL,
        ..Segment::default()
    }])
    .marshal()?;
    Ok(MappedOutput {
        text: content.to_string(),
        extension: ".ts".to_string(),
        mappings: JsonValue(mappings),
        ..MappedOutput::default()
    })
}

// Go: protocol.go:40 staticProjectHandler
pub(super) struct StaticProjectHandler {
    pub handler: Box<dyn MapperHandler>,
}

// Go: protocol.go:42 projectLifecycleHandler
pub trait ProjectLifecycleHandler {
    fn open_project(&self, params: &OpenProjectParams) -> Result<(), GoError>;
    fn close_project(&self, params: &CloseProjectParams);
}

impl MapperHandler for StaticProjectHandler {
    // Go: protocol.go:47 staticProjectHandler.HandleRequest
    fn handle_request(&self, ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_OPEN_PROJECT => {
                let p: OpenProjectParams = unmarshal_params(&params)?;
                if let Some(handler) = self.handler.project_lifecycle() {
                    handler.open_project(&p)?;
                }
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
                reply(OpenProjectResult {
                    option_diagnostics: diagnostics,
                    ..OpenProjectResult::default()
                })
            }
            contentmapper::METHOD_CLOSE_PROJECT => {
                let p: CloseProjectParams = unmarshal_params(&params)?;
                if let Some(handler) = self.handler.project_lifecycle() {
                    handler.close_project(&p);
                }
                Ok(None)
            }
            _ => self.handler.handle_request(ctx, method, params),
        }
    }
}
