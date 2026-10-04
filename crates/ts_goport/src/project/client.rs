//! Go `internal/project/client.go`.
//!
//! PORT: Go `Client` is an interface; here it is a trait used as
//! `Rc<dyn Client>` (a Go nil client is `None` where Go checks for nil).
//! The LSP server (w6) implements it on the dispatch thread.

use crate::project::prelude::*;

/// PORT: the future of a client call from a snapshot task.
pub type ClientCall<'a> =
    std::pin::Pin<Box<dyn std::future::Future<Output = Result<(), GoError>> + 'a>>;

// Go: project/client.go:11 Client
// PORT: `watchers []*lsproto.FileSystemWatcher` is `&[..]` (PORTING
// "Types"). `params *lsproto.PublishDiagnosticsParams` is passed by value,
// because the server moves it into the outgoing notification. `args ...any`
// is `Vec<String>` (built with `args![..]`).
pub trait Client {
    fn watch_files(
        &self,
        ctx: &Context,
        id: WatcherID,
        watchers: &[lsproto::FileSystemWatcher],
    ) -> Result<(), GoError>;
    fn unwatch_files(&self, ctx: &Context, id: WatcherID) -> Result<(), GoError>;
    /// PORT: `WatchFiles` from a snapshot task (`Session::update_watches`).
    /// The LSP server waits for the client's reply without blocking while a
    /// request is in flight (`background::race`). The default calls
    /// `watch_files`.
    fn watch_files_async<'a>(
        &'a self,
        ctx: &Context,
        id: WatcherID,
        watchers: &[lsproto::FileSystemWatcher],
    ) -> ClientCall<'a> {
        let result = self.watch_files(ctx, id, watchers);
        Box::pin(std::future::ready(result))
    }
    /// PORT: `UnwatchFiles` from a snapshot task, as `watch_files_async`.
    fn unwatch_files_async<'a>(&'a self, ctx: &Context, id: WatcherID) -> ClientCall<'a> {
        let result = self.unwatch_files(ctx, id);
        Box::pin(std::future::ready(result))
    }
    // tsgo#4712
    fn register_content_mapper_extensions(
        &self,
        ctx: &Context,
        extensions: &[String],
    ) -> Result<(), GoError>;
    fn refresh_diagnostics(&self, ctx: &Context) -> Result<(), GoError>;
    fn publish_diagnostics(
        &self,
        ctx: &Context,
        params: lsproto::PublishDiagnosticsParams,
    ) -> Result<(), GoError>;
    fn refresh_inlay_hints(&self, ctx: &Context) -> Result<(), GoError>;
    fn refresh_code_lens(&self, ctx: &Context) -> Result<(), GoError>;
    fn progress_start(&self, message: &'static crate::diagnostics::Message, args: Vec<String>);
    fn progress_finish(&self, message: &'static crate::diagnostics::Message, args: Vec<String>);
    fn send_telemetry(
        &self,
        ctx: &Context,
        telemetry: lsproto::TelemetryEvent,
    ) -> Result<(), GoError>;
    fn is_active(&self) -> bool;
    // SetLocale updates the locale used for diagnostic messages.
    fn set_locale(&self, locale: &str);
    // GetLocale returns the current display locale for diagnostic messages.
    fn get_locale(&self) -> locale::Locale;
}
