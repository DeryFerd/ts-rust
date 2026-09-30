//! Go: internal/testutil/contentmappertest (tsgo#4712).
//!
//! Package contentmappertest provides realistic content mapper implementations used by tests.
//!
//! One Rust file per Go file. Users: the compiler runner (`CompileFilesEx`
//! serves the mappers of a test in-process), and the tsc, project, LSP and
//! auto-import tests of tsgo#4712.
//!
//! PORT: Go serves each spawned mapper with `ipc.NewAsyncConn(server,
//! handler).Run` on a goroutine over `net.Pipe`. Here the pipe is a Unix
//! socket pair, and the mapper side runs on its own thread. The connection
//! holds its handler in an `Rc` on that thread, so the mapper handlers are
//! `Send` values (`MapperHandler`) that move there (see spawner.rs).

mod component;
mod diagnostic_code_collision;
mod duplicate;
mod duplicate_projection;
mod dynamic_verbatim;
mod editing;
mod failing;
mod hoisting;
mod lisp;
mod manifest;
mod mapper_test;
mod protocol;
mod registry;
mod spawner;
mod supplemental;
mod supplemental_diagnostics;
mod supplemental_globals;
mod supplemental_module;
mod synthesizing;
mod transforming;
mod verbatim;

// The re-exports keep the whole exported API of the Go package. Some items
// have no user in the ported tests, so `unused_imports` is allowed on the
// lines that hold them.
#[allow(unused_imports)]
pub use dynamic_verbatim::ProjectLifecycle;
pub use manifest::{PACKAGE_NAME, package_json};
#[allow(unused_imports)]
pub use protocol::{HandlerResult, MapperHandler, ProjectLifecycleHandler};
#[allow(unused_imports)]
pub use registry::{
    COMPONENT_MAPPER, DIAGNOSTIC_CODE_COLLISION_MAPPER, DUPLICATE_MAPPER,
    DUPLICATE_PROJECTION_MAPPER, DYNAMIC_VERBATIM_MAPPER, FAILING_MAPPER, HOISTING_MAPPER,
    LISP_MAPPER, MODULE_VERBATIM_MAPPER, PREFIXED_SUPPLEMENTAL_MAPPER,
    SUPPLEMENTAL_DIAGNOSTICS_MAPPER, SUPPLEMENTAL_GLOBALS_MAPPER, SUPPLEMENTAL_MAPPER,
    SUPPLEMENTAL_MODULE_MAPPER, SYNTHESIZING_MAPPER, TRANSFORMING_MAPPER, UNMAPPED_FOLDING_MAPPER,
    VERBATIM_MAPPER,
};
#[allow(unused_imports)]
pub use spawner::{new_spawner, new_spawner_with_project_lifecycle, serve};
#[allow(unused_imports)]
pub use transforming::{DECLARED_OPTIONS, Handler};

/// The imports of the files of this package.
mod prelude {
    pub use std::sync::Arc;

    pub use ts_goport::contentmapper::{
        self, CloseProjectParams, DiagnosticDirectivePolicy, DiagnosticDirectives,
        InitializeResult, MappedOutput, OpenProjectParams, OpenProjectResult,
        OptionDiagnosticResult, PositionEncoding, SupplementalOutput, TransformParams,
        TransformResult, UnusedExpectDirectiveDiagnostic,
    };
    pub use ts_goport::frontend::json::json_unmarshal;
    pub use ts_goport::frontend::json_ext::{AnyValue, JsonValue};
    pub use ts_goport::gostd::{Context, GoError, errors, strconv};
    pub use ts_goport::ipc;
    pub use ts_goport::spanmap::{self, Feature, Kind, Segment, SpanMap};

    pub use super::protocol::{
        HandlerResult, MapperHandler, ProjectLifecycleHandler, identity_mapped_output,
        initialize_result, reply, unexpected_method, unmarshal_params,
    };
}
