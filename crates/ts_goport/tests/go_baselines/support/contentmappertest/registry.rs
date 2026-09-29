//! Go: internal/testutil/contentmappertest/registry.go (tsgo#4712).

use super::component::ComponentHandler;
use super::diagnostic_code_collision::DiagnosticCodeCollisionHandler;
use super::duplicate::DuplicateHandler;
use super::dynamic_verbatim::{DynamicVerbatimHandler, ProjectLifecycle};
use super::editing::{PrefixedSupplementalHandler, UnmappedFoldingHandler};
use super::failing::FailingHandler;
use super::lisp::LispHandler;
use super::prelude::*;
use super::supplemental::SupplementalHandler;
use super::supplemental_diagnostics::SupplementalDiagnosticsHandler;
use super::supplemental_globals::SupplementalGlobalsHandler;
use super::supplemental_module::SupplementalModuleHandler;
use super::synthesizing::SynthesizingHandler;
use super::transforming::Handler;
use super::verbatim::{ModuleVerbatimHandler, VerbatimHandler};

// Go: registry.go:10
pub const TRANSFORMING_MAPPER: &str = "compiler-test-mapper";
pub const VERBATIM_MAPPER: &str = "verbatim-mapper";
pub const MODULE_VERBATIM_MAPPER: &str = "module-verbatim-mapper";
pub const DYNAMIC_VERBATIM_MAPPER: &str = "dynamic-verbatim-mapper";
pub const DIAGNOSTIC_CODE_COLLISION_MAPPER: &str = "diagnostic-code-collision-mapper";
pub const FAILING_MAPPER: &str = "failing-mapper";
pub const SYNTHESIZING_MAPPER: &str = "synthesizing-mapper";
pub const COMPONENT_MAPPER: &str = "component-mapper";
pub const DUPLICATE_MAPPER: &str = "duplicate-mapper";
pub const LISP_MAPPER: &str = "lisp-mapper";
pub const SUPPLEMENTAL_MAPPER: &str = "supplemental-mapper";
pub const SUPPLEMENTAL_DIAGNOSTICS_MAPPER: &str = "supplemental-diagnostics-mapper";
pub const SUPPLEMENTAL_GLOBALS_MAPPER: &str = "supplemental-globals-mapper";
pub const SUPPLEMENTAL_MODULE_MAPPER: &str = "supplemental-module-mapper";
pub const PREFIXED_SUPPLEMENTAL_MAPPER: &str = "prefixed-supplemental-mapper";
pub const UNMAPPED_FOLDING_MAPPER: &str = "unmapped-folding-mapper";

// Go: registry.go:29 handlerConstructor, registry.go:31 mapperHandlers
// PORT: the Go map of constructors is a match on the command name. `None`
// is a name that the map does not have.
fn new_mapper_handler(
    name: &str,
    lifecycle: Option<&Arc<ProjectLifecycle>>,
) -> Option<Box<dyn MapperHandler>> {
    let handler: Box<dyn MapperHandler> = match name {
        TRANSFORMING_MAPPER => Box::new(Handler::default()),
        VERBATIM_MAPPER => Box::new(VerbatimHandler),
        MODULE_VERBATIM_MAPPER => Box::new(ModuleVerbatimHandler),
        DYNAMIC_VERBATIM_MAPPER => Box::new(DynamicVerbatimHandler {
            verbatim_handler: VerbatimHandler,
            lifecycle: lifecycle.cloned(),
        }),
        DIAGNOSTIC_CODE_COLLISION_MAPPER => Box::new(DiagnosticCodeCollisionHandler),
        FAILING_MAPPER => Box::new(FailingHandler),
        SYNTHESIZING_MAPPER => Box::new(SynthesizingHandler),
        COMPONENT_MAPPER => Box::new(ComponentHandler),
        DUPLICATE_MAPPER => Box::new(DuplicateHandler),
        LISP_MAPPER => Box::new(LispHandler),
        SUPPLEMENTAL_MAPPER => Box::new(SupplementalHandler),
        SUPPLEMENTAL_DIAGNOSTICS_MAPPER => Box::new(SupplementalDiagnosticsHandler),
        SUPPLEMENTAL_GLOBALS_MAPPER => Box::new(SupplementalGlobalsHandler),
        SUPPLEMENTAL_MODULE_MAPPER => Box::new(SupplementalModuleHandler),
        PREFIXED_SUPPLEMENTAL_MAPPER => Box::new(PrefixedSupplementalHandler),
        UNMAPPED_FOLDING_MAPPER => Box::new(UnmappedFoldingHandler),
        _ => return None,
    };
    Some(handler)
}

// Go: registry.go:50 handlerForMapper
pub(super) fn handler_for_mapper(
    command: &[String],
    lifecycle: Option<&Arc<ProjectLifecycle>>,
) -> Result<Box<dyn MapperHandler>, GoError> {
    let Some(name) = command.first() else {
        return Err(errors::new("contentmappertest: empty mapper command"));
    };
    let Some(handler) = new_mapper_handler(name, lifecycle) else {
        // Go `fmt.Errorf("... %v", command)`: `%v` of a `[]string`.
        return Err(errors::new(format!(
            "contentmappertest: unknown mapper command [{}]",
            command.join(" ")
        )));
    };
    Ok(handler)
}
