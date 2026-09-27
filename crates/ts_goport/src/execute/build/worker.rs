//! PORT: not in Go. A stub of the removed build worker.
//!
//! `tsc -b` compiles every project in this process, as Go does
//! (build_task.rs), so no build starts a `--build-worker` process. The bins
//! `goport_build`, `tsgo` and `goport_watch` still have their worker entry,
//! and execute/watcher.rs imports `SystemParseConfigHost` from here. The
//! owner of those files removes both with
//! `target/continuation-r97-goport/mp2/bins.patch`, which also deletes this
//! file and `vfs::CachedFsState`. Until then, a worker entry that a person
//! runs by hand reaches `compile_and_emit_worker`, which reports the worker
//! as unported code, so the bin exits `EXIT_UNPORTED`.

use crate::execute::tsc::compile::{CommandLineTesting, System};
use crate::frontend::vfs::CachedFsState;
use crate::prelude::*;

pub use crate::execute::tsc::compile::SystemParseConfigHost;

/// The first argument of the worker entry of the bins.
pub const BUILD_WORKER_FLAG: &str = "--build-worker";

/// The result of a worker. `compile_and_emit_worker` never makes one.
pub struct WorkerCompileResult(());

/// Reads nothing: no build sends a worker its cached file system.
pub fn read_worker_fs_cache(_input: &mut dyn std::io::Read) -> Result<CachedFsState, String> {
    Ok(CachedFsState::default())
}

/// An empty line. Only `compile_and_emit_worker` would call it back.
pub fn marshal_worker_program_fs_cache(_state: &CachedFsState) -> String {
    String::new()
}

/// The removed worker compile: it reports the worker as unported code.
pub fn compile_and_emit_worker(
    _sys: Rc<dyn System>,
    _config: &str,
    _build_command_line: &[String],
    _fs_cache: &CachedFsState,
    _report_program_fs_cache: &mut dyn FnMut(&CachedFsState),
    _testing: Option<Rc<dyn CommandLineTesting>>,
) -> WorkerCompileResult {
    unported!("build worker")
}

/// An empty line. There is no result to write (see `WorkerCompileResult`).
pub fn marshal_worker_compile_result(_result: &WorkerCompileResult) -> String {
    String::new()
}
