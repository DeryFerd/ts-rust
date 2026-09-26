//! Go `internal/execute`: the `tsc` command line library, incremental
//! build info and `tsc --build`.

pub mod build;
pub mod execute_tsc;
pub mod incremental;
pub mod tsc;
pub mod watcher;
pub mod watchmanager;
