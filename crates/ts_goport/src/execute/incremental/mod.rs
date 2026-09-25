//! Go `internal/execute/incremental`.

pub mod affected_files;
pub mod build_info;
pub mod build_info_to_snapshot;
pub mod checker_access;
pub mod emit_files;
pub mod hash;
pub mod incremental;
pub mod program;
pub mod program_to_snapshot;
pub mod reference_map;
pub mod snapshot;
pub mod snapshot_to_build_info;

pub use build_info::BuildInfo;
pub use hash::compute_hash;
