//! Glob import for frontend port files: `use crate::frontend::prelude::*;`.
//! It adds the frontend modules to the crate prelude. Names that exist in
//! both are picked explicitly below.

pub use crate::diagnostics::Message;
pub use crate::frontend::bundled::*;
pub use crate::frontend::compiler::*;
pub use crate::frontend::core_ext::*;
pub use crate::frontend::json::*;
pub use crate::frontend::module::*;
pub use crate::frontend::packagejson::*;
pub use crate::frontend::parser::*;
pub use crate::frontend::scanner::*;
pub use crate::frontend::semver::*;
pub use crate::frontend::tsoptions::*;
pub use crate::frontend::tspath::*;
pub use crate::frontend::vfs::*;
pub use crate::prelude::*;

// Names that exist in both the crate prelude and the frontend.
pub use crate::frontend::outputpaths::*;
pub use crate::frontend::tsoptions::SourceOutputAndProjectReference;
// Go `internal/symlinks` is ported in modulespecifiers.
pub use crate::frontend::compiler::{get_source_files_to_emit, source_file_may_be_emitted};
pub use crate::frontend::module::types;
pub use crate::frontend::parser::jsdoc;
pub use crate::frontend::scanner::utilities;
pub use crate::modulespecifiers::symlinks::{KnownDirectoryLink, KnownSymlinks};
pub use crate::modulespecifiers::util::get_package_name_from_directory;
pub use crate::program::{get_default_resolution_mode_for_file, get_mode_for_usage_location};
