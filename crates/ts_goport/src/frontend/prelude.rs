//! Glob import for frontend port files: `use crate::frontend::prelude::*;`.
//! It adds the frontend modules to the crate prelude. Names that exist in
//! both are picked explicitly below.

pub use crate::prelude::*;
pub use crate::frontend::bundled::*;
pub use crate::frontend::compiler::*;
pub use crate::frontend::json::*;
pub use crate::frontend::module::*;
pub use crate::frontend::packagejson::*;
pub use crate::frontend::parser::*;
pub use crate::frontend::scanner::*;
pub use crate::frontend::semver::*;
pub use crate::frontend::tsoptions::*;
pub use crate::frontend::tspath::*;
pub use crate::frontend::vfs::*;
pub use crate::frontend::core_ext::*;
pub use ts_diagnostics::Message;

// Names that exist in both the crate prelude and the frontend.
pub use crate::frontend::tsoptions::SourceOutputAndProjectReference;
pub use crate::frontend::outputpaths::*;
// Go `internal/symlinks` is ported in modulespecifiers.
pub use crate::modulespecifiers::symlinks::{KnownDirectoryLink, KnownSymlinks};
pub use crate::modulespecifiers::util::get_package_name_from_directory;
