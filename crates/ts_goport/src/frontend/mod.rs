//! Go frontend port: scanner, parser, tspath, vfs, tsoptions, module
//! resolution and the program loader.
//!
//! The modules that come from `goport_util` below are declared in
//! `src/goport_util_root.rs`.

pub mod ast_factory_p2;
pub use goport_util::frontend::bundled;
pub mod compiler;
pub mod core_ext;
pub use goport_util::frontend::json;
pub mod module;
pub use goport_util::frontend::{nativepath, osutil};
pub mod outputpaths;
pub mod packagejson;
pub mod parser;
pub mod prelude;
pub mod scanner;
pub use goport_util::frontend::semver;
pub mod tsoptions;
pub use goport_util::frontend::tspath;
pub use goport_util::frontend::vfs;
// Language-service support files. Not glob-exported in the frontend prelude.
pub use goport_util::frontend::core_bfs;
pub use goport_util::frontend::core_binarysearch;
pub use goport_util::frontend::core_context;
pub mod core_ls_ext;
pub use goport_util::frontend::core_nodemodules;
pub mod core_textchange;
pub use goport_util::frontend::core_workgroup;
pub use goport_util::frontend::json_ext;
pub use goport_util::frontend::stringutil_ls;
