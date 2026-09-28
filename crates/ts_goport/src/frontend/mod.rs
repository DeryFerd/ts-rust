//! Go frontend port: scanner, parser, tspath, vfs, tsoptions, module
//! resolution and the program loader. Selected with `GOPORT_FRONTEND=go`
//! (see `program.rs`). The legacy frontend stays the default.

pub mod ast_factory_p2;
pub mod bundled;
pub mod compiler;
pub mod core_ext;
pub mod json;
pub mod module;
pub mod nativepath;
pub mod outputpaths;
pub mod packagejson;
pub mod parser;
pub mod prelude;
pub mod scanner;
pub mod semver;
pub mod tsoptions;
pub mod tspath;
pub mod vfs;
// Language-service support files. Not glob-exported in the frontend prelude.
pub mod core_bfs;
pub mod core_binarysearch;
pub mod core_context;
pub mod core_ls_ext;
pub mod core_nodemodules;
pub mod core_textchange;
pub mod core_workgroup;
pub mod json_ext;
pub mod stringutil_ls;
