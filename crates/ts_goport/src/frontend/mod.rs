//! Go frontend port: scanner, parser, tspath, vfs, tsoptions, module
//! resolution and the program loader. Selected with `GOPORT_FRONTEND=go`
//! (see `program.rs`). The legacy frontend stays the default.

pub mod prelude;
pub mod core_ext;
pub mod tspath;
pub mod vfs;
pub mod bundled;
pub mod json;
pub mod semver;
pub mod packagejson;
pub mod scanner;
pub mod parser;
pub mod ast_factory_p2;
pub mod tsoptions;
pub mod module;
pub mod compiler;
pub mod outputpaths;
