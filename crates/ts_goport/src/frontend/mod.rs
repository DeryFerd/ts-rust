//! Go frontend port: scanner, parser, tspath, vfs, tsoptions, module
//! resolution and the program loader. Selected with `GOPORT_FRONTEND=go`
//! (see `program.rs`). The legacy frontend stays the default.

pub mod ast_factory_p2;
pub mod bundled;
pub mod compiler;
pub mod core_ext;
pub mod json;
pub mod module;
pub mod outputpaths;
pub mod packagejson;
pub mod parser;
pub mod prelude;
pub mod scanner;
pub mod semver;
pub mod tsoptions;
pub mod tspath;
pub mod vfs;
