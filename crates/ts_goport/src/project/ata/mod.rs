//! Go package `internal/project/ata`.

pub mod ata;
pub mod discovertypings;
pub mod typesmap;
pub mod validatepackagename;

pub use ata::*;
pub use discovertypings::*;
pub use typesmap::*;
pub use validatepackagename::*;

/// Glob import for ata files: `use crate::project::ata::prelude::*;`.
pub mod prelude {
    pub use super::{ata::*, discovertypings::*, typesmap::*, validatepackagename::*};
    pub use crate::frontend::json_ext::{self, LspAny};
    pub use crate::frontend::{
        core_nodemodules, core_workgroup, json, module, packagejson, semver, tspath, vfs,
    };
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::ls::lsutil;
    pub use crate::lsp::lsproto;
    pub use crate::prelude::*;
    pub use crate::project::logging;
}
