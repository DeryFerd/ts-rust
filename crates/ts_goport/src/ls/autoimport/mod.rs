//! Go package `internal/ls/autoimport`.

pub mod aliasresolver;
pub mod export;
pub mod extract;
pub mod fix;
pub mod import_adder;
pub mod index;
pub mod registry;
pub mod specifiers;
pub mod util;
pub mod view;

pub use aliasresolver::*;
pub use export::*;
pub use extract::*;
pub use fix::*;
pub use import_adder::*;
pub use index::*;
pub use registry::*;
pub use specifiers::*;
pub use util::*;
pub use view::*;

/// Glob import for autoimport files: `use crate::ls::autoimport::prelude::*;`.
pub mod prelude {
    pub use super::{
        aliasresolver::*, export::*, extract::*, fix::*, import_adder::*, index::*, registry::*,
        specifiers::*, util::*, view::*,
    };
    pub use crate::astnav;
    pub use crate::frontend::json_ext::{self, LspAny};
    pub use crate::frontend::scanner::scanner_ls;
    pub use crate::frontend::{
        compiler, core_ls_ext, module, packagejson, stringutil_ls, tsoptions, tspath, vfs,
    };
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::locale;
    pub use crate::ls::{change, lsconv, lsutil};
    pub use crate::lsp::lsproto;
    pub use crate::modulespecifiers;
    pub use crate::prelude::*;
    pub use crate::program::ls_program;
    pub use crate::project::{dirty, logging};
}
