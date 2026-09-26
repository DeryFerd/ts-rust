//! Go package `internal/ls/lsutil`.

pub mod asi;
pub mod children;
pub mod completednode;
pub mod formatcodeoptions;
pub mod organizeimports;
pub mod symbol_display;
pub mod userpreferences;
pub mod utilities;

pub use asi::*;
pub use children::*;
pub use completednode::*;
pub use formatcodeoptions::*;
pub use organizeimports::*;
pub use symbol_display::*;
pub use userpreferences::*;
pub use utilities::*;

/// Glob import for lsutil files: `use crate::ls::lsutil::prelude::*;`.
pub mod prelude {
    pub use super::{
        asi::*, children::*, completednode::*, formatcodeoptions::*, organizeimports::*,
        symbol_display::*, userpreferences::*, utilities::*,
    };
    pub use crate::astnav;
    pub use crate::frontend::json_ext::{self, LspAny};
    pub use crate::frontend::scanner::scanner_ls;
    pub use crate::frontend::{compiler, tspath, vfs};
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::locale;
    pub use crate::lsp::lsproto;
    pub use crate::modulespecifiers;
    pub use crate::prelude::*;

    // Names that the crate prelude also exports. The package item wins.
    pub use super::organizeimports::get_external_module_name;
    pub use super::symbol_display::is_deprecated_declaration;
    pub use super::utilities::is_non_contextual_keyword;
}
