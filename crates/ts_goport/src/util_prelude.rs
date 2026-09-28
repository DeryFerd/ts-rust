//! `crate::prelude` of `goport_util`: the names of the `ts_goport` prelude
//! that util files use. Util files import it as `use crate::prelude::*;`.

pub use crate::core::*;
pub use crate::diag;
pub use crate::go_assert;
pub use crate::scanner_util::*;
pub use crate::unported;
pub use indexmap::{IndexMap, IndexSet};
pub use rustc_hash::{FxHashMap, FxHashSet};
pub use std::cell::RefCell;
pub use std::rc::Rc;
pub use ts_ast::SyntaxKind;
