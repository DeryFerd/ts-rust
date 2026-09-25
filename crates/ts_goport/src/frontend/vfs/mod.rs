//! Go packages `vfs`, `vfs/osvfs`, `vfs/cachedvfs`, `vfs/wrapvfs`, `vfs/vfsmatch`.
pub mod mod_impl;
pub mod osvfs;
pub mod cachedvfs;
pub mod wrapvfs;
pub mod vfsmatch;
pub use mod_impl::*;
pub use osvfs::*;
pub use cachedvfs::*;
pub use wrapvfs::*;
pub use vfsmatch::*;
