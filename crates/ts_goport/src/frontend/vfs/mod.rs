//! Go packages `vfs`, `vfs/osvfs`, `vfs/cachedvfs`, `vfs/wrapvfs`, `vfs/vfsmatch`.
pub mod cachedvfs;
pub mod mod_impl;
pub mod osvfs;
pub mod vfsmatch;
pub mod wrapvfs;
pub use cachedvfs::*;
pub use mod_impl::*;
pub use osvfs::*;
pub use vfsmatch::*;
pub use wrapvfs::*;
