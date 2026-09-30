//! Go package `internal/project`.

pub mod api;
pub mod ata;
pub mod autoimport;
pub mod background;
pub mod checkerpool;
pub mod client;
pub mod compilerhost;
pub mod configfileregistry;
pub mod configfileregistrybuilder;
pub mod dirty;
pub mod extendedconfigcache;
pub mod filechange;
pub mod logging;
pub mod overlayfs;
pub mod ownercache;
pub mod parsecache;
pub mod programcounter;
pub mod project;
pub mod project_stringer_generated;
pub mod projectcollection;
pub mod projectcollectionbuilder;
pub mod refcountcache;
pub mod session;
pub mod snapshot;
pub mod snapshotfs;
pub mod snapshothost;
pub mod watch;

pub use self::api::*;
pub use self::autoimport::*;
pub use self::checkerpool::*;
pub use self::client::*;
pub use self::compilerhost::*;
pub use self::configfileregistry::*;
pub use self::configfileregistrybuilder::*;
pub use self::extendedconfigcache::*;
pub use self::filechange::*;
pub use self::overlayfs::*;
pub use self::ownercache::*;
pub use self::parsecache::*;
pub use self::programcounter::*;
pub use self::project::*;
pub use self::project_stringer_generated::*;
pub use self::projectcollection::*;
pub use self::projectcollectionbuilder::*;
pub use self::refcountcache::*;
pub use self::session::*;
pub use self::snapshot::*;
pub use self::snapshotfs::*;
pub use self::snapshothost::*;
pub use self::watch::*;

/// Glob import for project files: `use crate::project::prelude::*;`.
/// `dirty` is only a module name here: `dirty::Box` stays qualified.
pub mod prelude {
    pub use super::{
        api::*, autoimport::*, checkerpool::*, client::*, compilerhost::*, configfileregistry::*,
        configfileregistrybuilder::*, extendedconfigcache::*, filechange::*, overlayfs::*,
        ownercache::*, parsecache::*, programcounter::*, project::*, project_stringer_generated::*,
        projectcollection::*, projectcollectionbuilder::*, refcountcache::*, session::*,
        snapshot::*, snapshotfs::*, snapshothost::*, watch::*,
    };
    pub use crate::frontend::json_ext::{self, LspAny};
    pub use crate::frontend::{compiler, packagejson, tsoptions, tspath, vfs};
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::locale;
    pub use crate::ls::{self, autoimport, lsconv, lsutil};
    pub use crate::lsp::lsproto;
    pub use crate::prelude::*;
    pub use crate::project::{ata, background, dirty, logging};
    pub use crate::sourcemap;

    // Names that a glob above also exports: the project item wins.
    pub use super::compilerhost::CompilerHost;
    pub use super::extendedconfigcache::{ExtendedConfigCache, ExtendedConfigCacheEntry};
    pub use super::parsecache::ParseCache;
    pub use super::project::Kind;
    pub use super::snapshot::Snapshot;

    // Trait methods on `Option<Rc<dyn Logger>>` and `Option<Rc<LogTree>>`.
    pub use crate::project::logging::{LogTreeMethods as _, Logger as _};
}
