//! Go runtime and standard library pieces used by the language-service port
//! (`context`, `errors`, `errgroup`, `slices`, `net/url`, `net/netip`,
//! `strconv`, `time` timers, `regexp` with its `unicode` tables,
//! `golang.org/x/text/collate` and `unicode/norm`, and the dispatch-thread
//! `go` queue). See PORTING.md "Go runtime".

pub mod collate;
pub mod context;
pub mod errgroup;
pub mod errors;
pub mod local;
pub mod netip;
pub mod norm;
pub mod regexp;
pub mod slices;
pub mod strconv;
pub mod timer;
pub mod unicode_tables;
pub mod url;

pub use context::Context;
pub use errors::GoError;
