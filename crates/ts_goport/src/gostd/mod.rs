//! Go runtime and standard library pieces used by the language-service port
//! (`context`, `errors`, `errgroup`, `slices`, `net/url`, `strconv`, `time`
//! timers, `regexp`, `golang.org/x/text/collate`, and the dispatch-thread `go`
//! queue). See PORTING.md "Go runtime".

pub mod collate;
pub mod context;
pub mod errgroup;
pub mod errors;
pub mod local;
pub mod regexp;
pub mod slices;
pub mod strconv;
pub mod timer;
pub mod url;

pub use context::Context;
pub use errors::GoError;
