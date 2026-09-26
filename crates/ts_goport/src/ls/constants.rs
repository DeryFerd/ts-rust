//! Port of Go `ls/constants.go`.

use crate::ls::prelude::*;

// Go: ls/constants.go:4 moduleSpecifierResolutionLimit
// PORT: Go untyped int constants; nothing reads them at this commit.
pub const MODULE_SPECIFIER_RESOLUTION_LIMIT: i32 = 100;

// Go: ls/constants.go:5 moduleSpecifierResolutionCacheAttemptLimit
pub const MODULE_SPECIFIER_RESOLUTION_CACHE_ATTEMPT_LIMIT: i32 = 1000;
