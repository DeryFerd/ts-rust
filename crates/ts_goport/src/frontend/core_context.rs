//! Go `internal/core/context.go`: request ids and checker lifetimes carried
//! in a `Context`.

use crate::frontend::prelude::*;

use crate::gostd::context::{self, Context, ContextKey};

// Go: core/context.go:7 key
// Go: core/context.go:10 requestIDKey
pub static REQUEST_ID_KEY: ContextKey<String> = ContextKey::new("requestIDKey");

// Go: core/context.go:11 checkerLifetimeKey
pub static CHECKER_LIFETIME_KEY: ContextKey<CheckerLifetime> =
    ContextKey::new("checkerLifetimeKey");

// Go: core/context.go:14 WithRequestID
pub fn with_request_id(ctx: &Context, id: &str) -> Context {
    context::with_value(ctx, &REQUEST_ID_KEY, id.to_string())
}

// Go: core/context.go:18 GetRequestID
pub fn get_request_id(ctx: &Context) -> String {
    if let Some(id) = ctx.value(&REQUEST_ID_KEY) {
        return (*id).clone();
    }
    String::new()
}

// Go: core/context.go:25 CheckerLifetime
/// Go `type CheckerLifetime int`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CheckerLifetime(pub i32);

impl CheckerLifetime {
    // Go: core/context.go:28 CheckerLifetimeTemporary
    pub const TEMPORARY: CheckerLifetime = CheckerLifetime(0);
    // Go: core/context.go:29 CheckerLifetimeDiagnostics
    pub const DIAGNOSTICS: CheckerLifetime = CheckerLifetime(1);
    // Go: core/context.go:30 CheckerLifetimeAPI
    pub const API: CheckerLifetime = CheckerLifetime(2);
}

// Go: core/context.go:33 WithCheckerLifetime
pub fn with_checker_lifetime(ctx: &Context, lifetime: CheckerLifetime) -> Context {
    context::with_value(ctx, &CHECKER_LIFETIME_KEY, lifetime)
}

// Go: core/context.go:37 GetCheckerLifetime
pub fn get_checker_lifetime(ctx: &Context) -> CheckerLifetime {
    if let Some(lifetime) = ctx.value(&CHECKER_LIFETIME_KEY) {
        return *lifetime;
    }
    CheckerLifetime::TEMPORARY
}
