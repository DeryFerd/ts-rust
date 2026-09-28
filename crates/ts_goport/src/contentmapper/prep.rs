//! Bump B wave 3 prep: stand-ins for the tsgo#4712 parts that other bump B
//! lanes own (queues-int12 `ownership.tsv`). The contentmapper package
//! compiles and runs its Go unit tests against these until wave 3 wires it
//! into the program. Wave 3 deletes this file and points the package prelude
//! back at the real items:
//!
//! - `ipc`: the api lane moves `api/conn*.rs`, `protocol*.rs` and
//!   `transport*.rs` to `crate::ipc`. Until then `ipc` re-exports them from
//!   `crate::api`. One known difference from Go `ipc` at pin B: an error
//!   response reads "api: remote error", not "ipc: remote error".
//! - `ast`: `crate::ast` plus the syntax lane's `MappedDiagnosticDirective`
//!   and `MappedDiagnosticDirectivePolicy` (Go `ast/ast.go`) and
//!   `new_external_diagnostic` (Go `ast/diagnostic.go`).
//! - `ExternalDiagnostic`: the Go `*ast.Diagnostic` that
//!   `NewExternalDiagnostic` makes. `crate::core::Diagnostic` cannot hold
//!   free message text or a source yet. Wave 3 uses `crate::core::Diagnostic`.
//! - `locale_string`: the config lane's `Locale::string` (Go `Locale.String`).
//!
//! Code that needs a missing part with no stand-in is under
//! `cfg(goport_wave3)`, which is never set: Go `SourceFile.SetContentMapperInfo`
//! and its accessors, and `SetDiagnostics` with external diagnostics
//! (`transform.rs`).

use crate::prelude::*;

use crate::locale::{self, Locale};

/// Go package `ipc` (tsgo#4712 moves the api connection code there).
/// PORT: re-exports of the api items until the api lane moves them.
pub mod ipc {
    pub use crate::api::{
        AsyncConn, Conn, Handler, Message, Protocol, ReadWriteCloser, new_async_conn,
        new_async_conn_with_protocol, new_jsonrpc_protocol,
    };
}

/// Go package `ast`: `crate::ast` plus the tsgo#4712 syntax lane items.
pub mod ast {
    pub use super::{
        MappedDiagnosticDirective, MappedDiagnosticDirectivePolicy, new_external_diagnostic,
    };
    pub use crate::ast::*;
}

// Go: ast/ast.go:2615 MappedDiagnosticDirectivePolicy
crate::flags_macros::go_enum!(MappedDiagnosticDirectivePolicy, u8 {
    IGNORE = 0;
    EXPECT = 1;
});

// Go: ast/ast.go:2622 MappedDiagnosticDirective
#[derive(Clone, Debug, Default, PartialEq)]
pub struct MappedDiagnosticDirective {
    pub original_range: TextRange,
    pub virtual_range: TextRange,
    pub policy: MappedDiagnosticDirectivePolicy,
    pub unused_code: i32,
    pub unused_message_text: String,
    pub source: String,
}

/// Go `*ast.Diagnostic` from `NewExternalDiagnostic`. The field names are the
/// ones of `crate::core::Diagnostic`, so wave 3 changes only the type name.
#[derive(Clone, Debug)]
pub struct ExternalDiagnostic {
    pub file: Node,
    pub pos: i32,
    pub end: i32,
    pub code: i32,
    pub category: ts_diagnostics::Category,
    pub source: String,
    pub message_text: String,
}

impl ExternalDiagnostic {
    // Go: ast/diagnostic.go:65 (*Diagnostic).Source
    #[must_use]
    pub fn source(&self) -> &str {
        &self.source
    }

    // Go: ast/diagnostic.go:76 (*Diagnostic).SetFile
    pub fn set_file(&mut self, file: Node) {
        self.file = file;
    }
}

// Go: ast/diagnostic.go:223 NewExternalDiagnostic
// NewExternalDiagnostic creates a diagnostic reported by an external source such as a content mapper.
// The message text is already localized (the external source owns localization) and the code is shown
// with the given source prefix (e.g. "vue") instead of "TS". The location refers to the file's original,
// untransformed content.
#[must_use]
pub fn new_external_diagnostic(
    file: Node,
    loc: TextRange,
    source: &str,
    category: ts_diagnostics::Category,
    code: i32,
    message_text: &str,
) -> ExternalDiagnostic {
    ExternalDiagnostic {
        file,
        pos: loc.pos(),
        end: loc.end(),
        code,
        category,
        source: source.to_string(),
        message_text: message_text.to_string(),
    }
}

// Go: locale/locale.go:15 (Locale).String
/// Go `Locale.String`: the default locale is "".
#[must_use]
pub fn locale_string(l: &Locale) -> String {
    if *l == locale::DEFAULT {
        return String::new();
    }
    l.0.string()
}
