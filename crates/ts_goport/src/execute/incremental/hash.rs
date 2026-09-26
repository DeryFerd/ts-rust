//! Port of the head of execute/incremental/snapshot.go (lines 20-131):
//! `FileInfo`, `ComputeHash`, `FileEmitKind`, the pending emit helpers and
//! `emitSignature`.
//!
//! PORT: the plan gives U0 only `ComputeHash`. The buildinfo types (U1)
//! need `FileInfo`, `FileEmitKind` and `emitSignature`, so this file ports
//! the whole snapshot.go block before `buildInfoDiagnosticWithFileName`.
//! `snapshot.rs` (U2) starts at snapshot.go:133.

use crate::frontend::prelude::*;

// Go: incremental/snapshot.go:20 FileInfo
// PORT: Go unexported fields are plain `pub` fields.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FileInfo {
    pub version: String,
    pub signature: String,
    pub affects_global_scope: bool,
    pub implied_node_format: ResolutionMode,
}

impl FileInfo {
    // Go: incremental/snapshot.go:27 Version
    #[must_use]
    pub fn version(&self) -> &str {
        &self.version
    }

    // Go: incremental/snapshot.go:28 Signature
    #[must_use]
    pub fn signature(&self) -> &str {
        &self.signature
    }

    // Go: incremental/snapshot.go:29 AffectsGlobalScope
    #[must_use]
    pub fn affects_global_scope(&self) -> bool {
        self.affects_global_scope
    }

    // Go: incremental/snapshot.go:30 ImpliedNodeFormat
    #[must_use]
    pub fn implied_node_format(&self) -> ResolutionMode {
        self.implied_node_format
    }
}

// Go: incremental/snapshot.go:32 ComputeHash
// PORT: Go `xxh3.HashString128(text).Bytes()` is big endian, Hi before Lo.
// `xxh3_128` returns the same 128 bits as a `u128` (Hi in the high half),
// so `{:032x}` is `hex.EncodeToString` of those bytes.
#[must_use]
pub fn compute_hash(text: &str, hash_with_text: bool) -> String {
    let hash_bytes = xxhash_rust::xxh3::xxh3_128(text.as_bytes());
    let mut hash = format!("{hash_bytes:032x}");
    if hash_with_text {
        hash.push('-');
        hash.push_str(text);
    }
    hash
}

// Go: incremental/snapshot.go:41 FileEmitKind
crate::flags_macros::go_flags!(FileEmitKind, u32 {
    NONE = 0; // FileEmitKindNone
    JS = 1 << 0; // FileEmitKindJs: emit js file
    JS_MAP = 1 << 1; // FileEmitKindJsMap: emit js.map file
    JS_INLINE_MAP = 1 << 2; // FileEmitKindJsInlineMap: emit inline source map in js file
    DTS_ERRORS = 1 << 3; // FileEmitKindDtsErrors: emit dts errors
    DTS_EMIT = 1 << 4; // FileEmitKindDtsEmit: emit d.ts file
    DTS_MAP = 1 << 5; // FileEmitKindDtsMap: emit d.ts.map file

    DTS = (1 << 3) | (1 << 4); // FileEmitKindDts = DtsErrors | DtsEmit
    ALL_JS = (1 << 0) | (1 << 1) | (1 << 2); // FileEmitKindAllJs = Js | JsMap | JsInlineMap
    ALL_DTS_EMIT = (1 << 4) | (1 << 5); // FileEmitKindAllDtsEmit = DtsEmit | DtsMap
    ALL_DTS = (1 << 3) | (1 << 4) | (1 << 5); // FileEmitKindAllDts = Dts | DtsMap
    ALL = 0b11_1111; // FileEmitKindAll = AllJs | AllDts
});

// Go: incremental/snapshot.go:59 GetFileEmitKind
#[must_use]
pub fn get_file_emit_kind(options: &CompilerOptions) -> FileEmitKind {
    let mut result = FileEmitKind::JS;
    if options.source_map.is_true() {
        result |= FileEmitKind::JS_MAP;
    }
    if options.inline_source_map.is_true() {
        result |= FileEmitKind::JS_INLINE_MAP;
    }
    if options.get_emit_declarations() {
        result |= FileEmitKind::DTS;
    }
    if options.declaration_map.is_true() {
        result |= FileEmitKind::DTS_MAP;
    }
    if options.emit_declaration_only.is_true() {
        result &= FileEmitKind::ALL_DTS;
    }
    result
}

// Go: incremental/snapshot.go:79 getPendingEmitKindWithOptions
#[must_use]
pub fn get_pending_emit_kind_with_options(
    options: &CompilerOptions,
    old_options: &CompilerOptions,
) -> FileEmitKind {
    let old_emit_kind = get_file_emit_kind(old_options);
    let new_emit_kind = get_file_emit_kind(options);
    get_pending_emit_kind(new_emit_kind, old_emit_kind)
}

// Go: incremental/snapshot.go:85 getPendingEmitKind
#[must_use]
pub fn get_pending_emit_kind(emit_kind: FileEmitKind, old_emit_kind: FileEmitKind) -> FileEmitKind {
    if old_emit_kind == emit_kind {
        return FileEmitKind::NONE;
    }
    if old_emit_kind.is_empty() || emit_kind.is_empty() {
        return emit_kind;
    }
    let diff = FileEmitKind(old_emit_kind.0 ^ emit_kind.0);
    let mut result = FileEmitKind::NONE;
    // If there is diff in Js emit, pending emit is js emit flags
    if diff.intersects(FileEmitKind::ALL_JS) {
        result |= emit_kind & FileEmitKind::ALL_JS;
    }
    // If dts errors pending, add dts errors flag
    if diff.intersects(FileEmitKind::DTS_ERRORS) {
        result |= emit_kind & FileEmitKind::ALL_DTS;
    }
    // If there is diff in Dts emit, pending emit is dts emit flags
    if diff.intersects(FileEmitKind::ALL_DTS_EMIT) {
        result |= emit_kind & FileEmitKind::ALL_DTS_EMIT;
    }
    result
}

// Go: incremental/snapshot.go:111 emitSignature
// Signature (Hash of d.ts emitted), is string if it was emitted using same d.ts.map option as what compilerOptions indicate,
// otherwise tuple of string
// PORT: Go `*emitSignature` values are never mutated after creation, so the
// Rust value is cloned. Go nil `signatureWithDifferentOptions` is `None`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct EmitSignature {
    pub signature: String,
    pub signature_with_different_options: Option<Vec<String>>,
}

impl EmitSignature {
    // Go: incremental/snapshot.go:118 getNewEmitSignature
    // Covert to Emit signature based on oldOptions and EmitSignature format
    // If d.ts map options differ then swap the format, otherwise use as is
    #[must_use]
    pub fn get_new_emit_signature(
        &self,
        old_options: &CompilerOptions,
        new_options: &CompilerOptions,
    ) -> EmitSignature {
        if old_options.declaration_map.is_true() == new_options.declaration_map.is_true() {
            return self.clone();
        }
        match &self.signature_with_different_options {
            None => EmitSignature {
                signature: String::new(),
                signature_with_different_options: Some(vec![self.signature.clone()]),
            },
            Some(list) => EmitSignature {
                signature: list[0].clone(),
                signature_with_different_options: None,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // The expected value is the `version` that tsgo-oracle wrote for a
    // file with this text.
    #[test]
    fn compute_hash_matches_go() {
        let text = "export const z = 1;\n";
        assert_eq!(
            compute_hash(text, false),
            "313d2a26e8bf4d4087aa22eb407e3977"
        );
        assert_eq!(
            compute_hash(text, true),
            format!("313d2a26e8bf4d4087aa22eb407e3977-{text}")
        );
    }
}
