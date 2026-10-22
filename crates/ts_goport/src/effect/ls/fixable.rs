//! Port of Effect-TS/tsgo `internal/fixable` (effect-tsgo 0.51.1, `47cb1ed7`):
//! the code fix type (`fixable.go`) and the context a fix runs with
//! (`context.go`). The fixes are in `effect::ls::fixables`.
//!
//! Not ported: `NewStandaloneContext`, `newStandaloneConverters` and
//! `LSPRangeToTextRange`. Only the oxlint runner (`etsoxlintrunner`) and
//! `context_test.go` use them.

use std::rc::Rc;

use crate::effect::etscore::ResolvedEffectPluginOptions;
use crate::effect::ls::rewriter::Tracker;
use crate::effect::typeparser::TypeParser;
use crate::frontend::compiler;
use crate::gostd::Context;
use crate::ls::{CodeAction, CodeFixContext, change, lsconv, lsutil};
use crate::lsp::lsproto;
use crate::prelude::*;

// Go: fixable/fixable.go:14 Fixable
/// Fixable defines a code fix provider for a set of diagnostic codes.
/// This is analogous to how Rule defines a diagnostic provider.
pub struct Fixable {
    /// Name is the unique identifier for this fixable (e.g., "effectDisable", "floatingEffectYield").
    pub name: &'static str,

    /// Description explains what this fixable does (used in documentation/tooling).
    pub description: &'static str,

    /// ErrorCodes is the set of diagnostic codes this fixable handles.
    /// A fixable can handle multiple related error codes.
    pub error_codes: &'static [i32],

    /// FixIDs for "fix all" support (optional). Each fix action can have its own ID.
    pub fix_ids: &'static [&'static str],

    /// Run executes the fixable and returns code actions for the given context.
    /// Return an empty list if no fixes are applicable.
    pub run: fn(&mut FixableContext<'_, '_>) -> Vec<CodeAction>,
}

impl Fixable {
    // Go: fixable/fixable.go:36 HandlesCode
    /// HandlesCode returns true if this fixable handles the given error code.
    #[must_use]
    pub fn handles_code(&self, code: i32) -> bool {
        self.error_codes.contains(&code)
    }
}

// Go: fixable/context.go:24 Context
/// Context bundles the code-fix request data and provides helpers for fixable implementations.
// PORT: Go `fixable.Context`; the Rust name avoids the Go `context.Context`
// port (`Context`), as `RuleContext` does. Go's `Checker` is `tp.checker`.
pub struct FixableContext<'a, 'c> {
    pub source_file: Node,
    pub span: TextRange,
    pub error_code: i32,
    pub options: &'a ResolvedEffectPluginOptions,
    pub program: &'a compiler::NewProgram,
    pub tp: &'a mut TypeParser<'c>,

    pub context: &'a Context,

    format_options: lsutil::FormatCodeSettings,
    converters: Rc<lsconv::Converters>,
}

// Go: fixable/context.go:40 NewContext
/// NewContext creates a fixable Context from the standard code-fix request parameters.
// PORT: Go panics on a nil program or checker; Rust references are never
// nil. Go reads the converters through an `unsafe.Pointer` copy of the
// language service struct; the Rust field is public.
pub fn new_context<'a, 'c>(
    ctx: &'a Context,
    fix_ctx: &CodeFixContext<'a>,
    options: &'a ResolvedEffectPluginOptions,
    tp: &'a mut TypeParser<'c>,
) -> FixableContext<'a, 'c> {
    FixableContext {
        source_file: fix_ctx.source_file,
        span: fix_ctx.span,
        error_code: fix_ctx.error_code,
        options,
        program: fix_ctx.program,
        tp,
        context: ctx,
        format_options: fix_ctx.ls.format_options(),
        converters: Rc::clone(&fix_ctx.ls.converters),
    }
}

impl FixableContext<'_, '_> {
    // Go: fixable/context.go:103 BytePosToLSPPosition
    /// BytePosToLSPPosition converts a byte offset using the context's LSP encoding.
    #[must_use]
    pub fn byte_pos_to_lsp_position(&self, pos: i32) -> lsproto::Position {
        self.converters.to_lsp_position(&self.source_file, pos).0
    }

    // Go: fixable/context.go:122 NewFixAction
    /// NewFixAction creates a tracker, runs the action's edit closure, and returns
    /// a CodeAction wrapping the resulting edits for the current SourceFile.
    /// Returns None if the closure produced no edits.
    // PORT: Go `FixAction{Description, Run}` is the two arguments.
    pub fn new_fix_action(
        &self,
        description: String,
        run: impl FnOnce(&mut Tracker),
    ) -> Option<CodeAction> {
        let raw_tracker = change::new_tracker(
            self.context,
            self.program.options(),
            self.format_options.clone(),
            Rc::clone(&self.converters),
        );
        let mut tracker = Tracker::new(raw_tracker);
        run(&mut tracker);
        let edits = tracker
            .get_changes()
            .shift_remove(source_file_file_name(self.source_file))
            .unwrap_or_default();
        if edits.is_empty() {
            return None;
        }
        Some(CodeAction {
            description,
            changes: edits,
            ..CodeAction::default()
        })
    }
}
