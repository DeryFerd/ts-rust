//! Port of Effect-TS/tsgo `internal/refactor` (effect-tsgo 0.51.1, `47cb1ed7`):
//! the refactor type (`refactor.go`) and the context a refactor runs with
//! (`context.go`). The refactors are in `effect::ls::refactors`.

use std::rc::Rc;

use crate::effect::ls::rewriter::Tracker;
use crate::effect::typeparser::TypeParser;
use crate::frontend::compiler;
use crate::gostd::Context;
use crate::ls::{CodeAction, LanguageService, change, lsconv, lsutil};
use crate::lsp::lsproto;
use crate::prelude::*;

// Go: refactor/refactor.go:13 Refactor
/// Refactor defines a selection-based refactoring action.
/// Unlike Fixable, refactors are not tied to a specific diagnostic error code —
/// they apply based on the user's selection.
pub struct Refactor {
    /// Name is the unique identifier for this refactor (e.g., "wrapWithPipe").
    pub name: &'static str,

    /// Description explains what this refactor does (shown in the editor's refactor menu).
    pub description: &'static str,

    /// Kind is the CodeActionKind suffix (e.g., "rewrite.effect.wrapWithPipe").
    pub kind: &'static str,

    /// Run executes the refactor and returns code actions for the given context.
    /// The Context provides access to the source file, span, type checker,
    /// and tracker lifecycle helpers.
    /// Return nil or empty slice if the refactor is not applicable.
    pub run: fn(&mut RefactorContext<'_, '_>) -> Vec<CodeAction>,
}

// Go: refactor/context.go:20 Context
/// Context bundles the refactor request data and provides helpers for refactor implementations.
/// Unlike fixable.Context, there is no ErrorCode — refactors apply to any selection.
// PORT: Go `refactor.Context`; the Rust name avoids the Go `context.Context`
// port (`Context`), as `FixableContext` does. Go's `Checker` is
// `tp.checker`. Go keeps the language service; the port keeps the two
// things `NewRefactorAction` reads from it (format options, converters).
pub struct RefactorContext<'a, 'c> {
    pub source_file: Node,
    pub span: TextRange,
    pub program: &'a compiler::NewProgram,
    pub tp: &'a mut TypeParser<'c>,

    pub context: &'a Context,

    format_options: lsutil::FormatCodeSettings,
    converters: Rc<lsconv::Converters>,
}

// Go: refactor/context.go:32 NewContext
/// NewContext creates a refactor Context from the refactor provider callback parameters.
// PORT: Go panics on a nil program or checker; Rust references are never
// nil.
pub fn new_context<'a, 'c>(
    ctx: &'a Context,
    source_file: Node,
    span: TextRange,
    program: &'a compiler::NewProgram,
    lang_service: &LanguageService,
    tp: &'a mut TypeParser<'c>,
) -> RefactorContext<'a, 'c> {
    RefactorContext {
        source_file,
        span,
        program,
        tp,
        context: ctx,
        format_options: lang_service.format_options(),
        converters: Rc::clone(&lang_service.converters),
    }
}

impl RefactorContext<'_, '_> {
    // Go: refactor/context.go:52 BytePosToLSPPosition
    /// BytePosToLSPPosition converts a single byte offset in the context's SourceFile
    /// to an lsproto.Position using ECMA line/character position.
    // PORT: as Go, this does not use the converters (the fixable context
    // does): the character is always UTF-16.
    #[must_use]
    pub fn byte_pos_to_lsp_position(&self, pos: i32) -> lsproto::Position {
        let (ln, ch) = get_ecma_line_and_utf16_character_of_position(self.source_file, pos);
        lsproto::Position {
            line: ln as u32,
            character: ch as u32,
        }
    }

    // Go: refactor/context.go:66 NewRefactorAction
    /// NewRefactorAction creates a tracker, runs the action's edit closure, and returns
    /// a CodeAction wrapping the resulting edits for the current SourceFile.
    /// Returns None if the closure produced no edits.
    // PORT: Go `RefactorAction{Description, Run}` is the two arguments. The
    // caller sets the action's kind, as in Go.
    pub fn new_refactor_action(
        &self,
        description: &str,
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
            description: description.to_string(),
            changes: edits,
            ..CodeAction::default()
        })
    }
}
