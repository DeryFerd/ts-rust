//! Port of Effect-TS/tsgo `internal/rewriter` (effect-tsgo 0.51.1,
//! `47cb1ed7`): `tracker.go` here and `piping_flow.go` in
//! `rewriter/piping_flow.rs`.
//!
//! The rewriter tracker wraps `change::Tracker`. Its node edits are text
//! edits: the new node is printed with the non-formatted printer and put in
//! place as text, so the base tracker's node formatting is never used.
//!
//! Not ported: `NewModuleDeclaration` (only the E9 refactor
//! `make_schema_opaque_with_ns.go` uses it).

use std::rc::Rc;

use indexmap::IndexMap;

use crate::ls::change::{self, LeadingTriviaOption, NodeOptions, TrailingTriviaOption};
use crate::lsp::lsproto;
use crate::prelude::*;
use crate::printer::syntheticfile::print_and_position_node;

mod piping_flow;

pub use piping_flow::PipingFlowTransformationReplacement;

// Go: rewriter/tracker.go:27 pendingBeforeEdit
struct PendingBeforeEdit {
    source_file: Node,
    before: Node,
    text: String,
    leading: LeadingTriviaOption,
}

// Go: rewriter/tracker.go:34 Tracker
// PORT: Go embeds `*change.Tracker`; `Deref` gives its promoted methods.
// The methods below shadow the base methods of the same name. Go promoted
// factory calls such as `t.NewIdentifier(..)` are
// `t.node_factory().new_identifier(..)`.
pub struct Tracker {
    pub tracker: change::Tracker,
    pending_before: Vec<PendingBeforeEdit>,
}

impl std::ops::Deref for Tracker {
    type Target = change::Tracker;
    fn deref(&self) -> &change::Tracker {
        &self.tracker
    }
}

impl std::ops::DerefMut for Tracker {
    fn deref_mut(&mut self) -> &mut change::Tracker {
        &mut self.tracker
    }
}

impl Tracker {
    // Go: rewriter/tracker.go:39 NewTracker
    #[must_use]
    pub fn new(raw: change::Tracker) -> Self {
        Tracker {
            tracker: raw,
            pending_before: Vec::new(),
        }
    }

    // Go: rewriter/tracker.go:43 GetChanges
    // PORT: Go `change.CollectChanges` is the base `GetChanges` without the
    // list of unmappable files.
    pub fn get_changes(&mut self) -> IndexMap<String, Vec<lsproto::TextEdit>> {
        self.flush_pending_before();
        self.tracker.get_changes().0
    }

    // Go: rewriter/tracker.go:57 ReplaceNode
    // PORT: Go `options *change.NodeOptions` is `Option<NodeOptions>`. Go
    // `change.ReplaceAdjustedRangeWithText` (an E0 shim) is its two calls:
    // `GetAdjustedRange`, then `ReplaceTextRangeWithText`.
    pub fn replace_node(
        &mut self,
        source_file: Node,
        old_node: Node,
        new_node: Node,
        options: Option<NodeOptions>,
    ) {
        if old_node.is_nil() || new_node.is_nil() {
            return;
        }
        let options = options.unwrap_or_else(|| NodeOptions {
            leading_trivia_option: LeadingTriviaOption::EXCLUDE,
            trailing_trivia_option: TrailingTriviaOption::EXCLUDE,
            ..NodeOptions::default()
        });
        let mut text = self.consume_pending_prefix(source_file, old_node)
            + &self.node_text(source_file, new_node);
        if !options.prefix.is_empty() {
            text = options.prefix.clone() + &text;
        }
        if !options.suffix.is_empty() {
            text += &options.suffix;
        }
        let rng = self.tracker.get_adjusted_range(
            source_file,
            old_node,
            old_node,
            options.leading_trivia_option,
            options.trailing_trivia_option,
        );
        self.tracker
            .replace_text_range_with_text(source_file, rng, &text);
    }

    // Go: rewriter/tracker.go:85 InsertNodeBefore
    pub fn insert_node_before(
        &mut self,
        source_file: Node,
        before: Node,
        new_node: Node,
        blank_line_between: bool,
        leading_trivia_option: LeadingTriviaOption,
    ) {
        if before.is_nil() || new_node.is_nil() {
            return;
        }
        let mut text = self.node_text(source_file, new_node);
        if blank_line_between {
            text += "\n\n";
        } else {
            text += "\n";
        }
        self.pending_before.push(PendingBeforeEdit {
            source_file,
            before,
            text,
            leading: leading_trivia_option,
        });
    }

    // Go: rewriter/tracker.go:98 flushPendingBefore
    // PORT: Go `change.InsertTextAtAdjustedRangeStart` (an E0 shim) is its
    // two calls: `GetAdjustedRange`, then an empty-range
    // `ReplaceTextRangeWithText` at the range start.
    fn flush_pending_before(&mut self) {
        for edit in std::mem::take(&mut self.pending_before) {
            if edit.before.is_nil() || edit.source_file.is_nil() || edit.text.is_empty() {
                continue;
            }
            let rng = self.tracker.get_adjusted_range(
                edit.source_file,
                edit.before,
                edit.before,
                edit.leading,
                TrailingTriviaOption::NONE,
            );
            let start = rng.pos();
            self.tracker.replace_text_range_with_text(
                edit.source_file,
                TextRange::new(start, start),
                &edit.text,
            );
        }
    }

    // Go: rewriter/tracker.go:116 consumePendingPrefix
    fn consume_pending_prefix(&mut self, source_file: Node, target: Node) -> String {
        if target.is_nil() || self.pending_before.is_empty() {
            return String::new();
        }
        let mut builder = String::new();
        self.pending_before.retain(|edit| {
            if edit.source_file == source_file && edit.before == target {
                builder.push_str(&edit.text);
                return false;
            }
            true
        });
        builder
    }

    // Go: rewriter/tracker.go:133 nodeText
    // PORT: Go calls the unexported `change.Tracker.getNonformattedText`
    // through a `go:linkname` shim. Rust calls what it calls,
    // `printer.PrintAndPositionNode` with the tracker's factory, new line,
    // indent size and emit context. The synthetic source file that
    // `getNonformattedText` also makes is not used here.
    fn node_text(&self, source_file: Node, node: Node) -> String {
        let (text, _) = print_and_position_node(
            self.tracker.node_factory(),
            node,
            source_file,
            &self.tracker.new_line,
            self.tracker.format_settings.editor_settings.indent_size,
            Some(Rc::clone(&self.tracker.emit_context)),
        );
        text
    }
}
