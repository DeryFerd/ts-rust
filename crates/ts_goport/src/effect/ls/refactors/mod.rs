//! Port of Effect-TS/tsgo `internal/refactors` (effect-tsgo 0.51.1,
//! `47cb1ed7`): all refactor implementations and the registry. One Go file
//! per Rust file.
//!
//! All 21 refactors are ported, and [`ALL`] has them in Go order: lane E9a
//! the 9 of group a (pipe, toggle, arrow and gen wrappers), E9b the 5 of
//! group b (async/await and effectGenToFn), E9c the 5 Schema refactors and
//! E9d layerMagic and writeTagClassAccessors.

use std::borrow::Cow;

use crate::effect::ls::refactor::Refactor;
use crate::effect::ls::rewriter::Tracker;
use crate::ls::CodeAction;
use crate::lsp::lsproto;
use crate::prelude::*;

pub mod async_await_to_fn;
pub mod async_await_to_fn_try_promise;
pub mod async_await_to_gen;
pub mod async_await_to_gen_try_promise;
pub mod effect_gen_to_fn;
pub mod function_to_arrow;
pub mod layer_magic;
pub mod make_schema_opaque;
pub mod make_schema_opaque_with_ns;
pub mod pipeable_to_datafirst;
pub mod remove_unnecessary_effect_gen;
pub mod structural_type_to_schema;
pub mod toggle_lazy_const;
pub mod toggle_pipe_style;
pub mod toggle_return_type_annotation;
pub mod toggle_type_annotation;
pub mod type_to_effect_schema;
pub mod type_to_effect_schema_class;
pub mod wrap_with_effect_gen;
pub mod wrap_with_pipe;
pub mod write_tag_class_accessors;

// Go: refactors/refactors.go:9 All
/// All is the list of all refactor providers.
/// Add new refactors here explicitly - no init() magic.
pub static ALL: &[&Refactor] = &[
    &wrap_with_pipe::WRAP_WITH_PIPE,
    &toggle_pipe_style::TOGGLE_PIPE_STYLE,
    &pipeable_to_datafirst::PIPEABLE_TO_DATAFIRST,
    &wrap_with_effect_gen::WRAP_WITH_EFFECT_GEN,
    &remove_unnecessary_effect_gen::REMOVE_UNNECESSARY_EFFECT_GEN,
    &async_await_to_gen::ASYNC_AWAIT_TO_GEN,
    &async_await_to_gen_try_promise::ASYNC_AWAIT_TO_GEN_TRY_PROMISE,
    &async_await_to_fn::ASYNC_AWAIT_TO_FN,
    &async_await_to_fn_try_promise::ASYNC_AWAIT_TO_FN_TRY_PROMISE,
    &effect_gen_to_fn::EFFECT_GEN_TO_FN,
    &toggle_type_annotation::TOGGLE_TYPE_ANNOTATION,
    &toggle_return_type_annotation::TOGGLE_RETURN_TYPE_ANNOTATION,
    &toggle_lazy_const::TOGGLE_LAZY_CONST,
    &function_to_arrow::FUNCTION_TO_ARROW,
    &layer_magic::LAYER_MAGIC,
    &write_tag_class_accessors::WRITE_TAG_CLASS_ACCESSORS,
    &type_to_effect_schema::TYPE_TO_EFFECT_SCHEMA,
    &type_to_effect_schema_class::TYPE_TO_EFFECT_SCHEMA_CLASS,
    &make_schema_opaque::MAKE_SCHEMA_OPAQUE,
    &make_schema_opaque_with_ns::MAKE_SCHEMA_OPAQUE_WITH_NS,
    &structural_type_to_schema::STRUCTURAL_TYPE_TO_SCHEMA,
];

/// The refactor's answer: `action` with its full LSP kind
/// (`refactor.rewrite.effect.<name>`), or nothing when the action has no
/// edits.
// PORT: Go repeats this tail in each refactor: `if action == nil { return
// nil }; action.Kind = "..."; return []ls.CodeAction{*action}`.
pub(crate) fn with_kind(action: Option<CodeAction>, kind: &'static str) -> Vec<CodeAction> {
    let Some(mut action) = action else {
        return Vec::new();
    };
    action.kind = lsproto::CodeActionKind(Cow::Borrowed(kind));
    vec![action]
}

// Go: refactors/async_await_to_gen.go:365 cloneNodeList
// PORT: Go has it in a group b file (asyncAwaitToGen), and functionToArrow
// (group a) uses it, so it is here for both.
pub(crate) fn clone_node_list(tracker: &Tracker, list: NodeList) -> NodeList {
    if list.is_nil() {
        return NodeList::NIL;
    }
    let f = tracker.node_factory();
    if list.nodes().is_empty() {
        return f.new_node_list(&[]);
    }
    let cloned: Vec<Node> = list.nodes().iter().map(|n| f.deep_clone_node(n)).collect();
    f.new_node_list(&cloned)
}
