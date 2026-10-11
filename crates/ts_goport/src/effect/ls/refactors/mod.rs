//! Port of Effect-TS/tsgo `internal/refactors` (effect-tsgo 0.51.1,
//! `47cb1ed7`): all refactor implementations and the registry. One Go file
//! per Rust file.
//!
//! Lane E9a ports the 9 refactors of group a (pipe, toggle, arrow and gen
//! wrappers). The other 12 are comments in [`ALL`] at their Go place: E9b
//! (async/await and effectGenToFn), E9c (the Schema refactors) and E9d
//! (layerMagic, writeTagClassAccessors).

use std::borrow::Cow;

use crate::effect::ls::refactor::Refactor;
use crate::effect::ls::rewriter::Tracker;
use crate::ls::CodeAction;
use crate::lsp::lsproto;
use crate::prelude::*;

pub mod function_to_arrow;
pub mod pipeable_to_datafirst;
pub mod remove_unnecessary_effect_gen;
pub mod toggle_lazy_const;
pub mod toggle_pipe_style;
pub mod toggle_return_type_annotation;
pub mod toggle_type_annotation;
pub mod wrap_with_effect_gen;
pub mod wrap_with_pipe;

// Go: refactors/refactors.go:9 All
/// All is the list of all refactor providers.
/// Add new refactors here explicitly - no init() magic.
pub static ALL: &[&Refactor] = &[
    &wrap_with_pipe::WRAP_WITH_PIPE,
    &toggle_pipe_style::TOGGLE_PIPE_STYLE,
    &pipeable_to_datafirst::PIPEABLE_TO_DATAFIRST,
    &wrap_with_effect_gen::WRAP_WITH_EFFECT_GEN,
    &remove_unnecessary_effect_gen::REMOVE_UNNECESSARY_EFFECT_GEN,
    // E9b: AsyncAwaitToGen,
    // E9b: AsyncAwaitToGenTryPromise,
    // E9b: AsyncAwaitToFn,
    // E9b: AsyncAwaitToFnTryPromise,
    // E9b: EffectGenToFn,
    &toggle_type_annotation::TOGGLE_TYPE_ANNOTATION,
    &toggle_return_type_annotation::TOGGLE_RETURN_TYPE_ANNOTATION,
    &toggle_lazy_const::TOGGLE_LAZY_CONST,
    &function_to_arrow::FUNCTION_TO_ARROW,
    // E9d: LayerMagic,
    // E9d: WriteTagClassAccessors,
    // E9c: TypeToEffectSchema,
    // E9c: TypeToEffectSchemaClass,
    // E9c: MakeSchemaOpaque,
    // E9c: MakeSchemaOpaqueWithNs,
    // E9c: StructuralTypeToSchema,
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
