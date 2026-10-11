//! Port of Effect-TS/tsgo `internal/fixables/effect_module.go`.

use crate::effect::ls::rewriter::Tracker;
use crate::effect::typeparser::find_effect_module_identifier;
use crate::prelude::*;

// Go: fixables/effect_module.go:9 effectModuleMethod
/// `receiver.method`, where a nil receiver is the file's Effect module name.
pub(super) fn effect_module_method(
    tracker: &Tracker,
    sf: Node,
    receiver: Node,
    method: &str,
) -> Node {
    let f = tracker.node_factory();
    let receiver = if receiver.is_nil() {
        f.new_identifier(find_effect_module_identifier(sf))
    } else {
        f.deep_clone_node(receiver)
    };
    f.new_property_access_expression(
        receiver,
        Node::NIL,
        f.new_identifier(method),
        NodeFlags::NONE,
    )
}

// Go: fixables/effect_module.go:18 replaceEffectMethodCallee
/// Replaces the method name `name` with `method`, or, when there is no name
/// node, the whole callee with `Effect.method`.
pub(super) fn replace_effect_method_callee(
    tracker: &mut Tracker,
    sf: Node,
    callee: Node,
    name: Node,
    method: &str,
) {
    if name.is_some() {
        let new_name = tracker.node_factory().new_identifier(method);
        tracker.replace_node(sf, name, new_name, None);
        return;
    }
    let new_callee = effect_module_method(tracker, sf, Node::NIL, method);
    tracker.replace_node(sf, callee, new_callee, None);
}
