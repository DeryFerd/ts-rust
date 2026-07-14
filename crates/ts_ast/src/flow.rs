use std::ops::{BitOr, BitOrAssign};

use crate::{FlowNodeId, NodeRef};

/// Control-flow node flags.
///
/// Bit positions intentionally match `internal/ast/flow.go` in the pinned
/// typescript-go epoch. `REFERENCED` and `SHARED` are mutable graph metadata,
/// not separate node kinds.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct FlowFlags(u32);

impl FlowFlags {
    pub const NONE: Self = Self(0);
    pub const UNREACHABLE: Self = Self(1 << 0);
    pub const START: Self = Self(1 << 1);
    pub const BRANCH_LABEL: Self = Self(1 << 2);
    pub const LOOP_LABEL: Self = Self(1 << 3);
    pub const ASSIGNMENT: Self = Self(1 << 4);
    pub const TRUE_CONDITION: Self = Self(1 << 5);
    pub const FALSE_CONDITION: Self = Self(1 << 6);
    pub const SWITCH_CLAUSE: Self = Self(1 << 7);
    pub const ARRAY_MUTATION: Self = Self(1 << 8);
    pub const CALL: Self = Self(1 << 9);
    pub const REDUCE_LABEL: Self = Self(1 << 10);
    pub const REFERENCED: Self = Self(1 << 11);
    pub const SHARED: Self = Self(1 << 12);

    pub const LABEL: Self = Self(Self::BRANCH_LABEL.0 | Self::LOOP_LABEL.0);
    pub const CONDITION: Self = Self(Self::TRUE_CONDITION.0 | Self::FALSE_CONDITION.0);

    #[must_use]
    pub const fn bits(self) -> u32 {
        self.0
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    #[must_use]
    pub const fn intersects(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

impl BitOr for FlowFlags {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for FlowFlags {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

/// Source payload associated with a flow node.
///
/// typescript-go represents switch and reduce-label payloads as synthetic AST
/// nodes. Keeping them explicit avoids placing non-source nodes in a parsed
/// source arena while preserving the same information and ordering.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FlowNodePayload {
    Ast(NodeRef),
    SwitchClause {
        switch_statement: NodeRef,
        clause_start: i32,
        clause_end: i32,
    },
    ReduceLabel {
        target: FlowNodeId,
        antecedents: Vec<FlowNodeId>,
    },
}

impl FlowNodePayload {
    #[must_use]
    pub fn is_empty_switch_clause(&self) -> bool {
        matches!(
            self,
            Self::SwitchClause {
                clause_start,
                clause_end,
                ..
            } if clause_start == clause_end
        )
    }
}

/// One node in the binder-created control-flow graph.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FlowNode {
    pub flags: FlowFlags,
    pub payload: Option<FlowNodePayload>,
    /// Antecedent for every node except branch and loop labels.
    pub antecedent: Option<FlowNodeId>,
    /// Ordered, de-duplicated antecedents for branch and loop labels.
    ///
    /// This `Vec` is the safe Rust equivalent of typescript-go's linked
    /// `FlowList`; insertion order remains observable and is preserved.
    pub antecedents: Vec<FlowNodeId>,
}

impl FlowNode {
    #[must_use]
    pub const fn new(flags: FlowFlags) -> Self {
        Self {
            flags,
            payload: None,
            antecedent: None,
            antecedents: Vec::new(),
        }
    }

    #[must_use]
    pub fn with_antecedent(
        flags: FlowFlags,
        payload: FlowNodePayload,
        antecedent: FlowNodeId,
    ) -> Self {
        Self {
            flags,
            payload: Some(payload),
            antecedent: Some(antecedent),
            antecedents: Vec::new(),
        }
    }
}

/// Stable storage for flow nodes allocated in binder traversal order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FlowNodeArena {
    nodes: Vec<FlowNode>,
}

impl FlowNodeArena {
    #[must_use]
    pub const fn new() -> Self {
        Self { nodes: Vec::new() }
    }

    #[must_use]
    /// Allocates one flow node in binder traversal order.
    ///
    /// # Panics
    ///
    /// Panics if a single flow arena would exceed `u32::MAX` nodes.
    pub fn alloc(&mut self, node: FlowNode) -> FlowNodeId {
        let id = FlowNodeId(
            u32::try_from(self.nodes.len()).expect("flow-node arena exceeds u32::MAX nodes"),
        );
        self.nodes.push(node);
        id
    }

    #[must_use]
    pub fn get(&self, id: FlowNodeId) -> Option<&FlowNode> {
        self.nodes.get(id.0 as usize)
    }

    #[must_use]
    pub fn get_mut(&mut self, id: FlowNodeId) -> Option<&mut FlowNode> {
        self.nodes.get_mut(id.0 as usize)
    }

    /// Applies typescript-go's first-reference/then-shared flag transition.
    ///
    /// Returns the updated flags, or `None` when `id` is not in this arena.
    pub fn mark_referenced(&mut self, id: FlowNodeId) -> Option<FlowFlags> {
        let node = self.get_mut(id)?;
        if node.flags.intersects(FlowFlags::REFERENCED) {
            node.flags |= FlowFlags::SHARED;
        } else {
            node.flags |= FlowFlags::REFERENCED;
        }
        Some(node.flags)
    }

    /// Adds an ordered label antecedent with upstream unreachable and duplicate
    /// suppression.
    ///
    /// Returns `Some(true)` when the edge was added, `Some(false)` when it was
    /// suppressed, or `None` when either ID is invalid or `label` is not a
    /// branch/loop label.
    pub fn add_antecedent(&mut self, label: FlowNodeId, antecedent: FlowNodeId) -> Option<bool> {
        let antecedent_flags = self.get(antecedent)?.flags;
        let label_node = self.get(label)?;
        if !label_node.flags.intersects(FlowFlags::LABEL) {
            return None;
        }
        if antecedent_flags.intersects(FlowFlags::UNREACHABLE)
            || label_node.antecedents.contains(&antecedent)
        {
            return Some(false);
        }
        self.get_mut(label)?.antecedents.push(antecedent);
        self.mark_referenced(antecedent)?;
        Some(true)
    }

    /// Collapses an empty or single-edge label exactly as the upstream binder.
    ///
    /// Returns `None` when `label` is invalid or is not a branch/loop label.
    #[must_use]
    pub fn finish_label(&self, label: FlowNodeId, unreachable: FlowNodeId) -> Option<FlowNodeId> {
        let node = self.get(label)?;
        if !node.flags.intersects(FlowFlags::LABEL) {
            return None;
        }
        Some(match node.antecedents.as_slice() {
            [] => unreachable,
            [only] => *only,
            _ => label,
        })
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    #[must_use]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &FlowNode> {
        self.nodes.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::{FlowFlags, FlowNode, FlowNodeArena, FlowNodePayload};
    use crate::{FileId, NodeId, NodeRef};

    #[test]
    fn flags_match_typescript_go_bit_layout() {
        assert_eq!(FlowFlags::UNREACHABLE.bits(), 1 << 0);
        assert_eq!(FlowFlags::START.bits(), 1 << 1);
        assert_eq!(FlowFlags::BRANCH_LABEL.bits(), 1 << 2);
        assert_eq!(FlowFlags::LOOP_LABEL.bits(), 1 << 3);
        assert_eq!(FlowFlags::ASSIGNMENT.bits(), 1 << 4);
        assert_eq!(FlowFlags::TRUE_CONDITION.bits(), 1 << 5);
        assert_eq!(FlowFlags::FALSE_CONDITION.bits(), 1 << 6);
        assert_eq!(FlowFlags::SWITCH_CLAUSE.bits(), 1 << 7);
        assert_eq!(FlowFlags::ARRAY_MUTATION.bits(), 1 << 8);
        assert_eq!(FlowFlags::CALL.bits(), 1 << 9);
        assert_eq!(FlowFlags::REDUCE_LABEL.bits(), 1 << 10);
        assert_eq!(FlowFlags::REFERENCED.bits(), 1 << 11);
        assert_eq!(FlowFlags::SHARED.bits(), 1 << 12);
        assert_eq!(
            FlowFlags::LABEL.bits(),
            FlowFlags::BRANCH_LABEL.bits() | FlowFlags::LOOP_LABEL.bits()
        );
        assert_eq!(
            FlowFlags::CONDITION.bits(),
            FlowFlags::TRUE_CONDITION.bits() | FlowFlags::FALSE_CONDITION.bits()
        );
    }

    #[test]
    fn arena_assigns_dense_ids_and_preserves_graph_edges() {
        let mut arena = FlowNodeArena::new();
        let start = arena.alloc(FlowNode::new(FlowFlags::START));
        let node = NodeRef::new(FileId::new(3), NodeId::new(7));
        let assignment = arena.alloc(FlowNode::with_antecedent(
            FlowFlags::ASSIGNMENT,
            FlowNodePayload::Ast(node),
            start,
        ));

        assert_eq!(start.0, 0);
        assert_eq!(assignment.0, 1);
        assert_eq!(arena.get(assignment).unwrap().antecedent, Some(start));
        assert_eq!(arena.iter().count(), 2);
    }

    #[test]
    fn switch_payload_retains_exact_clause_range() {
        let payload = FlowNodePayload::SwitchClause {
            switch_statement: NodeRef::new(FileId::new(1), NodeId::new(12)),
            clause_start: 4,
            clause_end: 4,
        };
        assert!(payload.is_empty_switch_clause());

        let non_empty = FlowNodePayload::SwitchClause {
            switch_statement: NodeRef::new(FileId::new(1), NodeId::new(12)),
            clause_start: 4,
            clause_end: 6,
        };
        assert!(!non_empty.is_empty_switch_clause());
    }

    #[test]
    fn reference_and_label_transitions_match_upstream() {
        let mut arena = FlowNodeArena::new();
        let unreachable = arena.alloc(FlowNode::new(FlowFlags::UNREACHABLE));
        let first = arena.alloc(FlowNode::new(FlowFlags::START));
        let second = arena.alloc(FlowNode::new(FlowFlags::ASSIGNMENT));
        let label = arena.alloc(FlowNode::new(FlowFlags::BRANCH_LABEL));

        assert_eq!(arena.finish_label(label, unreachable), Some(unreachable));
        assert_eq!(arena.add_antecedent(label, unreachable), Some(false));
        assert_eq!(arena.add_antecedent(label, first), Some(true));
        assert!(
            arena
                .get(first)
                .unwrap()
                .flags
                .contains(FlowFlags::REFERENCED)
        );
        assert_eq!(arena.finish_label(label, unreachable), Some(first));
        assert_eq!(arena.add_antecedent(label, first), Some(false));
        assert_eq!(arena.add_antecedent(label, second), Some(true));
        assert_eq!(arena.finish_label(label, unreachable), Some(label));

        arena.mark_referenced(first).unwrap();
        assert!(arena.get(first).unwrap().flags.contains(FlowFlags::SHARED));
    }
}
