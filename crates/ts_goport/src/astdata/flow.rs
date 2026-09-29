use std::ops::{BitOr, BitOrAssign};

use crate::astdata::{FileId, FlowNodeId, NodeArenaId, NodeRef};

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

/// Unambiguous identity for a flow node within a compiler Program.
///
/// `FlowNodeId` remains dense and file-local because generated AST fields store
/// it directly. Convert it to `FlowRef` before retaining it in program-wide
/// semantic state.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct FlowRef {
    pub arena: NodeArenaId,
    pub file: FileId,
    pub flow: FlowNodeId,
}

impl FlowRef {
    #[must_use]
    pub const fn new(arena: NodeArenaId, file: FileId, flow: FlowNodeId) -> Self {
        Self { arena, file, flow }
    }

    #[must_use]
    pub fn is_for(self, arena: NodeArenaId, file: FileId) -> bool {
        self.arena == arena && self.file == file
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
        target: FlowRef,
        antecedents: Vec<FlowRef>,
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
    pub antecedent: Option<FlowRef>,
    /// Ordered antecedents for branch and loop labels.
    ///
    /// This `Vec` is the safe Rust equivalent of typescript-go's linked
    /// `FlowList`; insertion order remains observable and is preserved. Normal
    /// `add_antecedent` calls suppress duplicates within a label, while
    /// `replace_antecedents` intentionally preserves duplicates produced by
    /// upstream `combineFlowLists` in try/finally binding.
    pub antecedents: Vec<FlowRef>,
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
        antecedent: FlowRef,
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
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FlowNodeArena {
    arena: NodeArenaId,
    file: FileId,
    nodes: Vec<FlowNode>,
}

impl FlowNodeArena {
    /// Creates a file-scoped flow arena with its canonical unreachable node at
    /// local ID zero.
    #[must_use]
    pub fn new(arena: NodeArenaId, file: FileId) -> Self {
        Self {
            arena,
            file,
            nodes: vec![FlowNode::new(FlowFlags::UNREACHABLE)],
        }
    }

    #[must_use]
    pub const fn node_arena(&self) -> NodeArenaId {
        self.arena
    }

    #[must_use]
    pub const fn file(&self) -> FileId {
        self.file
    }

    #[must_use]
    pub const fn unreachable(&self) -> FlowRef {
        FlowRef::new(self.arena, self.file, FlowNodeId(0))
    }

    #[must_use]
    /// Allocates one flow node in binder traversal order.
    ///
    /// Returns `None` without changing the arena when any embedded flow
    /// reference does not already exist in this arena or an AST payload belongs
    /// to a different AST arena or file. This arena does not own the AST, so the
    /// producer remains responsible for ensuring that a same-brand `NodeRef`'s
    /// local node ID exists.
    ///
    /// # Panics
    ///
    /// Panics if a single flow arena would exceed `u32::MAX` nodes.
    pub fn alloc(&mut self, node: FlowNode) -> Option<FlowRef> {
        if !self.can_alloc(&node) {
            return None;
        }
        let flow = FlowNodeId(
            u32::try_from(self.nodes.len()).expect("flow-node arena exceeds u32::MAX nodes"),
        );
        self.nodes.push(node);
        Some(FlowRef::new(self.arena, self.file, flow))
    }

    fn can_alloc(&self, node: &FlowNode) -> bool {
        node.antecedent
            .is_none_or(|antecedent| self.get(antecedent).is_some())
            && node
                .antecedents
                .iter()
                .all(|antecedent| self.get(*antecedent).is_some())
            && node
                .payload
                .as_ref()
                .is_none_or(|payload| self.payload_belongs_to_arena(payload))
    }

    fn payload_belongs_to_arena(&self, payload: &FlowNodePayload) -> bool {
        match payload {
            FlowNodePayload::Ast(node) => node.is_for(self.arena, self.file),
            FlowNodePayload::SwitchClause {
                switch_statement, ..
            } => switch_statement.is_for(self.arena, self.file),
            FlowNodePayload::ReduceLabel {
                target,
                antecedents,
            } => {
                self.get(*target).is_some()
                    && antecedents
                        .iter()
                        .all(|antecedent| self.get(*antecedent).is_some())
            }
        }
    }

    #[must_use]
    pub fn get(&self, reference: FlowRef) -> Option<&FlowNode> {
        reference
            .is_for(self.arena, self.file)
            .then(|| self.nodes.get(reference.flow.0 as usize))
            .flatten()
    }

    #[must_use]
    pub fn get_mut(&mut self, reference: FlowRef) -> Option<&mut FlowNode> {
        reference
            .is_for(self.arena, self.file)
            .then(|| self.nodes.get_mut(reference.flow.0 as usize))
            .flatten()
    }

    /// Converts an AST's file-local flow ID into a checked program-wide
    /// reference.
    #[must_use]
    pub fn flow_ref(&self, flow: FlowNodeId) -> Option<FlowRef> {
        self.nodes
            .get(flow.0 as usize)
            .map(|_| FlowRef::new(self.arena, self.file, flow))
    }

    /// Applies typescript-go's first-reference/then-shared flag transition.
    ///
    /// Returns the updated flags, or `None` when `reference` is not in this
    /// arena.
    pub fn mark_referenced(&mut self, reference: FlowRef) -> Option<FlowFlags> {
        let node = self.get_mut(reference)?;
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
    pub fn add_antecedent(&mut self, label: FlowRef, antecedent: FlowRef) -> Option<bool> {
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

    /// Replaces a label's antecedents with an upstream-combined list.
    ///
    /// Unlike [`Self::add_antecedent`], this operation deliberately preserves
    /// order and duplicates and does not alter `REFERENCED`/`SHARED`. It is the
    /// direct representation of `combineFlowLists` followed by wholesale label
    /// assignment in the upstream try/finally binder.
    pub fn replace_antecedents(&mut self, label: FlowRef, antecedents: Vec<FlowRef>) -> Option<()> {
        if !self.get(label)?.flags.intersects(FlowFlags::LABEL)
            || antecedents.iter().any(|flow| self.get(*flow).is_none())
        {
            return None;
        }
        self.get_mut(label)?.antecedents = antecedents;
        Some(())
    }

    /// Concatenates flow lists in upstream order without de-duplication or
    /// graph mutation.
    #[must_use]
    pub fn combine_antecedent_lists(head: &[FlowRef], tail: &[FlowRef]) -> Vec<FlowRef> {
        head.iter().chain(tail).copied().collect()
    }

    /// Collapses an empty or single-edge label exactly as the upstream binder.
    ///
    /// Returns `None` when `label` is invalid or is not a branch/loop label.
    #[must_use]
    pub fn finish_label(&self, label: FlowRef) -> Option<FlowRef> {
        let node = self.get(label)?;
        if !node.flags.intersects(FlowFlags::LABEL) {
            return None;
        }
        Some(match node.antecedents.as_slice() {
            [] => self.unreachable(),
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
    use crate::astdata::{FileId, NodeArena, NodeId, NodeRef};

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
        let nodes = NodeArena::new();
        let mut arena = FlowNodeArena::new(nodes.id(), FileId::new(3));
        let start = arena.alloc(FlowNode::new(FlowFlags::START)).unwrap();
        let node = NodeRef::new(nodes.id(), FileId::new(3), NodeId::new(7));
        let assignment = arena
            .alloc(FlowNode::with_antecedent(
                FlowFlags::ASSIGNMENT,
                FlowNodePayload::Ast(node),
                start,
            ))
            .unwrap();

        assert_eq!(arena.unreachable().flow.0, 0);
        assert_eq!(start.flow.0, 1);
        assert_eq!(assignment.flow.0, 2);
        assert_eq!(arena.get(assignment).unwrap().antecedent, Some(start));
        assert_eq!(arena.iter().count(), 3);
    }

    #[test]
    fn switch_payload_retains_exact_clause_range() {
        let nodes = NodeArena::new();
        let payload = FlowNodePayload::SwitchClause {
            switch_statement: NodeRef::new(nodes.id(), FileId::new(1), NodeId::new(12)),
            clause_start: 4,
            clause_end: 4,
        };
        assert!(payload.is_empty_switch_clause());

        let non_empty = FlowNodePayload::SwitchClause {
            switch_statement: NodeRef::new(nodes.id(), FileId::new(1), NodeId::new(12)),
            clause_start: 4,
            clause_end: 6,
        };
        assert!(!non_empty.is_empty_switch_clause());
    }

    #[test]
    fn reference_and_label_transitions_match_upstream() {
        let nodes = NodeArena::new();
        let mut arena = FlowNodeArena::new(nodes.id(), FileId::new(0));
        let unreachable = arena.unreachable();
        let first = arena.alloc(FlowNode::new(FlowFlags::START)).unwrap();
        let second = arena.alloc(FlowNode::new(FlowFlags::ASSIGNMENT)).unwrap();
        let label = arena.alloc(FlowNode::new(FlowFlags::BRANCH_LABEL)).unwrap();

        assert_eq!(arena.finish_label(label), Some(unreachable));
        assert_eq!(arena.add_antecedent(label, unreachable), Some(false));
        assert_eq!(arena.add_antecedent(label, first), Some(true));
        assert!(
            arena
                .get(first)
                .unwrap()
                .flags
                .contains(FlowFlags::REFERENCED)
        );
        assert_eq!(arena.finish_label(label), Some(first));
        assert_eq!(arena.add_antecedent(label, first), Some(false));
        assert_eq!(arena.add_antecedent(label, second), Some(true));
        assert_eq!(arena.finish_label(label), Some(label));

        arena.mark_referenced(first).unwrap();
        assert!(arena.get(first).unwrap().flags.contains(FlowFlags::SHARED));
    }

    #[test]
    fn combined_lists_preserve_duplicates_order_and_reference_flags() {
        let nodes = NodeArena::new();
        let mut arena = FlowNodeArena::new(nodes.id(), FileId::new(4));
        let shared_path = arena.alloc(FlowNode::new(FlowFlags::ASSIGNMENT)).unwrap();
        let normal_only = arena.alloc(FlowNode::new(FlowFlags::START)).unwrap();
        let exceptional_only = arena.alloc(FlowNode::new(FlowFlags::CALL)).unwrap();
        let finally_label = arena.alloc(FlowNode::new(FlowFlags::BRANCH_LABEL)).unwrap();

        let normal = [shared_path, normal_only];
        let exceptional = [shared_path, exceptional_only];
        let combined = FlowNodeArena::combine_antecedent_lists(&normal, &exceptional);
        arena
            .replace_antecedents(finally_label, combined.clone())
            .unwrap();

        assert_eq!(
            combined,
            [shared_path, normal_only, shared_path, exceptional_only]
        );
        assert_eq!(arena.get(finally_label).unwrap().antecedents, combined);
        assert_eq!(arena.get(shared_path).unwrap().flags, FlowFlags::ASSIGNMENT);
    }

    #[test]
    fn program_wide_refs_reject_a_different_node_arena() {
        let first_nodes = NodeArena::new();
        let second_nodes = NodeArena::new();
        let file = FileId::new(5);
        let mut first = FlowNodeArena::new(first_nodes.id(), file);
        let mut second = FlowNodeArena::new(second_nodes.id(), file);
        let first_start = first.alloc(FlowNode::new(FlowFlags::START)).unwrap();
        let second_start = second.alloc(FlowNode::new(FlowFlags::START)).unwrap();

        assert_eq!(first_start.flow, second_start.flow);
        assert_ne!(first_start, second_start);
        assert!(first.get(second_start).is_none());
        assert!(second.get(first_start).is_none());
        assert!(first.mark_referenced(second_start).is_none());
    }

    #[test]
    fn allocation_rejects_a_foreign_antecedent_before_mutation() {
        let owner_nodes = NodeArena::new();
        let foreign_nodes = NodeArena::new();
        let file = FileId::new(6);
        let mut owner = FlowNodeArena::new(owner_nodes.id(), file);
        let mut foreign = FlowNodeArena::new(foreign_nodes.id(), file);
        let foreign_start = foreign.alloc(FlowNode::new(FlowFlags::START)).unwrap();
        let before = owner.len();

        let result = owner.alloc(FlowNode::with_antecedent(
            FlowFlags::ASSIGNMENT,
            FlowNodePayload::Ast(NodeRef::new(owner_nodes.id(), file, NodeId::new(0))),
            foreign_start,
        ));

        assert_eq!(result, None);
        assert_eq!(owner.len(), before);
    }

    #[test]
    fn allocation_rejects_a_foreign_label_antecedent_before_mutation() {
        let owner_nodes = NodeArena::new();
        let foreign_nodes = NodeArena::new();
        let file = FileId::new(7);
        let mut owner = FlowNodeArena::new(owner_nodes.id(), file);
        let mut foreign = FlowNodeArena::new(foreign_nodes.id(), file);
        let foreign_start = foreign.alloc(FlowNode::new(FlowFlags::START)).unwrap();
        let before = owner.len();
        let mut label = FlowNode::new(FlowFlags::BRANCH_LABEL);
        label.antecedents.push(foreign_start);

        assert_eq!(owner.alloc(label), None);
        assert_eq!(owner.len(), before);
    }

    #[test]
    fn allocation_rejects_foreign_reduce_label_refs_before_mutation() {
        let owner_nodes = NodeArena::new();
        let foreign_nodes = NodeArena::new();
        let file = FileId::new(8);
        let mut owner = FlowNodeArena::new(owner_nodes.id(), file);
        let mut foreign = FlowNodeArena::new(foreign_nodes.id(), file);
        let local_target = owner.alloc(FlowNode::new(FlowFlags::BRANCH_LABEL)).unwrap();
        let foreign_target = foreign
            .alloc(FlowNode::new(FlowFlags::BRANCH_LABEL))
            .unwrap();
        let before = owner.len();

        let mut foreign_target_node = FlowNode::new(FlowFlags::REDUCE_LABEL);
        foreign_target_node.payload = Some(FlowNodePayload::ReduceLabel {
            target: foreign_target,
            antecedents: vec![local_target],
        });
        assert_eq!(owner.alloc(foreign_target_node), None);
        assert_eq!(owner.len(), before);

        let mut foreign_antecedent_node = FlowNode::new(FlowFlags::REDUCE_LABEL);
        foreign_antecedent_node.payload = Some(FlowNodePayload::ReduceLabel {
            target: local_target,
            antecedents: vec![foreign_target],
        });
        assert_eq!(owner.alloc(foreign_antecedent_node), None);
        assert_eq!(owner.len(), before);
    }

    #[test]
    fn allocation_rejects_a_foreign_ast_payload_before_mutation() {
        let owner_nodes = NodeArena::new();
        let foreign_nodes = NodeArena::new();
        let file = FileId::new(9);
        let mut owner = FlowNodeArena::new(owner_nodes.id(), file);
        let before = owner.len();
        let mut node = FlowNode::new(FlowFlags::ASSIGNMENT);
        node.payload = Some(FlowNodePayload::Ast(NodeRef::new(
            foreign_nodes.id(),
            file,
            NodeId::new(0),
        )));

        assert_eq!(owner.alloc(node), None);
        assert_eq!(owner.len(), before);
    }

    #[test]
    fn allocation_rejects_a_foreign_switch_payload_before_mutation() {
        let owner_nodes = NodeArena::new();
        let file = FileId::new(10);
        let mut owner = FlowNodeArena::new(owner_nodes.id(), file);
        let before = owner.len();
        let mut node = FlowNode::new(FlowFlags::SWITCH_CLAUSE);
        node.payload = Some(FlowNodePayload::SwitchClause {
            switch_statement: NodeRef::new(owner_nodes.id(), FileId::new(11), NodeId::new(0)),
            clause_start: 0,
            clause_end: 1,
        });

        assert_eq!(owner.alloc(node), None);
        assert_eq!(owner.len(), before);
    }
}
