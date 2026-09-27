//! Per-file Go node stores (the nodes the ported Go parser creates) and the
//! file registry (the published stores and the `GoFile` of each file id).
//!
//! Go parser nodes are ordinary `*ast.Node` values made by `ast.NodeFactory`.
//! Here each parsed file gets one store. The store id is the file id, so a
//! store node is a normal `Node` handle: high 32 bits are the file id, low 32
//! bits are the slot index + 1.
//!
//! Each slot has a header (Go kind plus the mutable Go `NodeBase` fields:
//! parent, flags, loc) and, for a node slot, a leaked `ts_ast::Node` that
//! holds the node data. Child ids inside that data are slot indexes of the
//! same store:
//! - a child in the same file uses its own slot index;
//! - a child from another file or a synthetic child (Go shares the pointer)
//!   uses an alias slot, which `Node::new` resolves to that node;
//! - Go `nil` in a field that ts_ast stores as a required `NodeId` uses
//!   slot 0, which resolves to `Node::NIL`.
//!
//! `node.rs` reads kind, loc, flags and parent from the header for files that
//! have a store. Files of the legacy loader (ts_parser) never have a store,
//! so their reads do not change.
//!
//! Phases of a store:
//! - Build: the parser runs on one thread and writes the stores of that
//!   thread (`BUILD`). The header and the data can change until the parser
//!   finishes the file (`finishNode`, parent setting, JSDoc flags,
//!   reparser.go writes). Then the parser freezes the file, which also
//!   builds the per-store tables that a publish puts in the registry. The
//!   build stores of a thread get consecutive ids from `BuildStores::base`,
//!   the published count when its first store was made. The last store
//!   made on a thread is its `ACTIVE` store: the parser reads and writes it
//!   without a store lookup.
//! - Detached: a parse worker (`files_parser.rs` prefetch) parses one file
//!   into a store with a provisional id (`DETACHED_STORE_BASE` + job) that
//!   only its thread sees (`DETACHED`). The loading thread adopts the
//!   finished store when the loader asks for that file
//!   (`adopt_detached_store`). The store then gets the next real id, so ids
//!   still follow the serial parse order.
//! - Published: the loader calls `publish_file_stores` with the `GoFile` of
//!   each build store before it installs the program. The stores and their
//!   `GoFile`s move into the process-wide, read-only registry. Node reads
//!   then need no thread-local and no `RefCell` borrow, and any thread can
//!   read them. Writes to a published store panic. A table that needs the
//!   real id of an adopted store is built then, on scoped threads for a
//!   large publish (`publish_stores`).
//!
//! The registry:
//! - One file id is one file version. Ids only grow (`PUBLISHED` is the
//!   next unused id), and a published file is never changed or freed. A new
//!   program version shares the ids of its unchanged files.
//! - Tier 0 (`FROZEN`) is the first publish: program 1, or the files of the
//!   legacy loader. The hot node reads in `node.rs` read only its dense
//!   tables, inline, and return `None` on a miss.
//! - Tier 1 (`LATER`) holds every later publish (edited files, other
//!   programs). One slot per id points at the `Frozen` of its publish. Reads
//!   reach it out of line, after a tier 0 miss.
//! - After a tier 0 miss, a synthetic id has no store (two compares, no
//!   call). Any other id takes one cold call: tier 1, then the detached
//!   store, then the build stores of this thread.
//!
//! Binder data is not stored here: it stays in `GoFile::node_bind`, indexed
//! by slot index.
//!
//! PORT: a program is either all legacy files or all store files. A legacy
//! publish has only `GoFile`s. It must be the only publish: file ids are
//! store ids, so no store can be made or published after it.

use crate::frontend::parser::SourceFileParseOptions;
use crate::prelude::*;
use std::cell::Cell;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};
use ts_ast::NodeData;

/// Slot 0: Go `nil` stored in a ts_ast field that has no `Option`.
const NIL_SLOT: u32 = 0;

/// Position that marks a Go `nil` list in a ts_ast list field that has no
/// `Option`. Go positions are byte offsets, so they never reach it, and
/// `u32::MAX` is already the undefined position `-1`.
// PORT: ts_ast cannot change under the R97 rules. For store nodes the factory
// stores Go `nil` in a required list field as an empty list at this position,
// and `NodeList::is_nil` reads it back as nil (plan risk 1).
pub const NIL_LIST_POS: u32 = u32::MAX - 1;

/// The Go kind and the mutable Go `NodeBase` fields of a store node.
///
/// A nil or alias slot has kind `Unknown`, no flags, an undefined loc, and
/// its target (nil for slot 0) in `parent`.
#[derive(Clone, Copy, Debug)]
pub struct NodeHeader {
    /// Go `node.Parent`. Inside a store a parent in the same store is kept
    /// as a `LOCAL_STORE` handle; the read hooks return the real handle.
    pub parent: Node,
    pub loc: TextRange,
    pub flags: NodeFlags,
    pub kind: SyntaxKind,
    /// Set by `mark_source_file_roots`: Go `GetSourceFileOfNode(node)` is the
    /// root of this store (`FileStore::root`). False means "walk the parents".
    source_file_is_root: bool,
    /// Set when the slot is made or its data is replaced, for an Identifier
    /// or PrivateIdentifier slot: Go `scanner.GetIdentifierToken(node.Text())
    /// != KindIdentifier` (`frozen_store_text_is_keyword`). False for other
    /// slots.
    // PERF: U1 (a). The header has a spare byte after `source_file_is_root`,
    // so this bit adds no memory.
    text_is_keyword: bool,
}

impl NodeHeader {
    /// The header as the node reads see it: a parent in the same store (see
    /// `LOCAL_STORE`) becomes a handle of store `file`.
    #[inline]
    fn read(mut self, file: usize) -> Self {
        if self.parent.file_index() == LOCAL_STORE {
            self.parent = handle(file, slot_index(self.parent) as u32);
        }
        self
    }

    /// The stored form of `parent` for a node of store `file`.
    #[inline]
    fn stored_parent(file: usize, parent: Node) -> Node {
        if parent.is_some() && parent.file_index() == file {
            handle(LOCAL_STORE, slot_index(parent) as u32)
        } else {
            parent
        }
    }

    /// The header of a nil (`target` nil) or alias slot.
    const fn target(target: Node) -> Self {
        Self {
            parent: target,
            loc: TextRange::undefined(),
            flags: NodeFlags::NONE,
            kind: SyntaxKind::Unknown,
            source_file_is_root: false,
            text_is_keyword: false,
        }
    }
}

/// The Go nodes of one parsed file. Slot `i` is `headers[i]` and `nodes[i]`.
/// The default value is an empty placeholder with no slots.
#[derive(Default)]
struct FileStore {
    file_name: &'static str,
    text: &'static str,
    headers: Vec<NodeHeader>,
    /// The ts_ast node (kind and data) of each node slot. `None` for the nil
    /// slot and alias slots.
    nodes: Vec<Option<&'static ts_ast::Node>>,
    /// Alias slot of each foreign node, so one node gets one slot. Emptied
    /// by `publish_file_stores`.
    aliases: FxHashMap<Node, u32>,
    /// Set when the parser has finished the file.
    frozen: bool,
    /// Slot of the SourceFile node that `mark_source_file_roots` found when
    /// the file was frozen, or 0 (the nil slot).
    root_slot: u32,
    /// `file_store_parser_flags`, made on the parsing thread when the file
    /// is frozen. The loader takes it once.
    parser_flags: Option<Vec<NodeFlags>>,
    /// Go `file.jsdocCache`, set by `finishSourceFile`. Node reads use it
    /// until the file is published (its `GoFile` holds it then), so
    /// `publish_file_stores` empties it.
    jsdoc_cache: FxHashMap<Node, &'static [Node]>,
    /// Go `file.hasLazyJSDoc`, set by `finishSourceFile` for a non-JS file,
    /// with the inputs that Go `parseJSDocForNode` reads from the file
    /// (`ParseOptions()` and `ScriptKind`; the text is `text`). Node reads
    /// use it until the file is published (the program then keeps the
    /// inputs), so `publish_file_stores` drops it.
    lazy_js_doc: Option<(SourceFileParseOptions, ScriptKind)>,
    /// Go `file.jsdocCache` entries that `resolveJSDoc` adds before the file
    /// is published.
    // PORT: the parsed JSDoc nodes are synthetic nodes of the thread that
    // parsed them, so they are kept apart from `jsdoc_cache`.
    // `adopt_detached_store` (another thread) and `publish_file_stores`
    // drop them.
    lazy_jsdoc_cache: FxHashMap<Node, &'static [Node]>,
    /// Go `file.LanguageVariant`, the parse `file.Diagnostics()` and
    /// `file.ContainsNonASCII`, set by `finishSourceFile`. Reads of a file
    /// that is not published use them (`ast::source_file_language_variant`,
    /// `ast::source_file_diagnostics`, `ast::source_file_get_position_map`),
    /// for example the format tests, which parse a file with no program.
    language_variant: LanguageVariant,
    diagnostics: &'static [Diagnostic],
    contains_non_ascii: bool,
    /// The SourceFile node of this store, set by `publish_file_stores`.
    root: Node,
    /// Go `SourceFile.ECMALineMap()`, computed on first use after publish
    /// and shared by every thread.
    ecma_line_starts: OnceLock<Box<[i32]>>,
    /// `headers[i].kind` for every slot (`Frozen::kinds`). Made when the
    /// file is frozen. A length other than `headers.len()` means "not made".
    kinds: Box<[SyntaxKind]>,
    /// Made with `kinds`, in the same pass, so it is valid when `kinds` is.
    facts: StoreFacts,
    /// `resolve_slot` for every slot (`FrozenStore::resolved`), with the
    /// file id of the store. Same length rule as `kinds`. Never made for an
    /// alias-free store (`StoreFacts::alias_free`).
    resolved: Box<[Node]>,
    /// U1 (a): Go `node.Text()` of every Identifier and PrivateIdentifier
    /// slot, interned (`Frozen::names`). `Name::default()` for other slots.
    /// Moved from `build_names` when `kinds` is made (`move_build_columns`),
    /// same length rule. U1 (d): the only copy of the text of a node that
    /// `alloc_store_name_node` or `alloc_store_shared_name_node` made
    /// (`store_identifier_name`).
    names: Box<[Name]>,
    /// U1 (b): `ModifierList::modifier_flags` of the node's own modifier list
    /// for every slot, 0 when it has none (`Frozen::modifier_bits`). Moved
    /// from `build_modifier_bits` when `kinds` is made. Empty when made but a
    /// value does not fit in 16 bits; the reads then use the list.
    modifier_bits: Box<[u16]>,
    /// U1 (a) while the parser runs: the `names` entry of every slot, in slot
    /// order, pushed when the slot is made (one entry per header).
    // PERF: the text is interned while the new node data is hot, not in a
    // pass over every slot after the parse, which loaded each Identifier
    // data box again when it was cold.
    build_names: Vec<Name>,
    /// U1 (b) while the parser runs: the `modifier_bits` entry of every slot,
    /// pushed when the slot is made, 0 when the value does not fit in 16 bits
    /// (see `modifier_bits_overflow`).
    build_modifier_bits: Vec<u16>,
    /// Some slot got a modifier value that does not fit in 16 bits.
    modifier_bits_overflow: bool,
    /// U4: the `SlotChildren` of every slot (`FrozenStore::children`).
    /// Moved from `build_children` when `kinds` is made, same length rule.
    children: Box<[SlotChildren]>,
    /// U4 while the parser runs: the `children` entry of every slot, pushed
    /// when the slot is made and made again when its data is replaced.
    build_children: Vec<SlotChildren>,
    /// R2-5: the `SlotLinks` of every slot (`FrozenStore::links`). Moved
    /// from `build_links` when `kinds` is made, same length rule.
    links: Box<[SlotLinks]>,
    /// R2-5 while the parser runs: the `links` entry of every slot, pushed
    /// (`SlotLinks::NONE`) when the slot is made and written by
    /// `StoreChildLinks` and `replace_store_node_data`.
    build_links: Vec<SlotLinks>,
    /// Go parser `identifiers` (`internIdentifier`): the name and keyword
    /// bit of each identifier text of this file, keyed by the interned text.
    /// Dropped by the freeze.
    // PERF: one text hash per identifier node; the process-wide intern (a
    // shard `Mutex`) runs once per distinct text of the file.
    identifier_names: FxHashMap<&'static str, (Name, bool)>,
    /// U1 (e): binder capacity hints, made with `kinds`.
    bind_estimate: BindEstimate,
}

/// Facts about the slots of one finished store, made in the pass that makes
/// `FileStore::kinds`. They do not depend on the store id, so a detached
/// store gets them when its parse ends.
#[derive(Clone, Copy, Debug, Default)]
pub struct StoreFacts {
    /// Every slot after slot 0 holds a node (the store has no alias slot),
    /// so `resolve_slot(file, i) == handle(file, i)` for every `i >= 1`,
    /// and a child walk from a node of this store stays in this store.
    pub alias_free: bool,
    /// The parent of every node slot is nil or a node of this store, so a
    /// parent walk from a node of this store stays in this store.
    pub parents_local: bool,
    /// Some node slot has kind `ExportAssignment` or `ExportSpecifier`.
    pub has_export_alias_kind: bool,
    /// Some node slot has kind `ConditionalType` or `MappedType`.
    pub has_flow_constraint_kind: bool,
    /// U4 (CH7): some node slot has the parser flag
    /// `POSSIBLY_CONTAINS_DEPRECATED_TAG`. The binder never adds that bit
    /// (`BINDER_ADDED_FLAGS` in node.rs), and a frozen header does not
    /// change, so without it no node of the store has the bit in Go
    /// `node.Flags` (`frozen_store_lacks_deprecated_tag`).
    pub has_deprecated_tag: bool,
}

impl StoreFacts {
    /// The facts of a store that has only slot 0. `add` adds the others.
    const ONLY_NIL_SLOT: Self = Self {
        alias_free: true,
        parents_local: true,
        has_export_alias_kind: false,
        has_flow_constraint_kind: false,
        has_deprecated_tag: false,
    };

    /// Adds slot `header` (a node slot when `is_node`), after slot 0.
    #[inline]
    fn add(&mut self, header: &NodeHeader, is_node: bool) {
        if !is_node {
            self.alias_free = false;
            return;
        }
        if header.parent.is_some() && header.parent.file_index() != LOCAL_STORE {
            self.parents_local = false;
        }
        if header
            .flags
            .intersects(NodeFlags::POSSIBLY_CONTAINS_DEPRECATED_TAG)
        {
            self.has_deprecated_tag = true;
        }
        match header.kind {
            SyntaxKind::ExportAssignment | SyntaxKind::ExportSpecifier => {
                self.has_export_alias_kind = true;
            }
            SyntaxKind::ConditionalType | SyntaxKind::MappedType => {
                self.has_flow_constraint_kind = true;
            }
            _ => {}
        }
    }
}

/// U4 (CH6, bind A): two child ids of a node slot, so that `Node::name`,
/// `Node::expression`, `Node::postfix_token` and `Node::question_token` of a
/// published store node need no load of its ts_ast node and data
/// (`FileStore::children`, `frozen_store_child`). C2 adds a third field for
/// `Node::type_`, `Node::initializer`, `Node::type_name` and
/// `Node::type_argument_list`. The ids are store-local
/// slot indexes, like the child ids in the node data, so they stay valid
/// when a detached store gets its real id. `node.rs`
/// (`store_node_children`) makes the value from the node data with the arm
/// lists of those accessors.
///
/// - `name`: the id of the Go `Name()` child, 0 for nil or for a kind
///   without the field, or `UNKNOWN_ID`.
/// - `other`: a tag in the top two bits and an id below. Each kind has at
///   most one of these fields: `TAG_EXPRESSION` (Go `Expression()`, also
///   tag 0 with id 0 for a kind with none of the fields), `TAG_POSTFIX` (Go
///   `PostfixToken()`) or `TAG_QUESTION` (the node's own Go
///   `QuestionToken` field). All ones (`UNKNOWN_ID`) is unknown.
/// - `typed` (C2): a tag in the top three bits, the `NO_TYPE_ARGUMENTS` bit
///   and an id below, for Go `Type()`, `Initializer()` and
///   `AsTypeReference().TypeName`. `TYPED_TYPE`: `Type()` is the id and
///   `Initializer()` is nil (also id 0 for a node where both are nil, as for
///   a kind with neither field). `TYPED_INITIALIZER`: `Type()` is nil and
///   `Initializer()` is the id. `TYPED_TYPE_WITH_INITIALIZER`: `Type()` is
///   the id, and `Initializer()` is set too but not held. `TYPED_TYPE_NAME`
///   (TypeReference): `TypeName` is the id, `Type()` and `Initializer()`
///   are nil. `NO_TYPE_ARGUMENTS` is set when Go `TypeArgumentList()` is nil
///   and the node data has no list (`Node::type_argument_list` then gives
///   `NodeList::NIL`).
///
/// Unknown means "read the node data": nil and alias slots, the kinds whose
/// accessor arm is not a plain field read (QualifiedName,
/// CaseOrDefaultClause) and an id that does not fit.
// PERF: one 12-byte entry per slot. A read is the entry and the per-store
// record of `Node::new`, not the chain kind table, node pointer, node tag,
// data box, field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SlotChildren {
    name: u32,
    other: u32,
    typed: u32,
}

impl SlotChildren {
    /// A field value that means "read the node data".
    const UNKNOWN_ID: u32 = u32::MAX;
    const TAG_SHIFT: u32 = 30;
    /// The largest id that `other` can hold.
    const MAX_TAGGED_ID: u32 = (1 << Self::TAG_SHIFT) - 1;
    pub(crate) const TAG_EXPRESSION: u32 = 0;
    pub(crate) const TAG_POSTFIX: u32 = 1;
    pub(crate) const TAG_QUESTION: u32 = 2;
    const TAG_UNKNOWN: u32 = 3;

    const TYPED_TAG_SHIFT: u32 = 29;
    /// C2: Go `TypeArgumentList()` is nil (see the type doc).
    const NO_TYPE_ARGUMENTS: u32 = 1 << 28;
    /// The largest id that `typed` can hold.
    const MAX_TYPED_ID: u32 = Self::NO_TYPE_ARGUMENTS - 1;
    pub(crate) const TYPED_TYPE: u32 = 0;
    pub(crate) const TYPED_INITIALIZER: u32 = 1;
    pub(crate) const TYPED_TYPE_WITH_INITIALIZER: u32 = 2;
    pub(crate) const TYPED_TYPE_NAME: u32 = 3;
    /// Tags 4 to 6 are not used.
    const TYPED_UNKNOWN: u32 = 7;
    /// `typed` when unknown: every read takes the node data. The
    /// `NO_TYPE_ARGUMENTS` bit is clear.
    const TYPED_UNKNOWN_VALUE: u32 = Self::TYPED_UNKNOWN << Self::TYPED_TAG_SHIFT;

    /// Every read takes the node data.
    pub(crate) const UNKNOWN: Self = Self {
        name: Self::UNKNOWN_ID,
        other: Self::UNKNOWN_ID,
        typed: Self::TYPED_UNKNOWN_VALUE,
    };

    /// `name` is the name child id (0 for nil or no field, `None` for
    /// unknown); `other` is `(tag, id)` (`None` for unknown). The `typed`
    /// field is unknown (see `with_typed`).
    #[inline]
    pub(crate) fn new(name: Option<u32>, other: Option<(u32, u32)>) -> Self {
        let other = match other {
            Some((tag, id)) if tag < Self::TAG_UNKNOWN && id <= Self::MAX_TAGGED_ID => {
                (tag << Self::TAG_SHIFT) | id
            }
            _ => Self::UNKNOWN_ID,
        };
        Self {
            // `UNKNOWN_ID` itself is not a slot id a store can reach, and
            // it reads as unknown, which is always exact.
            name: name.unwrap_or(Self::UNKNOWN_ID),
            other,
            typed: Self::TYPED_UNKNOWN_VALUE,
        }
    }

    /// C2: this entry with `typed` set from `typed` (`(tag, id)`, `None`
    /// for unknown) and `no_type_arguments`.
    #[inline]
    pub(crate) fn with_typed(self, typed: Option<(u32, u32)>, no_type_arguments: bool) -> Self {
        let typed = match typed {
            Some((tag, id)) if tag <= Self::TYPED_TYPE_NAME && id <= Self::MAX_TYPED_ID => {
                (tag << Self::TYPED_TAG_SHIFT) | id
            }
            _ => Self::TYPED_UNKNOWN_VALUE,
        };
        let no_type_arguments = if no_type_arguments {
            Self::NO_TYPE_ARGUMENTS
        } else {
            0
        };
        Self {
            typed: typed | no_type_arguments,
            ..self
        }
    }

    /// The tag and id of `other`.
    #[inline]
    fn other_parts(self) -> (u32, u32) {
        (
            self.other >> Self::TAG_SHIFT,
            self.other & Self::MAX_TAGGED_ID,
        )
    }

    /// C2: the tag and id of `typed`.
    #[inline]
    fn typed_parts(self) -> (u32, u32) {
        (
            self.typed >> Self::TYPED_TAG_SHIFT,
            self.typed & Self::MAX_TYPED_ID,
        )
    }

    /// C2: Go `TypeArgumentList()` is nil.
    #[inline]
    fn has_no_type_arguments(self) -> bool {
        self.typed & Self::NO_TYPE_ARGUMENTS != 0
    }
}

/// Which `SlotChildren` field `frozen_store_child` reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StoreChild {
    /// Go `node.Name()`.
    Name,
    /// Go `node.Expression()`.
    Expression,
    /// Go `node.PostfixToken()`.
    PostfixToken,
    /// Go `node.QuestionToken()`: the own field, else the postfix token when
    /// it is a `?` token.
    QuestionToken,
    /// C2: Go `node.Type()`.
    Type,
    /// C2: Go `node.Initializer()`.
    Initializer,
    /// C2: Go `node.AsTypeReference().TypeName`. `None` (read the data, which
    /// panics like Go) for other kinds.
    TypeName,
}

/// R2-5: the binder child links of one slot (`FileStore::links`): the
/// children of a node in Go `ForEachChild` order as a chain, first child
/// and next sibling, so `Binder::bind_each_child` walks them without the
/// node data. The ids are store-local slot indexes, so they stay valid when
/// a detached store gets its real id.
///
/// - `first_child`: the first child of this node, `LINK_END` for a node
///   with no child, `LINK_NONE` when the chain of this node is not known.
/// - `next_sibling`: the next child in the chain that holds this slot,
///   `LINK_END` for the last one, `LINK_NONE` when no chain holds it.
///
/// Rules that keep a known chain equal to Go `ForEachChild` of its node:
/// - The parser links a node when it sets the parents of its children
///   (`StoreChildLinks`), in the same visit. A chain holds only node slots
///   of the same store.
/// - A slot is in at most one chain. A child that another chain holds
///   (a node that two parents share, or a child twice in one node), a
///   child of another store and an alias child make the node unknown.
/// - A new data write to a node (`replace_store_node_data`) frees its chain
///   and makes it unknown until the parser links it again.
/// - A store whose parse did not finish gets no links (`publish`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SlotLinks {
    first_child: u32,
    next_sibling: u32,
}

/// R2-5: a `SlotLinks` field value: the chain ends (slot 0, the nil slot,
/// is never a child in a chain).
const LINK_END: u32 = NIL_SLOT;
/// R2-5: a `SlotLinks` field value: not known (`first_child`) or in no
/// chain (`next_sibling`).
const LINK_NONE: u32 = u32::MAX;

impl SlotLinks {
    /// A slot with no known chain that no chain holds.
    const NONE: Self = Self {
        first_child: LINK_NONE,
        next_sibling: LINK_NONE,
    };
}

/// U1 (e): capacity hints for the binder of a store file, counted from the
/// slot kinds when the store is frozen (`frozen_store_bind_estimate`).
/// Only capacities: the binder output does not depend on them.
#[derive(Clone, Copy, Debug, Default)]
struct BindEstimate {
    /// `NodeBindBuilder` entries: about the nodes that get binder data.
    entries: u32,
    /// `Binder::flow_nodes`: about the flow nodes the binder makes.
    flow_nodes: u32,
}

/// The slot kind counts of a `BindEstimate`, one `add` per slot kind.
// PERF: U1 (e). `set_kinds_and_facts` adds each kind in its pass over the
// headers, so the estimate needs no second pass over the kinds.
#[derive(Default)]
struct BindCounts {
    identifiers: usize,
    others: usize,
    flow_nodes: usize,
}

impl BindCounts {
    #[inline]
    fn add(&mut self, kind: SyntaxKind) {
        match kind {
            // The nil slot and alias slots.
            SyntaxKind::Unknown => {}
            SyntaxKind::Identifier => self.identifiers += 1,
            _ => {
                self.others += 1;
                self.flow_nodes += flow_node_weight(kind);
            }
        }
    }

    fn estimate(&self) -> BindEstimate {
        // Every identifier gets its flow node (binder.go `bind`), and about
        // one other node in two is a declaration, a container, a statement
        // or a narrowable reference. An estimate above the count only costs
        // untouched capacity until the builder is dropped.
        let entries = self.identifiers + self.others / 2 + 1;
        // The unreachable flow node and the source file start node.
        let flow_nodes = self.flow_nodes + 2;
        BindEstimate {
            entries: u32::try_from(entries).unwrap_or(u32::MAX),
            flow_nodes: u32::try_from(flow_nodes).unwrap_or(u32::MAX),
        }
    }
}

/// About how many flow nodes the binder makes for a node of kind `kind`
/// (binder.go `bindContainer` and the `bind*Flow` functions).
fn flow_node_weight(kind: SyntaxKind) -> usize {
    match kind {
        // A start node for a control flow container, a flow call, a flow
        // assignment, or a logical or assignment operator.
        SyntaxKind::MethodSignature
        | SyntaxKind::CallSignature
        | SyntaxKind::ConstructSignature
        | SyntaxKind::FunctionType
        | SyntaxKind::ConstructorType
        | SyntaxKind::FunctionDeclaration
        | SyntaxKind::MethodDeclaration
        | SyntaxKind::GetAccessor
        | SyntaxKind::SetAccessor
        | SyntaxKind::FunctionExpression
        | SyntaxKind::ArrowFunction
        | SyntaxKind::ModuleBlock
        | SyntaxKind::CallExpression
        | SyntaxKind::VariableDeclaration
        | SyntaxKind::BindingElement
        | SyntaxKind::BinaryExpression
        | SyntaxKind::PostfixUnaryExpression
        | SyntaxKind::DeleteExpression => 1,
        // A start node and a return label, or a clause and its label.
        SyntaxKind::Constructor
        | SyntaxKind::ClassStaticBlockDeclaration
        | SyntaxKind::CaseClause
        | SyntaxKind::DefaultClause
        | SyntaxKind::LabeledStatement => 2,
        // Branch or loop labels and the true and false conditions.
        SyntaxKind::IfStatement
        | SyntaxKind::ConditionalExpression
        | SyntaxKind::WhileStatement
        | SyntaxKind::DoStatement
        | SyntaxKind::ForStatement
        | SyntaxKind::ForInStatement
        | SyntaxKind::ForOfStatement
        | SyntaxKind::SwitchStatement
        | SyntaxKind::TryStatement => 5,
        _ => 0,
    }
}

/// A store that is not published yet. It lives in a leaked cell of the
/// thread that made it, so `ACTIVE` can keep a plain reference to it.
type StoreCell = &'static RefCell<FileStore>;

/// The build stores of one thread. `stores[i]` has file id `base + i`.
#[derive(Default)]
struct BuildStores {
    /// `PUBLISHED` when the first of `stores` was made.
    base: usize,
    stores: Vec<StoreCell>,
}

impl BuildStores {
    /// The file id of the next store of this thread. Only a publish changes
    /// `PUBLISHED`, so the ids of one build are consecutive.
    fn next_id(&mut self) -> usize {
        let published = PUBLISHED.load(Ordering::Acquire);
        if self.stores.is_empty() {
            self.base = published;
        } else {
            assert_eq!(
                self.base, published,
                "another thread published node stores while this thread built stores"
            );
        }
        let id = self.base + self.stores.len();
        assert!(id < TIER1_LIMIT, "too many file ids");
        id
    }
}

thread_local! {
    /// The stores of this thread, while the parser runs.
    static BUILD: RefCell<BuildStores> = const {
        RefCell::new(BuildStores {
            base: 0,
            stores: Vec::new(),
        })
    };
    /// The detached store of a parse worker and its provisional id.
    static DETACHED: Cell<Option<(usize, StoreCell)>> = const { Cell::new(None) };
    /// The emptied cell of the last detached store of this thread. The next
    /// detached store reuses it.
    static SPARE_CELL: Cell<Option<StoreCell>> = const { Cell::new(None) };
    /// The store this thread made or adopted last, and its id: during a
    /// parse, the store of the file the parser reads and writes. It is also
    /// in `BUILD` or `DETACHED`, so clearing it is always safe.
    // PERF: query Q8. Node reads have no parser or factory to ask, so the
    // store of the parsed file is found here. The type has no destructor,
    // so a read is one thread-local load and an id compare: no `FROZEN`
    // check, no detached check and no `RefCell` borrow of `BUILD`.
    // `publish_file_stores` and `take_detached_file_store` clear it before
    // they empty its cell, and a thread publishes only its own build
    // stores, so an active store is never published. (One loading thread
    // builds at a time: `BuildStores::next_id` and the publish check it.)
    static ACTIVE: Cell<Option<(usize, StoreCell)>> = const { Cell::new(None) };
}

/// The cell of store `file` when it is the active store of this thread.
#[inline]
fn active_store(file: usize) -> Option<StoreCell> {
    match ACTIVE.get() {
        Some((id, store)) if id == file => Some(store),
        _ => None,
    }
}

/// The unpublished store `file` of this thread (active, detached or
/// built), or `None` when this thread has no such store.
#[inline]
fn build_store(file: usize) -> Option<StoreCell> {
    match active_store(file) {
        Some(store) => Some(store),
        None => inactive_build_store(file),
    }
}

/// `build_store` without the `ACTIVE` check.
#[inline(never)]
fn inactive_build_store(file: usize) -> Option<StoreCell> {
    if is_detached_id(file) {
        return DETACHED
            .get()
            .and_then(|(id, store)| (id == file).then_some(store));
    }
    BUILD.with(|b| {
        let b = b.borrow();
        b.stores.get(file.wrapping_sub(b.base)).copied()
    })
}

/// File index that marks a parent in the same store inside a stored
/// header. Reads give the handle of the store (`NodeHeader::read`), so a
/// store keeps its headers when its id changes (`adopt_detached_store`).
const LOCAL_STORE: usize = 0x7fff_ffff;

/// First provisional store id. Real file ids stay below `TIER1_LIMIT`;
/// synthetic node and flow ids are above every provisional id.
pub const DETACHED_STORE_BASE: usize = 0x8000_0000;
/// Number of provisional ids.
pub const DETACHED_STORE_LIMIT: usize = 0x4000_0000;

/// Every real file id is below this. Tier 1 has one slot per id.
const TIER1_LIMIT: usize = 1 << 22;
/// Slots per tier 1 chunk.
const LATER_CHUNK: usize = 256;

#[inline]
fn is_detached_id(file: usize) -> bool {
    (DETACHED_STORE_BASE..DETACHED_STORE_BASE + DETACHED_STORE_LIMIT).contains(&file)
}

/// True for an id that never has a store: a synthetic node or flow id, or
/// any other id at or above `TIER1_LIMIT` that is not a provisional id.
#[inline]
fn is_storeless_id(file: usize) -> bool {
    file >= TIER1_LIMIT && !is_detached_id(file)
}

/// The stores and `GoFile`s of one publish, read-only, with dense
/// per-store header and node tables for the hot node reads. File `file` of
/// the publish is at index `file - base`. Tier 0 has `base` 0, so its hot
/// reads index the tables by file id.
struct Frozen {
    /// The first file id of the publish.
    base: usize,
    stores: &'static [FileStore],
    headers: Box<[&'static [NodeHeader]]>,
    nodes: Box<[&'static [Option<&'static ts_ast::Node>]]>,
    /// `headers[file][i].kind`, packed (`FileStore::kinds`). `Node::kind`
    /// reads only this.
    kinds: Box<[&'static [SyntaxKind]]>,
    /// U1 (a): `FileStore::names` of each store (`Node::text_name`).
    names: Box<[&'static [Name]]>,
    /// U1 (b): `FileStore::modifier_bits` of each store
    /// (`Node::modifier_flags`).
    modifier_bits: Box<[&'static [u16]]>,
    /// What `Node::new` reads for each store, and its facts.
    per_store: Box<[FrozenStore]>,
    /// The `GoFile` of each file id of the publish.
    go_files: Box<[GoFile]>,
    /// True for the legacy loader: `go_files` only, no stores.
    legacy: bool,
}

/// The per-store part of `Frozen` that `Node::new` reads.
#[derive(Clone, Copy)]
struct FrozenStore {
    /// `try_resolve_store_id(file, i)` for every slot, computed once
    /// (`FileStore::resolved`). Empty for an alias-free store.
    resolved: &'static [Node],
    /// What slot 0 resolves to (Go `nil`).
    nil: Node,
    facts: StoreFacts,
    /// U4: `FileStore::children`. Next to `resolved`, so a child read loads
    /// one per-store record.
    children: &'static [SlotChildren],
    /// R2-5: `FileStore::links`.
    links: &'static [SlotLinks],
}

/// `try_resolve_store_id(file, index)` for store `file` of publish `f`, whose
/// per-store part is `s`.
// PERF: effect P7-1. Most stores have no alias slot. For them a child id is
// the slot handle (or the slot 0 value), so `Node::new` needs no load from
// a per-slot table.
#[inline]
fn frozen_resolve_slot(f: &Frozen, s: &FrozenStore, file: usize, index: usize) -> Node {
    if !s.facts.alias_free {
        return s.resolved[index];
    }
    let n = if index == NIL_SLOT as usize {
        s.nil
    } else {
        handle(file, index as u32)
    };
    debug_assert_eq!(
        n,
        resolve_slot(
            file,
            index,
            f.nodes[file - f.base],
            f.headers[file - f.base]
        )
    );
    n
}

/// Tier 0: the first publish.
static FROZEN: OnceLock<Frozen> = OnceLock::new();

/// The tier 1 slots of `LATER_CHUNK` consecutive file ids.
type LaterChunk = [OnceLock<&'static Frozen>; LATER_CHUNK];

/// Tier 1: the publish of each file id after the first publish. Each later
/// publish is leaked once, and the slot of each of its ids names it.
static LATER: [OnceLock<Box<LaterChunk>>; TIER1_LIMIT / LATER_CHUNK] =
    [const { OnceLock::new() }; TIER1_LIMIT / LATER_CHUNK];

/// The next unused file id. Only `publish_file_stores` changes it.
static PUBLISHED: AtomicUsize = AtomicUsize::new(0);

/// The tier 1 publish of file `file` and the index of `file` in it.
#[cold]
#[inline(never)]
fn later(file: usize) -> Option<(&'static Frozen, usize)> {
    let chunk = LATER.get(file / LATER_CHUNK)?.get()?;
    let frozen: &'static Frozen = *chunk[file % LATER_CHUNK].get()?;
    Some((frozen, file - frozen.base))
}

/// The one file lookup of the U4 per-store reads (PORTING.md "AST": new
/// store columns go through one helper): the publish that holds store
/// `file` and the index of `file` in its tables. Tier 0 only for now;
/// `None` for any other file (tier 1, unpublished, synthetic, legacy),
/// whose readers take their slow path. The multiprog port can add tier 1
/// (`later`) here.
#[inline]
fn column_store(file: usize) -> Option<(&'static Frozen, usize)> {
    let f = FROZEN.get()?;
    (file < f.per_store.len()).then_some((f, file))
}

/// The handle of slot `index` in store `file`. Does not resolve aliases.
const fn handle(file: usize, index: u32) -> Node {
    Node(((file as u64) << 32) | (index as u64 + 1))
}

/// Slot index of a store handle.
#[inline]
fn slot_index(n: Node) -> usize {
    ((n.0 & 0xffff_ffff) - 1) as usize
}

/// Runs `f` on an unpublished store of this thread: its active, detached
/// or build store. `None` when this thread has no store `file`.
#[inline]
fn with_thread_store<R>(file: usize, f: impl FnOnce(&FileStore) -> R) -> Option<R> {
    build_store(file).map(|store| f(&store.borrow()))
}

/// A store read after a tier 0 miss: a synthetic id (or any id when tier 0
/// is legacy) has no store; any other id takes one cold call.
#[inline]
fn after_tier0_miss<R>(tier0: &Frozen, file: usize, f: impl FnOnce(&FileStore) -> R) -> Option<R> {
    if is_storeless_id(file) || tier0.legacy {
        return None;
    }
    with_later_store(file, f)
}

/// The cold part of `after_tier0_miss`: tier 1, then the detached store,
/// then the build stores of this thread.
#[cold]
#[inline(never)]
fn with_later_store<R>(file: usize, f: impl FnOnce(&FileStore) -> R) -> Option<R> {
    match later(file) {
        Some((frozen, local)) => Some(f(&frozen.stores[local])),
        None => with_thread_store(file, f),
    }
}

/// A published tier 1 store, for readers that need it `'static`. `None`
/// after a tier 0 miss when `file` is not published in tier 1.
#[inline]
fn later_store(tier0: &Frozen, file: usize) -> Option<&'static FileStore> {
    if file >= TIER1_LIMIT || tier0.legacy {
        return None;
    }
    later(file).map(|(frozen, local)| &frozen.stores[local])
}

/// Runs `f` on store `file`: published, or an unpublished store of this
/// thread. `None` when this thread cannot see a store `file`.
#[inline]
fn try_with_store<R>(file: usize, f: impl FnOnce(&FileStore) -> R) -> Option<R> {
    match FROZEN.get() {
        Some(tier0) => match tier0.stores.get(file) {
            Some(store) => Some(f(store)),
            None => after_tier0_miss(tier0, file, f),
        },
        None => with_thread_store(file, f),
    }
}

fn with_store<R>(file: usize, f: impl FnOnce(&FileStore) -> R) -> R {
    try_with_store(file, f)
        .unwrap_or_else(|| panic!("file {file:#x} has no node store on this thread"))
}

/// Runs `f` on unpublished store `file` of this thread. Panics when `file`
/// is published or this thread has no store `file`.
fn with_store_mut<R>(file: usize, f: impl FnOnce(&mut FileStore) -> R) -> R {
    // PERF: query Q8. The parse writes the active store, which is never
    // published (see `ACTIVE`), so it needs no publish check.
    let store = match active_store(file) {
        Some(store) => store,
        None => inactive_unpublished_store(file),
    };
    f(&mut store.borrow_mut())
}

/// The store that `with_store_mut` writes when it is not the active store.
#[inline(never)]
fn inactive_unpublished_store(file: usize) -> StoreCell {
    assert!(
        !is_published(file),
        "cannot change the node store of published file {file:#x}"
    );
    inactive_build_store(file)
        .unwrap_or_else(|| panic!("file {file:#x} has no node store on this thread"))
}

/// Writes the header of the node slot of a store handle. Panics on a frozen
/// store. Data writes go through `replace_store_node_data`, which keeps the
/// U1, U4 and R2-5 build entries of the slot.
fn with_slot_mut<R>(n: Node, f: impl FnOnce(&mut NodeHeader) -> R) -> R {
    with_store_mut(n.file_index(), |s| {
        assert!(!s.frozen, "cannot mutate a node of a finished file");
        let index = slot_index(n);
        match s.nodes[index] {
            Some(_) => f(&mut s.headers[index]),
            None => panic!("store handle does not name a node slot"),
        }
    })
}

// ──────────────────────────────────────────────────────────────────────
// Stores
// ──────────────────────────────────────────────────────────────────────

/// Makes the store of the next parsed file and returns its file id. Ids
/// follow parse order (see `BuildStores`). The store becomes the active
/// store of this thread.
pub fn new_file_store(file_name: &'static str, text: &'static str) -> usize {
    assert_no_legacy_publish();
    let store: StoreCell = leak_in_ast_arena(RefCell::new(FileStore::new(file_name, text)));
    let id = BUILD.with(|b| {
        let mut b = b.borrow_mut();
        let id = b.next_id();
        b.stores.push(store);
        id
    });
    ACTIVE.set(Some((id, store)));
    id
}

/// Panics when tier 0 is a legacy publish: its file ids would collide with
/// store ids.
fn assert_no_legacy_publish() {
    assert!(
        FROZEN.get().is_none_or(|tier0| !tier0.legacy),
        "a legacy program is published; file ids would collide with store ids"
    );
}

/// Text bytes per slot that a new store reserves for (`FileStore::new`).
// PERF: U1 (e). The TypeScript parser makes one node for about 6 to 8 text
// bytes of the Query, Zod and Hono sources, and one for about 14 to 21 bytes
// of the lib and `@types` declaration files and the Effect sources (long
// JSDoc comments). At 12 a declaration file, such as lib.dom, fills its
// vectors without a `realloc` copy, and a source file grows them once.
// `end_parse` gives the unused capacity back.
const STORE_TEXT_BYTES_PER_SLOT: usize = 12;

impl FileStore {
    fn new(file_name: &'static str, text: &'static str) -> Self {
        let slots = text.len() / STORE_TEXT_BYTES_PER_SLOT + 1;
        let mut headers = Vec::with_capacity(slots);
        headers.push(NodeHeader::target(Node::NIL));
        let mut nodes = Vec::with_capacity(slots);
        nodes.push(None);
        let mut build_names = Vec::with_capacity(slots);
        build_names.push(Name::default());
        let mut build_modifier_bits = Vec::with_capacity(slots);
        build_modifier_bits.push(0);
        let mut build_children = Vec::with_capacity(slots);
        build_children.push(SlotChildren::UNKNOWN);
        let mut build_links = Vec::with_capacity(slots);
        build_links.push(SlotLinks::NONE);
        // PERF: U1 (a). About one distinct identifier text per 16 slots, so
        // the map of a large file does not rehash while it grows.
        let identifier_names = FxHashMap::with_capacity_and_hasher(slots / 16, Default::default());
        Self {
            file_name,
            text,
            headers,
            nodes,
            build_names,
            build_modifier_bits,
            build_children,
            build_links,
            identifier_names,
            ..Self::default()
        }
    }

    /// U1 (a): the `names` entry and the `text_is_keyword` bit of a new slot
    /// of kind `kind` with data `node`. The text is `text`, or the data text
    /// when `text` is `None`. `Name::default()` and false for a kind other
    /// than Identifier and PrivateIdentifier.
    #[inline]
    fn slot_text_name(
        &mut self,
        kind: SyntaxKind,
        node: &'static ts_ast::Node,
        text: Option<&str>,
    ) -> (Name, bool) {
        if !matches!(kind, SyntaxKind::Identifier | SyntaxKind::PrivateIdentifier) {
            return (Name::default(), false);
        }
        let text = text.unwrap_or_else(|| identifier_text(node));
        if let Some(entry) = self.identifier_names.get(text) {
            return entry.clone();
        }
        // U1 (d): the key is the interned text, which lives as long as the
        // map. The data of a store identifier has no text to borrow.
        let entry = (
            Name::from(text),
            get_identifier_token(text) != SyntaxKind::Identifier,
        );
        self.identifier_names
            .insert(entry.0.as_str(), entry.clone());
        entry
    }

    /// U1 (b): `bits` as the `modifier_bits` entry of a slot: the value, or
    /// 0 and `modifier_bits_overflow` when it does not fit in 16 bits.
    #[inline]
    fn slot_modifier_bits(&mut self, bits: u32) -> u16 {
        u16::try_from(bits).unwrap_or_else(|_| {
            self.modifier_bits_overflow = true;
            0
        })
    }

    /// The U1 and U4 build vectors have one entry per slot.
    #[inline]
    fn debug_assert_build_columns(&self) {
        debug_assert_eq!(self.build_names.len(), self.headers.len());
        debug_assert_eq!(self.build_modifier_bits.len(), self.headers.len());
        debug_assert_eq!(self.build_children.len(), self.headers.len());
        debug_assert_eq!(self.build_links.len(), self.headers.len());
    }

    /// R2-5: frees the chain of slot `index` (no chain holds its old
    /// children then) and makes the chain of `index` unknown.
    fn unlink_children(&mut self, index: usize) {
        let mut child = std::mem::replace(&mut self.build_links[index].first_child, LINK_NONE);
        if child == LINK_NONE {
            return;
        }
        while child != LINK_END {
            let links = &mut self.build_links[child as usize];
            child = std::mem::replace(&mut links.next_sibling, LINK_NONE);
            debug_assert_ne!(child, LINK_NONE, "R2-5 chain without an end");
        }
    }

    /// R2-5: appends slot `child` to the chain of slot `parent`, whose last
    /// child is `*last` (`LINK_END` before the first). False, with nothing
    /// written, when a chain already holds `child`.
    #[inline]
    fn link_child(&mut self, parent: usize, last: &mut u32, child: usize) -> bool {
        if self.build_links[child].next_sibling != LINK_NONE {
            return false;
        }
        self.build_links[child].next_sibling = LINK_END;
        let child = child as u32;
        if *last == LINK_END {
            self.build_links[parent].first_child = child;
        } else {
            self.build_links[*last as usize].next_sibling = child;
        }
        *last = child;
        true
    }
}

// ──────────────────────────────────────────────────────────────────────
// Detached stores (parse workers)
// ──────────────────────────────────────────────────────────────────────

/// A finished store that a parse worker made with a provisional id. Only
/// `adopt_detached_store` can make it part of the program.
pub struct DetachedStore {
    id: usize,
    store: FileStore,
}

impl DetachedStore {
    /// The provisional id of the store.
    #[must_use]
    pub fn id(&self) -> usize {
        self.id
    }

    /// True when every node the store names is its own. A store that names
    /// a node of another store (an alias slot, for example a synthetic
    /// node of the worker) cannot be adopted.
    #[must_use]
    pub fn is_self_contained(&self) -> bool {
        self.store.frozen && self.store.aliases.is_empty()
    }
}

/// Makes the detached store of this thread with provisional id
/// `DETACHED_STORE_BASE + job` and returns that id. A parse worker parses
/// one file at a time; the store stays until `take_detached_file_store`.
pub fn new_detached_file_store(job: usize, file_name: &'static str, text: &'static str) -> usize {
    assert!(job < DETACHED_STORE_LIMIT, "too many detached stores");
    let id = DETACHED_STORE_BASE + job;
    assert!(
        DETACHED.get().is_none(),
        "this thread already has a detached store"
    );
    let store = SPARE_CELL
        .take()
        .unwrap_or_else(|| leak_in_ast_arena(RefCell::default()));
    *store.borrow_mut() = FileStore::new(file_name, text);
    DETACHED.set(Some((id, store)));
    ACTIVE.set(Some((id, store)));
    id
}

/// Removes the detached store of this thread, if any.
pub fn take_detached_file_store() -> Option<DetachedStore> {
    let (id, cell) = DETACHED.take()?;
    if active_store(id).is_some() {
        ACTIVE.set(None);
    }
    let store = cell.take();
    SPARE_CELL.set(Some(cell));
    Some(DetachedStore { id, store })
}

/// Maps the node handles of an adopted detached store to its real id.
#[derive(Clone, Copy, Debug)]
pub struct StoreRemap {
    from: usize,
    to: usize,
}

impl StoreRemap {
    /// The real store id.
    #[must_use]
    pub fn store(self) -> usize {
        self.to
    }

    /// `n` with the provisional store id replaced by the real one. Other
    /// handles (nil, other stores) do not change.
    #[inline]
    #[must_use]
    pub fn node(self, n: Node) -> Node {
        if n.is_some() && n.file_index() == self.from {
            handle(self.to, slot_index(n) as u32)
        } else {
            n
        }
    }
}

/// Gives a self-contained detached store the next real store id on this
/// thread, as `new_file_store` would have at this point, and returns the
/// handle map for the values the parse returned with it. The store becomes
/// the active store of this thread.
pub fn adopt_detached_store(detached: DetachedStore) -> StoreRemap {
    assert_no_legacy_publish();
    assert!(
        detached.is_self_contained(),
        "cannot adopt a store that names other stores"
    );
    let DetachedStore { id, mut store } = detached;
    let (remap, cell) = BUILD.with(|b| {
        let mut b = b.borrow_mut();
        let remap = StoreRemap {
            from: id,
            to: b.next_id(),
        };
        store.jsdoc_cache = store
            .jsdoc_cache
            .iter()
            .map(|(&node, &jsdocs)| {
                let jsdocs: &'static [Node] = if jsdocs.iter().any(|&n| remap.node(n) != n) {
                    Box::leak(jsdocs.iter().map(|&n| remap.node(n)).collect())
                } else {
                    jsdocs
                };
                (remap.node(node), jsdocs)
            })
            .collect();
        // The lazy JSDoc nodes are synthetic nodes of the parse worker.
        store.lazy_jsdoc_cache = FxHashMap::default();
        // The resolved table holds handles of the store id, which changes
        // here. `publish_file_stores` makes it for the real id. The U1, U4
        // and R2-5 columns are slot-indexed and hold no store id, so they
        // stay.
        store.resolved = Box::default();
        let cell: StoreCell = leak_in_ast_arena(RefCell::new(store));
        b.stores.push(cell);
        (remap, cell)
    });
    ACTIVE.set(Some((remap.to, cell)));
    remap
}

// ──────────────────────────────────────────────────────────────────────
// File registry
// ──────────────────────────────────────────────────────────────────────

/// The `GoFile` of published file `file`. Panics when it is not published.
#[inline]
#[must_use]
pub fn go_file(file: usize) -> &'static GoFile {
    if let Some(tier0) = FROZEN.get()
        && let Some(go_file) = tier0.go_files.get(file)
    {
        return go_file;
    }
    go_file_slow(file)
}

#[cold]
#[inline(never)]
fn go_file_slow(file: usize) -> &'static GoFile {
    try_go_file(file).unwrap_or_else(|| panic!("file {file} is not published"))
}

/// `go_file`, or `None` for a store still being built, a synthetic id or
/// an unknown id.
#[inline]
#[must_use]
pub fn try_go_file(file: usize) -> Option<&'static GoFile> {
    let tier0 = FROZEN.get()?;
    if let Some(go_file) = tier0.go_files.get(file) {
        return Some(go_file);
    }
    if file >= TIER1_LIMIT || tier0.legacy {
        return None;
    }
    later(file).map(|(frozen, local)| &frozen.go_files[local])
}

/// True when `file` has a `GoFile` in the registry (tier 0 or tier 1).
#[inline]
#[must_use]
pub fn is_published(file: usize) -> bool {
    try_go_file(file).is_some()
}

/// Ids of the stores that this thread built and did not publish, in id
/// order. The next publish of this thread gives them their `GoFile`s.
#[must_use]
pub fn unpublished_file_ids() -> std::ops::Range<usize> {
    BUILD.with(|b| {
        let b = b.borrow();
        if b.stores.is_empty() {
            let next = PUBLISHED.load(Ordering::Acquire);
            return next..next;
        }
        b.base..b.base + b.stores.len()
    })
}

/// True when file `file` was parsed by the ported parser.
#[inline]
#[must_use]
pub fn has_file_store(file: usize) -> bool {
    match FROZEN.get() {
        Some(tier0) => {
            file < tier0.headers.len()
                || (!tier0.legacy
                    && !is_storeless_id(file)
                    && with_later_store(file, |_| ()).is_some())
        }
        None => build_store(file).is_some(),
    }
}

/// True when `n` is a node of a store file.
#[inline]
#[must_use]
pub fn is_store_node(n: Node) -> bool {
    n.is_some() && has_file_store(n.file_index())
}

/// Go `file.FileName()` of a store file.
#[must_use]
pub fn file_store_file_name(file: usize) -> &'static str {
    with_store(file, |s| s.file_name)
}

/// Go `file.Text()` of a store file.
#[must_use]
pub fn file_store_text(file: usize) -> &'static str {
    with_store(file, |s| s.text)
}

/// Go `result.jsdocCache = p.createJSDocCache()` in `finishSourceFile`.
// PORT: the lists are leaked so reads can return `&'static` slices, like
// `GoFile::info.jsdoc_cache` after the program is installed.
pub fn set_file_store_js_doc_cache(file: usize, cache: &FxHashMap<Node, Vec<Node>>) {
    let cache = cache
        .iter()
        .map(|(node, jsdocs)| (*node, &*Box::leak(jsdocs.clone().into_boxed_slice())))
        .collect();
    with_store_mut(file, |s| s.jsdoc_cache = cache);
}

/// Go `result.LanguageVariant`, `result.diagnostics` and
/// `result.ContainsNonASCII` in `finishSourceFile`.
// PORT: the diagnostics are leaked so reads can return a `&'static` slice,
// like `GoFile::info.diagnostics` after the publish. A parse without errors
// leaks nothing.
pub fn set_file_store_parse_fields(
    file: usize,
    language_variant: LanguageVariant,
    diagnostics: &[Diagnostic],
    contains_non_ascii: bool,
) {
    let diagnostics: &'static [Diagnostic] = Box::leak(diagnostics.to_vec().into_boxed_slice());
    with_store_mut(file, |s| {
        s.language_variant = language_variant;
        s.diagnostics = diagnostics;
        s.contains_non_ascii = contains_non_ascii;
    });
}

/// Go `file.LanguageVariant` of a store file.
#[must_use]
pub fn file_store_language_variant(file: usize) -> LanguageVariant {
    with_store(file, |s| s.language_variant)
}

/// Go `file.Diagnostics()` (the parse diagnostics) of a store file.
#[must_use]
pub fn file_store_diagnostics(file: usize) -> &'static [Diagnostic] {
    with_store(file, |s| s.diagnostics)
}

/// Go `file.ContainsNonASCII` of a store file: true when the scanner
/// decoded a non-ASCII rune. False for a store that `finishSourceFile` did
/// not finish.
#[must_use]
pub fn file_store_contains_non_ascii(file: usize) -> bool {
    with_store(file, |s| s.contains_non_ascii)
}

/// Go `file.jsdocCache[node]` of a store file whose program is not
/// installed yet. It never parses (Go `EagerJSDoc`).
#[must_use]
pub fn file_store_js_doc(file: usize, node: Node) -> Option<&'static [Node]> {
    with_store(file, |s| {
        s.jsdoc_cache
            .get(&node)
            .or_else(|| s.lazy_jsdoc_cache.get(&node))
            .copied()
    })
}

/// Go `result.SetHasLazyJSDoc(true)` in `finishSourceFile`. The store keeps
/// the parse options and script kind of the file for
/// `resolve_file_store_js_doc`.
pub fn set_file_store_lazy_js_doc(
    file: usize,
    parse_options: &SourceFileParseOptions,
    script_kind: ScriptKind,
) {
    let lazy = Some((parse_options.clone(), script_kind));
    with_store_mut(file, |s| s.lazy_js_doc = lazy);
}

// Go: ast/ast.go:2614 (*SourceFile).resolveJSDoc
/// Go `node.JSDoc(file)` of a store file whose program is not installed
/// yet: the cache, then, in a lazy file (`set_file_store_lazy_js_doc`), Go
/// `parseJSDocForNode`, whose result the cache keeps. None on a cache miss
/// in a file that is not lazy.
// PORT: Go takes `jsdocMu`. A store that is not published has one thread.
// The lists are leaked so reads can return `&'static` slices.
#[must_use]
pub fn resolve_file_store_js_doc(file: usize, node: Node) -> Option<&'static [Node]> {
    if let Some(jsdocs) = file_store_js_doc(file, node) {
        return Some(jsdocs);
    }
    let (parse_options, script_kind, text) = with_store(file, |s| {
        s.lazy_js_doc
            .clone()
            .map(|(parse_options, script_kind)| (parse_options, script_kind, s.text))
    })?;
    let jsdocs: &'static [Node] = Box::leak(
        crate::frontend::parser::parse_js_doc_for_node(&parse_options, text, script_kind, node)
            .into_boxed_slice(),
    );
    with_store_mut(file, |s| s.lazy_jsdoc_cache.insert(node, jsdocs));
    Some(jsdocs)
}

/// True when node reads of store file `file` must use the store, because
/// the file is not published yet (the parser is still running).
#[must_use]
pub fn is_file_store_before_program(file: usize) -> bool {
    !is_published(file) && has_file_store(file)
}

/// Ends the parse of a file. Header and data writes panic after this.
/// Headers cannot change after this, so it also marks the source file roots
/// (`mark_source_file_roots`) and builds the tables that the publish puts
/// in the registry (`FileStore::kinds`, `FileStore::facts`,
/// `FileStore::resolved`) on the parsing thread.
pub fn freeze_file_store(file: usize) {
    with_store_mut(file, |s| s.freeze(file));
}

impl FileStore {
    /// `freeze_file_store` for this store, which has id `file`.
    fn freeze(&mut self, file: usize) {
        self.end_parse();
        // One pass over the headers for the parser flags, the kinds and the
        // facts.
        let mut flags = Vec::with_capacity(self.headers.len());
        self.set_kinds_and_facts(|h| flags.push(h.flags));
        self.parser_flags = Some(flags);
        // PERF: query Q7. The table is made here, on the parse thread, not
        // in `publish_file_stores` on the loader. A detached store gets its
        // real id only when the loader adopts it, so its table waits for
        // `publish_file_stores`. An alias-free store needs no table.
        if !is_detached_id(file) && !self.facts.alias_free {
            self.resolved = self.resolved_table(file);
        }
    }

    /// Makes `kinds`, `facts` and the U1 (e) `bind_estimate` in one pass over
    /// the slots, and calls `each` on every slot header. Then moves the U1,
    /// U4 and R2-5 build vectors into the `names`, `modifier_bits`,
    /// `children` and `links` columns (`move_build_columns`).
    fn set_kinds_and_facts(&mut self, mut each: impl FnMut(&NodeHeader)) {
        let mut facts = StoreFacts::ONLY_NIL_SLOT;
        let mut kinds = Vec::with_capacity(self.headers.len());
        let mut counts = BindCounts::default();
        for (i, (h, node)) in self.headers.iter().zip(&self.nodes).enumerate() {
            each(h);
            kinds.push(h.kind);
            counts.add(h.kind);
            if i != NIL_SLOT as usize {
                facts.add(h, node.is_some());
            }
        }
        self.kinds = kinds.into_boxed_slice();
        self.facts = facts;
        self.bind_estimate = counts.estimate();
        self.move_build_columns();
    }

    /// U1 (a) (b), U4, R2-5: moves `build_names`, `build_modifier_bits`,
    /// `build_children` and `build_links`, made when each slot was made,
    /// into `names`, `modifier_bits`, `children` and `links`, and drops
    /// `identifier_names`. Needs `kinds`. A modifier vector without one entry
    /// per slot is not used: `modifier_bits_column` makes that column from
    /// the slots.
    // PERF: no pass over the node data. Debug builds check the moved columns
    // and the header keyword bits against the node data.
    fn move_build_columns(&mut self) {
        let slots = self.headers.len();
        self.identifier_names = FxHashMap::default();
        let names = std::mem::take(&mut self.build_names);
        // PORT: U1 (d). The name column is the only copy of the text of an
        // identifier that `alloc_store_name_node` or
        // `alloc_store_shared_name_node` made, so it cannot be made again
        // from the node data. Every slot push adds its entry.
        assert_eq!(
            names.len(),
            slots,
            "U1 (a) build_names must have one entry per slot"
        );
        self.names = names.into_boxed_slice();
        #[cfg(debug_assertions)]
        self.debug_check_text_names();
        let bits = std::mem::take(&mut self.build_modifier_bits);
        // PORT: a slot whose value did not fit may have got new data since
        // (`replace_store_node_data`), so an overflow makes the column from
        // the slots, as before. Store lists hold 16-bit values, so this does
        // not happen.
        if bits.len() == slots && !self.modifier_bits_overflow {
            self.modifier_bits = bits.into_boxed_slice();
            debug_assert_eq!(
                self.modifier_bits,
                self.modifier_bits_column(),
                "U1 (b) modifier bits differ from modifier_bits_column"
            );
        } else {
            self.modifier_bits = self.modifier_bits_column();
        }
        // U4: a vector without one entry per slot (not expected) gives an
        // all-unknown column, whose reads take the node data.
        let children = std::mem::take(&mut self.build_children);
        self.children = if children.len() == slots {
            children.into_boxed_slice()
        } else {
            vec![SlotChildren::UNKNOWN; slots].into_boxed_slice()
        };
        // PORT: a child written after the slot was made must have gone
        // through `replace_store_node_data`, which makes the entry again.
        // C2: the check covers the `typed` field too.
        debug_assert!(
            self.children_column_matches(),
            "U4 children column differs from the node data"
        );
        // R2-5: the same rule. The chains are checked against Go
        // `ForEachChild` when the binder walks them (`bind_each_child`).
        let links = std::mem::take(&mut self.build_links);
        self.links = if links.len() == slots {
            links.into_boxed_slice()
        } else {
            vec![SlotLinks::NONE; slots].into_boxed_slice()
        };
    }

    /// U4, debug builds: true when every `children` entry is unknown or
    /// equals the value `store_node_children` makes from the final node data
    /// of the slot. Needs `kinds`.
    fn children_column_matches(&self) -> bool {
        let slots = self.kinds.iter().zip(&self.nodes).zip(&self.children[..]);
        slots.enumerate().all(|(i, ((&kind, node), &entry))| {
            let expected = match node {
                Some(node) if i != NIL_SLOT as usize => {
                    super::node::store_node_children(kind, node)
                }
                _ => SlotChildren::UNKNOWN,
            };
            entry == expected || entry == SlotChildren::UNKNOWN
        })
    }

    /// U1 (a) (d), debug builds: checks `names` and the `text_is_keyword`
    /// header bits against `kinds` and the node data. An identifier slot
    /// whose data has a text has that name; one whose data text is empty
    /// (`alloc_store_name_node`, `alloc_store_shared_name_node`) keeps the
    /// name it was made with.
    #[cfg(debug_assertions)]
    fn debug_check_text_names(&self) {
        let slots = self.kinds.iter().zip(&self.nodes).zip(&self.headers);
        for (((&kind, node), header), name) in slots.zip(&self.names[..]) {
            match (kind, node) {
                (SyntaxKind::Identifier | SyntaxKind::PrivateIdentifier, Some(node)) => {
                    let text = identifier_text(node);
                    assert!(
                        text.is_empty() || name.as_str() == text,
                        "U1 (a) name differs from the node data"
                    );
                    assert_eq!(
                        header.text_is_keyword,
                        get_identifier_token(name.as_str()) != SyntaxKind::Identifier,
                        "U1 (a) keyword bit differs from the name"
                    );
                }
                _ => {
                    assert_eq!(*name, Name::default(), "U1 (a) name on a non-name slot");
                    assert!(
                        !header.text_is_keyword,
                        "U1 (a) keyword bit on a non-name slot"
                    );
                }
            }
        }
    }

    /// U1 (b): `FileStore::modifier_bits` from `kinds`. Only the slots whose
    /// kind can hold a modifier list read their data. Empty when a value
    /// does not fit in 16 bits. `move_build_columns` uses it only when
    /// `build_modifier_bits` cannot be used, and to check it in debug builds.
    // PORT: store lists hold `ModifiersToFlags(nodes)`, which only has the
    // syntactic bits (`ModifierFlags::SYNTACTIC_MODIFIERS`, 16 bits). The
    // empty column keeps the result exact if that ever changes.
    fn modifier_bits_column(&self) -> Box<[u16]> {
        let mut bits = Vec::with_capacity(self.kinds.len());
        for (&kind, node) in self.kinds.iter().zip(&self.nodes) {
            let flags = node.map_or(0, |node| super::node::store_node_modifier_bits(kind, node));
            match u16::try_from(flags) {
                Ok(flags) => bits.push(flags),
                Err(_) => return Box::default(),
            }
        }
        bits.into_boxed_slice()
    }

    /// Marks the store finished and marks its source file roots.
    fn end_parse(&mut self) {
        self.frozen = true;
        self.headers.shrink_to_fit();
        self.nodes.shrink_to_fit();
        mark_source_file_roots(self);
    }

    /// `resolve_slot(file, i, ..)` for every slot, for store id `file`.
    fn resolved_table(&self, file: usize) -> Box<[Node]> {
        (0..self.headers.len())
            .map(|i| resolve_slot(file, i, &self.nodes, &self.headers))
            .collect()
    }

    /// The part of `publish_file_stores` for this store, which has id
    /// `file`: drops what only the parse and the loader used, and makes a
    /// table that `freeze_file_store` did not make or that no longer fits
    /// the slots.
    fn publish(&mut self, file: usize) {
        if !self.frozen {
            // PORT: a store whose parse did not finish (a parse panic).
            self.end_parse();
            // R2-5: a panic can stop the parser between two children of a
            // node, so its chains may be partial. No links: the binder uses
            // Go `ForEachChild` (`move_build_columns`).
            self.build_links = Vec::new();
        }
        self.aliases = FxHashMap::default();
        self.jsdoc_cache = FxHashMap::default();
        self.lazy_js_doc = None;
        self.lazy_jsdoc_cache = FxHashMap::default();
        self.parser_flags = None;
        if self.root_slot != NIL_SLOT {
            self.root = handle(file, self.root_slot);
        }
        if self.kinds.len() != self.headers.len() {
            self.set_kinds_and_facts(|_| {});
        }
        if !self.facts.alias_free && self.resolved.len() != self.headers.len() {
            self.resolved = self.resolved_table(file);
        }
    }

    /// About how much work `publish` does, in slots: a fixed part for the
    /// maps it drops and one per slot of each table it still makes.
    fn publish_work(&self) -> usize {
        let slots = self.headers.len();
        let mut work = PUBLISH_WORK_PER_STORE;
        // `facts` is valid only when `kinds` is made.
        let kinds_made = self.kinds.len() == slots;
        if !kinds_made {
            work += slots;
        }
        if self.resolved.len() != slots && !(kinds_made && self.facts.alias_free) {
            work += slots;
        }
        work
    }
}

/// `FileStore::publish_work` of one store without tables to make: about
/// the cost of its map drops, in slots.
const PUBLISH_WORK_PER_STORE: usize = 32;
/// `publish_stores` uses scoped threads from this much work on. Below it
/// the thread starts cost more than they save.
const PARALLEL_PUBLISH_WORK: usize = 1 << 17;
/// Threads for `publish_stores`, the calling thread included.
const PUBLISH_THREADS: usize = 4;

/// `FileStore::publish` for every store; store `i` has id `base + i`.
// PERF: effect R2-13. The stores are independent, so a large program is
// split into `PUBLISH_THREADS` runs of about equal work, one per scoped
// thread. The result does not depend on the split.
fn publish_stores(stores: &mut [FileStore], base: usize) {
    let total: usize = stores.iter().map(FileStore::publish_work).sum();
    if total < PARALLEL_PUBLISH_WORK {
        publish_run(stores, base);
        return;
    }
    let share = total.div_ceil(PUBLISH_THREADS);
    std::thread::scope(|scope| {
        let mut rest = stores;
        let mut first = base;
        for _ in 1..PUBLISH_THREADS {
            if rest.is_empty() {
                break;
            }
            let mut end = 0;
            let mut work = 0;
            while end < rest.len() && work < share {
                work += rest[end].publish_work();
                end += 1;
            }
            let (run, tail) = std::mem::take(&mut rest).split_at_mut(end);
            scope.spawn(move || publish_run(run, first));
            first += end;
            rest = tail;
        }
        publish_run(rest, first);
    });
}

/// `FileStore::publish` for `stores`, whose first store has id `first`.
fn publish_run(stores: &mut [FileStore], first: usize) {
    for (i, store) in stores.iter_mut().enumerate() {
        store.publish(first + i);
    }
}

/// True when the parse of store file `file` is over: the file is published
/// or `freeze_file_store` ran.
#[must_use]
pub fn is_file_store_frozen(file: usize) -> bool {
    is_published(file) || with_store(file, |s| s.frozen)
}

/// Number of slots (nil, alias and node slots). Per-node vectors that are
/// indexed by `NodeId::index()` (`GoFile::node_bind`) need this length.
#[must_use]
pub fn file_store_slot_count(file: usize) -> usize {
    with_store(file, |s| s.headers.len())
}

/// The parser `node.Flags` of every slot, indexed by slot index. Nil and
/// alias slots give no flags. The loader fills `GoFile::parser_flags` from
/// this, so the binder reads the same flags as for a legacy file.
#[must_use]
pub fn file_store_parser_flags(file: usize) -> Vec<NodeFlags> {
    let computed = |s: &FileStore| s.headers.iter().map(|h| h.flags).collect();
    if is_published(file) {
        return with_store(file, computed);
    }
    with_store_mut(file, |s| {
        s.parser_flags.take().unwrap_or_else(|| computed(s))
    })
}

/// Publishes the build stores of this thread: `go_files[i]` is the
/// `GoFile` of id `unpublished_file_ids().start + i`. The legacy loader has
/// no stores and passes its files. The loader calls this once per program,
/// before `core::set_prog`. The stores are then read-only, and any thread
/// can read them. The first publish is tier 0; later ones go to tier 1. An
/// empty later publish does nothing.
// PORT: Go needs no publish; its nodes are heap objects. The publish also
// computes `NodeHeader::source_file_is_root` for `get_source_file_of_node`.
pub fn publish_file_stores(go_files: Vec<GoFile>) {
    // The cells stay leaked and empty. Nothing reads them after this.
    ACTIVE.set(None);
    let BuildStores {
        base,
        stores: cells,
    } = BUILD.with(|b| std::mem::take(&mut *b.borrow_mut()));
    let base = if cells.is_empty() {
        PUBLISHED.load(Ordering::Acquire)
    } else {
        base
    };
    let legacy = cells.is_empty() && !go_files.is_empty();
    assert!(
        legacy || go_files.len() == cells.len(),
        "a publish needs one GoFile per store ({} stores, {} GoFiles)",
        cells.len(),
        go_files.len()
    );
    let tier0 = FROZEN.get();
    if let Some(tier0) = tier0 {
        assert!(
            !tier0.legacy && !legacy,
            "a legacy program must be the only publish; file ids would collide with store ids"
        );
        if go_files.is_empty() {
            return;
        }
    }
    let count = cells.len().max(go_files.len());
    assert!(base + count <= TIER1_LIMIT, "too many file ids");
    if let Err(published) =
        PUBLISHED.compare_exchange(base, base + count, Ordering::AcqRel, Ordering::Acquire)
    {
        panic!(
            "another thread published file ids while this thread built ids {base}.. (now {published})"
        );
    }
    let mut stores: Vec<FileStore> = cells.iter().map(|cell| cell.take()).collect();
    publish_stores(&mut stores, base);
    let stores: &'static [FileStore] = Box::leak(stores.into_boxed_slice());
    // PERF: query Q7. The per-store tables are made already, so this only
    // collects slices.
    let frozen = Frozen {
        base,
        stores,
        headers: stores.iter().map(|s| &s.headers[..]).collect(),
        nodes: stores.iter().map(|s| &s.nodes[..]).collect(),
        kinds: stores.iter().map(|s| &s.kinds[..]).collect(),
        names: stores.iter().map(|s| &s.names[..]).collect(),
        modifier_bits: stores.iter().map(|s| &s.modifier_bits[..]).collect(),
        per_store: stores
            .iter()
            .enumerate()
            .map(|(i, s)| FrozenStore {
                resolved: &s.resolved[..],
                nil: resolve_slot(base + i, NIL_SLOT as usize, &s.nodes, &s.headers),
                facts: s.facts,
                children: &s.children[..],
                links: &s.links[..],
            })
            .collect(),
        go_files: go_files.into_boxed_slice(),
        legacy,
    };
    if tier0.is_none() {
        assert_eq!(base, 0, "the first publish must start at file id 0");
        assert!(
            FROZEN.set(frozen).is_ok(),
            "another thread made the first publish"
        );
        return;
    }
    let frozen: &'static Frozen = Box::leak(Box::new(frozen));
    for file in base..base + count {
        let chunk = LATER[file / LATER_CHUNK]
            .get_or_init(|| Box::new([const { OnceLock::new() }; LATER_CHUNK]));
        assert!(
            chunk[file % LATER_CHUNK].set(frozen).is_ok(),
            "file {file} is already published"
        );
    }
}

/// Sets `store.root_slot` and `NodeHeader::source_file_is_root` of each node
/// slot whose Go parent walk (`GetSourceFileOfNode`) ends at that root.
/// Headers are frozen, so the walk result cannot change. A walk that leaves
/// the store (a synthetic or foreign parent) stays unmarked and is walked
/// at read time.
fn mark_source_file_roots(store: &mut FileStore) {
    // PORT: the parser makes the SourceFile node last, so the root is the
    // last SourceFile slot. Any other SourceFile node stays unmarked.
    let Some(root) = (0..store.headers.len())
        .rev()
        .find(|&i| store.nodes[i].is_some() && store.headers[i].kind == SyntaxKind::SourceFile)
    else {
        return;
    };
    store.root_slot = root as u32;

    const UNSEEN: u8 = 0;
    const ON_PATH: u8 = 1;
    const ROOT: u8 = 2;
    const NOT_ROOT: u8 = 3;
    let mut state = vec![UNSEEN; store.headers.len()];
    let mut path = Vec::new();
    // The parser makes a parent after its children, so most parents have a
    // higher slot. Walking the slots down finds them already marked.
    for start in (1..store.headers.len()).rev() {
        if store.nodes[start].is_none() {
            continue;
        }
        let header = &store.headers[start];
        let parent = header.parent;
        if header.kind != SyntaxKind::SourceFile
            && parent.file_index() == LOCAL_STORE
            && matches!(state[slot_index(parent)], ROOT | NOT_ROOT)
        {
            let result = state[slot_index(parent)];
            state[start] = result;
            store.headers[start].source_file_is_root = result == ROOT;
            continue;
        }
        let mut cur = start;
        let result = loop {
            match state[cur] {
                ROOT | NOT_ROOT => break state[cur],
                // A parent cycle: Go never returns. Leave it to the walk.
                ON_PATH => break NOT_ROOT,
                _ => {}
            }
            state[cur] = ON_PATH;
            path.push(cur);
            let header = &store.headers[cur];
            if header.kind == SyntaxKind::SourceFile {
                break if cur == root { ROOT } else { NOT_ROOT };
            }
            let parent = header.parent;
            if parent.file_index() != LOCAL_STORE {
                break NOT_ROOT;
            }
            cur = slot_index(parent);
        };
        for i in path.drain(..) {
            state[i] = result;
            store.headers[i].source_file_is_root = result == ROOT;
        }
    }
}

// ──────────────────────────────────────────────────────────────────────
// Read hooks for node.rs and core.rs
// ──────────────────────────────────────────────────────────────────────

/// Hook for `Node::new(file, id)` on a store file: the Go node that a child
/// id inside store `NodeData` stands for.
#[inline]
#[must_use]
pub fn resolve_store_id(file: usize, id: ts_ast::NodeId) -> Node {
    let index = id.index();
    let resolve = |s: &FileStore| match s.nodes[index] {
        Some(_) => handle(file, index as u32),
        // The nil slot or an alias slot: the target is in the header.
        None => s.headers[index].parent,
    };
    if let Some(f) = FROZEN.get()
        && file < f.nodes.len()
    {
        return match f.nodes[file][index] {
            Some(_) => handle(file, index as u32),
            None => f.headers[file][index].parent,
        };
    }
    with_store(file, resolve)
}

/// Hook for `raw(n)`: the ts_ast node (Go kind and data) of a store node.
#[inline]
#[must_use]
pub fn store_ast_node(n: Node) -> &'static ts_ast::Node {
    let get =
        |s: &FileStore| s.nodes[slot_index(n)].expect("store handle does not name a node slot");
    if let Some(f) = FROZEN.get()
        && n.file_index() < f.nodes.len()
    {
        return f.nodes[n.file_index()][slot_index(n)]
            .expect("store handle does not name a node slot");
    }
    with_store(n.file_index(), get)
}

/// Hook for `Node::kind`, `flags`, `parent` and `loc` on a store node.
#[inline]
#[must_use]
pub fn store_header(n: Node) -> NodeHeader {
    let get = |s: &FileStore| {
        let index = slot_index(n);
        debug_assert!(
            s.nodes[index].is_some(),
            "store handle does not name a node slot"
        );
        s.headers[index].read(n.file_index())
    };
    if let Some(f) = FROZEN.get()
        && n.file_index() < f.headers.len()
    {
        let (file, index) = (n.file_index(), slot_index(n));
        debug_assert!(
            f.nodes[file][index].is_some(),
            "store handle does not name a node slot"
        );
        return f.headers[file][index].read(file);
    }
    with_store(n.file_index(), get)
}

/// The header of `n` when it is a store node (kind, parser flags, parent,
/// loc): one thread-local load for the active store, one table lookup in
/// tier 0, one more thread-local access before the first publish. `None`
/// for nil, synthetic and legacy nodes. With it a node read needs no
/// separate `has_file_store` call.
// PERF: query Q8. The active store is checked first and inline; every
// other case is out of line.
#[inline]
#[must_use]
pub fn try_store_header(n: Node) -> Option<NodeHeader> {
    if n.is_nil() {
        return None;
    }
    match active_store_header(n) {
        Some(header) => Some(header),
        None => try_store_header_slow(n.file_index(), slot_index(n)),
    }
}

/// `try_store_header` for a node that is not in the active store.
#[inline(never)]
fn try_store_header_slow(file: usize, index: usize) -> Option<NodeHeader> {
    let read = |s: &FileStore| s.headers[index].read(file);
    match FROZEN.get() {
        Some(f) => match f.headers.get(file) {
            Some(headers) => Some(headers[index].read(file)),
            None => after_tier0_miss(f, file, read),
        },
        None => inactive_build_store(file).map(|store| read(&store.borrow())),
    }
}

/// The header of `n` when `n` is a node of the active store of this thread
/// (see `ACTIVE`): the parse fast path of the node reads. That store is not
/// published. `None` for any other node.
#[inline]
#[must_use]
pub fn active_store_header(n: Node) -> Option<NodeHeader> {
    if n.is_nil() {
        return None;
    }
    let file = n.file_index();
    let store = active_store(file)?;
    Some(store.borrow().headers[slot_index(n)].read(file))
}

/// Go `node.Kind` of a tier 0 store node. `None` for any other node: nil,
/// synthetic, legacy, tier 1 and unpublished store nodes.
#[inline]
#[must_use]
pub fn frozen_store_kind(n: Node) -> Option<SyntaxKind> {
    if n.is_nil() {
        return None;
    }
    let kinds = FROZEN.get()?.kinds.get(n.file_index())?;
    Some(kinds[slot_index(n)])
}

/// The header of a tier 0 store node, by reference, so a read of one field
/// does not copy the whole header. The parent is still in its stored
/// form (see `LOCAL_STORE`). `None` as for `frozen_store_kind`.
#[inline]
fn frozen_header(n: Node) -> Option<&'static NodeHeader> {
    if n.is_nil() {
        return None;
    }
    let headers = FROZEN.get()?.headers.get(n.file_index())?;
    Some(&headers[slot_index(n)])
}

/// Parser `node.Flags` of a tier 0 store node (see `frozen_header`).
#[inline]
#[must_use]
pub fn frozen_store_flags(n: Node) -> Option<NodeFlags> {
    frozen_header(n).map(|h| h.flags)
}

/// Go `node.Loc` of a tier 0 store node (see `frozen_header`).
#[inline]
#[must_use]
pub fn frozen_store_loc(n: Node) -> Option<TextRange> {
    frozen_header(n).map(|h| h.loc)
}

/// Go `node.Parent` of a tier 0 store node (see `frozen_header`).
#[inline]
#[must_use]
pub fn frozen_store_parent(n: Node) -> Option<Node> {
    frozen_header(n).map(|h| h.read(n.file_index()).parent)
}

/// The ts_ast node of a tier 0 store node: the inlined fast path of
/// `ast_node_of`. `None` as for `frozen_store_kind`. Panics like
/// `try_store_ast_node` on a nil or alias slot.
#[inline]
#[must_use]
pub fn frozen_store_ast_node(n: Node) -> Option<&'static ts_ast::Node> {
    if n.is_nil() {
        return None;
    }
    let nodes = FROZEN.get()?.nodes.get(n.file_index())?;
    Some(nodes[slot_index(n)].expect("store handle does not name a node slot"))
}

/// `store_ast_node(n)` when `n` is a store node, in one lookup (see
/// `try_store_header`). `None` for nil, synthetic and legacy nodes.
#[inline]
#[must_use]
pub fn try_store_ast_node(n: Node) -> Option<&'static ts_ast::Node> {
    if n.is_nil() {
        return None;
    }
    let (file, index) = (n.file_index(), slot_index(n));
    // PERF: query Q8, see `ACTIVE`.
    if let Some(store) = active_store(file) {
        return Some(slot_node(store.borrow().nodes[index]));
    }
    try_store_ast_node_slow(file, index)
}

/// `try_store_ast_node` for a node that is not in the active store.
#[inline(never)]
fn try_store_ast_node_slow(file: usize, index: usize) -> Option<&'static ts_ast::Node> {
    let read = |s: &FileStore| slot_node(s.nodes[index]);
    match FROZEN.get() {
        Some(f) => match f.nodes.get(file) {
            Some(nodes) => Some(slot_node(nodes[index])),
            None => after_tier0_miss(f, file, read),
        },
        None => inactive_build_store(file).map(|store| read(&store.borrow())),
    }
}

/// The ts_ast node of a node slot. Panics on the nil slot and alias slots.
#[inline]
fn slot_node(slot: Option<&'static ts_ast::Node>) -> &'static ts_ast::Node {
    slot.expect("store handle does not name a node slot")
}

/// `resolve_store_id(file, id)` when `file` has a store, in one lookup (see
/// `try_store_header`). `None` when it has none.
#[inline]
#[must_use]
pub fn try_resolve_store_id(file: usize, id: ts_ast::NodeId) -> Option<Node> {
    let index = id.index();
    // PERF: query Q8, see `ACTIVE`.
    if let Some(store) = active_store(file) {
        let s = store.borrow();
        return Some(resolve_slot(file, index, &s.nodes, &s.headers));
    }
    try_resolve_store_id_slow(file, index)
}

/// `try_resolve_store_id` for a file that is not the active store.
#[inline(never)]
fn try_resolve_store_id_slow(file: usize, index: usize) -> Option<Node> {
    let resolve = |s: &FileStore| resolve_slot(file, index, &s.nodes, &s.headers);
    match FROZEN.get() {
        Some(f) => match f.per_store.get(file) {
            Some(s) => Some(frozen_resolve_slot(f, s, file, index)),
            None => after_tier0_miss(f, file, resolve),
        },
        None => inactive_build_store(file).map(|store| resolve(&store.borrow())),
    }
}

/// The text in the data of an Identifier or PrivateIdentifier node. Empty
/// for a store node made by `alloc_store_name_node` or
/// `alloc_store_shared_name_node` (see `store_identifier_name`) and for
/// other kinds.
fn identifier_text(node: &ts_ast::Node) -> &str {
    match &node.data {
        NodeData::Identifier(d) => &d.text,
        NodeData::PrivateIdentifier(d) => &d.text,
        _ => "",
    }
}

/// U1 (d): Go `node.Text()` of an Identifier or PrivateIdentifier store
/// node, from the name column of its slot (`FileStore::names`, or
/// `build_names` while the file is parsed), in tier 0, tier 1 or an
/// unpublished store of this thread. `None` for nil, synthetic and legacy
/// nodes. `Name::default()` (the empty text) for other slots.
#[inline]
#[must_use]
pub fn store_identifier_name(n: Node) -> Option<Name> {
    if n.is_nil() {
        return None;
    }
    let (file, index) = (n.file_index(), slot_index(n));
    if let Some(f) = FROZEN.get()
        && let Some(names) = f.names.get(file)
    {
        return Some(names[index].clone());
    }
    store_identifier_name_slow(file, index)
}

/// `store_identifier_name` for a node that is not in tier 0: a tier 1
/// store, or an unpublished (built or detached) store of this thread.
// PORT: the name column is the only copy of the text, so every store that
// a thread can read must answer here, not only tier 0.
#[inline(never)]
fn store_identifier_name_slow(file: usize, index: usize) -> Option<Name> {
    let read = |s: &FileStore| {
        // A finished file has moved `build_names` into `names`.
        let names = if s.names.len() == s.headers.len() {
            &s.names[..]
        } else {
            &s.build_names[..]
        };
        names[index].clone()
    };
    match FROZEN.get() {
        Some(tier0) => after_tier0_miss(tier0, file, read),
        None => with_thread_store(file, read),
    }
}

/// The node for slot `index` of store `file`: the slot itself when it holds
/// a node, else the handle stored in its header.
fn resolve_slot(
    file: usize,
    index: usize,
    nodes: &[Option<&'static ts_ast::Node>],
    headers: &[NodeHeader],
) -> Node {
    match nodes[index] {
        Some(_) => handle(file, index as u32),
        None => headers[index].parent,
    }
}

/// `try_resolve_store_id(file, _)` for every slot of tier 0 store `file`,
/// indexed by `NodeId::index()`. `None` for any other file and for an
/// alias-free store, which has no table (`Node::new` resolves its ids
/// without one).
#[inline]
#[must_use]
pub fn frozen_resolved(file: usize) -> Option<&'static [Node]> {
    let s = FROZEN.get()?.per_store.get(file)?;
    (!s.facts.alias_free).then_some(s.resolved)
}

/// Hook for `Node::new(file, id)` on a tier 0 store: `try_resolve_store_id(
/// file, id)` without a per-slot table load for an alias-free store. `None`
/// for any other file (tier 1, unpublished, synthetic or legacy).
#[inline]
#[must_use]
pub fn frozen_resolve_store_id(file: usize, id: ts_ast::NodeId) -> Option<Node> {
    let f = FROZEN.get()?;
    let s = f.per_store.get(file)?;
    Some(frozen_resolve_slot(f, s, file, id.index()))
}

/// The `StoreFacts` of tier 0 store `file`. `None` for any other file.
#[inline]
#[must_use]
pub fn frozen_store_facts(file: usize) -> Option<StoreFacts> {
    FROZEN.get()?.per_store.get(file).map(|s| s.facts)
}

/// The `StoreFacts` of the store of `n` when it is a tier 0 store node.
/// `None` for any other node: nil, synthetic, legacy, tier 1 and
/// unpublished store nodes.
#[inline]
#[must_use]
pub fn frozen_node_store_facts(n: Node) -> Option<StoreFacts> {
    if n.is_nil() {
        return None;
    }
    frozen_store_facts(n.file_index())
}

/// Go `SourceFile.ECMALineMap()` of published store file `file`. It is
/// computed once and shared by every thread. `None` for an unpublished
/// store or a file without a store.
#[must_use]
pub fn frozen_file_ecma_line_starts(file: usize) -> Option<&'static [i32]> {
    let tier0 = FROZEN.get()?;
    let store = match tier0.stores.get(file) {
        Some(store) => store,
        None => later_store(tier0, file)?,
    };
    Some(store.ecma_line_starts.get_or_init(|| {
        crate::scanner_util::compute_ecma_line_starts(store.text).into_boxed_slice()
    }))
}

/// Go `GetSourceFileOfNode(n)` in O(1), when `n` is a published store node
/// whose parent walk ends at its store root. `None` means "walk".
#[inline]
#[must_use]
pub fn frozen_source_file_of_node(n: Node) -> Option<Node> {
    if n.is_nil() {
        return None;
    }
    let f = FROZEN.get()?;
    let file = n.file_index();
    let Some(headers) = f.headers.get(file) else {
        let store = later_store(f, file)?;
        return store.headers[slot_index(n)]
            .source_file_is_root
            .then_some(store.root);
    };
    headers[slot_index(n)]
        .source_file_is_root
        .then(|| f.stores[file].root)
}

/// U1 (a): Go `node.Text()` of a tier 0 Identifier or PrivateIdentifier
/// store node, interned when its slot was made (`FileStore::names`).
/// `None` for other kinds and for any other node: nil, synthetic, legacy,
/// tier 1 and unpublished store nodes.
#[inline]
#[must_use]
pub fn frozen_store_text_name(n: Node) -> Option<Name> {
    if n.is_nil() {
        return None;
    }
    let f = FROZEN.get()?;
    let (file, index) = (n.file_index(), slot_index(n));
    match f.kinds.get(file)?[index] {
        SyntaxKind::Identifier | SyntaxKind::PrivateIdentifier => {
            Some(f.names[file][index].clone())
        }
        _ => None,
    }
}

/// U1 (a): Go `scanner.GetIdentifierToken(node.Text()) != KindIdentifier` of
/// a tier 0 Identifier or PrivateIdentifier store node, from its header.
/// `None` as for `frozen_store_text_name`.
#[inline]
#[must_use]
pub fn frozen_store_text_is_keyword(n: Node) -> Option<bool> {
    let h = frozen_header(n)?;
    matches!(
        h.kind,
        SyntaxKind::Identifier | SyntaxKind::PrivateIdentifier
    )
    .then_some(h.text_is_keyword)
}

/// U1 (b): Go `node.ModifierFlags()` (the flags of the node's own modifier
/// list) of a tier 0 store node, from `FileStore::modifier_bits`. `None`
/// for a store whose column is empty and for any other node: nil,
/// synthetic, legacy, tier 1 and unpublished store nodes.
#[inline]
#[must_use]
pub fn frozen_store_modifier_flags(n: Node) -> Option<ModifierFlags> {
    if n.is_nil() {
        return None;
    }
    let bits = FROZEN.get()?.modifier_bits.get(n.file_index())?;
    bits.get(slot_index(n))
        .map(|&bits| ModifierFlags(u32::from(bits)))
}

/// U4 (CH6, bind A): Go `n.Name()`, `n.Expression()`, `n.PostfixToken()` or
/// `n.QuestionToken()` (`which`) of a tier 0 store node, from the
/// `children` column of its store (`SlotChildren`), resolved like
/// `Node::new`. C2: also Go `n.Type()`, `n.Initializer()` and
/// `n.AsTypeReference().TypeName`. `None` when the entry is unknown and for
/// any other node (nil, synthetic, legacy, tier 1, unpublished): the caller
/// reads the node data.
#[inline]
#[must_use]
pub fn frozen_store_child(n: Node, which: StoreChild) -> Option<Node> {
    if n.is_nil() {
        return None;
    }
    let file = n.file_index();
    let (f, local) = column_store(file)?;
    let s = &f.per_store[local];
    let entry = *s.children.get(slot_index(n))?;
    let id = match which {
        StoreChild::Name => {
            if entry.name == SlotChildren::UNKNOWN_ID {
                return None;
            }
            entry.name
        }
        StoreChild::Expression | StoreChild::PostfixToken | StoreChild::QuestionToken => {
            let (tag, id) = entry.other_parts();
            match (which, tag) {
                (_, SlotChildren::TAG_UNKNOWN) => return None,
                (StoreChild::Expression, SlotChildren::TAG_EXPRESSION)
                | (StoreChild::PostfixToken, SlotChildren::TAG_POSTFIX)
                | (StoreChild::QuestionToken, SlotChildren::TAG_QUESTION) => id,
                // Go `QuestionToken()` of a kind with a postfix token: that
                // token when it is a `?` token (`question_of_postfix`).
                (StoreChild::QuestionToken, SlotChildren::TAG_POSTFIX) => {
                    let postfix = column_child(f, s, file, id);
                    let is_question =
                        postfix.is_some() && postfix.kind() == SyntaxKind::QuestionToken;
                    return Some(if is_question { postfix } else { Node::NIL });
                }
                // The kind of `n` has no such field.
                _ => NIL_SLOT,
            }
        }
        StoreChild::Type | StoreChild::Initializer | StoreChild::TypeName => {
            let (tag, id) = entry.typed_parts();
            match (which, tag) {
                (_, SlotChildren::TYPED_UNKNOWN) => return None,
                (
                    StoreChild::Type,
                    SlotChildren::TYPED_TYPE | SlotChildren::TYPED_TYPE_WITH_INITIALIZER,
                )
                | (StoreChild::Initializer, SlotChildren::TYPED_INITIALIZER)
                | (StoreChild::TypeName, SlotChildren::TYPED_TYPE_NAME) => id,
                // An initializer that the column does not hold.
                (StoreChild::Initializer, SlotChildren::TYPED_TYPE_WITH_INITIALIZER) => {
                    return None;
                }
                // Go `AsTypeReference()` panics on other kinds; the data read
                // keeps the panic.
                (StoreChild::TypeName, _) => return None,
                // The field is nil, or the kind of `n` has no such field.
                _ => NIL_SLOT,
            }
        }
    };
    Some(column_child(f, s, file, id))
}

/// C2: true when `n` is a tier 0 store node whose Go `TypeArgumentList()`
/// is nil with no list in its node data (`SlotChildren` `NO_TYPE_ARGUMENTS`),
/// so `Node::type_argument_list` is `NodeList::NIL`. False when not known and
/// for any other node (nil, synthetic, legacy, tier 1, unpublished).
#[inline]
#[must_use]
pub fn frozen_store_lacks_type_arguments(n: Node) -> bool {
    if n.is_nil() {
        return false;
    }
    column_store(n.file_index()).is_some_and(|(f, local)| {
        f.per_store[local]
            .children
            .get(slot_index(n))
            .is_some_and(|entry| entry.has_no_type_arguments())
    })
}

/// R2-5: the children of a tier 0 store node in Go `ForEachChild` order,
/// from the link column of its store (`SlotLinks`), without its node data.
/// `None` when the chain of `n` is not known and for any other node (nil,
/// synthetic, legacy, tier 1, unpublished): the caller uses `for_each_child`.
#[inline]
#[must_use]
pub fn frozen_store_children(n: Node) -> Option<StoreChildren> {
    if n.is_nil() {
        return None;
    }
    let file = n.file_index();
    let (f, local) = column_store(file)?;
    let links = f.per_store[local].links;
    let first = links.get(slot_index(n))?.first_child;
    (first != LINK_NONE).then_some(StoreChildren {
        file,
        links,
        next: first,
    })
}

/// R2-5: the iterator of `frozen_store_children`. A chain holds only node
/// slots of its store, so each child is the handle of its slot.
#[derive(Clone, Copy, Debug)]
pub struct StoreChildren {
    file: usize,
    links: &'static [SlotLinks],
    /// The next child, `LINK_END` at the end.
    next: u32,
}

impl Iterator for StoreChildren {
    type Item = Node;

    #[inline]
    fn next(&mut self) -> Option<Node> {
        if self.next == LINK_END {
            return None;
        }
        let index = self.next;
        self.next = self.links[index as usize].next_sibling;
        Some(handle(self.file, index))
    }
}

/// The node of child id `id` of store `file` in a `children` entry.
#[inline]
fn column_child(f: &Frozen, s: &FrozenStore, file: usize, id: u32) -> Node {
    // Slot 0 stands for Go nil, as for an optional field that is nil and a
    // kind without the field: it resolves to `FrozenStore::nil`, which is
    // nil (the header of slot 0 never changes).
    debug_assert_eq!(s.nil, Node::NIL);
    if id == NIL_SLOT {
        return Node::NIL;
    }
    frozen_resolve_slot(f, s, file, id as usize)
}

/// U4 (CH7): what `frozen_find_ancestor` found.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AncestorWalk {
    /// The first node for which the callback was true, or nil when the walk
    /// passed the root.
    Found(Node),
    /// The walk reached this parent, which is not in the store. Walk on
    /// from it.
    Next(Node),
}

/// U4 (CH7): the part of Go `FindAncestor(n, callback)` that is inside the
/// tier 0 store of `n`. `callback(node, kind)` gets `n` and then each
/// parent, with its Go `node.Kind`. The kind and header tables of the store
/// are found once, not once per `kind()` and `parent()` read. `None` when
/// `n` is not a tier 0 store node (nil included).
#[inline]
pub fn frozen_find_ancestor(
    n: Node,
    mut callback: impl FnMut(Node, SyntaxKind) -> bool,
) -> Option<AncestorWalk> {
    if n.is_nil() {
        return None;
    }
    let file = n.file_index();
    let (f, local) = column_store(file)?;
    let (headers, kinds) = (f.headers[local], f.kinds[local]);
    let mut index = slot_index(n);
    loop {
        let node = handle(file, index as u32);
        if callback(node, kinds[index]) {
            return Some(AncestorWalk::Found(node));
        }
        // The stored parent (`NodeHeader::read`): a `LOCAL_STORE` handle is
        // a node of this store; anything else is nil or another store.
        let parent = headers[index].parent;
        if parent.file_index() != LOCAL_STORE {
            return Some(if parent.is_nil() {
                AncestorWalk::Found(Node::NIL)
            } else {
                AncestorWalk::Next(parent)
            });
        }
        index = slot_index(parent);
    }
}

/// U4 (CH7): Go `n.Parent` and `n.Parent.Kind` of a tier 0 store node whose
/// parent is a node of the same store, with one store lookup. `None` for
/// any other node or parent (nil, another store): the caller reads them one
/// by one.
#[inline]
#[must_use]
pub fn frozen_store_parent_kind(n: Node) -> Option<(Node, SyntaxKind)> {
    if n.is_nil() {
        return None;
    }
    let file = n.file_index();
    let (f, local) = column_store(file)?;
    let parent = f.headers[local][slot_index(n)].parent;
    if parent.file_index() != LOCAL_STORE {
        return None;
    }
    let index = slot_index(parent);
    Some((handle(file, index as u32), f.kinds[local][index]))
}

/// U4 (CH7): true when `n` is a tier 0 store node and no node of its store
/// has `POSSIBLY_CONTAINS_DEPRECATED_TAG` (`StoreFacts::has_deprecated_tag`)
/// while every parent in the store is local (`parents_local`). Then no
/// ancestor of `n` has the bit, so Go `GetCombinedNodeFlags(n)` lacks it
/// and `IsDeprecatedDeclaration(n)` is false. False for any other node.
#[inline]
#[must_use]
pub fn frozen_store_lacks_deprecated_tag(n: Node) -> bool {
    if n.is_nil() {
        return false;
    }
    column_store(n.file_index()).is_some_and(|(f, local)| {
        let facts = f.per_store[local].facts;
        facts.parents_local && !facts.has_deprecated_tag
    })
}

/// U1 (c): how `Node::new(file, id)` maps the child ids of one tier 0 store,
/// read once for a loop over many ids (`NodeSliceIter`).
#[derive(Clone, Copy, Debug)]
pub enum FrozenIds {
    /// A store with alias slots: its resolved table (`FrozenStore::resolved`).
    Table(&'static [Node]),
    /// An alias-free store: id 0 is `nil` (what slot 0 resolves to), and
    /// any other id is the handle `base | (id + 1)`, `base` = `file << 32`.
    Direct { base: u64, nil: Node },
}

impl FrozenIds {
    /// `Node::new(file, id)` for the store this value was read for.
    #[inline]
    #[must_use]
    pub fn node(self, id: ts_ast::NodeId) -> Node {
        match self {
            FrozenIds::Table(resolved) => resolved[id.index()],
            FrozenIds::Direct { base, nil } => {
                if id.index() == NIL_SLOT as usize {
                    nil
                } else {
                    Node(base | (id.index() as u64 + 1))
                }
            }
        }
    }
}

/// U1 (c): the `FrozenIds` of tier 0 store `file`. `None` for any other
/// file (tier 1, unpublished, synthetic or legacy).
#[inline]
#[must_use]
pub fn frozen_store_ids(file: usize) -> Option<FrozenIds> {
    let s = FROZEN.get()?.per_store.get(file)?;
    Some(if s.facts.alias_free {
        FrozenIds::Direct {
            base: (file as u64) << 32,
            nil: s.nil,
        }
    } else {
        FrozenIds::Table(s.resolved)
    })
}

/// U1 (e): capacity hints for binding published store file `file`
/// (`NodeBindBuilder` entries, flow nodes), tier 0 or tier 1. `None` for an
/// unpublished store and a file without a store.
#[must_use]
pub fn frozen_store_bind_estimate(file: usize) -> Option<(usize, usize)> {
    let tier0 = FROZEN.get()?;
    let store = match tier0.stores.get(file) {
        Some(store) => store,
        None => later_store(tier0, file)?,
    };
    let e = store.bind_estimate;
    Some((e.entries as usize, e.flow_nodes as usize))
}

// ──────────────────────────────────────────────────────────────────────
// Go field writes during the parse
// ──────────────────────────────────────────────────────────────────────

/// The cell of the unpublished store of this thread (built or detached)
/// that holds `n`, with one thread-local access. `None` when `n` is not a
/// node of such a store (for example nil, a synthetic or a published node).
#[inline]
fn thread_build_cell(n: Node) -> Option<StoreCell> {
    if n.is_nil() {
        return None;
    }
    let file = n.file_index();
    // A tier 0 node or a synthetic node leaves here, inline: one load and
    // two compares, as the one-program `FROZEN` check. The active store is
    // never in tier 0 (its id is at least the published count).
    if let Some(tier0) = FROZEN.get()
        && (file < tier0.headers.len() || is_storeless_id(file) || tier0.legacy)
    {
        return None;
    }
    // PERF: query Q8. The parse writes the active store, which is never
    // published (see `ACTIVE`).
    match active_store(file) {
        Some(store) => Some(store),
        None => inactive_thread_store(file),
    }
}

/// Runs `f` on the store and the slot index of `n` when `n` is a node slot
/// of an unpublished store of this thread (built or detached), with one
/// thread-local access. False when `n` is not such a node (for example a
/// synthetic or a published node). Panics on a finished store, like
/// `with_slot_mut`.
fn try_with_build_slot(n: Node, f: impl FnOnce(&mut FileStore, usize)) -> bool {
    let Some(store) = thread_build_cell(n) else {
        return false;
    };
    let mut s = store.borrow_mut();
    assert!(!s.frozen, "cannot mutate a node of a finished file");
    let index = slot_index(n);
    assert!(
        s.nodes[index].is_some(),
        "store handle does not name a node slot"
    );
    f(&mut *s, index);
    true
}

/// `try_with_build_slot` on the header of `n`.
fn try_with_build_header(n: Node, f: impl FnOnce(&mut NodeHeader)) -> bool {
    try_with_build_slot(n, |s, index| f(&mut s.headers[index]))
}

/// `thread_build_cell` for a file that is not in tier 0 and not the active
/// store: `None` for a tier 1 file (published), else the detached store,
/// then the build stores of this thread.
#[inline(never)]
fn inactive_thread_store(file: usize) -> Option<StoreCell> {
    if FROZEN.get().is_some() && later(file).is_some() {
        return None;
    }
    inactive_build_store(file)
}

/// Go `finishNode` writes `node.Loc = loc` and `node.Flags |= flags` on a
/// node of an unfinished store, in one store access. False (nothing
/// written) when `n` is not a store node of this thread.
pub fn finish_store_node(n: Node, loc: TextRange, flags: NodeFlags) -> bool {
    try_with_build_header(n, |h| {
        h.loc = loc;
        h.flags |= flags;
    })
}

/// Go `node.Parent = parent` on a node of an unfinished store, in one store
/// access. False (nothing written) when `n` is not a store node of this
/// thread.
pub fn try_set_store_node_parent(n: Node, parent: Node) -> bool {
    let parent = NodeHeader::stored_parent(n.file_index(), parent);
    try_with_build_header(n, |h| h.parent = parent)
}

/// R2-5: Go `child.Parent = parent` for each child of `parent` in Go
/// `ForEachChild` order (parser.go `overrideParentInImmediateChildren`),
/// which also makes the chain of `parent` in the link column (`SlotLinks`).
/// `new` starts the chain; `set_parent` sets the parent of one child and
/// links it, in the same store access.
pub struct StoreChildLinks {
    parent: Node,
    /// The last child linked so far, `LINK_END` before the first.
    last: u32,
    /// True while the chain of `parent` is made. False when `parent` is not
    /// a node of an unfinished store of this thread, or a child could not be
    /// linked (the chain of `parent` is then unknown).
    linking: bool,
}

impl StoreChildLinks {
    /// Starts the chain of `parent`: frees its old chain (the parser can set
    /// the parents of the same children again) and marks it as a node with
    /// no child yet.
    #[must_use]
    pub fn new(parent: Node) -> Self {
        let linking = thread_build_cell(parent).is_some_and(|store| {
            let mut s = store.borrow_mut();
            let index = slot_index(parent);
            // Nothing to link in a finished file; a child write panics there.
            if s.frozen || s.nodes[index].is_none() {
                return false;
            }
            s.unlink_children(index);
            s.build_links[index].first_child = LINK_END;
            true
        });
        Self {
            parent,
            last: LINK_END,
            linking,
        }
    }

    /// Go `child.Parent = parent` for the next child of `parent`, and links
    /// `child` after the children before it. False (nothing written) when
    /// `child` is not a store node of this thread; the caller then sets the
    /// parent itself (`set_node_parent`).
    pub fn set_parent(&mut self, child: Node) -> bool {
        let parent = self.parent;
        let stored = NodeHeader::stored_parent(child.file_index(), parent);
        // A chain holds only node slots of the store of `parent`.
        let link = self.linking && child.file_index() == parent.file_index();
        let last = &mut self.last;
        let mut linked = false;
        let written = try_with_build_slot(child, |s, index| {
            s.headers[index].parent = stored;
            linked = link && s.link_child(slot_index(parent), last, index);
        });
        if self.linking && !linked {
            // PORT: Go has no such case; only the link column cannot hold it
            // (see `SlotLinks`). The binder then uses Go `ForEachChild`.
            self.linking = false;
            try_with_build_slot(self.parent, |s, index| s.unlink_children(index));
        }
        written
    }
}

/// R3-2: parser.go `overrideParentInImmediateChildren` for `parent` in one
/// borrow of its store: Go `child.Parent = parent` for each child in Go
/// `ForEachChild` order (`for_each_store_child_id`), and the R2-5 chain of
/// `parent`, with the same writes as `StoreChildLinks`. False when `parent`
/// is not a node of an unfinished store of this thread, or when a child is
/// not a node slot of that store (an alias slot, or a nil list entry). The
/// caller then runs the `StoreChildLinks` walk, which gives the same result
/// from any state this left: it frees the chain of `parent` first, and sets
/// the same parents again.
// PERF: R3-2. The `StoreChildLinks` walk found the store once per child
// (`try_with_build_slot`: the `FROZEN` check, the thread-local lookup and a
// `RefCell` borrow) and read the data and each child through the node
// reads. This reads the data from the slot and writes the children by slot
// index.
pub fn set_parent_in_store_children(parent: Node) -> bool {
    let Some(store) = thread_build_cell(parent) else {
        return false;
    };
    let mut guard = store.borrow_mut();
    let s = &mut *guard;
    let index = slot_index(parent);
    // A finished file: the `StoreChildLinks` walk panics on the first write.
    if s.frozen {
        return false;
    }
    let Some(node) = s.nodes[index] else {
        return false;
    };
    let kind = s.headers[index].kind;
    // `NodeHeader::stored_parent` of a child in the store of `parent`.
    let stored = handle(LOCAL_STORE, index as u32);
    // `StoreChildLinks::new`.
    s.unlink_children(index);
    s.build_links[index].first_child = LINK_END;
    let mut last = LINK_END;
    let mut linking = true;
    let stopped = super::node::for_each_store_child_id(kind, node, |child| {
        let child = child as usize;
        if s.nodes[child].is_none() {
            return true;
        }
        // `StoreChildLinks::set_parent`.
        s.headers[child].parent = stored;
        if linking && !s.link_child(index, &mut last, child) {
            linking = false;
            s.unlink_children(index);
        }
        false
    });
    !stopped
}

/// R3-2, debug builds: the slot index, stored parent and R2-5 links of
/// `parent` and of each child that the generic walk (`Node::iter_children`)
/// visits. Every child must be a node of the store of `parent`, an
/// unfinished store of this thread (`set_parent_in_store_children` made
/// its parents).
#[cfg(debug_assertions)]
pub fn debug_store_child_link_state(parent: Node) -> Vec<(u32, Node, u32, u32)> {
    // The walk reads the store, so it runs before the borrow below.
    let children = parent.iter_children();
    let store = thread_build_cell(parent).expect("R3-2: parent is not a build store node");
    let s = store.borrow();
    std::iter::once(parent)
        .chain(children)
        .map(|n| {
            assert_eq!(
                n.file_index(),
                parent.file_index(),
                "R3-2: a child in another store"
            );
            let index = slot_index(n);
            let links = s.build_links[index];
            (
                index as u32,
                s.headers[index].parent,
                links.first_child,
                links.next_sibling,
            )
        })
        .collect()
}

/// Go `node.Parent = parent` on a node of an unfrozen file.
pub fn set_store_node_parent(n: Node, parent: Node) {
    let parent = NodeHeader::stored_parent(n.file_index(), parent);
    with_slot_mut(n, |h| h.parent = parent);
}

/// Go `node.Loc = loc` on a node of an unfrozen file.
pub fn set_store_node_loc(n: Node, loc: TextRange) {
    with_slot_mut(n, |h| h.loc = loc);
}

/// Go `node.Flags = flags` on a node of an unfrozen file.
pub fn set_store_node_flags(n: Node, flags: NodeFlags) {
    with_slot_mut(n, |h| h.flags = flags);
}

/// Go write to a data field of a node of an unfrozen file (reparser.go,
/// `internIdentifier`). The new data replaces the old; the old node leaks.
/// The U1 and U4 build entries and the keyword bit of the slot follow the
/// new data, and its R2-5 chain becomes unknown.
pub fn replace_store_node_data(n: Node, data: NodeData) {
    with_store_mut(n.file_index(), |s| {
        assert!(!s.frozen, "cannot mutate a node of a finished file");
        let index = slot_index(n);
        let Some(old) = s.nodes[index] else {
            panic!("store handle does not name a node slot");
        };
        debug_assert!(
            data.matches_syntax_kind(old.kind),
            "{:?} does not fit its NodeData",
            old.kind
        );
        let node = leak_ast_node(old.kind, data);
        s.nodes[index] = Some(node);
        // The same code as `alloc_store_node`, on the header kind (the kind
        // `debug_check_text_names` and `modifier_bits_column` read).
        let kind = s.headers[index].kind;
        // PORT: U1 (d). Data cloned from a store identifier has an empty text
        // (`alloc_store_name_node`, `alloc_store_shared_name_node`), so an
        // empty text keeps the slot name. A new text replaces it. Go writes
        // no empty identifier text here. S1: the new data gets a new node;
        // a shared name node does not change.
        let keeps_name = matches!(kind, SyntaxKind::Identifier | SyntaxKind::PrivateIdentifier)
            && identifier_text(node).is_empty();
        if !keeps_name {
            let (name, text_is_keyword) = s.slot_text_name(kind, node, None);
            s.headers[index].text_is_keyword = text_is_keyword;
            s.build_names[index] = name;
        }
        let modifier_bits = s.slot_modifier_bits(super::node::store_node_modifier_bits(kind, node));
        s.build_modifier_bits[index] = modifier_bits;
        // U4: a reparser write can change a child that the column holds.
        // C2: the same for the `typed` field.
        s.build_children[index] = super::node::store_node_children(kind, node);
        // R2-5: the children of the node can change, so its chain is freed
        // and unknown until the parser sets their parents again
        // (`StoreChildLinks`; reparser.go `finishMutatedNode`).
        s.unlink_children(index);
    });
}

// ──────────────────────────────────────────────────────────────────────
// Lib parse snapshot (R3-1, frontend/parser/lib_parse_snapshot.rs)
// ──────────────────────────────────────────────────────────────────────

/// R3-1: one node slot of a lib parse snapshot: what the parse left in the
/// slot when it froze the file, besides what the freeze and the U1 and U4
/// build entries make from it. A snapshot store has no alias slot, and slot
/// 0 (nil) is not in the snapshot.
pub(crate) struct LibParseSlot {
    pub(crate) kind: SyntaxKind,
    pub(crate) flags: NodeFlags,
    pub(crate) loc: TextRange,
    /// The slot of the Go parent, 0 for nil.
    pub(crate) parent: u32,
    /// The R2-5 links (`SlotLinks`): a slot, `Self::LINK_END` or
    /// `Self::LINK_NONE`.
    pub(crate) first_child: u32,
    pub(crate) next_sibling: u32,
    /// The node data. `None`: the slot points at the shared name node of
    /// `kind` (S1, `alloc_store_shared_name_node`).
    pub(crate) data: Option<NodeData>,
    /// The name column entry and the keyword bit (`slot_text_name`):
    /// `Name::default()` and false for a kind other than Identifier and
    /// PrivateIdentifier.
    pub(crate) name: Name,
    pub(crate) text_is_keyword: bool,
}

impl LibParseSlot {
    pub(crate) const LINK_END: u32 = LINK_END;
    pub(crate) const LINK_NONE: u32 = LINK_NONE;
}

/// R3-1: fills store `file`, which `new_file_store` or
/// `new_detached_file_store` just made on this thread, with `count` slots
/// after slot 0 from `next`, in slot order, as the parse made them: the
/// header, data, name and link entries of each slot, and the U1 (b) and U4
/// build entries made from the data as `alloc_store_slot_node` makes them.
/// The caller freezes the store, which makes the other tables as for a live
/// parse. False when `next` fails; the store then holds part of the slots
/// (`reset_file_store` empties it).
// PERF: R3-1. One store borrow for all slots. The vectors are made at their
// final size, which `freeze` keeps.
pub(crate) fn load_lib_parse_slots(
    file: usize,
    count: usize,
    mut next: impl FnMut() -> Option<LibParseSlot>,
) -> bool {
    with_store_mut(file, |s| {
        assert!(
            !s.frozen && s.headers.len() == 1,
            "a lib parse snapshot loads into a new store"
        );
        s.headers.reserve_exact(count);
        s.nodes.reserve_exact(count);
        s.build_names.reserve_exact(count);
        s.build_modifier_bits.reserve_exact(count);
        s.build_children.reserve_exact(count);
        s.build_links.reserve_exact(count);
        for _ in 0..count {
            let Some(slot) = next() else {
                return false;
            };
            s.push_lib_parse_slot(slot);
        }
        s.debug_assert_build_columns();
        true
    })
}

impl FileStore {
    /// `load_lib_parse_slots` for one slot.
    fn push_lib_parse_slot(&mut self, slot: LibParseSlot) {
        let LibParseSlot {
            kind,
            flags,
            loc,
            parent,
            first_child,
            next_sibling,
            data,
            name,
            text_is_keyword,
        } = slot;
        let node = match data {
            Some(data) => leak_ast_node(kind, data),
            None => shared_name_node(kind),
        };
        self.headers.push(NodeHeader {
            // `NodeHeader::stored_parent` of a parent in this store.
            parent: if parent == NIL_SLOT {
                Node::NIL
            } else {
                handle(LOCAL_STORE, parent)
            },
            loc,
            flags,
            kind,
            source_file_is_root: false,
            text_is_keyword,
        });
        self.nodes.push(Some(node));
        self.build_names.push(name);
        let modifier_bits =
            self.slot_modifier_bits(super::node::store_node_modifier_bits(kind, node));
        self.build_modifier_bits.push(modifier_bits);
        self.build_children
            .push(super::node::store_node_children(kind, node));
        self.build_links.push(SlotLinks {
            first_child,
            next_sibling,
        });
    }
}

/// R3-1: empties store `file`, an unfinished store of this thread, to what
/// `new_file_store` made, after a snapshot load failed part way. The file
/// is then parsed into it, so its id does not change.
pub(crate) fn reset_file_store(file: usize) {
    with_store_mut(file, |s| {
        assert!(!s.frozen, "cannot reset a finished store");
        *s = FileStore::new(s.file_name, s.text);
    });
}

/// R3-1, tests: one slot of a finished store as a snapshot keeps it
/// (`LibParseSlot`), with the data by reference.
#[cfg(test)]
pub(crate) struct LibParseSlotView {
    pub(crate) kind: SyntaxKind,
    pub(crate) flags: NodeFlags,
    pub(crate) loc: TextRange,
    pub(crate) parent: u32,
    pub(crate) first_child: u32,
    pub(crate) next_sibling: u32,
    pub(crate) node: &'static ts_ast::Node,
    /// The slot points at the shared name node of its kind (S1).
    pub(crate) shared_name: bool,
    pub(crate) name: Name,
    pub(crate) text_is_keyword: bool,
}

/// R3-1, tests: the slots after slot 0 of store `file`, a store of this
/// thread whose parse is finished and that is not published. An error when
/// a snapshot cannot keep the store: an alias slot, a parent in another
/// store, or a ts_ast node with other base fields than `ast_node` gives.
#[cfg(test)]
pub(crate) fn lib_parse_slot_views(file: usize) -> Result<Vec<LibParseSlotView>, String> {
    with_store(file, |s| {
        if !s.frozen || s.names.len() != s.headers.len() || s.links.len() != s.headers.len() {
            return Err("the store is not frozen".into());
        }
        if !s.aliases.is_empty() {
            return Err("the store has alias slots".into());
        }
        let base = ast_node(
            SyntaxKind::Unknown,
            NodeData::Token(Box::new(ts_ast::TokenData)),
        );
        let mut views = Vec::with_capacity(s.headers.len());
        for index in 1..s.headers.len() {
            let header = &s.headers[index];
            let node = s.nodes[index].ok_or_else(|| format!("slot {index} is not a node slot"))?;
            if node.kind != header.kind
                || node.flags != base.flags
                || node.range != base.range
                || node.parent.is_some()
            {
                return Err(format!(
                    "slot {index}: the ts_ast node has other base fields"
                ));
            }
            let parent = match header.parent {
                p if p.is_nil() => NIL_SLOT,
                p if p.file_index() == LOCAL_STORE => slot_index(p) as u32,
                _ => return Err(format!("slot {index}: a parent in another store")),
            };
            let is_name = matches!(
                header.kind,
                SyntaxKind::Identifier | SyntaxKind::PrivateIdentifier
            );
            let shared_name = is_name && std::ptr::eq(node, shared_name_node(header.kind));
            let links = s.links[index];
            views.push(LibParseSlotView {
                kind: header.kind,
                flags: header.flags,
                loc: header.loc,
                parent,
                first_child: links.first_child,
                next_sibling: links.next_sibling,
                node,
                shared_name,
                name: s.names[index].clone(),
                text_is_keyword: header.text_is_keyword,
            });
        }
        Ok(views)
    })
}

/// R3-1, tests: one line for each part of store `file` (a store of this
/// thread whose parse is finished) that the snapshot load and the freeze
/// make, in a form that does not depend on the store id, so the store of a
/// live parse and of a snapshot load can be compared. The node data is not
/// in it (the snapshot test compares it field by field).
#[cfg(test)]
pub(crate) fn lib_parse_store_dump(file: usize) -> Vec<String> {
    let local = |n: Node| {
        if n.is_nil() {
            "nil".to_string()
        } else if n.file_index() == file {
            format!("#{}", slot_index(n))
        } else {
            format!("{n:?}")
        }
    };
    with_store(file, |s| {
        let mut jsdoc: Vec<String> = s
            .jsdoc_cache
            .iter()
            .map(|(&n, jsdocs)| {
                let list: Vec<String> = jsdocs.iter().map(|&j| local(j)).collect();
                format!("{} {list:?}", local(n))
            })
            .collect();
        jsdoc.sort();
        let diagnostics: Vec<String> = s
            .diagnostics
            .iter()
            .map(|d| {
                format!(
                    "{} {} {} {} {} {:?}",
                    local(d.file),
                    d.pos,
                    d.end,
                    d.code,
                    d.message.key(),
                    d.message_args
                )
            })
            .collect();
        let mut lines = vec![
            format!("file {} text {}", s.file_name, s.text.len()),
            format!(
                "frozen {} root_slot {} root {} aliases {} resolved {}",
                s.frozen,
                s.root_slot,
                local(s.root),
                s.aliases.len(),
                s.resolved.len()
            ),
            format!("parser_flags {:?}", s.parser_flags),
            format!("jsdoc {jsdoc:?}"),
            format!(
                "lazy {:?} lazy_cache {}",
                s.lazy_js_doc,
                s.lazy_jsdoc_cache.len()
            ),
            format!(
                "variant {:?} diagnostics {diagnostics:?} non_ascii {}",
                s.language_variant, s.contains_non_ascii
            ),
            format!(
                "facts {:?} bind {:?} overflow {}",
                s.facts, s.bind_estimate, s.modifier_bits_overflow
            ),
            format!(
                "build {} {} {} {} {} names {}",
                s.build_names.len(),
                s.build_modifier_bits.len(),
                s.build_children.len(),
                s.build_links.len(),
                s.identifier_names.len(),
                s.ecma_line_starts.get().is_some()
            ),
            format!(
                "columns {} {} {} {} {} {} {}",
                s.headers.len(),
                s.nodes.len(),
                s.kinds.len(),
                s.names.len(),
                s.modifier_bits.len(),
                s.children.len(),
                s.links.len()
            ),
        ];
        for index in 0..s.headers.len() {
            let shared = s.nodes[index].is_some_and(|node| {
                matches!(
                    node.kind,
                    SyntaxKind::Identifier | SyntaxKind::PrivateIdentifier
                ) && std::ptr::eq(node, shared_name_node(node.kind))
            });
            lines.push(format!(
                "{index}: {:?} node {} shared {shared} kind {:?} name {:?} bits {:?} children {:?} links {:?}",
                s.headers[index],
                s.nodes[index].is_some(),
                s.kinds.get(index),
                s.names.get(index).map(Name::as_str),
                s.modifier_bits.get(index),
                s.children.get(index),
                s.links.get(index),
            ));
        }
        lines
    })
}

// ──────────────────────────────────────────────────────────────────────
// Allocation (used by factory.rs through `NodeFactory::for_file`)
// ──────────────────────────────────────────────────────────────────────

thread_local! {
    /// The size of the first chunk of this thread's AST arena
    /// (`set_ast_arena_start`).
    static AST_ARENA_START: Cell<usize> = const { Cell::new(1 << 20) };
    /// Set when this thread made its AST arena.
    static AST_ARENA_MADE: Cell<bool> = const { Cell::new(false) };
    /// AST nodes and lists live for the whole process. One leaked bump
    /// arena per thread holds them, so each node costs a pointer bump, not
    /// a malloc. The arena never drops, like the `Box::leak` it replaces.
    static AST_ARENA: &'static bumpalo::Bump = {
        AST_ARENA_MADE.set(true);
        Box::leak(Box::new(bumpalo::Bump::with_capacity(AST_ARENA_START.get())))
    };
}

/// Moves `value` into this thread's leaked AST arena.
// PERF: U1 (b). Only the arena reference comes out of the out-of-line
// `LocalKey::with`, so `value` is not copied through its closure.
pub(crate) fn leak_in_ast_arena<T>(value: T) -> &'static T {
    let arena: &'static bumpalo::Bump = AST_ARENA.with(|a| *a);
    arena.alloc(value)
}

/// Sets the size of the first chunk of this thread's AST arena (1 MiB by
/// default). Later chunks double in size. Call it before the thread makes
/// its first node. A released program leaks the arenas of its checker
/// workers, and the part of a chunk that no node uses leaks with them, so
/// the workers of a later program version size the chunk from what the
/// workers of a released one used (`program.rs` `worker_arena_start`).
pub(crate) fn set_ast_arena_start(bytes: usize) {
    AST_ARENA_START.set(bytes);
}

/// The bytes that the nodes of this thread's AST arena use, or 0 when the
/// thread made no arena (asking does not make one).
pub(crate) fn ast_arena_used() -> usize {
    if !AST_ARENA_MADE.get() {
        return 0;
    }
    AST_ARENA.with(|arena| arena.allocated_bytes() - arena.chunk_capacity())
}

/// A ts_ast node with kind `kind` and data `data`. Only kind and data are
/// read for store and synthetic nodes; the header lives in the slot.
fn ast_node(kind: SyntaxKind, data: NodeData) -> ts_ast::Node {
    ts_ast::Node {
        kind,
        flags: ts_ast::NodeFlags(0),
        range: ts_range(TextRange::undefined()),
        parent: None,
        data,
    }
}

/// `ast_node(kind, data)`, leaked in this thread's AST arena.
fn leak_ast_node(kind: SyntaxKind, data: NodeData) -> &'static ts_ast::Node {
    leak_in_ast_arena(ast_node(kind, data))
}

/// S1: the one ts_ast node that every store Identifier (or
/// PrivateIdentifier, by `kind`) made by `alloc_store_shared_name_node`
/// points at. Its data is the Go factory payload with the default fields:
/// no flow node (the binder keeps flow nodes in its tables) and an empty
/// text (the name column holds the text).
fn shared_name_node(kind: SyntaxKind) -> &'static ts_ast::Node {
    static IDENTIFIER: OnceLock<&'static ts_ast::Node> = OnceLock::new();
    static PRIVATE_IDENTIFIER: OnceLock<&'static ts_ast::Node> = OnceLock::new();
    let leak = |data| -> &'static ts_ast::Node { Box::leak(Box::new(ast_node(kind, data))) };
    match kind {
        SyntaxKind::Identifier => *IDENTIFIER.get_or_init(|| {
            leak(NodeData::Identifier(Box::new(ts_ast::IdentifierData {
                flow_node: None,
                text: String::new(),
            })))
        }),
        SyntaxKind::PrivateIdentifier => *PRIVATE_IDENTIFIER.get_or_init(|| {
            leak(NodeData::PrivateIdentifier(Box::new(
                ts_ast::PrivateIdentifierData {
                    text: String::new(),
                },
            )))
        }),
        _ => panic!("{kind:?} is not a name kind"),
    }
}

/// S1, debug builds: panics unless `data` (the payload the factory builds
/// for a store name node of kind `kind`) equals the data of the shared node
/// of `kind`. The struct patterns name every field, so a new ts_ast field
/// does not compile here until it is checked.
#[cfg(debug_assertions)]
pub fn debug_assert_shared_name_data(kind: SyntaxKind, data: &NodeData) {
    let same = match (data, &shared_name_node(kind).data) {
        (NodeData::Identifier(a), NodeData::Identifier(b)) => {
            let ts_ast::IdentifierData { flow_node, text } = &**a;
            *flow_node == b.flow_node && *text == b.text
        }
        (NodeData::PrivateIdentifier(a), NodeData::PrivateIdentifier(b)) => {
            let ts_ast::PrivateIdentifierData { text } = &**a;
            *text == b.text
        }
        _ => false,
    };
    assert!(
        same,
        "S1: the factory payload of a store {kind:?} differs from the shared node"
    );
}

/// Go `newNode(kind, data, hooks)` in store `file`: `Loc =
/// UndefinedTextRange()`, nil parent, no flags.
pub fn alloc_store_node(file: usize, kind: SyntaxKind, data: NodeData) -> Node {
    alloc_store_slot(file, kind, data, None)
}

/// `alloc_store_node` for an Identifier or PrivateIdentifier with Go text
/// `text`, whose `data` has an empty text: the name column of the slot
/// holds the text (`store_identifier_name`).
// PERF: U1 (d). The node data needs no `String` for the text.
pub fn alloc_store_name_node(file: usize, kind: SyntaxKind, data: NodeData, text: &str) -> Node {
    debug_assert!(
        matches!(kind, SyntaxKind::Identifier | SyntaxKind::PrivateIdentifier),
        "{kind:?} is not a name kind"
    );
    alloc_store_slot(file, kind, data, Some(text))
}

/// S1: `alloc_store_name_node` for the Go factory payload of a name node
/// (no flow node, empty data text), without a new data box or ts_ast node:
/// the slot points at the process-wide node of `kind` (`shared_name_node`).
/// The name column holds `text`. The factory checks its payload against the
/// shared one in debug builds (`debug_assert_shared_name_data`).
// PERF: S1. Saves one malloc and about 88 bytes per identifier (a 32-byte
// data box and a 40-byte arena node). Sharing one node is safe because a
// ts_ast node is never changed in place: its data has no interior
// mutability, the crate forbids unsafe code, and a data write gives the slot
// a new node (`replace_store_node_data`). No code uses the address of a
// ts_ast node as an identity (the `data_accessor!` `_in` debug check only
// compares the data of one node with itself).
pub fn alloc_store_shared_name_node(file: usize, kind: SyntaxKind, text: &str) -> Node {
    alloc_store_slot_node(file, kind, shared_name_node(kind), Some(text))
}

/// `alloc_store_node` with the name text `text` (`slot_text_name`).
#[inline]
fn alloc_store_slot(file: usize, kind: SyntaxKind, data: NodeData, text: Option<&str>) -> Node {
    debug_assert!(
        data.matches_syntax_kind(kind),
        "{kind:?} does not fit its NodeData"
    );
    alloc_store_slot_node(file, kind, leak_ast_node(kind, data), text)
}

/// `alloc_store_slot` for a ts_ast node that is already made.
#[inline]
fn alloc_store_slot_node(
    file: usize,
    kind: SyntaxKind,
    node: &'static ts_ast::Node,
    text: Option<&str>,
) -> Node {
    debug_assert!(
        text.is_none() || identifier_text(node).is_empty(),
        "a name node keeps its text in the name column"
    );
    // PERF: U1 (b), U4. Read while the new data is hot, not at freeze.
    let modifier_bits = super::node::store_node_modifier_bits(kind, node);
    let children = super::node::store_node_children(kind, node);
    with_store_mut(file, |s| {
        assert!(!s.frozen, "cannot create a node in a finished file");
        let index = s.headers.len() as u32;
        let (name, text_is_keyword) = s.slot_text_name(kind, node, text);
        s.headers.push(NodeHeader {
            parent: Node::NIL,
            loc: TextRange::undefined(),
            flags: NodeFlags::NONE,
            kind,
            source_file_is_root: false,
            text_is_keyword,
        });
        s.nodes.push(Some(node));
        s.build_names.push(name);
        let modifier_bits = s.slot_modifier_bits(modifier_bits);
        s.build_modifier_bits.push(modifier_bits);
        s.build_children.push(children);
        s.build_links.push(SlotLinks::NONE);
        s.debug_assert_build_columns();
        handle(file, index)
    })
}

/// The store-local id that stands for `n` inside `NodeData` of store `file`.
/// Nil maps to the nil slot. A node of another file gets (or reuses) an
/// alias slot.
// PERF: U4 (4). The factory calls this for every child and list entry, and
// nearly all are nil or of the same file. Those two tests are inline; the
// alias path is out of line, so the function body stays small.
#[inline]
#[must_use]
pub fn store_child_id(file: usize, n: Node) -> ts_ast::NodeId {
    if n.is_nil() {
        return ts_ast::NodeId::new(NIL_SLOT);
    }
    if n.file_index() == file {
        return ts_ast::NodeId::new(slot_index(n) as u32);
    }
    store_alias_id(file, n)
}

/// The alias slot of foreign node `n` in store `file` (`store_child_id`).
#[inline(never)]
fn store_alias_id(file: usize, n: Node) -> ts_ast::NodeId {
    with_store_mut(file, |s| {
        if let Some(&index) = s.aliases.get(&n) {
            return ts_ast::NodeId::new(index);
        }
        let index = s.headers.len() as u32;
        s.headers.push(NodeHeader::target(n));
        s.nodes.push(None);
        s.build_names.push(Name::default());
        s.build_modifier_bits.push(0);
        s.build_children.push(SlotChildren::UNKNOWN);
        s.build_links.push(SlotLinks::NONE);
        s.debug_assert_build_columns();
        s.aliases.insert(n, index);
        ts_ast::NodeId::new(index)
    })
}

/// Like `store_child_id`, for ts_ast fields that are `Option<NodeId>`.
#[must_use]
pub fn store_opt_child_id(file: usize, n: Node) -> Option<ts_ast::NodeId> {
    if n.is_nil() {
        None
    } else {
        Some(store_child_id(file, n))
    }
}

/// A Go `core.TextRange` in ts_ast form (`-1` is stored as `u32::MAX`).
fn ts_range(loc: TextRange) -> ts_core::TextRange {
    ts_core::TextRange {
        start: ts_core::TextPos::new(loc.pos() as u32),
        end: ts_core::TextPos::new(loc.end() as u32),
    }
}

/// The ts_ast list for a list of store `file`.
fn ts_list(file: usize, nodes: &[Node], loc: TextRange) -> ts_ast::NodeList {
    ts_ast::NodeList {
        range: ts_range(loc),
        nodes: nodes.iter().map(|&n| store_child_id(file, n)).collect(),
        has_trailing_comma: false,
    }
}

/// U1 (e): a list that the parser made in a store and that no node data
/// holds yet: what a pending `NodeList` handle names. Its ids live in the
/// AST bump arena. `store_list_value` builds the ts_ast list from it, once
/// for each node data that stores it.
#[derive(Debug)]
pub struct PendingList {
    /// Go `list.Loc` in ts_ast form (`ts_range`).
    pub(crate) range: ts_core::TextRange,
    /// The store ids of the nodes (`store_child_id`).
    pub(crate) nodes: &'static [ts_ast::NodeId],
    /// The ts_ast bit (`NodeList::stored_trailing_comma`).
    pub(crate) has_trailing_comma: bool,
}

impl PendingList {
    /// A pending list of store `file` over `nodes`, at `loc`. Makes the
    /// alias slots of the nodes in order, as `ts_list` does.
    fn new(file: usize, nodes: &[Node], loc: TextRange) -> Self {
        let arena: &'static bumpalo::Bump = AST_ARENA.with(|a| *a);
        Self {
            range: ts_range(loc),
            nodes: arena.alloc_slice_fill_iter(nodes.iter().map(|&n| store_child_id(file, n))),
            has_trailing_comma: false,
        }
    }

    /// The ts_ast list with the same range, ids and bit.
    fn to_ts(&self) -> ts_ast::NodeList {
        ts_ast::NodeList {
            range: self.range,
            nodes: self.nodes.to_vec(),
            has_trailing_comma: self.has_trailing_comma,
        }
    }
}

/// U1 (e): the `PendingList` of a modifier list, with Go
/// `ModifiersToFlags(nodes)`.
#[derive(Debug)]
pub struct PendingModifierList {
    pub(crate) list: PendingList,
    pub(crate) flags: ts_ast::ModifierFlags,
}

impl PendingModifierList {
    /// The ts_ast modifier list with the same list and flags.
    fn to_ts(&self) -> ts_ast::ModifierList {
        ts_ast::ModifierList {
            list: self.list.to_ts(),
            flags: self.flags,
        }
    }
}

/// Go `f.NewNodeList(nodes)` followed by `list.Loc = loc`, in store `file`.
// PERF: U1 (e). A pending handle: the ids go into the AST bump arena, not
// into a `Vec` that `store_list_value` copied again (two mallocs, and the
// first copy leaked).
#[must_use]
pub fn new_store_node_list(file: usize, nodes: &[Node], loc: TextRange) -> NodeList {
    NodeList::pending(file, leak_in_ast_arena(PendingList::new(file, nodes, loc)))
}

/// Go `f.NewModifierList(nodes)` followed by `list.Loc = loc`, in store
/// `file`. `ModifierFlags = ModifiersToFlags(nodes)` as in Go.
// PERF: U1 (e), as `new_store_node_list`.
#[must_use]
pub fn new_store_modifier_list(file: usize, nodes: &[Node], loc: TextRange) -> ModifierList {
    let list = leak_in_ast_arena(PendingModifierList {
        list: PendingList::new(file, nodes, loc),
        flags: ts_ast::ModifierFlags(modifiers_to_flags(nodes).0 as u32),
    });
    ModifierList::pending(file, list)
}

/// A list value to store inside new `NodeData` of store `file`. Go stores
/// the `*NodeList` pointer. A list of the same store is copied as is; any
/// other list is rebuilt over ids of this store with its own `Loc`.
// PORT: ts_ast stores lists by value, so `NodeList` equality on the copy is
// false where Go compares equal pointers (plan risk 2).
#[must_use]
pub fn store_list_value(file: usize, list: NodeList) -> Option<ts_ast::NodeList> {
    if list.is_nil() {
        return None;
    }
    if list.file() == file {
        // U1 (e): the ts_ast list of a pending list is made here, once.
        if let Some(p) = list.pending_list() {
            return Some(p.to_ts());
        }
        if let Some(l) = list.ts_list() {
            return Some(l.clone());
        }
    }
    let nodes = list.nodes().to_vec();
    Some(ts_list(file, &nodes, list.loc()))
}

/// Like `store_list_value` for a list field that ts_ast requires. Go `nil`
/// becomes an empty list at `NIL_LIST_POS`, which `NodeList::is_nil` reads
/// as nil.
#[must_use]
pub fn store_req_list_value(file: usize, list: NodeList) -> ts_ast::NodeList {
    store_list_value(file, list).unwrap_or_else(|| ts_ast::NodeList {
        range: ts_core::TextRange {
            start: ts_core::TextPos::new(NIL_LIST_POS),
            end: ts_core::TextPos::new(NIL_LIST_POS),
        },
        nodes: Vec::new(),
        has_trailing_comma: false,
    })
}

/// A modifier list value to store inside new `NodeData` of store `file`.
#[must_use]
pub fn store_modifiers_value(file: usize, modifiers: ModifierList) -> Option<ts_ast::ModifierList> {
    if modifiers.is_nil() {
        return None;
    }
    if modifiers.file() == file {
        // U1 (e): as in `store_list_value`.
        if let Some(p) = modifiers.pending_list() {
            return Some(p.to_ts());
        }
        if let Some(m) = modifiers.ts_list() {
            return Some(m.clone());
        }
    }
    let nodes = modifiers.nodes().to_vec();
    Some(ts_ast::ModifierList {
        list: ts_list(file, &nodes, modifiers.loc()),
        flags: ts_ast::ModifierFlags(modifiers_to_flags(&nodes).0 as u32),
    })
}

/// True when `l` is the Go `nil` marker of a required list field.
#[inline]
#[must_use]
pub fn is_nil_list_marker(l: &ts_ast::NodeList) -> bool {
    is_nil_list_range(&l.range)
}

/// True when `range` is the range of a Go `nil` marker list
/// (`NIL_LIST_POS`).
#[inline]
#[must_use]
pub fn is_nil_list_range(range: &ts_core::TextRange) -> bool {
    range.start.get() == NIL_LIST_POS && range.end.get() == NIL_LIST_POS
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parser_factory_writes_into_the_file_store() {
        let file = new_file_store("/a.ts", "a.b");
        let f = NodeFactory::for_file(file);
        let a = f.new_identifier("a");
        let b = f.new_identifier("b");
        set_node_loc(a, TextRange::new(0, 1));
        let q = f.new_qualified_name(a, b);
        set_node_parent(a, q);
        set_node_flags(q, NodeFlags::AMBIENT);

        assert_eq!(q.file_index(), file);
        assert_eq!(q.kind(), SyntaxKind::QualifiedName);
        assert_eq!(q.left(), a);
        assert_eq!(a.parent(), q);
        assert_eq!(a.loc(), TextRange::new(0, 1));
        assert_eq!(q.loc(), TextRange::undefined());
        assert_eq!(q.flags(), NodeFlags::AMBIENT);
        assert_eq!(source_file_text(q), "a.b");

        // A synthetic child is an alias slot that resolves to the same node.
        let s = NodeFactory::new().new_identifier("s");
        let q2 = f.new_qualified_name(q, s);
        assert_eq!(q2.right(), s);

        // Go nil in a required list field reads back as nil.
        let decls = f.new_variable_declaration_list(NodeList::NIL, NodeFlags::NONE);
        assert!(decls.declarations().is_nil());
        let list = f.new_node_list_with_loc(&[a], TextRange::new(0, 3));
        assert_eq!(list.loc(), TextRange::new(0, 3));
        assert_eq!(list.nodes().get(0), a);

        freeze_file_store(file);
        assert!(std::panic::catch_unwind(|| set_node_parent(b, q)).is_err());
    }

    #[test]
    fn freeze_makes_the_name_and_modifier_columns() {
        let file = new_file_store("/c.ts", "");
        let f = NodeFactory::for_file(file);
        let keyword = f.new_identifier("await");
        let plain = f.new_identifier("b");
        let private = f.new_private_identifier("#c");
        let export = f.new_modifier(SyntaxKind::ExportKeyword);
        let declare = f.new_modifier(SyntaxKind::DeclareKeyword);
        let modifiers = f.new_modifier_list(&[export, declare]);
        let list = f.new_variable_declaration_list(NodeList::NIL, NodeFlags::NONE);
        let statement = f.new_variable_statement(modifiers, list);
        freeze_file_store(file);

        with_store(file, |s| {
            let names = |n: Node| s.names[slot_index(n)].clone();
            assert_eq!(names(keyword), Name::from("await"));
            assert_eq!(names(plain), Name::from("b"));
            assert_eq!(names(private), Name::from("#c"));
            assert_eq!(names(statement), Name::default());
            let is_keyword = |n: Node| s.headers[slot_index(n)].text_is_keyword;
            assert!(is_keyword(keyword));
            assert!(!is_keyword(plain));
            assert!(!is_keyword(private));
            let bits = |n: Node| u32::from(s.modifier_bits[slot_index(n)]);
            assert_eq!(
                bits(statement),
                (ModifierFlags::EXPORT | ModifierFlags::AMBIENT).0
            );
            assert_eq!(bits(list), 0);
            assert_eq!(bits(export), 0);
        });
    }

    #[test]
    fn replaced_data_updates_the_name_and_modifier_columns() {
        let file = new_file_store("/d.ts", "");
        let f = NodeFactory::for_file(file);
        let id = f.new_identifier("a");
        let export = f.new_modifier(SyntaxKind::ExportKeyword);
        let modifiers = f.new_modifier_list(&[export]);
        let list = f.new_variable_declaration_list(NodeList::NIL, NodeFlags::NONE);
        let statement = f.new_variable_statement(modifiers, list);
        with_store(file, |s| {
            assert_eq!(s.build_names[slot_index(id)], Name::from("a"));
            assert_ne!(s.build_modifier_bits[slot_index(statement)], 0);
        });

        let mut data = store_ast_node(id).data.clone();
        if let NodeData::Identifier(d) = &mut data {
            d.text = "await".to_string();
        }
        replace_store_node_data(id, data);
        let mut data = store_ast_node(statement).data.clone();
        if let NodeData::VariableStatement(d) = &mut data {
            d.modifiers = None;
        }
        replace_store_node_data(statement, data);
        freeze_file_store(file);

        with_store(file, |s| {
            assert_eq!(s.names[slot_index(id)], Name::from("await"));
            assert!(s.headers[slot_index(id)].text_is_keyword);
            assert_eq!(s.modifier_bits[slot_index(statement)], 0);
        });
    }

    #[test]
    fn slots_get_the_children_column() {
        let file = new_file_store("/g.ts", "");
        let f = NodeFactory::for_file(file);
        let id = |n: Node| slot_index(n) as u32;
        let a = f.new_identifier("a");
        let b = f.new_identifier("b");
        let access = f.new_property_access_expression(a, Node::NIL, b, NodeFlags::NONE);
        let statement = f.new_expression_statement(access);
        let question = f.new_token(SyntaxKind::QuestionToken);
        let p = f.new_identifier("p");
        let signature = f.new_property_signature_declaration(
            ModifierList::NIL,
            p,
            question,
            Node::NIL,
            Node::NIL,
        );
        let x = f.new_identifier("x");
        let parameter = f.new_parameter_declaration(
            ModifierList::NIL,
            Node::NIL,
            x,
            Node::NIL,
            Node::NIL,
            Node::NIL,
        );
        let qualified = f.new_qualified_name(a, b);
        // A synthetic child gets an alias slot.
        let s = NodeFactory::new().new_identifier("s");
        let aliased = f.new_property_access_expression(s, Node::NIL, b, NodeFlags::NONE);
        // A reparser write replaces a child that the column holds.
        let c = f.new_identifier("c");
        let mut data = store_ast_node(statement).data.clone();
        if let NodeData::ExpressionStatement(d) = &mut data {
            d.expression = store_child_id(file, c);
        }
        replace_store_node_data(statement, data);
        freeze_file_store(file);

        with_store(file, |st| {
            let entry = |n: Node| st.children[slot_index(n)];
            let expression = SlotChildren::TAG_EXPRESSION;
            // C2: none of these nodes has a type, an initializer or type
            // arguments.
            let untyped = |e: SlotChildren| e.with_typed(Some((SlotChildren::TYPED_TYPE, 0)), true);
            let no_type =
                |e: SlotChildren| e.with_typed(Some((SlotChildren::TYPED_INITIALIZER, 0)), true);
            assert_eq!(
                entry(access),
                untyped(SlotChildren::new(Some(id(b)), Some((expression, id(a)))))
            );
            assert_eq!(
                entry(statement),
                untyped(SlotChildren::new(Some(0), Some((expression, id(c)))))
            );
            assert_eq!(
                entry(signature),
                no_type(SlotChildren::new(
                    Some(id(p)),
                    Some((SlotChildren::TAG_POSTFIX, id(question)))
                ))
            );
            assert_eq!(
                entry(parameter),
                no_type(SlotChildren::new(
                    Some(id(x)),
                    Some((SlotChildren::TAG_QUESTION, 0))
                ))
            );
            assert_eq!(
                entry(a),
                untyped(SlotChildren::new(Some(0), Some((expression, 0))))
            );
            assert_eq!(entry(qualified), untyped(SlotChildren::UNKNOWN));
            // The nil slot and alias slots are unknown; an aliased child has
            // its alias slot id, as in the node data.
            assert_eq!(st.children[NIL_SLOT as usize], SlotChildren::UNKNOWN);
            let alias = st.aliases[&s];
            assert_eq!(st.children[alias as usize], SlotChildren::UNKNOWN);
            assert_eq!(
                entry(aliased),
                untyped(SlotChildren::new(Some(id(b)), Some((expression, alias))))
            );
            assert!(st.children_column_matches());
        });
    }

    #[test]
    fn slots_get_the_typed_column() {
        let file = new_file_store("/i.ts", "");
        let f = NodeFactory::for_file(file);
        let id = |n: Node| slot_index(n) as u32;
        let x = f.new_identifier("x");
        let t = f.new_keyword_type_node(SyntaxKind::NumberKeyword);
        let one = f.new_numeric_literal("1", TokenFlags::NONE);
        let both = f.new_variable_declaration(x, Node::NIL, t, one);
        let only_initializer = f.new_variable_declaration(x, Node::NIL, Node::NIL, one);
        let only_type = f.new_variable_declaration(x, Node::NIL, t, Node::NIL);
        let name = f.new_identifier("T");
        let plain_reference = f.new_type_reference_node(name, NodeList::NIL);
        let generic_reference = f.new_type_reference_node(name, f.new_node_list(&[t]));
        let call = f.new_call_expression(
            x,
            Node::NIL,
            NodeList::NIL,
            f.new_node_list(&[]),
            NodeFlags::NONE,
        );
        freeze_file_store(file);

        with_store(file, |st| {
            let typed = |n: Node| {
                let entry = st.children[slot_index(n)];
                (entry.typed_parts(), entry.has_no_type_arguments())
            };
            // Both set: the column holds the type only.
            assert_eq!(
                typed(both),
                ((SlotChildren::TYPED_TYPE_WITH_INITIALIZER, id(t)), true)
            );
            // One set: the column holds it, and the other reads as nil.
            assert_eq!(
                typed(only_initializer),
                ((SlotChildren::TYPED_INITIALIZER, id(one)), true)
            );
            assert_eq!(typed(only_type), ((SlotChildren::TYPED_TYPE, id(t)), true));
            assert_eq!(
                typed(plain_reference),
                ((SlotChildren::TYPED_TYPE_NAME, id(name)), true)
            );
            assert_eq!(
                typed(generic_reference),
                ((SlotChildren::TYPED_TYPE_NAME, id(name)), false)
            );
            assert_eq!(typed(call), ((SlotChildren::TYPED_TYPE, 0), true));
            assert_eq!(typed(x), ((SlotChildren::TYPED_TYPE, 0), true));
            // Unknown never claims a nil type argument list.
            assert!(!SlotChildren::UNKNOWN.has_no_type_arguments());
            assert!(st.children_column_matches());
        });
    }

    /// R2-5: the chain of `n` in the build links of its store, or `None`
    /// when it is not known.
    fn build_chain(n: Node) -> Option<Vec<Node>> {
        let file = n.file_index();
        with_store(file, |s| {
            let mut next = s.build_links[slot_index(n)].first_child;
            if next == LINK_NONE {
                return None;
            }
            let mut chain = Vec::new();
            while next != LINK_END {
                chain.push(handle(file, next));
                next = s.build_links[next as usize].next_sibling;
            }
            Some(chain)
        })
    }

    /// R2-5: what `override_parent_in_immediate_children` does for `parent`.
    fn link_children(parent: Node) {
        let mut links = StoreChildLinks::new(parent);
        parent.for_each_child(|child| {
            if !links.set_parent(child) {
                set_node_parent(child, parent);
            }
            false
        });
    }

    #[test]
    fn child_links_follow_the_parent_writes() {
        let file = new_file_store("/h.ts", "");
        let f = NodeFactory::for_file(file);
        let a = f.new_identifier("a");
        let b = f.new_identifier("b");
        let q = f.new_qualified_name(a, b);
        link_children(q);
        assert_eq!(build_chain(q), Some(vec![a, b]));
        assert_eq!(a.parent(), q);
        // Setting the parents again makes the same chain.
        link_children(q);
        assert_eq!(build_chain(q), Some(vec![a, b]));
        // A leaf has an empty chain; a node the parser did not finish has
        // none.
        link_children(a);
        assert_eq!(build_chain(a), Some(Vec::new()));
        assert_eq!(build_chain(b), None);
        // A second parent of linked children is unknown; the first keeps
        // its chain, as Go keeps them in its fields.
        let q2 = f.new_qualified_name(a, b);
        link_children(q2);
        assert_eq!(build_chain(q2), None);
        assert_eq!(build_chain(q), Some(vec![a, b]));
        assert_eq!(a.parent(), q2);
        // A data write frees the chain, so the children can be linked again.
        replace_store_node_data(q, store_ast_node(q).data.clone());
        assert_eq!(build_chain(q), None);
        link_children(q2);
        assert_eq!(build_chain(q2), Some(vec![a, b]));
        // A child twice in one node, or a child of another store, makes the
        // chain unknown and frees the children linked before it.
        let twice = f.new_qualified_name(q, q);
        link_children(twice);
        assert_eq!(build_chain(twice), None);
        let synthetic = NodeFactory::new().new_identifier("s");
        let mixed = f.new_qualified_name(q, synthetic);
        link_children(mixed);
        assert_eq!(build_chain(mixed), None);
        assert_eq!(synthetic.parent(), mixed);
        link_children(twice);
        assert_eq!(build_chain(twice), None);
        freeze_file_store(file);
        with_store(file, |s| {
            assert_eq!(s.links.len(), s.headers.len());
            assert_eq!(s.links[slot_index(q2)].first_child, slot_index(a) as u32);
            assert_eq!(s.links[slot_index(a)].next_sibling, slot_index(b) as u32);
            assert_eq!(s.links[slot_index(b)].next_sibling, LINK_END);
        });
    }

    #[test]
    fn parsed_chains_equal_for_each_child() {
        use crate::frontend::parser::{SourceFileParseOptions, parse_source_file};
        let text = "function f(a: number, b = 1) { return a + b; }\n\
            let x: Array<string> = [1, 2].map(y => `${y}`);\n\
            type T = { a?: string } | number;\n\
            class C<U> extends Object { m(): U | undefined { return undefined; } }\n";
        let opts = SourceFileParseOptions {
            file_name: "/links.ts".to_string(),
            ..Default::default()
        };
        let parsed = parse_source_file(&opts, text, ScriptKind::TS);
        let file = parsed.store;
        let links = with_store(file, |s| s.links.clone());
        assert_eq!(links.len(), file_store_slot_count(file));
        let mut known = 0;
        for index in 1..links.len() as u32 {
            let mut next = links[index as usize].first_child;
            if next == LINK_NONE {
                continue;
            }
            known += 1;
            let mut chain = Vec::new();
            while next != LINK_END {
                chain.push(handle(file, next));
                next = links[next as usize].next_sibling;
            }
            let n = handle(file, index);
            assert_eq!(
                chain,
                n.iter_children().collect::<Vec<_>>(),
                "{:?}",
                n.kind()
            );
        }
        assert!(known > 0);
        // The parser links the root too.
        assert_ne!(links[slot_index(parsed.root)].first_child, LINK_NONE);
    }

    #[test]
    fn slot_children_tags_round_trip() {
        let entry = SlotChildren::new(Some(7), Some((SlotChildren::TAG_QUESTION, 9)));
        assert_eq!(entry.name, 7);
        assert_eq!(entry.other_parts(), (SlotChildren::TAG_QUESTION, 9));
        // An id that does not fit next to the tag is unknown.
        let big = SlotChildren::new(Some(1), Some((SlotChildren::TAG_POSTFIX, 1 << 30)));
        assert_eq!(big.other, SlotChildren::UNKNOWN_ID);
        assert_eq!(big.other_parts().0, SlotChildren::TAG_UNKNOWN);
        assert_eq!(SlotChildren::new(None, None), SlotChildren::UNKNOWN);
        // C2: the tag, the id and the type arguments bit round trip, and an
        // id that does not fit is unknown.
        let typed = entry.with_typed(Some((SlotChildren::TYPED_TYPE_NAME, 11)), true);
        assert_eq!(typed.typed_parts(), (SlotChildren::TYPED_TYPE_NAME, 11));
        assert!(typed.has_no_type_arguments());
        let big = entry.with_typed(Some((SlotChildren::TYPED_TYPE, 1 << 28)), false);
        assert_eq!(big.typed_parts().0, SlotChildren::TYPED_UNKNOWN);
        assert_eq!(std::mem::size_of::<SlotChildren>(), 12);
    }

    #[test]
    fn store_identifier_text_lives_in_the_name_column() {
        let file = new_file_store("/e.ts", "");
        let f = NodeFactory::for_file(file);
        let id = f.new_identifier("abc");
        let private = f.new_private_identifier("#p");
        let missing = f.new_identifier("");
        assert!(identifier_text(store_ast_node(id)).is_empty());
        // S1: every store identifier points at one shared ts_ast node.
        assert!(std::ptr::eq(store_ast_node(id), store_ast_node(missing)));
        assert!(std::ptr::eq(
            store_ast_node(id),
            shared_name_node(SyntaxKind::Identifier)
        ));
        assert!(std::ptr::eq(
            store_ast_node(private),
            shared_name_node(SyntaxKind::PrivateIdentifier)
        ));
        assert_eq!(id.text(), "abc");
        assert_eq!(private.text(), "#p");
        assert_eq!(missing.text(), "");
        // Data cloned from a store identifier has no text; the name stays.
        replace_store_node_data(id, store_ast_node(id).data.clone());
        assert_eq!(id.text(), "abc");
        // S1: the write gives the slot its own node; the shared one stays.
        assert!(!std::ptr::eq(store_ast_node(id), store_ast_node(missing)));
        assert_eq!(missing.text(), "");
        // A synthetic identifier keeps its text in the data.
        assert_eq!(NodeFactory::new().new_identifier("syn").text(), "syn");
        freeze_file_store(file);
        assert_eq!(id.text(), "abc");
        assert_eq!(missing.text(), "");
    }

    #[test]
    fn pending_lists_are_built_once_into_node_data() {
        assert_eq!(std::mem::size_of::<NodeList>(), 16);
        assert_eq!(std::mem::size_of::<ModifierList>(), 16);
        let file = new_file_store("/f.ts", "");
        let f = NodeFactory::for_file(file);
        let a = f.new_identifier("a");
        let list = f.new_node_list_with_loc(&[a], TextRange::new(1, 4));
        assert!(list.pending_list().is_some());
        assert_eq!(list, list);
        assert_eq!(list.nodes().get(0), a);
        assert_eq!(list.loc(), TextRange::new(1, 4));
        let decls = f.new_variable_declaration_list(list, NodeFlags::NONE);
        let stored = decls.declarations();
        assert!(stored.ts_list().is_some());
        assert_eq!(stored, decls.declarations());
        assert_ne!(stored, list);
        assert_eq!(stored.nodes().get(0), a);
        assert_eq!(stored.loc(), TextRange::new(1, 4));

        let export = f.new_modifier(SyntaxKind::ExportKeyword);
        let modifiers = f.new_modifier_list(&[export]);
        assert!(modifiers.pending_list().is_some());
        assert_eq!(modifiers.modifier_flags(), ModifierFlags::EXPORT);
        let statement = f.new_variable_statement(modifiers, decls);
        assert_eq!(
            statement.modifiers().modifier_flags(),
            ModifierFlags::EXPORT
        );
        assert_ne!(statement.modifiers(), modifiers);

        let empty = f.new_node_list_with_loc(&[], TextRange::new(2, 2));
        let missing = empty.with_missing_marker();
        assert!(!crate::frontend::parser::parser_p1::is_missing_node_list(
            empty
        ));
        assert!(crate::frontend::parser::parser_p1::is_missing_node_list(
            missing
        ));
        let holder = f.new_variable_declaration_list(missing, NodeFlags::NONE);
        assert!(crate::frontend::parser::parser_p1::is_missing_node_list(
            holder.declarations()
        ));
    }

    #[test]
    fn adopted_detached_parse_equals_a_serial_parse() {
        use crate::frontend::parser::{
            ParsedSourceFile, SourceFileParseOptions, adopt_detached_parse, parse_source_file,
            parse_source_file_detached,
        };
        let text =
            "/** doc */\nexport function f(a: number) { return a + 1; }\nlet x = <T>(y: T) => y;\n";
        let opts = SourceFileParseOptions {
            file_name: "/a.ts".to_string(),
            ..Default::default()
        };
        let serial = parse_source_file(&opts, text, ScriptKind::TS);
        let worker_opts = opts.clone();
        let detached = std::thread::spawn(move || {
            parse_source_file_detached(7, &worker_opts, text, ScriptKind::TS)
        })
        .join()
        .unwrap();
        assert_eq!(detached.store.id(), DETACHED_STORE_BASE + 7);
        let adopted: ParsedSourceFile = adopt_detached_parse(detached, &opts);

        assert_eq!(adopted.store, serial.store + 1);
        let slots = file_store_slot_count(serial.store);
        assert_eq!(file_store_slot_count(adopted.store), slots);
        let to_serial = |n: Node| {
            if n.is_some() && n.file_index() == adopted.store {
                handle(serial.store, slot_index(n) as u32)
            } else {
                n
            }
        };
        for index in 1..slots as u32 {
            let (a, b) = (handle(serial.store, index), handle(adopted.store, index));
            let (ha, hb) = (store_header(a), store_header(b));
            assert_eq!(ha.kind, hb.kind);
            assert_eq!(ha.flags, hb.flags);
            assert_eq!(ha.loc, hb.loc);
            assert_eq!(ha.parent, to_serial(hb.parent));
        }
        assert_eq!(serial.root, to_serial(adopted.root));
        assert_eq!(serial.imports.len(), adopted.imports.len());
        assert_eq!(serial.jsdoc_cache.len(), adopted.jsdoc_cache.len());
        for (node, jsdocs) in &adopted.jsdoc_cache {
            let expected: Vec<Node> = jsdocs.iter().map(|&n| to_serial(n)).collect();
            assert_eq!(serial.jsdoc_cache[&to_serial(*node)], expected);
            assert_eq!(file_store_js_doc(adopted.store, *node), Some(&jsdocs[..]));
        }
    }
}
