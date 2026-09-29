//! Per-file Go node stores (the nodes the ported Go parser creates) and the
//! file registry (the published stores and the `GoFile` of each file id).
//!
//! Go parser nodes are ordinary `*ast.Node` values made by `ast.NodeFactory`.
//! Here each parsed file gets one store. The store id is the file id, so a
//! store node is a normal `Node` handle: high 32 bits are the file id, low 32
//! bits are the slot index + 1.
//!
//! Each slot has a header (Go kind plus the mutable Go `NodeBase` fields:
//! parent, flags, loc) and, for a node slot, a leaked `crate::astdata::Node` that
//! holds the node data (a freeable parse owns it instead, `OwnedAst`).
//! Child ids inside that data are slot indexes of the same store:
//! - a child in the same file uses its own slot index;
//! - a child from another file or a synthetic child (Go shares the pointer)
//!   uses an alias slot, which `Node::new` resolves to that node;
//! - Go `nil` in a field that astdata stores as a required `NodeId` uses
//!   slot 0, which resolves to `Node::NIL`.
//!
//! `node.rs` reads kind, loc, flags and parent from the header of every
//! parsed node. Only synthetic nodes have no store.
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
//!   next unused id), and a published file is never changed. A static
//!   published file is never freed; a freeable file version is freed with
//!   its last holder (lsshells M3b, `ast/file_version.rs`), and a read of
//!   its id after that panics. A new program version shares the ids of its
//!   unchanged files.
//! - Tier 0 (`FROZEN`) is the first publish: program 1. Its dense tables
//!   are indexed by file id.
//! - Tier 1 (`LATER`) holds every later publish (edited files, other
//!   programs). One slot per id points at the `Frozen` of its publish.
//! - A freeable file version (an edited file in a language server or API
//!   process): its `FileVersion` owns its store and `GoFile`
//!   (`VersionStore`), and its tier 1 slot names its node shell, a leaked
//!   publish with only its node columns (`node_shell`). With
//!   `GOPORT_OWNED_NODES=1` its parse is a freeable parse
//!   (`enter_freeable_parse`, lsshells M3c), so its store also owns its
//!   astdata nodes, its pending lists and its parse lists (`OwnedAst`): the
//!   shell has no node column, and a node data read of the file is a scoped
//!   read (`read_store_node_miss`). By default the parse is a static parse,
//!   whose node column is in the shell, as before M3c.
//! - Every read of a published store goes through one inline lookup
//!   (`frozen!`, `static_frozen_of`): tier 0 first, then the tier 1 slot of the
//!   id, then the freeable version (its store and `GoFile`), in a cold
//!   block so a one-program process keeps the tier 0 code layout. So the hot node reads in
//!   `node.rs` and the perf columns (kinds, names, modifier bits, children,
//!   links, facts) answer for the nodes of a later program too, and return
//!   `None` on a miss. A read gets a borrow for its closure only; the
//!   accessors that return a borrow return a `FileRef` guard.
//! - After a registry miss, a synthetic id has no store (a few compares, no
//!   call). Any other id takes one cold call: the detached store, then the
//!   build stores of this thread.
//!
//! Binder data is not stored here: it stays in `GoFile::node_bind`, indexed
//! by slot index.

use crate::astdata::NodeData;
use crate::frontend::parser::SourceFileParseOptions;
use crate::prelude::*;
use std::cell::Cell;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, OnceLock};

/// Slot 0: Go `nil` stored in a astdata field that has no `Option`.
const NIL_SLOT: u32 = 0;

/// Position that marks a Go `nil` list in a astdata list field that has no
/// `Option`. Go positions are byte offsets, so they never reach it, and
/// `u32::MAX` is already the undefined position `-1`.
// PORT: astdata cannot change under the R97 rules. For store nodes the factory
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
    /// The astdata node (kind and data) of each node slot. `None` for the nil
    /// slot and alias slots. A node that a freeable parse owns is the marker
    /// node here (`owned_marker`); its data is in `owned`.
    nodes: Vec<Option<&'static crate::astdata::Node>>,
    /// lsshells M3c: the astdata nodes, pending lists and parse lists of a
    /// freeable parse (`enter_freeable_parse`), which the store owns. `None`
    /// for a static parse, whose nodes are in the leaked AST arena.
    owned: Option<Box<OwnedAst>>,
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
    /// `file.ContainsNonASCII` (Go `NewSourceFile` sets it from the text),
    /// written by `finishSourceFile`. Reads of a file that is not published
    /// use them (`ast::source_file_language_variant`,
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
/// published store node need no load of its astdata node and data
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
///
/// Tier 0 and tier 1 are `Frozen<'static>` (leaked). A freeable file
/// version (lsshells M3b) owns its store and `GoFile` (`VersionStore`); a
/// read of them sees a one-file `Frozen` view that borrows them for the
/// read (`VersionStore::view`). Its node columns are leaked in its node
/// shell, the tier 1 publish of its id (`node_shell`), so its nodes
/// are read inline, as the nodes of a tier 1 file. When the store owns its
/// astdata nodes (lsshells M3c) the shell has no node column (`nodes` is
/// empty): the version owns the nodes, and a data read of them is a scoped
/// read.
struct Frozen<'a> {
    /// The first file id of the publish.
    base: usize,
    stores: &'a [FileStore],
    headers: &'a [&'a [NodeHeader]],
    /// `FileStore::nodes` of each store. Empty in the node shell of a store
    /// that owns its nodes (`Frozen::lacks_node_column`), so a node data read
    /// of that freeable file version misses the static tiers.
    nodes: &'a [&'a [Option<&'static crate::astdata::Node>]],
    /// `headers[file][i].kind`, packed (`FileStore::kinds`). `Node::kind`
    /// reads only this.
    kinds: &'a [&'a [SyntaxKind]],
    /// U1 (a): `FileStore::names` of each store (`Node::text_name`).
    names: &'a [&'a [Name]],
    /// U1 (b): `FileStore::modifier_bits` of each store
    /// (`Node::modifier_flags`).
    modifier_bits: &'a [&'a [u16]],
    /// What `Node::new` reads for each store, and its facts.
    per_store: &'a [FrozenStore<'a>],
    /// The `GoFile` of each file id of the publish.
    go_files: &'a [GoFile],
}

/// The per-store part of `Frozen` that `Node::new` reads.
#[derive(Clone, Copy)]
struct FrozenStore<'a> {
    /// `try_resolve_store_id(file, i)` for every slot, computed once
    /// (`FileStore::resolved`). Empty for an alias-free store.
    resolved: &'a [Node],
    /// What slot 0 resolves to (Go `nil`).
    nil: Node,
    facts: StoreFacts,
    /// U4: `FileStore::children`. Next to `resolved`, so a child read loads
    /// one per-store record.
    children: &'a [SlotChildren],
    /// R2-5: `FileStore::links`.
    links: &'a [SlotLinks],
    /// `FileStore::root` (`frozen_source_file_of_node`).
    root: Node,
}

impl<'a> FrozenStore<'a> {
    /// The per-store part of store `s`, whose slot 0 resolves to `nil`.
    fn of(s: &'a FileStore, nil: Node) -> Self {
        FrozenStore {
            resolved: &s.resolved,
            nil,
            facts: s.facts,
            children: &s.children,
            links: &s.links,
            root: s.root,
        }
    }
}

/// `try_resolve_store_id(file, index)` for store `file` of publish `f`, whose
/// per-store part is `s`.
// PERF: effect P7-1. Most stores have no alias slot. For them a child id is
// the slot handle (or the slot 0 value), so `Node::new` needs no load from
// a per-slot table.
#[inline]
fn frozen_resolve_slot(f: &Frozen<'_>, s: &FrozenStore<'_>, file: usize, index: usize) -> Node {
    if !s.facts.alias_free {
        return s.resolved[index];
    }
    let n = if index == NIL_SLOT as usize {
        s.nil
    } else {
        handle(file, index as u32)
    };
    // A node shell has no node column (lsshells M3c).
    debug_assert!(
        f.nodes.get(file - f.base).is_none_or(|nodes| {
            n == resolve_slot(file, index, nodes, f.headers[file - f.base])
        })
    );
    n
}

impl Frozen<'_> {
    /// True for a publish with no node column: the node shell of a freeable
    /// file version whose store owns its astdata nodes (`node_shell`,
    /// lsshells M3c). Every other publish has one entry per store.
    #[inline]
    fn lacks_node_column(&self) -> bool {
        self.nodes.is_empty()
    }
}

/// The store and `GoFile` of a freeable file version (lsshells M3b), owned
/// by its `FileVersion` (`ast::file_version`). The publish moves them here
/// instead of into a leaked `Frozen`; they are freed with the version.
pub(crate) struct VersionStore {
    /// The file id.
    file: usize,
    /// The store, without its node columns, which are in `shell`, and
    /// without the columns that only cache node data (`node_shell`). A
    /// store that owns its astdata nodes (`FileStore::owned`, lsshells M3c)
    /// keeps them and its node column (`FileStore::nodes`).
    store: FileStore,
    go_file: GoFile,
    /// The node shell of the file: its tier 1 publish, with the leaked node
    /// columns.
    shell: &'static Frozen<'static>,
}

impl VersionStore {
    /// The `GoFile` of the version.
    #[inline]
    pub(crate) fn go_file(&self) -> &GoFile {
        &self.go_file
    }

    /// Runs `read` on a one-file `Frozen` view of this version: the file is
    /// at index 0. Its node tables are the ones of its node shell, so the
    /// view has no node column (a `frozen!` read of `nodes` misses; the
    /// scoped reads use `VersionStore::store`).
    #[inline]
    fn view<R>(&self, read: impl for<'v> FnOnce(&'v Frozen<'v>) -> R) -> R {
        let shell = self.shell;
        let frozen = Frozen {
            base: self.file,
            stores: std::slice::from_ref(&self.store),
            headers: shell.headers,
            nodes: shell.nodes,
            kinds: shell.kinds,
            names: shell.names,
            modifier_bits: shell.modifier_bits,
            per_store: shell.per_store,
            go_files: std::slice::from_ref(&self.go_file),
        };
        read(&frozen)
    }
}

/// Tier 0: the first publish.
static FROZEN: OnceLock<Frozen<'static>> = OnceLock::new();

/// The tier 1 slots of `LATER_CHUNK` consecutive file ids.
type LaterChunk = [OnceLock<&'static Frozen<'static>>; LATER_CHUNK];

/// Tier 1: the publish of each file id after the first publish. Each later
/// publish is leaked once, and the slot of each of its ids names it. The
/// slot of a freeable file version names its node shell
/// (`node_shell`).
static LATER: [OnceLock<Box<LaterChunk>>; TIER1_LIMIT / LATER_CHUNK] =
    [const { OnceLock::new() }; TIER1_LIMIT / LATER_CHUNK];

/// The next unused file id. Only `publish_file_stores` changes it.
static PUBLISHED: AtomicUsize = AtomicUsize::new(0);

/// The tier 1 publish of file `file` and the index of `file` in it. `None`
/// for an id that no later publish holds. An id at or above `TIER1_LIMIT`
/// (a synthetic or provisional id) leaves after one compare.
// PERF: M3 (multiprog `97c2ed829` (2)). Inline, so a node of a later
// program (`tsc -b`, an edited file) costs a few more loads and compares
// (the chunk and the slot of its id) than a node of the first program, not
// two out-of-line calls and a closure. Before M3 the perf columns also
// missed for such a node, so its reads took the slow paths in `node.rs`.
// `inline(always)`: in `static_frozen_of` it is in a cold block, where LLVM
// inlines less.
#[inline(always)]
fn later(file: usize) -> Option<(&'static Frozen<'static>, usize)> {
    let chunk = LATER.get(file / LATER_CHUNK)?.get()?;
    let frozen: &'static Frozen<'static> = chunk[file % LATER_CHUNK].get()?;
    Some((frozen, file - frozen.base))
}

/// Marks the tier 1 part of `static_frozen_of` as cold. It does nothing.
// PERF: rustc gives a branch into a block that calls a `#[cold]` function
// a low weight (`find_cold_blocks`), and LLVM puts that block after the hot
// code. `std::hint::cold_path` does the same, but is stable only from Rust
// 1.95. `inline(never)` keeps the call in the MIR until codegen reads it;
// LLVM can then drop the call, as it has no effect.
#[cold]
#[inline(never)]
fn later_publish_path() {}

/// Where `static_frozen_of` found no entry for a file.
#[derive(Clone, Copy)]
enum StaticMiss {
    /// No publish holds the file: unpublished, synthetic or provisional.
    None,
    /// No static publish holds the id, and it is below `PUBLISHED`: it can
    /// be a freeable file version (lsshells M3b, `freeable_read`).
    MaybeFreeable,
}

/// The one file lookup of the registry reads (PORTING.md "AST": store
/// columns are read through one helper), static part: for published store
/// file `file` in tier 0 or tier 1, its publish, the index of `file` in
/// that publish, and that entry of the table that `table` picks. Tier 0
/// first, then tier 1 (`later`). The `frozen!` macro reads a freeable file
/// version after a `StaticMiss::MaybeFreeable`.
// PERF: M3. The tier 0 test is the bounds check of the picked table. The
// entry is found before the two tiers join, so the caller indexes it with
// no second bounds check.
// PERF: M3 `goport -p` cost (mp3). A one-program process never runs tier 1:
// its only tier 0 misses are synthetic ids, which leave at the
// `TIER1_LIMIT` compare. But tier 1 code inline in each hot read site made
// `goport -p` 1.5% to 3.5% slower (more icache and branch misses, +0.3%
// instructions; `mp2/m3.md`). So tier 1 is a cold block
// (`later_publish_path`) that LLVM puts after the hot code. A later program
// still reads tier 1 inline, with no call. A runtime "later publish" flag
// would not help: it removes no code from the read sites.
// PERF: lsshells M3b. The read runs once, after the tiers join, as in R134
// `frozen_of`. A first M3b shape ran the read closure in each tier branch
// and called `freeable_read` from the cold block; the read sites grew, LLVM
// stopped inlining `frozen_read` and `Node::parent`, and `goport -p` ran
// 2.8% to 4.2% more instructions (lsshells/m3/M3b/prof).
#[inline]
fn static_frozen_of<T: 'static>(
    file: usize,
    table: impl Fn(&'static Frozen<'static>) -> &'static [T],
) -> Result<(&'static Frozen<'static>, usize, &'static T), StaticMiss> {
    let Some(tier0) = FROZEN.get() else {
        return Err(StaticMiss::None);
    };
    if let Some(entry) = table(tier0).get(file) {
        return Ok((tier0, file, entry));
    }
    // A synthetic or provisional id is in no publish. It leaves here,
    // outside the cold block.
    if file >= TIER1_LIMIT {
        return Err(StaticMiss::None);
    }
    later_publish_path();
    match later(file) {
        Some((f, local)) => match table(f).get(local) {
            Some(entry) => Ok((f, local, entry)),
            // A node shell (`node_shell`) has no store and no
            // `GoFile`: they are in the freeable file version.
            None => Err(StaticMiss::MaybeFreeable),
        },
        None => Err(StaticMiss::MaybeFreeable),
    }
}

/// A registry read of table `$table` of published store file `$file`:
/// `$body` runs with `$f` (the publish), `$local` (the index of the file in
/// it) and `$entry` (`&$f.$table[$local]`), and gives `Some` of its value.
/// Tier 0 and tier 1 (`static_frozen_of`), then a freeable file version
/// (`freeable_read`, lsshells M3b), which is pinned while `$body` runs and
/// is seen as a one-file publish (`$local` is 0). `None` for any other
/// file: unpublished, synthetic or provisional. Panics for a dead file
/// version. `$body` gets a borrow for the read only, so it copies its
/// result out.
// PERF: `$body` is written twice: once inline after the static tiers join,
// once in the closure that the out-of-line `freeable_read` runs. So a read
// site holds one copy of the read, as in R134.
macro_rules! frozen {
    ($file:expr, $table:ident, |$f:pat_param, $local:pat_param, $entry:pat_param| $body:expr) => {{
        let file: usize = $file;
        match static_frozen_of(file, |f| f.$table) {
            Ok((f, local, entry)) => {
                let ($f, $local, $entry) = (f, local, entry);
                Some($body)
            }
            Err(StaticMiss::None) => None,
            Err(StaticMiss::MaybeFreeable) => freeable_read(file, |f| {
                f.$table.first().map(|entry| {
                    let ($f, $local, $entry) = (f, 0usize, entry);
                    $body
                })
            }),
        }
    }};
}

/// `frozen!` for the static tiers only (tier 0 and tier 1): `None` for the
/// store and `GoFile` of a freeable file version, as for any other file.
/// The inline fast paths of the node reads use it, so their code has no
/// call, as in R134. The node tables of a freeable file version are in its
/// node shell in tier 1, so they are read here. Use it only where `None`
/// sends the caller to an exact path.
// PERF: lsshells M3b. With the `freeable_read` call in each inline fast
// path, those paths were no longer leaf code: LLVM saved registers on each
// call and stopped inlining some readers (`frozen_header`, `bind_field`),
// and `goport -p` ran 2% to 3.4% more instructions (lsshells/m3/M3b/prof).
macro_rules! frozen_static {
    ($file:expr, $table:ident, |$f:pat_param, $local:pat_param, $entry:pat_param| $body:expr) => {
        match static_frozen_of($file, |f| f.$table) {
            Ok((f, local, entry)) => {
                let ($f, $local, $entry) = (f, local, entry);
                Some($body)
            }
            Err(_) => None,
        }
    };
}

/// The freeable branch of `frozen!`: `read` on the view of live file
/// version `file` (lsshells M3b). `None` for any other id and before the
/// version is published. Panics for a dead version.
#[cold]
#[inline(never)]
fn freeable_read<R>(
    file: usize,
    read: impl for<'a> FnOnce(&'a Frozen<'a>) -> Option<R>,
) -> Option<R> {
    if super::file_version::is_hot(file) {
        return super::file_version::with_hot(|store| store.view(read));
    }
    if !super::file_version::any_freeable_published() {
        return None;
    }
    freeable_read_inline(file, read)
}

/// `freeable_read`, inline: the binder data read of a node of a freeable
/// file version (`freeable_go_file_read`, `Node::bind_field`) has no
/// further call on a pin hit.
// PERF: lsshells M3b. A call more per read made query-core and effect
// edits about 2 ms slower than one call (lsshells/m3/M3b/long q3, q4).
#[inline]
fn freeable_read_inline<R>(
    file: usize,
    read: impl for<'a> FnOnce(&'a Frozen<'a>) -> Option<R>,
) -> Option<R> {
    // Callers test `any_freeable_published` first.
    if file >= PUBLISHED.load(Ordering::Acquire) {
        return None;
    }
    super::file_version::with_file_version(file, |version| {
        version.published().and_then(|store| store.view(read))
    })
    .flatten()
}

/// `read` on the `GoFile` of freeable file version `file`. `None` for any
/// other file.
#[inline]
pub fn freeable_go_file_read<R>(file: usize, read: impl FnOnce(&GoFile) -> R) -> Option<R> {
    if super::file_version::is_hot(file) {
        return Some(super::file_version::with_hot(|store| read(&store.go_file)));
    }
    if !super::file_version::any_freeable_published() {
        return None;
    }
    freeable_read_inline(file, |f| f.go_files.first().map(read))
}

/// `read` on the store and `GoFile` of live freeable file version `file`
/// (lsshells M3c), pinned while `read` runs. `None` for any other id and
/// before the version is published; `read` then did not run. Panics for a
/// dead version.
// PERF: lsshells M3c. The node data reads of the edited file come here
// (`with_scoped_store_node`, `with_store_list`), so they build no one-file
// `Frozen` view, as `Node::bind_field_slow` does for the binder data.
#[inline]
fn with_version_store<R>(file: usize, read: impl FnOnce(&VersionStore) -> R) -> Option<R> {
    if super::file_version::is_hot(file) {
        return Some(super::file_version::with_hot(read));
    }
    if !super::file_version::any_freeable_published()
        || file >= TIER1_LIMIT
        || file >= PUBLISHED.load(Ordering::Acquire)
    {
        return None;
    }
    super::file_version::with_file_version(file, |version| version.published().map(read)).flatten()
}

/// The static part of the registry read (tier 0 and tier 1) for table
/// `table`, with a `'static` entry. `None` for the store and `GoFile` of a
/// freeable file version, as for any other file.
#[inline]
fn static_frozen<T: 'static>(
    file: usize,
    table: impl Fn(&'static Frozen<'static>) -> &'static [T],
) -> Option<&'static T> {
    static_frozen_of(file, table)
        .ok()
        .map(|(_, _, entry)| entry)
}

/// The live freeable version of published file `file` as a pin, for a
/// `FileRef::Pinned` guard. `None` for any other id and before the
/// version is published. Panics for a dead version.
#[cold]
#[inline(never)]
fn published_version(file: usize) -> Option<super::file_version::VersionPin> {
    if super::file_version::is_hot(file) {
        return Some(super::file_version::hot_pin());
    }
    if file >= TIER1_LIMIT
        || !super::file_version::any_freeable_published()
        || file >= PUBLISHED.load(Ordering::Acquire)
    {
        return None;
    }
    super::file_version::pinned_file_version(file).filter(|version| version.published().is_some())
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

/// The unpublished store `file` of this thread (active, detached or built),
/// after a registry miss (`frozen!`). Before the first publish every
/// store is here. After it, a synthetic id has no store (a few compares,
/// no call), and any other id takes one cold call.
#[inline]
fn unpublished_store(file: usize) -> Option<StoreCell> {
    match FROZEN.get() {
        None => build_store(file),
        Some(_) if is_storeless_id(file) => None,
        Some(_) => unpublished_store_after_publish(file),
    }
}

/// The cold part of `unpublished_store`.
#[cold]
#[inline(never)]
fn unpublished_store_after_publish(file: usize) -> Option<StoreCell> {
    build_store(file)
}

/// Runs `f` on store `file`: published (tier 0, tier 1 or a freeable file
/// version), or an unpublished store of this thread. `None` when this
/// thread cannot see a store `file`.
#[inline]
fn try_with_store<R>(file: usize, f: impl FnOnce(&FileStore) -> R) -> Option<R> {
    let mut f = Some(f);
    // `frozen!` gives `None` only when it did not call its body.
    if let Some(result) = frozen!(file, stores, |_, _, store| {
        (f.take().expect("the store is read once"))(store)
    }) {
        return Some(result);
    }
    let f = f.take()?;
    unpublished_store(file).map(|store| f(&store.borrow()))
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
/// store of this thread. Inside a freeable parse scope
/// (`enter_freeable_parse`) the store owns its astdata nodes (`OwnedAst`).
pub fn new_file_store(file_name: &'static str, text: &'static str) -> usize {
    let mut new = FileStore::new(file_name, text);
    if FREEABLE_PARSE.get() {
        new.owned = Some(Box::new(OwnedAst::new(new.headers.capacity())));
    }
    let store: StoreCell = leak_in_ast_arena(RefCell::new(new));
    let id = BUILD.with(|b| {
        let mut b = b.borrow_mut();
        let id = b.next_id();
        b.stores.push(store);
        id
    });
    ACTIVE.set(Some((id, store)));
    id
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
        node: &crate::astdata::Node,
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
        debug_assert!(
            self.owned
                .as_deref()
                .is_none_or(|owned| owned.cell_of.len() == self.headers.len())
        );
    }

    /// R2-5: frees the chain of slot `index` (no chain holds its old
    /// children then) and makes the chain of `index` unknown.
    fn unlink_children(&mut self, index: usize) {
        unlink_children(&mut self.build_links, index);
    }

    /// R2-5: appends slot `child` to the chain of slot `parent`, whose last
    /// child is `*last` (`LINK_END` before the first). False, with nothing
    /// written, when a chain already holds `child`.
    #[inline]
    fn link_child(&mut self, parent: usize, last: &mut u32, child: usize) -> bool {
        link_child(&mut self.build_links, parent, last, child)
    }
}

/// `FileStore::unlink_children` on the link column `links`.
fn unlink_children(links: &mut [SlotLinks], index: usize) {
    let mut child = std::mem::replace(&mut links[index].first_child, LINK_NONE);
    if child == LINK_NONE {
        return;
    }
    while child != LINK_END {
        let entry = &mut links[child as usize];
        child = std::mem::replace(&mut entry.next_sibling, LINK_NONE);
        debug_assert_ne!(child, LINK_NONE, "R2-5 chain without an end");
    }
}

/// `FileStore::link_child` on the link column `links`.
#[inline]
fn link_child(links: &mut [SlotLinks], parent: usize, last: &mut u32, child: usize) -> bool {
    if links[child].next_sibling != LINK_NONE {
        return false;
    }
    links[child].next_sibling = LINK_END;
    let child = child as u32;
    if *last == LINK_END {
        links[parent].first_child = child;
    } else {
        links[*last as usize].next_sibling = child;
    }
    *last = child;
    true
}

// ──────────────────────────────────────────────────────────────────────
// Owned nodes of a freeable parse (lsshells M3c)
// ──────────────────────────────────────────────────────────────────────

thread_local! {
    /// Set while a freeable parse with owned nodes runs on this thread
    /// (`enter_freeable_parse`, `GOPORT_OWNED_NODES=1`): `new_file_store`
    /// makes a store that owns its astdata nodes.
    static FREEABLE_PARSE: Cell<bool> = const { Cell::new(false) };
    /// Set while any freeable parse runs on this thread
    /// (`is_freeable_parse`).
    static FREEABLE_VERSION_PARSE: Cell<bool> = const { Cell::new(false) };
}

/// Starts a freeable parse on this thread (`is_freeable_parse`). With
/// `GOPORT_OWNED_NODES=1` (`owned_nodes_enabled`) the stores that
/// `new_file_store` makes until the scope ends own their astdata nodes,
/// pending lists and parse lists (`OwnedAst`), so they are freed with the
/// store, not leaked in the AST arena. The language server parse cache
/// opens it for a new version of a published path (`ast::freeable_path`),
/// the version that gets a `FileVersion`.
// PORT: Go nodes are heap objects that the GC frees with their file. A
// static parse keeps its nodes in the leaked AST arena, so its node reads
// stay `'static`.
#[must_use]
pub fn enter_freeable_parse() -> FreeableParseScope {
    FreeableParseScope {
        previous: FREEABLE_PARSE.replace(owned_nodes_enabled()),
        previous_version: FREEABLE_VERSION_PARSE.replace(true),
    }
}

/// True when `GOPORT_OWNED_NODES=1`: a freeable parse owns its nodes
/// (lsshells M3c). Otherwise it is a static parse (its nodes stay in the
/// leaked AST arena, and its node shell has a node column), as before M3c.
/// Read once.
// PERF: off by default. With it on, the edits of query-core, hono and
// effect freed 0.2 to 1.0 MiB more each, but their median was 0.9 to 1.6 ms
// slower than with it off (ls_edit_bench long, mini-abf9, lsshells/m3/M3c
// ab2), over the 0.5 ms line: every node data and list read of the edited
// file is a pinned read (about 40,000 per edit on effect).
fn owned_nodes_enabled() -> bool {
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("GOPORT_OWNED_NODES").as_deref() == Ok("1"))
}

/// `enter_freeable_parse` with owned nodes on, whatever the flag, for the
/// unit tests of the owned stores.
#[cfg(test)]
pub(crate) fn enter_owned_parse() -> FreeableParseScope {
    FreeableParseScope {
        previous: FREEABLE_PARSE.replace(true),
        previous_version: FREEABLE_VERSION_PARSE.replace(true),
    }
}

/// The scope of `enter_freeable_parse`.
pub struct FreeableParseScope {
    previous: bool,
    previous_version: bool,
}

impl Drop for FreeableParseScope {
    fn drop(&mut self) {
        FREEABLE_PARSE.set(self.previous);
        FREEABLE_VERSION_PARSE.set(self.previous_version);
    }
}

/// True while a freeable parse runs on this thread (`enter_freeable_parse`),
/// with or without owned nodes: the parse of a new version of an edited
/// file, which leaks nothing per version (`parse_source_file`).
#[must_use]
pub fn is_freeable_parse() -> bool {
    FREEABLE_VERSION_PARSE.get()
}

/// Cells per chunk of `OwnedAst::chunks`.
// PERF: 256 cells of about 48 bytes is a 12 KiB chunk, one small size
// class of jemalloc.
const OWNED_CHUNK: usize = 256;

/// `OwnedAst::cell_of` of a slot that has no owned node: the nil slot, an
/// alias slot, or a node slot with a static node (a shared name node,
/// `alloc_store_shared_name_node`, or a lib snapshot slot).
const NO_CELL: u32 = u32::MAX;

/// A sealed chunk of `OwnedAst::chunks` (up to `OWNED_CHUNK` cells), or
/// the flat table of every cell after the parse (`OwnedAst::flat`). A held
/// read shares it (`HeldStoreNode::Owned`).
pub type OwnedChunk = Arc<Vec<crate::astdata::Node>>;

/// The number of astdata nodes that the live freeable stores own
/// (`OwnedAst`), for tests.
static OWNED_NODES: AtomicUsize = AtomicUsize::new(0);

/// The number of astdata nodes that the live stores of freeable parses own
/// (lsshells M3c). A freeable file version frees its nodes when it dies, so
/// this does not grow with the edits. Tests use it.
#[must_use]
pub fn owned_node_count() -> usize {
    OWNED_NODES.load(Ordering::Relaxed)
}

/// The astdata nodes, pending lists and parse lists of a freeable parse
/// (lsshells M3c, `enter_freeable_parse`), owned by its store and so, after
/// the publish, by its `FileVersion`: they are freed with the version. A
/// static parse keeps them in the leaked AST arena (`AST_ARENA`).
///
/// A node slot names its node by cell (`cell_of`). Its `FileStore::nodes`
/// entry is the marker node (`owned_marker`), so the node column keeps its
/// meaning (a node slot is `Some`); the marker is never read as data (every
/// read of a slot goes through `FileStore::slot_ast_node` or
/// `FileStore::static_node_of`). A data write (`replace_store_node_data`)
/// fills a new cell and moves the slot to it, so a list handle taken before
/// the write (`StoreList`, which names the cell) still reads the old list,
/// like a Go `*NodeList` pointer.
pub(crate) struct OwnedAst {
    /// While the parser runs: the sealed chunks, whose nodes never move, so
    /// a held read can share one apart from the store borrow
    /// (`HeldStoreNode`). Cell `c` is node `c % OWNED_CHUNK` of chunk
    /// `c / OWNED_CHUNK`; the open chunk (`open`) has the chunk index
    /// `chunks.len()`.
    chunks: Vec<OwnedChunk>,
    /// While the parser runs: the open chunk. A new node fills its next
    /// cell (a plain push); a full chunk, or one that a held read needs, is
    /// sealed (`seal`), and the next node starts a new chunk.
    open: Vec<crate::astdata::Node>,
    /// After the parse (`finish`): every cell, `flat[cell]`, in one table.
    /// A cell that an early seal skipped holds `hole_node`.
    // PERF: lsshells M3f. A node read of a published version is one index
    // (after `cell_of`), not a chunk and a cell.
    flat: OwnedChunk,
    /// The number of nodes in the chunks.
    len: usize,
    /// The part of `len` that `OWNED_NODES` counts (`count_owned_nodes`).
    counted: usize,
    /// The cell of each slot, `NO_CELL` for a slot with no owned node. One
    /// entry per header.
    cell_of: Vec<u32>,
    /// The pending lists of the parse (U1 (e), `StoreList` with
    /// `PENDING_SEL`).
    pending: Vec<OwnedPending>,
    /// Go `file.jsdocCache` before the publish: the entries of
    /// `set_file_store_js_doc_cache` and of `resolve_file_store_js_doc`. A
    /// static parse leaks them (`FileStore::jsdoc_cache`).
    jsdoc: FxHashMap<Node, Box<[Node]>>,
    /// The parse diagnostics before the publish
    /// (`set_file_store_parse_fields`). A static parse leaks them
    /// (`FileStore::diagnostics`).
    diagnostics: Box<[Diagnostic]>,
}

impl OwnedAst {
    /// The owned part of a new store with room for `slots` slots, with the
    /// entry of the nil slot.
    fn new(slots: usize) -> Self {
        let mut cell_of = Vec::with_capacity(slots);
        cell_of.push(NO_CELL);
        Self {
            chunks: Vec::new(),
            open: Vec::new(),
            flat: Arc::default(),
            len: 0,
            counted: 0,
            cell_of,
            pending: Vec::new(),
            jsdoc: FxHashMap::default(),
            diagnostics: Box::default(),
        }
    }

    /// The astdata node in cell `cell`.
    #[inline(always)]
    fn node(&self, cell: u32) -> &crate::astdata::Node {
        match self.flat.get(cell as usize) {
            Some(node) => node,
            None => self.build_node(cell as usize),
        }
    }

    /// `node` while the parser runs.
    #[inline]
    fn build_node(&self, cell: usize) -> &crate::astdata::Node {
        match self.chunks.get(cell / OWNED_CHUNK) {
            Some(chunk) => &chunk[cell % OWNED_CHUNK],
            None => &self.open[cell % OWNED_CHUNK],
        }
    }

    /// The node in cell `cell`, held apart from the store borrow. A cell of
    /// the open chunk seals it first (`&mut`). `None` for a cell of the
    /// open chunk when the caller has only a shared borrow.
    fn held(&self, cell: u32) -> Option<HeldStoreNode> {
        let cell = cell as usize;
        if cell < self.flat.len() {
            return Some(HeldStoreNode::Owned {
                chunk: Arc::clone(&self.flat),
                index: cell,
            });
        }
        let chunk = self.chunks.get(cell / OWNED_CHUNK)?;
        Some(HeldStoreNode::Owned {
            chunk: Arc::clone(chunk),
            index: cell % OWNED_CHUNK,
        })
    }

    /// `held`, which seals the open chunk when it has the cell.
    fn held_mut(&mut self, cell: u32) -> HeldStoreNode {
        if self.flat.is_empty() && cell as usize / OWNED_CHUNK == self.chunks.len() {
            self.seal();
        }
        self.held(cell).expect("a sealed cell")
    }

    /// Moves the open chunk to the sealed chunks.
    fn seal(&mut self) {
        let open = std::mem::replace(&mut self.open, Vec::with_capacity(OWNED_CHUNK));
        self.chunks.push(Arc::new(open));
    }

    /// Puts `node` in the next cell and returns that cell.
    // PERF: lsshells M3f. A plain push into the open chunk; M3c tested
    // `Arc::get_mut` (an atomic compare-exchange) per node.
    #[inline]
    fn push(&mut self, node: crate::astdata::Node) -> u32 {
        debug_assert!(self.flat.is_empty(), "a node pushed after the parse");
        self.len += 1;
        if self.open.len() == OWNED_CHUNK {
            self.seal();
        } else if self.open.capacity() == 0 {
            self.open.reserve_exact(OWNED_CHUNK);
        }
        self.open.push(node);
        owned_cell(self.chunks.len(), self.open.len() - 1)
    }

    /// Moves every cell into `flat` (end of the parse). A sealed chunk that
    /// a held read still shares is copied.
    fn finish(&mut self) {
        let chunks = std::mem::take(&mut self.chunks);
        let mut flat = Vec::with_capacity(chunks.len() * OWNED_CHUNK + self.open.len());
        for chunk in chunks {
            let mut cells = Arc::try_unwrap(chunk).unwrap_or_else(|chunk| (*chunk).clone());
            flat.append(&mut cells);
            // An early seal (`held_mut`) leaves the rest of its chunk unused.
            flat.resize_with(flat.len().next_multiple_of(OWNED_CHUNK), hole_node);
        }
        flat.append(&mut self.open);
        self.open = Vec::new();
        self.flat = Arc::new(flat);
    }

    /// Adds the nodes of this store that `OWNED_NODES` does not count yet.
    // PERF: once per parse (`FileStore::end_parse`), not an atomic write per
    // node.
    fn count_owned_nodes(&mut self) {
        OWNED_NODES.fetch_add(self.len - self.counted, Ordering::Relaxed);
        self.counted = self.len;
    }

    /// Adds pending list `list` and returns its handle in store `file`.
    fn push_pending(&mut self, file: usize, list: OwnedPending) -> StoreList {
        let key = u32::try_from(self.pending.len()).expect("too many pending lists");
        let handle = StoreList::new(file, key, PENDING_SEL, StoreListView::Pending(&list));
        self.pending.push(list);
        handle
    }
}

impl Drop for OwnedAst {
    fn drop(&mut self) {
        OWNED_NODES.fetch_sub(self.counted, Ordering::Relaxed);
    }
}

/// The node in a cell that an early seal skipped (`OwnedAst::finish`). No
/// slot names it. Its data box has no size, so it allocates nothing.
fn hole_node() -> crate::astdata::Node {
    ast_node(
        SyntaxKind::Unknown,
        NodeData::Token(Box::new(crate::astdata::TokenData)),
    )
}

/// The cell of node `index` of chunk `chunk` (`OwnedAst::chunks`).
fn owned_cell(chunk: usize, index: usize) -> u32 {
    let cell = chunk
        .checked_mul(OWNED_CHUNK)
        .and_then(|first| u32::try_from(first + index).ok())
        .expect("too many owned nodes in one store");
    assert_ne!(cell, NO_CELL, "too many owned nodes in one store");
    cell
}

/// The node that `FileStore::nodes` holds for a slot whose astdata node a
/// freeable parse owns (`OwnedAst`). It is never read as data.
fn owned_marker() -> &'static crate::astdata::Node {
    static MARKER: OnceLock<&'static crate::astdata::Node> = OnceLock::new();
    MARKER.get_or_init(|| {
        Box::leak(Box::new(ast_node(
            SyntaxKind::Unknown,
            NodeData::Token(Box::new(crate::astdata::TokenData)),
        )))
    })
}

/// U1 (e) for a freeable parse: a pending list that the store owns (what
/// `PendingList` and `PendingModifierList` are for a static parse).
#[derive(Debug)]
pub struct OwnedPending {
    /// Go `list.Loc` in astdata form (`ts_range`).
    range: crate::astdata::text::TextRange,
    /// The store ids of the nodes (`store_child_id`).
    nodes: Box<[crate::astdata::NodeId]>,
    /// The astdata bit (`NodeList::stored_trailing_comma`).
    has_trailing_comma: bool,
    /// Go `ModifiersToFlags(nodes)` of a modifier list; `None` for a node
    /// list.
    flags: Option<crate::astdata::ModifierFlags>,
}

/// The selector id of a pending list (`StoreList::sel_id`). The selector
/// ids of the list sites are below it (`ast::synthetic::SELECTOR_LIMIT`).
pub(crate) const PENDING_SEL: u32 = (1 << StoreList::SEL_BITS) - 1;

/// A list of a store that owns its astdata nodes (a freeable parse,
/// lsshells M3c), as a `NodeList`, `ModifierList` or `NodeSlice` names it:
/// the list field that list selector `sel` (`list_selector`) finds in the
/// data of cell `key` of store `file`, or pending list `key` of that store
/// when `sel` is `PENDING_SEL`. It is read at each use (`with_store_list`),
/// so it keeps no borrow. 12 bytes, so the list handles stay 16 bytes.
// PERF: lsshells M3f. The handle also keeps what the hot list reads need
// and a list never changes (`sel`: the Go nil marker, the astdata
// `has_trailing_comma` bit and the length), so `NodeList::is_nil`,
// `NodeList::nodes` and `NodeSlice::len` read no store.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StoreList {
    file: u32,
    key: u32,
    /// Bits 0 to 9: the selector id, or `PENDING_SEL`. Bit 10: the range
    /// is the Go nil marker (`is_nil_list_range`). Bit 11: the astdata
    /// `has_trailing_comma` bit. Bits 12 to 31: the length, or `LEN_MAX`
    /// for a longer list (then read at each use).
    sel: u32,
}

impl StoreList {
    const SEL_BITS: u32 = 10;
    const NIL_BIT: u32 = 1 << 10;
    const COMMA_BIT: u32 = 1 << 11;
    const LEN_SHIFT: u32 = 12;
    const LEN_MAX: u32 = u32::MAX >> Self::LEN_SHIFT;

    /// The handle of list `view` of store `file`: pending list `key`
    /// (`sel` is `PENDING_SEL`), or the list that selector `sel` finds in
    /// the data of cell `key`.
    fn new(file: usize, key: u32, sel: u32, view: StoreListView<'_>) -> Self {
        debug_assert!(sel <= PENDING_SEL);
        let mut bits = sel;
        if is_nil_list_range(&view.range()) {
            bits |= Self::NIL_BIT;
        }
        if view.has_trailing_comma() {
            bits |= Self::COMMA_BIT;
        }
        let len =
            u32::try_from(view.ids().len()).map_or(Self::LEN_MAX, |len| len.min(Self::LEN_MAX));
        Self {
            file: file as u32,
            key,
            sel: bits | (len << Self::LEN_SHIFT),
        }
    }

    /// The store id of the list.
    #[inline]
    #[must_use]
    pub fn file(self) -> usize {
        self.file as usize
    }

    /// The selector id, or `PENDING_SEL` for a pending list.
    #[inline]
    fn sel_id(self) -> u32 {
        self.sel & PENDING_SEL
    }

    /// True when the list is the Go `nil` marker (`NIL_LIST_POS`): Go
    /// `list == nil`.
    #[inline]
    #[must_use]
    pub fn is_nil_marker(self) -> bool {
        self.sel & Self::NIL_BIT != 0
    }

    /// The astdata `has_trailing_comma` bit.
    #[inline]
    #[must_use]
    pub fn stored_trailing_comma(self) -> bool {
        self.sel & Self::COMMA_BIT != 0
    }

    /// The number of nodes in the list.
    #[inline]
    #[must_use]
    pub fn len(self) -> usize {
        match self.sel >> Self::LEN_SHIFT {
            Self::LEN_MAX => self.long_len(),
            len => len as usize,
        }
    }

    /// `len` of a list of `LEN_MAX` nodes or more.
    #[cold]
    #[inline(never)]
    fn long_len(self) -> usize {
        with_store_list(self, |l| l.ids().len())
    }

    /// True when the list has no nodes.
    #[inline]
    #[must_use]
    pub fn is_empty(self) -> bool {
        self.sel >> Self::LEN_SHIFT == 0
    }
}

/// A list of a store that owns its nodes, read in place
/// (`with_store_list`): a list field of node data (`AnyList`) or a pending
/// list.
#[derive(Clone, Copy)]
pub enum StoreListView<'a> {
    Data(AnyList<'a>),
    Pending(&'a OwnedPending),
}

impl<'a> StoreListView<'a> {
    /// Go `list.Loc` in astdata form.
    #[must_use]
    pub fn range(self) -> crate::astdata::text::TextRange {
        match self {
            Self::Data(l) => l.nodes().range,
            Self::Pending(p) => p.range,
        }
    }

    /// The store ids of the nodes.
    #[must_use]
    pub fn ids(self) -> &'a [crate::astdata::NodeId] {
        match self {
            Self::Data(l) => &l.nodes().nodes,
            Self::Pending(p) => &p.nodes,
        }
    }

    /// The astdata `has_trailing_comma` bit.
    #[must_use]
    pub fn has_trailing_comma(self) -> bool {
        match self {
            Self::Data(l) => l.nodes().has_trailing_comma,
            Self::Pending(p) => p.has_trailing_comma,
        }
    }

    /// Go `modifiers.ModifierFlags` of a modifier list. Panics on a node
    /// list.
    #[must_use]
    pub fn modifier_flags(self) -> ModifierFlags {
        match self {
            Self::Data(l) => ModifierFlags(l.modifiers().flags.0),
            Self::Pending(p) => ModifierFlags(p.flags.expect("a pending modifier list").0),
        }
    }

    /// The address of the list, for Go pointer compares and keys
    /// (`NodeList::list_ptr`). It stays the same while the store lives.
    #[must_use]
    pub fn ptr(self) -> *const () {
        match self {
            Self::Data(l) => std::ptr::from_ref(l.nodes()).cast(),
            Self::Pending(p) => std::ptr::from_ref(p).cast(),
        }
    }

    /// The astdata list with the same range, ids and bit.
    #[must_use]
    pub fn to_ts(self) -> crate::astdata::NodeList {
        crate::astdata::NodeList {
            range: self.range(),
            nodes: self.ids().to_vec(),
            has_trailing_comma: self.has_trailing_comma(),
        }
    }

    /// The astdata modifier list with the same list and flags.
    #[must_use]
    pub fn to_ts_modifiers(self) -> crate::astdata::ModifierList {
        crate::astdata::ModifierList {
            list: self.to_ts(),
            flags: crate::astdata::ModifierFlags(self.modifier_flags().0),
        }
    }
}

/// `read` on list `list`, of a store that owns its nodes: a freeable file
/// version (pinned while `read` runs), an unpublished store of this thread
/// (borrowed while `read` runs, so `read` must not change that store), or
/// a static store whose freeable parse lost its version before the publish
/// (`FileStore::leak_owned_nodes`). Panics for a dead version.
#[inline]
pub fn with_store_list<R>(list: StoreList, read: impl FnOnce(StoreListView<'_>) -> R) -> R {
    let file = list.file();
    if super::file_version::is_hot(file) {
        return super::file_version::with_hot(|version| read(version.store.list_view(list)));
    }
    let mut read = Some(read);
    if let Some(result) = with_version_store(file, |version| {
        (read.take().expect("the list is read once"))(version.store.list_view(list))
    }) {
        return result;
    }
    let read = read.take().expect("the list is read once");
    with_store(file, |s| read(s.list_view(list)))
}

/// Go pointer equality of two lists of stores that own their nodes: the
/// same pending list, or the same list in the data of the same cell.
#[must_use]
pub fn same_store_list(a: StoreList, b: StoreList) -> bool {
    if a == b {
        return true;
    }
    a.file == b.file
        && a.key == b.key
        && a.sel_id() != PENDING_SEL
        && b.sel_id() != PENDING_SEL
        && with_store_list(a, |l| l.ptr()) == with_store_list(b, |l| l.ptr())
}

/// A new pending list of unpublished store `file`, which owns its nodes:
/// `range`, no nodes, and the astdata `has_trailing_comma` bit (parser
/// `createMissingList`, `NodeList::with_missing_marker`).
#[must_use]
pub fn new_store_missing_list(file: usize, range: crate::astdata::text::TextRange) -> StoreList {
    with_store_mut(file, |s| {
        s.owned_mut().push_pending(
            file,
            OwnedPending {
                range,
                nodes: Box::default(),
                has_trailing_comma: true,
                flags: None,
            },
        )
    })
}

/// The astdata node of a store slot, held apart from the store, so the
/// reader can make and change nodes of that store: a static node, an
/// owned cell with its chunk, or a node of a freeable file version with
/// its pin.
pub enum HeldStoreNode {
    Static(&'static crate::astdata::Node),
    Owned {
        chunk: OwnedChunk,
        index: usize,
    },
    Pinned {
        version: super::file_version::VersionPin,
        slot: usize,
    },
}

impl std::ops::Deref for HeldStoreNode {
    type Target = crate::astdata::Node;

    #[inline(always)]
    fn deref(&self) -> &crate::astdata::Node {
        match self {
            Self::Static(node) => *node,
            Self::Owned { chunk, index } => &chunk[*index],
            Self::Pinned { version, slot } => version
                .published()
                .expect("a pinned file version is published")
                .store
                .slot_ast_node(*slot),
        }
    }
}

/// What `static_store_node` found for a store node.
pub enum StaticNode {
    /// The node has `'static` data.
    Static(&'static crate::astdata::Node),
    /// The node has no `'static` data: a node of a freeable file version or
    /// an owned node of an unpublished store. Read it with
    /// `with_scoped_store_node` (lsshells M3c).
    Scoped,
    /// No store of this thread or of the registry has the node.
    NoStore,
}

/// The `'static` astdata node of non-nil store node `n`, or what keeps it
/// from one (`StaticNode`). The caller already missed the static tiers
/// (`frozen_store_ast_node`). Panics on a nil or alias slot.
// PERF: query Q8. The active store is checked first and inline, as in
// `try_store_ast_node`: the parse reads its own nodes here.
#[inline]
#[must_use]
pub fn static_store_node(n: Node) -> StaticNode {
    let (file, index) = (n.file_index(), slot_index(n));
    // A published store is never a build store. The static tiers missed,
    // so the hot version has no node column: it owns its nodes.
    if super::file_version::is_hot(file) {
        return StaticNode::Scoped;
    }
    if let Some(store) = active_store(file) {
        return store.borrow().static_node_of(index);
    }
    static_store_node_slow(file, index)
}

/// `static_store_node` for a node that is not in the active store.
// PERF: lsshells M3c. Inline: its callers are out of line already
// (`static_ast_node_slow`), and a node data read of the edited file comes
// here, so one call fewer per read.
#[inline]
fn static_store_node_slow(file: usize, index: usize) -> StaticNode {
    // A node shell has no node column (lsshells M3c), and a freeable file
    // version owns its nodes: the scoped read reads them.
    if FROZEN.get().is_some()
        && file < TIER1_LIMIT
        && later(file).is_some_and(|(f, _)| f.lacks_node_column())
    {
        return StaticNode::Scoped;
    }
    if let Some(node) = frozen!(file, nodes, |_, _, nodes| slot_node(nodes[index])) {
        return StaticNode::Static(node);
    }
    match unpublished_store(file) {
        Some(store) => store.borrow().static_node_of(index),
        None => StaticNode::NoStore,
    }
}

/// `read` on the astdata node of store node `n` when it has no `'static`
/// node (`StaticNode::Scoped`): a node of a freeable file version, pinned
/// while `read` runs, or an owned node of an unpublished store of this
/// thread, borrowed while `read` runs. `read` must not change the store of
/// `n` (a field read); `held_store_node` gives a node that a reader that
/// makes nodes can hold. Panics for a node with no store and for a dead
/// version.
// PERF: lsshells M3c. A pin hit is a thread-local borrow and a short scan
// (`with_file_version`), with no atomic write, as the binder data reads of
// the edited file (`Node::bind_field_slow`).
pub fn with_scoped_store_node<R>(n: Node, read: impl FnOnce(&crate::astdata::Node) -> R) -> R {
    let (file, index) = (n.file_index(), slot_index(n));
    if super::file_version::is_hot(file) {
        return super::file_version::with_hot(|version| read(version.store.slot_ast_node(index)));
    }
    let mut read = Some(read);
    if let Some(result) = with_version_store(file, |version| {
        (read.take().expect("the node is read once"))(version.store.slot_ast_node(index))
    }) {
        return result;
    }
    let read = read.take().expect("the node is read once");
    match unpublished_store(file) {
        Some(store) => read(store.borrow().slot_ast_node(index)),
        None => panic!("node {n:?} is not synthetic and has no store"),
    }
}

/// `read_ast_node_miss` for store node `n`, which is not a node of a static
/// tier: an unpublished store node (read in place; a node that the store
/// owns with the store borrowed while `read` runs), or a node of a live
/// freeable file version, pinned while `read` runs. Panics for a node with
/// no store and for a dead version.
// PERF: lsshells M3c. The active store first (the parse reads its own
// nodes, as `static_store_node`), then the version store: after the publish
// nearly every miss of a store node is a node of the edited file.
#[inline]
pub fn read_store_node_miss<R>(n: Node, read: impl FnOnce(&crate::astdata::Node) -> R) -> R {
    let (file, index) = (n.file_index(), slot_index(n));
    if super::file_version::is_hot(file) {
        return super::file_version::with_hot(|version| read(version.store.slot_ast_node(index)));
    }
    if let Some(store) = active_store(file) {
        let s = store.borrow();
        if s.cell_of(index) == NO_CELL {
            // A static node: no borrow while `read` runs, as before M3c.
            let node = slot_node(s.nodes[index]);
            drop(s);
            return read(node);
        }
        return read(s.slot_ast_node(index));
    }
    let mut read = Some(read);
    if let Some(result) = with_version_store(file, |version| {
        (read.take().expect("the node is read once"))(version.store.slot_ast_node(index))
    }) {
        return result;
    }
    let read = read.take().expect("the node is read once");
    match static_store_node_slow(file, index) {
        StaticNode::Static(node) => read(node),
        StaticNode::Scoped => match unpublished_store(file) {
            Some(store) => read(store.borrow().slot_ast_node(index)),
            None => panic!("node {n:?} is not synthetic and has no store"),
        },
        StaticNode::NoStore => panic!("node {n:?} is not synthetic and has no store"),
    }
}

/// True when `file` is the hot file version of this thread
/// (`ast::file_version::is_hot`, lsshells M3f).
#[inline(always)]
#[must_use]
pub fn is_hot_file(file: usize) -> bool {
    super::file_version::is_hot(file)
}

/// `read` on the `GoFile` of the hot file version (`is_hot_file`). `read`
/// runs inside the thread-local borrow: keep it small.
#[inline(always)]
pub fn with_hot_go_file<R>(read: impl FnOnce(&GoFile) -> R) -> R {
    super::file_version::with_hot(|version| read(&version.go_file))
}

/// True when store node `n` is a node of the hot file version of this
/// thread (`ast::file_version::is_hot`, lsshells M3f).
#[inline(always)]
#[must_use]
pub fn is_hot_store_node(n: Node) -> bool {
    super::file_version::is_hot(n.file_index())
}

/// `read` on the astdata node of node `n` of the hot file version
/// (`is_hot_store_node`). `read` can make nodes (of other stores: a
/// published store takes no new node).
#[inline(always)]
pub fn with_hot_store_node<R>(n: Node, read: impl FnOnce(&crate::astdata::Node) -> R) -> R {
    let index = slot_index(n);
    super::file_version::with_hot(|version| read(version.store.slot_ast_node(index)))
}

/// The astdata node of store node `n` held apart from its store
/// (`HeldStoreNode`), so the reader can make and change nodes of that
/// store. For a node with no `'static` node, as `with_scoped_store_node`.
#[must_use]
pub fn held_store_node(n: Node) -> HeldStoreNode {
    let (file, index) = (n.file_index(), slot_index(n));
    if let Some(version) = published_version(file) {
        return HeldStoreNode::Pinned {
            version,
            slot: index,
        };
    }
    // A held read inside a scoped read of the same store (a shared borrow)
    // cannot seal the open chunk, so it clones the node.
    match unpublished_store(file) {
        Some(store) => match store.try_borrow_mut() {
            Ok(mut s) => s.held_slot_node_mut(index),
            Err(_) => store.borrow().held_slot_node(index),
        },
        None => panic!("node {n:?} is not synthetic and has no store"),
    }
}

/// A list field that a list selector found in the data of a store node
/// with no `'static` node (`scoped_store_list_of`).
#[derive(Clone, Copy)]
pub enum ScopedList {
    /// The node is static after all (a shared name node, or a freeable
    /// file version whose parse was not freeable): a `'static` list.
    Static(AnyList<'static>),
    /// A list that the store owns.
    Store(StoreList),
}

/// Entries of `HOT_LISTS`.
const HOT_LIST_SLOTS: usize = 256;

/// One entry of `HOT_LISTS`: a node, a selector id and what
/// `scoped_store_list_of` gave for them.
#[derive(Clone, Copy)]
struct HotListEntry {
    node: Node,
    sel_id: u32,
    found: Option<Option<ScopedList>>,
}

thread_local! {
    /// The last `scoped_store_list_of` answers for nodes of hot file
    /// versions (`file_version::is_hot`), by node and selector id, direct
    /// mapped (lsshells M3f). A published version never changes and a file
    /// id is never reused, so an entry stays true; a node of a dead
    /// version is never hot, so its entries are not read.
    // PERF: the checker asks for the same lists of the edited file many
    // times (parameters, type parameters, members).
    static HOT_LISTS: RefCell<[HotListEntry; HOT_LIST_SLOTS]> = const {
        RefCell::new(
            [HotListEntry {
                node: Node::NIL,
                sel_id: 0,
                found: None,
            }; HOT_LIST_SLOTS],
        )
    };
}

/// `scoped_store_list_of` for node `n` of the hot version: the entry of
/// `HOT_LISTS`, or `pick` (the read), whose answer becomes the entry.
#[inline]
fn hot_list_of(
    n: Node,
    sel_id: u32,
    pick: impl FnOnce() -> Option<Option<ScopedList>>,
) -> Option<Option<ScopedList>> {
    let slot = ((n.0 ^ (u64::from(sel_id) << 44)).wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 56)
        as usize
        % HOT_LIST_SLOTS;
    let hit = HOT_LISTS
        .try_with(|lists| {
            let entry = lists.borrow()[slot];
            (entry.node == n && entry.sel_id == sel_id).then_some(entry.found)
        })
        .ok()
        .flatten();
    if let Some(found) = hit {
        return found;
    }
    let found = pick();
    let _ = HOT_LISTS.try_with(|lists| {
        if let Ok(mut lists) = lists.try_borrow_mut() {
            lists[slot] = HotListEntry {
                node: n,
                sel_id,
                found,
            };
        }
    });
    found
}

/// The list field that `sel` finds in the data of store node `n`, which
/// has no `'static` node (see `with_scoped_store_node`): `None` when the
/// data has no such field, `Some(None)` when the field is Go `nil`.
/// `sel_id` is the id of `sel` (`SelectorSite::id`).
// PERF: lsshells M3c. Inline in its two callers (`scoped_node_list_of`,
// `scoped_modifiers_of`), which are out of line.
#[inline]
#[must_use]
pub fn scoped_store_list_of(n: Node, sel_id: u32, sel: ListSel) -> Option<Option<ScopedList>> {
    let (file, index) = (n.file_index(), slot_index(n));
    let pick = |s: &FileStore| match s.cell_of(index) {
        NO_CELL => {
            let node: &'static crate::astdata::Node = slot_node(s.nodes[index]);
            sel(&node.data).map(|found| found.map(ScopedList::Static))
        }
        cell => sel(&s.owned_ref().node(cell).data).map(|found| {
            found.map(|list| {
                ScopedList::Store(StoreList::new(
                    file,
                    cell,
                    sel_id,
                    StoreListView::Data(list),
                ))
            })
        }),
    };
    if super::file_version::is_hot(file) {
        return hot_list_of(n, sel_id, || {
            super::file_version::with_hot(|version| pick(&version.store))
        });
    }
    if let Some(found) = with_version_store(file, |version| pick(&version.store)) {
        return found;
    }
    match unpublished_store(file) {
        Some(store) => pick(&store.borrow()),
        None => panic!("node {n:?} is not synthetic and has no store"),
    }
}

impl FileStore {
    /// The owned cell of slot `index`, `NO_CELL` for a static store.
    #[inline]
    fn cell_of(&self, index: usize) -> u32 {
        self.owned
            .as_deref()
            .map_or(NO_CELL, |owned| owned.cell_of[index])
    }

    /// The owned part of a store that owns its nodes. Panics for a static
    /// store.
    fn owned_ref(&self) -> &OwnedAst {
        self.owned
            .as_deref()
            .expect("a store that owns its nodes (a freeable parse)")
    }

    /// `owned_ref` for a write.
    fn owned_mut(&mut self) -> &mut OwnedAst {
        self.owned
            .as_deref_mut()
            .expect("a store that owns its nodes (a freeable parse)")
    }

    /// The astdata node of node slot `index`: the node that the store owns
    /// or its static node. Panics on the nil slot and alias slots.
    #[inline(always)]
    fn slot_ast_node(&self, index: usize) -> &crate::astdata::Node {
        match self.cell_of(index) {
            NO_CELL => slot_node(self.nodes[index]),
            cell => self.owned_ref().node(cell),
        }
    }

    /// `slot_ast_node` as `StaticNode`: `Scoped` for a node that the store
    /// owns.
    #[inline]
    fn static_node_of(&self, index: usize) -> StaticNode {
        match self.cell_of(index) {
            NO_CELL => StaticNode::Static(slot_node(self.nodes[index])),
            _ => StaticNode::Scoped,
        }
    }

    /// `slot_ast_node`, held apart from the store borrow. A node of the
    /// open chunk is cloned: this borrow is shared (see `held_store_node`).
    fn held_slot_node(&self, index: usize) -> HeldStoreNode {
        match self.cell_of(index) {
            NO_CELL => HeldStoreNode::Static(slot_node(self.nodes[index])),
            cell => {
                let owned = self.owned_ref();
                owned.held(cell).unwrap_or_else(|| HeldStoreNode::Owned {
                    chunk: Arc::new(vec![owned.node(cell).clone()]),
                    index: 0,
                })
            }
        }
    }

    /// `held_slot_node` with the store borrowed for a write: a node of the
    /// open chunk seals it.
    fn held_slot_node_mut(&mut self, index: usize) -> HeldStoreNode {
        match self.cell_of(index) {
            NO_CELL => HeldStoreNode::Static(slot_node(self.nodes[index])),
            cell => self.owned_mut().held_mut(cell),
        }
    }

    /// The astdata node of each slot, `None` for the nil slot and alias
    /// slots (`slot_ast_node`).
    fn slot_nodes(&self) -> impl Iterator<Item = Option<&crate::astdata::Node>> + '_ {
        (0..self.nodes.len()).map(|i| self.nodes[i].map(|_| self.slot_ast_node(i)))
    }

    /// The list that `list` names in this store (`with_store_list`).
    #[inline]
    fn list_view(&self, list: StoreList) -> StoreListView<'_> {
        let owned = self.owned_ref();
        if list.sel_id() == PENDING_SEL {
            return StoreListView::Pending(&owned.pending[list.key as usize]);
        }
        match list_selector(list.sel_id())(&owned.node(list.key).data) {
            Some(Some(found)) => StoreListView::Data(found),
            _ => panic!("a store list handle names a list that its node data does not have"),
        }
    }

    /// Adds the `cell_of` entry of a new slot with no owned node, in a
    /// store that owns its nodes.
    #[inline]
    fn push_no_cell(&mut self) {
        if let Some(owned) = self.owned.as_deref_mut() {
            owned.cell_of.push(NO_CELL);
        }
    }

    /// A static publish of a store that owns its nodes (a freeable parse
    /// whose `FileVersion` died before the publish): its nodes are leaked
    /// and its node column names them, so the static reads find them. The
    /// owned part stays, for the list handles that name it.
    fn leak_owned_nodes(&mut self) {
        let Some(owned) = self.owned.as_deref() else {
            return;
        };
        let flat: &'static OwnedChunk = Box::leak(Box::new(Arc::clone(&owned.flat)));
        for (slot, &cell) in owned.cell_of.iter().enumerate() {
            if cell != NO_CELL {
                self.nodes[slot] = Some(&flat[cell as usize]);
            }
        }
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

/// The `GoFile` of published file `file` (tier 0, tier 1 or a freeable
/// file version). Panics when it is not published, and for a dead file
/// version. The guard pins a freeable version while it lives; hot readers
/// use `with_go_file`, which pins nothing past the read.
#[inline]
#[must_use]
pub fn go_file(file: usize) -> FileRef<GoFile> {
    match try_go_file(file) {
        Some(go_file) => go_file,
        None => not_published(file),
    }
}

#[cold]
#[inline(never)]
fn not_published(file: usize) -> ! {
    panic!("file {file} is not published")
}

/// `go_file`, or `None` for a store still being built, a synthetic id or
/// an unknown id.
#[inline]
#[must_use]
pub fn try_go_file(file: usize) -> Option<FileRef<GoFile>> {
    if let Some(go_file) = static_go_file(file) {
        return Some(FileRef::Static(go_file));
    }
    let version = published_version(file)?;
    Some(FileRef::Pinned {
        version,
        key: 0,
        get: |version, _| version.go_file(),
    })
}

/// The `GoFile` of file `file` when it is in a static publish (tier 0 or
/// tier 1). `None` for any other file, a freeable file version included.
/// Hot readers use it inline and read any other file out of line.
#[inline]
#[must_use]
pub fn static_go_file(file: usize) -> Option<&'static GoFile> {
    static_frozen(file, |f| f.go_files)
}

/// Runs `f` on the `GoFile` of published file `file`, or gives `None` as
/// `try_go_file`. It pins a freeable version only while `f` runs, so it
/// costs no guard: hot readers (`Node::bind`) use it.
#[inline]
pub fn try_with_go_file<R>(file: usize, f: impl FnOnce(&GoFile) -> R) -> Option<R> {
    if let Some(go_file) = static_go_file(file) {
        return Some(f(go_file));
    }
    try_with_go_file_slow(file, f)
}

/// `try_with_go_file` after the static tiers missed: the hot file version
/// with no `Frozen` view (lsshells M3f), else the registry read.
#[cold]
#[inline(never)]
fn try_with_go_file_slow<R>(file: usize, f: impl FnOnce(&GoFile) -> R) -> Option<R> {
    if super::file_version::is_hot(file) {
        return Some(super::file_version::with_hot(|version| f(&version.go_file)));
    }
    frozen!(file, go_files, |_, _, go_file| f(go_file))
}

/// `try_with_go_file`, which panics as `go_file` when `file` is not
/// published.
#[inline]
pub fn with_go_file<R>(file: usize, f: impl FnOnce(&GoFile) -> R) -> R {
    match try_with_go_file(file, f) {
        Some(result) => result,
        None => not_published(file),
    }
}

/// True when `file` has a `GoFile` in the registry (tier 0, tier 1 or a
/// freeable file version).
#[inline]
#[must_use]
pub fn is_published(file: usize) -> bool {
    try_with_go_file(file, |_| ()).is_some()
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
    frozen!(file, headers, |_, _, _| ()).is_some() || unpublished_store(file).is_some()
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
// `GoFile::info.jsdoc_cache` after the program is installed. A store that
// owns its nodes (a freeable parse, lsshells M3c) keeps them instead.
pub fn set_file_store_js_doc_cache(file: usize, cache: &FxHashMap<Node, Vec<Node>>) {
    with_store_mut(file, |s| match s.owned.as_deref_mut() {
        Some(owned) => {
            owned.jsdoc = cache
                .iter()
                .map(|(node, jsdocs)| (*node, jsdocs.clone().into_boxed_slice()))
                .collect();
        }
        None => {
            s.jsdoc_cache = cache
                .iter()
                .map(|(node, jsdocs)| (*node, &*Box::leak(jsdocs.clone().into_boxed_slice())))
                .collect();
        }
    });
}

/// Go `result.LanguageVariant` and `result.diagnostics` in
/// `finishSourceFile`, and `ContainsNonASCII`, which Go `NewSourceFile` sets
/// from the text (`ParsedSourceFile::new`).
// PORT: the diagnostics are leaked so reads can return a `&'static` slice,
// like `GoFile::info.diagnostics` after the publish. A parse without errors
// leaks nothing. A store that owns its nodes (a freeable parse, lsshells
// M3c) keeps them instead.
pub fn set_file_store_parse_fields(
    file: usize,
    language_variant: LanguageVariant,
    diagnostics: &[Diagnostic],
    contains_non_ascii: bool,
) {
    with_store_mut(file, |s| {
        s.language_variant = language_variant;
        match s.owned.as_deref_mut() {
            Some(owned) => owned.diagnostics = diagnostics.into(),
            None => s.diagnostics = Box::leak(diagnostics.to_vec().into_boxed_slice()),
        }
        s.contains_non_ascii = contains_non_ascii;
    });
}

/// Go `file.LanguageVariant` of a store file.
#[must_use]
pub fn file_store_language_variant(file: usize) -> LanguageVariant {
    with_store(file, |s| s.language_variant)
}

/// Go `file.Diagnostics()` (the parse diagnostics) of a store file.
// PORT: a store that owns its nodes (lsshells M3c) keeps its diagnostics,
// so this read leaks a copy. Only a read before the publish comes here
// (`source_file_diagnostics`), and the language server makes none.
#[must_use]
pub fn file_store_diagnostics(file: usize) -> &'static [Diagnostic] {
    with_store(file, |s| match s.owned.as_deref() {
        Some(owned) if !owned.diagnostics.is_empty() => &*Box::leak(owned.diagnostics.clone()),
        _ => s.diagnostics,
    })
}

/// Go `file.ContainsNonASCII` of a store file: true when the text has a
/// byte >= 0x80. False for a store that `finishSourceFile` did not finish.
#[must_use]
pub fn file_store_contains_non_ascii(file: usize) -> bool {
    with_store(file, |s| s.contains_non_ascii)
}

/// Go `file.jsdocCache[node]` of a store file whose program is not
/// installed yet. It never parses (Go `EagerJSDoc`). The list of a store
/// that owns its nodes (lsshells M3c) is read at each use
/// (`NodeSlice::from_file_js_doc`).
#[must_use]
pub fn file_store_js_doc(file: usize, node: Node) -> Option<NodeSlice> {
    let found = with_store(file, |s| match s.owned.as_deref() {
        Some(owned) => owned.jsdoc.contains_key(&node).then_some(None),
        None => s
            .jsdoc_cache
            .get(&node)
            .or_else(|| s.lazy_jsdoc_cache.get(&node))
            .map(|&jsdocs| Some(jsdocs)),
    })?;
    // The slice of an owned list reads the store, so it is made after the
    // borrow ends.
    Some(match found {
        Some(jsdocs) => NodeSlice::from_nodes(jsdocs),
        None => NodeSlice::from_file_js_doc(file, node),
    })
}

/// `read` on the JSDoc cache entry of `node` in unpublished store `file`,
/// which owns its nodes (lsshells M3c; `file_store_js_doc`). `None` when
/// `file` is no such store or the entry is missing.
pub fn with_owned_store_js_doc<R>(
    file: usize,
    node: Node,
    read: impl FnOnce(&[Node]) -> R,
) -> Option<R> {
    try_with_store(file, |s| {
        s.owned
            .as_deref()
            .and_then(|owned| owned.jsdoc.get(&node))
            .map(|jsdocs| read(&jsdocs[..]))
    })
    .flatten()
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
// The lists are leaked so reads can return `&'static` slices; a store that
// owns its nodes keeps them (lsshells M3c).
#[must_use]
pub fn resolve_file_store_js_doc(file: usize, node: Node) -> Option<NodeSlice> {
    if let Some(jsdocs) = file_store_js_doc(file, node) {
        return Some(jsdocs);
    }
    let (parse_options, script_kind, text) = with_store(file, |s| {
        s.lazy_js_doc
            .clone()
            .map(|(parse_options, script_kind)| (parse_options, script_kind, s.text))
    })?;
    let jsdocs =
        crate::frontend::parser::parse_js_doc_for_node(&parse_options, text, script_kind, node);
    let leaked = with_store_mut(file, |s| match s.owned.as_deref_mut() {
        Some(owned) => {
            owned.jsdoc.insert(node, jsdocs.into_boxed_slice());
            None
        }
        None => {
            let jsdocs: &'static [Node] = Box::leak(jsdocs.into_boxed_slice());
            s.lazy_jsdoc_cache.insert(node, jsdocs);
            Some(jsdocs)
        }
    });
    // The slice of an owned list reads the store, so it is made after the
    // borrow ends.
    Some(match leaked {
        Some(jsdocs) => NodeSlice::from_nodes(jsdocs),
        None => NodeSlice::from_file_js_doc(file, node),
    })
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
        let slots = self
            .kinds
            .iter()
            .zip(self.slot_nodes())
            .zip(&self.children[..]);
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
        let slots = self.kinds.iter().zip(self.slot_nodes()).zip(&self.headers);
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
        for (&kind, node) in self.kinds.iter().zip(self.slot_nodes()) {
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
        if let Some(owned) = self.owned.as_deref_mut() {
            owned.cell_of.shrink_to_fit();
            owned.pending.shrink_to_fit();
            owned.count_owned_nodes();
            owned.finish();
        }
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
        // lsshells M3c: the `GoFile` holds the JSDoc cache and the
        // diagnostics of the file from now on.
        if let Some(owned) = self.owned.as_deref_mut() {
            owned.jsdoc = FxHashMap::default();
            owned.diagnostics = Box::default();
        }
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
    // A freeable file version keeps its headers in its node shell.
    frozen!(file, headers, |_, _, headers| headers.len())
        .unwrap_or_else(|| with_store(file, |s| s.headers.len()))
}

/// The parser `node.Flags` of every slot, indexed by slot index. Nil and
/// alias slots give no flags. The loader fills `GoFile::parser_flags` from
/// this for the binder.
#[must_use]
pub fn file_store_parser_flags(file: usize) -> Vec<NodeFlags> {
    // A freeable file version keeps its headers in its node shell.
    if let Some(flags) = frozen!(file, headers, |_, _, headers| headers
        .iter()
        .map(|h| h.flags)
        .collect())
    {
        return flags;
    }
    let computed = |s: &FileStore| s.headers.iter().map(|h| h.flags).collect();
    with_store_mut(file, |s| {
        s.parser_flags.take().unwrap_or_else(|| computed(s))
    })
}

/// Publishes the build stores of this thread: `go_files[i]` is the
/// `GoFile` of id `unpublished_file_ids().start + i`. The loader calls this
/// once per program, before `core::set_prog`. The stores are then
/// read-only, and any thread can read them. The first publish is tier 0;
/// later ones go to tier 1. A freeable file version (lsshells M3b) owns its
/// store and `GoFile`, and its tier 1 slot names its node shell
/// (`node_shell`). An empty later publish does nothing.
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
    assert!(
        go_files.len() == cells.len(),
        "a publish needs one GoFile per store ({} stores, {} GoFiles)",
        cells.len(),
        go_files.len()
    );
    let tier0 = FROZEN.get();
    if tier0.is_some() && go_files.is_empty() {
        return;
    }
    let count = cells.len();
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
    if tier0.is_none() {
        assert_eq!(base, 0, "the first publish must start at file id 0");
        assert!(
            FROZEN.set(leaked_frozen(base, stores, go_files)).is_ok(),
            "another thread made the first publish"
        );
        return;
    }
    // lsshells M3b: a freeable file version (a live `FileVersion` of the
    // id, made by the language server parse cache) takes its store and
    // `GoFile`, and its tier 1 slot names its node shell. The other files
    // go to tier 1 in runs of consecutive ids, one leaked `Frozen` per run.
    let versions: FxHashMap<usize, std::sync::Arc<super::FileVersion>> =
        super::file_version::live_file_versions(base..base + count)
            .into_iter()
            .map(|version| (version.file(), version))
            .collect();
    if versions.is_empty() {
        publish_later(leaked_frozen(base, stores, go_files));
        return;
    }
    let mut run_start = base;
    let mut run_stores = Vec::new();
    let mut run_files = Vec::new();
    for (i, (store, go_file)) in stores.into_iter().zip(go_files).enumerate() {
        let file = base + i;
        let Some(version) = versions.get(&file) else {
            run_stores.push(store);
            run_files.push(go_file);
            continue;
        };
        if !run_stores.is_empty() {
            publish_later(leaked_frozen(
                run_start,
                std::mem::take(&mut run_stores),
                std::mem::take(&mut run_files),
            ));
        }
        run_start = file + 1;
        let mut store = store;
        let shell = node_shell(file, &mut store);
        version.set_published(VersionStore {
            file,
            store,
            go_file,
            shell,
        });
        set_later_slot(file, shell);
    }
    if !run_stores.is_empty() {
        publish_later(leaked_frozen(run_start, run_stores, run_files));
    }
}

/// The leaked `Frozen` of the published `stores` and `go_files`, whose first
/// file id is `base` (tier 0 or one tier 1 publish).
// PERF: query Q7. The per-store tables are made already, so this only
// collects slices.
fn leaked_frozen(
    base: usize,
    mut stores: Vec<FileStore>,
    go_files: Vec<GoFile>,
) -> Frozen<'static> {
    // lsshells M3c: a freeable parse whose version died before the publish
    // is published static, so its nodes are leaked now.
    for store in &mut stores {
        store.leak_owned_nodes();
    }
    let stores: &'static [FileStore] = Box::leak(stores.into_boxed_slice());
    Frozen {
        base,
        stores,
        headers: Box::leak(stores.iter().map(|s| &s.headers[..]).collect::<Box<[_]>>()),
        nodes: Box::leak(stores.iter().map(|s| &s.nodes[..]).collect::<Box<[_]>>()),
        kinds: Box::leak(stores.iter().map(|s| &s.kinds[..]).collect::<Box<[_]>>()),
        names: Box::leak(stores.iter().map(|s| &s.names[..]).collect::<Box<[_]>>()),
        modifier_bits: Box::leak(
            stores
                .iter()
                .map(|s| &s.modifier_bits[..])
                .collect::<Box<[_]>>(),
        ),
        per_store: Box::leak(
            stores
                .iter()
                .enumerate()
                .map(|(i, s)| {
                    let nil = resolve_slot(base + i, NIL_SLOT as usize, &s.nodes, &s.headers);
                    FrozenStore::of(s, nil)
                })
                .collect::<Box<[_]>>(),
        ),
        go_files: Box::leak(go_files.into_boxed_slice()),
    }
}

/// Leaks tier 1 publish `frozen` and points the tier 1 slot of each of its
/// file ids at it.
fn publish_later(frozen: Frozen<'static>) {
    let count = frozen.stores.len();
    let frozen: &'static Frozen<'static> = Box::leak(Box::new(frozen));
    for file in frozen.base..frozen.base + count {
        set_later_slot(file, frozen);
    }
}

/// Points the tier 1 slot of `file` at `frozen`.
fn set_later_slot(file: usize, frozen: &'static Frozen<'static>) {
    let chunk = LATER[file / LATER_CHUNK]
        .get_or_init(|| Box::new([const { OnceLock::new() }; LATER_CHUNK]));
    assert!(
        chunk[file % LATER_CHUNK].set(frozen).is_ok(),
        "file {file} is already published"
    );
}

/// The node shell of freeable file version `file`, whose store is `store`:
/// a leaked one-file tier 1 publish with the node columns of the store
/// (headers, kinds, names, modifier bits, children and the resolved table),
/// moved out of `store`. It has no store, no `GoFile` and no child link
/// column. A store that owns its astdata nodes (lsshells M3c) keeps its
/// node column and its nodes, and the shell has none
/// (`Frozen::lacks_node_column`), so a node data read misses the shell and
/// reads the version (`static_store_node`, `StaticNode::Scoped`); a store
/// with leaked nodes moves its node column into the shell.
/// The binder's child walk (`frozen_store_children`) reads the node data:
/// the link column is dropped here. Every read of the store or the `GoFile`
/// misses the shell and reads the version (`StaticMiss::MaybeFreeable`).
/// The caller points the tier 1 slot of `file` at it after the version is
/// published.
// PERF: lsshells M3 repair. A pinned read of the version (a thread-local
// pin lookup) for each node read of the edited file made query-core and
// effect edits 3 to 4 ms slower than R134 (lsshells/m3/final/editor-off),
// and 1.5 to 2 ms with only the kind column static
// (lsshells/m3/repair/prof): an edit reads the nodes of the edited file
// about 400,000 times. The node columns that the header and child reads
// need (44 bytes per node) are leaked and read inline, as a tier 1 file.
// Without the children and modifier columns, the child reads of the edited
// file read the node data, and edits were about 0.3 ms slower
// (lsshells/m3/repair/r4). The store maps and lists, the node column, the
// astdata nodes, the link column and the `GoFile` (binder and flow data,
// parse lists) are freed with the version. A stale read of a leaked column
// gives the data of that node (ids are never reused); a stale node data
// read panics.
fn node_shell(file: usize, store: &mut FileStore) -> &'static Frozen<'static> {
    let nil = resolve_slot(file, NIL_SLOT as usize, &store.nodes, &store.headers);
    // lsshells M3c: a store that owns its nodes keeps its node column. A
    // store with leaked nodes (a prefetched parse, or owned nodes off)
    // leaks it here, as before M3c, so its node data reads stay inline.
    let nodes: &'static [&'static [Option<&'static crate::astdata::Node>]] =
        if store.owned.is_some() {
            &[]
        } else {
            let nodes: &'static [Option<&'static crate::astdata::Node>] =
                Vec::leak(std::mem::take(&mut store.nodes));
            Box::leak(Box::new([nodes]))
        };
    let headers: &'static [NodeHeader] = Vec::leak(std::mem::take(&mut store.headers));
    let kinds: &'static [SyntaxKind] = Box::leak(std::mem::take(&mut store.kinds));
    let names: &'static [Name] = Box::leak(std::mem::take(&mut store.names));
    let resolved: &'static [Node] = Box::leak(std::mem::take(&mut store.resolved));
    let modifier_bits: &'static [u16] = Box::leak(std::mem::take(&mut store.modifier_bits));
    let children: &'static [SlotChildren] = Box::leak(std::mem::take(&mut store.children));
    store.links = Box::default();
    let per_store = FrozenStore {
        resolved,
        nil,
        facts: store.facts,
        children,
        links: &[],
        root: store.root,
    };
    Box::leak(Box::new(Frozen {
        base: file,
        stores: &[],
        headers: Box::leak(Box::new([headers])),
        nodes,
        kinds: Box::leak(Box::new([kinds])),
        names: Box::leak(Box::new([names])),
        modifier_bits: Box::leak(Box::new([modifier_bits])),
        per_store: Box::leak(Box::new([per_store])),
        go_files: &[],
    }))
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
pub fn resolve_store_id(file: usize, id: crate::astdata::NodeId) -> Node {
    let index = id.index();
    // The nil slot or an alias slot: the target is in the header
    // (`resolve_slot`).
    if let Some(n) = frozen_static!(file, nodes, |f, local, nodes| resolve_slot(
        file,
        index,
        nodes,
        f.headers[local]
    )) {
        return n;
    }
    // A node shell has no node column (lsshells M3c): its resolved table.
    if let Some(n) = frozen_resolve_store_id(file, id) {
        return n;
    }
    with_store(file, |s| resolve_slot(file, index, &s.nodes, &s.headers))
}

/// Hook for `raw(n)`: the astdata node (Go kind and data) of a store node.
/// Panics for a node with no `'static` data (a node that a freeable parse
/// owns, lsshells M3c): read it with `ast::with_ast_node`.
#[inline]
#[must_use]
pub fn store_ast_node(n: Node) -> &'static crate::astdata::Node {
    if let Some(node) = frozen_static!(n.file_index(), nodes, |_, _, nodes| slot_node(
        nodes[slot_index(n)]
    )) {
        return node;
    }
    match static_store_node(n) {
        StaticNode::Static(node) => node,
        StaticNode::Scoped => {
            panic!("node {n:?} is owned by a freeable parse and has no 'static data")
        }
        StaticNode::NoStore => panic!(
            "file {:#x} has no node store on this thread",
            n.file_index()
        ),
    }
}

/// Hook for `Node::kind`, `flags`, `parent` and `loc` on a store node.
#[inline]
#[must_use]
pub fn store_header(n: Node) -> NodeHeader {
    let (file, index) = (n.file_index(), slot_index(n));
    if let Some(header) = frozen_static!(file, headers, |f, local, headers| {
        // A node shell has no node column (lsshells M3c).
        debug_assert!(
            f.nodes
                .get(local)
                .is_none_or(|nodes| nodes[index].is_some()),
            "store handle does not name a node slot"
        );
        headers[index].read(file)
    }) {
        return header;
    }
    with_store(file, |s| {
        debug_assert!(
            s.nodes[index].is_some(),
            "store handle does not name a node slot"
        );
        s.headers[index].read(file)
    })
}

/// The header of `n` when it is a store node (kind, parser flags, parent,
/// loc): one thread-local load for the active store, one table lookup in
/// the registry (`frozen!`), one more thread-local access for another
/// unpublished store. `None` for nil and synthetic nodes. With it a
/// node read needs no separate `has_file_store` call.
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
    if let Some(header) = frozen!(file, headers, |_, _, headers| headers[index].read(file)) {
        return Some(header);
    }
    unpublished_store(file).map(|store| store.borrow().headers[index].read(file))
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

/// Go `node.Kind` of a published store node (tier 0 or tier 1, see
/// `frozen_static!`; tier 1 has the node shell of a freeable file version).
/// `None` for any other node: nil, synthetic and unpublished store nodes.
#[inline]
#[must_use]
pub fn frozen_store_kind(n: Node) -> Option<SyntaxKind> {
    if n.is_nil() {
        return None;
    }
    frozen_static!(n.file_index(), kinds, |_, _, kinds| kinds[slot_index(n)])
}

/// The header of a node of a static publish, by reference, so a read of
/// one field does not copy the whole header. The parent is still in its
/// stored form (see `LOCAL_STORE`). `None` as for `frozen_store_kind`.
// PERF: lsshells M3 repair. Not generic over the read, as in R134: a
// generic `frozen_header<R>` was out of line in 21 copies, and `goport -p`
// ran more instructions in the header reads.
#[inline]
fn frozen_header(n: Node) -> Option<&'static NodeHeader> {
    if n.is_nil() {
        return None;
    }
    frozen_static!(n.file_index(), headers, |_, _, headers| &headers
        [slot_index(n)])
}

/// Parser `node.Flags` of a published store node (see `frozen_header`).
#[inline]
#[must_use]
pub fn frozen_store_flags(n: Node) -> Option<NodeFlags> {
    frozen_header(n).map(|h| h.flags)
}

/// Go `node.Loc` of a published store node (see `frozen_header`).
#[inline]
#[must_use]
pub fn frozen_store_loc(n: Node) -> Option<TextRange> {
    frozen_header(n).map(|h| h.loc)
}

/// Go `node.Parent` of a published store node (see `frozen_header`).
#[inline]
#[must_use]
pub fn frozen_store_parent(n: Node) -> Option<Node> {
    frozen_header(n).map(|h| h.read(n.file_index()).parent)
}

/// The astdata node of a published store node: the inlined fast path of
/// `static_ast_node`. `None` as for `frozen_store_kind`. Panics like
/// `try_store_ast_node` on a nil or alias slot.
#[inline]
#[must_use]
pub fn frozen_store_ast_node(n: Node) -> Option<&'static crate::astdata::Node> {
    if n.is_nil() {
        return None;
    }
    frozen_static!(n.file_index(), nodes, |_, _, nodes| nodes[slot_index(n)]
        .expect("store handle does not name a node slot"))
}

/// `store_ast_node(n)` when `n` is a store node, in one lookup (see
/// `try_store_header`). `None` for nil and synthetic nodes, and for a node
/// with no `'static` data (a node that a freeable parse owns, lsshells M3c;
/// `static_store_node` tells them apart).
#[inline]
#[must_use]
pub fn try_store_ast_node(n: Node) -> Option<&'static crate::astdata::Node> {
    if n.is_nil() {
        return None;
    }
    match static_store_node(n) {
        StaticNode::Static(node) => Some(node),
        StaticNode::Scoped | StaticNode::NoStore => None,
    }
}

/// The astdata node of a node slot. Panics on the nil slot and alias slots.
#[inline]
fn slot_node(slot: Option<&'static crate::astdata::Node>) -> &'static crate::astdata::Node {
    slot.expect("store handle does not name a node slot")
}

/// `resolve_store_id(file, id)` when `file` has a store, in one lookup (see
/// `try_store_header`). `None` when it has none.
#[inline]
#[must_use]
pub fn try_resolve_store_id(file: usize, id: crate::astdata::NodeId) -> Option<Node> {
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
    if let Some(n) = frozen!(file, per_store, |f, _, s| frozen_resolve_slot(
        f, s, file, index
    )) {
        return Some(n);
    }
    unpublished_store(file).map(|store| {
        let s = store.borrow();
        resolve_slot(file, index, &s.nodes, &s.headers)
    })
}

/// The text in the data of an Identifier or PrivateIdentifier node. Empty
/// for a store node made by `alloc_store_name_node` or
/// `alloc_store_shared_name_node` (see `store_identifier_name`) and for
/// other kinds.
fn identifier_text(node: &crate::astdata::Node) -> &str {
    match &node.data {
        NodeData::Identifier(d) => &d.text,
        NodeData::PrivateIdentifier(d) => &d.text,
        _ => "",
    }
}

/// U1 (d): Go `node.Text()` of an Identifier or PrivateIdentifier store
/// node, from the name column of its slot (`FileStore::names`, or
/// `build_names` while the file is parsed), in tier 0, tier 1 (with the
/// node shell of a freeable file version) or an unpublished store of this
/// thread. `None` for nil and synthetic nodes. `Name::default()` (the empty
/// text) for other slots.
#[inline]
#[must_use]
pub fn store_identifier_name(n: Node) -> Option<Name> {
    if n.is_nil() {
        return None;
    }
    let (file, index) = (n.file_index(), slot_index(n));
    if let Some(name) = frozen_static!(file, names, |_, _, names| names[index].clone()) {
        return Some(name);
    }
    store_identifier_name_slow(file, index)
}

/// `store_identifier_name` for a node that is not published: an
/// unpublished (built or detached) store of this thread.
// PORT: the name column is the only copy of the text, so every store that
// a thread can read must answer, not only the published ones.
#[inline(never)]
fn store_identifier_name_slow(file: usize, index: usize) -> Option<Name> {
    if let Some(name) = frozen!(file, names, |_, _, names| names[index].clone()) {
        return Some(name);
    }
    unpublished_store(file).map(|store| {
        let s = store.borrow();
        // A finished file has moved `build_names` into `names`.
        let names = if s.names.len() == s.headers.len() {
            &s.names[..]
        } else {
            &s.build_names[..]
        };
        names[index].clone()
    })
}

/// The node for slot `index` of store `file`: the slot itself when it holds
/// a node, else the handle stored in its header.
fn resolve_slot(
    file: usize,
    index: usize,
    nodes: &[Option<&'static crate::astdata::Node>],
    headers: &[NodeHeader],
) -> Node {
    match nodes[index] {
        Some(_) => handle(file, index as u32),
        None => headers[index].parent,
    }
}

/// `try_resolve_store_id(file, _)` for every slot of published store
/// `file` (tier 0 or tier 1), indexed by `NodeId::index()`. `None` for any
/// other file and for an alias-free store, which has no table (`Node::new`
/// resolves its ids without one). On `None` the caller resolves each id.
#[inline]
#[must_use]
pub fn frozen_resolved(file: usize) -> Option<&'static [Node]> {
    let s = static_frozen(file, |f| f.per_store)?;
    (!s.facts.alias_free).then_some(s.resolved)
}

/// Hook for `Node::new(file, id)` on a published store (tier 0 or tier 1):
/// `try_resolve_store_id(file, id)` without a per-slot table load for an
/// alias-free store. `None` for any other file (unpublished or
/// synthetic).
#[inline]
#[must_use]
pub fn frozen_resolve_store_id(file: usize, id: crate::astdata::NodeId) -> Option<Node> {
    frozen_static!(file, per_store, |f, _, s| frozen_resolve_slot(
        f,
        s,
        file,
        id.index()
    ))
}

/// The `StoreFacts` of published store `file` (tier 0 or tier 1). `None`
/// for any other file.
#[inline]
#[must_use]
pub fn frozen_store_facts(file: usize) -> Option<StoreFacts> {
    frozen_static!(file, per_store, |_, _, s| s.facts)
}

/// The `StoreFacts` of the store of `n` when it is a published store node.
/// `None` for any other node: nil, synthetic and unpublished store
/// nodes.
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
/// store or a file without a store. A freeable file version keeps it in its
/// store, so the guard pins the version.
#[must_use]
pub fn frozen_file_ecma_line_starts(file: usize) -> Option<FileRef<[i32]>> {
    if let Some(store) = static_frozen(file, |f| f.stores) {
        return Some(FileRef::Static(line_starts(store)));
    }
    let version = published_version(file)?;
    Some(FileRef::Pinned {
        version,
        key: 0,
        get: |version, _| {
            let store = version
                .published()
                .expect("a pinned file version is published");
            line_starts(&store.store)
        },
    })
}

/// The ECMA line map of published store `file` (see
/// `frozen_file_ecma_line_starts`), made once.
fn line_starts(store: &FileStore) -> &[i32] {
    store.ecma_line_starts.get_or_init(|| {
        crate::scanner_util::compute_ecma_line_starts(store.text).into_boxed_slice()
    })
}

/// `read` on the ECMA line map of published store `file`, with no guard: a
/// freeable file version is pinned only while `read` runs. `None` as for
/// `frozen_file_ecma_line_starts`, and then `read` did not run.
#[inline]
pub fn with_frozen_file_ecma_line_starts<R>(
    file: usize,
    read: impl FnOnce(&[i32]) -> R,
) -> Option<R> {
    let mut read = Some(read);
    frozen!(file, stores, |_, _, store| (read
        .take()
        .expect("the line map is read once"))(
        line_starts(store)
    ))
}

/// Go `GetSourceFileOfNode(n)` in O(1), when `n` is a published store node
/// whose parent walk ends at its store root. `None` means "walk".
#[inline]
#[must_use]
pub fn frozen_source_file_of_node(n: Node) -> Option<Node> {
    if n.is_nil() {
        return None;
    }
    frozen_static!(n.file_index(), headers, |f, local, headers| headers
        [slot_index(n)]
    .source_file_is_root
    .then(|| f.per_store[local].root))
    .flatten()
}

/// U1 (a): Go `node.Text()` of a published Identifier or PrivateIdentifier
/// store node (tier 0 or tier 1), interned when its slot was made
/// (`FileStore::names`). `None` for other kinds and for any other node:
/// nil, synthetic and unpublished store nodes.
#[inline]
#[must_use]
pub fn frozen_store_text_name(n: Node) -> Option<Name> {
    if n.is_nil() {
        return None;
    }
    let index = slot_index(n);
    frozen_static!(
        n.file_index(),
        kinds,
        |f, local, kinds| match kinds[index] {
            SyntaxKind::Identifier | SyntaxKind::PrivateIdentifier => {
                Some(f.names[local][index].clone())
            }
            _ => None,
        }
    )
    .flatten()
}

/// U1 (a): Go `scanner.GetIdentifierToken(node.Text()) != KindIdentifier` of
/// a published Identifier or PrivateIdentifier store node, from its header.
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
/// list) of a published store node (tier 0 or tier 1), from
/// `FileStore::modifier_bits`. `None` for a store whose column is empty and
/// for any other node: nil, synthetic and unpublished store nodes.
#[inline]
#[must_use]
pub fn frozen_store_modifier_flags(n: Node) -> Option<ModifierFlags> {
    if n.is_nil() {
        return None;
    }
    frozen_static!(n.file_index(), modifier_bits, |_, _, bits| bits
        .get(slot_index(n))
        .map(|&bits| ModifierFlags(u32::from(bits))))
    .flatten()
}

/// U4 (CH6, bind A): Go `n.Name()`, `n.Expression()`, `n.PostfixToken()` or
/// `n.QuestionToken()` (`which`) of a published store node (tier 0 or
/// tier 1), from the `children` column of its store (`SlotChildren`),
/// resolved like `Node::new`. C2: also Go `n.Type()`, `n.Initializer()` and
/// `n.AsTypeReference().TypeName`. `None` when the entry is unknown and for
/// any other node (nil, synthetic, unpublished): the caller reads
/// the node data.
#[inline]
#[must_use]
pub fn frozen_store_child(n: Node, which: StoreChild) -> Option<Node> {
    if n.is_nil() {
        return None;
    }
    let file = n.file_index();
    frozen_static!(file, per_store, |f, _, s| column_store_child(
        f, s, n, which
    ))
    .flatten()
}

/// `frozen_store_child` in the publish `f` of `n`, whose per-store part is
/// `s`.
#[inline]
fn column_store_child(
    f: &Frozen<'_>,
    s: &FrozenStore<'_>,
    n: Node,
    which: StoreChild,
) -> Option<Node> {
    let file = n.file_index();
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

/// C2: true when `n` is a published store node whose Go `TypeArgumentList()`
/// is nil with no list in its node data (`SlotChildren` `NO_TYPE_ARGUMENTS`),
/// so `Node::type_argument_list` is `NodeList::NIL`. False when not known and
/// for any other node (nil, synthetic, unpublished).
#[inline]
#[must_use]
pub fn frozen_store_lacks_type_arguments(n: Node) -> bool {
    if n.is_nil() {
        return false;
    }
    frozen_static!(n.file_index(), per_store, |_, _, s| {
        s.children
            .get(slot_index(n))
            .is_some_and(|entry| entry.has_no_type_arguments())
    })
    .unwrap_or(false)
}

/// R2-5: the children of a published store node (tier 0 or tier 1) in Go
/// `ForEachChild` order, from the link column of its store (`SlotLinks`),
/// without its node data. `None` when the chain of `n` is not known (a
/// node shell has no link column) and for any other node (nil, synthetic,
/// unpublished): the caller uses `for_each_child`.
#[inline]
#[must_use]
pub fn frozen_store_children(n: Node) -> Option<StoreChildren> {
    if n.is_nil() {
        return None;
    }
    let file = n.file_index();
    let s = static_frozen(file, |f| f.per_store)?;
    let links = s.links;
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
fn column_child(f: &Frozen<'_>, s: &FrozenStore<'_>, file: usize, id: u32) -> Node {
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
/// published store of `n`. `callback(node, kind)` gets `n` and then each
/// parent, with its Go `node.Kind`. The kind and header tables of the store
/// are found once, not once per `kind()` and `parent()` read. `None` when
/// `n` is not a published store node (nil included).
#[inline]
pub fn frozen_find_ancestor(
    n: Node,
    callback: impl FnMut(Node, SyntaxKind) -> bool,
) -> Option<AncestorWalk> {
    if n.is_nil() {
        return None;
    }
    let file = n.file_index();
    frozen_static!(file, headers, |f, local, &headers| {
        store_find_ancestor(file, headers, f.kinds[local], slot_index(n), callback)
    })
}

/// `frozen_find_ancestor` in store `file`, whose header and kind tables
/// are `headers` and `kinds`, from slot `index`.
#[inline]
fn store_find_ancestor(
    file: usize,
    headers: &[NodeHeader],
    kinds: &[SyntaxKind],
    mut index: usize,
    mut callback: impl FnMut(Node, SyntaxKind) -> bool,
) -> AncestorWalk {
    loop {
        let node = handle(file, index as u32);
        if callback(node, kinds[index]) {
            return AncestorWalk::Found(node);
        }
        // The stored parent (`NodeHeader::read`): a `LOCAL_STORE` handle is
        // a node of this store; anything else is nil or another store.
        let parent = headers[index].parent;
        if parent.file_index() != LOCAL_STORE {
            return if parent.is_nil() {
                AncestorWalk::Found(Node::NIL)
            } else {
                AncestorWalk::Next(parent)
            };
        }
        index = slot_index(parent);
    }
}

/// U4 (CH7): Go `n.Parent` and `n.Parent.Kind` of a published store node
/// whose parent is a node of the same store, with one store lookup. `None` for
/// any other node or parent (nil, another store): the caller reads them one
/// by one.
#[inline]
#[must_use]
pub fn frozen_store_parent_kind(n: Node) -> Option<(Node, SyntaxKind)> {
    if n.is_nil() {
        return None;
    }
    let file = n.file_index();
    frozen_static!(file, headers, |f, local, headers| {
        let parent = headers[slot_index(n)].parent;
        (parent.file_index() == LOCAL_STORE).then(|| {
            let index = slot_index(parent);
            (handle(file, index as u32), f.kinds[local][index])
        })
    })
    .flatten()
}

/// U4 (CH7): true when `n` is a published store node and no node of its store
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
    frozen_static!(n.file_index(), per_store, |_, _, s| s.facts.parents_local
        && !s.facts.has_deprecated_tag)
    .unwrap_or(false)
}

/// U1 (c): how `Node::new(file, id)` maps the child ids of one published
/// store, read once for a loop over many ids (`NodeSliceIter`).
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
    pub fn node(self, id: crate::astdata::NodeId) -> Node {
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

/// U1 (c): the `FrozenIds` of published store `file` (tier 0 or tier 1).
/// `None` for any other file (unpublished or synthetic): the caller
/// resolves each id.
#[inline]
#[must_use]
pub fn frozen_store_ids(file: usize) -> Option<FrozenIds> {
    let s = static_frozen(file, |f| f.per_store)?;
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
/// (`NodeBindBuilder` entries, flow nodes), tier 0, tier 1 or a freeable
/// file version. `None` for an unpublished store and a file without a
/// store.
#[must_use]
pub fn frozen_store_bind_estimate(file: usize) -> Option<(usize, usize)> {
    frozen!(file, stores, |_, _, store| {
        let e = store.bind_estimate;
        (e.entries as usize, e.flow_nodes as usize)
    })
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
        && (file < tier0.headers.len() || is_storeless_id(file))
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
    // lsshells M3c: a node that the store owns (a freeable parse).
    if s.cell_of(index) != NO_CELL {
        return set_parent_in_owned_store_children(s, index);
    }
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

/// `set_parent_in_store_children` for slot `index` of `s`, whose node the
/// store owns (lsshells M3c). The fields are borrowed apart, so the node
/// data is read while the headers and the links change.
#[inline(never)]
fn set_parent_in_owned_store_children(s: &mut FileStore, index: usize) -> bool {
    let FileStore {
        nodes,
        headers,
        build_links,
        owned,
        ..
    } = s;
    let owned = owned.as_deref().expect("a store that owns its nodes");
    let node = owned.node(owned.cell_of[index]);
    let kind = headers[index].kind;
    let stored = handle(LOCAL_STORE, index as u32);
    unlink_children(build_links, index);
    build_links[index].first_child = LINK_END;
    let mut last = LINK_END;
    let mut linking = true;
    let stopped = super::node::for_each_store_child_id(kind, node, |child| {
        let child = child as usize;
        if nodes[child].is_none() {
            return true;
        }
        headers[child].parent = stored;
        if linking && !link_child(build_links, index, &mut last, child) {
            linking = false;
            unlink_children(build_links, index);
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
/// `internIdentifier`). The new data replaces the old; the old node leaks
/// (a freeable parse keeps it in its store until the store is freed, so a
/// list handle taken before the write still reads the old list). The U1 and
/// U4 build entries and the keyword bit of the slot follow the new data,
/// and its R2-5 chain becomes unknown.
pub fn replace_store_node_data(n: Node, data: NodeData) {
    with_store_mut(n.file_index(), |s| {
        assert!(!s.frozen, "cannot mutate a node of a finished file");
        let index = slot_index(n);
        if s.nodes[index].is_none() {
            panic!("store handle does not name a node slot");
        }
        let old_kind = s.slot_ast_node(index).kind;
        debug_assert!(
            data.matches_syntax_kind(old_kind),
            "{old_kind:?} does not fit its NodeData"
        );
        let node = ast_node(old_kind, data);
        // The same code as `alloc_store_node`, on the header kind (the kind
        // `debug_check_text_names` and `modifier_bits_column` read).
        let kind = s.headers[index].kind;
        // PORT: U1 (d). Data cloned from a store identifier has an empty text
        // (`alloc_store_name_node`, `alloc_store_shared_name_node`), so an
        // empty text keeps the slot name. A new text replaces it. Go writes
        // no empty identifier text here. S1: the new data gets a new node;
        // a shared name node does not change.
        let keeps_name = matches!(kind, SyntaxKind::Identifier | SyntaxKind::PrivateIdentifier)
            && identifier_text(&node).is_empty();
        if !keeps_name {
            let (name, text_is_keyword) = s.slot_text_name(kind, &node, None);
            s.headers[index].text_is_keyword = text_is_keyword;
            s.build_names[index] = name;
        }
        let modifier_bits =
            s.slot_modifier_bits(super::node::store_node_modifier_bits(kind, &node));
        s.build_modifier_bits[index] = modifier_bits;
        // U4: a reparser write can change a child that the column holds.
        // C2: the same for the `typed` field.
        s.build_children[index] = super::node::store_node_children(kind, &node);
        // lsshells M3c: a freeable parse keeps the new node in a new cell.
        match s.owned.as_deref_mut() {
            Some(owned) => {
                let cell = owned.push(node);
                owned.cell_of[index] = cell;
                s.nodes[index] = Some(owned_marker());
            }
            None => s.nodes[index] = Some(leak_in_ast_arena(node)),
        }
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
        // PORT: a snapshot node is leaked in the AST arena, also in a store
        // that owns its nodes (a lib file is not edited), so no slot has a
        // cell.
        if let Some(owned) = s.owned.as_deref_mut() {
            owned.cell_of.resize(s.headers.len(), NO_CELL);
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
        let owns_nodes = s.owned.is_some();
        *s = FileStore::new(s.file_name, s.text);
        if owns_nodes {
            s.owned = Some(Box::new(OwnedAst::new(s.headers.capacity())));
        }
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
    pub(crate) node: &'static crate::astdata::Node,
    /// The slot points at the shared name node of its kind (S1).
    pub(crate) shared_name: bool,
    pub(crate) name: Name,
    pub(crate) text_is_keyword: bool,
}

/// R3-1, tests: the slots after slot 0 of store `file`, a store of this
/// thread whose parse is finished and that is not published. An error when
/// a snapshot cannot keep the store: an alias slot, a parent in another
/// store, or a astdata node with other base fields than `ast_node` gives.
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
            NodeData::Token(Box::new(crate::astdata::TokenData)),
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
    /// Parsed AST nodes and lists live for the whole process. One leaked
    /// bump arena per parsing thread holds them, so each node costs a
    /// pointer bump, not a malloc. The arena never drops, like the
    /// `Box::leak` it replaces. Synthetic nodes are not here: the synthetic
    /// arena (`ast/synthetic.rs`) owns them, so checker workers make no AST
    /// arena.
    static AST_ARENA: &'static bumpalo::Bump =
        Box::leak(Box::new(bumpalo::Bump::with_capacity(1 << 20)));
}

/// Moves `value` into this thread's leaked AST arena.
// PERF: U1 (b). Only the arena reference comes out of the out-of-line
// `LocalKey::with`, so `value` is not copied through its closure.
#[inline]
pub(crate) fn leak_in_ast_arena<T>(value: T) -> &'static T {
    let arena: &'static bumpalo::Bump = AST_ARENA.with(|a| *a);
    arena.alloc(value)
}

/// A astdata node with kind `kind` and data `data`. Only kind and data are
/// read for store and synthetic nodes; the header lives in the slot.
fn ast_node(kind: SyntaxKind, data: NodeData) -> crate::astdata::Node {
    crate::astdata::Node {
        kind,
        flags: crate::astdata::NodeFlags(0),
        range: ts_range(TextRange::undefined()),
        parent: None,
        data,
    }
}

/// `ast_node(kind, data)`, leaked in this thread's AST arena.
fn leak_ast_node(kind: SyntaxKind, data: NodeData) -> &'static crate::astdata::Node {
    leak_in_ast_arena(ast_node(kind, data))
}

/// S1: the one astdata node that every store Identifier (or
/// PrivateIdentifier, by `kind`) made by `alloc_store_shared_name_node`
/// points at. Its data is the Go factory payload with the default fields:
/// no flow node (the binder keeps flow nodes in its tables) and an empty
/// text (the name column holds the text).
fn shared_name_node(kind: SyntaxKind) -> &'static crate::astdata::Node {
    static IDENTIFIER: OnceLock<&'static crate::astdata::Node> = OnceLock::new();
    static PRIVATE_IDENTIFIER: OnceLock<&'static crate::astdata::Node> = OnceLock::new();
    let leak =
        |data| -> &'static crate::astdata::Node { Box::leak(Box::new(ast_node(kind, data))) };
    match kind {
        SyntaxKind::Identifier => *IDENTIFIER.get_or_init(|| {
            leak(NodeData::Identifier(Box::new(
                crate::astdata::IdentifierData {
                    flow_node: None,
                    text: String::new(),
                },
            )))
        }),
        SyntaxKind::PrivateIdentifier => *PRIVATE_IDENTIFIER.get_or_init(|| {
            leak(NodeData::PrivateIdentifier(Box::new(
                crate::astdata::PrivateIdentifierData {
                    text: String::new(),
                },
            )))
        }),
        _ => panic!("{kind:?} is not a name kind"),
    }
}

/// S1, debug builds: panics unless `data` (the payload the factory builds
/// for a store name node of kind `kind`) equals the data of the shared node
/// of `kind`. The struct patterns name every field, so a new astdata field
/// does not compile here until it is checked.
#[cfg(debug_assertions)]
pub fn debug_assert_shared_name_data(kind: SyntaxKind, data: &NodeData) {
    let same = match (data, &shared_name_node(kind).data) {
        (NodeData::Identifier(a), NodeData::Identifier(b)) => {
            let crate::astdata::IdentifierData { flow_node, text } = &**a;
            *flow_node == b.flow_node && *text == b.text
        }
        (NodeData::PrivateIdentifier(a), NodeData::PrivateIdentifier(b)) => {
            let crate::astdata::PrivateIdentifierData { text } = &**a;
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
/// (no flow node, empty data text), without a new data box or astdata node:
/// the slot points at the process-wide node of `kind` (`shared_name_node`).
/// The name column holds `text`. The factory checks its payload against the
/// shared one in debug builds (`debug_assert_shared_name_data`).
// PERF: S1. Saves one malloc and about 88 bytes per identifier (a 32-byte
// data box and a 40-byte arena node). Sharing one node is safe because a
// astdata node is never changed in place: its data has no interior
// mutability, the crate forbids unsafe code, and a data write gives the slot
// a new node (`replace_store_node_data`). No code uses the address of a
// astdata node as an identity (the `data_accessor!` `_in` debug check only
// compares the data of one node with itself).
pub fn alloc_store_shared_name_node(file: usize, kind: SyntaxKind, text: &str) -> Node {
    alloc_store_slot_node(file, kind, shared_name_node(kind), Some(text))
}

/// `alloc_store_node` with the name text `text` (`slot_text_name`).
// PERF: lsshells M3c. A static parse (every CLI parse) leaks the node first
// and passes a reference, as before M3c: one thread-local load picks the
// path, and the node value is not moved into the store closure.
#[inline]
fn alloc_store_slot(file: usize, kind: SyntaxKind, data: NodeData, text: Option<&str>) -> Node {
    debug_assert!(
        data.matches_syntax_kind(kind),
        "{kind:?} does not fit its NodeData"
    );
    if FREEABLE_PARSE.get() {
        return alloc_store_owned_slot(file, kind, ast_node(kind, data), text);
    }
    alloc_store_slot_node(file, kind, leak_ast_node(kind, data), text)
}

/// `alloc_store_slot` for a astdata node that is already made (a leaked
/// node, or a shared name node). In a store that owns its nodes the slot
/// has no cell, like a lib snapshot slot.
#[inline]
fn alloc_store_slot_node(
    file: usize,
    kind: SyntaxKind,
    node: &'static crate::astdata::Node,
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
        s.push_node_header(kind, text_is_keyword);
        s.nodes.push(Some(node));
        s.push_no_cell();
        s.push_build_columns(name, modifier_bits, children);
        handle(file, index)
    })
}

/// `alloc_store_slot` inside a freeable parse (lsshells M3c): a store that
/// owns its nodes keeps `node` in a new cell. Any other store leaks it.
#[inline(never)]
fn alloc_store_owned_slot(
    file: usize,
    kind: SyntaxKind,
    node: crate::astdata::Node,
    text: Option<&str>,
) -> Node {
    if !with_store(file, |s| s.owned.is_some()) {
        return alloc_store_slot_node(file, kind, leak_in_ast_arena(node), text);
    }
    debug_assert!(
        text.is_none() || identifier_text(&node).is_empty(),
        "a name node keeps its text in the name column"
    );
    let modifier_bits = super::node::store_node_modifier_bits(kind, &node);
    let children = super::node::store_node_children(kind, &node);
    with_store_mut(file, |s| {
        assert!(!s.frozen, "cannot create a node in a finished file");
        let index = s.headers.len() as u32;
        let (name, text_is_keyword) = s.slot_text_name(kind, &node, text);
        s.push_node_header(kind, text_is_keyword);
        let owned = s.owned_mut();
        let cell = owned.push(node);
        owned.cell_of.push(cell);
        s.nodes.push(Some(owned_marker()));
        s.push_build_columns(name, modifier_bits, children);
        handle(file, index)
    })
}

impl FileStore {
    /// The header of a new node slot (`alloc_store_slot_node`).
    #[inline]
    fn push_node_header(&mut self, kind: SyntaxKind, text_is_keyword: bool) {
        self.headers.push(NodeHeader {
            parent: Node::NIL,
            loc: TextRange::undefined(),
            flags: NodeFlags::NONE,
            kind,
            source_file_is_root: false,
            text_is_keyword,
        });
    }

    /// The U1 and U4 build entries of a new node slot, after its header and
    /// node (`alloc_store_slot_node`).
    #[inline]
    fn push_build_columns(&mut self, name: Name, modifier_bits: u32, children: SlotChildren) {
        self.build_names.push(name);
        let modifier_bits = self.slot_modifier_bits(modifier_bits);
        self.build_modifier_bits.push(modifier_bits);
        self.build_children.push(children);
        self.build_links.push(SlotLinks::NONE);
        self.debug_assert_build_columns();
    }
}

/// The store-local id that stands for `n` inside `NodeData` of store `file`.
/// Nil maps to the nil slot. A node of another file gets (or reuses) an
/// alias slot.
// PERF: U4 (4). The factory calls this for every child and list entry, and
// nearly all are nil or of the same file. Those two tests are inline; the
// alias path is out of line, so the function body stays small.
#[inline]
#[must_use]
pub fn store_child_id(file: usize, n: Node) -> crate::astdata::NodeId {
    if n.is_nil() {
        return crate::astdata::NodeId::new(NIL_SLOT);
    }
    if n.file_index() == file {
        return crate::astdata::NodeId::new(slot_index(n) as u32);
    }
    store_alias_id(file, n)
}

/// The alias slot of foreign node `n` in store `file` (`store_child_id`).
#[inline(never)]
fn store_alias_id(file: usize, n: Node) -> crate::astdata::NodeId {
    with_store_mut(file, |s| {
        if let Some(&index) = s.aliases.get(&n) {
            return crate::astdata::NodeId::new(index);
        }
        let index = s.headers.len() as u32;
        s.headers.push(NodeHeader::target(n));
        s.nodes.push(None);
        s.push_no_cell();
        s.build_names.push(Name::default());
        s.build_modifier_bits.push(0);
        s.build_children.push(SlotChildren::UNKNOWN);
        s.build_links.push(SlotLinks::NONE);
        s.debug_assert_build_columns();
        s.aliases.insert(n, index);
        crate::astdata::NodeId::new(index)
    })
}

/// Like `store_child_id`, for astdata fields that are `Option<NodeId>`.
#[must_use]
pub fn store_opt_child_id(file: usize, n: Node) -> Option<crate::astdata::NodeId> {
    if n.is_nil() {
        None
    } else {
        Some(store_child_id(file, n))
    }
}

/// A Go `core.TextRange` in astdata form (`-1` is stored as `u32::MAX`).
fn ts_range(loc: TextRange) -> crate::astdata::text::TextRange {
    crate::astdata::text::TextRange {
        start: crate::astdata::text::TextPos::new(loc.pos() as u32),
        end: crate::astdata::text::TextPos::new(loc.end() as u32),
    }
}

/// The astdata list for a list of store `file`.
fn ts_list(file: usize, nodes: &[Node], loc: TextRange) -> crate::astdata::NodeList {
    crate::astdata::NodeList {
        range: ts_range(loc),
        nodes: nodes.iter().map(|&n| store_child_id(file, n)).collect(),
        has_trailing_comma: false,
    }
}

/// U1 (e): a list that the parser made in a store and that no node data
/// holds yet: what a pending `NodeList` handle names. Its ids live in the
/// AST bump arena. `store_list_value` builds the astdata list from it, once
/// for each node data that stores it.
#[derive(Debug)]
pub struct PendingList {
    /// Go `list.Loc` in astdata form (`ts_range`).
    pub(crate) range: crate::astdata::text::TextRange,
    /// The store ids of the nodes (`store_child_id`).
    pub(crate) nodes: &'static [crate::astdata::NodeId],
    /// The astdata bit (`NodeList::stored_trailing_comma`).
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

    /// The astdata list with the same range, ids and bit.
    fn to_ts(&self) -> crate::astdata::NodeList {
        crate::astdata::NodeList {
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
    pub(crate) flags: crate::astdata::ModifierFlags,
}

impl PendingModifierList {
    /// The astdata modifier list with the same list and flags.
    fn to_ts(&self) -> crate::astdata::ModifierList {
        crate::astdata::ModifierList {
            list: self.list.to_ts(),
            flags: self.flags,
        }
    }
}

/// Go `f.NewNodeList(nodes)` followed by `list.Loc = loc`, in store `file`.
// PERF: U1 (e). A pending handle: the ids go into the AST bump arena, not
// into a `Vec` that `store_list_value` copied again (two mallocs, and the
// first copy leaked). A store that owns its nodes (lsshells M3c) keeps the
// list (`OwnedPending`).
#[must_use]
pub fn new_store_node_list(file: usize, nodes: &[Node], loc: TextRange) -> NodeList {
    if FREEABLE_PARSE.get()
        && let Some(list) = new_owned_pending(file, nodes, loc, None)
    {
        return NodeList::store(list);
    }
    NodeList::pending(file, leak_in_ast_arena(PendingList::new(file, nodes, loc)))
}

/// The pending list of `nodes` at `loc` (with `flags` for a modifier
/// list) in store `file` when that store owns its nodes (lsshells M3c).
/// `None`, with nothing made, for a static store.
// PERF: the callers test `FREEABLE_PARSE` inline, so a static parse (every
// CLI parse) does not call this.
#[inline(never)]
fn new_owned_pending(
    file: usize,
    nodes: &[Node],
    loc: TextRange,
    flags: Option<crate::astdata::ModifierFlags>,
) -> Option<StoreList> {
    // A store that owns its nodes is made and filled only inside a freeable
    // parse scope.
    if !FREEABLE_PARSE.get() || !with_store(file, |s| s.owned.is_some()) {
        return None;
    }
    // The alias slots are made in order, as `PendingList::new` does, before
    // the store borrow below.
    let nodes: Box<[crate::astdata::NodeId]> =
        nodes.iter().map(|&n| store_child_id(file, n)).collect();
    Some(with_store_mut(file, |s| {
        s.owned_mut().push_pending(
            file,
            OwnedPending {
                range: ts_range(loc),
                nodes,
                has_trailing_comma: false,
                flags,
            },
        )
    }))
}

/// Go `f.NewModifierList(nodes)` followed by `list.Loc = loc`, in store
/// `file`. `ModifierFlags = ModifiersToFlags(nodes)` as in Go.
// PERF: U1 (e), as `new_store_node_list`.
#[must_use]
pub fn new_store_modifier_list(file: usize, nodes: &[Node], loc: TextRange) -> ModifierList {
    let flags = crate::astdata::ModifierFlags(modifiers_to_flags(nodes).0 as u32);
    if FREEABLE_PARSE.get()
        && let Some(list) = new_owned_pending(file, nodes, loc, Some(flags))
    {
        return ModifierList::store(list);
    }
    let list = leak_in_ast_arena(PendingModifierList {
        list: PendingList::new(file, nodes, loc),
        flags,
    });
    ModifierList::pending(file, list)
}

/// A list value to store inside new `NodeData` of store `file`. Go stores
/// the `*NodeList` pointer. A list of the same store is copied as is; any
/// other list is rebuilt over ids of this store with its own `Loc`.
// PORT: astdata stores lists by value, so `NodeList` equality on the copy is
// false where Go compares equal pointers (plan risk 2).
#[must_use]
pub fn store_list_value(file: usize, list: NodeList) -> Option<crate::astdata::NodeList> {
    if list.is_nil() {
        return None;
    }
    if list.file() == file {
        // U1 (e): the astdata list of a pending list is made here, once.
        if let Some(p) = list.pending_list() {
            return Some(p.to_ts());
        }
        if let Some(l) = list.ts_list() {
            return Some(l.clone());
        }
        // lsshells M3c: a list of a store that owns its nodes.
        if let Some(l) = list.store_list() {
            return Some(with_store_list(l, |l| l.to_ts()));
        }
    }
    let nodes = list.nodes().to_vec();
    Some(ts_list(file, &nodes, list.loc()))
}

/// Like `store_list_value` for a list field that astdata requires. Go `nil`
/// becomes an empty list at `NIL_LIST_POS`, which `NodeList::is_nil` reads
/// as nil.
#[must_use]
pub fn store_req_list_value(file: usize, list: NodeList) -> crate::astdata::NodeList {
    store_list_value(file, list).unwrap_or_else(|| crate::astdata::NodeList {
        range: crate::astdata::text::TextRange {
            start: crate::astdata::text::TextPos::new(NIL_LIST_POS),
            end: crate::astdata::text::TextPos::new(NIL_LIST_POS),
        },
        nodes: Vec::new(),
        has_trailing_comma: false,
    })
}

/// A modifier list value to store inside new `NodeData` of store `file`.
#[must_use]
pub fn store_modifiers_value(
    file: usize,
    modifiers: ModifierList,
) -> Option<crate::astdata::ModifierList> {
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
        // lsshells M3c: a list of a store that owns its nodes.
        if let Some(m) = modifiers.store_list() {
            return Some(with_store_list(m, |l| l.to_ts_modifiers()));
        }
    }
    let nodes = modifiers.nodes().to_vec();
    Some(crate::astdata::ModifierList {
        list: ts_list(file, &nodes, modifiers.loc()),
        flags: crate::astdata::ModifierFlags(modifiers_to_flags(&nodes).0 as u32),
    })
}

/// True when `l` is the Go `nil` marker of a required list field.
#[inline]
#[must_use]
pub fn is_nil_list_marker(l: &crate::astdata::NodeList) -> bool {
    is_nil_list_range(&l.range)
}

/// True when `range` is the range of a Go `nil` marker list
/// (`NIL_LIST_POS`).
#[inline]
#[must_use]
pub fn is_nil_list_range(range: &crate::astdata::text::TextRange) -> bool {
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
        // S1: every store identifier points at one shared astdata node.
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
            assert_eq!(
                file_store_js_doc(adopted.store, *node).map(NodeSlice::to_vec),
                Some(jsdocs.clone())
            );
        }
    }

    /// The nodes of the tree of `root` in `for_each_child` order.
    fn tree(root: Node) -> Vec<Node> {
        fn walk(n: Node, out: &mut Vec<Node>) {
            out.push(n);
            n.for_each_child(|child| {
                walk(child, out);
                false
            });
        }
        let mut out = Vec::new();
        walk(root, &mut out);
        out
    }

    /// What the node reads give for `n` (lsshells M3c twin parses): header,
    /// text, modifiers, JSDoc and the lists of its data.
    fn twin_facts(n: Node) -> String {
        let mut lists = Vec::new();
        n.for_each_child_and_lists(&mut |_| false, &mut |l, is_mod| {
            lists.push((l.nodes().len(), l.pos(), l.end(), is_mod));
        });
        format!(
            "{:?} {:?} {:?} {:?} {:?} {:?} {} {:?}",
            n.kind(),
            n.loc(),
            n.flags(),
            n.text(),
            n.modifier_flags(),
            n.modifiers().nodes().to_vec().len(),
            n.js_doc(Node::NIL).len(),
            lists
        )
    }

    // lsshells M3c: a freeable parse keeps its astdata nodes in its store
    // and answers every node read as a static parse of the same text.
    #[test]
    fn owned_parse_reads_like_a_static_parse() {
        use crate::frontend::parser::{SourceFileParseOptions, parse_source_file};
        let text = "/** doc */\nexport async function f(a: number, b = 1) { return a + b; }\n\
            let x: Array<string> = [1, 2].map(y => `${y}`);\n\
            type T = { a?: string } | number;\n\
            @dec class C<U> extends Object { private m(): U | undefined { return undefined; } }\n\
            const re = /ab+c/g, s = 'str', n = 0x10, big = 10n;\n";
        let opts = |name: &str| SourceFileParseOptions {
            file_name: name.to_string(),
            ..Default::default()
        };
        let fixed = parse_source_file(&opts("/static.ts"), text, ScriptKind::TS);
        let before = owned_node_count();
        let owned = {
            let _scope = enter_owned_parse();
            parse_source_file(&opts("/owned.ts"), text, ScriptKind::TS)
        };
        assert!(!is_freeable_parse(), "the scope ends");
        assert!(
            owned_node_count() > before,
            "the freeable parse owns its nodes"
        );
        assert!(with_store(owned.store, |s| s.owned.is_some()));
        assert!(with_store(fixed.store, |s| s.owned.is_none()));
        assert!(try_store_ast_node(fixed.root).is_some());
        assert!(
            try_store_ast_node(owned.root).is_none(),
            "an owned node has no 'static data"
        );
        let (a, b) = (tree(fixed.root), tree(owned.root));
        assert_eq!(a.len(), b.len());
        for (&a, &b) in a.iter().zip(&b) {
            assert_eq!(twin_facts(a), twin_facts(b), "{:?}", a.kind());
        }
        assert!(owned.root.statement_list().store_list().is_some());
        assert_eq!(fixed.root.statements().len(), owned.root.statements().len());
    }

    // lsshells M3c: a data write in a store that owns its nodes fills a new
    // cell, so a list handle of the old data still reads the old list (a Go
    // `*NodeList` pointer), and the pending lists are the store's.
    #[test]
    fn owned_data_write_keeps_old_list_handles() {
        let _scope = enter_owned_parse();
        let file = new_file_store("/owned-write.ts", "");
        let f = NodeFactory::for_file(file);
        let export = f.new_modifier(SyntaxKind::ExportKeyword);
        let modifiers = f.new_modifier_list(&[export]);
        assert!(modifiers.store_list().is_some(), "an owned pending list");
        let list = f.new_variable_declaration_list(NodeList::NIL, NodeFlags::NONE);
        let statement = f.new_variable_statement(modifiers, list);
        let old = statement.modifiers();
        assert!(old.store_list().is_some());
        assert_eq!(old.nodes().to_vec(), vec![export]);
        assert_eq!(old.modifier_flags(), ModifierFlags::EXPORT);
        assert_eq!(old, statement.modifiers(), "one list, one handle identity");
        assert!(list.declarations().is_nil());

        let mut data = with_ast_data(statement, Clone::clone);
        if let NodeData::VariableStatement(d) = &mut data {
            d.modifiers = None;
        }
        replace_store_node_data(statement, data);
        assert!(statement.modifiers().is_nil());
        assert_eq!(old.nodes().to_vec(), vec![export], "the old list stays");
        assert_ne!(old, statement.modifiers());
        freeze_file_store(file);
        assert_eq!(statement.kind(), SyntaxKind::VariableStatement);
        assert_eq!(statement.declaration_list(), list);
        assert!(with_store(file, |s| s.owned_ref().len >= 4));
    }
}
