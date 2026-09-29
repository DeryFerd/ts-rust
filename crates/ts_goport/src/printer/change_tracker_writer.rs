//! Port of Go `printer/changetrackerwriter.go`.

use crate::prelude::*;

use crate::frontend::scanner::scanner_p1::{rune_to_char, utf8_decode_last_rune_in_string};

// Go: printer/changetrackerwriter.go:12 ChangeTrackerWriter
// PORT: Go embeds `textWriter`; here it is the field `text_writer`, and the
// promoted methods are the `EmitTextWriter` impl below. The print handlers
// (closures the printer calls while it also writes to this writer) and the
// writer share `lastNonTriviaPosition`, `pos` and `end` through `positions`.
// Borrows of `positions` are short and never nested.
pub struct ChangeTrackerWriter {
    text_writer: TextWriter,
    positions: Rc<RefCell<TriviaPositions>>,
}

/// The Go `ChangeTrackerWriter` fields that the print handlers share.
// PORT: not a Go type; see `ChangeTrackerWriter`.
#[derive(Debug, Default)]
struct TriviaPositions {
    last_non_trivia_position: i32,
    pos: FxHashMap<TriviaPositionKey, i32>,
    end: FxHashMap<TriviaPositionKey, i32>,
}

// Go: printer/changetrackerwriter.go:19 triviaPositionKey
// Go: interface { // *astNode | *ast.NodeList
// PORT: Go keys the maps by pointer. `NodeList` has no `Hash`, so a list is
// keyed by the address of the list it names (`NodeList::list_ptr`; pointer
// identity, as Go and `NodeList`'s `PartialEq`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum TriviaPositionKey {
    Node(Node),
    NodeList(usize),
}

impl TriviaPositionKey {
    fn node_list(list: NodeList) -> TriviaPositionKey {
        TriviaPositionKey::NodeList(list.list_ptr().map_or(0, |l| l as usize))
    }
}

impl TriviaPositions {
    // Go: printer/changetrackerwriter.go:74 setPos
    fn set_pos(&mut self, node: TriviaPositionKey) {
        self.pos.insert(node, self.last_non_trivia_position);
    }

    // Go: printer/changetrackerwriter.go:78 setEnd
    fn set_end(&mut self, node: TriviaPositionKey) {
        self.end.insert(node, self.last_non_trivia_position);
    }

    // Go: printer/changetrackerwriter.go:82 getPos
    fn get_pos(&self, node: TriviaPositionKey) -> i32 {
        self.pos.get(&node).copied().unwrap_or(0)
    }

    // Go: printer/changetrackerwriter.go:86 getEnd
    fn get_end(&self, node: TriviaPositionKey) -> i32 {
        self.end.get(&node).copied().unwrap_or(0)
    }
}

// Go: printer/changetrackerwriter.go:24 NewChangeTrackerWriter
#[must_use]
pub fn new_change_tracker_writer(newline: &str, indent_size: i32) -> ChangeTrackerWriter {
    let mut indent_size = indent_size;
    // TODO: Callers passing -1 should pass actual indent options once indent-related formatting is ported.
    if indent_size < 0 {
        // PORT: Go `defaultIndentSize`, private in text_writer.rs.
        indent_size = get_default_indent_size();
    }
    let mut ctw = ChangeTrackerWriter {
        // PORT: Go struct literal `textWriter{newLine, indentSize}`. It keeps
        // an indent size of 0; `new_text_writer` would turn 0 into 4.
        text_writer: new_text_writer_literal(newline, indent_size),
        positions: Rc::new(RefCell::new(TriviaPositions {
            last_non_trivia_position: 0,
            pos: FxHashMap::default(),
            end: FxHashMap::default(),
        })),
    };
    ctw.text_writer.clear();
    ctw
}

impl ChangeTrackerWriter {
    // Go: printer/changetrackerwriter.go:39 GetPrintHandlers
    // PORT: the handlers hold the shared `positions` instead of `ct`.
    #[must_use]
    pub fn get_print_handlers(&self) -> PrintHandlers {
        let before_node = self.positions.clone();
        let after_node = self.positions.clone();
        let before_list = self.positions.clone();
        let after_list = self.positions.clone();
        let before_token = self.positions.clone();
        let after_token = self.positions.clone();
        PrintHandlers {
            on_before_emit_node: Some(Rc::new(move |node_opt: Node| {
                if node_opt.is_some() {
                    before_node
                        .borrow_mut()
                        .set_pos(TriviaPositionKey::Node(node_opt));
                }
            })),
            on_after_emit_node: Some(Rc::new(move |node_opt: Node| {
                if node_opt.is_some() {
                    after_node
                        .borrow_mut()
                        .set_end(TriviaPositionKey::Node(node_opt));
                }
            })),
            on_before_emit_node_list: Some(Rc::new(move |nodes_opt: NodeList| {
                if nodes_opt.is_some() {
                    before_list
                        .borrow_mut()
                        .set_pos(TriviaPositionKey::node_list(nodes_opt));
                }
            })),
            on_after_emit_node_list: Some(Rc::new(move |nodes_opt: NodeList| {
                if nodes_opt.is_some() {
                    after_list
                        .borrow_mut()
                        .set_end(TriviaPositionKey::node_list(nodes_opt));
                }
            })),
            on_before_emit_token: Some(Rc::new(move |node_opt: Node| {
                if node_opt.is_some() {
                    before_token
                        .borrow_mut()
                        .set_pos(TriviaPositionKey::Node(node_opt));
                }
            })),
            on_after_emit_token: Some(Rc::new(move |node_opt: Node| {
                if node_opt.is_some() {
                    after_token
                        .borrow_mut()
                        .set_end(TriviaPositionKey::Node(node_opt));
                }
            })),
            ..PrintHandlers::default()
        }
    }

    // Go: printer/changetrackerwriter.go:74 setPos
    fn set_pos(&self, node: TriviaPositionKey) {
        self.positions.borrow_mut().set_pos(node);
    }

    // Go: printer/changetrackerwriter.go:78 setEnd
    fn set_end(&self, node: TriviaPositionKey) {
        self.positions.borrow_mut().set_end(node);
    }

    // Go: printer/changetrackerwriter.go:82 getPos
    fn get_pos(&self, node: TriviaPositionKey) -> i32 {
        self.positions.borrow().get_pos(node)
    }

    // Go: printer/changetrackerwriter.go:86 getEnd
    fn get_end(&self, node: TriviaPositionKey) -> i32 {
        self.positions.borrow().get_end(node)
    }

    // Go: printer/changetrackerwriter.go:90 setLastNonTriviaPosition
    fn set_last_non_trivia_position(&mut self, s: &str, force: bool) {
        if force || skip_trivia(s, 0) != s.len() as i32 {
            let text_pos = self.text_writer.get_text_pos();
            let mut positions = self.positions.borrow_mut();
            positions.last_non_trivia_position = text_pos;
            // trim trailing whitespaces
            let mut pos = s.len();
            while pos > 0 {
                let (r, size) = utf8_decode_last_rune_in_string(s, pos);
                if is_white_space_like(rune_to_char(r)) {
                    pos -= size as usize;
                } else {
                    break;
                }
            }
            positions.last_non_trivia_position -= (s.len() - pos) as i32;
        }
    }

    // Go: printer/changetrackerwriter.go:107 AssignPositionsToNode
    pub fn assign_positions_to_node<'a>(&'a self, node: Node, factory: &'a NodeFactory) -> Node {
        let mut visitor: NodeVisitor<'a, ()> = new_node_visitor(
            move |n: Node, v: &mut NodeVisitor<'a, ()>| self.assign_positions_to_node_worker(n, v),
            Some(factory),
            NodeVisitorHooks {
                visit_node: Some(Rc::new(move |n: Node, v: &mut NodeVisitor<'a, ()>| {
                    self.assign_positions_to_node_worker(n, v)
                })),
                visit_nodes: Some(Rc::new(
                    move |nodes: NodeList, v: &mut NodeVisitor<'a, ()>| {
                        self.assign_positions_to_node_array(nodes, v)
                    },
                )),
                visit_token: Some(Rc::new(move |n: Node, v: &mut NodeVisitor<'a, ()>| {
                    self.assign_positions_to_node_worker(n, v)
                })),
                visit_modifiers: Some(Rc::new(
                    move |modifiers: ModifierList, v: &mut NodeVisitor<'a, ()>| {
                        if modifiers.is_some() {
                            let new_node_list =
                                self.assign_positions_to_node_array(modifiers.node_list(), v);
                            // Return a new ModifierList so that VisitEachChild/Update detects the
                            // change and creates a new node with reassigned child positions.
                            return factory.new_modifier_list(&new_node_list.nodes().to_vec());
                        }
                        modifiers
                    },
                )),
                ..NodeVisitorHooks::default()
            },
            (),
        );
        self.assign_positions_to_node_worker(node, &mut visitor)
    }

    // Go: printer/changetrackerwriter.go:130 assignPositionsToNodeWorker
    fn assign_positions_to_node_worker(&self, node: Node, v: &mut NodeVisitor<'_, ()>) -> Node {
        if node.is_nil() {
            return node;
        }
        let visited = node.visit_each_child(v);
        // Assigning positions must not mutate the caller's node: it may be printed again (a change in a
        // content-mapped file is formatted once per virtual projection of its insertion point), and a node
        // that has acquired positions is printed by reading text back out of the source file. VisitEachChild
        // returns a fresh node only when a child changed, so clone whenever it hands back the input.
        let mut new_node = visited;
        if visited == node {
            new_node = v.factory().clone_node(visited);
        }
        // Go returns true from this callback, which stops ForEachChild after
        // the first child. Kept as Go.
        new_node.for_each_child(|child| {
            set_node_parent(child, new_node);
            true
        });
        set_node_loc(
            new_node,
            TextRange::new(
                self.get_pos(TriviaPositionKey::Node(node)),
                self.get_end(TriviaPositionKey::Node(node)),
            ),
        );
        new_node
    }

    // Go: printer/changetrackerwriter.go:151 assignPositionsToNodeArray
    fn assign_positions_to_node_array(
        &self,
        nodes: NodeList,
        v: &mut NodeVisitor<'_, ()>,
    ) -> NodeList {
        let visited = v.visit_nodes(nodes);
        if visited.is_nil() {
            return visited;
        }
        if nodes.is_nil() {
            // Debug.assert(nodes);
            panic!("if nodes is nil, visited should not be nil");
        }
        // clone nodearray if necessary
        // PORT: Go clones the list when `visited == nodes` and then sets
        // `nodeArray.Loc` on the (new or cloned) list. A list `Loc` is fixed
        // when the list is made, so both cases make one new list with the
        // same nodes and the assigned `Loc`.
        let loc = TextRange::new(
            self.get_pos(TriviaPositionKey::node_list(nodes)),
            self.get_end(TriviaPositionKey::node_list(nodes)),
        );
        v.factory()
            .new_node_list_with_loc(&visited.nodes().to_vec(), loc)
    }
}

impl EmitTextWriter for ChangeTrackerWriter {
    // Go: printer/changetrackerwriter.go:173 Write
    fn write(&mut self, text: &str) {
        self.text_writer.write(text);
        self.set_last_non_trivia_position(text, false);
    }

    // Go: printer/changetrackerwriter.go:178 WriteTrailingSemicolon
    fn write_trailing_semicolon(&mut self, text: &str) {
        self.text_writer.write_trailing_semicolon(text);
        self.set_last_non_trivia_position(text, false);
    }

    // Go: printer/changetrackerwriter.go:182 WriteComment
    fn write_comment(&mut self, text: &str) {
        self.text_writer.write_comment(text);
    }

    // Go: printer/changetrackerwriter.go:183 WriteKeyword
    fn write_keyword(&mut self, text: &str) {
        self.text_writer.write_keyword(text);
        self.set_last_non_trivia_position(text, false);
    }

    // Go: printer/changetrackerwriter.go:188 WriteOperator
    fn write_operator(&mut self, text: &str) {
        self.text_writer.write_operator(text);
        self.set_last_non_trivia_position(text, false);
    }

    // Go: printer/changetrackerwriter.go:193 WritePunctuation
    fn write_punctuation(&mut self, text: &str) {
        self.text_writer.write_punctuation(text);
        self.set_last_non_trivia_position(text, false);
    }

    // Go: printer/changetrackerwriter.go:198 WriteSpace
    fn write_space(&mut self, text: &str) {
        self.text_writer.write_space(text);
        self.set_last_non_trivia_position(text, false);
    }

    // Go: printer/changetrackerwriter.go:203 WriteStringLiteral
    fn write_string_literal(&mut self, text: &str) {
        self.text_writer.write_string_literal(text);
        self.set_last_non_trivia_position(text, false);
    }

    // Go: printer/changetrackerwriter.go:208 WriteParameter
    fn write_parameter(&mut self, text: &str) {
        self.text_writer.write_parameter(text);
        self.set_last_non_trivia_position(text, false);
    }

    // Go: printer/changetrackerwriter.go:213 WriteProperty
    fn write_property(&mut self, text: &str) {
        self.text_writer.write_property(text);
        self.set_last_non_trivia_position(text, false);
    }

    // Go: printer/changetrackerwriter.go:218 WriteSymbol
    fn write_symbol(&mut self, text: &str, symbol: SymbolId) {
        self.text_writer.write_symbol(text, symbol);
        self.set_last_non_trivia_position(text, false);
    }

    // Go: printer/changetrackerwriter.go:222 WriteLine
    fn write_line(&mut self) {
        self.text_writer.write_line();
    }

    // Go: printer/changetrackerwriter.go:223 WriteLineForce
    fn write_line_force(&mut self, force: bool) {
        self.text_writer.write_line_force(force);
    }

    // Go: printer/changetrackerwriter.go:224 IncreaseIndent
    fn increase_indent(&mut self) {
        self.text_writer.increase_indent();
    }

    // Go: printer/changetrackerwriter.go:225 DecreaseIndent
    fn decrease_indent(&mut self) {
        self.text_writer.decrease_indent();
    }

    // Go: printer/changetrackerwriter.go:226 Clear
    fn clear(&mut self) {
        self.text_writer.clear();
        self.positions.borrow_mut().last_non_trivia_position = 0;
    }

    // Go: printer/changetrackerwriter.go:227 String
    fn string(&self) -> String {
        self.text_writer.string()
    }

    // Go: printer/changetrackerwriter.go:228 RawWrite
    fn raw_write(&mut self, s: &str) {
        self.text_writer.raw_write(s);
        self.set_last_non_trivia_position(s, false);
    }

    // Go: printer/changetrackerwriter.go:233 WriteLiteral
    fn write_literal(&mut self, s: &str) {
        self.text_writer.write_literal(s);
        self.set_last_non_trivia_position(s, true);
    }

    // Go: printer/changetrackerwriter.go:237 GetTextPos
    fn get_text_pos(&self) -> i32 {
        self.text_writer.get_text_pos()
    }

    // Go: printer/changetrackerwriter.go:238 GetLine
    fn get_line(&self) -> i32 {
        self.text_writer.get_line()
    }

    // Go: printer/changetrackerwriter.go:239 GetColumn
    fn get_column(&self) -> i32 {
        self.text_writer.get_column()
    }

    // Go: printer/changetrackerwriter.go:240 GetIndent
    fn get_indent(&self) -> i32 {
        self.text_writer.get_indent()
    }

    // Go: printer/changetrackerwriter.go:241 IsAtStartOfLine
    fn is_at_start_of_line(&self) -> bool {
        self.text_writer.is_at_start_of_line()
    }

    // Go: printer/changetrackerwriter.go:243 HasTrailingComment
    fn has_trailing_comment(&self) -> bool {
        self.text_writer.has_trailing_comment()
    }

    // Go: printer/changetrackerwriter.go:245 HasTrailingWhitespace
    fn has_trailing_whitespace(&self) -> bool {
        self.text_writer.has_trailing_whitespace()
    }
}
