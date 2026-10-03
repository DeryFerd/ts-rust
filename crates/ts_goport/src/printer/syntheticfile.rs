//! Port of Go `printer/syntheticfile.go`.

use crate::prelude::*;

// Go: printer/syntheticfile.go:17 PrintAndPositionNode
// PrintAndPositionNode prints a synthesized node to text using the standard
// change-tracker printer options, trims the trailing newline, and assigns
// positions to the resulting node tree.
// sourceFile may be nil; when non-nil it is passed to the printer for comment
// preservation.
// The returned text is the printed source, and positioned is the node with
// concrete source positions assigned to it and all descendants.
// PORT: Go returns `(text string, positioned *ast.Node)` as a tuple. A nil
// Go `emitContext` is `None`. The printer writes through
// `Rc<RefCell<dyn EmitTextWriter>>`, so the writer is shared. The print
// handlers are taken first; they share the writer's positions (see
// `ChangeTrackerWriter`).
pub fn print_and_position_node(
    factory: &NodeFactory,
    node: Node,
    source_file: Node,
    new_line: &str,
    indent_size: i32,
    emit_context: Option<Rc<EmitContext>>,
) -> (String, Node) {
    let writer = Rc::new(RefCell::new(new_change_tracker_writer(
        new_line,
        indent_size,
    )));
    let print_handlers = writer.borrow().get_print_handlers();
    let emit_text_writer: Rc<RefCell<dyn EmitTextWriter>> = writer.clone();
    new_printer(
        PrinterOptions {
            new_line: get_new_line_kind(new_line),
            never_ascii_escape: true,
            preserve_source_newlines: true,
            terminate_unterminated_literals: true,
            ..PrinterOptions::default()
        },
        print_handlers,
        emit_context,
    )
    .write_exported(node, source_file, emit_text_writer, None);

    let text = writer.borrow().string();
    let text = text.strip_suffix(new_line).unwrap_or(&text).to_string();
    let positioned = writer.borrow().assign_positions_to_node(node, factory);
    (text, positioned)
}

// Go: printer/syntheticfile.go:39 CreateSyntheticSourceFile
// CreateSyntheticSourceFile wraps a positioned node in a synthetic source file
// suitable for use with the formatter. The node must already have valid source
// positions assigned (e.g. via PrintAndPositionNode or AssignPositionsToNode).
// PORT: Go takes `parseOptions ast.SourceFileParseOptions`. The Rust
// `NodeFactory::new_source_file` keeps only its file name and path, so this
// takes those two. A factory SourceFile keeps `&'static` text, like the
// leaked synthetic nodes, so the text is leaked.
pub fn create_synthetic_source_file(
    factory: &NodeFactory,
    node: Node,
    text: &str,
    file_name: &'static str,
    path: &str,
) -> Node {
    let eof = factory.new_token(SyntaxKind::EndOfFile);
    set_node_loc(eof, TextRange::new(text.len() as i32, text.len() as i32));
    // PORT: Go sets `statements.Loc` after `NewNodeList`. A list `Loc` is
    // fixed when the list is made, so it is made with the loc.
    let statements =
        factory.new_node_list_with_loc(&[node], TextRange::new(node.pos(), node.end()));
    let text: &'static str = Box::leak(text.to_string().into_boxed_str());
    let synthetic_file = factory.new_source_file(file_name, path, text, statements, eof);
    set_node_loc(synthetic_file, TextRange::new(0, text.len() as i32));
    set_parent_in_children(synthetic_file);
    synthetic_file
}
