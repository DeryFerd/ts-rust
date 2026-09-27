//! Port of the Go `ast.NodeFactory` constructors that `ast/factory.rs` does
//! not have yet (`ast/ast.go`, `ast/ast_generated.go`). The parser needs them.
//!
//! The argument rules are the same as in `ast/factory.rs`: Go `*Node` is
//! `Node`, Go `*NodeList` is `NodeList`, Go `*ModifierList` is
//! `ModifierList`, and Go `nil` is the `NIL` value of each. Nodes go to the
//! factory target (synthetic arena or the store of the parsed file).

use crate::frontend::prelude::*;
use ts_ast::NodeData as D;

/// Go `TokenFlagsNone` in ts_ast form.
const NO_TOKEN_FLAGS: ts_ast::TokenFlags = ts_ast::TokenFlags(0);

impl NodeFactory {
    // Go: ast/ast.go:2549 NewSourceFile
    // PORT: Go stores `fileName`, `parseOptions` and `text` on the
    // SourceFile data. Here the file name and text live in the node store
    // (`new_file_store`) and the parse options in `ParsedSourceFile`, so only
    // the Go check on the file name is kept. Go `ContainsNonASCII` (from the
    // text) is set by `ParsedSourceFile::new`, and the parser writes it to the
    // store. The other callers (an empty tsconfig file, a build worker
    // diagnostics file) do not make a position map, so their store keeps
    // false.
    // PORT: named `new_parsed_source_file` because `ast/factory.rs` has the
    // synthetic form of Go NewSourceFile with a different signature.
    pub fn new_parsed_source_file(
        &self,
        opts: &SourceFileParseOptions,
        text: &str,
        statements: NodeList,
        end_of_file_token: Node,
    ) -> Node {
        let _ = text;
        if get_encoded_root_length(&opts.file_name) == 0
            || opts.file_name != normalize_path(&opts.file_name)
        {
            panic!(
                "fileName should be normalized and absolute: {:?}",
                opts.file_name
            );
        }
        self.new_node(
            SyntaxKind::SourceFile,
            D::SourceFile(Box::new(ts_ast::SourceFileData {
                end_of_file_token: self.id(end_of_file_token),
                locals: ts_ast::SymbolTable,
                next_container: None,
                statements: self.req_list(statements),
                symbol: None,
                facts: 0,
            })),
        )
    }

    // Go: ast/ast.go:2987 NewCommentRange
    #[must_use]
    pub fn new_comment_range(
        &self,
        kind: SyntaxKind,
        pos: i32,
        end: i32,
        has_trailing_new_line: bool,
    ) -> CommentRange {
        CommentRange {
            text_range: TextRange::new(pos, end),
            kind,
            has_trailing_new_line,
        }
    }
}
