//! Port of checker/printer.go: the checker entry points that print types,
//! symbols, signatures and type predicates through the node builder and the
//! printer.

use crate::prelude::*;
use crate::printer::{
    EmitContext, EmitTextWriter, PrintHandlers, Printer, PrinterOptions,
    get_single_line_string_writer, new_printer, new_text_writer,
};
use std::cell::Cell;

/// Go `VerbosityContext` (checker/nodebuilder.go). Hover code sets it; the
/// checker passes nil.
// PORT: Go passes `*VerbosityContext`, and the node builder writes
// `CanIncreaseVerbosity` and `Truncated` back through the pointer. Here the
// two output fields are shared cells, so a clone that the node builder keeps
// writes to the same place as the caller's value.
#[derive(Clone, Debug, Default)]
pub struct VerbosityContext {
    pub level: i32,
    pub max_truncation_length: i32,
    pub can_increase_verbosity: Rc<Cell<bool>>,
    pub truncated: Rc<Cell<bool>>,
}

// Go: checker/printer.go:13 createPrinterWithDefaults
pub fn create_printer_with_defaults(emit_context: Rc<EmitContext>) -> Printer {
    new_printer(
        PrinterOptions::default(),
        PrintHandlers::default(),
        Some(emit_context),
    )
}

// Go: checker/printer.go:17 createPrinterWithRemoveComments
pub fn create_printer_with_remove_comments(emit_context: Rc<EmitContext>) -> Printer {
    new_printer(
        PrinterOptions {
            remove_comments: true,
            ..Default::default()
        },
        PrintHandlers::default(),
        Some(emit_context),
    )
}

// Go: checker/printer.go:21 createPrinterWithRemoveCommentsOmitTrailingSemicolonNeverAsciiEscape
pub fn create_printer_with_remove_comments_omit_trailing_semicolon_never_ascii_escape(
    emit_context: Rc<EmitContext>,
) -> Printer {
    // TODO: OmitTrailingSemicolon support
    new_printer(
        PrinterOptions {
            remove_comments: true,
            never_ascii_escape: true,
            ..Default::default()
        },
        PrintHandlers::default(),
        Some(emit_context),
    )
}

// Go: checker/printer.go:29 createPrinterWithRemoveCommentsNeverAsciiEscape
pub fn create_printer_with_remove_comments_never_ascii_escape(
    emit_context: Rc<EmitContext>,
) -> Printer {
    new_printer(
        PrinterOptions {
            remove_comments: true,
            never_ascii_escape: true,
            ..Default::default()
        },
        PrintHandlers::default(),
        Some(emit_context),
    )
}

// Go: checker/printer.go:36 semicolonRemoverWriter
pub struct SemicolonRemoverWriter {
    has_pending_semicolon: bool,
    inner: Rc<RefCell<dyn EmitTextWriter>>,
}

impl SemicolonRemoverWriter {
    // Go: checker/printer.go:41 commitSemicolon
    fn commit_semicolon(&mut self) {
        if self.has_pending_semicolon {
            self.inner.borrow_mut().write_trailing_semicolon(";");
            self.has_pending_semicolon = false;
        }
    }
}

impl EmitTextWriter for SemicolonRemoverWriter {
    // Go: checker/printer.go:48 Clear
    fn clear(&mut self) {
        self.inner.borrow_mut().clear();
    }

    // Go: checker/printer.go:52 DecreaseIndent
    fn decrease_indent(&mut self) {
        self.commit_semicolon();
        self.inner.borrow_mut().decrease_indent();
    }

    // Go: checker/printer.go:57 GetColumn
    fn get_column(&self) -> i32 {
        self.inner.borrow().get_column()
    }

    // Go: checker/printer.go:61 GetIndent
    fn get_indent(&self) -> i32 {
        self.inner.borrow().get_indent()
    }

    // Go: checker/printer.go:65 GetLine
    fn get_line(&self) -> i32 {
        self.inner.borrow().get_line()
    }

    // Go: checker/printer.go:69 GetTextPos
    fn get_text_pos(&self) -> i32 {
        self.inner.borrow().get_text_pos()
    }

    // Go: checker/printer.go:73 HasTrailingComment
    fn has_trailing_comment(&self) -> bool {
        self.inner.borrow().has_trailing_comment()
    }

    // Go: checker/printer.go:77 HasTrailingWhitespace
    fn has_trailing_whitespace(&self) -> bool {
        self.inner.borrow().has_trailing_whitespace()
    }

    // Go: checker/printer.go:81 IncreaseIndent
    fn increase_indent(&mut self) {
        self.commit_semicolon();
        self.inner.borrow_mut().increase_indent();
    }

    // Go: checker/printer.go:86 IsAtStartOfLine
    fn is_at_start_of_line(&self) -> bool {
        self.inner.borrow().is_at_start_of_line()
    }

    // Go: checker/printer.go:90 RawWrite
    fn raw_write(&mut self, s1: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().raw_write(s1);
    }

    // Go: checker/printer.go:95 String
    // PORT: the trait method takes `&self`, so it cannot commit the pending
    // semicolon into the inner writer. It returns the text that Go returns
    // after the commit. A later write commits the semicolon, so the inner
    // writer ends with the same text as in Go. This assumes the inner
    // writer writes `text` for WriteTrailingSemicolon, as the Go writers do.
    fn string(&self) -> String {
        let mut text = self.inner.borrow().string();
        if self.has_pending_semicolon {
            // Go `WriteTrailingSemicolon(";")` on the inner writer writes ";".
            text.push(';');
        }
        text
    }

    // Go: checker/printer.go:100 Write
    fn write(&mut self, s1: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write(s1);
    }

    // Go: checker/printer.go:105 WriteComment
    fn write_comment(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_comment(text);
    }

    // Go: checker/printer.go:110 WriteKeyword
    fn write_keyword(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_keyword(text);
    }

    // Go: checker/printer.go:115 WriteLine
    fn write_line(&mut self) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_line();
    }

    // Go: checker/printer.go:120 WriteLineForce
    fn write_line_force(&mut self, force: bool) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_line_force(force);
    }

    // Go: checker/printer.go:125 WriteLiteral
    fn write_literal(&mut self, s1: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_literal(s1);
    }

    // Go: checker/printer.go:130 WriteOperator
    fn write_operator(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_operator(text);
    }

    // Go: checker/printer.go:135 WriteParameter
    fn write_parameter(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_parameter(text);
    }

    // Go: checker/printer.go:140 WriteProperty
    fn write_property(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_property(text);
    }

    // Go: checker/printer.go:145 WritePunctuation
    fn write_punctuation(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_punctuation(text);
    }

    // Go: checker/printer.go:150 WriteSpace
    fn write_space(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_space(text);
    }

    // Go: checker/printer.go:155 WriteStringLiteral
    fn write_string_literal(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_string_literal(text);
    }

    // Go: checker/printer.go:160 WriteSymbol
    fn write_symbol(&mut self, text: &str, symbol: SymbolId) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_symbol(text, symbol);
    }

    // Go: checker/printer.go:165 WriteTrailingSemicolon
    fn write_trailing_semicolon(&mut self, _text: &str) {
        self.has_pending_semicolon = true;
    }
}

// Go: checker/printer.go:169 getTrailingSemicolonDeferringWriter
pub fn get_trailing_semicolon_deferring_writer(
    writer: Rc<RefCell<dyn EmitTextWriter>>,
) -> Rc<RefCell<dyn EmitTextWriter>> {
    Rc::new(RefCell::new(SemicolonRemoverWriter {
        has_pending_semicolon: false,
        inner: writer,
    }))
}

// Go: checker/printer.go:181 toNodeBuilderFlags
pub fn to_node_builder_flags(flags: TypeFormatFlags) -> NodeBuilderFlags {
    NodeBuilderFlags((flags & TypeFormatFlags::NODE_BUILDER_FLAGS_MASK).0)
}

// PORT: Go `ast.GetSourceFileOfNode(enclosingDeclaration)` guarded by a nil
// check appears in every entry point. `get_source_file_of_node` panics on
// nil, so the guard is kept at each call through this helper.
fn source_file_of_enclosing(enclosing_declaration: Node) -> Node {
    if enclosing_declaration.is_some() {
        get_source_file_of_node(enclosing_declaration)
    } else {
        Node::NIL
    }
}

impl Checker {
    // Go: checker/printer.go:173 TypeToString
    pub fn type_to_string_exported(&mut self, t: TypeId) -> String {
        self.type_to_string_enclosing(t, Node::NIL)
    }

    /// Go `typeToString(t, nil)`. Calls that pass an enclosing declaration use
    /// `type_to_string_enclosing`.
    // PORT: Go has one `typeToString(t, enclosingDeclaration)`; the nil form is
    // split out so existing callers keep their signature.
    pub fn type_to_string(&mut self, t: TypeId) -> String {
        self.type_to_string_enclosing(t, Node::NIL)
    }

    // Go: checker/printer.go:177 typeToString
    pub fn type_to_string_enclosing(&mut self, t: TypeId, enclosing_declaration: Node) -> String {
        self.type_to_string_ex(
            t,
            enclosing_declaration,
            TypeFormatFlags::ALLOW_UNIQUE_ES_SYMBOL_TYPE
                | TypeFormatFlags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE,
            None,
        )
    }

    // Go: checker/printer.go:185 TypeToStringEx and checker/printer.go:189 typeToStringEx
    pub fn type_to_string_ex(
        &mut self,
        t: TypeId,
        enclosing_declaration: Node,
        flags: TypeFormatFlags,
        vc: Option<&VerbosityContext>,
    ) -> String {
        // Serialization of types can lead to (lazy) resolution of members, which can cause diagnostics that again require
        // serialization of types. This can potentially result in infinite recursion and stack overflows. To prevent that,
        // after a certain number of recursive invocations the function simply returns "?".
        if self.serialization_level >= MAX_SERIALIZATION_LEVEL {
            return "?".to_string();
        }
        let mut new_line = "";
        if flags.intersects(TypeFormatFlags::MULTILINE_OBJECT_LITERALS) {
            new_line = "\n";
        }
        let writer = Rc::new(RefCell::new(new_text_writer(new_line, 0)));
        let no_truncation = (vc.is_none_or(|vc| vc.max_truncation_length == 0)
            && self.compiler_options.no_error_truncation == Tristate::True)
            || flags.intersects(TypeFormatFlags::NO_TRUNCATION);
        let mut combined_flags = to_node_builder_flags(flags) | NodeBuilderFlags::IGNORE_ERRORS;
        if no_truncation {
            combined_flags = combined_flags | NodeBuilderFlags::NO_TRUNCATION;
        }
        // PORT: Go defers the release func from getNodeBuilder, which only lets
        // the factory free its arenas. Rust frees nodes by ownership, so there
        // is nothing to release.
        let node_builder = self.get_node_builder();
        let old_verbosity =
            std::mem::replace(&mut node_builder.borrow_mut().verbosity, vc.cloned());
        self.serialization_level += 1;
        let type_node = self.node_builder_type_to_type_node(
            &node_builder,
            t,
            enclosing_declaration,
            combined_flags,
            InternalNodeBuilderFlags::NONE,
            None,
        );
        self.serialization_level -= 1;
        // PORT: Go restores the verbosity in a defer at function exit. Nothing
        // below reads it, so it is restored here.
        node_builder.borrow_mut().verbosity = old_verbosity;
        if type_node.is_nil() {
            panic!("should always get typenode");
        }
        // The unresolved type gets a synthesized comment on `any` to hint to users that it's not a plain `any`.
        // Otherwise, we always strip comments out.
        let emit_context = node_builder.borrow().emit_context();
        let mut p = if t == self.unresolved_type {
            create_printer_with_defaults(emit_context)
        } else {
            create_printer_with_remove_comments(emit_context)
        };
        let source_file = source_file_of_enclosing(enclosing_declaration);
        p.write_exported(type_node, source_file, writer.clone(), None);
        let result = writer.borrow().string();

        let mut max_length = DEFAULT_MAXIMUM_TRUNCATION_LENGTH * 2;
        if let Some(vc) = vc {
            if vc.max_truncation_length > 0 {
                max_length = vc.max_truncation_length * 10; // hard cutoff matching Strada's absoluteMaximumLength
            }
        }
        if no_truncation {
            max_length = NO_TRUNCATION_MAXIMUM_TRUNCATION_LENGTH * 2;
        }
        // PORT: Go `len(result)` and the slice are byte based. The slice here
        // is byte based too, so it panics where Go would cut a UTF-8 sequence.
        // Go keeps the broken bytes; Rust `String` cannot hold them.
        let max_length = usize::try_from(max_length).unwrap_or(0);
        if max_length > 0 && !result.is_empty() && result.len() >= max_length {
            if let Some(vc) = vc {
                vc.truncated.set(true);
            }
            return result[0..max_length - "...".len()].to_string() + "...";
        }
        result
    }

    // Go: checker/printer.go:249 SymbolToString
    pub fn symbol_to_string_exported(&mut self, symbol: SymbolId) -> String {
        self.symbol_to_string(symbol)
    }

    // Go: checker/printer.go:253 symbolToString
    pub fn symbol_to_string(&mut self, symbol: SymbolId) -> String {
        self.symbol_to_string_ex(
            symbol,
            Node::NIL,
            SymbolFlags::ALL,
            SymbolFormatFlags::ALLOW_ANY_NODE_KIND,
        )
    }

    // Go: checker/printer.go:257 SymbolToStringEx and checker/printer.go:261 symbolToStringEx
    pub fn symbol_to_string_ex(
        &mut self,
        symbol: SymbolId,
        enclosing_declaration: Node,
        meaning: SymbolFlags,
        flags: SymbolFormatFlags,
    ) -> String {
        let writer = Rc::new(RefCell::new(get_single_line_string_writer()));

        let mut node_flags = NodeBuilderFlags::IGNORE_ERRORS;
        let mut internal_node_flags = InternalNodeBuilderFlags::NONE;
        if flags.intersects(SymbolFormatFlags::USE_ONLY_EXTERNAL_ALIASING) {
            node_flags = node_flags | NodeBuilderFlags::USE_ONLY_EXTERNAL_ALIASING;
        }
        if flags.intersects(SymbolFormatFlags::WRITE_TYPE_PARAMETERS_OR_ARGUMENTS) {
            node_flags = node_flags | NodeBuilderFlags::WRITE_TYPE_PARAMETERS_IN_QUALIFIED_NAME;
        }
        if flags.intersects(SymbolFormatFlags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE) {
            node_flags = node_flags | NodeBuilderFlags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE;
        }
        if flags.intersects(SymbolFormatFlags::DO_NOT_INCLUDE_SYMBOL_CHAIN) {
            internal_node_flags =
                internal_node_flags | InternalNodeBuilderFlags::DO_NOT_INCLUDE_SYMBOL_CHAIN;
        }
        if flags.intersects(SymbolFormatFlags::WRITE_COMPUTED_PROPS) {
            internal_node_flags =
                internal_node_flags | InternalNodeBuilderFlags::WRITE_COMPUTED_PROPS;
        }

        // PORT: see type_to_string_ex about the release func.
        let node_builder = self.get_node_builder();
        let source_file = source_file_of_enclosing(enclosing_declaration);
        let emit_context = node_builder.borrow().emit_context();
        // add neverAsciiEscape for GH#39027
        let mut printer_ = if enclosing_declaration.is_some()
            && enclosing_declaration.kind() == SyntaxKind::SourceFile
        {
            create_printer_with_remove_comments_never_ascii_escape(emit_context)
        } else {
            create_printer_with_remove_comments(emit_context)
        };

        let entity = if flags.intersects(SymbolFormatFlags::ALLOW_ANY_NODE_KIND) {
            self.node_builder_symbol_to_node(
                &node_builder,
                symbol,
                meaning,
                enclosing_declaration,
                node_flags,
                internal_node_flags,
                None,
            )
        } else {
            self.node_builder_symbol_to_entity_name(
                &node_builder,
                symbol,
                meaning,
                enclosing_declaration,
                node_flags,
                internal_node_flags,
                None,
            )
        }; // TODO: GH#18217
        let inner: Rc<RefCell<dyn EmitTextWriter>> = writer.clone();
        printer_.write_exported(
            entity,
            source_file,
            get_trailing_semicolon_deferring_writer(inner),
            None,
        ); // TODO: GH#18217
        let text = writer.borrow().string();
        text
    }

    // Go: checker/printer.go:311 signatureToString
    pub fn signature_to_string(&mut self, signature: SignatureId) -> String {
        self.signature_to_string_ex(signature, Node::NIL, TypeFormatFlags::NONE, None)
    }

    // Go: checker/printer.go:315 SignatureToStringEx and checker/printer.go:319 signatureToStringEx
    pub fn signature_to_string_ex(
        &mut self,
        signature: SignatureId,
        enclosing_declaration: Node,
        flags: TypeFormatFlags,
        vc: Option<&VerbosityContext>,
    ) -> String {
        let is_constructor = self
            .sig(signature)
            .flags
            .intersects(SignatureFlags::CONSTRUCT)
            && !flags.intersects(TypeFormatFlags::WRITE_CALL_STYLE_SIGNATURE);
        let sig_output = if flags.intersects(TypeFormatFlags::WRITE_ARROW_STYLE_SIGNATURE) {
            if is_constructor {
                SyntaxKind::ConstructorType
            } else {
                SyntaxKind::FunctionType
            }
        } else if is_constructor {
            SyntaxKind::ConstructSignature
        } else {
            SyntaxKind::CallSignature
        };

        // PORT: see type_to_string_ex about the release func.
        let node_builder = self.get_node_builder();
        let old_verbosity =
            std::mem::replace(&mut node_builder.borrow_mut().verbosity, vc.cloned());
        let combined_flags = to_node_builder_flags(flags)
            | NodeBuilderFlags::IGNORE_ERRORS
            | NodeBuilderFlags::WRITE_TYPE_PARAMETERS_IN_QUALIFIED_NAME;
        let sig = self.node_builder_signature_to_signature_declaration(
            &node_builder,
            signature,
            sig_output,
            enclosing_declaration,
            combined_flags,
            InternalNodeBuilderFlags::NONE,
            None,
        );
        // PORT: Go restores the verbosity in a defer; the printer below does
        // not read it.
        node_builder.borrow_mut().verbosity = old_verbosity;
        let emit_context = node_builder.borrow().emit_context();
        let mut p = create_printer_with_remove_comments_omit_trailing_semicolon_never_ascii_escape(
            emit_context,
        );
        let source_file = source_file_of_enclosing(enclosing_declaration);
        if flags.intersects(TypeFormatFlags::MULTILINE_OBJECT_LITERALS) {
            let writer = Rc::new(RefCell::new(new_text_writer("\n", 0)));
            let inner: Rc<RefCell<dyn EmitTextWriter>> = writer.clone();
            p.write_exported(
                sig,
                source_file,
                get_trailing_semicolon_deferring_writer(inner),
                None,
            );
            let text = writer.borrow().string();
            return text;
        }
        let writer = Rc::new(RefCell::new(get_single_line_string_writer()));
        let inner: Rc<RefCell<dyn EmitTextWriter>> = writer.clone();
        p.write_exported(
            sig,
            source_file,
            get_trailing_semicolon_deferring_writer(inner),
            None,
        );
        let text = writer.borrow().string();
        text
    }

    // Go: checker/printer.go:362 typePredicateToString
    pub fn type_predicate_to_string(&mut self, type_predicate: TypePredicateId) -> String {
        self.type_predicate_to_string_ex(
            type_predicate,
            Node::NIL,
            TypeFormatFlags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE,
        )
    }

    // Go: checker/printer.go:366 typePredicateToStringEx
    pub fn type_predicate_to_string_ex(
        &mut self,
        type_predicate: TypePredicateId,
        enclosing_declaration: Node,
        flags: TypeFormatFlags,
    ) -> String {
        let writer = Rc::new(RefCell::new(get_single_line_string_writer()));
        // PORT: see type_to_string_ex about the release func.
        let node_builder = self.get_node_builder();
        let combined_flags = to_node_builder_flags(flags)
            | NodeBuilderFlags::IGNORE_ERRORS
            | NodeBuilderFlags::WRITE_TYPE_PARAMETERS_IN_QUALIFIED_NAME;
        let predicate = self.node_builder_type_predicate_to_type_predicate_node(
            &node_builder,
            type_predicate,
            enclosing_declaration,
            combined_flags,
            InternalNodeBuilderFlags::NONE,
            None,
        ); // TODO: GH#18217
        let emit_context = node_builder.borrow().emit_context();
        let mut printer_ = create_printer_with_remove_comments(emit_context);
        let source_file = source_file_of_enclosing(enclosing_declaration);
        let inner: Rc<RefCell<dyn EmitTextWriter>> = writer.clone();
        printer_.write_exported(predicate, source_file, inner, None);
        let text = writer.borrow().string();
        text
    }

    // PORT: Go checker/printer.go:379 valueToString is a wrapper over
    // `ValueToString`; callers use the free fn `value_to_string`
    // (checker/utilities_p2.rs).

    // Go: checker/printer.go:383 formatUnionTypes
    pub fn format_union_types(&mut self, types: &[TypeId], expanding_enum: bool) -> Vec<TypeId> {
        let mut result = Vec::new();
        let mut flags = TypeFlags::NONE;
        let mut i = 0;
        while i < types.len() {
            let t = types[i];
            let t_flags = self.ty(t).flags;
            flags = flags | t_flags;
            if !t_flags.intersects(TypeFlags::NULLABLE) {
                if t_flags.intersects(TypeFlags::BOOLEAN_LITERAL)
                    || (!expanding_enum && t_flags.intersects(TypeFlags::ENUM_LIKE))
                {
                    let base_type = if t_flags.intersects(TypeFlags::BOOLEAN_LITERAL) {
                        self.boolean_type
                    } else {
                        self.get_base_type_of_enum_like_type(t)
                    };
                    if self.ty(base_type).flags.intersects(TypeFlags::UNION) {
                        // PORT: Go reads AsUnionType().types. Type.types() returns the same slice for a union.
                        let base_types = self.ty(base_type).types_list();
                        let count = base_types.len();
                        if i + count <= types.len()
                            && self.get_regular_type_of_literal_type(types[i + count - 1])
                                == self.get_regular_type_of_literal_type(base_types[count - 1])
                        {
                            result.push(base_type);
                            i += count;
                            continue;
                        }
                    }
                }
                result.push(t);
            }
            i += 1;
        }
        if flags.intersects(TypeFlags::NULL) {
            result.push(self.null_type);
        }
        if flags.intersects(TypeFlags::UNDEFINED) {
            result.push(self.undefined_type);
        }
        result
    }

    // Go: checker/printer.go:419 TypeToTypeNode
    // PORT: `_exported` suffix, because the node builder method
    // `typeToTypeNode` has the same snake name.
    pub fn type_to_type_node_exported(
        &mut self,
        t: TypeId,
        enclosing_declaration: Node,
        flags: NodeBuilderFlags,
        id_to_symbol: Option<FxHashMap<Node, SymbolId>>,
    ) -> Node {
        let node_builder = self.get_node_builder_ex(id_to_symbol);
        self.node_builder_type_to_type_node(
            &node_builder,
            t,
            enclosing_declaration,
            flags,
            InternalNodeBuilderFlags::NONE,
            None,
        )
    }

    // Go: checker/printer.go:424 SignatureToSignatureDeclaration
    // PORT: `_exported` suffix, as for type_to_type_node_exported.
    pub fn signature_to_signature_declaration_exported(
        &mut self,
        signature: SignatureId,
        kind: SyntaxKind,
        enclosing_declaration: Node,
        flags: NodeBuilderFlags,
    ) -> Node {
        // PORT: see type_to_string_ex about the release func.
        let node_builder = self.get_node_builder();
        self.node_builder_signature_to_signature_declaration(
            &node_builder,
            signature,
            kind,
            enclosing_declaration,
            flags,
            InternalNodeBuilderFlags::NONE,
            None,
        )
    }

    /// Produces declaration strings for a symbol with verbosity support for expandable hover.
    // Go: checker/printer.go:431 ExpandSymbolForHover
    // PORT: `_exported` suffix, because the node builder method
    // `expandSymbolForHover` has the same snake name.
    pub fn expand_symbol_for_hover_exported(
        &mut self,
        symbol: SymbolId,
        meaning: SymbolFlags,
        vc: Option<&VerbosityContext>,
    ) -> String {
        // PORT: see type_to_string_ex about the release func.
        let node_builder = self.get_node_builder();
        let old_verbosity =
            std::mem::replace(&mut node_builder.borrow_mut().verbosity, vc.cloned());
        let nodes = self.node_builder_expand_symbol_for_hover(&node_builder, symbol, meaning);
        let result = if nodes.is_empty() {
            String::new()
        } else {
            let emit_context = node_builder.borrow().emit_context();
            let mut p = create_printer_with_remove_comments(emit_context);
            let value_declaration = self.sym(symbol).value_declaration;
            let source_file = if value_declaration.is_some() {
                get_source_file_of_node(value_declaration)
            } else {
                Node::NIL
            };
            let mut b = String::new();
            for (i, node) in nodes.into_iter().enumerate() {
                if i > 0 {
                    b.push('\n');
                }
                b.push_str(&p.emit(node, source_file));
            }
            b
        };
        // PORT: Go restores the verbosity in a defer at function exit.
        node_builder.borrow_mut().verbosity = old_verbosity;
        result
    }

    /// Renders a type parameter declaration (e.g. "T extends Foo") with optional verbosity support.
    // Go: checker/printer.go:457 TypeParameterToStringEx
    pub fn type_parameter_to_string_ex(
        &mut self,
        t: TypeId,
        enclosing_declaration: Node,
        vc: Option<&VerbosityContext>,
    ) -> String {
        // PORT: see type_to_string_ex about the release func.
        let node_builder = self.get_node_builder();
        let old_verbosity =
            std::mem::replace(&mut node_builder.borrow_mut().verbosity, vc.cloned());
        let type_param_node = self.node_builder_type_parameter_to_declaration(
            &node_builder,
            t,
            enclosing_declaration,
            NodeBuilderFlags::IGNORE_ERRORS,
            InternalNodeBuilderFlags::NONE,
            None,
        );
        let result = if type_param_node.is_nil() {
            // PORT: Go calls TypeToString while the deferred verbosity restore
            // is still pending, so the node builder still holds `vc` here.
            self.type_to_string_exported(t)
        } else {
            let emit_context = node_builder.borrow().emit_context();
            let mut p = create_printer_with_remove_comments(emit_context);
            let source_file = source_file_of_enclosing(enclosing_declaration);
            p.emit(type_param_node, source_file)
        };
        node_builder.borrow_mut().verbosity = old_verbosity;
        result
    }

    // Go: checker/printer.go:476 TypeToTypeNodeEx
    pub fn type_to_type_node_ex_exported(
        &mut self,
        t: TypeId,
        enclosing_declaration: Node,
        flags: NodeBuilderFlags,
        internal_flags: InternalNodeBuilderFlags,
        id_to_symbol: Option<FxHashMap<Node, SymbolId>>,
    ) -> Node {
        let node_builder = self.get_node_builder_ex(id_to_symbol);
        self.node_builder_type_to_type_node(
            &node_builder,
            t,
            enclosing_declaration,
            flags,
            internal_flags,
            None,
        )
    }

    // Go: checker/printer.go:481 TypePredicateToTypePredicateNode
    // PORT: `_exported` suffix, as for type_to_type_node_exported.
    pub fn type_predicate_to_type_predicate_node_exported(
        &mut self,
        t: TypePredicateId,
        enclosing_declaration: Node,
        flags: NodeBuilderFlags,
        id_to_symbol: Option<FxHashMap<Node, SymbolId>>,
    ) -> Node {
        let node_builder = self.get_node_builder_ex(id_to_symbol);
        self.node_builder_type_predicate_to_type_predicate_node(
            &node_builder,
            t,
            enclosing_declaration,
            flags,
            InternalNodeBuilderFlags::NONE,
            None,
        )
    }
}
