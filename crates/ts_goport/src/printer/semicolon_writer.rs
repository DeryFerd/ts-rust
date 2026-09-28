//! Port of Go `printer/semicolon_writer.go`.

use crate::prelude::*;

// Go: printer/semicolon_writer.go:8 trailingSemicolonDeferringWriter
pub(crate) struct TrailingSemicolonDeferringWriter {
    inner: Rc<RefCell<dyn EmitTextWriter>>,
    has_pending_semicolon: bool,
}

// Go: printer/semicolon_writer.go:13 getTrailingSemicolonDeferringWriter
pub(crate) fn get_trailing_semicolon_deferring_writer(
    writer: Rc<RefCell<dyn EmitTextWriter>>,
) -> Rc<RefCell<dyn EmitTextWriter>> {
    Rc::new(RefCell::new(TrailingSemicolonDeferringWriter {
        inner: writer,
        has_pending_semicolon: false,
    }))
}

impl TrailingSemicolonDeferringWriter {
    // Go: printer/semicolon_writer.go:17 commitSemicolon
    fn commit_semicolon(&mut self) {
        if self.has_pending_semicolon {
            self.inner.borrow_mut().write_trailing_semicolon(";");
            self.has_pending_semicolon = false;
        }
    }
}

impl EmitTextWriter for TrailingSemicolonDeferringWriter {
    // Go: printer/semicolon_writer.go:24 Write
    fn write(&mut self, s: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write(s);
    }

    // Go: printer/semicolon_writer.go:29 WriteTrailingSemicolon
    fn write_trailing_semicolon(&mut self, _text: &str) {
        self.has_pending_semicolon = true;
    }

    // Go: printer/semicolon_writer.go:33 WriteComment
    fn write_comment(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_comment(text);
    }

    // Go: printer/semicolon_writer.go:38 WriteKeyword
    fn write_keyword(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_keyword(text);
    }

    // Go: printer/semicolon_writer.go:43 WriteOperator
    fn write_operator(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_operator(text);
    }

    // Go: printer/semicolon_writer.go:48 WritePunctuation
    fn write_punctuation(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_punctuation(text);
    }

    // Go: printer/semicolon_writer.go:53 WriteSpace
    fn write_space(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_space(text);
    }

    // Go: printer/semicolon_writer.go:58 WriteStringLiteral
    fn write_string_literal(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_string_literal(text);
    }

    // Go: printer/semicolon_writer.go:63 WriteParameter
    fn write_parameter(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_parameter(text);
    }

    // Go: printer/semicolon_writer.go:68 WriteProperty
    fn write_property(&mut self, text: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_property(text);
    }

    // Go: printer/semicolon_writer.go:73 WriteSymbol
    fn write_symbol(&mut self, text: &str, symbol: SymbolId) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_symbol(text, symbol);
    }

    // Go: printer/semicolon_writer.go:78 WriteLine
    fn write_line(&mut self) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_line();
    }

    // Go: printer/semicolon_writer.go:83 WriteLineForce
    fn write_line_force(&mut self, force: bool) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_line_force(force);
    }

    // Go: printer/semicolon_writer.go:88 IncreaseIndent
    fn increase_indent(&mut self) {
        self.commit_semicolon();
        self.inner.borrow_mut().increase_indent();
    }

    // Go: printer/semicolon_writer.go:93 DecreaseIndent
    fn decrease_indent(&mut self) {
        self.commit_semicolon();
        self.inner.borrow_mut().decrease_indent();
    }

    // Go: printer/semicolon_writer.go:98 Clear
    fn clear(&mut self) {
        self.has_pending_semicolon = false;
        self.inner.borrow_mut().clear();
    }

    // Go: printer/semicolon_writer.go:103 String
    fn string(&self) -> String {
        self.inner.borrow().string()
    }

    // Go: printer/semicolon_writer.go:107 RawWrite
    fn raw_write(&mut self, s: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().raw_write(s);
    }

    // Go: printer/semicolon_writer.go:112 WriteLiteral
    fn write_literal(&mut self, s: &str) {
        self.commit_semicolon();
        self.inner.borrow_mut().write_literal(s);
    }

    // Go: printer/semicolon_writer.go:117 GetTextPos
    fn get_text_pos(&self) -> i32 {
        self.inner.borrow().get_text_pos()
    }

    // Go: printer/semicolon_writer.go:121 GetLine
    fn get_line(&self) -> i32 {
        self.inner.borrow().get_line()
    }

    // Go: printer/semicolon_writer.go:125 GetColumn
    fn get_column(&self) -> i32 {
        self.inner.borrow().get_column()
    }

    // Go: printer/semicolon_writer.go:129 GetIndent
    fn get_indent(&self) -> i32 {
        self.inner.borrow().get_indent()
    }

    // Go: printer/semicolon_writer.go:133 IsAtStartOfLine
    fn is_at_start_of_line(&self) -> bool {
        self.inner.borrow().is_at_start_of_line()
    }

    // Go: printer/semicolon_writer.go:137 HasTrailingComment
    fn has_trailing_comment(&self) -> bool {
        self.inner.borrow().has_trailing_comment()
    }

    // Go: printer/semicolon_writer.go:141 HasTrailingWhitespace
    fn has_trailing_whitespace(&self) -> bool {
        self.inner.borrow().has_trailing_whitespace()
    }
}
