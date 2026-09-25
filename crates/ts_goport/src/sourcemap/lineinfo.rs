//! Port of Go `sourcemap/lineinfo.go`.

use crate::prelude::*;

// Go: sourcemap/lineinfo.go:5 ECMALineInfo
// PORT: Go `core.ECMALineStarts` is a slice of `core.TextPos`; here `Vec<i32>`.
#[derive(Clone, Debug, Default)]
pub struct ECMALineInfo {
    text: String,
    line_starts: Vec<i32>,
}

// Go: sourcemap/lineinfo.go:10 CreateECMALineInfo
#[must_use]
pub fn create_ecma_line_info(text: &str, line_starts: Vec<i32>) -> ECMALineInfo {
    ECMALineInfo {
        text: text.to_string(),
        line_starts,
    }
}

impl ECMALineInfo {
    // Go: sourcemap/lineinfo.go:17 LineCount
    #[must_use]
    pub fn line_count(&self) -> i32 {
        self.line_starts.len() as i32
    }

    // Go: sourcemap/lineinfo.go:21 LineText
    #[must_use]
    pub fn line_text(&self, line: i32) -> &str {
        let pos = self.line_starts[line as usize] as usize;
        let end = if ((line + 1) as usize) < self.line_starts.len() {
            self.line_starts[(line + 1) as usize] as usize
        } else {
            self.text.len()
        };
        &self.text[pos..end]
    }
}
