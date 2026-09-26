//! Port of Go `sourcemap/source.go`.

use crate::prelude::*;

// Go: sourcemap/source.go:5 Source
// PORT: Go `ECMALineMap() []core.TextPos` returns `&[i32]`. The printer port
// passes the source file `Node` directly (`Printer.source_map_source`), so no
// type implements this trait yet.
pub trait Source {
    fn text(&self) -> &str;
    fn file_name(&self) -> &str;
    fn ecma_line_map(&self) -> &[i32];
}
