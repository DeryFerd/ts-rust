//! Port of Go `sourcemap/source.go`.

use crate::prelude::*;

// Go: sourcemap/source.go:5 Source
// PORT: Go `ECMALineMap() []core.TextPos` returns `&[i32]`. A source file is
// the printer's `SourceMapSource::Node`; other sources (Go
// `compiler.declarationMapSource`, ts#63936) implement this trait.
pub trait Source {
    fn text(&self) -> &str;
    fn file_name(&self) -> &str;
    fn ecma_line_map(&self) -> &[i32];
}
