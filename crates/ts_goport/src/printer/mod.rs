//! Go package `printer`. One file per ported Go range.

pub mod emit_context;
pub mod name_generator;
pub mod single_line_writer;
pub mod text_writer;
pub mod types;
// PORT: `factory` is not glob-exported. Its `NodeFactory` (Go
// `printer.NodeFactory`) would clash with `ast::NodeFactory` in the prelude.
pub mod change_tracker_writer;
pub mod factory;
pub mod helpers;
pub mod printer_p1;
pub mod printer_p2;
pub mod printer_p3;
pub mod printer_p4;
pub mod printer_p5;
// PORT: not glob-exported. Its Go names are unexported, and the checker
// still has its own `get_trailing_semicolon_deferring_writer` until the
// checker lane ports its part of tsgo#3949.
pub mod semicolon_writer;
pub mod syntheticfile;
pub mod utilities;

pub use change_tracker_writer::*;
pub use emit_context::*;
pub use helpers::*;
pub use name_generator::*;
pub use printer_p1::*;
pub use printer_p2::*;
pub use printer_p3::*;
pub use printer_p4::*;
pub use printer_p5::*;
pub use single_line_writer::*;
pub use syntheticfile::*;
pub use text_writer::*;
pub use types::*;
pub use utilities::*;
