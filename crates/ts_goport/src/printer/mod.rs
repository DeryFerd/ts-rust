//! Go package `printer`. One file per ported Go range.

pub mod types;
pub mod text_writer;
pub mod single_line_writer;
pub mod emit_context;
pub mod name_generator;
// PORT: `factory` is not glob-exported. Its `NodeFactory` (Go
// `printer.NodeFactory`) would clash with `ast::NodeFactory` in the prelude.
pub mod factory;
pub mod utilities;
pub mod helpers;
pub mod printer_p1;
pub mod printer_p2;
pub mod printer_p3;
pub mod printer_p4;
pub mod printer_p5;

pub use types::*;
pub use text_writer::*;
pub use single_line_writer::*;
pub use emit_context::*;
pub use name_generator::*;
pub use utilities::*;
pub use helpers::*;
pub use printer_p1::*;
pub use printer_p2::*;
pub use printer_p3::*;
pub use printer_p4::*;
pub use printer_p5::*;
