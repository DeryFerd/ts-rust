//! Port of Go `internal/transformers/declarations`: the declaration emit
//! transformer and the diagnostics it reports.

pub mod diagnostics;
pub mod tracker;
pub mod transform;
pub mod transform_p2;
pub mod transform_p3;
pub mod transform_p4;
pub mod util;

pub use diagnostics::*;
pub use tracker::*;
pub use transform::*;

use crate::prelude::*;
use crate::printer::EmitResolver;

// Go: transformers/declarations/transform.go:28 OutputPaths
pub trait OutputPaths {
    fn declaration_file_path(&self) -> String;
    fn js_file_path(&self) -> String;
}

// Go: transformers/declarations/transform.go:34 DeclarationEmitHost
// Used to be passed in the TransformationContext, which is now just an EmitContext
// PORT: Go embeds `modulespecifiers.ModuleSpecifierGenerationHost`. That
// interface is not ported, so its methods are not part of this trait yet.
pub trait DeclarationEmitHost {
    fn get_current_directory(&self) -> String;
    fn use_case_sensitive_file_names(&self) -> bool;
    /// `Node::NIL` is Go nil.
    fn get_source_file_from_reference(&self, origin: Node, r#ref: &FileReference) -> Node;

    fn get_output_paths_for(&self, file: Node, force_dts_paths: bool) -> Box<dyn OutputPaths>;
    fn get_resolution_mode_override(&self, node: Node) -> ResolutionMode;
    fn get_effective_declaration_flags(&self, node: Node, flags: ModifierFlags) -> ModifierFlags;
    fn get_emit_resolver(&self) -> Rc<dyn EmitResolver>;
}
