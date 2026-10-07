// Go: internal/typeparser/yieldable_error.go

use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: sourceFileProgram is a local interface for accessing program source
// files (`SourceFiles() []*ast.SourceFile`). The port's program always has
// it: `GoProgram::source_files`.

impl TypeParser<'_> {
    /// IsYieldableErrorType reports whether the given type is assignable to Cause.YieldableError
    /// from the "effect" package. Returns false for never and any types.
    pub fn is_yieldable_error_type(&mut self, t: TypeId) -> bool {
        if t.is_nil() {
            return false;
        }
        cached!(self, is_yieldable_error_type, t, 'compute: {
            // never is assignable to everything, so we need to exclude it
            if self.checker.ty(t).flags().intersects(TypeFlags::NEVER) {
                break 'compute false;
            }
            // any is assignable to everything, so we need to exclude it
            if self.checker.ty(t).flags().intersects(TypeFlags::ANY) {
                break 'compute false;
            }

            let source_files: Vec<Node> =
                self.program.source_files().map(|file| file.root).collect();

            for sf in source_files {
                if sf.is_nil() {
                    continue;
                }

                // Check this source file belongs to the "effect" package
                let Some(pkg) = self.package_json_for_source_file(sf) else {
                    continue;
                };
                let (name, ok) = pkg.fields.name.get_value();
                if !ok || !crate::frontend::vfs::vfsmatch::equal_fold(name.as_bytes(), b"effect") {
                    continue;
                }

                let module_sym = self.checker.get_symbol_of_declaration(sf);
                if module_sym.is_nil() {
                    continue;
                }

                // Look for the YieldableError export
                let mut export_sym = self
                    .checker
                    .try_get_member_in_module_exports_and_properties("YieldableError", module_sym);
                if export_sym.is_nil() {
                    continue;
                }

                // Verify this is the Cause module by checking for a Cause export
                let cause_sym = self
                    .checker
                    .try_get_member_in_module_exports_and_properties("Cause", module_sym);
                if cause_sym.is_nil() {
                    continue;
                }

                export_sym = self.resolve_aliased_symbol(export_sym);
                if export_sym.is_nil() {
                    continue;
                }

                let yieldable_error_type = self
                    .checker
                    .get_declared_type_of_symbol_exported(export_sym);
                if yieldable_error_type.is_nil() {
                    continue;
                }

                if self.checker.is_type_assignable_to(t, yieldable_error_type) {
                    break 'compute true;
                }
            }

            false
        })
    }
}
