//! Package typeparser provides Effect type detection and parsing utilities.
// Go: internal/typeparser/packagejson.go

use crate::effect::typeparser::*;
use crate::modulespecifiers::host::ProgramHost;
use crate::modulespecifiers::types::ModuleSpecifierGenerationHost;
use crate::prelude::*;
use std::sync::Arc;

/// Go `*packagejson.PackageJson`. On a checker thread the Go program's
/// `GetPackageJsonInfo` is `ProgramHost::get_package_json_info`, whose entry
/// holds the contents in an `Arc`.
pub type PackageJsonRef = Arc<crate::modulespecifiers::packagejson::PackageJson>;

// Go: packageJsonProgram is an interface with GetSourceFileMetaData and
// GetPackageJsonInfo. The port's program has both: `get_source_file_meta_data`
// and `ProgramHost::get_package_json_info` (both read the current program of
// the thread, which is `tp.program`).

impl TypeParser<'_> {
    /// PackageJsonForSourceFile returns the nearest package.json contents for a source file, or nil.
    /// Results are cached per source file on EffectLinks for the checker's lifetime.
    pub fn package_json_for_source_file(&mut self, sf: Node) -> Option<PackageJsonRef> {
        if sf.is_nil() {
            return None;
        }

        cached!(self, package_json_for_source_file, sf, 'compute: {
            let meta = get_source_file_meta_data(&source_file_info(sf).path);
            if meta.package_json_directory.is_empty() {
                break 'compute None;
            }

            let package_json_path = crate::frontend::tspath::combine_paths(
                &meta.package_json_directory,
                &["package.json"],
            );
            let Some(info) = ProgramHost.get_package_json_info(&package_json_path) else {
                break 'compute None;
            };
            // Go: info.GetContents()
            info.contents.clone()
        })
    }
}
