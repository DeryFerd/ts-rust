//! Go: internal/testutil/contentmappertest/manifest.go (tsgo#4712).

use super::prelude::*;
use super::registry::{DYNAMIC_VERBATIM_MAPPER, TRANSFORMING_MAPPER};

// Go: manifest.go:5 PackageName
pub const PACKAGE_NAME: &str = "mapper";

// Go: manifest.go:8 PackageJSON
// PackageJSON returns a package manifest selecting the requested mapper.
pub fn package_json(mapper: &str) -> String {
    let mut compiler_options = "";
    let mut dynamic_config = "";
    if mapper == TRANSFORMING_MAPPER {
        compiler_options = r#", "compilerOptions": ["target", "jsx"]"#;
    }
    if mapper == DYNAMIC_VERBATIM_MAPPER {
        dynamic_config = r#", "dynamicConfig": true"#;
    }
    // Go `fmt.Sprintf` with `%q` for the name and the mapper.
    format!(
        "{{\n\t\"name\": {},\n\t\"version\": \"1.0.0\",\n\t\"typescript\": {{ \"contentMapper\": {{ \"exec\": [{}]{}{} }} }}\n}}",
        strconv::quote(PACKAGE_NAME),
        strconv::quote(mapper),
        compiler_options,
        dynamic_config
    )
}
