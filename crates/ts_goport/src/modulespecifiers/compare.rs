//! Port of modulespecifiers/compare.go.

use crate::prelude::*;

// Go: modulespecifiers/compare.go:7 CountPathComponents
pub fn count_path_components(path: &str) -> usize {
    let mut initial = 0;
    if path.starts_with("./") {
        initial = 2;
    }
    path[initial..].matches('/').count()
}
