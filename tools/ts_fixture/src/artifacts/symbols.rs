//! Pinned `.symbols` baseline selection.

use ts_ast::Node;

pub(crate) const EXTENSION: &str = ".symbols";

pub(crate) fn baseline_base(file_name: &str) -> Option<&str> {
    file_name.strip_suffix(EXTENSION)
}

pub(super) const fn includes(_node: &Node) -> bool {
    true
}

#[cfg(test)]
mod tests {
    use super::baseline_base;

    #[test]
    fn recognizes_configured_symbol_baselines_without_accepting_diffs() {
        assert_eq!(baseline_base("case.symbols"), Some("case"));
        assert_eq!(
            baseline_base("case(module=commonjs).symbols"),
            Some("case(module=commonjs)")
        );
        assert_eq!(baseline_base("case.symbols.diff"), None);
    }
}
