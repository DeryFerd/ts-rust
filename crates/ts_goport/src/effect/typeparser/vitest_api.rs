// Go: internal/typeparser/vitest_api.go

use crate::effect::typeparser::*;
use crate::prelude::*;
use std::sync::LazyLock;

pub static VITEST_RUNNER_PACKAGE_DESCRIPTOR: LazyLock<PackageSourceFileDescriptor> =
    LazyLock::new(|| new_package_source_file_descriptor("@vitest/runner", None));

pub static VITEST_PACKAGE_DESCRIPTOR: LazyLock<PackageSourceFileDescriptor> =
    LazyLock::new(|| new_package_source_file_descriptor("vitest", None));

pub static EFFECT_VITEST_PACKAGE_DESCRIPTOR: LazyLock<PackageSourceFileDescriptor> =
    LazyLock::new(|| new_package_source_file_descriptor("@effect/vitest", None));

impl TypeParser<'_> {
    /// IsNodeReferenceToVitestApi reports whether node resolves to a Vitest API.
    /// Vitest re-exports most test APIs from @vitest/runner, while global APIs are
    /// declared directly by the vitest package. The package fallback handles globals
    /// and Vitest 4 exports whose public names alias minified runner symbols.
    pub fn is_node_reference_to_vitest_api(&mut self, node: Node, member_name: &str) -> bool {
        if self.is_node_reference_to_module_export(
            node,
            &VITEST_RUNNER_PACKAGE_DESCRIPTOR,
            member_name,
        ) || self.is_node_reference_to_module_export(
            node,
            &VITEST_PACKAGE_DESCRIPTOR,
            member_name,
        ) {
            return true;
        }

        if reference_node_name(node) != member_name {
            return false;
        }
        self.is_node_reference_to_module(node, &VITEST_RUNNER_PACKAGE_DESCRIPTOR)
            || self.is_node_reference_to_module(node, &VITEST_PACKAGE_DESCRIPTOR)
    }

    /// IsNodeReferenceToEffectVitestApi reports whether node resolves to an API
    /// implemented by @effect/vitest rather than re-exported from Vitest.
    pub fn is_node_reference_to_effect_vitest_api(
        &mut self,
        node: Node,
        member_name: &str,
    ) -> bool {
        self.is_node_reference_to_module_export(
            node,
            &EFFECT_VITEST_PACKAGE_DESCRIPTOR,
            member_name,
        )
    }
}

pub fn reference_node_name(node: Node) -> &'static str {
    if node.is_nil() {
        return "";
    }
    match node.kind() {
        SyntaxKind::Identifier => return node.text(),
        SyntaxKind::PropertyAccessExpression => {
            let name = node.name();
            if name.is_some() {
                return name.text();
            }
        }
        _ => {}
    }
    ""
}
