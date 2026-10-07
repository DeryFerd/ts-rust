// Go: internal/typeparser/scope_type.go

use crate::effect::typeparser::*;
use crate::prelude::*;

/// ScopeTypeId is the property key for Scope's variance struct.
pub const SCOPE_TYPE_ID: &str = "~effect/Scope";

impl TypeParser<'_> {
    // Go: typeparser/scope_type.go IsScopeType
    /// IsScopeType returns true if the type is an Effect Scope type.
    /// For v4, this checks for the "~effect/Scope" computed property.
    /// For v3/unknown, this checks that the type is "pipeable" (has a callable pipe property)
    /// and that any required non-optional property's symbol name contains "ScopeTypeId".
    pub fn is_scope_type(&mut self, t: TypeId) -> bool {
        if t.is_nil() {
            return false;
        }
        cached!(self, is_scope_type, t, 'compute: {
            let version = self.detect_effect_version();
            if version == EffectMajorVersion::V4 {
                break 'compute self
                    .get_type_of_property_by_name(t, SCOPE_TYPE_ID)
                    .is_some();
            }

            // v3 / unknown: check that the type is "pipeable"
            let pipe_type = self.get_type_of_property_by_name(t, "pipe");
            if pipe_type.is_nil() {
                break 'compute false;
            }
            let signatures = self
                .checker
                .get_signatures_of_type_exported(pipe_type, SignatureKind::CALL);
            if signatures.is_empty() {
                break 'compute false;
            }

            // Check if any required non-optional property's symbol name contains "ScopeTypeId"
            for prop in self.checker.get_properties_of_type_exported(t) {
                if prop.is_nil() {
                    continue;
                }
                let s = self.checker.sym(prop);
                if !s.flags.intersects(SymbolFlags::PROPERTY) {
                    continue;
                }
                if s.flags.intersects(SymbolFlags::OPTIONAL) {
                    continue;
                }
                if s.value_declaration.is_nil() {
                    continue;
                }
                if s.name.as_str().contains("ScopeTypeId") {
                    break 'compute true;
                }
            }

            false
        })
    }
}
