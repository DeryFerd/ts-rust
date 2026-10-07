// Go: internal/typeparser/effect_yieldable_type.go

use crate::effect::typeparser::*;
use crate::prelude::*;

impl TypeParser<'_> {
    // Go: typeparser/effect_yieldable_type.go EffectYieldableType
    /// EffectYieldableType resolves both plain Effect types and yieldable wrappers
    /// that implement the asEffect() protocol.
    /// For v3: delegates directly to EffectType (v3 models yieldable through Effect subtyping).
    /// For v4: tries EffectType first; if that fails, looks for an asEffect property,
    /// checks if it's callable, and tries EffectType on the return type of each call signature.
    /// Returns nil if the type is not an Effect and not yieldable.
    pub fn effect_yieldable_type(&mut self, t: TypeId) -> Option<Rc<Effect>> {
        if t.is_nil() {
            return None;
        }
        cached!(self, effect_yieldable_type, t, 'compute: {
            let version = self.detect_effect_version();

            // For v3, yieldable types are modeled through Effect subtyping,
            // so EffectType alone is sufficient.
            if version != EffectMajorVersion::V4 {
                break 'compute self.effect_type(t);
            }

            // v4: first try plain Effect type
            if let Some(result) = self.effect_type(t) {
                break 'compute Some(result);
            }

            // v4: look for asEffect() protocol
            let as_effect_type = self.get_type_of_property_by_name(t, "asEffect");
            if as_effect_type.is_nil() {
                break 'compute None;
            }

            let signatures = self
                .checker
                .get_signatures_of_type_exported(as_effect_type, SignatureKind::CALL);
            for sig in signatures {
                let return_type = self.checker.get_return_type_of_signature_exported(sig);
                if return_type.is_nil() {
                    continue;
                }
                if let Some(result) = self.effect_type(return_type) {
                    break 'compute Some(result);
                }
            }

            None
        })
    }
}
