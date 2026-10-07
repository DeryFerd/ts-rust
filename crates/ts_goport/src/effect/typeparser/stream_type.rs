// Go: internal/typeparser/stream_type.go

use crate::effect::typeparser::*;
use crate::prelude::*;

/// StreamTypeId is the property key for Stream's variance struct.
pub const STREAM_TYPE_ID: &str = "~effect/Stream";

impl TypeParser<'_> {
    /// StreamType parses a Stream type and extracts A, E, R parameters.
    /// For v3, Stream carries the Effect variance struct, so this delegates to EffectType.
    pub fn stream_type(&mut self, t: TypeId) -> Option<Rc<Effect>> {
        if t.is_nil() {
            return None;
        }
        cached!(self, stream_type, t, 'compute: {
            if self.detect_effect_version() != EffectMajorVersion::V4 {
                break 'compute self.effect_type(t);
            }

            let variance_struct_type = self.get_type_of_property_by_name(t, STREAM_TYPE_ID);
            if variance_struct_type.is_nil() {
                break 'compute None;
            }
            self.parse_variance_struct(variance_struct_type)
        })
    }
}
