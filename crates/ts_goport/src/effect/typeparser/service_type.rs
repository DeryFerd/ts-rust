// Go: internal/typeparser/service_type.go

use crate::effect::typeparser::*;
use crate::prelude::*;

/// ServiceTypeId is the property key for the newer Context.Service variance struct.
pub const SERVICE_TYPE_ID: &str = "~effect/Context/Service";

/// Service represents parsed v4 service type parameters.
#[derive(Clone, Debug)]
pub struct Service {
    /// The service identifier/tag type
    pub identifier: TypeId,
    /// The service implementation shape
    pub shape: TypeId,
}

impl TypeParser<'_> {
    // Go: typeparser/service_type.go parseServiceVarianceStruct
    /// parseServiceVarianceStruct extracts Identifier and Shape from a Service variance struct type.
    pub fn parse_service_variance_struct(&mut self, t: TypeId) -> Option<Rc<Service>> {
        let identifier = self.extract_invariant_type(t, "_Identifier");
        if identifier.is_nil() {
            return None;
        }

        let shape = self.extract_invariant_type(t, "_Service");
        if shape.is_nil() {
            return None;
        }

        Some(Rc::new(Service { identifier, shape }))
    }

    // Go: typeparser/service_type.go ServiceType
    /// ServiceType parses a v4 service type and extracts Identifier, Shape parameters.
    /// Returns nil if the type is not a v4 service.
    pub fn service_type(&mut self, t: TypeId) -> Option<Rc<Service>> {
        if t.is_nil() {
            return None;
        }
        cached!(self, service_type, t, 'compute: {
            if self.detect_effect_version() != EffectMajorVersion::V4 {
                break 'compute None;
            }
            if !self.is_pipeable_type(t) {
                break 'compute None;
            }

            let service_key_type_id_type = self.get_type_of_property_by_name(t, SERVICE_TYPE_ID);
            if service_key_type_id_type.is_nil() {
                break 'compute None;
            }
            let identifier = self.get_type_of_property_by_name(t, "Identifier");
            if identifier.is_nil() {
                break 'compute None;
            }
            let shape = self.get_type_of_property_by_name(t, "Service");
            if shape.is_nil() {
                break 'compute None;
            }

            Some(Rc::new(Service { identifier, shape }))
        })
    }

    // Go: typeparser/service_type.go IsServiceType
    /// IsServiceType returns true if the type has the Service variance struct.
    pub fn is_service_type(&mut self, t: TypeId) -> bool {
        self.service_type(t).is_some()
    }
}
