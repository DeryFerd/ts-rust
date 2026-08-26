//! Syntax-neutral validation and consumer projections for exact callables.
//!
//! Callable families retain ownership of their syntax, binder provenance, and
//! publication protocol. This module only dispatches to those providers after
//! publication and normalizes the immutable views consumed by union/array
//! validation, type display, and signature relation. Keeping this boundary
//! free of `FunctionTypeNode` storage details lets later source-callable
//! providers participate without borrowing `FunctionType` provenance.

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost, SignatureId, TypeId,
    array_types::CanonicalArrayTargets,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set},
    functions::{
        FunctionTypeDisplayError, StoredFunctionTypeValidation, function_type_display_projection,
        validate_stored_function_type,
    },
    source_callables::{
        SourceCallableDisplayError, SourceCallableFamily, StoredSourceCallableValidation,
        source_callable_display_projection, stored_source_callable_family,
        validate_stored_source_callable,
    },
};

/// Provider family for an exact, independently validated callable object.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum CallableFamily {
    FunctionType,
    FunctionDeclaration,
    ArrowFunction,
    SourceFunctionOverloads,
    DeclaredCallSignatures,
}

impl From<SourceCallableFamily> for CallableFamily {
    fn from(family: SourceCallableFamily) -> Self {
        match family {
            SourceCallableFamily::FunctionDeclaration => Self::FunctionDeclaration,
            SourceCallableFamily::ArrowFunction => Self::ArrowFunction,
        }
    }
}

/// Immutable signature view consumed by structural relation.
///
/// The provider has already proved the owner, signature, and parameter caches.
/// A return type remains optional because an otherwise resolved callable may
/// still require its provider-specific lazy-return path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ValidatedSingleCallable {
    pub(super) owner: TypeId,
    pub(super) signature: SignatureId,
    pub(super) parameters: Vec<TypeId>,
    /// Raw final rest parameter type, kept separate from fixed positions.
    /// Providers may publish the canonical empty tuple to represent an
    /// exhausted contextual rest tail.
    pub(super) rest_parameter: Option<TypeId>,
    pub(super) min_argument_count: usize,
    pub(super) return_type: Option<TypeId>,
    pub(super) strict_variance_exempt: bool,
}

/// Store-only callable classification shared by cache validators and relation.
///
/// `edges` includes every semantic type dependency that the provider requires
/// graph validation to traverse. It is deliberately separate from the
/// relation projection: circular-return recovery, for example, retains an
/// annotation edge in addition to the signature's published return type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum StoredSingleCallableValidation {
    NotCallable,
    Pending {
        family: CallableFamily,
    },
    Valid {
        family: CallableFamily,
        callable: ValidatedSingleCallable,
        edges: Vec<TypeId>,
    },
    Malformed {
        family: CallableFamily,
    },
}

/// Syntax-neutral display data for one parameter of a validated single-call
/// signature. The semantic value type includes optional `undefined`; the
/// syntactic question mark remains an independent display fact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ValidatedSingleCallParameterDisplay {
    pub(super) name: String,
    pub(super) value_type: TypeId,
    pub(super) optional: bool,
}

/// Immutable display projection produced by a callable-family validator.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ValidatedSingleCallSignatureDisplay {
    pub(super) owner: TypeId,
    pub(super) parameters: Vec<ValidatedSingleCallParameterDisplay>,
    pub(super) return_type: Option<TypeId>,
}

/// Provider-specific reason that an admitted callable cannot be displayed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SingleCallableDisplayError {
    FunctionType(FunctionTypeDisplayError),
    SourceCallable(SourceCallableDisplayError),
}

/// Returns the installed provider brand without attempting cache validation.
///
/// Display uses this narrow query to preserve the distinction between a
/// branded provider value and an unbranded function-shaped object. Relation
/// and graph validation instead use [`validate_stored_single_callable`], which
/// deliberately detects malformed provider-shaped storage as well.
pub(super) fn single_callable_family(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<CallableFamily> {
    if super::instantiated_members::validate_instantiated_function_member_callable(store, type_)
        .is_some()
    {
        return Some(CallableFamily::FunctionType);
    }
    if store.type_has_function_type_provenance(type_) {
        Some(CallableFamily::FunctionType)
    } else {
        store
            .source_callable_provenance(type_)
            .map(|provenance| provenance.family.into())
    }
}

/// Validates an exact callable using only retained semantic-store state.
pub(super) fn validate_stored_single_callable(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> StoredSingleCallableValidation {
    match validate_stored_callable_set(store, type_) {
        StoredCallableSetValidation::NotCallable => StoredSingleCallableValidation::NotCallable,
        StoredCallableSetValidation::Pending { family } => {
            StoredSingleCallableValidation::Pending { family }
        }
        StoredCallableSetValidation::Malformed { family } => {
            StoredSingleCallableValidation::Malformed { family }
        }
        StoredCallableSetValidation::Valid {
            family,
            projection,
            edges,
        } => {
            if projection.owner != type_ {
                return StoredSingleCallableValidation::Malformed { family };
            }
            if !projection.construct_signatures.is_empty() || projection.call_signatures.len() != 1
            {
                return StoredSingleCallableValidation::NotCallable;
            }
            let mut call_signatures = projection.call_signatures.into_vec();
            let Some(callable) = call_signatures.pop() else {
                return StoredSingleCallableValidation::Malformed { family };
            };
            StoredSingleCallableValidation::Valid {
                family,
                callable,
                edges,
            }
        }
    }
}

/// Provider dispatch used by the ordered callable-set boundary.
///
/// This remains separate from [`validate_stored_single_callable`] so the
/// single-call compatibility adapter can consume a set without recursively
/// dispatching back into itself. New callable families join the set dispatcher
/// only after their own syntax, provenance, and publication caches are proven.
pub(super) fn validate_stored_single_callable_provider(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> StoredSingleCallableValidation {
    match validate_stored_function_type(store, type_) {
        StoredFunctionTypeValidation::NotFunctionType => {}
        StoredFunctionTypeValidation::Pending => {
            return StoredSingleCallableValidation::Pending {
                family: CallableFamily::FunctionType,
            };
        }
        StoredFunctionTypeValidation::Malformed => {
            return StoredSingleCallableValidation::Malformed {
                family: CallableFamily::FunctionType,
            };
        }
        StoredFunctionTypeValidation::Valid(edges) => {
            let Some(callable) = validated_single_callable(store, type_) else {
                return StoredSingleCallableValidation::Malformed {
                    family: CallableFamily::FunctionType,
                };
            };
            return StoredSingleCallableValidation::Valid {
                family: CallableFamily::FunctionType,
                callable,
                edges,
            };
        }
    }
    match validate_stored_source_callable(store, type_) {
        StoredSourceCallableValidation::NotSourceCallable => {
            StoredSingleCallableValidation::NotCallable
        }
        validation => {
            let Some(family) =
                stored_source_callable_family(store, type_).map(CallableFamily::from)
            else {
                return StoredSingleCallableValidation::NotCallable;
            };
            match validation {
                StoredSourceCallableValidation::NotSourceCallable => {
                    StoredSingleCallableValidation::NotCallable
                }
                StoredSourceCallableValidation::Pending => {
                    StoredSingleCallableValidation::Pending { family }
                }
                StoredSourceCallableValidation::Malformed => {
                    StoredSingleCallableValidation::Malformed { family }
                }
                StoredSourceCallableValidation::Valid(edges) => {
                    let Some(callable) = validated_single_callable(store, type_) else {
                        return StoredSingleCallableValidation::Malformed { family };
                    };
                    StoredSingleCallableValidation::Valid {
                        family,
                        callable,
                        edges,
                    }
                }
            }
        }
    }
}

/// Produces the display overlay for one branded callable provider.
pub(super) fn single_callable_display_projection(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_: TypeId,
    global_types: Option<&CanonicalGlobalTypes>,
) -> Result<Option<ValidatedSingleCallSignatureDisplay>, SingleCallableDisplayError> {
    if let Some(display) = super::instantiated_members::instantiated_function_member_display(
        store,
        host,
        type_,
        global_types.map(CanonicalArrayTargets::from_global_types),
    ) {
        return display
            .map(Some)
            .map_err(SingleCallableDisplayError::FunctionType);
    }
    let Some(family) = single_callable_family(store, type_) else {
        return Ok(None);
    };
    match family {
        CallableFamily::FunctionType => function_type_display_projection(
            store,
            host,
            type_,
            global_types.map(CanonicalArrayTargets::from_global_types),
        )
        .map(Some)
        .map_err(SingleCallableDisplayError::FunctionType),
        CallableFamily::FunctionDeclaration | CallableFamily::ArrowFunction => {
            source_callable_display_projection(
                store,
                host,
                type_,
                global_types.map(CanonicalArrayTargets::from_global_types),
            )
            .map(Some)
            .map_err(SingleCallableDisplayError::SourceCallable)
        }
        CallableFamily::SourceFunctionOverloads | CallableFamily::DeclaredCallSignatures => {
            Ok(None)
        }
    }
}

fn validated_single_callable(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<ValidatedSingleCallable> {
    let structured = store.type_payload(type_)?.data().structured()?;
    let [signature] = structured.signatures.as_deref()? else {
        return None;
    };
    let signature = *signature;
    let signature_record = store.signature(signature)?;
    let mut parameters = store
        .callable_signature_parameter_types(signature)?
        .to_vec();
    if parameters.len() != signature_record.parameters().len() {
        return None;
    }
    let rest_parameter = if signature_record.has_rest_parameter() {
        parameters.pop()
    } else {
        None
    };
    if signature_record.has_rest_parameter() && rest_parameter.is_none() {
        return None;
    }
    let min_argument_count = usize::try_from(signature_record.min_argument_count()).ok()?;
    Some(ValidatedSingleCallable {
        owner: type_,
        signature,
        parameters,
        rest_parameter,
        min_argument_count,
        return_type: signature_record.resolved_return_type(),
        // These exact source/type-node providers are neither methods nor constructors.
        strict_variance_exempt: false,
    })
}
