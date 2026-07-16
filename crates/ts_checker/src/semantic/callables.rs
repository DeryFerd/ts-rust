//! Syntax-neutral validation and consumer projections for exact callables.
//!
//! Callable families retain ownership of their syntax, binder provenance, and
//! publication protocol. This module only dispatches to those providers after
//! publication and normalizes the immutable views consumed by union/array
//! validation, type display, and signature relation. Keeping this boundary
//! free of `FunctionTypeNode` storage details lets later source-callable
//! providers participate without borrowing FunctionType provenance.

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost, SignatureId, TypeId,
    array_types::CanonicalArrayTargets,
    functions::{
        FunctionTypeDisplayError, StoredFunctionTypeValidation, function_type_display_projection,
        validate_stored_function_type,
    },
};

/// Provider family for an exact, independently validated callable object.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum CallableFamily {
    FunctionType,
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
    store
        .type_has_function_type_provenance(type_)
        .then_some(CallableFamily::FunctionType)
}

/// Validates an exact callable using only retained semantic-store state.
pub(super) fn validate_stored_single_callable(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> StoredSingleCallableValidation {
    const FAMILY: CallableFamily = CallableFamily::FunctionType;
    match validate_stored_function_type(store, type_) {
        StoredFunctionTypeValidation::NotFunctionType => {
            StoredSingleCallableValidation::NotCallable
        }
        StoredFunctionTypeValidation::Pending => {
            StoredSingleCallableValidation::Pending { family: FAMILY }
        }
        StoredFunctionTypeValidation::Malformed => {
            StoredSingleCallableValidation::Malformed { family: FAMILY }
        }
        StoredFunctionTypeValidation::Valid(edges) => {
            let Some(callable) = validated_function_type_callable(store, type_) else {
                return StoredSingleCallableValidation::Malformed { family: FAMILY };
            };
            StoredSingleCallableValidation::Valid {
                family: FAMILY,
                callable,
                edges,
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
    }
}

fn validated_function_type_callable(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<ValidatedSingleCallable> {
    let structured = store.type_payload(type_)?.data().structured()?;
    let [signature] = structured.signatures.as_deref()? else {
        return None;
    };
    let signature = *signature;
    let signature_record = store.signature(signature)?;
    let parameters = signature_record
        .parameters()
        .iter()
        .map(|parameter| {
            store
                .value_symbol_links(*parameter)
                .and_then(|links| links.resolved_type)
        })
        .collect::<Option<Vec<_>>>()?;
    let min_argument_count = usize::try_from(signature_record.min_argument_count()).ok()?;
    Some(ValidatedSingleCallable {
        owner: type_,
        signature,
        parameters,
        min_argument_count,
        return_type: signature_record.resolved_return_type(),
        // FunctionTypeNode declarations are neither methods nor constructors.
        strict_variance_exempt: false,
    })
}
