//! Standard-library identities created by the pinned `initializeChecker`.
//!
//! This module owns the dependency-closed initialization sequence after
//! ordinary globals and global-scope augmentations have been merged. Missing
//! or malformed required library declarations retain the pinned empty-type
//! fallback. Wrong-kind and wrong-arity records are exact; missing-name
//! records include the pinned eager-name library hints, while general spelling
//! suggestion elaboration remains a later checker-diagnostics capability.
//! Unsupported semantic dependencies fail construction instead of silently
//! changing a type identity.

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalNameResolutionError, SemanticSymbolId, SymbolFlags, SymbolTableId, resolve_global_name,
};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, TypeId, ValueSymbolLinks,
    declared::type_list_key,
    type_records::{TypeCacheState, TypeData},
    types::ObjectFlags,
};

const GLOBAL_TYPE_MUST_BE_CLASS_OR_INTERFACE: u32 = 2_316;
const GLOBAL_TYPE_MUST_HAVE_ARITY: u32 = 2_317;
const CANNOT_FIND_GLOBAL_TYPE: u32 = 2_318;
const ES2015_LIBRARY_SUGGESTION: &str = "es2015";

/// One diagnostic produced while resolving the pinned standard-library
/// identities. A missing global has no source node; wrong-kind and wrong-arity
/// diagnostics use the first class/interface/enum/type-alias declaration just
/// like `getGlobalTypeDeclaration` upstream.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalGlobalTypeDiagnostic {
    pub node: Option<NodeRef>,
    pub diagnostic: Diagnostic,
}

/// The eager standard-library identities installed by `initializeChecker`.
///
/// These IDs belong to the enclosing [`super::CanonicalCheckerContext`]. The
/// empty object/generic fallbacks are observable when a library is absent or
/// malformed, and [`Self::diagnostics`] records every required fallback.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalGlobalTypes {
    pub arguments_type: TypeId,
    pub global_this_value_type: TypeId,
    pub array_type: TypeId,
    pub object_type: TypeId,
    pub function_type: TypeId,
    pub callable_function_type: TypeId,
    pub newable_function_type: TypeId,
    pub string_type: TypeId,
    pub number_type: TypeId,
    pub boolean_type: TypeId,
    pub regexp_type: TypeId,
    pub any_array_type: TypeId,
    pub auto_array_type: TypeId,
    pub readonly_array_type: TypeId,
    pub any_readonly_array_type: TypeId,
    pub this_type: TypeId,
    diagnostics: Vec<CanonicalGlobalTypeDiagnostic>,
}

impl CanonicalGlobalTypes {
    /// Global fallback records in pinned initialization order.
    ///
    /// TS2316/TS2317 and the eager-name missing-library arguments are exact.
    /// General missing-name spelling suggestions remain a later diagnostics
    /// slice and currently retain the base TS2318 record.
    #[must_use]
    pub fn diagnostics(&self) -> &[CanonicalGlobalTypeDiagnostic] {
        &self.diagnostics
    }
}

/// An invariant or not-yet-ported semantic dependency that prevents exact
/// global-library initialization.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalGlobalTypeInitializationError {
    MissingBootstrap,
    InvalidGlobals(SymbolTableId),
    InvalidSymbol(SemanticSymbolId),
    InvalidType(TypeId),
    InvalidValueSymbolLinks(SemanticSymbolId),
    NameResolution(CanonicalNameResolutionError),
    DeclaredType(DeclaredTypeError),
    InvalidAnonymousType,
    InvalidAnonymousTypeMembers(TypeId),
    InvalidGenericTarget(TypeId),
    InvalidTypeReference(TypeId),
    InvalidInstantiationCache(TypeId),
}

impl std::fmt::Display for CanonicalGlobalTypeInitializationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingBootstrap => {
                formatter.write_str("global library types require intrinsic bootstrap")
            }
            Self::InvalidGlobals(_) => {
                formatter.write_str("global library types received a foreign globals table")
            }
            Self::InvalidSymbol(symbol) => {
                write!(
                    formatter,
                    "global library type references invalid symbol {symbol:?}"
                )
            }
            Self::InvalidType(type_id) => {
                write!(
                    formatter,
                    "global library initialization cannot read {type_id:?}"
                )
            }
            Self::InvalidValueSymbolLinks(symbol) => write!(
                formatter,
                "global library initialization cannot publish value links for {symbol:?}"
            ),
            Self::NameResolution(error) => write!(formatter, "{error}"),
            Self::DeclaredType(error) => write!(formatter, "{error}"),
            Self::InvalidAnonymousType => formatter
                .write_str("global library initialization cannot allocate an anonymous type"),
            Self::InvalidAnonymousTypeMembers(type_id) => write!(
                formatter,
                "global library anonymous type {type_id:?} rejected empty resolved members"
            ),
            Self::InvalidGenericTarget(type_id) => write!(
                formatter,
                "global library type {type_id:?} is not an initialized generic interface"
            ),
            Self::InvalidTypeReference(type_id) => write!(
                formatter,
                "global library initialization cannot create a reference to {type_id:?}"
            ),
            Self::InvalidInstantiationCache(type_id) => write!(
                formatter,
                "global library type {type_id:?} rejected its canonical instantiation"
            ),
        }
    }
}

impl std::error::Error for CanonicalGlobalTypeInitializationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::NameResolution(error) => Some(error),
            Self::DeclaredType(error) => Some(error),
            _ => None,
        }
    }
}

impl From<DeclaredTypeError> for CanonicalGlobalTypeInitializationError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<CanonicalNameResolutionError> for CanonicalGlobalTypeInitializationError {
    fn from(error: CanonicalNameResolutionError) -> Self {
        Self::NameResolution(error)
    }
}

#[derive(Clone, Copy)]
struct BootstrapTypes {
    globals: SymbolTableId,
    undefined_symbol: SemanticSymbolId,
    arguments_symbol: SemanticSymbolId,
    unknown_symbol: SemanticSymbolId,
    global_this_symbol: SemanticSymbolId,
    undefined_widening_type: TypeId,
    error_type: TypeId,
    any_type: TypeId,
    auto_type: TypeId,
    empty_object_type: TypeId,
    empty_generic_type: TypeId,
}

struct GlobalTypeResolver<'store, 'host, 'arena> {
    store: &'store mut CanonicalTypeMapperStore,
    host: &'host DeclaredTypeHost<'arena>,
    globals: SymbolTableId,
    empty_object_type: TypeId,
    empty_generic_type: TypeId,
    diagnostics: Vec<CanonicalGlobalTypeDiagnostic>,
}

impl GlobalTypeResolver<'_, '_, '_> {
    fn resolve(
        &mut self,
        name: &str,
        arity: usize,
        report_errors: bool,
    ) -> Result<TypeId, CanonicalGlobalTypeInitializationError> {
        if self.store.symbol_table(self.globals).is_none() {
            return Err(CanonicalGlobalTypeInitializationError::InvalidGlobals(
                self.globals,
            ));
        }
        let symbol = {
            let mut resolver_host = self.host.name_resolver_host(self.store)?;
            resolve_global_name(
                self.store.symbol_store(),
                &mut resolver_host,
                name,
                SymbolFlags::TYPE,
                None,
                false,
                false,
            )?
        };
        let Some(symbol) = symbol else {
            if report_errors {
                if matches!(name, "Array" | "RegExp" | "String") {
                    self.push_diagnostic(
                        None,
                        CANNOT_FIND_GLOBAL_TYPE,
                        [name.to_owned(), ES2015_LIBRARY_SUGGESTION.to_owned()],
                    );
                } else {
                    self.push_diagnostic(None, CANNOT_FIND_GLOBAL_TYPE, [name.to_owned()]);
                }
            }
            return Ok(self.fallback(arity));
        };
        let flags = self
            .store
            .symbol(symbol)
            .ok_or(CanonicalGlobalTypeInitializationError::InvalidSymbol(
                symbol,
            ))?
            .flags();
        if flags.intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE) {
            let declared_type = self.store.get_declared_type_of_symbol(self.host, symbol)?;
            let actual_arity = interface_arity(self.store, declared_type)?;
            if actual_arity == arity {
                return Ok(declared_type);
            }
            if report_errors {
                self.push_diagnostic(
                    global_type_declaration(self.store, self.host, symbol),
                    GLOBAL_TYPE_MUST_HAVE_ARITY,
                    [name.to_owned(), arity.to_string()],
                );
            }
            return Ok(self.fallback(arity));
        }

        if report_errors {
            self.push_diagnostic(
                global_type_declaration(self.store, self.host, symbol),
                GLOBAL_TYPE_MUST_BE_CLASS_OR_INTERFACE,
                [name.to_owned()],
            );
        }
        Ok(self.fallback(arity))
    }

    fn fallback(&self, arity: usize) -> TypeId {
        if arity == 0 {
            self.empty_object_type
        } else {
            self.empty_generic_type
        }
    }

    fn push_diagnostic<const N: usize>(
        &mut self,
        node: Option<NodeRef>,
        code: u32,
        arguments: [String; N],
    ) {
        let message = message_by_code(code).expect("pinned global diagnostic is in the catalog");
        self.diagnostics.push(CanonicalGlobalTypeDiagnostic {
            node,
            diagnostic: Diagnostic::with_arguments(message, arguments),
        });
    }
}

/// Ports the eager global-type portion of pinned `initializeChecker`.
pub(super) fn initialize_global_library_types(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: SymbolTableId,
    strict_bind_call_apply: bool,
) -> Result<CanonicalGlobalTypes, CanonicalGlobalTypeInitializationError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .map(|bootstrap| BootstrapTypes {
            globals: bootstrap.globals,
            undefined_symbol: bootstrap.undefined_symbol,
            arguments_symbol: bootstrap.arguments_symbol,
            unknown_symbol: bootstrap.unknown_symbol,
            global_this_symbol: bootstrap.global_this_symbol,
            undefined_widening_type: bootstrap.undefined_widening_type,
            error_type: bootstrap.error_type,
            any_type: bootstrap.any_type,
            auto_type: bootstrap.auto_type,
            empty_object_type: bootstrap.empty_object_type,
            empty_generic_type: bootstrap.empty_generic_type,
        })
        .ok_or(CanonicalGlobalTypeInitializationError::MissingBootstrap)?;
    if globals != bootstrap.globals {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGlobals(
            globals,
        ));
    }

    set_resolved_value_type(
        store,
        bootstrap.undefined_symbol,
        bootstrap.undefined_widening_type,
    )?;

    let mut resolver = GlobalTypeResolver {
        store,
        host,
        globals,
        empty_object_type: bootstrap.empty_object_type,
        empty_generic_type: bootstrap.empty_generic_type,
        diagnostics: Vec::new(),
    };
    let arguments_type = resolver.resolve("IArguments", 0, true)?;
    set_resolved_value_type(resolver.store, bootstrap.arguments_symbol, arguments_type)?;
    set_resolved_value_type(
        resolver.store,
        bootstrap.unknown_symbol,
        bootstrap.error_type,
    )?;
    let global_this_value_type = resolver
        .store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(bootstrap.global_this_symbol))
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidAnonymousType)?;
    set_resolved_value_type(
        resolver.store,
        bootstrap.global_this_symbol,
        global_this_value_type,
    )?;

    let array_type = resolver.resolve("Array", 1, true)?;
    let object_type = resolver.resolve("Object", 0, true)?;
    let function_type = resolver.resolve("Function", 0, true)?;
    let callable_function_type = if strict_bind_call_apply {
        resolver.resolve("CallableFunction", 0, true)?
    } else {
        function_type
    };
    let newable_function_type = if strict_bind_call_apply {
        resolver.resolve("NewableFunction", 0, true)?
    } else {
        function_type
    };
    let string_type = resolver.resolve("String", 0, true)?;
    let number_type = resolver.resolve("Number", 0, true)?;
    let boolean_type = resolver.resolve("Boolean", 0, true)?;
    let regexp_type = resolver.resolve("RegExp", 0, true)?;
    let any_array_type = create_type_from_generic_global_type(
        resolver.store,
        array_type,
        bootstrap.any_type,
        bootstrap.empty_generic_type,
        bootstrap.empty_object_type,
    )?;
    let mut auto_array_type = create_type_from_generic_global_type(
        resolver.store,
        array_type,
        bootstrap.auto_type,
        bootstrap.empty_generic_type,
        bootstrap.empty_object_type,
    )?;
    if auto_array_type == bootstrap.empty_object_type {
        auto_array_type = resolver
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .ok_or(CanonicalGlobalTypeInitializationError::InvalidAnonymousType)?;
        if !resolver.store.set_structured_type_members(
            auto_array_type,
            None,
            None,
            None,
            None,
            None,
        ) {
            return Err(
                CanonicalGlobalTypeInitializationError::InvalidAnonymousTypeMembers(
                    auto_array_type,
                ),
            );
        }
    }
    let mut readonly_array_type = resolver.resolve("ReadonlyArray", 1, false)?;
    if readonly_array_type == bootstrap.empty_generic_type {
        readonly_array_type = array_type;
    }
    let any_readonly_array_type = create_type_from_generic_global_type(
        resolver.store,
        readonly_array_type,
        bootstrap.any_type,
        bootstrap.empty_generic_type,
        bootstrap.empty_object_type,
    )?;
    let this_type = resolver.resolve("ThisType", 1, false)?;

    Ok(CanonicalGlobalTypes {
        arguments_type,
        global_this_value_type,
        array_type,
        object_type,
        function_type,
        callable_function_type,
        newable_function_type,
        string_type,
        number_type,
        boolean_type,
        regexp_type,
        any_array_type,
        auto_array_type,
        readonly_array_type,
        any_readonly_array_type,
        this_type,
        diagnostics: resolver.diagnostics,
    })
}

fn interface_arity(
    store: &CanonicalTypeMapperStore,
    type_id: TypeId,
) -> Result<usize, CanonicalGlobalTypeInitializationError> {
    let record = store
        .type_payload(type_id)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidType(type_id))?;
    let TypeData::Interface(interface) = record.data() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidType(type_id));
    };
    Ok(interface
        .all_type_parameters
        .as_ref()
        .map_or(0, |parameters| parameters.len() - 1))
}

fn global_type_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Option<NodeRef> {
    store
        .symbol(symbol)?
        .declarations()?
        .iter()
        .copied()
        .find(|declaration| {
            host.node(*declaration).is_some_and(|node| {
                matches!(
                    node.kind,
                    SyntaxKind::ClassDeclaration
                        | SyntaxKind::InterfaceDeclaration
                        | SyntaxKind::EnumDeclaration
                        | SyntaxKind::TypeAliasDeclaration
                )
            })
        })
}

fn set_resolved_value_type(
    store: &mut CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    resolved_type: TypeId,
) -> Result<(), CanonicalGlobalTypeInitializationError> {
    let mut links = store
        .value_symbol_links(symbol)
        .cloned()
        .unwrap_or_else(ValueSymbolLinks::default);
    links.resolved_type = Some(resolved_type);
    if store.set_value_symbol_links(symbol, links) {
        Ok(())
    } else {
        Err(CanonicalGlobalTypeInitializationError::InvalidValueSymbolLinks(symbol))
    }
}

fn create_type_from_generic_global_type(
    store: &mut CanonicalTypeMapperStore,
    target: TypeId,
    type_argument: TypeId,
    empty_generic_type: TypeId,
    empty_object_type: TypeId,
) -> Result<TypeId, CanonicalGlobalTypeInitializationError> {
    if target == empty_generic_type {
        return Ok(empty_object_type);
    }

    let key = type_list_key(&[type_argument]);
    let target_record = store
        .type_payload(target)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidType(target))?;
    let TypeData::Interface(interface) = target_record.data() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let TypeCacheState::Allocated(instantiations) = &interface.reference.object.instantiations
    else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    if let Some(existing) = instantiations.get(&key) {
        return Ok(*existing);
    }
    let symbol = target_record.symbol();
    let argument_flags = store
        .type_payload(type_argument)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidType(
            type_argument,
        ))?
        .object_flags()
        & ObjectFlags::PROPAGATING_FLAGS;
    let reference = store
        .alloc_type_reference(argument_flags, symbol)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidTypeReference(target))?;
    if !store.set_object_target_and_mapper(reference, Some(target), None)
        || !store.set_type_reference_resolution(reference, None, Some(vec![type_argument]))
    {
        return Err(CanonicalGlobalTypeInitializationError::InvalidTypeReference(target));
    }
    store
        .insert_object_instantiation(target, key, reference)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target))
}
