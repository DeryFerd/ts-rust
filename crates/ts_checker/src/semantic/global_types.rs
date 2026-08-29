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

use std::collections::HashSet;

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalNameResolutionError, SemanticSymbolId, SymbolFlags, SymbolTableId, resolve_global_name,
};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, TypeId, ValueSymbolLinks,
    declared::{cached_ordinary_type_parameter_owner, type_list_key},
    store::SourceNodeParent,
    type_records::{TypeCacheState, TypeData},
    types::{ObjectFlags, TypeFlags},
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

/// A demanded global and the source proof retained with its diagnostics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ResolvedGlobalType {
    type_: TypeId,
    diagnostics: Vec<CanonicalGlobalTypeDiagnostic>,
    proof: RequiredGlobalTypeProof,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RequiredGlobalTypeProof {
    globals: SymbolTableId,
    name: String,
    arity: usize,
    symbol: Option<RequiredGlobalSymbolProof>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RequiredGlobalSymbolProof {
    symbol: SemanticSymbolId,
    flags: SymbolFlags,
    declarations: Vec<NodeRef>,
    declared_type: Option<TypeId>,
}

impl ResolvedGlobalType {
    pub(super) const fn type_(&self) -> TypeId {
        self.type_
    }

    pub(super) fn diagnostics(&self) -> &[CanonicalGlobalTypeDiagnostic] {
        &self.diagnostics
    }

    pub(super) fn is_for(&self, name: &str, arity: usize) -> bool {
        self.proof.name == name && self.proof.arity == arity
    }

    pub(super) fn validate(
        &self,
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
    ) -> Result<(), CanonicalGlobalTypeInitializationError> {
        if store.type_payload(self.type_).is_none()
            || self.proof
                != required_global_type_proof(store, host, &self.proof.name, self.proof.arity)?
        {
            return Err(CanonicalGlobalTypeInitializationError::InvalidType(
                self.type_,
            ));
        }
        Ok(())
    }
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
    InvalidGlobalObjectDeclaration(NodeRef),
    InvalidGlobalObjectBaseResolution(TypeId),
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
            Self::InvalidGlobalObjectDeclaration(declaration) => write!(
                formatter,
                "global Object base resolution cannot validate declaration {declaration:?}"
            ),
            Self::InvalidGlobalObjectBaseResolution(type_id) => write!(
                formatter,
                "global Object type {type_id:?} has contradictory base-resolution state"
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum GlobalObjectNoBasePlan {
    NoPublish,
    Publish(TypeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum GlobalObjectBaseResolutionState {
    Cold,
    NoBases,
    ResolvedBases,
    Invalid,
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
    let global_object_no_base_plan = preflight_global_object_no_base(
        resolver.store,
        resolver.host,
        resolver.globals,
        object_type,
    )?;
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
        ObjectFlags::NONE,
    )?;
    let mut auto_array_type = create_type_from_generic_global_type(
        resolver.store,
        array_type,
        bootstrap.auto_type,
        ObjectFlags::NONE,
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
        ObjectFlags::NONE,
    )?;
    let this_type = resolver.resolve("ThisType", 1, false)?;

    commit_global_object_no_base(resolver.store, global_object_no_base_plan)?;

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

/// Checks the optional `Iterable` declaration and cache without creating types.
pub(super) fn global_iterable_type_requires_protocol(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
) -> Result<bool, CanonicalGlobalTypeInitializationError> {
    optional_global_type_has_arity(store, host, "Iterable", 3)
}

/// Validates an optional global identity without publishing declaration caches.
pub(super) fn optional_global_type_has_arity(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    name: &str,
    expected_arity: usize,
) -> Result<bool, CanonicalGlobalTypeInitializationError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(CanonicalGlobalTypeInitializationError::MissingBootstrap)?;
    if store.symbol_table(bootstrap.globals).is_none() {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGlobals(
            bootstrap.globals,
        ));
    }
    let symbol = {
        let mut resolver_host = host.name_resolver_host(store)?;
        resolve_global_name(
            store.symbol_store(),
            &mut resolver_host,
            name,
            SymbolFlags::TYPE,
            None,
            false,
            false,
        )?
    };
    let Some(symbol) = symbol else {
        return Ok(false);
    };
    let symbol = store.get_merged_symbol(symbol).ok_or(
        CanonicalGlobalTypeInitializationError::InvalidSymbol(symbol),
    )?;
    let record =
        store
            .symbol(symbol)
            .ok_or(CanonicalGlobalTypeInitializationError::InvalidSymbol(
                symbol,
            ))?;
    let flags = record.flags();
    if !flags.intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE) {
        return Ok(false);
    }
    if super::declared::malformed_alias_merge(flags) {
        return Err(DeclaredTypeError::Unavailable(
            super::declared::DeclaredTypeUnavailable::AliasMergedWithDeclaredSymbol(symbol),
        )
        .into());
    }
    let arity =
        super::declared::preflight_class_or_interface_reference(store, host, symbol, flags)?;
    let declarations = record
        .declarations()
        .filter(|declarations| !declarations.is_empty())
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidSymbol(
            symbol,
        ))?;
    let mut checked = HashSet::new();
    let mut parameters = HashSet::new();
    let mut has_class = false;
    let mut has_interface = false;
    for declaration in declarations {
        let node = super::declared::preflight_node(store, host, *declaration)?;
        if !host.symbol_matches(store, *declaration, symbol) {
            return Err(CanonicalGlobalTypeInitializationError::InvalidSymbol(
                symbol,
            ));
        }
        let declared_parameters = match &node.data {
            NodeData::ClassDeclaration(data) if node.kind == SyntaxKind::ClassDeclaration => {
                has_class = true;
                data.type_parameters.as_ref()
            }
            NodeData::ClassExpression(data) if node.kind == SyntaxKind::ClassExpression => {
                has_class = true;
                data.type_parameters.as_ref()
            }
            NodeData::InterfaceDeclaration(data)
                if node.kind == SyntaxKind::InterfaceDeclaration =>
            {
                has_interface = true;
                data.type_parameters.as_ref()
            }
            NodeData::TypeAliasDeclaration(_) => {
                return Err(CanonicalGlobalTypeInitializationError::InvalidSymbol(
                    symbol,
                ));
            }
            _ if matches!(
                node.kind,
                SyntaxKind::ClassDeclaration
                    | SyntaxKind::ClassExpression
                    | SyntaxKind::InterfaceDeclaration
            ) =>
            {
                return Err(CanonicalGlobalTypeInitializationError::InvalidSymbol(
                    symbol,
                ));
            }
            _ => continue,
        };
        parameters.extend(super::declared::explicit_type_parameter_symbols(
            store,
            host,
            *declaration,
            declared_parameters,
            &mut checked,
        )?);
    }
    let cached_arity = store
        .declared_type_links(symbol)
        .and_then(|links| links.declared_type)
        .map(|type_| interface_arity(store, type_))
        .transpose()?;
    if flags.contains(SymbolFlags::CLASS) != has_class
        || !has_class && !has_interface
        || arity != parameters.len()
        || cached_arity.is_some_and(|cached| cached != parameters.len())
    {
        return Err(CanonicalGlobalTypeInitializationError::InvalidSymbol(
            symbol,
        ));
    }
    Ok(arity == expected_arity)
}

/// Resolves an optional global through the same kind and arity rules as initialization.
pub(super) fn resolve_optional_global_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    name: &str,
    arity: usize,
) -> Result<Option<TypeId>, CanonicalGlobalTypeInitializationError> {
    if !optional_global_type_has_arity(store, host, name, arity)? {
        return Ok(None);
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(CanonicalGlobalTypeInitializationError::MissingBootstrap)?;
    let mut resolver = GlobalTypeResolver {
        globals: bootstrap.globals,
        empty_object_type: bootstrap.empty_object_type,
        empty_generic_type: bootstrap.empty_generic_type,
        store,
        host,
        diagnostics: Vec::new(),
    };
    resolver.resolve(name, arity, false).map(Some)
}

/// Uses the ordinary global resolver and retains proof for a lazy required demand.
pub(super) fn resolve_required_global_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    name: &str,
    arity: usize,
) -> Result<ResolvedGlobalType, CanonicalGlobalTypeInitializationError> {
    let before = required_global_type_proof(store, host, name, arity)?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(CanonicalGlobalTypeInitializationError::MissingBootstrap)?;
    let mut resolver = GlobalTypeResolver {
        globals: bootstrap.globals,
        empty_object_type: bootstrap.empty_object_type,
        empty_generic_type: bootstrap.empty_generic_type,
        store,
        host,
        diagnostics: Vec::new(),
    };
    let type_ = resolver.resolve(name, arity, true)?;
    let mut diagnostics = resolver.diagnostics;
    let proof = required_global_type_proof(store, host, name, arity)?;
    if before.globals != proof.globals
        || before.symbol.as_ref().map(|symbol| symbol.symbol)
            != proof.symbol.as_ref().map(|symbol| symbol.symbol)
    {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGlobals(
            proof.globals,
        ));
    }
    for diagnostic in &mut diagnostics {
        let Some(declaration) = diagnostic.node else {
            continue;
        };
        let symbol = proof
            .symbol
            .as_ref()
            .ok_or(CanonicalGlobalTypeInitializationError::InvalidType(type_))?
            .symbol;
        let invalid = || CanonicalGlobalTypeInitializationError::InvalidSymbol(symbol);
        let record = host.node(declaration).ok_or_else(invalid)?;
        let name = match &record.data {
            NodeData::ClassDeclaration(class) => class.name,
            NodeData::InterfaceDeclaration(interface) => Some(interface.name),
            NodeData::TypeAliasDeclaration(alias) => Some(alias.name),
            NodeData::EnumDeclaration(enumeration) => Some(enumeration.name),
            _ => None,
        }
        .ok_or_else(invalid)?;
        let name = NodeRef::new(declaration.arena, declaration.file, name);
        if !host.node(name).is_some_and(|name| {
            name.parent == Some(declaration.node)
                && matches!(&name.data, NodeData::Identifier(identifier) if identifier.text == proof.name)
        }) {
            return Err(invalid());
        }
        diagnostic.node = Some(name);
    }
    Ok(ResolvedGlobalType {
        type_,
        diagnostics,
        proof,
    })
}

fn required_global_type_proof(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    name: &str,
    arity: usize,
) -> Result<RequiredGlobalTypeProof, CanonicalGlobalTypeInitializationError> {
    let globals = store
        .intrinsic_bootstrap()
        .ok_or(CanonicalGlobalTypeInitializationError::MissingBootstrap)?
        .globals;
    if store.symbol_table(globals).is_none() {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGlobals(
            globals,
        ));
    }
    let symbol = {
        let mut resolver_host = host.name_resolver_host(store)?;
        resolve_global_name(
            store.symbol_store(),
            &mut resolver_host,
            name,
            SymbolFlags::TYPE,
            None,
            false,
            false,
        )?
    };
    let symbol = symbol
        .map(|symbol| {
            let invalid = || CanonicalGlobalTypeInitializationError::InvalidSymbol(symbol);
            let record = store.symbol(symbol).ok_or_else(invalid)?;
            if store.get_merged_symbol(symbol) != Some(symbol)
                || record.name().as_utf8() != Some(name)
                || !store.source_merged_symbol_declarations_match(symbol)
            {
                return Err(invalid());
            }
            let declarations = record
                .declarations()
                .filter(|declarations| !declarations.is_empty())
                .ok_or_else(invalid)?;
            if declarations.iter().any(|declaration| {
                host.node(*declaration).is_none()
                    || !host.symbol_matches(store, *declaration, symbol)
            }) {
                return Err(invalid());
            }
            for declaration in declarations {
                validate_required_global_declaration(store, host, *declaration, symbol, name)?;
            }
            let declared_type = if record
                .flags()
                .intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE)
            {
                optional_global_type_has_arity(store, host, name, arity)?;
                let declared = store
                    .declared_type_links(symbol)
                    .and_then(|links| links.declared_type);
                if let Some(type_) = declared
                    && store
                        .type_payload(type_)
                        .and_then(super::type_records::TypeRecord::symbol)
                        != Some(symbol)
                {
                    return Err(CanonicalGlobalTypeInitializationError::InvalidType(type_));
                }
                declared
            } else {
                None
            };
            Ok(RequiredGlobalSymbolProof {
                symbol,
                flags: record.flags(),
                declarations: declarations.to_vec(),
                declared_type,
            })
        })
        .transpose()?;
    Ok(RequiredGlobalTypeProof {
        globals,
        name: name.to_owned(),
        arity,
        symbol,
    })
}

fn validate_required_global_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    expected_name: &str,
) -> Result<(), CanonicalGlobalTypeInitializationError> {
    let invalid = || CanonicalGlobalTypeInitializationError::InvalidSymbol(symbol);
    let record = host.node(declaration).ok_or_else(invalid)?;
    let source_parent = record.parent.map_or(SourceNodeParent::Root, |parent| {
        SourceNodeParent::Parent(NodeRef::new(declaration.arena, declaration.file, parent))
    });
    if store.source_node_kind(declaration) != Some(record.kind)
        || store.source_node_start(declaration) != Some(record.range.start.get())
        || store.source_node_parent(declaration) != Some(source_parent)
        || !record.data.matches_syntax_kind(record.kind)
    {
        return Err(invalid());
    }
    let name = match &record.data {
        NodeData::ClassDeclaration(class) => class.name,
        NodeData::ClassExpression(class) => class.name,
        NodeData::InterfaceDeclaration(interface) => Some(interface.name),
        NodeData::TypeAliasDeclaration(alias) => Some(alias.name),
        NodeData::EnumDeclaration(enumeration) => Some(enumeration.name),
        NodeData::ModuleDeclaration(module) => Some(module.name),
        NodeData::FunctionDeclaration(function) => function.name,
        NodeData::VariableDeclaration(variable) => Some(variable.name),
        NodeData::BindingElement(binding) => binding.name,
        _ => None,
    }
    .ok_or_else(invalid)?;
    let name = NodeRef::new(declaration.arena, declaration.file, name);
    if store.source_identifier_text(name) != Some(expected_name)
        || store.source_node_parent(name) != Some(SourceNodeParent::Parent(declaration))
    {
        return Err(invalid());
    }
    let mut children = Vec::new();
    record.for_each_child(|child| {
        children.push(NodeRef::new(declaration.arena, declaration.file, child));
    });
    children.sort_unstable();
    if store.source_direct_children(declaration).as_deref() != Some(children.as_slice()) {
        return Err(invalid());
    }
    for child in children {
        let child_record = host.node(child).ok_or_else(invalid)?;
        if store.source_node_kind(child) != Some(child_record.kind)
            || store.source_node_start(child) != Some(child_record.range.start.get())
            || child_record.parent != Some(declaration.node)
            || !child_record.data.matches_syntax_kind(child_record.kind)
            || store.source_identifier_text(child).is_some_and(|expected| {
                !matches!(&child_record.data,
                    NodeData::Identifier(identifier) if identifier.text == expected)
            })
        {
            return Err(invalid());
        }
    }
    Ok(())
}

/// Proves the pinned no-heritage `Object` fast path without resolving any
/// heritage expressions. The proof is deliberately restricted to a real,
/// non-generic merged interface; value-side `var Object` declarations do not
/// contribute bases and are ignored.
fn preflight_global_object_no_base(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: SymbolTableId,
    object_type: TypeId,
) -> Result<GlobalObjectNoBasePlan, CanonicalGlobalTypeInitializationError> {
    let object_record = store.type_payload(object_type).ok_or(
        CanonicalGlobalTypeInitializationError::InvalidType(object_type),
    )?;
    let TypeData::Interface(interface) = object_record.data() else {
        // Missing, wrong-kind, and wrong-arity globals use the pinned empty
        // object fallback and cannot establish a fact about global Object.
        return Ok(GlobalObjectNoBasePlan::NoPublish);
    };
    let object_origin = object_record.object_flags() & ObjectFlags::CLASS_OR_INTERFACE;
    let symbol = object_record.symbol().ok_or(
        CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
    )?;
    let raw_global = store
        .symbol_table(globals)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidGlobals(
            globals,
        ))?
        .get_source("Object")
        .ok_or(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        )?;
    let global_symbol = store.get_merged_symbol(raw_global).ok_or(
        CanonicalGlobalTypeInitializationError::InvalidSymbol(raw_global),
    )?;
    if symbol != global_symbol {
        return Err(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        );
    }
    let symbol_record =
        store
            .symbol(symbol)
            .ok_or(CanonicalGlobalTypeInitializationError::InvalidSymbol(
                symbol,
            ))?;
    let has_exact_interface_type_side =
        (symbol_record.flags() & SymbolFlags::TYPE) == SymbolFlags::INTERFACE;
    let declarations = symbol_record.declarations().ok_or(
        CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
    )?;
    if declarations.is_empty() {
        return Err(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        );
    }

    let mut saw_interface = false;
    let mut saw_interface_heritage = false;
    let mut declarations_prove_no_bases = true;
    for declaration in declarations {
        let node = host.node(*declaration).ok_or(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectDeclaration(*declaration),
        )?;
        if !host.symbol_matches(store, *declaration, symbol) {
            return Err(
                CanonicalGlobalTypeInitializationError::InvalidGlobalObjectDeclaration(
                    *declaration,
                ),
            );
        }
        match (node.kind, &node.data) {
            (SyntaxKind::InterfaceDeclaration, NodeData::InterfaceDeclaration(interface)) => {
                saw_interface = true;
                let has_heritage = interface.heritage_clauses.is_some();
                if has_heritage {
                    saw_interface_heritage = true;
                }
                if interface.type_parameters.is_some() || has_heritage {
                    declarations_prove_no_bases = false;
                }
            }
            (SyntaxKind::VariableDeclaration, NodeData::VariableDeclaration(_)) => {
                // `declare var Object` is the value-side constructor and does
                // not participate in interface base resolution.
            }
            (SyntaxKind::InterfaceDeclaration | SyntaxKind::VariableDeclaration, _) => {
                return Err(
                    CanonicalGlobalTypeInitializationError::InvalidGlobalObjectDeclaration(
                        *declaration,
                    ),
                );
            }
            _ => declarations_prove_no_bases = false,
        }
    }
    if has_exact_interface_type_side && !saw_interface {
        return Err(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        );
    }
    if !has_exact_interface_type_side || !declarations_prove_no_bases {
        // A class is both a type and a value, but it is not evidence for the
        // interface-only no-heritage result. Other valid unsupported merged
        // forms are equally conservative.
        if object_origin == ObjectFlags::CLASS {
            return Ok(GlobalObjectNoBasePlan::NoPublish);
        }
        if object_origin != ObjectFlags::INTERFACE {
            return Err(
                CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(
                    object_type,
                ),
            );
        }
        return match global_object_base_resolution_state(interface) {
            GlobalObjectBaseResolutionState::Cold => Ok(GlobalObjectNoBasePlan::NoPublish),
            GlobalObjectBaseResolutionState::ResolvedBases if saw_interface_heritage => {
                Ok(GlobalObjectNoBasePlan::NoPublish)
            }
            GlobalObjectBaseResolutionState::NoBases
            | GlobalObjectBaseResolutionState::ResolvedBases
            | GlobalObjectBaseResolutionState::Invalid => Err(
                CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(
                    object_type,
                ),
            ),
        };
    }
    if object_origin != ObjectFlags::INTERFACE {
        return Err(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        );
    }

    match global_object_base_resolution_state(interface) {
        GlobalObjectBaseResolutionState::NoBases => Ok(GlobalObjectNoBasePlan::NoPublish),
        GlobalObjectBaseResolutionState::Cold => Ok(GlobalObjectNoBasePlan::Publish(object_type)),
        GlobalObjectBaseResolutionState::ResolvedBases
        | GlobalObjectBaseResolutionState::Invalid => Err(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        ),
    }
}

/// Publishes only after all other fallible global-library initialization has
/// completed, so a later failure cannot leave behind this newly resolved fact.
fn commit_global_object_no_base(
    store: &mut CanonicalTypeMapperStore,
    plan: GlobalObjectNoBasePlan,
) -> Result<(), CanonicalGlobalTypeInitializationError> {
    let GlobalObjectNoBasePlan::Publish(object_type) = plan else {
        return Ok(());
    };
    let record = store.type_payload(object_type).ok_or(
        CanonicalGlobalTypeInitializationError::InvalidType(object_type),
    )?;
    let TypeData::Interface(interface) = record.data() else {
        return Err(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        );
    };
    match global_object_base_resolution_state(interface) {
        // An already-warm cache is valid and must retain its member resolution
        // state.
        GlobalObjectBaseResolutionState::NoBases => Ok(()),
        GlobalObjectBaseResolutionState::Cold
            if store.publish_interface_no_base_resolution(object_type) =>
        {
            Ok(())
        }
        GlobalObjectBaseResolutionState::Cold
        | GlobalObjectBaseResolutionState::ResolvedBases
        | GlobalObjectBaseResolutionState::Invalid => Err(
            CanonicalGlobalTypeInitializationError::InvalidGlobalObjectBaseResolution(object_type),
        ),
    }
}

fn global_object_base_resolution_state(
    interface: &super::type_records::InterfaceTypeData,
) -> GlobalObjectBaseResolutionState {
    match (
        interface.base_types_resolved,
        interface.resolved_base_constructor_type,
        interface.resolved_base_types.as_deref(),
    ) {
        (false, None, None) => GlobalObjectBaseResolutionState::Cold,
        (true, None, None) => GlobalObjectBaseResolutionState::NoBases,
        (true, None, Some(bases)) if !bases.is_empty() => {
            GlobalObjectBaseResolutionState::ResolvedBases
        }
        _ => GlobalObjectBaseResolutionState::Invalid,
    }
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

/// Validates one authoritative generic-global target and its complete
/// target-local instantiation cache. The returned type is the pinned missing
/// or malformed-library fallback; `None` means the target is an initialized
/// one-parameter class or interface.
///
/// Validation is intentionally read-only so callers can reject a poisoned
/// retained target before resolving an argument node or allocating a new
/// reference identity.
#[allow(clippy::too_many_lines)] // One complete target-and-cache invariant matrix.
pub(super) fn preflight_generic_global_type_target(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
) -> Result<Option<TypeId>, CanonicalGlobalTypeInitializationError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(CanonicalGlobalTypeInitializationError::MissingBootstrap)?;
    if target == bootstrap.empty_generic_type {
        return Ok(Some(bootstrap.empty_object_type));
    }

    let target_record = store
        .type_payload(target)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidType(target))?;
    let TypeData::Interface(interface) = target_record.data() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let Some(type_arguments) = interface.reference.resolved_type_arguments.as_deref() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let Some(all_type_parameters) = interface.all_type_parameters.as_deref() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let TypeCacheState::Allocated(instantiations) = &interface.reference.object.instantiations
    else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let target_symbol = target_record
        .symbol()
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target))?;
    let target_origin = target_record.object_flags() & ObjectFlags::CLASS_OR_INTERFACE;
    let target_allowed_flags = ObjectFlags::CLASS_OR_INTERFACE
        | ObjectFlags::REFERENCE
        | ObjectFlags::PROPAGATING_FLAGS
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
        | ObjectFlags::MEMBERS_RESOLVED
        | ObjectFlags::CONTAINS_SPREAD
        | ObjectFlags::OBJECT_REST_TYPE
        | ObjectFlags::IDENTICAL_BASE_TYPE_CALCULATED
        | ObjectFlags::IDENTICAL_BASE_TYPE_EXISTS
        | ObjectFlags::UNRESOLVED_MEMBERS;
    if target_record.flags() != TypeFlags::OBJECT
        || !matches!(target_origin, ObjectFlags::CLASS | ObjectFlags::INTERFACE)
        || !target_record
            .object_flags()
            .contains(ObjectFlags::REFERENCE)
        || !(target_record.object_flags() & !target_allowed_flags).is_empty()
        || type_arguments.len() != 1
        || all_type_parameters.len() != 2
        || all_type_parameters.first() != type_arguments.first()
        || all_type_parameters.last().copied() != interface.this_type
        || interface.outer_type_parameter_count != 0
        || interface.reference.object.target != Some(target)
        || interface.reference.object.mapper.is_some()
        || interface.reference.node.is_some()
        || target_record.alias().is_some()
        || cached_ordinary_type_parameter_owner(store, type_arguments[0]).is_none()
    {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    }
    let this_type = interface
        .this_type
        .expect("the validated all-type-parameter tail is the this type");
    let Some(this_record) = store.type_payload(this_type) else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let this_flags = this_record.object_flags();
    let resolved_type_parameter_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    if this_record.flags() != TypeFlags::TYPE_PARAMETER
        || !(this_flags == ObjectFlags::NONE || this_flags == resolved_type_parameter_flags)
        || this_record.symbol() != Some(target_symbol)
        || this_record.alias().is_some()
        || !matches!(
            this_record.data(),
            TypeData::TypeParameter(data)
                if data.is_this_type
                    && data.constraint == Some(target)
                    && data.target.is_none()
                    && data.mapper.is_none()
        )
    {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    }

    let identity_key = type_list_key(type_arguments);
    if instantiations.get(&identity_key) != Some(&target) {
        return Err(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target));
    }
    for (key, instantiation) in instantiations {
        if *instantiation == target {
            if *key != identity_key {
                return Err(
                    CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target),
                );
            }
            continue;
        }
        let record = store
            .type_payload(*instantiation)
            .ok_or(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target))?;
        let TypeData::TypeReference(reference) = record.data() else {
            return Err(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target));
        };
        let Some(arguments) = reference.resolved_type_arguments.as_deref() else {
            return Err(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target));
        };
        let propagating_flags = arguments.iter().fold(ObjectFlags::NONE, |flags, argument| {
            flags
                | store
                    .type_payload(*argument)
                    .map_or(ObjectFlags::NONE, |record| {
                        record.object_flags() & ObjectFlags::PROPAGATING_FLAGS
                    })
        });
        let allowed_flags = ObjectFlags::REFERENCE
            | ObjectFlags::FROM_TYPE_NODE
            | ObjectFlags::PROPAGATING_FLAGS
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
            | ObjectFlags::MEMBERS_RESOLVED
            | ObjectFlags::CONTAINS_SPREAD
            | ObjectFlags::OBJECT_REST_TYPE
            | ObjectFlags::IDENTICAL_BASE_TYPE_CALCULATED
            | ObjectFlags::IDENTICAL_BASE_TYPE_EXISTS
            | ObjectFlags::UNRESOLVED_MEMBERS;
        if arguments.len() != 1
            || arguments
                .iter()
                .any(|argument| store.type_payload(*argument).is_none())
            || *key != type_list_key(arguments)
            || reference.object.target != Some(target)
            || reference.object.mapper.is_some()
            || reference.object.instantiations != TypeCacheState::Unallocated
            || reference.node.is_some()
            || record.alias().is_some()
            || record.symbol() != target_record.symbol()
            || !record
                .object_flags()
                .contains(ObjectFlags::REFERENCE | propagating_flags)
            || !(record.object_flags() & !allowed_flags).is_empty()
        {
            return Err(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target));
        }
    }
    Ok(None)
}

/// Validates the authoritative generic target shell used by one relation
/// lookup without scanning unrelated target-local instantiations.
///
/// The relation path separately records and validates each exact `(target,
/// key)` entry it consumes. Shell replacement invalidates the broad target
/// observation, while ordinary target-cache insertion invalidates only an
/// observed exact key (or an explicitly map-wide reader).
pub(super) fn preflight_relation_generic_global_type_target(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
) -> Result<Option<TypeId>, CanonicalGlobalTypeInitializationError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(CanonicalGlobalTypeInitializationError::MissingBootstrap)?;
    if target == bootstrap.empty_generic_type {
        return Ok(Some(bootstrap.empty_object_type));
    }

    let target_record = store
        .type_payload(target)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidType(target))?;
    let TypeData::Interface(interface) = target_record.data() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let Some(type_arguments) = interface.reference.resolved_type_arguments.as_deref() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let Some(all_type_parameters) = interface.all_type_parameters.as_deref() else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let TypeCacheState::Allocated(_) = &interface.reference.object.instantiations else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let target_symbol = target_record
        .symbol()
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target))?;
    let target_origin = target_record.object_flags() & ObjectFlags::CLASS_OR_INTERFACE;
    let target_allowed_flags = ObjectFlags::CLASS_OR_INTERFACE
        | ObjectFlags::REFERENCE
        | ObjectFlags::PROPAGATING_FLAGS
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
        | ObjectFlags::MEMBERS_RESOLVED
        | ObjectFlags::CONTAINS_SPREAD
        | ObjectFlags::OBJECT_REST_TYPE
        | ObjectFlags::IDENTICAL_BASE_TYPE_CALCULATED
        | ObjectFlags::IDENTICAL_BASE_TYPE_EXISTS
        | ObjectFlags::UNRESOLVED_MEMBERS;
    if target_record.flags() != TypeFlags::OBJECT
        || !matches!(target_origin, ObjectFlags::CLASS | ObjectFlags::INTERFACE)
        || !target_record
            .object_flags()
            .contains(ObjectFlags::REFERENCE)
        || !(target_record.object_flags() & !target_allowed_flags).is_empty()
        || type_arguments.len() != 1
        || all_type_parameters.len() != 2
        || all_type_parameters.first() != type_arguments.first()
        || all_type_parameters.last().copied() != interface.this_type
        || interface.outer_type_parameter_count != 0
        || interface.reference.object.target != Some(target)
        || interface.reference.object.mapper.is_some()
        || interface.reference.node.is_some()
        || target_record.alias().is_some()
        || cached_ordinary_type_parameter_owner(store, type_arguments[0]).is_none()
    {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    }
    let this_type = interface
        .this_type
        .expect("the validated all-type-parameter tail is the this type");
    let Some(this_record) = store.type_payload(this_type) else {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    };
    let this_flags = this_record.object_flags();
    let resolved_type_parameter_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    if this_record.flags() != TypeFlags::TYPE_PARAMETER
        || !(this_flags == ObjectFlags::NONE || this_flags == resolved_type_parameter_flags)
        || this_record.symbol() != Some(target_symbol)
        || this_record.alias().is_some()
        || !matches!(
            this_record.data(),
            TypeData::TypeParameter(data)
                if data.is_this_type
                    && data.constraint == Some(target)
                    && data.target.is_none()
                    && data.mapper.is_none()
        )
        || store.relation_object_instantiation(target, type_list_key(type_arguments))
            != Some(target)
    {
        return Err(CanonicalGlobalTypeInitializationError::InvalidGenericTarget(target));
    }
    Ok(None)
}

/// Returns whether `instantiation` is the canonical result owned by `target`.
/// The malformed-library fallback is canonical only for the exact intrinsic
/// empty-object identity; initialized targets accept only values present in
/// their validated target-local cache.
pub(super) fn validate_generic_global_type_instantiation(
    store: &CanonicalTypeMapperStore,
    target: TypeId,
    instantiation: TypeId,
) -> Result<(), CanonicalGlobalTypeInitializationError> {
    if let Some(fallback) = preflight_generic_global_type_target(store, target)? {
        return if instantiation == fallback {
            Ok(())
        } else {
            Err(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target))
        };
    }
    let TypeData::Interface(interface) = store
        .type_payload(target)
        .expect("the generic-global target was preflighted")
        .data()
    else {
        unreachable!("the generic-global target changed after preflight")
    };
    let TypeCacheState::Allocated(instantiations) = &interface.reference.object.instantiations
    else {
        unreachable!("the generic-global cache changed after preflight")
    };
    if instantiations
        .values()
        .any(|cached| *cached == instantiation)
    {
        Ok(())
    } else {
        Err(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target))
    }
}

/// Creates or reuses the pinned one-argument reference for an authoritative
/// generic global. Identity is owned solely by the target's instantiation map
/// and keyed by the exact ordered type-argument list. `creation_flags` are
/// applied only when this call wins the first allocation for that key.
pub(super) fn create_type_from_generic_global_type(
    store: &mut CanonicalTypeMapperStore,
    target: TypeId,
    type_argument: TypeId,
    creation_flags: ObjectFlags,
) -> Result<TypeId, CanonicalGlobalTypeInitializationError> {
    if let Some(fallback) = preflight_generic_global_type_target(store, target)? {
        return Ok(fallback);
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
        unreachable!("the generic-global target changed after preflight")
    };
    if let Some(existing) = instantiations.get(&key) {
        return Ok(*existing);
    }
    if !(creation_flags & !ObjectFlags::FROM_TYPE_NODE).is_empty() {
        return Err(CanonicalGlobalTypeInitializationError::InvalidTypeReference(target));
    }
    let symbol = target_record.symbol();
    let argument_flags = store
        .type_payload(type_argument)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidType(
            type_argument,
        ))?
        .object_flags()
        & ObjectFlags::PROPAGATING_FLAGS;
    if !store.try_reserve_object_instantiations(target, 1) {
        return Err(CanonicalGlobalTypeInitializationError::InvalidInstantiationCache(target));
    }
    let reference = store
        .alloc_type_reference(argument_flags | creation_flags, symbol)
        .ok_or(CanonicalGlobalTypeInitializationError::InvalidTypeReference(target))?;
    assert!(store.set_object_target_and_mapper(reference, Some(target), None));
    assert!(store.set_type_reference_resolution(reference, None, Some(vec![type_argument]),));
    let canonical = store
        .insert_object_instantiation(target, key, reference)
        .expect("the preflighted generic-global target accepts its reference");
    assert_eq!(canonical, reference);
    Ok(canonical)
}
