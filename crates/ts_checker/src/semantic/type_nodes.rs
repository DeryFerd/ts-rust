use std::collections::{BTreeMap, HashMap, HashSet};

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalNameResolutionError, CanonicalNameResolver, CanonicalResolutionLocation,
    SemanticSymbolId, SymbolFlags,
};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalTypeMapperStore,
    DeclaredTypeError, DeclaredTypeHost, DeclaredTypeUnavailable, TypeId, TypeResolutionTarget,
    TypeSystemPropertyName, UnsupportedDeclaredTypeKind,
    declared::{
        cached_ordinary_type_parameter_owner, execute_type_parameter,
        explicit_type_parameter_symbols, get_declared_class_interface_or_type_parameter,
        malformed_alias_merge, preflight_class_or_interface_reference, preflight_node,
        preflight_type_parameter_symbol, type_list_key,
    },
};

const NODE_FLAG_JSDOC: u32 = 1 << 22;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CanonicalTypeQueryOptions {
    pub strict_builtin_iterator_return: bool,
}

impl From<CanonicalCheckerOptions> for CanonicalTypeQueryOptions {
    fn from(options: CanonicalCheckerOptions) -> Self {
        Self {
            strict_builtin_iterator_return: options.strict_builtin_iterator_return,
        }
    }
}

impl From<&CanonicalCheckerOptions> for CanonicalTypeQueryOptions {
    fn from(options: &CanonicalCheckerOptions) -> Self {
        (*options).into()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeNodeUnavailable {
    UnsupportedSyntax {
        node: NodeRef,
        kind: SyntaxKind,
    },
    JsDoc(NodeRef),
    InvalidParenthesizedType(NodeRef),
    InvalidTypeReference(NodeRef),
    QualifiedTypeReference(NodeRef),
    TypeArgumentsUnsupported(NodeRef),
    MissingTypeReference(NodeRef),
    ImportAliasTypeReference {
        node: NodeRef,
        alias: SemanticSymbolId,
    },
    UnsupportedReferenceTarget {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    GenericReferenceUnsupported {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    InvalidTypeAliasSymbol(SemanticSymbolId),
    MissingTypeAliasDeclaration(SemanticSymbolId),
    InvalidTypeAliasDeclaration(NodeRef),
    JsDocTypeAlias(NodeRef),
    InvalidCachedTypeAlias(SemanticSymbolId),
    InvalidCachedSymbol {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    MissingPlannedTypeAlias(SemanticSymbolId),
    MissingPlannedTypeReference(NodeRef),
    ResolutionStackInvariant(SemanticSymbolId),
}

#[derive(Clone, Debug)]
struct TypeAliasPlan {
    name: NodeRef,
    name_text: String,
    type_node: NodeRef,
    type_parameter_symbols: Vec<SemanticSymbolId>,
}

#[derive(Debug, Default)]
struct TypeQueryPlan {
    aliases: BTreeMap<SemanticSymbolId, TypeAliasPlan>,
    references: BTreeMap<NodeRef, SemanticSymbolId>,
}

#[derive(Clone, Copy, Debug)]
struct CachedTypeAlias {
    declared_type: TypeId,
    type_parameter_count: usize,
}

fn type_node_unavailable(reason: TypeNodeUnavailable) -> DeclaredTypeError {
    DeclaredTypeError::TypeNodeUnavailable(reason)
}

fn cached_type_alias(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
) -> Result<Option<CachedTypeAlias>, DeclaredTypeError> {
    let Some(links) = store.type_alias_links(symbol) else {
        return Ok(None);
    };
    let Some(declared_type) = links.declared_type else {
        if links.type_parameters.is_some() || links.instantiations.is_some() {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
            ));
        }
        return Ok(None);
    };

    let type_parameter_count = match links.type_parameters.as_deref() {
        None if links.instantiations.is_none() => 0,
        Some(type_parameters) if !type_parameters.is_empty() => {
            let unique_parameters = type_parameters.iter().copied().collect::<HashSet<_>>();
            let parameters_are_valid = unique_parameters.len() == type_parameters.len()
                && type_parameters.iter().all(|parameter| {
                    cached_ordinary_type_parameter_owner(store, *parameter).is_some()
                });
            let has_identity_seed = links.instantiations.as_ref().is_some_and(|instantiations| {
                instantiations.get(&type_list_key(type_parameters)) == Some(&declared_type)
            });
            if !parameters_are_valid || !has_identity_seed {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
                ));
            }
            type_parameters.len()
        }
        None | Some(_) => {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidCachedTypeAlias(symbol),
            ));
        }
    };
    Ok(Some(CachedTypeAlias {
        declared_type,
        type_parameter_count,
    }))
}

struct TypeQueryPlanner<'store, 'host, 'arena> {
    store: &'store CanonicalTypeMapperStore,
    host: &'host DeclaredTypeHost<'arena>,
    plan: TypeQueryPlan,
}

impl<'store, 'host, 'arena> TypeQueryPlanner<'store, 'host, 'arena> {
    fn new(store: &'store CanonicalTypeMapperStore, host: &'host DeclaredTypeHost<'arena>) -> Self {
        Self {
            store,
            host,
            plan: TypeQueryPlan::default(),
        }
    }

    fn finish(self) -> TypeQueryPlan {
        self.plan
    }

    fn plan_type_node(&mut self, node: NodeRef) -> Result<(), DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, node)?;
        if record.flags.0 & NODE_FLAG_JSDOC != 0 {
            return Err(type_node_unavailable(TypeNodeUnavailable::JsDoc(node)));
        }
        match record.kind {
            SyntaxKind::AnyKeyword
            | SyntaxKind::UnknownKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::BigIntKeyword
            | SyntaxKind::BooleanKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::VoidKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::NullKeyword
            | SyntaxKind::NeverKeyword
            | SyntaxKind::ObjectKeyword
            | SyntaxKind::IntrinsicKeyword => Ok(()),
            SyntaxKind::ParenthesizedType => {
                let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data else {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidParenthesizedType(node),
                    ));
                };
                let inner = NodeRef::new(node.arena, node.file, parenthesized.type_);
                if preflight_node(self.store, self.host, inner)?.parent != Some(node.node) {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidParenthesizedType(node),
                    ));
                }
                self.plan_type_node(inner)
            }
            SyntaxKind::LiteralType => {
                let NodeData::LiteralTypeNode(literal) = &record.data else {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::UnsupportedSyntax {
                            node,
                            kind: record.kind,
                        },
                    ));
                };
                let literal = NodeRef::new(node.arena, node.file, literal.literal);
                let literal_node = preflight_node(self.store, self.host, literal)?;
                if literal_node.parent == Some(node.node)
                    && literal_node.kind == SyntaxKind::NullKeyword
                {
                    Ok(())
                } else {
                    Err(type_node_unavailable(
                        TypeNodeUnavailable::UnsupportedSyntax {
                            node,
                            kind: record.kind,
                        },
                    ))
                }
            }
            SyntaxKind::TypeReference => self.plan_type_reference(node),
            kind => Err(type_node_unavailable(
                TypeNodeUnavailable::UnsupportedSyntax { node, kind },
            )),
        }
    }

    fn plan_type_reference(&mut self, node: NodeRef) -> Result<(), DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, node)?;
        let NodeData::TypeReferenceNode(reference) = &record.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        };
        if reference
            .type_arguments
            .as_ref()
            .is_some_and(|arguments| !arguments.nodes.is_empty())
        {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::TypeArgumentsUnsupported(node),
            ));
        }

        let name = NodeRef::new(node.arena, node.file, reference.type_name);
        let name_node = preflight_node(self.store, self.host, name)?;
        if name_node.parent != Some(node.node) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        }
        if name_node.flags.0 & NODE_FLAG_JSDOC != 0 {
            return Err(type_node_unavailable(TypeNodeUnavailable::JsDoc(name)));
        }
        let NodeData::Identifier(identifier) = &name_node.data else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::QualifiedTypeReference(node),
            ));
        };

        if self
            .store
            .type_node_links(node)
            .and_then(|links| links.resolved_type)
            .is_some()
        {
            return Ok(());
        }

        let symbol = if let Some(symbol) = self
            .store
            .symbol_node_links(node)
            .and_then(|links| links.resolved_symbol)
        {
            self.store.symbol(symbol).map(|_| symbol).ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::InvalidCachedSymbol { node, symbol })
            })?
        } else {
            let (arena, bound) = self.host.source(node).ok_or({
                DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::MissingOrForeignFacts(node))
            })?;
            let mut callback_host = self.host.name_resolver_host(self.store)?;
            let resolved = CanonicalNameResolver::new(
                arena,
                bound,
                self.store.symbol_store(),
                &mut callback_host,
            )?
            .resolve(
                Some(CanonicalResolutionLocation::Bound(node)),
                &identifier.text,
                SymbolFlags::TYPE,
                None,
                false,
                false,
            );
            match resolved {
                Ok(Some(symbol)) => self.store.symbol(symbol).map(|_| symbol).ok_or({
                    DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol))
                })?,
                Ok(None) => {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::MissingTypeReference(node),
                    ));
                }
                Err(CanonicalNameResolutionError::AliasResolutionUnavailable(alias)) => {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::ImportAliasTypeReference { node, alias },
                    ));
                }
                Err(error) => return Err(error.into()),
            }
        };

        let flags = self
            .store
            .symbol(symbol)
            .ok_or({
                DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol))
            })?
            .flags();
        if malformed_alias_merge(flags) {
            return Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::AliasMergedWithDeclaredSymbol(symbol),
            ));
        }

        if flags.intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE) {
            let local_count =
                preflight_class_or_interface_reference(self.store, self.host, symbol, flags)?;
            if local_count != 0 {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::GenericReferenceUnsupported { node, symbol },
                ));
            }
        } else if flags.contains(SymbolFlags::TYPE_PARAMETER) {
            preflight_type_parameter_symbol(self.store, self.host, symbol, &mut HashSet::new())?;
        } else if flags.contains(SymbolFlags::TYPE_ALIAS) {
            let type_parameter_count = self.plan_type_alias(symbol)?;
            if type_parameter_count != 0 {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::GenericReferenceUnsupported { node, symbol },
                ));
            }
        } else if flags.contains(SymbolFlags::ALIAS) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::ImportAliasTypeReference {
                    node,
                    alias: symbol,
                },
            ));
        } else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::UnsupportedReferenceTarget { node, symbol },
            ));
        }

        if let Some(existing) = self.plan.references.insert(node, symbol) {
            assert_eq!(existing, symbol, "one type-reference node has one symbol");
        }
        Ok(())
    }

    fn plan_type_alias(&mut self, symbol: SemanticSymbolId) -> Result<usize, DeclaredTypeError> {
        if let Some(cached) = cached_type_alias(self.store, symbol)? {
            return Ok(cached.type_parameter_count);
        }
        if let Some(plan) = self.plan.aliases.get(&symbol) {
            return Ok(plan.type_parameter_symbols.len());
        }

        let record = self.store.symbol(symbol).ok_or({
            DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol))
        })?;
        let flags = record.flags();
        if !flags.contains(SymbolFlags::TYPE_ALIAS) || malformed_alias_merge(flags) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeAliasSymbol(symbol),
            ));
        }
        let declarations = record
            .declarations()
            .filter(|declarations| !declarations.is_empty())
            .ok_or_else(|| {
                type_node_unavailable(TypeNodeUnavailable::MissingTypeAliasDeclaration(symbol))
            })?
            .to_vec();

        let mut first = None;
        let mut type_parameter_symbols = Vec::new();
        let mut checked = HashSet::new();
        for declaration in declarations {
            let declaration_node = preflight_node(self.store, self.host, declaration)?;
            if declaration_node.kind == SyntaxKind::JsTypeAliasDeclaration {
                return Err(type_node_unavailable(TypeNodeUnavailable::JsDocTypeAlias(
                    declaration,
                )));
            }
            let NodeData::TypeAliasDeclaration(alias) = &declaration_node.data else {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
                ));
            };
            if declaration_node.kind != SyntaxKind::TypeAliasDeclaration
                || !self.host.symbol_matches(self.store, declaration, symbol)
            {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
                ));
            }
            let name = NodeRef::new(declaration.arena, declaration.file, alias.name);
            let type_node = NodeRef::new(declaration.arena, declaration.file, alias.type_);
            let name_node = preflight_node(self.store, self.host, name)?;
            let type_record = preflight_node(self.store, self.host, type_node)?;
            let NodeData::Identifier(identifier) = &name_node.data else {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
                ));
            };
            if name_node.parent != Some(declaration.node)
                || type_record.parent != Some(declaration.node)
                || declaration_node.flags.0 & NODE_FLAG_JSDOC != 0
            {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidTypeAliasDeclaration(declaration),
                ));
            }
            for parameter in explicit_type_parameter_symbols(
                self.store,
                self.host,
                declaration,
                alias.type_parameters.as_ref(),
                &mut checked,
            )? {
                if !type_parameter_symbols.contains(&parameter) {
                    type_parameter_symbols.push(parameter);
                }
            }
            if first.is_none() {
                first = Some((name, identifier.text.clone(), type_node));
            }
        }

        let Some((name, name_text, type_node)) = first else {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::MissingTypeAliasDeclaration(symbol),
            ));
        };
        let type_parameter_count = type_parameter_symbols.len();
        self.plan.aliases.insert(
            symbol,
            TypeAliasPlan {
                name,
                name_text,
                type_node,
                type_parameter_symbols,
            },
        );
        self.plan_type_node(type_node)?;
        Ok(type_parameter_count)
    }
}

pub struct CanonicalTypeQuery<'store, 'host, 'arena, 'diagnostics> {
    store: &'store mut CanonicalTypeMapperStore,
    host: &'host DeclaredTypeHost<'arena>,
    options: CanonicalTypeQueryOptions,
    diagnostics: &'diagnostics mut CanonicalCheckerDiagnostics,
}

impl<'store, 'host, 'arena, 'diagnostics> CanonicalTypeQuery<'store, 'host, 'arena, 'diagnostics> {
    pub fn new(
        store: &'store mut CanonicalTypeMapperStore,
        host: &'host DeclaredTypeHost<'arena>,
        options: impl Into<CanonicalTypeQueryOptions>,
        diagnostics: &'diagnostics mut CanonicalCheckerDiagnostics,
    ) -> Self {
        Self {
            store,
            host,
            options: options.into(),
            diagnostics,
        }
    }

    /// Resolves one dependency-closed type-node query.
    ///
    /// # Errors
    ///
    /// Returns a typed unavailable or provenance error before mutation when
    /// the node's dependency closure is outside the installed semantic cut.
    pub fn get_type_from_type_node(&mut self, node: NodeRef) -> Result<TypeId, DeclaredTypeError> {
        let mut planner = TypeQueryPlanner::new(self.store, self.host);
        planner.plan_type_node(node)?;
        let plan = planner.finish();
        self.execute_type_node(node, &plan)
    }

    /// Resolves the declared type identity of one symbol.
    ///
    /// # Errors
    ///
    /// Returns a typed unavailable, resolution, or provenance error when the
    /// symbol's dependency closure cannot be resolved by this semantic cut.
    pub fn get_declared_type_of_symbol(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<TypeId, DeclaredTypeError> {
        let symbol = self.canonical_symbol(symbol)?;
        let flags = self.symbol_flags(symbol)?;
        let mut planner = TypeQueryPlanner::new(self.store, self.host);
        if !flags
            .intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE | SymbolFlags::TYPE_PARAMETER)
            && flags.contains(SymbolFlags::TYPE_ALIAS)
        {
            planner.plan_type_alias(symbol)?;
        }
        let plan = planner.finish();
        self.execute_declared_type(symbol, &plan)
    }

    fn canonical_symbol(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, DeclaredTypeError> {
        self.store.get_merged_symbol(symbol).ok_or({
            DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol))
        })
    }

    fn symbol_flags(&self, symbol: SemanticSymbolId) -> Result<SymbolFlags, DeclaredTypeError> {
        self.store
            .symbol(symbol)
            .map(ts_binder::semantic::Symbol::flags)
            .ok_or({
                DeclaredTypeError::Unavailable(DeclaredTypeUnavailable::SymbolNotOwned(symbol))
            })
    }

    fn execute_declared_type(
        &mut self,
        symbol: SemanticSymbolId,
        plan: &TypeQueryPlan,
    ) -> Result<TypeId, DeclaredTypeError> {
        let flags = self.symbol_flags(symbol)?;
        let error_type = self
            .store
            .intrinsic_bootstrap()
            .ok_or(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized,
            ))?
            .error_type;
        if malformed_alias_merge(flags) {
            return Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::AliasMergedWithDeclaredSymbol(symbol),
            ));
        }
        if let Some(declared_type) =
            get_declared_class_interface_or_type_parameter(self.store, self.host, symbol, flags)?
        {
            return Ok(declared_type);
        }
        if flags.contains(SymbolFlags::TYPE_ALIAS) {
            return self.execute_type_alias(symbol, plan);
        }
        if flags.intersects(SymbolFlags::ENUM) {
            return Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::UnsupportedDeclaredType(UnsupportedDeclaredTypeKind::Enum),
            ));
        }
        if flags.contains(SymbolFlags::ENUM_MEMBER) {
            return Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::UnsupportedDeclaredType(
                    UnsupportedDeclaredTypeKind::EnumMember,
                ),
            ));
        }
        if flags.contains(SymbolFlags::ALIAS) {
            return Err(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::UnsupportedDeclaredType(
                    UnsupportedDeclaredTypeKind::Alias,
                ),
            ));
        }
        Ok(error_type)
    }

    fn execute_type_alias(
        &mut self,
        symbol: SemanticSymbolId,
        plan: &TypeQueryPlan,
    ) -> Result<TypeId, DeclaredTypeError> {
        if let Some(cached) = cached_type_alias(self.store, symbol)? {
            return Ok(cached.declared_type);
        }
        let alias = plan.aliases.get(&symbol).cloned().ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::MissingPlannedTypeAlias(symbol))
        })?;
        let error_type = self
            .store
            .intrinsic_bootstrap()
            .ok_or(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized,
            ))?
            .error_type;
        if !self.store.push_type_resolution(
            TypeResolutionTarget::Symbol(symbol),
            TypeSystemPropertyName::DeclaredType,
        )? {
            return Ok(error_type);
        }

        let resolved = match self.execute_type_node(alias.type_node, plan) {
            Ok(resolved) => resolved,
            Err(error) => {
                if self.store.pop_type_resolution().is_none() {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::ResolutionStackInvariant(symbol),
                    ));
                }
                return Err(error);
            }
        };
        let cycle_free = self.store.pop_type_resolution().ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::ResolutionStackInvariant(symbol))
        })?;

        let mut links = self
            .store
            .type_alias_links(symbol)
            .cloned()
            .unwrap_or_default();
        let declared_type = if cycle_free {
            if !alias.type_parameter_symbols.is_empty() {
                let type_parameters = alias
                    .type_parameter_symbols
                    .iter()
                    .map(|parameter| execute_type_parameter(self.store, *parameter))
                    .collect::<Vec<_>>();
                let mut instantiations = HashMap::new();
                instantiations.insert(type_list_key(&type_parameters), resolved);
                links.type_parameters = Some(type_parameters);
                links.instantiations = Some(instantiations);
            }
            let intrinsic_marker = self
                .store
                .intrinsic_bootstrap()
                .expect("bootstrap was checked before alias resolution")
                .intrinsic_marker_type;
            if resolved == intrinsic_marker && alias.name_text == "BuiltinIteratorReturn" {
                let bootstrap = self
                    .store
                    .intrinsic_bootstrap()
                    .expect("bootstrap was checked before alias resolution");
                if self.options.strict_builtin_iterator_return {
                    bootstrap.undefined_type
                } else {
                    bootstrap.any_type
                }
            } else {
                resolved
            }
        } else {
            self.diagnostics.add(
                Some(alias.name),
                Diagnostic::with_arguments(
                    message_by_code(2456).expect("TS2456 is in the diagnostic catalog"),
                    [alias.name_text],
                ),
            );
            error_type
        };

        if links.declared_type.is_none() {
            links.declared_type = Some(declared_type);
        }
        let published = links
            .declared_type
            .expect("the alias declared type was just initialized");
        if !self.store.set_type_alias_links(symbol, links) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeAliasSymbol(symbol),
            ));
        }
        Ok(published)
    }

    fn execute_type_node(
        &mut self,
        node: NodeRef,
        plan: &TypeQueryPlan,
    ) -> Result<TypeId, DeclaredTypeError> {
        let record = preflight_node(self.store, self.host, node)?;
        match record.kind {
            SyntaxKind::AnyKeyword
            | SyntaxKind::UnknownKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::BigIntKeyword
            | SyntaxKind::BooleanKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::VoidKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::NullKeyword
            | SyntaxKind::NeverKeyword
            | SyntaxKind::ObjectKeyword
            | SyntaxKind::IntrinsicKeyword => self.keyword_type(record.kind),
            SyntaxKind::ParenthesizedType => {
                let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data else {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::InvalidParenthesizedType(node),
                    ));
                };
                self.execute_type_node(
                    NodeRef::new(node.arena, node.file, parenthesized.type_),
                    plan,
                )
            }
            SyntaxKind::LiteralType => {
                let NodeData::LiteralTypeNode(literal) = &record.data else {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::UnsupportedSyntax {
                            node,
                            kind: record.kind,
                        },
                    ));
                };
                let literal = NodeRef::new(node.arena, node.file, literal.literal);
                if preflight_node(self.store, self.host, literal)?.kind != SyntaxKind::NullKeyword {
                    return Err(type_node_unavailable(
                        TypeNodeUnavailable::UnsupportedSyntax {
                            node,
                            kind: record.kind,
                        },
                    ));
                }
                self.store
                    .intrinsic_bootstrap()
                    .map(|bootstrap| bootstrap.null_type)
                    .ok_or(DeclaredTypeError::Unavailable(
                        DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized,
                    ))
            }
            SyntaxKind::TypeReference => self.execute_type_reference(node, plan),
            kind => Err(type_node_unavailable(
                TypeNodeUnavailable::UnsupportedSyntax { node, kind },
            )),
        }
    }

    fn execute_type_reference(
        &mut self,
        node: NodeRef,
        plan: &TypeQueryPlan,
    ) -> Result<TypeId, DeclaredTypeError> {
        if let Some(resolved_type) = self
            .store
            .type_node_links(node)
            .and_then(|links| links.resolved_type)
        {
            return Ok(resolved_type);
        }
        let symbol = plan.references.get(&node).copied().ok_or_else(|| {
            type_node_unavailable(TypeNodeUnavailable::MissingPlannedTypeReference(node))
        })?;

        let mut symbol_links = self
            .store
            .symbol_node_links(node)
            .cloned()
            .unwrap_or_default();
        if let Some(cached) = symbol_links.resolved_symbol {
            if cached != symbol || self.store.symbol(cached).is_none() {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidCachedSymbol {
                        node,
                        symbol: cached,
                    },
                ));
            }
        } else {
            symbol_links.resolved_symbol = Some(symbol);
            if !self.store.set_symbol_node_links(node, symbol_links) {
                return Err(type_node_unavailable(
                    TypeNodeUnavailable::InvalidCachedSymbol { node, symbol },
                ));
            }
        }

        let resolved_type = self.execute_declared_type(symbol, plan)?;
        let mut type_links = self
            .store
            .type_node_links(node)
            .cloned()
            .unwrap_or_default();
        type_links.resolved_type = Some(resolved_type);
        if !self.store.set_type_node_links(node, type_links) {
            return Err(type_node_unavailable(
                TypeNodeUnavailable::InvalidTypeReference(node),
            ));
        }
        Ok(resolved_type)
    }

    fn keyword_type(&self, kind: SyntaxKind) -> Result<TypeId, DeclaredTypeError> {
        let bootstrap = self
            .store
            .intrinsic_bootstrap()
            .ok_or(DeclaredTypeError::Unavailable(
                DeclaredTypeUnavailable::IntrinsicBootstrapNotInitialized,
            ))?;
        Ok(match kind {
            SyntaxKind::AnyKeyword => bootstrap.any_type,
            SyntaxKind::UnknownKeyword => bootstrap.unknown_type,
            SyntaxKind::StringKeyword => bootstrap.string_type,
            SyntaxKind::NumberKeyword => bootstrap.number_type,
            SyntaxKind::BigIntKeyword => bootstrap.bigint_type,
            SyntaxKind::BooleanKeyword => bootstrap.boolean_type,
            SyntaxKind::SymbolKeyword => bootstrap.es_symbol_type,
            SyntaxKind::VoidKeyword => bootstrap.void_type,
            SyntaxKind::UndefinedKeyword => bootstrap.undefined_type,
            SyntaxKind::NullKeyword => bootstrap.null_type,
            SyntaxKind::NeverKeyword => bootstrap.never_type,
            SyntaxKind::ObjectKeyword => bootstrap.non_primitive_type,
            SyntaxKind::IntrinsicKeyword => bootstrap.intrinsic_marker_type,
            _ => unreachable!("keyword_type is called only for supported keyword nodes"),
        })
    }
}

impl CanonicalTypeMapperStore {
    /// Resolves a type node using default query options and discarded diagnostics.
    ///
    /// # Errors
    ///
    /// Returns a typed unavailable or provenance error before mutation when
    /// the node's dependency closure is outside the installed semantic cut.
    pub fn get_type_from_type_node(
        &mut self,
        host: &DeclaredTypeHost<'_>,
        node: NodeRef,
    ) -> Result<TypeId, DeclaredTypeError> {
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        CanonicalTypeQuery::new(
            self,
            host,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .get_type_from_type_node(node)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{FileId, Node, NodeArena, NodeData, NodeFlags, NodeId};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        DeclaredTypeHostError, DeclaredTypeLinks, IntrinsicBootstrapOptions, SymbolNodeLinks,
        TypeNodeLinks, production::GlobalMergeCompletion,
    };

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        files: BTreeMap<FileId, BoundFile>,
        store: CanonicalTypeMapperStore,
    }

    fn fixture(source: &str) -> Fixture {
        fixture_with(source, CanonicalModuleState::Script, |_| {})
    }

    fn fixture_with_mutation(source: &str, mutate: impl FnOnce(&mut ParseResult)) -> Fixture {
        fixture_with(source, CanonicalModuleState::Script, mutate)
    }

    fn fixture_with_module_state(source: &str, module_state: CanonicalModuleState) -> Fixture {
        fixture_with(source, module_state, |_| {})
    }

    fn fixture_with(
        source: &str,
        module_state: CanonicalModuleState,
        mutate: impl FnOnce(&mut ParseResult),
    ) -> Fixture {
        let mut parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        mutate(&mut parsed);
        let file = FileId::new(71);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/type-nodes.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();

        if module_state == CanonicalModuleState::Script {
            let bound = files.get(&file).unwrap();
            let locals = bound.locals(bound.source_file()).unwrap();
            let mut symbols = store
                .symbol_table(locals)
                .unwrap()
                .iter()
                .map(|(name, symbol)| (name.as_bytes().to_vec(), symbol))
                .collect::<Vec<_>>();
            symbols.sort_unstable_by(|left, right| left.0.cmp(&right.0));
            let globals = store.intrinsic_bootstrap().unwrap().globals;
            for (_, symbol) in symbols {
                store.merge_global_symbol(globals, symbol).unwrap();
            }
        }

        Fixture {
            parsed,
            file,
            files,
            store,
        }
    }

    fn post_global_host<'a>(arena: &'a NodeArena, bound: &'a BoundFile) -> DeclaredTypeHost<'a> {
        DeclaredTypeHost::new_after_global_merge(
            [(arena, bound)],
            GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
        )
        .unwrap()
    }

    fn identifier_text(arena: &NodeArena, identifier: NodeId) -> Option<&str> {
        let NodeData::Identifier(identifier) = &arena.get(identifier)?.data else {
            return None;
        };
        Some(&identifier.text)
    }

    fn declaration_name<'a>(arena: &'a NodeArena, node: &Node) -> Option<&'a str> {
        let name = match &node.data {
            NodeData::TypeAliasDeclaration(data) => data.name,
            NodeData::InterfaceDeclaration(data) => data.name,
            NodeData::ClassDeclaration(data) => data.name?,
            NodeData::TypeParameterDeclaration(data) => data.name,
            NodeData::ImportSpecifier(data) => data.name,
            _ => return None,
        };
        identifier_text(arena, name)
    }

    fn named_node(fixture: &Fixture, kind: SyntaxKind, name: &str) -> NodeRef {
        let node = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(id, node)| {
                (node.kind == kind && declaration_name(&fixture.parsed.arena, node) == Some(name))
                    .then_some(id)
            })
            .unwrap_or_else(|| panic!("missing {kind:?} named {name}"));
        NodeRef::new(fixture.parsed.arena.id(), fixture.file, node)
    }

    fn node_symbol(fixture: &Fixture, node: NodeRef) -> SemanticSymbolId {
        fixture
            .files
            .get(&fixture.file)
            .unwrap()
            .symbol(node)
            .unwrap()
    }

    fn named_symbol(fixture: &Fixture, kind: SyntaxKind, name: &str) -> SemanticSymbolId {
        node_symbol(fixture, named_node(fixture, kind, name))
    }

    fn alias_parts(fixture: &Fixture, name: &str) -> (NodeRef, NodeRef, NodeRef) {
        let declaration = named_node(fixture, SyntaxKind::TypeAliasDeclaration, name);
        let NodeData::TypeAliasDeclaration(alias) =
            &fixture.parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        (
            declaration,
            NodeRef::new(declaration.arena, declaration.file, alias.name),
            NodeRef::new(declaration.arena, declaration.file, alias.type_),
        )
    }

    fn store_state(store: &CanonicalTypeMapperStore) -> (usize, usize, [usize; 26], usize, usize) {
        (
            store.type_len(),
            store.mapper_len(),
            store.checker_link_allocated_lengths(),
            store.type_resolution_len(),
            store.type_resolution_start(),
        )
    }

    fn query_declared(
        fixture: &mut Fixture,
        symbol: SemanticSymbolId,
        options: CanonicalTypeQueryOptions,
        diagnostics: &mut CanonicalCheckerDiagnostics,
    ) -> Result<TypeId, DeclaredTypeError> {
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        CanonicalTypeQuery::new(&mut fixture.store, &host, options, diagnostics)
            .get_declared_type_of_symbol(symbol)
    }

    #[test]
    fn keyword_and_parenthesized_nodes_reuse_exact_bootstrap_identities() {
        let source = concat!(
            "type Any = any; type Unknown = unknown; type String = string; ",
            "type Number = number; type BigInt = bigint; type Boolean = boolean; ",
            "type Symbol = symbol; type Void = void; type Undefined = undefined; ",
            "type Null = null; type Never = never; type Object = object; ",
            "type Intrinsic = intrinsic; type Parenthesized = ((string));",
        );
        let mut fixture = fixture(source);
        let expected = {
            let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
            [
                ("Any", bootstrap.any_type),
                ("Unknown", bootstrap.unknown_type),
                ("String", bootstrap.string_type),
                ("Number", bootstrap.number_type),
                ("BigInt", bootstrap.bigint_type),
                ("Boolean", bootstrap.boolean_type),
                ("Symbol", bootstrap.es_symbol_type),
                ("Void", bootstrap.void_type),
                ("Undefined", bootstrap.undefined_type),
                ("Null", bootstrap.null_type),
                ("Never", bootstrap.never_type),
                ("Object", bootstrap.non_primitive_type),
                ("Intrinsic", bootstrap.intrinsic_marker_type),
                ("Parenthesized", bootstrap.string_type),
            ]
        };
        let nodes = expected
            .iter()
            .map(|(name, expected)| (alias_parts(&fixture, name).2, *expected))
            .collect::<Vec<_>>();
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let mut query = CanonicalTypeQuery::new(
            &mut fixture.store,
            &host,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        );
        for (node, expected) in nodes {
            assert_eq!(query.get_type_from_type_node(node), Ok(expected));
        }
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn alias_chains_cache_in_type_alias_links_and_ignore_declared_type_links() {
        let mut fixture = fixture("type Base = string; type Alias = Base;");
        let base = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Base");
        let alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Alias");
        let (_, _, reference) = alias_parts(&fixture, "Alias");
        let number_type = fixture.store.intrinsic_bootstrap().unwrap().number_type;
        let string_type = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(fixture.store.set_declared_type_links(
            alias,
            DeclaredTypeLinks {
                declared_type: Some(number_type),
                ..DeclaredTypeLinks::default()
            },
        ));

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_declared(
                &mut fixture,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(string_type)
        );
        assert_eq!(
            fixture
                .store
                .type_alias_links(base)
                .and_then(|links| links.declared_type),
            Some(string_type)
        );
        assert_eq!(
            fixture
                .store
                .type_alias_links(alias)
                .and_then(|links| links.declared_type),
            Some(string_type)
        );
        assert_eq!(
            fixture
                .store
                .declared_type_links(alias)
                .and_then(|links| links.declared_type),
            Some(number_type)
        );
        assert_eq!(
            fixture
                .store
                .type_node_links(reference)
                .and_then(|links| links.resolved_type),
            Some(string_type)
        );
        assert_eq!(
            fixture
                .store
                .symbol_node_links(reference)
                .and_then(|links| links.resolved_symbol),
            Some(base)
        );

        let empty = DeclaredTypeHost::new(std::iter::empty::<(&NodeArena, &BoundFile)>()).unwrap();
        assert_eq!(
            fixture.store.get_declared_type_of_symbol(&empty, alias),
            Ok(string_type)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_alias_seeds_its_identity_instantiation_in_parameter_order() {
        let mut fixture = fixture("type Id<T, U> = T;");
        let alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Id");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let declared = query_declared(
            &mut fixture,
            alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let links = fixture.store.type_alias_links(alias).unwrap();
        let parameters = links.type_parameters.as_deref().unwrap();
        assert_eq!(parameters.len(), 2);
        let names = parameters
            .iter()
            .map(|parameter| {
                let symbol = fixture
                    .store
                    .type_payload(*parameter)
                    .unwrap()
                    .symbol()
                    .unwrap();
                fixture
                    .store
                    .symbol(symbol)
                    .unwrap()
                    .name()
                    .as_utf8()
                    .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(names, ["T", "U"]);
        assert_eq!(declared, parameters[0]);
        assert_eq!(
            links
                .instantiations
                .as_ref()
                .unwrap()
                .get(&type_list_key(parameters)),
            Some(&declared)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn non_generic_aliases_to_class_and_interface_preserve_origin_identities() {
        let mut fixture = fixture(concat!(
            "class Model {} interface Shape {} ",
            "type ModelAlias = Model; type ShapeAlias = Shape;",
        ));
        let class = named_symbol(&fixture, SyntaxKind::ClassDeclaration, "Model");
        let interface = named_symbol(&fixture, SyntaxKind::InterfaceDeclaration, "Shape");
        let class_alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "ModelAlias");
        let interface_alias =
            named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "ShapeAlias");
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let class_alias_type = query_declared(
            &mut fixture,
            class_alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let interface_alias_type = query_declared(
            &mut fixture,
            interface_alias,
            CanonicalTypeQueryOptions::default(),
            &mut diagnostics,
        )
        .unwrap();
        let host = post_global_host(
            &fixture.parsed.arena,
            fixture.files.get(&fixture.file).unwrap(),
        );
        let class_type = fixture
            .store
            .get_declared_type_of_symbol(&host, class)
            .unwrap();
        let interface_type = fixture
            .store
            .get_declared_type_of_symbol(&host, interface)
            .unwrap();
        assert_eq!(class_alias_type, class_type);
        assert_eq!(interface_alias_type, interface_type);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn direct_alias_cycle_uses_the_shared_stack_and_issues_ts2456_once() {
        let mut fixture = fixture("type A = A;");
        let alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "A");
        let (_, name, reference) = alias_parts(&fixture, "A");
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        {
            let host = post_global_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            let mut query = CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            );
            assert_eq!(query.get_declared_type_of_symbol(alias), Ok(error_type));
            assert_eq!(query.get_declared_type_of_symbol(alias), Ok(error_type));
        }
        assert!(fixture.store.type_resolution_is_empty());
        let links = fixture.store.type_alias_links(alias).unwrap();
        assert_eq!(links.declared_type, Some(error_type));
        assert!(links.type_parameters.is_none());
        assert!(links.instantiations.is_none());
        assert_eq!(
            fixture
                .store
                .type_node_links(reference)
                .and_then(|links| links.resolved_type),
            Some(error_type)
        );
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].node, Some(name));
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2456);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.arguments, ["A"]);
    }

    #[test]
    fn mutual_alias_cycle_reports_each_unwound_alias_once_and_caches_error() {
        let mut fixture = fixture("type A = B; type B = A;");
        let a = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "A");
        let b = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "B");
        let error_type = fixture.store.intrinsic_bootstrap().unwrap().error_type;
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        {
            let host = post_global_host(
                &fixture.parsed.arena,
                fixture.files.get(&fixture.file).unwrap(),
            );
            let mut query = CanonicalTypeQuery::new(
                &mut fixture.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            );
            assert_eq!(query.get_declared_type_of_symbol(a), Ok(error_type));
            assert_eq!(query.get_declared_type_of_symbol(b), Ok(error_type));
        }
        assert!(fixture.store.type_resolution_is_empty());
        assert_eq!(
            fixture
                .store
                .type_alias_links(a)
                .and_then(|links| links.declared_type),
            Some(error_type)
        );
        assert_eq!(
            fixture
                .store
                .type_alias_links(b)
                .and_then(|links| links.declared_type),
            Some(error_type)
        );
        assert_eq!(diagnostics.len(), 2);
        assert_eq!(
            diagnostics
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.arguments[0].as_str())
                .collect::<Vec<_>>(),
            ["B", "A"]
        );
        assert!(
            diagnostics
                .as_slice()
                .iter()
                .all(|diagnostic| diagnostic.diagnostic.code() == 2456)
        );
    }

    #[test]
    fn builtin_iterator_return_uses_the_query_option_and_other_intrinsics_do_not() {
        for (strict, expected_undefined) in [(false, false), (true, true)] {
            let mut fixture = fixture(concat!(
                "type BuiltinIteratorReturn = intrinsic; ",
                "type OtherIntrinsic = intrinsic;",
            ));
            let builtin = named_symbol(
                &fixture,
                SyntaxKind::TypeAliasDeclaration,
                "BuiltinIteratorReturn",
            );
            let other = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "OtherIntrinsic");
            let (expected, marker) = {
                let bootstrap = fixture.store.intrinsic_bootstrap().unwrap();
                (
                    if expected_undefined {
                        bootstrap.undefined_type
                    } else {
                        bootstrap.any_type
                    },
                    bootstrap.intrinsic_marker_type,
                )
            };
            let options = CanonicalTypeQueryOptions {
                strict_builtin_iterator_return: strict,
            };
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            assert_eq!(
                query_declared(&mut fixture, builtin, options, &mut diagnostics),
                Ok(expected)
            );
            assert_eq!(
                query_declared(&mut fixture, other, options, &mut diagnostics),
                Ok(marker)
            );
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn type_and_symbol_node_caches_are_reused_without_name_reresolution() {
        let mut type_cached = fixture("type Base = string; type Alias = Base;");
        let alias = named_symbol(&type_cached, SyntaxKind::TypeAliasDeclaration, "Alias");
        let base = named_symbol(&type_cached, SyntaxKind::TypeAliasDeclaration, "Base");
        let reference = alias_parts(&type_cached, "Alias").2;
        let number_type = type_cached.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(type_cached.store.set_type_node_links(
            reference,
            TypeNodeLinks {
                resolved_type: Some(number_type),
                ..TypeNodeLinks::default()
            },
        ));
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert_eq!(
            query_declared(
                &mut type_cached,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(number_type)
        );
        assert!(type_cached.store.type_alias_links(base).is_none());
        assert!(type_cached.store.symbol_node_links(reference).is_none());

        let mut symbol_cached = fixture("type Base = string; type Alias = Missing;");
        let alias = named_symbol(&symbol_cached, SyntaxKind::TypeAliasDeclaration, "Alias");
        let base = named_symbol(&symbol_cached, SyntaxKind::TypeAliasDeclaration, "Base");
        let reference = alias_parts(&symbol_cached, "Alias").2;
        let string_type = symbol_cached
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .string_type;
        assert!(symbol_cached.store.set_symbol_node_links(
            reference,
            SymbolNodeLinks {
                resolved_symbol: Some(base),
            },
        ));
        assert_eq!(
            query_declared(
                &mut symbol_cached,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Ok(string_type)
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn named_reference_boundaries_are_typed_and_atomic_without_diagnostics() {
        let cases = [
            ("namespace N { export interface X {} } type Bad = N.X;", 0),
            ("type Bad = Missing;", 1),
            ("interface Box<T> {} type Bad = Box<string>;", 2),
            ("type Id<T> = T; type Bad = Id;", 3),
            ("class Box<T> {} type Bad = Box;", 3),
        ];

        for (source, expected) in cases {
            let mut fixture = fixture(source);
            let bad = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Bad");
            let before = store_state(&fixture.store);
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            let error = query_declared(
                &mut fixture,
                bad,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            )
            .unwrap_err();
            assert!(
                matches!(
                    (expected, error),
                    (
                        0,
                        DeclaredTypeError::TypeNodeUnavailable(
                            TypeNodeUnavailable::QualifiedTypeReference(_)
                        )
                    ) | (
                        1,
                        DeclaredTypeError::TypeNodeUnavailable(
                            TypeNodeUnavailable::MissingTypeReference(_)
                        )
                    ) | (
                        2,
                        DeclaredTypeError::TypeNodeUnavailable(
                            TypeNodeUnavailable::TypeArgumentsUnsupported(_)
                        )
                    ) | (
                        3,
                        DeclaredTypeError::TypeNodeUnavailable(
                            TypeNodeUnavailable::GenericReferenceUnsupported { .. }
                        )
                    )
                ),
                "unexpected error: {error:?}"
            );
            assert_eq!(store_state(&fixture.store), before);
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn import_alias_references_are_typed_and_atomic() {
        let mut fixture = fixture_with_module_state(
            "import { Remote as Local } from 'pkg'; type Bad = Local;",
            CanonicalModuleState::External,
        );
        let bad = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, "Bad");
        let before = store_state(&fixture.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(matches!(
            query_declared(
                &mut fixture,
                bad,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::ImportAliasTypeReference { .. }
            ))
        ));
        assert_eq!(store_state(&fixture.store), before);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn every_deferred_type_node_family_and_recursive_array_fail_atomically() {
        let source = concat!(
            "declare const value: string; ",
            "type Literal = 'x'; type ArrayAlias = string[]; type TupleAlias = [string]; ",
            "type UnionAlias = string | number; type IntersectionAlias = object & {}; ",
            "type ObjectAlias = { value: string }; type FunctionAlias = () => string; ",
            "type OperatorAlias = keyof object; type IndexedAlias = { a: string }['a']; ",
            "type MappedAlias<T> = { [K in keyof T]: T[K] }; ",
            "type ConditionalAlias<T> = T extends string ? string : number; ",
            "type InferAlias<T> = T extends infer U ? U : never; ",
            "type ImportTypeAlias = import('pkg').Value; type QueryAlias = typeof value; ",
            "type ThisAlias = this; type RecursiveArray = RecursiveArray[];",
        );
        let aliases = [
            "Literal",
            "ArrayAlias",
            "TupleAlias",
            "UnionAlias",
            "IntersectionAlias",
            "ObjectAlias",
            "FunctionAlias",
            "OperatorAlias",
            "IndexedAlias",
            "MappedAlias",
            "ConditionalAlias",
            "InferAlias",
            "ImportTypeAlias",
            "QueryAlias",
            "ThisAlias",
            "RecursiveArray",
        ];
        let mut fixture = fixture(source);
        for name in aliases {
            let alias = named_symbol(&fixture, SyntaxKind::TypeAliasDeclaration, name);
            let before = store_state(&fixture.store);
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            assert!(matches!(
                query_declared(
                    &mut fixture,
                    alias,
                    CanonicalTypeQueryOptions::default(),
                    &mut diagnostics,
                ),
                Err(DeclaredTypeError::TypeNodeUnavailable(
                    TypeNodeUnavailable::UnsupportedSyntax { .. }
                ))
            ));
            assert_eq!(store_state(&fixture.store), before, "alias {name}");
            assert!(diagnostics.is_empty());
            assert!(fixture.store.type_alias_links(alias).is_none());
        }
    }

    #[test]
    fn jsdoc_foreign_and_stale_inputs_fail_before_checker_writes() {
        let mut jsdoc = fixture_with_mutation("type A = string;", |parsed| {
            let body = parsed
                .arena
                .iter()
                .find_map(|(_, node)| {
                    let NodeData::TypeAliasDeclaration(alias) = &node.data else {
                        return None;
                    };
                    Some(alias.type_)
                })
                .unwrap();
            parsed.arena.get_mut(body).unwrap().flags = NodeFlags(NODE_FLAG_JSDOC);
        });
        let alias = named_symbol(&jsdoc, SyntaxKind::TypeAliasDeclaration, "A");
        let before = store_state(&jsdoc.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(matches!(
            query_declared(
                &mut jsdoc,
                alias,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            ),
            Err(DeclaredTypeError::TypeNodeUnavailable(
                TypeNodeUnavailable::JsDoc(_)
            ))
        ));
        assert_eq!(store_state(&jsdoc.store), before);
        assert!(diagnostics.is_empty());

        let mut local = fixture("type Local = string;");
        let foreign = fixture("type Foreign = string;");
        let foreign_body = alias_parts(&foreign, "Foreign").2;
        let before = store_state(&local.store);
        let host = post_global_host(&local.parsed.arena, local.files.get(&local.file).unwrap());
        {
            let mut query = CanonicalTypeQuery::new(
                &mut local.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                &mut diagnostics,
            );
            assert!(matches!(
                query.get_type_from_type_node(foreign_body),
                Err(DeclaredTypeError::Unavailable(
                    DeclaredTypeUnavailable::MissingOrForeignFacts(_)
                ))
            ));
        }
        assert_eq!(store_state(&local.store), before);

        let mut stale = fixture("type Stale = string;");
        let before = store_state(&stale.store);
        let orphan = stale
            .parsed
            .arena
            .iter()
            .next()
            .map(|(_, node)| node.clone())
            .unwrap();
        stale.parsed.arena.alloc(orphan);
        assert!(matches!(
            DeclaredTypeHost::new([(&stale.parsed.arena, stale.files.get(&stale.file).unwrap())]),
            Err(DeclaredTypeHostError::ArenaRevisionMismatch { .. })
        ));
        assert_eq!(store_state(&stale.store), before);
    }
}
