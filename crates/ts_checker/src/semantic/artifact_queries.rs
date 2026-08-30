//! Production location queries used by semantic fixture artifacts.
//!
//! The canonical binder attaches declaration symbols to declaration nodes,
//! while checker caches attach reference symbols to expressions and type
//! references. Artifact walkers normally visit the identifier inside those
//! nodes, so these queries preserve the existing graph instead of constructing
//! replacement symbols or types.
//! Missing type names use the store's symbol-only unresolved-name cache.

use std::collections::HashSet;

use ts_ast::{FileId, Node, NodeArena, NodeArenaRevision, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalNameResolver, CanonicalResolutionLocation, EscapedName, EscapedNameRef,
    InternalSymbolName, SemanticSymbolId, SymbolFlags,
};
use ts_jsnum::PseudoBigInt;

use super::{
    AliasTargetState, CanonicalAliasQueryError, CanonicalCheckerContext,
    CanonicalModuleResolutionLookup, DeclaredTypeError, SourceCheckError, TypeData, TypeId,
    TypeNodeLinks,
    alias::{CanonicalAliasResolutionError, CanonicalAliasTargetUnavailable},
    source::unresolved_namespace_import_read,
    source_callables::{StoredSourceCallableValidation, validate_stored_source_callable},
    source_imports::{SourceImportError, plan_top_level_named_value_import},
    type_nodes::{normalize_bigint_literal, normalize_numeric_separators},
    type_records::TypeRecord,
};

/// A location query could not prove an exact result from this checker program.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalArtifactQueryError {
    MissingFile(FileId),
    ForeignNode(NodeRef),
    StaleFile {
        file: FileId,
        expected: NodeArenaRevision,
        actual: NodeArenaRevision,
    },
    UnsupportedNode {
        node: NodeRef,
        kind: SyntaxKind,
    },
    MissingType {
        node: NodeRef,
        kind: SyntaxKind,
    },
    InvalidType {
        node: NodeRef,
        type_: TypeId,
    },
    InvalidSymbol {
        node: NodeRef,
        symbol: SemanticSymbolId,
    },
    ForeignSymbol(SemanticSymbolId),
    ForeignDeclaration {
        symbol: SemanticSymbolId,
        declaration: NodeRef,
    },
    SourceCheck(SourceCheckError),
    Class {
        node: NodeRef,
        error: super::ClassError,
    },
    DeclaredType(DeclaredTypeError),
    Alias(CanonicalAliasQueryError),
    SymbolDisplay(super::SymbolDisplayError),
}

impl std::fmt::Display for CanonicalArtifactQueryError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingFile(file) => {
                write!(
                    formatter,
                    "artifact query references missing file {}",
                    file.index()
                )
            }
            Self::ForeignNode(node) => {
                write!(
                    formatter,
                    "artifact query references a foreign node {node:?}"
                )
            }
            Self::StaleFile { file, .. } => {
                write!(
                    formatter,
                    "artifact query references stale file {}",
                    file.index()
                )
            }
            Self::UnsupportedNode { node, kind } => {
                write!(
                    formatter,
                    "artifact query does not support {kind:?} at {node:?}"
                )
            }
            Self::MissingType { node, kind } => {
                write!(
                    formatter,
                    "artifact query has no exact type for {kind:?} at {node:?}"
                )
            }
            Self::InvalidType { node, type_ } => {
                write!(
                    formatter,
                    "artifact query found invalid type {type_:?} at {node:?}"
                )
            }
            Self::InvalidSymbol { node, symbol } => {
                write!(
                    formatter,
                    "artifact query found invalid symbol {symbol:?} at {node:?}"
                )
            }
            Self::ForeignSymbol(symbol) => {
                write!(
                    formatter,
                    "artifact query references foreign symbol {symbol:?}"
                )
            }
            Self::ForeignDeclaration {
                symbol,
                declaration,
            } => {
                write!(
                    formatter,
                    "artifact symbol {symbol:?} has foreign declaration {declaration:?}"
                )
            }
            Self::SourceCheck(error) => error.fmt(formatter),
            Self::Class { node, error } => write!(
                formatter,
                "artifact class query failed at {node:?}: {error}"
            ),
            Self::DeclaredType(error) => error.fmt(formatter),
            Self::Alias(error) => error.fmt(formatter),
            Self::SymbolDisplay(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for CanonicalArtifactQueryError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::SourceCheck(error) => Some(error),
            Self::Class { error, .. } => Some(error),
            Self::DeclaredType(error) => Some(error),
            Self::Alias(error) => Some(error),
            Self::SymbolDisplay(error) => Some(error),
            Self::MissingFile(_)
            | Self::ForeignNode(_)
            | Self::StaleFile { .. }
            | Self::UnsupportedNode { .. }
            | Self::MissingType { .. }
            | Self::InvalidType { .. }
            | Self::InvalidSymbol { .. }
            | Self::ForeignSymbol(_)
            | Self::ForeignDeclaration { .. } => None,
        }
    }
}

impl From<SourceCheckError> for CanonicalArtifactQueryError {
    fn from(error: SourceCheckError) -> Self {
        Self::SourceCheck(error)
    }
}

impl From<DeclaredTypeError> for CanonicalArtifactQueryError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<CanonicalAliasQueryError> for CanonicalArtifactQueryError {
    fn from(error: CanonicalAliasQueryError) -> Self {
        Self::Alias(error)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LocationParent {
    Declaration(NodeRef),
    AliasedPropertyName(NodeRef),
    PropertyAccess(NodeRef),
    ElementAccess(NodeRef),
    TypeReference(NodeRef),
    TypeQuery(NodeRef),
    QualifiedName(NodeRef),
}

struct ArtifactTypeName {
    reference: NodeRef,
    full_name: NodeRef,
    parts: Vec<ArtifactTypeNamePart>,
}

struct ArtifactTypeNamePart {
    entity: NodeRef,
    identifier: NodeRef,
    text: EscapedName,
}

impl CanonicalCheckerContext<'_> {
    /// Returns the canonical semantic type for one exact Program node.
    ///
    /// Ordinary source files are checked on first demand. Declaration files
    /// remain lazily resolved because `skipLibCheck` must not force their
    /// unsupported source-checking path.
    ///
    /// # Errors
    ///
    /// Returns an exact provenance, source-checking, alias, declared-type, or
    /// unsupported-node error instead of manufacturing `any` or `unknown`.
    pub fn get_type_at_location(
        &mut self,
        node: NodeRef,
    ) -> Result<TypeId, CanonicalArtifactQueryError> {
        let catch_rest = self.catch_rest_artifact_type(node)?;
        let declaration = self.prepare_artifact_type_location(node)?;

        if let Some(type_) = self
            .import_meta_artifact_type(node)
            .map_err(|error| CanonicalArtifactQueryError::SourceCheck(error.into()))?
        {
            return self.validate_artifact_type(node, type_);
        }

        if let Some(type_) = catch_rest {
            return self.validate_artifact_type(node, type_);
        }

        if let Some(symbol) = declaration {
            let type_ = self.get_declared_type_of_symbol(symbol)?;
            if let Some(cached) = self.cached_artifact_type(node)?
                && cached != type_
            {
                return Err(CanonicalArtifactQueryError::InvalidType {
                    node,
                    type_: cached,
                });
            }
            return self.validate_artifact_type(node, type_);
        }

        if let Some(type_) = self.type_reference_qualifier_artifact_type(node)? {
            return Ok(type_);
        }

        if let Some(type_) = self.literal_annotation_artifact_type(node)? {
            return Ok(type_);
        }

        if let Some(type_) = self.checked_conditional_literal_artifact_type(node)? {
            return Ok(type_);
        }

        if let Some(type_) = self.arrow_artifact_type(node)? {
            return Ok(type_);
        }

        if let Some(type_) = self.duplicate_property_artifact_type(node)? {
            return Ok(type_);
        }

        if let Some(type_) = self.enum_initializer_artifact_type(node)? {
            return Ok(type_);
        }

        let (kind, is_type_node, parent) = {
            let (arena, bound, record) = self.validated_artifact_node(node)?;
            (
                record.kind,
                is_type_syntax(&record.data),
                location_parent(arena, bound, node, record)?,
            )
        };

        if let Some(LocationParent::Declaration(declaration)) = parent {
            if let Some(type_) = self.unresolved_namespace_declaration_type(node, declaration)? {
                return Ok(type_);
            }
            if let Some(type_) = self.module_declaration_artifact_type(node, declaration)? {
                return Ok(type_);
            }
        }

        if let Some(type_) = self.declaration_method_artifact_type(node)? {
            return Ok(type_);
        }

        if let Some(type_) = self.export_equals_declared_artifact_type(node)? {
            return Ok(type_);
        }

        if let Some(type_) = self.javascript_class_heritage_artifact_type(node)? {
            return Ok(type_);
        }

        if let Some((type_, _)) = self.class_heritage_artifact_target(node)? {
            return Ok(type_);
        }

        if let Some((type_, _)) = self.class_super_artifact_target(node)? {
            return Ok(type_);
        }

        if supports_type_location(&self.validated_artifact_node(node)?.2.data)
            && let Some(type_) = self.cached_artifact_type(node)?
        {
            return Ok(type_);
        }

        match self.get_class_query_type_at_location(node) {
            Ok(Some(type_)) => return self.validate_artifact_type(node, type_),
            Ok(None) | Err(super::ClassError::Unsupported(_)) => {}
            Err(super::ClassError::DeclaredType(error)) => return Err(error.into()),
            Err(error) => return Err(CanonicalArtifactQueryError::Class { node, error }),
        }

        if let Some((type_, _)) = self.heritage_artifact_target(node)? {
            return self.validate_artifact_type(node, type_);
        }

        if is_type_node {
            return self
                .type_node_artifact_type(node)
                .map_err(CanonicalArtifactQueryError::from)
                .and_then(|type_| self.validate_artifact_type(node, type_));
        }

        if let Some(parent) = parent {
            let parent_node = match parent {
                LocationParent::PropertyAccess(parent)
                | LocationParent::ElementAccess(parent)
                | LocationParent::TypeReference(parent)
                | LocationParent::TypeQuery(parent)
                | LocationParent::QualifiedName(parent) => Some(parent),
                LocationParent::Declaration(_) | LocationParent::AliasedPropertyName(_) => None,
            };
            if let Some(parent_node) = parent_node {
                if let Some(type_) = self.cached_artifact_type(parent_node)? {
                    return Ok(type_);
                }
                if matches!(
                    parent,
                    LocationParent::TypeReference(_) | LocationParent::TypeQuery(_)
                ) {
                    return self
                        .type_node_artifact_type(parent_node)
                        .map_err(CanonicalArtifactQueryError::from)
                        .and_then(|type_| self.validate_artifact_type(node, type_));
                }
            }
        }

        if let Some(symbol) = self.get_symbol_at_location(node)?
            && let Some(type_) = self.type_of_artifact_symbol(node, symbol)?
        {
            return Ok(type_);
        }

        if supports_type_location(&self.validated_artifact_node(node)?.2.data) {
            Err(CanonicalArtifactQueryError::MissingType { node, kind })
        } else {
            Err(CanonicalArtifactQueryError::UnsupportedNode { node, kind })
        }
    }

    /// Returns the canonical declaration or reference symbol at `node`.
    ///
    /// A successful `None` represents a supported location with no symbol,
    /// such as a literal or a missing property. Imported names retain their
    /// alias identity rather than silently returning their target.
    /// Type names do not demand their type, arguments, or source diagnostics.
    ///
    /// # Errors
    ///
    /// Returns an exact provenance or source-checking error when the query
    /// cannot prove that its answer belongs to this checker program.
    pub fn get_symbol_at_location(
        &mut self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        self.validated_artifact_node(node)?;
        match self
            .import_meta_artifact_symbol(node, super::source_meta::ImportMetaSymbolQuery::Name)
            .map_err(|error| CanonicalArtifactQueryError::SourceCheck(error.into()))?
        {
            super::source_meta::ImportMetaSymbolResult::Resolved(symbol) => return Ok(symbol),
            super::source_meta::ImportMetaSymbolResult::Unrelated => {}
        }
        if let Some(symbol) = self.type_name_artifact_symbol(node)? {
            return Ok(symbol);
        }
        self.prepare_artifact_location(node)?;

        match self
            .import_meta_artifact_symbol(
                node,
                super::source_meta::ImportMetaSymbolQuery::Expression,
            )
            .map_err(|error| CanonicalArtifactQueryError::SourceCheck(error.into()))?
        {
            super::source_meta::ImportMetaSymbolResult::Resolved(symbol) => return Ok(symbol),
            super::source_meta::ImportMetaSymbolResult::Unrelated => {}
        }

        if matches!(
            &self.validated_artifact_node(node)?.2.data,
            NodeData::ArrowFunction(_)
                | NodeData::BinaryExpression(_)
                | NodeData::ClassExpression(_)
                | NodeData::ObjectLiteralExpression(_)
                | NodeData::JsxElement(_)
                | NodeData::JsxOpeningElement(_)
                | NodeData::JsxClosingElement(_)
                | NodeData::JsxSelfClosingElement(_)
                | NodeData::JsxFragment(_)
                | NodeData::JsxOpeningFragment(_)
                | NodeData::JsxClosingFragment(_)
                | NodeData::TypeQueryNode(_)
        ) {
            return Ok(None);
        }

        if let Some(symbol) = self.shorthand_artifact_symbol(node)? {
            return Ok(Some(symbol));
        }

        if let Some(symbol) = self.literal_computed_artifact_symbol(node)? {
            return Ok(Some(symbol));
        }

        if let Some(symbol) = self.declaration_method_artifact_symbol(node)? {
            return Ok(Some(symbol));
        }

        if let Some(symbol) = self.expando_artifact_symbol(node)? {
            return Ok(Some(symbol));
        }

        if let Some((_, symbol)) = self.class_heritage_artifact_target(node)? {
            return Ok(Some(symbol));
        }

        if let Some((_, symbol)) = self.class_super_artifact_target(node)? {
            return Ok(Some(symbol));
        }

        let (bound_symbol, parent, supported) = {
            let (arena, bound, record) = self.validated_artifact_node(node)?;
            (
                bound.symbol(node),
                location_parent(arena, bound, node, record)?,
                supports_symbol_location(&record.data),
            )
        };

        if matches!(parent, Some(LocationParent::TypeReference(_)))
            && let Some(symbol) =
                self.lexical_artifact_symbol(node, SymbolFlags::TYPE | SymbolFlags::ALIAS)?
            && self
                .store()
                .symbol(symbol)
                .is_some_and(|record| record.flags().contains(SymbolFlags::ALIAS))
        {
            return Ok(Some(symbol));
        }

        if bound_symbol.is_none()
            && !matches!(
                parent,
                Some(LocationParent::Declaration(_) | LocationParent::AliasedPropertyName(_))
            )
            && let Some(symbol) = self.cached_artifact_symbol(node)?
        {
            return Ok(Some(symbol));
        }

        if bound_symbol.is_none()
            && !matches!(
                parent,
                Some(LocationParent::Declaration(_) | LocationParent::AliasedPropertyName(_))
            )
            && !matches!(
                parent,
                Some(
                    LocationParent::TypeReference(_)
                        | LocationParent::TypeQuery(_)
                        | LocationParent::QualifiedName(_)
                )
            )
        {
            let host = self.declared_type_host()?;
            match super::classes::class_query_reference_symbol(self.store(), &host, node) {
                Ok(Some(symbol)) => return self.merged_artifact_symbol(node, symbol).map(Some),
                Ok(None) | Err(super::ClassError::Unsupported(_)) => {}
                Err(super::ClassError::DeclaredType(error)) => return Err(error.into()),
                Err(error) => return Err(CanonicalArtifactQueryError::Class { node, error }),
            }
        }

        if let Some(symbol) = self.module_specifier_artifact_symbol(node)? {
            return Ok(Some(symbol));
        }

        if let Some((_, symbol)) = self.heritage_artifact_target(node)? {
            return Ok(Some(symbol));
        }

        if matches!(
            self.validated_artifact_node(node)?.2.data,
            NodeData::QualifiedName(_)
        ) {
            return self.qualified_artifact_symbol(node);
        }

        if let Some(symbol) = bound_symbol {
            return self.merged_artifact_symbol(node, symbol).map(Some);
        }

        match parent {
            Some(LocationParent::Declaration(declaration)) => {
                let (_, bound, _) = self.validated_artifact_node(declaration)?;
                let Some(symbol) = bound.symbol(declaration) else {
                    return Ok(None);
                };
                self.merged_artifact_symbol(node, symbol).map(Some)
            }
            Some(LocationParent::AliasedPropertyName(declaration)) => {
                let (_, bound, _) = self.validated_artifact_node(declaration)?;
                let Some(alias) = bound.symbol(declaration) else {
                    return Ok(None);
                };
                let alias = self.merged_artifact_symbol(node, alias)?;
                if let Some(target) = self
                    .store()
                    .alias_symbol_links(alias)
                    .and_then(|links| links.immediate_target)
                {
                    return self.merged_artifact_symbol(node, target).map(Some);
                }
                match self.resolve_alias(alias)?.target {
                    AliasTargetState::Resolved(target) => {
                        self.merged_artifact_symbol(node, target).map(Some)
                    }
                    AliasTargetState::Unknown | AliasTargetState::Unresolved => Ok(None),
                }
            }
            Some(LocationParent::TypeReference(reference)) => {
                if let Some(symbol) = self.cached_artifact_symbol(reference)? {
                    return Ok(Some(symbol));
                }
                if matches!(
                    self.validated_artifact_node(node)?.2.data,
                    NodeData::Identifier(_)
                ) {
                    return self
                        .lexical_artifact_symbol(node, SymbolFlags::TYPE | SymbolFlags::ALIAS);
                }
                self.get_type_from_type_node(reference)?;
                self.cached_artifact_symbol(reference)
            }
            Some(LocationParent::TypeQuery(query)) => {
                self.get_type_from_type_node(query)?;
                self.cached_artifact_symbol(node)
            }
            Some(
                LocationParent::PropertyAccess(access) | LocationParent::ElementAccess(access),
            ) => self.cached_artifact_symbol(access),
            Some(LocationParent::QualifiedName(name)) => {
                if self
                    .store()
                    .symbol_node_links(node)
                    .is_some_and(|links| links.resolved_symbol.is_some())
                {
                    return self.cached_artifact_symbol(node);
                }
                self.qualified_artifact_symbol(name)
            }
            None if supported => {
                let (arena, bound, record) = self.validated_artifact_node(node)?;
                let NodeData::Identifier(identifier) = &record.data else {
                    return Ok(None);
                };

                if record
                    .parent
                    .and_then(|parent| arena.get(parent))
                    .is_some_and(|parent| {
                        matches!(
                            &parent.data,
                            NodeData::QualifiedName(qualified) if qualified.left == node.node
                        )
                    })
                {
                    return self.namespace_artifact_root(node);
                }

                if record
                    .parent
                    .and_then(|parent| arena.get(parent))
                    .is_some_and(|parent| {
                        matches!(
                            &parent.data,
                            NodeData::BinaryExpression(binary)
                                if binary.left == node.node
                                    && arena
                                        .get(binary.operator_token)
                                        .is_some_and(|operator| {
                                            operator.kind.is_assignment_operator()
                                        })
                                    && parent
                                        .parent
                                        .and_then(|statement| arena.get(statement))
                                        .is_some_and(|statement| {
                                            matches!(
                                                statement.data,
                                                NodeData::ExpressionStatement(_)
                                            ) && statement.parent
                                                == Some(bound.source_file().node)
                                        })
                        )
                    })
                {
                    let local = bound
                        .locals(bound.source_file())
                        .and_then(|locals| self.store().symbol_table(locals))
                        .and_then(|locals| locals.get_source(&identifier.text));
                    if let Some(symbol) = local {
                        return self.merged_artifact_symbol(node, symbol).map(Some);
                    }
                }

                if let Some(symbol) = self.uncached_artifact_reference_symbol(node)? {
                    return Ok(Some(symbol));
                }

                if identifier.text != "undefined" {
                    return Ok(None);
                }
                let Some(bootstrap) = self.store().intrinsic_bootstrap() else {
                    return Ok(None);
                };
                let global = self
                    .store()
                    .symbol_table(bootstrap.globals)
                    .and_then(|globals| globals.get_source("undefined"))
                    .and_then(|symbol| self.store().get_merged_symbol(symbol));
                let shadowed = bound
                    .locals(bound.source_file())
                    .and_then(|locals| self.store().symbol_table(locals))
                    .and_then(|locals| locals.get_source("undefined"))
                    .and_then(|symbol| self.store().get_merged_symbol(symbol))
                    .is_some_and(|symbol| symbol != bootstrap.undefined_symbol);
                if global == Some(bootstrap.undefined_symbol) && !shadowed {
                    Ok(global)
                } else {
                    Ok(None)
                }
            }
            None => {
                let (_, _, record) = self.validated_artifact_node(node)?;
                Err(CanonicalArtifactQueryError::UnsupportedNode {
                    node,
                    kind: record.kind,
                })
            }
        }
    }

    /// Returns source declarations after validating their exact Program owner.
    ///
    /// Synthetic symbols with no declarations return an empty slice.
    ///
    /// # Errors
    ///
    /// Returns an error for foreign symbols, foreign declarations, or stale
    /// source files instead of exposing another program's nodes.
    pub fn get_symbol_declarations(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<&[NodeRef], CanonicalArtifactQueryError> {
        let record = self
            .store()
            .symbol(symbol)
            .ok_or(CanonicalArtifactQueryError::ForeignSymbol(symbol))?;
        let declarations = record.declarations().unwrap_or(&[]);
        for declaration in declarations {
            if self.validated_artifact_node(*declaration).is_err() {
                return Err(CanonicalArtifactQueryError::ForeignDeclaration {
                    symbol,
                    declaration: *declaration,
                });
            }
        }
        Ok(declarations)
    }

    /// Renders one canonical symbol name with the pinned escaped-name rules.
    ///
    /// # Errors
    ///
    /// Returns an error when `symbol` does not belong to this checker program.
    pub fn symbol_to_string(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<String, CanonicalArtifactQueryError> {
        let record = self
            .store()
            .symbol(symbol)
            .ok_or(CanonicalArtifactQueryError::ForeignSymbol(symbol))?;
        if record
            .check_flags()
            .contains(ts_binder::CheckFlags::INDEX_SYMBOL)
        {
            return self.index_artifact_symbol_name(symbol);
        }
        let escaped_identifier = self.escaped_identifier_artifact_name(symbol)?;
        let name = if record.name() == InternalSymbolName::Global.as_ref() {
            "global".to_owned()
        } else if let Some(private) = self.private_artifact_symbol_name(symbol)? {
            private
        } else {
            escaped_identifier
                .clone()
                .unwrap_or_else(|| record.name().escaped_display().to_string())
        };
        if !record.flags().intersects(
            SymbolFlags::PROPERTY
                | SymbolFlags::METHOD
                | SymbolFlags::ACCESSOR
                | SymbolFlags::ENUM_MEMBER,
        ) {
            return Ok(name);
        }

        let (name, indexed) = if let Some(escaped) = escaped_identifier {
            let indexed = record
                .parent()
                .and_then(|owner| self.store().symbol(owner))
                .is_some_and(|owner| {
                    owner
                        .flags()
                        .intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE | SymbolFlags::ENUM)
                });
            (
                if indexed {
                    format!("[{escaped}]")
                } else {
                    escaped
                },
                indexed,
            )
        } else {
            self.literal_artifact_symbol_name(symbol)?
                .unwrap_or((name, false))
        };
        let mut names = Vec::new();
        let mut owner = record.parent();
        while let Some(parent) = owner {
            let record = self
                .store()
                .symbol(parent)
                .ok_or(CanonicalArtifactQueryError::ForeignSymbol(parent))?;
            if !record
                .flags()
                .intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE | SymbolFlags::ENUM)
            {
                break;
            }
            names.push(
                self.escaped_identifier_artifact_name(parent)?
                    .unwrap_or_else(|| record.name().escaped_display().to_string()),
            );
            owner = record.parent();
        }
        if names.is_empty() {
            return Ok(name);
        }
        names.reverse();
        let prefix = names.join(".");
        Ok(if indexed {
            format!("{prefix}{name}")
        } else {
            format!("{prefix}.{name}")
        })
    }

    /// Renders a symbol with the shortest name visible at `enclosing`.
    ///
    /// # Errors
    ///
    /// Returns an error for foreign source nodes, invalid symbol chains, or
    /// alias targets that cannot be proved from their declarations.
    pub fn symbol_to_string_at_location(
        &mut self,
        symbol: SemanticSymbolId,
        enclosing: NodeRef,
    ) -> Result<String, CanonicalArtifactQueryError> {
        self.with_display_alias_transaction(|context| {
            context.symbol_to_string_at_location_worker(symbol, enclosing)
        })
    }

    fn symbol_to_string_at_location_worker(
        &mut self,
        symbol: SemanticSymbolId,
        enclosing: NodeRef,
    ) -> Result<String, CanonicalArtifactQueryError> {
        self.validated_artifact_node(enclosing)?;
        self.get_symbol_declarations(symbol)?;
        let record = self
            .store()
            .symbol(symbol)
            .ok_or(CanonicalArtifactQueryError::ForeignSymbol(symbol))?;
        let indexed = record
            .check_flags()
            .contains(ts_binder::CheckFlags::INDEX_SYMBOL);
        let index_name = indexed.then(|| format!("[{}]", record.name().escaped_display()));
        let chain_symbol = if indexed {
            record.parent()
        } else {
            Some(symbol)
        };
        let chain = chain_symbol
            .map(|symbol| self.artifact_symbol_chain(symbol, enclosing))
            .transpose()
            .map_err(CanonicalArtifactQueryError::SymbolDisplay)?
            .unwrap_or_default();
        let mut result = String::new();
        for symbol in chain {
            let (name, indexed) =
                self.artifact_symbol_name_as_written(symbol, enclosing, !result.is_empty())?;
            if !result.is_empty() && !indexed {
                result.push('.');
            }
            result.push_str(&name);
        }
        if let Some(index) = index_name {
            result.push_str(&index);
        }
        Ok(result)
    }

    fn artifact_symbol_name_as_written(
        &self,
        symbol: SemanticSymbolId,
        enclosing: NodeRef,
        qualified: bool,
    ) -> Result<(String, bool), CanonicalArtifactQueryError> {
        let record = self
            .store()
            .symbol(symbol)
            .ok_or(CanonicalArtifactQueryError::ForeignSymbol(symbol))?;
        if record.name() == InternalSymbolName::Global.as_ref() {
            return Ok(("global".to_owned(), false));
        }
        if let Some(name) = self.private_artifact_symbol_name(symbol)? {
            return Ok((name, false));
        }
        if let Some(name) = self
            .written_default_symbol_name(symbol, enclosing, !qualified)
            .map_err(CanonicalArtifactQueryError::SymbolDisplay)?
        {
            return Ok((name, false));
        }
        if let Some((name, indexed)) = self.literal_artifact_symbol_name(symbol)? {
            return Ok(if qualified && !indexed {
                (format!("[{name}]"), true)
            } else {
                (name, indexed)
            });
        }
        if let Some(name) = self.escaped_identifier_artifact_name(symbol)? {
            let indexed = record.flags().intersects(
                SymbolFlags::PROPERTY
                    | SymbolFlags::METHOD
                    | SymbolFlags::ACCESSOR
                    | SymbolFlags::ENUM_MEMBER,
            ) && record
                .parent()
                .and_then(|parent| self.store().symbol(parent))
                .is_some_and(|parent| {
                    parent
                        .flags()
                        .intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE | SymbolFlags::ENUM)
                });
            return Ok((if indexed { format!("[{name}]") } else { name }, indexed));
        }
        for declaration in record.declarations().unwrap_or_default() {
            let (arena, _, node) = self.validated_artifact_node(*declaration)?;
            if declaration_name(&node.data).is_some() {
                break;
            }
            if matches!(
                node.kind,
                SyntaxKind::FunctionExpression
                    | SyntaxKind::ArrowFunction
                    | SyntaxKind::ClassExpression
            ) && let Some(NodeData::VariableDeclaration(variable)) = node
                .parent
                .and_then(|parent| arena.get(parent))
                .map(|node| &node.data)
                && variable.initializer == Some(declaration.node)
                && let Some(NodeData::Identifier(name)) =
                    arena.get(variable.name).map(|node| &node.data)
            {
                return Ok((name.text.clone(), false));
            }
        }
        Ok((record.name().escaped_display().to_string(), false))
    }

    fn prepare_artifact_type_location(
        &mut self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        let (_, bound, record) = self.validated_artifact_node(node)?;
        if !supports_type_location(&record.data)
            && bound.symbol(node).is_none()
            && self.store().type_node_links(node).is_some_and(|links| {
                links.resolved_type.is_some() || links.outer_type_parameters.is_some()
            })
            && self.declaration_method_artifact_symbol(node)?.is_none()
        {
            return Err(CanonicalArtifactQueryError::UnsupportedNode {
                node,
                kind: record.kind,
            });
        }
        let declaration = self.type_declaration_artifact_symbol(node)?;
        self.type_reference_qualifier_artifact_type(node)?;
        self.preflight_literal_annotation_nodes(node)?;
        self.preflight_duplicate_property_artifact_nodes(node)?;
        self.preflight_enum_initializer_artifact_node(node)?;
        self.prepare_artifact_location(node)?;
        Ok(declaration)
    }

    fn prepare_artifact_location(
        &mut self,
        node: NodeRef,
    ) -> Result<(), CanonicalArtifactQueryError> {
        let needs_source_check = {
            let (_, bound, _) = self.validated_artifact_node(node)?;
            let declaration_file = bound
                .source_facts()
                .is_some_and(|facts| facts.is_declaration_file() || facts.is_default_library());
            let source = self
                .source_file(node.file)
                .ok_or(CanonicalArtifactQueryError::MissingFile(node.file))?;
            !declaration_file
                && !self
                    .store()
                    .source_file_links(source)
                    .is_some_and(|links| links.type_checked)
        };
        if needs_source_check {
            self.check_source_file(node.file)?;
        }
        Ok(())
    }

    fn validated_artifact_node(
        &self,
        node: NodeRef,
    ) -> Result<(&NodeArena, &BoundFile, &Node), CanonicalArtifactQueryError> {
        let (arena, bound) = self
            .file(node.file)
            .ok_or(CanonicalArtifactQueryError::MissingFile(node.file))?;
        if arena.revision() != bound.node_arena_revision() {
            return Err(CanonicalArtifactQueryError::StaleFile {
                file: node.file,
                expected: bound.node_arena_revision(),
                actual: arena.revision(),
            });
        }
        if !node.is_for(arena.id(), bound.file_id())
            || !bound.contains(node)
            || !self.store().contains_node_ref(node)
        {
            return Err(CanonicalArtifactQueryError::ForeignNode(node));
        }
        let record = arena
            .get(node.node)
            .ok_or(CanonicalArtifactQueryError::ForeignNode(node))?;
        Ok((arena, bound, record))
    }

    fn cached_artifact_type(
        &self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let Some(type_) = self
            .store()
            .type_node_links(node)
            .and_then(|links| links.resolved_type)
        else {
            return Ok(None);
        };
        self.validate_artifact_type(node, type_).map(Some)
    }

    #[allow(clippy::too_many_lines)] // Keep the source recovery and cache checks together.
    fn unresolved_namespace_declaration_type(
        &self,
        node: NodeRef,
        declaration: NodeRef,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let (arena, bound, record) = self.validated_artifact_node(declaration)?;
        let NodeData::NamespaceImport(namespace) = &record.data else {
            return Ok(None);
        };
        if namespace.name != node.node {
            return Ok(None);
        }
        let source = self
            .source_file(node.file)
            .ok_or(CanonicalArtifactQueryError::MissingFile(node.file))?;
        if !self
            .store()
            .source_file_links(source)
            .is_some_and(|links| links.type_checked)
        {
            return Ok(None);
        }
        let clause = record
            .parent
            .map(|parent| NodeRef::new(declaration.arena, declaration.file, parent))
            .ok_or(CanonicalArtifactQueryError::ForeignNode(declaration))?;
        let import = self
            .validated_artifact_node(clause)?
            .2
            .parent
            .map(|parent| NodeRef::new(declaration.arena, declaration.file, parent))
            .ok_or(CanonicalArtifactQueryError::ForeignNode(clause))?;
        let NodeData::ImportDeclaration(import_data) =
            &self.validated_artifact_node(import)?.2.data
        else {
            return Ok(None);
        };
        let specifier = NodeRef::new(import.arena, import.file, import_data.module_specifier);
        if self.module_resolution(specifier) != CanonicalModuleResolutionLookup::Unresolved {
            return Ok(None);
        }
        let alias = bound
            .symbol(declaration)
            .ok_or(CanonicalArtifactQueryError::ForeignNode(declaration))?;
        let invalid = || CanonicalArtifactQueryError::InvalidSymbol {
            node,
            symbol: alias,
        };
        let import = plan_top_level_named_value_import(arena, bound, self.store(), import)
            .map_err(|_| invalid())?;
        let [binding] = import.bindings.as_slice() else {
            return Err(invalid());
        };
        if binding.declaration != declaration
            || binding.local_name != node
            || binding.alias_symbol != alias
        {
            return Err(invalid());
        }
        // Reuse the source recovery proof for this exact retained unresolved entry.
        let failure = SourceImportError::Alias(CanonicalAliasResolutionError::TargetUnavailable {
            alias,
            reason: CanonicalAliasTargetUnavailable::ModuleResolutionUnresolved(specifier),
        });
        let read = unresolved_namespace_import_read(
            arena,
            bound,
            source,
            self.store(),
            &import,
            binding,
            &failure,
        )
        .ok_or_else(invalid)?;
        let error_type = self
            .store()
            .intrinsic_bootstrap()
            .ok_or_else(invalid)?
            .error_type;
        let expected = TypeNodeLinks {
            resolved_type: Some(error_type),
            ..TypeNodeLinks::default()
        };
        for cached_node in [node, declaration, read] {
            if let Some(links) = self.store().type_node_links(cached_node)
                && links != &TypeNodeLinks::default()
                && links != &expected
            {
                return Err(CanonicalArtifactQueryError::InvalidType {
                    node: cached_node,
                    type_: links.resolved_type.unwrap_or(error_type),
                });
            }
            if let Some(symbol) = self
                .store()
                .symbol_node_links(cached_node)
                .and_then(|links| links.resolved_symbol)
                && symbol != alias
            {
                return Err(CanonicalArtifactQueryError::InvalidSymbol {
                    node: cached_node,
                    symbol,
                });
            }
        }
        if self.cached_artifact_type(read)? != Some(error_type) {
            return Err(CanonicalArtifactQueryError::MissingType {
                node: read,
                kind: SyntaxKind::Identifier,
            });
        }
        self.validate_artifact_type(node, error_type).map(Some)
    }

    fn catch_rest_artifact_type(
        &self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let (arena, bound, record) = self.validated_artifact_node(node)?;
        let element = match &record.data {
            NodeData::BindingElement(_) => node,
            NodeData::Identifier(_) => {
                let Some(LocationParent::Declaration(declaration)) =
                    location_parent(arena, bound, node, record)?
                else {
                    return Ok(None);
                };
                if self.validated_artifact_node(declaration)?.2.kind != SyntaxKind::BindingElement {
                    return Ok(None);
                }
                declaration
            }
            _ => return Ok(None),
        };
        let mut catch = element;
        for kind in [
            SyntaxKind::ObjectBindingPattern,
            SyntaxKind::VariableDeclaration,
            SyntaxKind::CatchClause,
        ] {
            let Some(parent) = self.validated_artifact_node(catch)?.2.parent else {
                return Ok(None);
            };
            catch = NodeRef::new(node.arena, node.file, parent);
            if self.validated_artifact_node(catch)?.2.kind != kind {
                return Ok(None);
            }
        }
        let unsupported = || CanonicalArtifactQueryError::UnsupportedNode {
            node,
            kind: record.kind,
        };
        if bound
            .source_facts()
            .is_none_or(|facts| facts.is_declaration_file() || facts.is_default_library())
        {
            return Err(unsupported());
        }
        let statement = self
            .validated_artifact_node(catch)?
            .2
            .parent
            .map(|parent| NodeRef::new(node.arena, node.file, parent))
            .ok_or_else(unsupported)?;
        let source = self
            .source_file(node.file)
            .ok_or(CanonicalArtifactQueryError::MissingFile(node.file))?;
        let (name, symbol) = super::source::catch_object_rest_artifact_binding(
            arena,
            bound,
            source,
            self.store(),
            statement,
        )?;
        if bound.symbol(element) != Some(symbol) || node != element && node != name {
            return Err(CanonicalArtifactQueryError::InvalidSymbol { node, symbol });
        }
        let bootstrap = self.store().intrinsic_bootstrap().ok_or_else(unsupported)?;
        let type_ = if self.options().use_unknown_in_catch_variables {
            bootstrap.error_type
        } else {
            bootstrap.any_type
        };
        for location in [element, name] {
            if let Some(links) = self.store().type_node_links(location)
                && links != &TypeNodeLinks::default()
                && links
                    != &(TypeNodeLinks {
                        resolved_type: Some(type_),
                        ..TypeNodeLinks::default()
                    })
            {
                return Err(CanonicalArtifactQueryError::InvalidType {
                    node: location,
                    type_: links.resolved_type.unwrap_or(type_),
                });
            }
            if let Some(cached) = self
                .store()
                .symbol_node_links(location)
                .and_then(|links| links.resolved_symbol)
                && cached != symbol
            {
                return Err(CanonicalArtifactQueryError::InvalidSymbol {
                    node: location,
                    symbol: cached,
                });
            }
        }
        Ok(Some(type_))
    }

    fn type_reference_qualifier_artifact_type(
        &self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let (_, _, record) = self.validated_artifact_node(node)?;
        if !matches!(
            record.data,
            NodeData::Identifier(_) | NodeData::QualifiedName(_)
        ) {
            return Ok(None);
        }
        let kind = record.kind;
        let mut current = node;
        let mut is_qualifier = false;
        loop {
            let (_, _, record) = self.validated_artifact_node(current)?;
            let Some(parent) = record.parent else {
                return Ok(None);
            };
            let parent = NodeRef::new(node.arena, node.file, parent);
            let (_, _, record) = self.validated_artifact_node(parent)?;
            match &record.data {
                NodeData::QualifiedName(name)
                    if name.left == current.node || name.right == current.node =>
                {
                    is_qualifier |= name.left == current.node;
                    current = parent;
                }
                NodeData::TypeReferenceNode(reference)
                    if is_qualifier && reference.type_name == current.node =>
                {
                    break;
                }
                _ => return Ok(None),
            }
        }

        // Pinned getTypeOfNode treats only the final name as a type node.
        // Namespace prefixes are neither type nodes nor expressions.
        let type_ = self
            .store()
            .intrinsic_bootstrap()
            .ok_or(CanonicalArtifactQueryError::MissingType { node, kind })?
            .error_type;
        if self.store().type_node_links(node).is_some_and(|links| {
            links.outer_type_parameters.is_some()
                || links.resolved_type.is_some_and(|cached| cached != type_)
        }) {
            return Err(CanonicalArtifactQueryError::InvalidType {
                node,
                type_: self
                    .store()
                    .type_node_links(node)
                    .and_then(|links| links.resolved_type)
                    .unwrap_or(type_),
            });
        }
        self.validate_artifact_type(node, type_).map(Some)
    }

    fn arrow_artifact_type(
        &self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let (_, bound, record) = self.validated_artifact_node(node)?;
        if !matches!(record.data, NodeData::ArrowFunction(_)) {
            return Ok(None);
        }
        let cached = self
            .store()
            .type_node_links(node)
            .and_then(|links| links.resolved_type);
        let owner = bound.symbol(node);
        let source_callable = self
            .store()
            .source_callable_type_for_declaration(node)
            .or_else(|| owner.and_then(|owner| self.store().source_callable_type_for_owner(owner)))
            .or_else(|| {
                owner
                    .and_then(|owner| self.store().value_symbol_links(owner))
                    .and_then(|links| links.resolved_type)
                    .filter(|type_| self.store().source_callable_provenance(*type_).is_some())
            })
            .or_else(|| {
                cached.filter(|type_| self.store().source_callable_provenance(*type_).is_some())
            });
        let Some(type_) = source_callable else {
            return Ok(None);
        };
        let valid_owner =
            self.store()
                .source_callable_provenance(type_)
                .is_some_and(|provenance| {
                    provenance.declaration == node && owner == Some(provenance.owner_symbol)
                });
        if !valid_owner
            || !matches!(
                validate_stored_source_callable(self.store(), type_),
                StoredSourceCallableValidation::Valid(_)
            )
        {
            return Err(CanonicalArtifactQueryError::InvalidType { node, type_ });
        }
        if self.store().type_node_links(node).is_some_and(|links| {
            links != &TypeNodeLinks::default()
                && links
                    != &(TypeNodeLinks {
                        resolved_type: Some(type_),
                        ..TypeNodeLinks::default()
                    })
        }) {
            return Err(CanonicalArtifactQueryError::InvalidType {
                node,
                type_: cached.unwrap_or(type_),
            });
        }
        Ok(Some(type_))
    }

    #[allow(clippy::too_many_lines)] // Keep declaration ownership and each cache-origin check together.
    fn type_declaration_artifact_symbol(
        &self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        let (symbol, declaration, is_enum) = {
            let (arena, bound, record) = self.validated_artifact_node(node)?;
            let declaration = if matches!(
                record.data,
                NodeData::ClassDeclaration(_)
                    | NodeData::InterfaceDeclaration(_)
                    | NodeData::EnumDeclaration(_)
            ) {
                node
            } else if let Some(parent) = record.parent {
                let Some(parent_record) = arena.get(parent) else {
                    return Ok(None);
                };
                if !matches!(
                    parent_record.data,
                    NodeData::ClassDeclaration(_)
                        | NodeData::InterfaceDeclaration(_)
                        | NodeData::EnumDeclaration(_)
                ) || declaration_name(&parent_record.data) != Some(node.node)
                {
                    return Ok(None);
                }
                NodeRef::new(node.arena, node.file, parent)
            } else {
                return Ok(None);
            };
            let symbol =
                bound
                    .symbol(declaration)
                    .ok_or(CanonicalArtifactQueryError::MissingType {
                        node,
                        kind: record.kind,
                    })?;
            (
                self.merged_artifact_symbol(node, symbol)?,
                declaration,
                matches!(
                    self.validated_artifact_node(declaration)?.2.data,
                    NodeData::EnumDeclaration(_)
                ),
            )
        };
        if matches!(
            self.validated_artifact_node(declaration)?.2.data,
            NodeData::InterfaceDeclaration(_)
        ) && self.store().symbol(symbol).is_none_or(|owner| {
            !owner.flags().contains(SymbolFlags::INTERFACE)
                || owner
                    .declarations()
                    .is_none_or(|declarations| !declarations.contains(&declaration))
        }) {
            return Err(CanonicalArtifactQueryError::InvalidSymbol { node, symbol });
        }
        let cached = self.cached_artifact_type(node)?;
        if is_enum {
            if self.store().get_merged_symbol(symbol) != Some(symbol) {
                return Err(CanonicalArtifactQueryError::InvalidSymbol { node, symbol });
            }
            let owner = self
                .store()
                .symbol(symbol)
                .ok_or(CanonicalArtifactQueryError::InvalidSymbol { node, symbol })?;
            let declarations = owner.declarations().unwrap_or_default();
            if !declarations.contains(&declaration)
                || !owner
                    .value_declaration()
                    .is_some_and(|value| declarations.contains(&value))
            {
                return Err(CanonicalArtifactQueryError::InvalidSymbol { node, symbol });
            }
            self.preflight_enum_type(symbol)?;
            let declared = self
                .store()
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type);
            if self
                .store()
                .type_node_links(node)
                .is_some_and(|links| links.outer_type_parameters.is_some())
                || cached.is_some() && cached != declared
            {
                return Err(
                    DeclaredTypeError::Enum(super::enums::EnumTypeError::Invariant(
                        super::enums::EnumTypeInvariant::InvalidCache(symbol),
                    ))
                    .into(),
                );
            }
        } else if let Some(cached) = cached {
            let declared = if matches!(
                self.validated_artifact_node(declaration)?.2.data,
                NodeData::ClassDeclaration(_)
            ) || self
                .store()
                .symbol(symbol)
                .is_some_and(|owner| owner.flags().contains(SymbolFlags::CLASS))
            {
                super::declared::cached_class_type(self.store(), symbol)?
            } else {
                super::declared::cached_interface_type(self.store(), symbol)?
            };
            if declared != Some(cached) {
                return Err(CanonicalArtifactQueryError::InvalidType {
                    node,
                    type_: cached,
                });
            }
        }
        Ok(Some(symbol))
    }

    fn preflight_duplicate_property_artifact_nodes(
        &self,
        node: NodeRef,
    ) -> Result<
        Option<(super::classes::RecoveredClassPropertyType, bool)>,
        CanonicalArtifactQueryError,
    > {
        let (arena, bound, record) = self.validated_artifact_node(node)?;
        let declaration = if matches!(record.data, NodeData::PropertyDeclaration(_)) {
            node
        } else if let Some(parent) = record.parent
            && let Some(NodeData::PropertyDeclaration(property)) =
                arena.get(parent).map(|record| &record.data)
            && (property.name == node.node
                || property.type_ == Some(node.node)
                || property.initializer == Some(node.node))
        {
            NodeRef::new(node.arena, node.file, parent)
        } else {
            return Ok(None);
        };
        let (_, _, declaration_record) = self.validated_artifact_node(declaration)?;
        let Some(parent) = declaration_record.parent else {
            return Ok(None);
        };
        let class_node = NodeRef::new(node.arena, node.file, parent);
        let (_, _, class_record) = self.validated_artifact_node(class_node)?;
        let NodeData::ClassDeclaration(class) = &class_record.data else {
            return Ok(None);
        };

        let mut symbols = HashSet::new();
        let has_duplicate = class
            .members
            .nodes
            .iter()
            .filter_map(|member| {
                let member = NodeRef::new(node.arena, node.file, *member);
                if !matches!(
                    arena.get(member.node)?.data,
                    NodeData::PropertyDeclaration(_)
                ) {
                    return None;
                }
                bound.symbol(member)
            })
            .any(|symbol| !symbols.insert(symbol));
        if !has_duplicate {
            return Ok(None);
        }

        let symbol = bound
            .symbol(declaration)
            .ok_or(CanonicalArtifactQueryError::MissingType {
                node,
                kind: record.kind,
            })?;
        let owner = bound
            .symbol(class_node)
            .ok_or(CanonicalArtifactQueryError::MissingType {
                node,
                kind: record.kind,
            })?;
        let invalid = || CanonicalArtifactQueryError::InvalidSymbol { node, symbol };
        let host = self.declared_type_host()?;
        let grammar = super::classes::plan_class_grammar_diagnostics(self.store(), &host, owner)
            .ok_or_else(invalid)?;
        if grammar.declaration != class_node
            || grammar.symbol != owner
            || !grammar
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == 2300)
        {
            return Err(invalid());
        }
        let plan = super::classes::plan_recovered_class_property(self.store(), &host, symbol)
            .ok_or_else(invalid)?;
        if plan.class != class_node || plan.owner != owner {
            return Err(invalid());
        }
        let property = plan
            .declarations
            .iter()
            .find(|property| property.declaration == declaration)
            .ok_or_else(invalid)?;
        let type_source = if property.annotation == Some(node) {
            super::classes::RecoveredClassPropertyType::Annotation(node)
        } else {
            plan.type_source
        };
        Ok(Some((type_source, property.initializer == node)))
    }

    fn duplicate_property_artifact_type(
        &mut self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let Some((source, initializer)) = self.preflight_duplicate_property_artifact_nodes(node)?
        else {
            return Ok(None);
        };
        if initializer {
            return self.primitive_initializer_artifact_type(node).map(Some);
        }
        let type_ = match source {
            super::classes::RecoveredClassPropertyType::Annotation(annotation) => {
                self.get_type_from_type_node(annotation)?
            }
            super::classes::RecoveredClassPropertyType::Initializer(initializer) => {
                let literal = self.primitive_initializer_artifact_type(initializer)?;
                let fresh = self
                    .store()
                    .fresh_type_of_literal_type(literal)
                    .map_err(|_| CanonicalArtifactQueryError::InvalidType {
                        node: initializer,
                        type_: literal,
                    })?;
                super::source::widened_fresh_literal_type(self.store(), fresh)?
            }
        };
        let host = self.declared_type_host()?;
        if super::classes::recovered_class_property_type(self.store(), &host, source) != Some(type_)
        {
            return Err(CanonicalArtifactQueryError::InvalidType { node, type_ });
        }
        if self.store().type_node_links(node).is_some_and(|links| {
            links.outer_type_parameters.is_some()
                || links.resolved_type.is_some_and(|cached| cached != type_)
        }) {
            return Err(CanonicalArtifactQueryError::InvalidType {
                node,
                type_: self.cached_artifact_type(node)?.unwrap_or(type_),
            });
        }
        self.validate_artifact_type(node, type_).map(Some)
    }

    fn enum_initializer_artifact_type(
        &mut self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        if !self.preflight_enum_initializer_artifact_node(node)? {
            return Ok(None);
        }
        self.primitive_initializer_artifact_type(node).map(Some)
    }

    fn preflight_enum_initializer_artifact_node(
        &self,
        node: NodeRef,
    ) -> Result<bool, CanonicalArtifactQueryError> {
        let owner = {
            let (arena, bound, record) = self.validated_artifact_node(node)?;
            if !matches!(
                record.data,
                NodeData::StringLiteral(_) | NodeData::NumericLiteral(_)
            ) {
                return Ok(false);
            }
            let Some(member_id) = record.parent else {
                return Ok(false);
            };
            let member = NodeRef::new(node.arena, node.file, member_id);
            let (_, _, member_record) = self.validated_artifact_node(member)?;
            let NodeData::EnumMember(data) = &member_record.data else {
                return Ok(false);
            };
            if data.initializer != Some(node.node) {
                return Ok(false);
            }
            let declaration = member_record
                .parent
                .ok_or(CanonicalArtifactQueryError::ForeignNode(member))?;
            if !matches!(arena.get(declaration).map(|record| &record.data),
                Some(NodeData::EnumDeclaration(enumeration))
                    if enumeration.members.nodes.iter().filter(|member| **member == member_id).count() == 1)
            {
                return Err(CanonicalArtifactQueryError::ForeignNode(member));
            }
            let declaration = NodeRef::new(node.arena, node.file, declaration);
            let owner = bound
                .symbol(declaration)
                .ok_or(CanonicalArtifactQueryError::ForeignNode(declaration))?;
            self.merged_artifact_symbol(node, owner)?
        };
        self.preflight_enum_type(owner)?;
        self.preflight_primitive_initializer_artifact_node(node)?;
        Ok(true)
    }

    fn primitive_initializer_artifact_type(
        &mut self,
        node: NodeRef,
    ) -> Result<TypeId, CanonicalArtifactQueryError> {
        let (_, _, record) = self.validated_artifact_node(node)?;
        let value = match &record.data {
            NodeData::StringLiteral(literal) => super::EvaluatorValue::String(literal.text.clone()),
            NodeData::NumericLiteral(literal) => super::EvaluatorValue::Number(
                normalize_numeric_separators(&literal.text)
                    .map(|text| ts_jsnum::from_string(&text))
                    .filter(|value| !value.is_nan())
                    .ok_or(CanonicalArtifactQueryError::UnsupportedNode {
                        node,
                        kind: record.kind,
                    })?,
            ),
            _ => {
                return Err(CanonicalArtifactQueryError::UnsupportedNode {
                    node,
                    kind: record.kind,
                });
            }
        };
        self.preflight_primitive_initializer_artifact_node(node)?;
        let type_ = self.artifact_literal_type(value)?;
        self.validate_artifact_type(node, type_)
    }

    fn preflight_primitive_initializer_artifact_node(
        &self,
        node: NodeRef,
    ) -> Result<(), CanonicalArtifactQueryError> {
        let (_, _, record) = self.validated_artifact_node(node)?;
        let regular = self.cached_literal_annotation_identity(node)?;
        let cached = self.cached_artifact_type(node)?;
        if let Some(cached) = cached
            && !regular.is_some_and(|regular| {
                (cached == regular
                    || self
                        .store()
                        .fresh_type_of_literal_type(regular)
                        .is_ok_and(|fresh| cached == fresh))
                    && self.store().validate_union_constituent(regular).is_ok()
            })
        {
            return Err(CanonicalArtifactQueryError::InvalidType {
                node,
                type_: cached,
            });
        }
        if self
            .store()
            .type_node_links(node)
            .is_some_and(|links| links.outer_type_parameters.is_some())
        {
            return Err(CanonicalArtifactQueryError::MissingType {
                node,
                kind: record.kind,
            });
        }
        if let Some(symbol) = self
            .store()
            .symbol_node_links(node)
            .and_then(|links| links.resolved_symbol)
        {
            return Err(CanonicalArtifactQueryError::InvalidSymbol { node, symbol });
        }
        Ok(())
    }

    fn checked_conditional_literal_artifact_type(
        &self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let (_, _, record) = self.validated_artifact_node(node)?;
        let scalar_literal = match record.data {
            NodeData::StringLiteral(_)
            | NodeData::NoSubstitutionTemplateLiteral(_)
            | NodeData::NumericLiteral(_)
            | NodeData::BigIntLiteral(_) => true,
            NodeData::KeywordExpression(_) => matches!(
                record.kind,
                SyntaxKind::TrueKeyword | SyntaxKind::FalseKeyword | SyntaxKind::NullKeyword
            ),
            _ => false,
        };
        if !scalar_literal {
            return Ok(None);
        }
        let Some(parent) = record.parent else {
            return Ok(None);
        };
        let parent = NodeRef::new(node.arena, node.file, parent);
        let (_, _, parent_record) = self.validated_artifact_node(parent)?;
        let NodeData::ConditionalExpression(conditional) = &parent_record.data else {
            return Ok(None);
        };
        if [
            conditional.condition,
            conditional.when_true,
            conditional.when_false,
        ]
        .into_iter()
        .filter(|child| *child == node.node)
        .count()
            != 1
        {
            return Err(CanonicalArtifactQueryError::ForeignNode(node));
        }
        let source = self
            .source_file(node.file)
            .ok_or(CanonicalArtifactQueryError::MissingFile(node.file))?;
        if !self
            .store()
            .source_file_links(source)
            .is_some_and(|links| links.type_checked)
        {
            return Ok(None);
        }
        let parent_type =
            self.cached_artifact_type(parent)?
                .ok_or(CanonicalArtifactQueryError::MissingType {
                    node: parent,
                    kind: parent_record.kind,
                })?;
        if self
            .store()
            .type_node_links(parent)
            .is_some_and(|links| links.outer_type_parameters.is_some())
        {
            return Err(CanonicalArtifactQueryError::InvalidType {
                node: parent,
                type_: parent_type,
            });
        }

        // Scalar conditional checking retains literal pairs without child links.
        let regular = self.cached_literal_annotation_identity(node)?.ok_or(
            CanonicalArtifactQueryError::MissingType {
                node,
                kind: record.kind,
            },
        )?;
        let type_ = if record.kind == SyntaxKind::NullKeyword {
            self.store()
                .intrinsic_bootstrap()
                .map(|bootstrap| bootstrap.null_widening_type)
                .ok_or(CanonicalArtifactQueryError::MissingType {
                    node,
                    kind: record.kind,
                })?
        } else {
            self.store()
                .fresh_type_of_literal_type(regular)
                .map_err(|_| CanonicalArtifactQueryError::InvalidType {
                    node,
                    type_: regular,
                })?
        };
        if self.store().type_node_links(node).is_some_and(|links| {
            links.outer_type_parameters.is_some()
                || links.resolved_type.is_some_and(|cached| cached != type_)
        }) {
            return Err(CanonicalArtifactQueryError::InvalidType {
                node,
                type_: self.cached_artifact_type(node)?.unwrap_or(type_),
            });
        }
        if let Some(symbol) = self
            .store()
            .symbol_node_links(node)
            .and_then(|links| links.resolved_symbol)
        {
            return Err(CanonicalArtifactQueryError::InvalidSymbol { node, symbol });
        }
        self.validate_artifact_type(node, type_).map(Some)
    }

    fn literal_annotation_artifact_type(
        &mut self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let Some((annotation, literal)) = self.preflight_literal_annotation_nodes(node)? else {
            return Ok(None);
        };
        let type_ = self.get_type_from_type_node(annotation)?;
        let type_ = if node != literal && node != annotation {
            self.cached_literal_annotation_identity(node)?.ok_or(
                CanonicalArtifactQueryError::MissingType {
                    node,
                    kind: self.validated_artifact_node(node)?.2.kind,
                },
            )?
        } else {
            type_
        };
        self.validate_artifact_type(node, type_).map(Some)
    }

    fn preflight_literal_annotation_nodes(
        &self,
        node: NodeRef,
    ) -> Result<Option<(NodeRef, NodeRef)>, CanonicalArtifactQueryError> {
        let Some((annotation, literal)) = self.literal_annotation_nodes(node)? else {
            return Ok(None);
        };
        let operand = (node != literal && node != annotation).then_some(node);

        // Type-node queries cache the annotation, not its literal child.
        // Check both against the literal table before resolving a cold query.
        for location in [literal, annotation].into_iter().chain(operand) {
            let cached = self.cached_artifact_type(location)?;
            if self
                .store()
                .type_node_links(location)
                .is_some_and(|links| links.outer_type_parameters.is_some())
            {
                return Err(CanonicalArtifactQueryError::MissingType {
                    node: location,
                    kind: self.validated_artifact_node(location)?.2.kind,
                });
            }
            let identity = if Some(location) == operand {
                location
            } else {
                literal
            };
            if let Some(cached) = cached
                && (self.cached_literal_annotation_identity(identity)? != Some(cached)
                    || self.store().validate_union_constituent(cached).is_err())
            {
                return Err(CanonicalArtifactQueryError::InvalidType {
                    node: location,
                    type_: cached,
                });
            }
        }
        if let Some(operand) = operand {
            if let Some(type_) = self.cached_literal_annotation_identity(operand)? {
                if self.store().validate_union_constituent(type_).is_err() {
                    return Err(CanonicalArtifactQueryError::InvalidType {
                        node: operand,
                        type_,
                    });
                }
            } else if self.cached_artifact_type(annotation)?.is_some() {
                return Err(CanonicalArtifactQueryError::MissingType {
                    node: operand,
                    kind: self.validated_artifact_node(operand)?.2.kind,
                });
            }
        }
        Ok(Some((annotation, literal)))
    }

    fn literal_annotation_nodes(
        &self,
        node: NodeRef,
    ) -> Result<Option<(NodeRef, NodeRef)>, CanonicalArtifactQueryError> {
        let (_, _, record) = self.validated_artifact_node(node)?;
        if let NodeData::LiteralTypeNode(literal) = &record.data {
            let literal = NodeRef::new(node.arena, node.file, literal.literal);
            if self.validated_artifact_node(literal)?.2.parent != Some(node.node) {
                return Err(CanonicalArtifactQueryError::ForeignNode(literal));
            }
            return Ok(Some((node, literal)));
        }
        let Some(parent) = record.parent else {
            return Ok(None);
        };
        let parent = NodeRef::new(node.arena, node.file, parent);
        let (_, _, parent_record) = self.validated_artifact_node(parent)?;
        let (annotation, literal) = if let NodeData::PrefixUnaryExpression(prefix) =
            &parent_record.data
            && prefix.operator == SyntaxKind::MinusToken
            && prefix.operand == node.node
            && matches!(
                record.data,
                NodeData::NumericLiteral(_) | NodeData::BigIntLiteral(_)
            ) {
            let Some(annotation) = parent_record.parent else {
                return Ok(None);
            };
            (NodeRef::new(node.arena, node.file, annotation), parent)
        } else {
            (parent, node)
        };
        let (_, _, annotation_record) = self.validated_artifact_node(annotation)?;
        let NodeData::LiteralTypeNode(data) = &annotation_record.data else {
            return Ok(None);
        };
        if data.literal != literal.node {
            return Err(CanonicalArtifactQueryError::ForeignNode(literal));
        }
        Ok(Some((annotation, literal)))
    }

    fn cached_literal_annotation_identity(
        &self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let (_, _, record) = self.validated_artifact_node(node)?;
        let Some(bootstrap) = self.store().intrinsic_bootstrap() else {
            return Ok(None);
        };
        let (record, negative) = if let NodeData::PrefixUnaryExpression(prefix) = &record.data {
            if prefix.operator != SyntaxKind::MinusToken {
                return Ok(None);
            }
            let operand = NodeRef::new(node.arena, node.file, prefix.operand);
            let (_, _, operand_record) = self.validated_artifact_node(operand)?;
            if operand_record.parent != Some(node.node) {
                return Err(CanonicalArtifactQueryError::ForeignNode(operand));
            }
            (operand_record, true)
        } else {
            (record, false)
        };
        Ok(match &record.data {
            NodeData::KeywordExpression(_) if !negative => match record.kind {
                SyntaxKind::TrueKeyword => Some(bootstrap.regular_true_type),
                SyntaxKind::FalseKeyword => Some(bootstrap.regular_false_type),
                SyntaxKind::NullKeyword => Some(bootstrap.null_type),
                _ => None,
            },
            NodeData::StringLiteral(literal) if !negative => {
                bootstrap.cached_string_literal_type(&literal.text)
            }
            NodeData::NoSubstitutionTemplateLiteral(literal) if !negative => {
                bootstrap.cached_string_literal_type(&literal.text)
            }
            NodeData::NumericLiteral(literal) => normalize_numeric_separators(&literal.text)
                .map(|text| ts_jsnum::from_string(&text))
                .filter(|value| !value.is_nan())
                .and_then(|value| {
                    bootstrap.cached_number_literal_type(if negative { -value } else { value })
                }),
            NodeData::BigIntLiteral(literal) => normalize_bigint_literal(&literal.text)
                .map(|text| PseudoBigInt::parse_valid(&text))
                .and_then(|value| {
                    bootstrap.cached_bigint_literal_type(&PseudoBigInt::new(
                        &value.base10_value,
                        negative,
                    ))
                }),
            _ => None,
        })
    }

    fn validate_artifact_type(
        &self,
        node: NodeRef,
        type_: TypeId,
    ) -> Result<TypeId, CanonicalArtifactQueryError> {
        self.store()
            .type_payload(type_)
            .map(|_| type_)
            .ok_or(CanonicalArtifactQueryError::InvalidType { node, type_ })
    }

    fn cached_artifact_symbol(
        &self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        let Some(symbol) = self
            .store()
            .symbol_node_links(node)
            .and_then(|links| links.resolved_symbol)
        else {
            return Ok(None);
        };
        let symbol = self.merged_artifact_symbol(node, symbol)?;
        if self
            .store()
            .intrinsic_bootstrap()
            .is_some_and(|bootstrap| symbol == bootstrap.unknown_symbol)
        {
            return Ok(None);
        }
        Ok(Some(symbol))
    }

    fn merged_artifact_symbol(
        &self,
        node: NodeRef,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, CanonicalArtifactQueryError> {
        self.store()
            .get_merged_symbol(symbol)
            .ok_or(CanonicalArtifactQueryError::InvalidSymbol { node, symbol })
    }

    fn module_declaration_artifact_type(
        &mut self,
        node: NodeRef,
        declaration: NodeRef,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let (_, bound, record) = self.validated_artifact_node(declaration)?;
        let NodeData::ModuleDeclaration(module) = &record.data else {
            return Ok(None);
        };
        if module.name != node.node || module.body.is_none() {
            return Ok(None);
        }
        let Some(symbol) = bound.symbol(declaration) else {
            return Ok(None);
        };
        let symbol = self.merged_artifact_symbol(node, symbol)?;
        let record = self
            .store()
            .symbol(symbol)
            .ok_or(CanonicalArtifactQueryError::InvalidSymbol { node, symbol })?;
        if module.keyword == SyntaxKind::GlobalKeyword
            && record.name() != InternalSymbolName::Global.as_ref()
        {
            return Err(CanonicalArtifactQueryError::InvalidSymbol { node, symbol });
        }
        let flags = record.flags();
        // A namespace declaration names the static side of its merged class.
        if flags.contains(SymbolFlags::CLASS) && flags.intersects(SymbolFlags::MODULE) {
            if self
                .cached_artifact_symbol(node)?
                .is_some_and(|cached| cached != symbol)
            {
                return Err(CanonicalArtifactQueryError::InvalidSymbol { node, symbol });
            }
            if let Some(cached) = self.cached_artifact_type(node)?
                && self
                    .store()
                    .value_symbol_links(symbol)
                    .and_then(|links| links.resolved_type)
                    != Some(cached)
            {
                return Err(CanonicalArtifactQueryError::InvalidType {
                    node,
                    type_: cached,
                });
            }
            return self.type_of_artifact_symbol(node, symbol);
        }
        if !super::source_namespaces::has_pure_module_flags(flags) {
            return Ok(None);
        }
        let type_ = self.get_type_of_module_value(symbol)?;
        self.validate_artifact_type(node, type_).map(Some)
    }

    fn shorthand_artifact_symbol(
        &self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        let (arena, bound, record) = self.validated_artifact_node(node)?;
        if !matches!(record.data, NodeData::Identifier(_)) {
            return Ok(None);
        }
        let Some(parent_id) = record.parent else {
            return Ok(None);
        };
        let Some(NodeData::ShorthandPropertyAssignment(shorthand)) =
            arena.get(parent_id).map(|parent| &parent.data)
        else {
            return Ok(None);
        };
        if shorthand.name != node.node {
            return Ok(None);
        }
        let declaration = NodeRef::new(node.arena, node.file, parent_id);
        let Some(symbol) = bound.symbol(declaration) else {
            return Ok(None);
        };
        self.merged_artifact_symbol(node, symbol).map(Some)
    }

    fn literal_computed_artifact_symbol(
        &self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        let (arena, bound, record) = self.validated_artifact_node(node)?;
        if !matches!(
            record.data,
            NodeData::StringLiteral(_)
                | NodeData::NumericLiteral(_)
                | NodeData::NoSubstitutionTemplateLiteral(_)
        ) {
            return Ok(None);
        }
        let Some(name_id) = record.parent else {
            return Ok(None);
        };
        let Some(name) = arena.get(name_id) else {
            return Ok(None);
        };
        let NodeData::ComputedPropertyName(computed) = &name.data else {
            return Ok(None);
        };
        if computed.expression != node.node {
            return Ok(None);
        }
        let Some(declaration_id) = name.parent else {
            return Ok(None);
        };
        let declaration = NodeRef::new(node.arena, node.file, declaration_id);
        let (_, _, declaration_record) = self.validated_artifact_node(declaration)?;
        if declaration_name(&declaration_record.data) != Some(name_id) {
            return Ok(None);
        }
        let Some(symbol) = bound.symbol(declaration) else {
            return Ok(None);
        };
        self.merged_artifact_symbol(node, symbol).map(Some)
    }

    fn expando_artifact_symbol(
        &self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        let (_, _, record) = self.validated_artifact_node(node)?;
        let access = match record.data {
            NodeData::PropertyAccessExpression(_) => node,
            NodeData::Identifier(_) => {
                let Some(parent) = record.parent else {
                    return Ok(None);
                };
                NodeRef::new(node.arena, node.file, parent)
            }
            _ => return Ok(None),
        };
        let (arena, bound, access_record) = self.validated_artifact_node(access)?;
        let NodeData::PropertyAccessExpression(property) = &access_record.data else {
            return Ok(None);
        };
        if node != access && property.name != node.node {
            return Ok(None);
        }
        let Some(parent) = access_record.parent else {
            return Ok(None);
        };
        let expression = NodeRef::new(node.arena, node.file, parent);
        let (_, _, expression_record) = self.validated_artifact_node(expression)?;
        let NodeData::BinaryExpression(binary) = &expression_record.data else {
            return Ok(None);
        };
        if binary.left != access.node {
            return Ok(None);
        }
        let Some(symbol) = bound.symbol(expression) else {
            return Ok(None);
        };
        let Some(parent) = expression_record.parent else {
            return Ok(None);
        };
        let statement = NodeRef::new(node.arena, node.file, parent);
        self.validated_artifact_node(statement)?;
        let invalid = || CanonicalArtifactQueryError::InvalidSymbol { node, symbol };

        let proven = if let Some(plan) = super::assignment::plan_function_expando_assignment(
            arena,
            bound,
            self.store(),
            statement,
        )
        .map_err(|_| invalid())?
        {
            Some((plan.left, plan.property_symbol, plan.property_symbol))
        } else {
            super::assignment::plan_arrow_expando_assignment(arena, bound, self.store(), statement)
                .map_err(|_| invalid())?
                .map(|plan| {
                    self.annotated_expando_artifact_symbol(
                        node,
                        plan.variable_symbol,
                        plan.property_symbol,
                    )
                    .map(|target| (plan.left, plan.property_symbol, target))
                })
                .transpose()?
        };
        let Some((left, property_symbol, target)) = proven else {
            return Ok(None);
        };
        if left != access || property_symbol != symbol {
            return Err(invalid());
        }

        for location in [access, node] {
            if let Some(cached) = self
                .store()
                .symbol_node_links(location)
                .and_then(|links| links.resolved_symbol)
                && self.merged_artifact_symbol(location, cached)? != target
            {
                return Err(CanonicalArtifactQueryError::InvalidSymbol {
                    node: location,
                    symbol: cached,
                });
            }
        }
        self.merged_artifact_symbol(node, target).map(Some)
    }

    fn annotated_expando_artifact_symbol(
        &self,
        node: NodeRef,
        variable: SemanticSymbolId,
        property: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, CanonicalArtifactQueryError> {
        let invalid = || CanonicalArtifactQueryError::InvalidSymbol {
            node,
            symbol: variable,
        };
        let declaration = self
            .store()
            .symbol(variable)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
            .ok_or_else(invalid)?;
        let (_, bound, record) = self.validated_artifact_node(declaration)?;
        let NodeData::VariableDeclaration(variable) = &record.data else {
            return Err(invalid());
        };
        let Some(annotation) = variable.type_ else {
            return Ok(property);
        };
        let annotation = NodeRef::new(declaration.arena, declaration.file, annotation);
        let name = self.store().symbol(property).ok_or_else(invalid)?.name();
        bound
            .symbol(annotation)
            .and_then(|symbol| self.store().symbol(symbol))
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| self.store().symbol_table(members))
            .and_then(|members| members.get(name))
            .ok_or_else(invalid)
    }

    #[allow(clippy::too_many_lines)] // Validate the private encoding against its source class and declarations.
    fn private_artifact_symbol_name(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<Option<String>, CanonicalArtifactQueryError> {
        let record = self
            .store()
            .symbol(symbol)
            .ok_or(CanonicalArtifactQueryError::ForeignSymbol(symbol))?;
        if !record.name().is_private_identifier() {
            return Ok(None);
        }
        let declarations = record
            .declarations()
            .filter(|nodes| !nodes.is_empty())
            .ok_or(CanonicalArtifactQueryError::ForeignSymbol(symbol))?;
        let declaration = record
            .value_declaration()
            .filter(|declaration| declarations.contains(declaration))
            .ok_or(CanonicalArtifactQueryError::InvalidSymbol {
                node: declarations[0],
                symbol,
            })?;
        let invalid = || CanonicalArtifactQueryError::InvalidSymbol {
            node: declaration,
            symbol,
        };
        let (_, _, member) = self.validated_artifact_node(declaration)?;
        let class = NodeRef::new(
            declaration.arena,
            declaration.file,
            member.parent.ok_or_else(invalid)?,
        );
        let (_, bound, class_record) = self.validated_artifact_node(class)?;
        let source_members = match &class_record.data {
            NodeData::ClassDeclaration(class) => &class.members.nodes,
            NodeData::ClassExpression(class) => &class.members.nodes,
            _ => return Err(invalid()),
        };
        let owner = bound
            .symbol(class)
            .and_then(|owner| self.store().get_merged_symbol(owner))
            .ok_or_else(invalid)?;
        let name =
            super::classes::authenticated_private_class_symbol_name(self.store(), owner, symbol)
                .ok_or_else(invalid)?;
        let owner_record = self.store().symbol(owner).ok_or_else(invalid)?;
        let owner_declarations_match = if owner_record.flags() == SymbolFlags::CLASS {
            owner_record.declarations() == Some(&[class])
        } else {
            let host = self.declared_type_host()?;
            super::classes::plan_nongeneric_class(self.store(), &host, owner)
                .is_ok_and(|plan| plan.declaration() == class && plan.symbol() == owner)
        };
        if !owner_declarations_match
            || owner_record.check_flags() != ts_binder::CheckFlags::NONE
            || owner_record.value_declaration() != Some(class)
            || !self.store().source_symbol_declarations_match(owner)
            || !self.store().source_symbol_declarations_match(symbol)
            || !self
                .store()
                .source_declaration_belongs_to_symbol(class, owner)
            || declarations
                .iter()
                .enumerate()
                .any(|(index, declaration)| declarations[..index].contains(declaration))
            || self.store().get_merged_symbol(symbol) != Some(symbol)
            || self.store().get_parent_of_symbol(symbol) != Some(owner)
            || record.members().is_some()
            || record.exports().is_some()
            || record.export_symbol().is_some()
            || record.check_flags().bits() & !ts_binder::CheckFlags::READONLY.bits() != 0
            || ![owner_record.members(), owner_record.exports()]
                .into_iter()
                .flatten()
                .any(|table| {
                    self.store()
                        .symbol_table(table)
                        .and_then(|table| table.get(record.name()))
                        == Some(symbol)
                })
        {
            return Err(invalid());
        }
        let mut expected_flags = SymbolFlags::NONE;
        for &declaration in declarations {
            let (arena, bound, member) = self.validated_artifact_node(declaration)?;
            let (name_id, flags, optional) = match &member.data {
                NodeData::PropertyDeclaration(property) => (
                    property.name,
                    if ts_binder::canonical_has_syntactic_modifier(
                        arena,
                        declaration.node,
                        SyntaxKind::AccessorKeyword,
                    ) {
                        SymbolFlags::ACCESSOR
                    } else {
                        SymbolFlags::PROPERTY
                    },
                    property.postfix_token,
                ),
                NodeData::MethodDeclaration(method) => {
                    (method.name, SymbolFlags::METHOD, method.postfix_token)
                }
                NodeData::GetAccessorDeclaration(accessor) => (
                    accessor.name,
                    SymbolFlags::GET_ACCESSOR,
                    accessor.postfix_token,
                ),
                NodeData::SetAccessorDeclaration(accessor) => (
                    accessor.name,
                    SymbolFlags::SET_ACCESSOR,
                    accessor.postfix_token,
                ),
                _ => return Err(invalid()),
            };
            expected_flags |= flags;
            if optional
                .and_then(|token| arena.get(token))
                .is_some_and(|token| token.kind == SyntaxKind::QuestionToken)
            {
                expected_flags |= SymbolFlags::OPTIONAL;
            }
            let name_node = NodeRef::new(declaration.arena, declaration.file, name_id);
            let (_, _, name_record) = self.validated_artifact_node(name_node)?;
            if member.parent != Some(class.node)
                || !declaration.is_for(class.arena, class.file)
                || source_members
                    .iter()
                    .filter(|member| **member == declaration.node)
                    .count()
                    != 1
                || bound
                    .symbol(declaration)
                    .and_then(|owner| self.store().get_merged_symbol(owner))
                    != Some(symbol)
                || !self
                    .store()
                    .source_declaration_belongs_to_symbol(declaration, symbol)
                || name_record.parent != Some(declaration.node)
                || !matches!(&name_record.data, NodeData::PrivateIdentifier(identifier) if identifier.text == name)
            {
                return Err(invalid());
            }
        }
        if record.flags() != expected_flags {
            return Err(invalid());
        }
        Ok(Some(name.to_owned()))
    }

    fn literal_artifact_symbol_name(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<Option<(String, bool)>, CanonicalArtifactQueryError> {
        let record = self
            .store()
            .symbol(symbol)
            .ok_or(CanonicalArtifactQueryError::ForeignSymbol(symbol))?;
        let Some(declaration) = record.value_declaration().or_else(|| {
            record
                .declarations()
                .and_then(|declarations| declarations.first().copied())
        }) else {
            return Ok(None);
        };
        let (arena, _, declaration_record) = self.validated_artifact_node(declaration)?;
        // Module names use the binder's canonical quotes, not property-name spelling.
        if matches!(declaration_record.data, NodeData::ModuleDeclaration(_)) {
            return Ok(None);
        }
        let Some(name_id) = declaration_name(&declaration_record.data) else {
            return Ok(None);
        };
        let Some(name_record) = arena.get(name_id) else {
            return Ok(None);
        };
        let (literal, computed) = match &name_record.data {
            NodeData::ComputedPropertyName(name) => {
                let Some(literal) = arena.get(name.expression) else {
                    return Ok(None);
                };
                if !matches!(
                    literal.data,
                    NodeData::StringLiteral(_)
                        | NodeData::NumericLiteral(_)
                        | NodeData::NoSubstitutionTemplateLiteral(_)
                ) {
                    return Ok(None);
                }
                (literal, true)
            }
            NodeData::StringLiteral(_) | NodeData::NumericLiteral(_) => (name_record, false),
            _ => return Ok(None),
        };
        let Some(spelling) = arena.source_text().and_then(|source| {
            source.get(literal.range.start.get() as usize..literal.range.end.get() as usize)
        }) else {
            return Ok(None);
        };
        let qualified_owner = record
            .parent()
            .and_then(|owner| self.store().symbol(owner))
            .is_some_and(|owner| {
                owner
                    .flags()
                    .intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE | SymbolFlags::ENUM)
            });
        Ok(Some((
            if computed || qualified_owner {
                format!("[{spelling}]")
            } else {
                spelling.to_owned()
            },
            computed || qualified_owner,
        )))
    }

    fn escaped_identifier_artifact_name(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<Option<String>, CanonicalArtifactQueryError> {
        let record = self
            .store()
            .symbol(symbol)
            .ok_or(CanonicalArtifactQueryError::ForeignSymbol(symbol))?;
        let Some(declaration) = record.value_declaration().or_else(|| {
            record
                .declarations()
                .and_then(|declarations| declarations.first().copied())
        }) else {
            return Ok(None);
        };
        let (arena, _, declaration_record) = self.validated_artifact_node(declaration)?;
        let Some(name) =
            declaration_name(&declaration_record.data).and_then(|name| arena.get(name))
        else {
            return Ok(None);
        };
        let NodeData::Identifier(identifier) = &name.data else {
            return Ok(None);
        };
        if record.name().as_utf8() != Some(identifier.text.as_str()) {
            return Ok(None);
        }
        let Some(spelling) = arena.source_text().and_then(|source| {
            source.get(name.range.start.get() as usize..name.range.end.get() as usize)
        }) else {
            return Ok(None);
        };
        Ok((spelling != identifier.text && spelling.contains("\\u")).then(|| spelling.to_owned()))
    }

    fn index_artifact_symbol_name(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<String, CanonicalArtifactQueryError> {
        let record = self
            .store()
            .symbol(symbol)
            .ok_or(CanonicalArtifactQueryError::ForeignSymbol(symbol))?;
        let mut owners = Vec::new();
        let mut owner = record.parent();
        while let Some(parent) = owner {
            let record = self
                .store()
                .symbol(parent)
                .ok_or(CanonicalArtifactQueryError::ForeignSymbol(parent))?;
            if !record.flags().intersects(
                SymbolFlags::CLASS
                    | SymbolFlags::INTERFACE
                    | SymbolFlags::ENUM
                    | SymbolFlags::MODULE,
            ) || record.name().is_internal()
            {
                break;
            }
            let name = self
                .escaped_identifier_artifact_name(parent)?
                .unwrap_or_else(|| record.name().escaped_display().to_string());
            if record.flags().intersects(SymbolFlags::MODULE) && name.starts_with('"') {
                break;
            }
            owners.push(name);
            owner = record.parent();
        }
        owners.reverse();
        let name = record.name().escaped_display();
        Ok(if owners.is_empty() {
            format!("[{name}]")
        } else {
            format!("{}[{name}]", owners.join("."))
        })
    }

    fn module_specifier_artifact_symbol(
        &self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        if !matches!(
            self.validated_artifact_node(node)?.2.data,
            NodeData::StringLiteral(_) | NodeData::NoSubstitutionTemplateLiteral(_)
        ) {
            return Ok(None);
        }
        let super::CanonicalModuleResolutionLookup::Resolved(resolved) =
            self.module_resolution(node)
        else {
            return Ok(None);
        };
        self.merged_artifact_symbol(node, resolved.target_symbol())
            .map(Some)
    }

    fn namespace_artifact_root(
        &self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        if self
            .store()
            .symbol_node_links(node)
            .is_some_and(|links| links.resolved_symbol.is_some())
        {
            return self.cached_artifact_symbol(node);
        }

        self.lexical_artifact_symbol(node, SymbolFlags::NAMESPACE | SymbolFlags::ALIAS)
    }

    /// A type-name query does not need its type, arguments, or a source-file check.
    #[allow(clippy::option_option)] // Distinguishes a non-type-name, no symbol, and a resolved symbol.
    fn type_name_artifact_symbol(
        &mut self,
        node: NodeRef,
    ) -> Result<Option<Option<SemanticSymbolId>>, CanonicalArtifactQueryError> {
        let Some(ArtifactTypeName {
            reference,
            full_name,
            parts,
        }) = self.type_name_artifact_path(node)?
        else {
            return Ok(None);
        };
        let name = parts.last().expect("a type name has an identifier").entity;
        for part in &parts {
            for cached_node in [part.entity, part.identifier] {
                if self
                    .store()
                    .symbol_node_links(cached_node)
                    .is_some_and(|links| links.resolved_symbol.is_some())
                    && self.cached_artifact_symbol(cached_node)?.is_none()
                    && (cached_node == part.entity || cached_node == node)
                {
                    return Ok(Some(None));
                }
            }
        }
        if name == full_name
            && self
                .store()
                .symbol_node_links(reference)
                .is_some_and(|links| links.resolved_symbol.is_some())
            && self.cached_artifact_symbol(reference)?.is_none()
        {
            return Ok(Some(None));
        }
        if parts
            .iter()
            .any(|part| part.text.as_utf8().is_none_or(str::is_empty))
        {
            return Ok(Some(None));
        }
        let mut symbols = Vec::with_capacity(parts.len());
        let mut symbol = None;
        for (index, part) in parts.iter().enumerate() {
            let meaning = if part.entity == full_name {
                SymbolFlags::TYPE
            } else {
                SymbolFlags::NAMESPACE
            };
            symbol = if index == 0 {
                self.lexical_artifact_symbol(part.entity, meaning | SymbolFlags::ALIAS)?
            } else if symbol.is_some() {
                // Resolve namespace aliases, then read the actual bindings without node caches.
                self.qualified_artifact_symbol(part.entity)?;
                self.name_resolver_host(self.options().name_resolution)
                    .map_err(DeclaredTypeError::from)?
                    .resolve_entity_name(part.entity, meaning | SymbolFlags::ALIAS)
                    .map_err(DeclaredTypeError::from)?
            } else {
                None
            };
            if let Some(candidate) = symbol {
                let record = self.store().symbol(candidate).ok_or(
                    CanonicalArtifactQueryError::InvalidSymbol {
                        node: part.entity,
                        symbol: candidate,
                    },
                )?;
                if !record.flags().intersects(meaning)
                    && !self.get_symbol_flags(candidate)?.flags.intersects(meaning)
                {
                    // Import-equals can retain namespace exports beside its value target.
                    let namespace = meaning == SymbolFlags::NAMESPACE
                        && self
                            .qualified_artifact_namespace(part.entity, part.entity, candidate)?
                            .is_some();
                    if !namespace {
                        symbol = None;
                    }
                }
            }
            symbols.push(symbol);
        }
        for (part, expected) in parts.iter().zip(symbols) {
            for cached_node in [part.entity, part.identifier] {
                self.validate_type_name_artifact_symbol_cache(cached_node, expected)?;
                if expected.is_none()
                    && let Some(links) = self.store().type_node_links(cached_node)
                    && (links.resolved_type.is_some() || links.outer_type_parameters.is_some())
                {
                    return Err(DeclaredTypeError::TypeNodeUnavailable(
                        super::type_nodes::TypeNodeUnavailable::InvalidTypeReference(reference),
                    )
                    .into());
                }
            }
        }
        if name == full_name {
            self.validate_type_name_artifact_symbol_cache(reference, symbol)?;
        }
        if symbol.is_some() {
            return Ok(Some(symbol));
        }
        if name == full_name
            && let Some(links) = self.store().type_node_links(reference)
            && (links.outer_type_parameters.is_some()
                || links.resolved_type.is_some_and(|type_| {
                    !self.cached_root_missing_type_name_is_exact(reference, type_)
                }))
        {
            return Err(DeclaredTypeError::TypeNodeUnavailable(
                super::type_nodes::TypeNodeUnavailable::InvalidTypeReference(reference),
            )
            .into());
        }
        let names = parts.into_iter().map(|part| part.text).collect::<Vec<_>>();
        self.artifact_unresolved_type_symbol(&names)
            .map(|symbol| Some(Some(symbol)))
            .map_err(|error| match error {
                super::store::UnresolvedTypeError::InvalidSymbol(symbol) => {
                    CanonicalArtifactQueryError::InvalidSymbol {
                        node: reference,
                        symbol,
                    }
                }
                _ => DeclaredTypeError::TypeNodeUnavailable(
                    super::type_nodes::TypeNodeUnavailable::InvalidTypeReference(reference),
                )
                .into(),
            })
    }

    fn validate_type_name_artifact_symbol_cache(
        &self,
        node: NodeRef,
        expected: Option<SemanticSymbolId>,
    ) -> Result<(), CanonicalArtifactQueryError> {
        if let Some(cached) = self.cached_artifact_symbol(node)?
            && Some(cached) != expected
            && !expected.is_some_and(|alias| {
                self.store().symbol(alias).is_some_and(|record| record.flags().contains(SymbolFlags::ALIAS))
                    && matches!(self.store().alias_symbol_links(alias).map(|links| links.alias_target),
                        Some(AliasTargetState::Resolved(target)) if self.store().get_merged_symbol(target) == Some(cached))
            })
        {
            return Err(CanonicalArtifactQueryError::InvalidSymbol { node, symbol: cached });
        }
        Ok(())
    }

    /// Root still uses its intrinsic error type for the admitted missing-reference cases.
    fn cached_root_missing_type_name_is_exact(&self, reference: NodeRef, type_: TypeId) -> bool {
        if self
            .store()
            .intrinsic_bootstrap()
            .is_none_or(|bootstrap| bootstrap.error_type != type_)
        {
            return false;
        }
        if self
            .store()
            .source_recovered_unresolved_type_reference_is_exact(reference, type_)
        {
            return true;
        }
        let Ok((arena, bound, record)) = self.validated_artifact_node(reference) else {
            return false;
        };
        let NodeData::TypeReferenceNode(data) = &record.data else {
            return false;
        };
        if data.type_arguments.is_some() {
            return false;
        }
        let valid_name = match arena.get(data.type_name).map(|node| &node.data) {
            Some(NodeData::Identifier(identifier)) => identifier.flow_node.is_none(),
            Some(NodeData::QualifiedName(qualified)) => [qualified.left, qualified.right].into_iter().all(|name| {
                matches!(arena.get(name).map(|node| &node.data), Some(NodeData::Identifier(identifier)) if identifier.flow_node.is_none())
            }),
            _ => false,
        };
        if !valid_name {
            return false;
        }
        let Some(declaration_id) = record.parent else {
            return false;
        };
        let declaration = NodeRef::new(reference.arena, reference.file, declaration_id);
        let Some(declaration_record) = arena.get(declaration_id) else {
            return false;
        };
        let NodeData::VariableDeclaration(variable) = &declaration_record.data else {
            return false;
        };
        if variable.type_ != Some(reference.node) {
            return false;
        }
        let Some(list_id) = declaration_record.parent else {
            return false;
        };
        let Some(list) = arena.get(list_id) else {
            return false;
        };
        let Some(statement_id) = list.parent else {
            return false;
        };
        let Some(statement) = arena.get(statement_id) else {
            return false;
        };
        declaration_record.kind == SyntaxKind::VariableDeclaration
            && list.kind == SyntaxKind::VariableDeclarationList
            && statement.kind == SyntaxKind::VariableStatement
            && statement.parent == Some(bound.source_file().node)
            && bound
                .source_facts()
                .is_some_and(|facts| !facts.is_javascript_file() && !facts.is_declaration_file())
            && bound
                .symbol(declaration)
                .and_then(|symbol| self.store().get_merged_symbol(symbol))
                .and_then(|symbol| self.store().symbol(symbol))
                .is_some_and(|symbol| symbol.flags().intersects(SymbolFlags::VARIABLE))
    }

    fn type_name_artifact_path(
        &self,
        node: NodeRef,
    ) -> Result<Option<ArtifactTypeName>, CanonicalArtifactQueryError> {
        let (arena, _, record) = self.validated_artifact_node(node)?;
        if !matches!(
            record.data,
            NodeData::Identifier(_) | NodeData::QualifiedName(_)
        ) {
            return Ok(None);
        }
        let mut name = node;
        let mut current = node;
        let mut remaining = arena.len();
        let reference = loop {
            if remaining == 0 {
                return Err(CanonicalArtifactQueryError::ForeignNode(current));
            }
            remaining -= 1;
            let (_, _, record) = self.validated_artifact_node(current)?;
            let Some(parent) = record.parent else {
                return Ok(None);
            };
            let parent = NodeRef::new(node.arena, node.file, parent);
            let (_, _, parent_record) = self.validated_artifact_node(parent)?;
            match &parent_record.data {
                NodeData::QualifiedName(qualified) => {
                    if qualified.left != current.node && qualified.right != current.node {
                        return Err(CanonicalArtifactQueryError::ForeignNode(current));
                    }
                    if current == node && qualified.right == node.node {
                        name = parent;
                    }
                    current = parent;
                }
                NodeData::TypeReferenceNode(reference)
                    if parent_record.kind == SyntaxKind::TypeReference =>
                {
                    if reference.type_name != current.node {
                        return Err(CanonicalArtifactQueryError::ForeignNode(current));
                    }
                    break parent;
                }
                NodeData::TypeReferenceNode(_) => {
                    return Err(CanonicalArtifactQueryError::ForeignNode(parent));
                }
                _ => return Ok(None),
            }
        };
        let full_name = current;
        let mut parts = Vec::new();
        loop {
            if parts.len() >= arena.len() {
                return Err(CanonicalArtifactQueryError::ForeignNode(current));
            }
            let (_, _, record) = self.validated_artifact_node(current)?;
            match &record.data {
                NodeData::Identifier(identifier) if record.kind == SyntaxKind::Identifier => {
                    parts.push(ArtifactTypeNamePart {
                        entity: current,
                        identifier: current,
                        text: EscapedName::source(&identifier.text),
                    });
                    break;
                }
                NodeData::QualifiedName(qualified) if record.kind == SyntaxKind::QualifiedName => {
                    let left = NodeRef::new(node.arena, node.file, qualified.left);
                    let right = NodeRef::new(node.arena, node.file, qualified.right);
                    let (_, _, right_record) = self.validated_artifact_node(right)?;
                    let NodeData::Identifier(identifier) = &right_record.data else {
                        return Err(CanonicalArtifactQueryError::ForeignNode(right));
                    };
                    if right_record.kind != SyntaxKind::Identifier
                        || right_record.parent != Some(current.node)
                        || self.validated_artifact_node(left)?.2.parent != Some(current.node)
                    {
                        return Err(CanonicalArtifactQueryError::ForeignNode(current));
                    }
                    parts.push(ArtifactTypeNamePart {
                        entity: current,
                        identifier: right,
                        text: EscapedName::source(&identifier.text),
                    });
                    current = left;
                }
                _ => return Err(CanonicalArtifactQueryError::ForeignNode(current)),
            }
        }
        parts.reverse();
        let end = parts
            .iter()
            .position(|part| part.entity == name)
            .ok_or(CanonicalArtifactQueryError::ForeignNode(node))?;
        parts.truncate(end + 1);
        Ok(Some(ArtifactTypeName {
            reference,
            full_name,
            parts,
        }))
    }

    fn uncached_artifact_reference_symbol(
        &self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        if self
            .store()
            .symbol_node_links(node)
            .is_some_and(|links| links.resolved_symbol.is_some())
        {
            return Ok(None);
        }

        let (arena, _, record) = self.validated_artifact_node(node)?;
        let Some(parent_id) = record.parent else {
            return Ok(None);
        };
        let Some(parent) = arena.get(parent_id) else {
            return Err(CanonicalArtifactQueryError::ForeignNode(NodeRef::new(
                node.arena, node.file, parent_id,
            )));
        };
        if matches!(
            &parent.data,
            NodeData::ImportEqualsDeclaration(import) if import.module_reference == node.node
        ) {
            return self.lexical_artifact_symbol(node, SymbolFlags::NAMESPACE | SymbolFlags::ALIAS);
        }

        if matches!(
            &parent.data,
            NodeData::ExportAssignment(export)
                if export.is_export_equals && export.expression == node.node
        ) {
            let Some(symbol) = self.lexical_artifact_symbol(
                node,
                SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE | SymbolFlags::ALIAS,
            )?
            else {
                return Ok(None);
            };
            // Read an existing value identity without producing a cold declaration type.
            let Some(type_) = self
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type)
            else {
                return Ok(None);
            };
            self.validate_artifact_type(node, type_)?;
            return Ok(Some(symbol));
        }

        let mut current = node.node;
        let mut ancestor_id = parent_id;
        let mut ancestor = parent;
        loop {
            if let NodeData::EnumMember(member) = &ancestor.data {
                return if member.initializer == Some(current) {
                    self.lexical_artifact_symbol(
                        node,
                        SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE | SymbolFlags::ALIAS,
                    )
                } else {
                    Ok(None)
                };
            }
            let Some(parent_id) = ancestor.parent else {
                return Ok(None);
            };
            current = ancestor_id;
            ancestor_id = parent_id;
            ancestor = arena.get(parent_id).ok_or_else(|| {
                CanonicalArtifactQueryError::ForeignNode(NodeRef::new(
                    node.arena, node.file, parent_id,
                ))
            })?;
        }
    }

    fn export_equals_declared_artifact_type(
        &self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let (_, _, record) = self.validated_artifact_node(node)?;
        let NodeData::Identifier(identifier) = &record.data else {
            return Ok(None);
        };
        let Some(parent) = record.parent else {
            return Ok(None);
        };
        let parent = NodeRef::new(node.arena, node.file, parent);
        if !matches!(
            &self.validated_artifact_node(parent)?.2.data,
            NodeData::ExportAssignment(export)
                if export.is_export_equals && export.expression == node.node
        ) {
            return Ok(None);
        }
        let Some(symbol) = self.lexical_artifact_symbol(
            node,
            SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE | SymbolFlags::ALIAS,
        )?
        else {
            return Ok(None);
        };
        let owner = self
            .store()
            .symbol(symbol)
            .ok_or(CanonicalArtifactQueryError::InvalidSymbol { node, symbol })?;
        let source_flags = self
            .store()
            .source_symbol_flags(symbol)
            .unwrap_or(SymbolFlags::NONE);
        if !(owner.flags() | source_flags).intersects(SymbolFlags::CLASS | SymbolFlags::ENUM) {
            return Ok(None);
        }
        if owner.name() != EscapedNameRef::source(&identifier.text)
            || !self.store().source_symbol_declarations_match(symbol)
                && super::classes::global_class_namespace_declaration(self.store(), symbol, owner)
                    .is_none()
            || !self.store().source_merged_symbol_declarations_match(symbol)
            || self
                .cached_artifact_symbol(node)?
                .is_some_and(|cached| cached != symbol)
        {
            return Err(CanonicalArtifactQueryError::InvalidSymbol { node, symbol });
        }
        if self
            .store()
            .value_symbol_links(symbol)
            .and_then(|links| links.resolved_type)
            .is_none()
        {
            let source = self
                .source_file(node.file)
                .ok_or(CanonicalArtifactQueryError::MissingFile(node.file))?;
            let untouched = self
                .store()
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .is_none()
                && self.cached_artifact_symbol(node)?.is_none()
                && self.cached_artifact_type(node)?.is_none()
                && !self
                    .store()
                    .source_file_links(source)
                    .is_some_and(|links| links.type_checked);
            // A cold declaration has no value to query. A checked class cannot fall through.
            return if untouched {
                Ok(None)
            } else {
                Err(CanonicalArtifactQueryError::MissingType {
                    node,
                    kind: record.kind,
                })
            };
        }
        let type_ = self
            .store()
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            .ok_or(CanonicalArtifactQueryError::MissingType {
                node,
                kind: record.kind,
            })?;
        if source_flags.intersects(SymbolFlags::CLASS) {
            if super::declared::cached_class_type(self.store(), symbol)? != Some(type_)
                || super::classes::validate_class_heritage_members(self.store(), type_)
                    != super::classes::ClassHeritageMembersValidation::Valid
            {
                return Err(CanonicalArtifactQueryError::InvalidType { node, type_ });
            }
        } else {
            self.preflight_enum_type(symbol)?;
        }
        if let Some(cached) = self.cached_artifact_type(node)?
            && cached != type_
        {
            return Err(CanonicalArtifactQueryError::InvalidType {
                node,
                type_: cached,
            });
        }
        self.validate_artifact_type(node, type_).map(Some)
    }

    fn lexical_artifact_symbol(
        &self,
        node: NodeRef,
        meaning: SymbolFlags,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        let (arena, bound, record) = self.validated_artifact_node(node)?;
        let NodeData::Identifier(identifier) = &record.data else {
            return Ok(None);
        };
        let mut host = self
            .name_resolver_host(self.options().name_resolution)
            .map_err(DeclaredTypeError::from)?;
        if matches!(
            record.parent.and_then(|parent| arena.get(parent)).map(|parent| &parent.data),
            Some(NodeData::ExportAssignment(export))
                if export.is_export_equals && export.expression == node.node
        ) {
            host = host.with_class_enum_source_validation();
        }
        let symbol =
            CanonicalNameResolver::new(arena, bound, self.store().symbol_store(), &mut host)
                .map_err(DeclaredTypeError::from)?
                .resolve(
                    Some(CanonicalResolutionLocation::Bound(node)),
                    &identifier.text,
                    meaning,
                    None,
                    true,
                    false,
                )
                .map_err(DeclaredTypeError::from)?;
        symbol
            .map(|symbol| self.merged_artifact_symbol(node, symbol))
            .transpose()
    }

    fn qualified_artifact_symbol(
        &mut self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        if self
            .store()
            .symbol_node_links(node)
            .is_some_and(|links| links.resolved_symbol.is_some())
        {
            return self.cached_artifact_symbol(node);
        }

        let (left, name) = {
            let (arena, _, record) = self.validated_artifact_node(node)?;
            let NodeData::QualifiedName(qualified) = &record.data else {
                return Ok(None);
            };
            let right = NodeRef::new(node.arena, node.file, qualified.right);
            let (_, _, right_record) = self.validated_artifact_node(right)?;
            let NodeData::Identifier(identifier) = &right_record.data else {
                return Ok(None);
            };
            if right_record.parent != Some(node.node)
                || arena
                    .get(qualified.left)
                    .is_none_or(|left| left.parent != Some(node.node))
            {
                return Err(CanonicalArtifactQueryError::ForeignNode(node));
            }
            (
                NodeRef::new(node.arena, node.file, qualified.left),
                identifier.text.clone(),
            )
        };

        let owner = match &self.validated_artifact_node(left)?.2.data {
            NodeData::Identifier(_) => self.namespace_artifact_root(left)?,
            NodeData::QualifiedName(_) => self.qualified_artifact_symbol(left)?,
            _ => None,
        };
        let Some(owner) = owner else {
            return Ok(None);
        };
        let Some(owner) = self.qualified_artifact_namespace(node, left, owner)? else {
            return Ok(None);
        };

        let record =
            self.store()
                .symbol(owner)
                .ok_or(CanonicalArtifactQueryError::InvalidSymbol {
                    node,
                    symbol: owner,
                })?;
        if !record.flags().intersects(SymbolFlags::NAMESPACE) {
            return Ok(None);
        }
        let Some(exports) = self
            .store()
            .module_symbol_links(owner)
            .and_then(|links| links.resolved_exports)
            .or_else(|| record.exports())
        else {
            return Ok(None);
        };
        let exports = self.store().symbol_table(exports).ok_or(
            CanonicalArtifactQueryError::InvalidSymbol {
                node,
                symbol: owner,
            },
        )?;
        let Some(symbol) = exports.get_source(&name) else {
            return Ok(None);
        };
        let symbol = self.merged_artifact_symbol(node, symbol)?;
        if self
            .store()
            .intrinsic_bootstrap()
            .is_some_and(|bootstrap| symbol == bootstrap.unknown_symbol)
        {
            return Ok(None);
        }
        Ok(Some(symbol))
    }

    fn qualified_artifact_namespace(
        &mut self,
        node: NodeRef,
        left: NodeRef,
        mut owner: SemanticSymbolId,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        let flags = self
            .store()
            .symbol(owner)
            .map(ts_binder::semantic::Symbol::flags)
            .ok_or(CanonicalArtifactQueryError::InvalidSymbol {
                node,
                symbol: owner,
            })?;
        if flags.contains(SymbolFlags::ALIAS) {
            owner = match self.resolve_alias(owner)?.target {
                AliasTargetState::Resolved(target) => self.merged_artifact_symbol(node, target)?,
                AliasTargetState::Unknown | AliasTargetState::Unresolved => return Ok(None),
            };
        }

        if self
            .store()
            .symbol(owner)
            .is_some_and(|record| !record.flags().intersects(SymbolFlags::NAMESPACE))
        {
            let mut resolver = self
                .name_resolver_host(self.options().name_resolution)
                .map_err(DeclaredTypeError::from)?;
            let Some(namespace) = resolver
                .resolve_entity_name(left, SymbolFlags::NAMESPACE)
                .map_err(DeclaredTypeError::from)?
            else {
                return Ok(None);
            };
            if self.store().get_parent_of_symbol(owner) != Some(namespace)
                || self
                    .store()
                    .symbol(namespace)
                    .and_then(ts_binder::semantic::Symbol::exports)
                    .and_then(|exports| self.store().symbol_table(exports))
                    .and_then(|exports| exports.get(InternalSymbolName::ExportEquals.as_ref()))
                    != Some(owner)
            {
                return Err(CanonicalArtifactQueryError::InvalidSymbol {
                    node,
                    symbol: owner,
                });
            }
            owner = self.merged_artifact_symbol(node, namespace)?;
        }
        Ok(Some(owner))
    }

    /// Demands an empty JavaScript class through the existing class member query.
    /// The written qualified base selects the class, not its JSDoc annotation.
    #[allow(clippy::too_many_lines)] // Keep source role selection and both exact class sides in one demand path.
    fn javascript_class_heritage_artifact_type(
        &mut self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let (whole, owner, value_leaf) = {
            let (arena, bound, record) = self.validated_artifact_node(node)?;
            if !bound.source_facts().is_some_and(|facts| {
                facts.is_javascript_file()
                    && !facts.is_declaration_file()
                    && !facts.is_external_or_common_js_module()
            }) {
                return Ok(None);
            }
            let whole = if matches!(
                record.data,
                NodeData::QualifiedName(_) | NodeData::PropertyAccessExpression(_)
            ) {
                node
            } else if record.kind == SyntaxKind::Identifier
                && let Some(parent) = record.parent
                && arena.get(parent).is_some_and(|record| match &record.data {
                    NodeData::QualifiedName(name) => name.right == node.node,
                    NodeData::PropertyAccessExpression(access) => access.name == node.node,
                    _ => false,
                })
            {
                NodeRef::new(node.arena, node.file, parent)
            } else {
                return Ok(None);
            };
            let Some(wrapper) = arena
                .get(whole.node)
                .and_then(|record| record.parent)
                .and_then(|parent| arena.get(parent))
            else {
                return Ok(None);
            };
            let NodeData::ExpressionWithTypeArguments(expression) = &wrapper.data else {
                return Ok(None);
            };
            if expression.expression != whole.node || expression.type_arguments.is_some() {
                return Ok(None);
            }
            let Some(clause) = wrapper.parent.and_then(|parent| arena.get(parent)) else {
                return Ok(None);
            };
            let NodeData::HeritageClause(heritage) = &clause.data else {
                return Ok(None);
            };
            let Some(owner) = clause.parent else {
                return Ok(None);
            };
            let Some(NodeData::ClassDeclaration(class)) =
                arena.get(owner).map(|record| &record.data)
            else {
                return Ok(None);
            };
            if heritage.token != SyntaxKind::ExtendsKeyword
                || class.type_parameters.is_some()
                || class.modifiers.is_some()
                || !class.members.nodes.is_empty()
            {
                return Ok(None);
            }
            let declaration = NodeRef::new(node.arena, node.file, owner);
            let symbol = bound
                .symbol(declaration)
                .and_then(|symbol| self.store().get_merged_symbol(symbol))
                .ok_or(CanonicalArtifactQueryError::ForeignNode(declaration))?;
            (whole, symbol, node != whole)
        };
        let members = self
            .get_nongeneric_class_members(owner)
            .map_err(|error| CanonicalArtifactQueryError::Class { node, error })?;
        let instance = members.shells().instance_type();
        let Some((base, symbol)) = self.class_heritage_artifact_target(whole)? else {
            return Err(CanonicalArtifactQueryError::InvalidType {
                node,
                type_: instance,
            });
        };
        let provenance = self
            .store()
            .direct_class_heritage_provenance(instance)
            .ok_or(CanonicalArtifactQueryError::InvalidType {
                node,
                type_: instance,
            })?;
        if provenance.owner_symbol != owner
            || provenance.base_symbol != symbol
            || provenance.base_instance_type != base
        {
            return Err(CanonicalArtifactQueryError::InvalidType {
                node,
                type_: instance,
            });
        }
        self.validate_artifact_type(
            node,
            if value_leaf {
                provenance.base_value_type
            } else {
                base
            },
        )
        .map(Some)
    }

    /// A class base name denotes its instance here, even when checking the
    /// extends expression retained the constructor value at that same node.
    fn class_heritage_artifact_target(
        &self,
        node: NodeRef,
    ) -> Result<Option<(TypeId, SemanticSymbolId)>, CanonicalArtifactQueryError> {
        let (arena, bound, record) = self.validated_artifact_node(node)?;
        let Some(reference) = record.parent.and_then(|parent| arena.get(parent)) else {
            return Ok(None);
        };
        let NodeData::ExpressionWithTypeArguments(expression) = &reference.data else {
            return Ok(None);
        };
        if expression.expression != node.node || expression.type_arguments.is_some() {
            return Ok(None);
        }
        let Some(clause) = reference.parent.and_then(|parent| arena.get(parent)) else {
            return Ok(None);
        };
        let NodeData::HeritageClause(heritage) = &clause.data else {
            return Ok(None);
        };
        let Some(owner_id) = clause.parent else {
            return Ok(None);
        };
        let Some(NodeData::ClassDeclaration(class)) = arena.get(owner_id).map(|node| &node.data)
        else {
            return Ok(None);
        };
        if heritage.token != SyntaxKind::ExtendsKeyword || class.type_parameters.is_some() {
            return Ok(None);
        }
        let Some((base, symbol)) = self.heritage_artifact_target(node)? else {
            return Ok(None);
        };
        let owner = NodeRef::new(node.arena, node.file, owner_id);
        let owner_symbol = bound
            .symbol(owner)
            .and_then(|symbol| self.store().get_merged_symbol(symbol))
            .ok_or(CanonicalArtifactQueryError::ForeignNode(owner))?;
        let owner_type = super::declared::cached_class_type(self.store(), owner_symbol)?.ok_or(
            CanonicalArtifactQueryError::MissingType {
                node: owner,
                kind: SyntaxKind::ClassDeclaration,
            },
        )?;
        if super::classes::validate_class_heritage_members(self.store(), owner_type)
            != super::classes::ClassHeritageMembersValidation::Valid
        {
            return Err(CanonicalArtifactQueryError::InvalidType {
                node,
                type_: owner_type,
            });
        }
        let provenance = self
            .store()
            .direct_class_heritage_provenance(owner_type)
            .ok_or(CanonicalArtifactQueryError::InvalidType {
                node,
                type_: owner_type,
            })?;
        if provenance.owner_symbol != owner_symbol
            || provenance.base_instance_type != base
            || provenance.base_symbol != symbol
        {
            return Err(CanonicalArtifactQueryError::InvalidType { node, type_: base });
        }
        // The source-body producer retains the value expression. The older
        // declaration producer retains the base type or leaves the name cold.
        let expected_cache = if self.store().source_class_provenance(owner_type).is_some() {
            provenance.base_value_type
        } else {
            base
        };
        if let Some(links) = self.store().type_node_links(node)
            && *links != TypeNodeLinks::default()
            && *links
                != (TypeNodeLinks {
                    resolved_type: Some(expected_cache),
                    ..TypeNodeLinks::default()
                })
        {
            return Err(CanonicalArtifactQueryError::InvalidType {
                node,
                type_: links.resolved_type.unwrap_or(expected_cache),
            });
        }
        if let Some(cached) = self
            .store()
            .symbol_node_links(node)
            .and_then(|links| links.resolved_symbol)
            && self.merged_artifact_symbol(node, cached)? != symbol
        {
            return Err(CanonicalArtifactQueryError::InvalidSymbol {
                node,
                symbol: cached,
            });
        }
        self.validate_artifact_type(node, base)?;
        Ok(Some((base, symbol)))
    }

    /// Reads the existing class receiver proof. This does not check a body again
    /// or replace its constructor or maps-this instance expression cache.
    fn class_super_artifact_target(
        &self,
        node: NodeRef,
    ) -> Result<Option<(TypeId, SemanticSymbolId)>, CanonicalArtifactQueryError> {
        let (arena, _, record) = self.validated_artifact_node(node)?;
        if record.kind != SyntaxKind::SuperKeyword {
            return Ok(None);
        }
        let Some(type_) = self.cached_artifact_type(node)? else {
            return Ok(None);
        };
        let invalid = || CanonicalArtifactQueryError::InvalidType { node, type_ };
        let host = self.declared_type_host()?;
        let access = super::source_properties::plan_class_access_context(self.store(), &host, node)
            .map_err(|_| invalid())?
            .ok_or_else(invalid)?;
        let instance = super::declared::cached_class_type(self.store(), access.class_symbol())?
            .ok_or_else(invalid)?;
        if super::classes::validate_class_heritage_members(self.store(), instance)
            != super::classes::ClassHeritageMembersValidation::Valid
        {
            return Err(invalid());
        }
        let base = self
            .store()
            .direct_class_heritage_provenance(instance)
            .ok_or_else(invalid)?;
        let parent = record
            .parent
            .and_then(|parent| arena.get(parent))
            .ok_or_else(invalid)?;
        let member = access.body_declaration();
        let static_member = self.validated_artifact_node(member)?.2.kind
            == SyntaxKind::ClassStaticBlockDeclaration
            || ts_binder::canonical_has_syntactic_modifier(
                arena,
                member.node,
                SyntaxKind::StaticKeyword,
            );
        let expected = if matches!(parent.data, NodeData::CallExpression(_)) || static_member {
            base.base_value_type
        } else {
            let view = self
                .store()
                .class_instance_super_view_for_instance(instance)
                .ok_or_else(invalid)?;
            super::classes::validate_class_instance_super_view(
                self.store(),
                &host,
                access.class_symbol(),
                None,
                view.receiver_type(),
            )
            .map_err(|_| invalid())?;
            view.receiver_type()
        };
        if type_ != expected
            || self.store().type_node_links(node)
                != Some(&TypeNodeLinks {
                    resolved_type: Some(expected),
                    ..TypeNodeLinks::default()
                })
            || self
                .store()
                .type_payload(type_)
                .and_then(TypeRecord::symbol)
                != Some(base.base_symbol)
        {
            return Err(invalid());
        }
        let symbol = self.merged_artifact_symbol(node, base.base_symbol)?;
        if let Some(cached) = self
            .store()
            .symbol_node_links(node)
            .and_then(|links| links.resolved_symbol)
            && self.merged_artifact_symbol(node, cached)? != symbol
        {
            return Err(CanonicalArtifactQueryError::InvalidSymbol {
                node,
                symbol: cached,
            });
        }
        Ok(Some((type_, symbol)))
    }

    fn heritage_artifact_target(
        &self,
        node: NodeRef,
    ) -> Result<Option<(TypeId, SemanticSymbolId)>, CanonicalArtifactQueryError> {
        let (arena, bound, record) = self.validated_artifact_node(node)?;
        let Some(reference_id) = record.parent else {
            return Ok(None);
        };
        let reference = NodeRef::new(node.arena, node.file, reference_id);
        let Some(reference_record) = arena.get(reference_id) else {
            return Err(CanonicalArtifactQueryError::ForeignNode(reference));
        };
        let NodeData::ExpressionWithTypeArguments(expression) = &reference_record.data else {
            return Ok(None);
        };
        if expression.expression != node.node {
            return Ok(None);
        }

        let Some(clause_id) = reference_record.parent else {
            return Ok(None);
        };
        let clause = NodeRef::new(node.arena, node.file, clause_id);
        let Some(clause_record) = arena.get(clause_id) else {
            return Err(CanonicalArtifactQueryError::ForeignNode(clause));
        };
        let NodeData::HeritageClause(heritage) = &clause_record.data else {
            return Ok(None);
        };
        let Some(owner_id) = clause_record.parent else {
            return Ok(None);
        };
        let owner = NodeRef::new(node.arena, node.file, owner_id);
        let Some(owner_record) = arena.get(owner_id) else {
            return Err(CanonicalArtifactQueryError::ForeignNode(owner));
        };
        if !matches!(
            owner_record.data,
            NodeData::ClassDeclaration(_) | NodeData::InterfaceDeclaration(_)
        ) {
            return Ok(None);
        }
        if !bound.contains(reference) || !bound.contains(clause) || !bound.contains(owner) {
            return Err(CanonicalArtifactQueryError::ForeignNode(node));
        }

        let Some(owner_symbol) = bound.symbol(owner) else {
            return Ok(None);
        };
        let owner_symbol = self.merged_artifact_symbol(node, owner_symbol)?;
        let Some(owner_type) = self
            .store()
            .declared_type_links(owner_symbol)
            .and_then(|links| links.declared_type)
        else {
            return Ok(None);
        };
        let Some(TypeData::Interface(interface)) =
            self.store().type_payload(owner_type).map(TypeRecord::data)
        else {
            return Err(CanonicalArtifactQueryError::InvalidType {
                node,
                type_: owner_type,
            });
        };
        let Some(index) = heritage
            .types
            .nodes
            .iter()
            .position(|base| *base == reference_id)
        else {
            return Ok(None);
        };
        if matches!(owner_record.data, NodeData::InterfaceDeclaration(_))
            && interface.resolved_base_types.is_some()
            && let Some(target) = self.merged_interface_heritage_artifact_target(
                node,
                reference,
                owner_symbol,
                owner_type,
            )?
        {
            return Ok(Some(target));
        }
        let Some(base) = interface
            .resolved_base_types
            .as_deref()
            .and_then(|types| types.get(index))
            .copied()
        else {
            return Ok(None);
        };
        let Some(symbol) = self.store().type_payload(base).and_then(TypeRecord::symbol) else {
            return Err(CanonicalArtifactQueryError::InvalidType { node, type_: base });
        };
        let symbol = self.merged_artifact_symbol(node, symbol)?;
        Ok(Some((base, symbol)))
    }

    fn merged_interface_heritage_artifact_target(
        &self,
        node: NodeRef,
        reference: NodeRef,
        owner: SemanticSymbolId,
        owner_type: TypeId,
    ) -> Result<Option<(TypeId, SemanticSymbolId)>, CanonicalArtifactQueryError> {
        let store = self.store();
        if !super::object_members::authenticated_nongeneric_global_interface_owner(store, owner)
            || store
                .symbol(owner)
                .and_then(ts_binder::semantic::Symbol::declarations)
                .is_none_or(|declarations| {
                    declarations
                        .iter()
                        .filter(|declaration| {
                            store.source_node_kind(**declaration)
                                == Some(SyntaxKind::InterfaceDeclaration)
                        })
                        .nth(1)
                        .is_none()
                })
        {
            return Ok(None);
        }
        let invalid = || CanonicalArtifactQueryError::InvalidType {
            node,
            type_: owner_type,
        };
        let host = self.declared_type_host()?;
        let plan =
            super::object_members::plan_interface(store, &host, owner).map_err(|_| invalid())?;
        let heritage = plan.heritage.as_ref().ok_or_else(invalid)?;
        if heritage.bases.iter().any(|base| {
            base.kind != super::interface_heritage::DirectInterfaceBaseKind::Interface
                || !base.type_arguments.is_empty()
                || !base.defaults.is_empty()
                || !super::object_members::authenticated_nongeneric_global_interface_owner(
                    store,
                    base.symbol,
                )
        }) {
            return Ok(None);
        }
        if !super::structured_members::validate_planned_interface_heritage_members_with_array_targets(
            store,
            &plan,
            owner_type,
            Some(super::array_types::CanonicalArrayTargets::from_global_types(
                self.global_types(),
            )),
        ) {
            return Err(invalid());
        }
        // Each repeated contribution has its own source node and retained base slot.
        let index = heritage
            .bases
            .iter()
            .position(|base| base.node == reference && base.expression == node)
            .ok_or_else(invalid)?;
        let &(symbol, type_) = store
            .direct_interface_heritage_provenance(owner_type)
            .and_then(|provenance| provenance.bases.get(index))
            .ok_or_else(invalid)?;
        let symbol = self.merged_artifact_symbol(node, symbol)?;
        Ok(Some((type_, symbol)))
    }

    fn type_of_artifact_symbol(
        &mut self,
        node: NodeRef,
        symbol: SemanticSymbolId,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let (flags, export_symbol) = self
            .store()
            .symbol(symbol)
            .map(|record| (record.flags(), record.export_symbol()))
            .ok_or(CanonicalArtifactQueryError::InvalidSymbol { node, symbol })?;

        if flags.intersects(SymbolFlags::PROPERTY | SymbolFlags::METHOD)
            && self
                .store()
                .symbol(symbol)
                .and_then(ts_binder::semantic::Symbol::parent)
                .and_then(|owner| self.store().symbol(owner))
                .is_some_and(|owner| owner.flags().contains(SymbolFlags::CLASS))
        {
            match self.get_class_query_member_type(symbol) {
                Ok(type_)
                    if !flags.contains(SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL)
                        || !self.options().intrinsic.strict_null_checks =>
                {
                    return self.validate_artifact_type(node, type_).map(Some);
                }
                Ok(_) | Err(super::ClassError::Unsupported(_)) => {}
                Err(super::ClassError::DeclaredType(error)) => return Err(error.into()),
                Err(error) => return Err(CanonicalArtifactQueryError::Class { node, error }),
            }
        }

        if super::source_namespaces::has_pure_module_flags(flags)
            && let Some(declaration) = self
                .store()
                .symbol(symbol)
                .and_then(|record| record.declarations())
                .and_then(|declarations| declarations.first())
                .copied()
            && matches!(&self.validated_artifact_node(declaration)?.2.data,
                NodeData::ModuleDeclaration(module) if module.body.is_some())
        {
            let type_ = self.get_type_of_module_value(symbol)?;
            return self.validate_artifact_type(node, type_).map(Some);
        }

        if let Some(type_) = self
            .store()
            .value_symbol_links(symbol)
            .and_then(|links| links.resolved_type)
        {
            return self
                .optional_property_artifact_type(node, flags, type_)
                .map(Some);
        }

        if super::source_namespaces::has_pure_module_flags(flags)
            && self
                .store()
                .source_file_namespace_wrapper_for_module(symbol)
                .is_none()
            && let Some(source) = self
                .store()
                .symbol(symbol)
                .and_then(ts_binder::semantic::Symbol::value_declaration)
                .filter(|source| {
                    self.store().source_node_kind(*source) == Some(SyntaxKind::SourceFile)
                })
            && self
                .validated_artifact_node(source)?
                .1
                .source_facts()
                .is_some_and(|facts| {
                    facts.is_external_module()
                        && !facts.is_javascript_file()
                        && !facts.is_common_js_module()
                })
        {
            let type_ = self.get_type_of_module_value(symbol)?;
            return self.validate_artifact_type(node, type_).map(Some);
        }

        if flags.intersects(SymbolFlags::PROPERTY)
            && let Some(type_) = self.object_literal_property_type(node, symbol)?
        {
            return Ok(Some(type_));
        }

        if let Some(type_) = self.declaration_file_annotation_type(node, symbol)? {
            return self
                .optional_property_artifact_type(node, flags, type_)
                .map(Some);
        }

        if flags.intersects(SymbolFlags::EXPORT_VALUE) {
            let target =
                export_symbol.ok_or(CanonicalArtifactQueryError::InvalidSymbol { node, symbol })?;
            return self.type_of_artifact_symbol(node, target);
        }

        if flags.intersects(SymbolFlags::ALIAS) {
            let resolution = self.resolve_alias(symbol)?;
            return match resolution.target {
                AliasTargetState::Resolved(target) => self.type_of_artifact_symbol(node, target),
                AliasTargetState::Unknown | AliasTargetState::Unresolved => Ok(None),
            };
        }

        if flags.contains(SymbolFlags::CLASS) && flags.intersects(SymbolFlags::MODULE) {
            let members =
                self.get_nongeneric_class_members(symbol)
                    .map_err(|error| match error {
                        super::ClassError::DeclaredType(error) => error.into(),
                        error => CanonicalArtifactQueryError::Class { node, error },
                    })?;
            return self
                .validate_artifact_type(node, members.shells().value_type())
                .map(Some);
        }

        if flags.intersects(SymbolFlags::TYPE) {
            return self
                .get_declared_type_of_symbol(symbol)
                .map_err(CanonicalArtifactQueryError::from)
                .and_then(|type_| self.validate_artifact_type(node, type_))
                .map(Some);
        }

        Ok(None)
    }

    // Apply declaration-name optionality without changing the stored annotation or value type.
    fn optional_property_artifact_type(
        &mut self,
        node: NodeRef,
        flags: SymbolFlags,
        type_: TypeId,
    ) -> Result<TypeId, CanonicalArtifactQueryError> {
        let type_ = self.validate_artifact_type(node, type_)?;
        if !flags.contains(SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL)
            || !self.options().intrinsic.strict_null_checks
        {
            return Ok(type_);
        }

        let sentinel = self
            .store()
            .intrinsic_bootstrap()
            .ok_or(CanonicalArtifactQueryError::InvalidType { node, type_ })?
            .undefined_or_missing_type;
        if type_ == sentinel
            || matches!(
                self.store().type_payload(type_).map(TypeRecord::data),
                Some(TypeData::Union(union)) if union.union.types.contains(&sentinel)
            )
        {
            return Ok(type_);
        }

        let read_type = self.artifact_union_type(&[type_, sentinel])?;
        self.validate_artifact_type(node, read_type)
    }

    fn type_node_artifact_type(&mut self, node: NodeRef) -> Result<TypeId, DeclaredTypeError> {
        if self.store().source_node_kind(node) == Some(SyntaxKind::TypeReference) {
            self.artifact_type_reference_identity(node)
        } else {
            self.get_type_from_type_node(node)
        }
    }

    fn declaration_method_artifact_type(
        &mut self,
        node: NodeRef,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let Some(symbol) = self.declaration_method_artifact_symbol(node)? else {
            return Ok(None);
        };
        let selected = self
            .store()
            .late_bound_links(symbol)
            .and_then(|links| links.late_symbol)
            .unwrap_or(symbol);
        if let Some(links) = self.store().type_node_links(node)
            && links != &TypeNodeLinks::default()
        {
            let type_ = links
                .resolved_type
                .ok_or(CanonicalArtifactQueryError::InvalidSymbol { node, symbol })?;
            if links.outer_type_parameters.is_some()
                || self
                    .store()
                    .value_symbol_links(selected)
                    .and_then(|value| value.resolved_type)
                    != Some(type_)
            {
                return Err(CanonicalArtifactQueryError::InvalidType { node, type_ });
            }
        }
        let type_ = self.artifact_interface_method_type(symbol)?;
        self.validate_artifact_type(node, type_).map(Some)
    }

    fn declaration_method_artifact_symbol(
        &self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        let (declaration, symbol) = {
            let (arena, bound, record) = self.validated_artifact_node(node)?;
            if !bound
                .source_facts()
                .is_some_and(|facts| facts.is_declaration_file() || facts.is_default_library())
            {
                return Ok(None);
            }
            let declaration = if record.kind == SyntaxKind::MethodSignature {
                node
            } else {
                let Some(parent) = record.parent else {
                    return Ok(None);
                };
                let Some(parent_record) = arena.get(parent) else {
                    return Err(CanonicalArtifactQueryError::ForeignNode(node));
                };
                if !matches!(&parent_record.data,
                    NodeData::MethodSignatureDeclaration(method) if method.name == node.node)
                {
                    return Ok(None);
                }
                NodeRef::new(node.arena, node.file, parent)
            };
            let symbol =
                bound
                    .symbol(declaration)
                    .ok_or(CanonicalArtifactQueryError::UnsupportedNode {
                        node: declaration,
                        kind: SyntaxKind::MethodSignature,
                    })?;
            (declaration, symbol)
        };
        let symbol = self.declaration_method_artifact_selection(node, declaration, symbol)?;
        Ok(Some(symbol))
    }

    fn declaration_method_artifact_selection(
        &self,
        node: NodeRef,
        declaration: NodeRef,
        raw: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, CanonicalArtifactQueryError> {
        let symbol = self.merged_artifact_symbol(node, raw)?;
        let invalid = || CanonicalArtifactQueryError::InvalidSymbol { node, symbol };
        if self.store().get_merged_symbol(symbol) != Some(symbol) {
            return Err(invalid());
        }
        let (_, bound, record) = self.validated_artifact_node(declaration)?;
        let NodeData::MethodSignatureDeclaration(method) = &record.data else {
            return Err(invalid());
        };
        if record.kind != SyntaxKind::MethodSignature
            || bound.symbol(declaration) != Some(raw)
            || node != declaration && method.name != node.node
        {
            return Err(invalid());
        }
        let owner_node = record
            .parent
            .map(|parent| NodeRef::new(declaration.arena, declaration.file, parent))
            .ok_or_else(invalid)?;
        let (_, owner_bound, owner_record) = self.validated_artifact_node(owner_node)?;
        if !matches!(
            owner_record.kind,
            SyntaxKind::InterfaceDeclaration | SyntaxKind::TypeLiteral
        ) {
            return Err(invalid());
        }
        let raw_owner = owner_bound.symbol(owner_node).ok_or_else(invalid)?;
        let owner = self
            .store()
            .get_merged_symbol(raw_owner)
            .ok_or_else(invalid)?;
        let owner_record = self.store().symbol(owner).ok_or_else(invalid)?;
        let method_record = self.store().symbol(symbol).ok_or_else(invalid)?;
        if self.store().get_merged_symbol(owner) != Some(owner)
            || self.store().get_parent_of_symbol(symbol) != Some(owner)
            || owner_record
                .declarations()
                .unwrap_or_default()
                .iter()
                .filter(|candidate| **candidate == owner_node)
                .count()
                != 1
            || method_record
                .declarations()
                .unwrap_or_default()
                .iter()
                .filter(|candidate| **candidate == declaration)
                .count()
                != 1
            || self
                .store()
                .symbol(raw)
                .is_none_or(|raw| raw.name() != method_record.name())
            || self
                .store()
                .symbol(raw_owner)
                .is_none_or(|raw| raw.name() != owner_record.name())
        {
            return Err(invalid());
        }
        if let Some(selected) = self
            .store()
            .late_bound_links(symbol)
            .and_then(|links| links.late_symbol)
        {
            let selected_record = self.store().symbol(selected).ok_or_else(invalid)?;
            if self.store().get_merged_symbol(selected) != Some(selected)
                || self
                    .store()
                    .late_bound_method_sources(selected)
                    .is_none_or(|sources| !sources.contains(&symbol))
                || self.store().source_declaration_symbol(declaration) != Some(symbol)
                || self.store().get_parent_of_symbol(selected) != Some(owner)
                || selected_record
                    .declarations()
                    .is_none_or(|declarations| !declarations.contains(&declaration))
            {
                return Err(invalid());
            }
        }
        Ok(symbol)
    }

    fn object_literal_property_type(
        &self,
        node: NodeRef,
        symbol: SemanticSymbolId,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let Some(declaration) = self
            .store()
            .symbol(symbol)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
        else {
            return Ok(None);
        };
        let (arena, _, property) = self.validated_artifact_node(declaration)?;
        if !matches!(
            property.data,
            NodeData::PropertyAssignment(_) | NodeData::ShorthandPropertyAssignment(_)
        ) {
            return Ok(None);
        }
        let Some(object_id) = property.parent else {
            return Ok(None);
        };
        let object = NodeRef::new(declaration.arena, declaration.file, object_id);
        if !matches!(
            arena.get(object_id).map(|record| &record.data),
            Some(NodeData::ObjectLiteralExpression(_))
        ) {
            return Ok(None);
        }
        let Some(object_type) = self.cached_artifact_type(object)? else {
            return Ok(None);
        };
        let Some(TypeData::Object(object_data)) =
            self.store().type_payload(object_type).map(TypeRecord::data)
        else {
            return Ok(None);
        };
        let Some(properties) = object_data.structured.properties.as_deref() else {
            return Ok(None);
        };
        let mut result = None;
        for candidate in properties {
            let Some(links) = self.store().value_symbol_links(*candidate) else {
                continue;
            };
            if links.target != Some(symbol) {
                continue;
            }
            let Some(type_) = links.resolved_type else {
                return Err(CanonicalArtifactQueryError::MissingType {
                    node,
                    kind: property.kind,
                });
            };
            let type_ = self.validate_artifact_type(node, type_)?;
            if result.replace(type_).is_some() {
                return Err(CanonicalArtifactQueryError::InvalidSymbol {
                    node,
                    symbol: *candidate,
                });
            }
        }
        Ok(result)
    }

    fn declaration_file_annotation_type(
        &mut self,
        node: NodeRef,
        symbol: SemanticSymbolId,
    ) -> Result<Option<TypeId>, CanonicalArtifactQueryError> {
        let Some(declaration) = self
            .store()
            .symbol(symbol)
            .and_then(ts_binder::semantic::Symbol::value_declaration)
        else {
            return Ok(None);
        };
        let annotation = {
            let (arena, bound, record) = self.validated_artifact_node(declaration)?;
            let declaration_file = bound
                .source_facts()
                .is_some_and(ts_binder::CanonicalSourceFileFacts::is_declaration_file);
            let mut ancestor = Some(declaration.node);
            let mut seen = HashSet::new();
            let mut ambient_variable = false;
            while let Some(node) = ancestor {
                if !seen.insert(node) {
                    break;
                }
                let Some(record) = arena.get(node) else {
                    break;
                };
                if record.kind == SyntaxKind::VariableStatement {
                    ambient_variable = ts_binder::canonical_has_syntactic_modifier(
                        arena,
                        node,
                        SyntaxKind::DeclareKeyword,
                    );
                    break;
                }
                ancestor = record.parent;
            }
            if !declaration_file && !ambient_variable {
                return Ok(None);
            }
            match &record.data {
                NodeData::VariableDeclaration(variable) => variable.type_.map(|annotation| {
                    NodeRef::new(declaration.arena, declaration.file, annotation)
                }),
                NodeData::ParameterDeclaration(parameter) => parameter.type_.map(|annotation| {
                    NodeRef::new(declaration.arena, declaration.file, annotation)
                }),
                NodeData::PropertyDeclaration(property) => property.type_.map(|annotation| {
                    NodeRef::new(declaration.arena, declaration.file, annotation)
                }),
                NodeData::PropertySignatureDeclaration(property) => Some(NodeRef::new(
                    declaration.arena,
                    declaration.file,
                    property.type_,
                )),
                NodeData::GetAccessorDeclaration(_) | NodeData::SetAccessorDeclaration(_) => {
                    self.declaration_file_accessor_annotation(node, symbol)?
                }
                _ => None,
            }
        };
        let Some(annotation) = annotation else {
            return Ok(None);
        };
        let type_ = self.type_node_artifact_type(annotation)?;
        self.validate_artifact_type(node, type_).map(Some)
    }

    fn declaration_file_accessor_annotation(
        &self,
        node: NodeRef,
        symbol: SemanticSymbolId,
    ) -> Result<Option<NodeRef>, CanonicalArtifactQueryError> {
        let record = self
            .store()
            .symbol(symbol)
            .ok_or(CanonicalArtifactQueryError::InvalidSymbol { node, symbol })?;
        if !record.flags().intersects(SymbolFlags::ACCESSOR) {
            return Err(CanonicalArtifactQueryError::InvalidSymbol { node, symbol });
        }

        let mut setter = None;
        for declaration in record.declarations().unwrap_or(&[]) {
            let (_, bound, record) = self.validated_artifact_node(*declaration)?;
            if !bound
                .source_facts()
                .is_some_and(ts_binder::CanonicalSourceFileFacts::is_declaration_file)
            {
                return Ok(None);
            }

            match &record.data {
                NodeData::GetAccessorDeclaration(accessor) => {
                    if record.kind != SyntaxKind::GetAccessor
                        || !accessor.parameters.nodes.is_empty()
                        || accessor.parameters.has_trailing_comma
                    {
                        return Ok(None);
                    }
                    if let Some(annotation) = accessor.type_ {
                        let annotation =
                            NodeRef::new(declaration.arena, declaration.file, annotation);
                        if self.validated_artifact_node(annotation)?.2.parent
                            != Some(declaration.node)
                        {
                            return Err(CanonicalArtifactQueryError::ForeignNode(annotation));
                        }
                        return Ok(Some(annotation));
                    }
                }
                NodeData::SetAccessorDeclaration(_) => setter = Some(*declaration),
                _ => return Ok(None),
            }
        }

        let Some(setter) = setter else {
            return Ok(None);
        };
        let (_, _, record) = self.validated_artifact_node(setter)?;
        let NodeData::SetAccessorDeclaration(accessor) = &record.data else {
            return Err(CanonicalArtifactQueryError::ForeignNode(setter));
        };
        if record.kind != SyntaxKind::SetAccessor
            || accessor.type_.is_some()
            || accessor.parameters.has_trailing_comma
        {
            return Ok(None);
        }
        let [parameter] = accessor.parameters.nodes.as_slice() else {
            return Ok(None);
        };
        let parameter = NodeRef::new(setter.arena, setter.file, *parameter);
        let (_, _, record) = self.validated_artifact_node(parameter)?;
        let NodeData::ParameterDeclaration(data) = &record.data else {
            return Err(CanonicalArtifactQueryError::ForeignNode(parameter));
        };
        if record.kind != SyntaxKind::Parameter || record.parent != Some(setter.node) {
            return Err(CanonicalArtifactQueryError::ForeignNode(parameter));
        }
        let Some(annotation) = data.type_ else {
            return Ok(None);
        };
        let annotation = NodeRef::new(parameter.arena, parameter.file, annotation);
        if self.validated_artifact_node(annotation)?.2.parent != Some(parameter.node) {
            return Err(CanonicalArtifactQueryError::ForeignNode(annotation));
        }
        Ok(Some(annotation))
    }
}

fn location_parent(
    arena: &NodeArena,
    bound: &BoundFile,
    node: NodeRef,
    record: &Node,
) -> Result<Option<LocationParent>, CanonicalArtifactQueryError> {
    let Some(parent_id) = record.parent else {
        return Ok(None);
    };
    let parent = NodeRef::new(node.arena, node.file, parent_id);
    if !bound.contains(parent) {
        return Err(CanonicalArtifactQueryError::ForeignNode(parent));
    }
    let parent_record = arena
        .get(parent_id)
        .ok_or(CanonicalArtifactQueryError::ForeignNode(parent))?;

    if declaration_name(&parent_record.data) == Some(node.node) {
        return Ok(Some(LocationParent::Declaration(parent)));
    }

    match &parent_record.data {
        NodeData::ImportSpecifier(specifier) if specifier.property_name == Some(node.node) => {
            Ok(Some(LocationParent::AliasedPropertyName(parent)))
        }
        NodeData::ExportSpecifier(specifier) if specifier.property_name == Some(node.node) => {
            Ok(Some(LocationParent::AliasedPropertyName(parent)))
        }
        NodeData::PropertyAccessExpression(access) if access.name == node.node => {
            Ok(Some(LocationParent::PropertyAccess(parent)))
        }
        NodeData::ElementAccessExpression(access) if access.argument_expression == node.node => {
            Ok(Some(LocationParent::ElementAccess(parent)))
        }
        NodeData::TypeReferenceNode(reference) if reference.type_name == node.node => {
            Ok(Some(LocationParent::TypeReference(parent)))
        }
        NodeData::TypeQueryNode(query) if query.expr_name == node.node => {
            Ok(Some(LocationParent::TypeQuery(parent)))
        }
        NodeData::QualifiedName(qualified) if qualified.right == node.node => {
            Ok(Some(LocationParent::QualifiedName(parent)))
        }
        _ => Ok(None),
    }
}

fn declaration_name(data: &NodeData) -> Option<NodeId> {
    match data {
        NodeData::BindingElement(declaration) => declaration.name,
        NodeData::ClassDeclaration(declaration) => declaration.name,
        NodeData::ClassExpression(declaration) => declaration.name,
        NodeData::EnumDeclaration(declaration) => Some(declaration.name),
        NodeData::EnumMember(declaration) => Some(declaration.name),
        NodeData::ExportSpecifier(declaration) => Some(declaration.name),
        NodeData::FunctionDeclaration(declaration) => declaration.name,
        NodeData::FunctionExpression(declaration) => declaration.name,
        NodeData::GetAccessorDeclaration(declaration) => Some(declaration.name),
        NodeData::ImportClause(declaration) => declaration.name,
        NodeData::ImportEqualsDeclaration(declaration) => Some(declaration.name),
        NodeData::ImportSpecifier(declaration) => Some(declaration.name),
        NodeData::InterfaceDeclaration(declaration) => Some(declaration.name),
        NodeData::JsxAttribute(declaration) => Some(declaration.name),
        NodeData::MethodDeclaration(declaration) => Some(declaration.name),
        NodeData::MethodSignatureDeclaration(declaration) => Some(declaration.name),
        NodeData::ModuleDeclaration(declaration) => Some(declaration.name),
        NodeData::NamedTupleMember(declaration) => Some(declaration.name),
        NodeData::NamespaceExport(declaration) => Some(declaration.name),
        NodeData::NamespaceExportDeclaration(declaration) => Some(declaration.name),
        NodeData::NamespaceImport(declaration) => Some(declaration.name),
        NodeData::ParameterDeclaration(declaration) => Some(declaration.name),
        NodeData::PropertyAssignment(declaration) => Some(declaration.name),
        NodeData::PropertyDeclaration(declaration) => Some(declaration.name),
        NodeData::PropertySignatureDeclaration(declaration) => Some(declaration.name),
        NodeData::SetAccessorDeclaration(declaration) => Some(declaration.name),
        NodeData::ShorthandPropertyAssignment(declaration) => Some(declaration.name),
        NodeData::TypeAliasDeclaration(declaration) => Some(declaration.name),
        NodeData::TypeParameterDeclaration(declaration) => Some(declaration.name),
        NodeData::VariableDeclaration(declaration) => Some(declaration.name),
        _ => None,
    }
}

fn is_type_syntax(data: &NodeData) -> bool {
    matches!(
        data,
        NodeData::ArrayTypeNode(_)
            | NodeData::ConditionalTypeNode(_)
            | NodeData::ConstructorTypeNode(_)
            | NodeData::FunctionTypeNode(_)
            | NodeData::ImportTypeNode(_)
            | NodeData::IndexedAccessTypeNode(_)
            | NodeData::InferTypeNode(_)
            | NodeData::IntersectionTypeNode(_)
            | NodeData::KeywordTypeNode(_)
            | NodeData::LiteralTypeNode(_)
            | NodeData::MappedTypeNode(_)
            | NodeData::OptionalTypeNode(_)
            | NodeData::ParenthesizedTypeNode(_)
            | NodeData::RestTypeNode(_)
            | NodeData::TemplateLiteralTypeNode(_)
            | NodeData::ThisTypeNode(_)
            | NodeData::TupleTypeNode(_)
            | NodeData::TypeLiteralNode(_)
            | NodeData::TypeOperatorNode(_)
            | NodeData::TypePredicateNode(_)
            | NodeData::TypeQueryNode(_)
            | NodeData::TypeReferenceNode(_)
            | NodeData::UnionTypeNode(_)
    )
}

fn supports_type_location(data: &NodeData) -> bool {
    is_type_syntax(data)
        || matches!(
            data,
            NodeData::ArrayLiteralExpression(_)
                | NodeData::ArrowFunction(_)
                | NodeData::AsExpression(_)
                | NodeData::AwaitExpression(_)
                | NodeData::BigIntLiteral(_)
                | NodeData::BinaryExpression(_)
                | NodeData::CallExpression(_)
                | NodeData::ClassDeclaration(_)
                | NodeData::ClassExpression(_)
                | NodeData::ConditionalExpression(_)
                | NodeData::DeleteExpression(_)
                | NodeData::ElementAccessExpression(_)
                | NodeData::EnumDeclaration(_)
                | NodeData::EnumMember(_)
                | NodeData::ExpressionWithTypeArguments(_)
                | NodeData::FunctionDeclaration(_)
                | NodeData::FunctionExpression(_)
                | NodeData::GetAccessorDeclaration(_)
                | NodeData::Identifier(_)
                | NodeData::ImportClause(_)
                | NodeData::ImportSpecifier(_)
                | NodeData::InterfaceDeclaration(_)
                | NodeData::JsxAttribute(_)
                | NodeData::JsxClosingElement(_)
                | NodeData::JsxClosingFragment(_)
                | NodeData::JsxElement(_)
                | NodeData::JsxExpression(_)
                | NodeData::JsxFragment(_)
                | NodeData::JsxOpeningElement(_)
                | NodeData::JsxOpeningFragment(_)
                | NodeData::JsxSelfClosingElement(_)
                | NodeData::KeywordExpression(_)
                | NodeData::MetaProperty(_)
                | NodeData::MethodDeclaration(_)
                | NodeData::MethodSignatureDeclaration(_)
                | NodeData::NewExpression(_)
                | NodeData::NoSubstitutionTemplateLiteral(_)
                | NodeData::NonNullExpression(_)
                | NodeData::NumericLiteral(_)
                | NodeData::ObjectLiteralExpression(_)
                | NodeData::OmittedExpression(_)
                | NodeData::ParameterDeclaration(_)
                | NodeData::ParenthesizedExpression(_)
                | NodeData::PostfixUnaryExpression(_)
                | NodeData::PrefixUnaryExpression(_)
                | NodeData::PrivateIdentifier(_)
                | NodeData::PropertyAccessExpression(_)
                | NodeData::PropertyAssignment(_)
                | NodeData::PropertyDeclaration(_)
                | NodeData::PropertySignatureDeclaration(_)
                | NodeData::QualifiedName(_)
                | NodeData::RegularExpressionLiteral(_)
                | NodeData::SatisfiesExpression(_)
                | NodeData::SetAccessorDeclaration(_)
                | NodeData::ShorthandPropertyAssignment(_)
                | NodeData::SpreadElement(_)
                | NodeData::StringLiteral(_)
                | NodeData::TaggedTemplateExpression(_)
                | NodeData::TemplateExpression(_)
                | NodeData::TypeAliasDeclaration(_)
                | NodeData::TypeAssertion(_)
                | NodeData::TypeOfExpression(_)
                | NodeData::TypeParameterDeclaration(_)
                | NodeData::VariableDeclaration(_)
                | NodeData::VoidExpression(_)
                | NodeData::YieldExpression(_)
        )
}

fn supports_symbol_location(data: &NodeData) -> bool {
    supports_type_location(data)
        || matches!(
            data,
            NodeData::ExportSpecifier(_)
                | NodeData::ImportEqualsDeclaration(_)
                | NodeData::ModuleDeclaration(_)
                | NodeData::NamespaceExport(_)
                | NodeData::NamespaceExportDeclaration(_)
                | NodeData::NamespaceImport(_)
                | NodeData::SourceFile(_)
        )
}

#[cfg(test)]
mod cold_merged_namespace_tests;

#[cfg(test)]
mod export_equals_final_invariant_tests;

#[cfg(test)]
mod heritage_super_query_tests;

#[cfg(test)]
#[path = "type_name_symbol_root_tests.rs"]
mod type_name_symbol_root_tests;

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        CheckFlags, EscapedName, InternalSymbolName, SymbolData, SymbolFlags,
    };
    use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};

    use super::{CanonicalArtifactQueryError, CanonicalCheckerContext};
    use crate::semantic::{
        AliasSymbolLinks, AliasTargetState, CanonicalCheckerOptions,
        CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
        CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, DeclaredTypeLinks,
        IntrinsicBootstrapOptions, ModuleSymbolLinks, SymbolNodeLinks, TypeData, TypeNodeLinks,
        ValueSymbolLinks,
        types::{ObjectFlags, TypeFlags},
    };

    fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        context_with_options(parsed, file, CanonicalCheckerOptions::default())
    }

    fn context_with_options(
        parsed: &ParseResult,
        file: FileId,
        options: CanonicalCheckerOptions,
    ) -> CanonicalCheckerContext<'_> {
        context_with_source_kind(parsed, file, options, false)
    }

    fn declaration_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        context_with_source_kind(parsed, file, CanonicalCheckerOptions::default(), true)
    }

    fn declaration_method_nodes(parsed: &ParseResult, file: FileId) -> Vec<(NodeRef, NodeRef)> {
        parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, method.name),
                ))
            })
            .collect()
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Check private allocation counters for both cold query orders.
    fn decorator_queries_keep_checker_link_allocations_stable() {
        for (declaration_file, text) in [
            (false, "class {\n  @x\n  m() {\n    // ...\n  }\n};\n"),
            (
                true,
                "declare const decorate: () => void;\nclass {\n  @decorate\n  m(): void;\n}\n",
            ),
            (
                true,
                "declare const decorate: () => void;\ndeclare class Named {\n  @decorate\n  m(): void;\n}\n",
            ),
            (
                true,
                concat!(
                    "declare class Decorators { static apply(): void; }\n",
                    "declare class Named { @Decorators.apply m(): void; }\n",
                ),
            ),
        ] {
            for type_first in [false, true] {
                let parsed = parse_source_file(text);
                let file = FileId::new(6_220);
                let mut context = context_with_source_kind(
                    &parsed,
                    file,
                    CanonicalCheckerOptions::default(),
                    declaration_file,
                );
                let expression = parsed
                    .arena
                    .iter()
                    .find_map(|(_, record)| {
                        let NodeData::Decorator(decorator) = &record.data else {
                            return None;
                        };
                        Some(NodeRef::new(parsed.arena.id(), file, decorator.expression))
                    })
                    .unwrap();
                let type_nodes = match &parsed.arena.get(expression.node).unwrap().data {
                    NodeData::PropertyAccessExpression(access) => vec![
                        NodeRef::new(parsed.arena.id(), file, access.expression),
                        expression,
                        NodeRef::new(parsed.arena.id(), file, access.name),
                    ],
                    _ => vec![expression],
                };
                let mut symbol_nodes = type_nodes.clone();
                if !declaration_file {
                    let method_name = parsed
                        .arena
                        .iter()
                        .find_map(|(_, record)| {
                            let NodeData::MethodDeclaration(method) = &record.data else {
                                return None;
                            };
                            Some(NodeRef::new(parsed.arena.id(), file, method.name))
                        })
                        .unwrap();
                    symbol_nodes.push(method_name);
                }

                if !type_first {
                    for node in &symbol_nodes {
                        context.get_symbol_at_location(*node).unwrap();
                    }
                }
                let types = type_nodes
                    .iter()
                    .map(|node| context.get_type_at_location(*node))
                    .collect::<Vec<_>>();
                if declaration_file {
                    for type_ in &types {
                        context.type_to_string((*type_).unwrap()).unwrap();
                    }
                } else {
                    assert_eq!(
                        types,
                        [Err(CanonicalArtifactQueryError::MissingType {
                            node: expression,
                            kind: SyntaxKind::Identifier,
                        })]
                    );
                }
                let symbols = symbol_nodes
                    .iter()
                    .map(|node| context.get_symbol_at_location(*node).unwrap())
                    .collect::<Vec<_>>();
                for symbol in symbols.iter().flatten() {
                    context.symbol_to_string(*symbol).unwrap();
                    context.get_symbol_declarations(*symbol).unwrap();
                }
                let warm = context.store().checker_link_allocated_lengths();
                let diagnostics = context.diagnostics().clone();

                for _ in 0..3 {
                    if !declaration_file {
                        context.recheck_source_file(file).unwrap();
                    }
                    for (node, expected) in symbol_nodes.iter().zip(&symbols) {
                        assert_eq!(context.get_symbol_at_location(*node), Ok(*expected));
                    }
                    for (node, expected) in type_nodes.iter().zip(&types) {
                        assert_eq!(context.get_type_at_location(*node), *expected);
                    }
                    assert_eq!(context.store().checker_link_allocated_lengths(), warm);
                    assert_eq!(context.diagnostics(), &diagnostics);
                }
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep both existing identities and rejected cache changes together.
    fn export_equals_queries_keep_declared_and_value_identities_separate() {
        for (index, text) in [
            "class Value { value: number = 1; }\nconst observed = Value;\nexport = Value;\n",
            "enum Value { One = 0, Two = 1 }\nconst observed = Value;\nexport = Value;\n",
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(text);
            assert!(parsed.diagnostics.is_empty());
            let file = FileId::new(147_020 + u32::try_from(index).unwrap());
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/export.ts\""),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::External,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
            let mut context = CanonicalCheckerContext::new(
                binder.finish(),
                [(file, &parsed.arena)].into_iter().collect(),
                CanonicalCheckerOptions::default(),
            )
            .unwrap();
            context.check_source_file(file).unwrap();
            let declaration = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(
                        record.kind,
                        SyntaxKind::ClassDeclaration | SyntaxKind::EnumDeclaration
                    )
                    .then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
            let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
            let owner = context.store().get_merged_symbol(owner).unwrap();
            let declared_links = context.store().declared_type_links(owner).cloned().unwrap();
            let declared = declared_links.declared_type.unwrap();
            let value = context
                .store()
                .value_symbol_links(owner)
                .unwrap()
                .resolved_type
                .unwrap();
            assert_ne!(declared, value);
            let exported = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::ExportAssignment(export) = &record.data else {
                        return None;
                    };
                    Some(NodeRef::new(parsed.arena.id(), file, export.expression))
                })
                .unwrap();
            let read = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::VariableDeclaration(variable) = &record.data else {
                        return None;
                    };
                    Some(NodeRef::new(parsed.arena.id(), file, variable.initializer?))
                })
                .unwrap();
            assert!(
                context
                    .store()
                    .type_node_links(exported)
                    .and_then(|links| links.resolved_type)
                    .is_none()
            );
            assert!(
                context
                    .store()
                    .symbol_node_links(exported)
                    .and_then(|links| links.resolved_symbol)
                    .is_none()
            );
            let state = |store: &crate::semantic::CanonicalTypeMapperStore| {
                (
                    [
                        store.type_len(),
                        store.symbol_len(),
                        store.signature_len(),
                        store.mapper_len(),
                    ],
                    store.checker_link_allocated_lengths(),
                    store.declared_type_links(owner).cloned(),
                    store.value_symbol_links(owner).cloned(),
                    store.type_node_links(exported).cloned(),
                    store.symbol_node_links(exported).cloned(),
                    store.relation_state_snapshot(),
                )
            };
            for replay in [false, true] {
                let before = state(context.store());
                if replay {
                    context.recheck_source_file(file).unwrap();
                }
                assert_eq!(context.get_type_at_location(exported), Ok(declared));
                assert_eq!(context.get_type_at_location(read), Ok(value));
                assert_eq!(context.get_symbol_at_location(exported), Ok(Some(owner)));
                assert_eq!(context.type_to_string(declared).unwrap(), "Value");
                assert_eq!(context.type_to_string(value).unwrap(), "typeof Value");
                assert_eq!(state(context.store()), before);
            }
            for missing_declared in [false, true] {
                if missing_declared {
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_declared_type_links(owner, DeclaredTypeLinks::default())
                    );
                } else {
                    assert!(context.store_mut_for_test().set_type_node_links(
                        exported,
                        TypeNodeLinks {
                            resolved_type: Some(value),
                            ..TypeNodeLinks::default()
                        }
                    ));
                }
                let before = state(context.store());
                assert!(context.get_type_at_location(exported).is_err());
                assert_eq!(state(context.store()), before);
                assert!(
                    context
                        .store_mut_for_test()
                        .set_declared_type_links(owner, declared_links.clone())
                );
                assert!(
                    context
                        .store_mut_for_test()
                        .set_type_node_links(exported, TypeNodeLinks::default())
                );
                assert_eq!(context.get_type_at_location(exported), Ok(declared));
            }
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn type_reference_qualifiers_do_not_change_type_query_expressions() {
        let parsed = parse_source_file(concat!(
            "declare namespace Scope { interface Item {} const value: number; }\n",
            "declare let item: Scope.Item;\n",
            "type Value = typeof Scope.value;\n",
        ));
        let file = FileId::new(6_075);
        let mut context = context(&parsed, file);
        let names = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                matches!(&record.data, NodeData::Identifier(identifier) if identifier.text == "Scope")
                    .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .collect::<Vec<_>>();
        let [declaration, qualifier, expression] = names.as_slice() else {
            panic!("expected a declaration, type-reference qualifier, and type-query expression")
        };
        let error = context.store().intrinsic_bootstrap().unwrap().error_type;
        assert_eq!(
            context.type_reference_qualifier_artifact_type(*declaration),
            Ok(None)
        );
        assert_eq!(
            context.type_reference_qualifier_artifact_type(*qualifier),
            Ok(Some(error))
        );
        assert_eq!(
            context.type_reference_qualifier_artifact_type(*expression),
            Ok(None)
        );
        let wrong = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(context.store_mut_for_test().set_type_node_links(
            *qualifier,
            TypeNodeLinks {
                resolved_type: Some(wrong),
                ..TypeNodeLinks::default()
            },
        ));
        let source = context.source_file(file).unwrap();
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
            context.store().source_file_links(source).cloned(),
            context.diagnostics().len(),
        );
        assert_eq!(
            context.get_type_at_location(*qualifier),
            Err(CanonicalArtifactQueryError::InvalidType {
                node: *qualifier,
                type_: wrong
            }),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().source_file_links(source).cloned(),
                context.diagnostics().len(),
            ),
            before,
        );
    }

    fn context_with_source_kind(
        parsed: &ParseResult,
        file: FileId,
        options: CanonicalCheckerOptions,
        declaration_file: bool,
    ) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/artifacts.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    declaration_file,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(binder.finish(), vec![(file, &parsed.arena)], options).unwrap()
    }

    #[derive(Clone, Copy)]
    struct NamespaceAliasNodes {
        declaration: NodeRef,
        name: NodeRef,
        specifier: NodeRef,
        read: NodeRef,
    }

    fn namespace_alias_nodes(parsed: &ParseResult, file: FileId) -> NamespaceAliasNodes {
        let reference = |node| NodeRef::new(parsed.arena.id(), file, node);
        let (declaration, name) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| match &record.data {
                NodeData::NamespaceImport(namespace) => {
                    Some((reference(node), reference(namespace.name)))
                }
                _ => None,
            })
            .unwrap();
        let specifier = parsed
            .arena
            .iter()
            .find_map(|(_, record)| match &record.data {
                NodeData::ImportDeclaration(import) => Some(reference(import.module_specifier)),
                _ => None,
            })
            .unwrap();
        let read = parsed
            .arena
            .iter()
            .find_map(|(_, record)| match &record.data {
                NodeData::ExpressionStatement(statement) => Some(reference(statement.expression)),
                _ => None,
            })
            .unwrap();
        NamespaceAliasNodes {
            declaration,
            name,
            specifier,
            read,
        }
    }

    fn namespace_alias_context(
        parsed: &ParseResult,
        file: FileId,
        manifest: Option<CanonicalModuleResolutionManifestInput>,
    ) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/main.cts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let files = vec![(file, &parsed.arena)];
        match manifest {
            Some(manifest) => CanonicalCheckerContext::new_with_module_resolutions(
                binder.finish(),
                files,
                CanonicalCheckerOptions::default(),
                manifest,
            ),
            None => CanonicalCheckerContext::new(
                binder.finish(),
                files,
                CanonicalCheckerOptions::default(),
            ),
        }
        .unwrap()
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Cold, warm, and replay queries use the same checker graph.
    fn unresolved_namespace_alias_declaration_queries_reuse_source_recovery_cold_and_warm() {
        for name in ["s", "renamed"] {
            let parsed = parse_source_file(&format!("import * as {name} from 'self';\n{name};\n"));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(6_080);
            let nodes = namespace_alias_nodes(&parsed, file);
            let mut context = namespace_alias_context(
                &parsed,
                file,
                Some(CanonicalModuleResolutionManifestInput::new([
                    CanonicalModuleResolutionEntry::unresolved(nodes.specifier),
                ])),
            );
            let alias = context
                .file(file)
                .unwrap()
                .1
                .symbol(nodes.declaration)
                .unwrap();
            let error_type = context.store().intrinsic_bootstrap().unwrap().error_type;
            assert_ne!(
                error_type,
                context.store().intrinsic_bootstrap().unwrap().any_type
            );
            assert!(context.store().type_node_links(nodes.read).is_none());

            assert_eq!(context.get_type_at_location(nodes.name), Ok(error_type));
            assert_eq!(context.get_type_at_location(nodes.read), Ok(error_type));
            assert_eq!(context.type_to_string(error_type).unwrap(), "any");
            assert_eq!(context.get_symbol_at_location(nodes.name), Ok(Some(alias)));
            assert_eq!(context.get_symbol_at_location(nodes.read), Ok(Some(alias)));
            assert_eq!(
                context.get_symbol_declarations(alias).unwrap(),
                &[nodes.declaration]
            );
            assert_eq!(
                context
                    .symbol_to_string_at_location(alias, nodes.declaration)
                    .unwrap(),
                name
            );
            assert!(context.store().alias_symbol_links(alias).is_none());
            assert!(context.store().value_symbol_links(alias).is_none());
            let warm = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().len(),
            );
            for _ in 0..2 {
                assert_eq!(context.get_type_at_location(nodes.name), Ok(error_type));
                assert_eq!(context.get_type_at_location(nodes.read), Ok(error_type));
                assert_eq!(context.get_symbol_at_location(nodes.name), Ok(Some(alias)));
                assert_eq!(context.get_symbol_at_location(nodes.read), Ok(Some(alias)));
                assert_eq!(
                    context.module_resolution(nodes.specifier),
                    crate::semantic::CanonicalModuleResolutionLookup::Unresolved,
                );
                assert!(context.store().alias_symbol_links(alias).is_none());
                assert!(context.store().value_symbol_links(alias).is_none());
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().symbol_len(),
                        context.store().checker_link_allocated_lengths(),
                        context.diagnostics().len(),
                    ),
                    warm,
                );
            }
            context.recheck_source_file(file).unwrap();
            assert_eq!(context.get_type_at_location(nodes.name), Ok(error_type));
            assert_eq!(context.get_symbol_at_location(nodes.name), Ok(Some(alias)));
            assert!(context.store().alias_symbol_links(alias).is_none());
            assert!(context.store().value_symbol_links(alias).is_none());
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Apply each cache control to an independently checked source.
    fn unresolved_namespace_alias_declaration_queries_reject_changed_recovery_caches() {
        for poison in [
            "name_type",
            "declaration_type",
            "read_type",
            "read_metadata",
            "missing_read",
            "name_symbol",
            "read_symbol",
            "alias_value",
            "alias_target",
        ] {
            let parsed = parse_source_file("import * as s from 'self';\ns;\n");
            let file = FileId::new(6_081);
            let nodes = namespace_alias_nodes(&parsed, file);
            let mut context = namespace_alias_context(
                &parsed,
                file,
                Some(CanonicalModuleResolutionManifestInput::new([
                    CanonicalModuleResolutionEntry::unresolved(nodes.specifier),
                ])),
            );
            context.check_source_file(file).unwrap();
            let alias = context
                .file(file)
                .unwrap()
                .1
                .symbol(nodes.declaration)
                .unwrap();
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let number = bootstrap.number_type;
            let error_type = bootstrap.error_type;
            let wrong_symbol = bootstrap.unknown_symbol;
            match poison {
                "name_type" | "declaration_type" | "read_type" => {
                    let node = match poison {
                        "name_type" => nodes.name,
                        "declaration_type" => nodes.declaration,
                        _ => nodes.read,
                    };
                    assert!(context.store_mut_for_test().set_type_node_links(
                        node,
                        TypeNodeLinks {
                            resolved_type: Some(number),
                            ..TypeNodeLinks::default()
                        }
                    ));
                }
                "read_metadata" => assert!(context.store_mut_for_test().set_type_node_links(
                    nodes.read,
                    TypeNodeLinks {
                        resolved_type: Some(error_type),
                        outer_type_parameters: Some(Vec::new()),
                    },
                )),
                "missing_read" => assert!(
                    context
                        .store_mut_for_test()
                        .set_type_node_links(nodes.read, TypeNodeLinks::default(),)
                ),
                "name_symbol" | "read_symbol" => {
                    let node = if poison == "name_symbol" {
                        nodes.name
                    } else {
                        nodes.read
                    };
                    assert!(context.store_mut_for_test().set_symbol_node_links(
                        node,
                        SymbolNodeLinks {
                            resolved_symbol: Some(wrong_symbol),
                        }
                    ));
                }
                "alias_value" => assert!(context.store_mut_for_test().set_value_symbol_links(
                    alias,
                    ValueSymbolLinks {
                        resolved_type: Some(number),
                        ..ValueSymbolLinks::default()
                    }
                )),
                "alias_target" => assert!(context.store_mut_for_test().set_alias_symbol_links(
                    alias,
                    AliasSymbolLinks {
                        immediate_target: Some(wrong_symbol),
                        alias_target: AliasTargetState::Resolved(wrong_symbol),
                        ..AliasSymbolLinks::default()
                    }
                )),
                _ => unreachable!("every recovery cache control is covered"),
            }
            let state = |context: &CanonicalCheckerContext<'_>| {
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.store().alias_symbol_links(alias).cloned(),
                    context.store().value_symbol_links(alias).cloned(),
                    [nodes.name, nodes.declaration, nodes.read].map(|node| {
                        (
                            context.store().type_node_links(node).cloned(),
                            context.store().symbol_node_links(node).cloned(),
                        )
                    }),
                    context.diagnostics().len(),
                )
            };
            let before = state(&context);
            assert!(
                matches!(
                    context.get_type_at_location(nodes.name),
                    Err(CanonicalArtifactQueryError::InvalidType { .. }
                        | CanonicalArtifactQueryError::InvalidSymbol { .. }
                        | CanonicalArtifactQueryError::MissingType { .. })
                ),
                "recovery cache control {poison} was accepted"
            );
            assert_eq!(
                state(&context),
                before,
                "recovery cache control {poison} changed state"
            );
        }
    }

    fn catch_rest_nodes(parsed: &ParseResult, file: FileId) -> (NodeRef, NodeRef) {
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::BindingElement(binding) = &record.data else {
                    return None;
                };
                binding.dot_dot_dot_token?;
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, binding.name?),
                ))
            })
            .unwrap()
    }

    #[test]
    fn catch_rest_artifacts_follow_the_option_without_publishing_bindings() {
        let parsed = parse_source_file("try {\n  // ...\n} catch ({ ...rest }) {\n  // ...\n}\n");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_210);
        let (element, name) = catch_rest_nodes(&parsed, file);
        for (use_unknown_in_catch_variables, checked_first) in [false, true]
            .into_iter()
            .flat_map(|unknown| [false, true].map(|checked| (unknown, checked)))
        {
            let mut context = context_with_options(
                &parsed,
                file,
                CanonicalCheckerOptions {
                    use_unknown_in_catch_variables,
                    ..CanonicalCheckerOptions::default()
                },
            );
            if checked_first {
                context.check_source_file(file).unwrap();
            }
            let symbol = context.file(file).unwrap().1.symbol(element).unwrap();
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            let expected = if use_unknown_in_catch_variables {
                bootstrap.error_type
            } else {
                bootstrap.any_type
            };
            assert_ne!(bootstrap.error_type, bootstrap.any_type);
            assert_eq!(context.get_type_at_location(name), Ok(expected));
            assert_eq!(context.type_to_string(expected).unwrap(), "any");
            assert_eq!(context.get_symbol_at_location(name), Ok(Some(symbol)));
            assert_eq!(
                context.diagnostics().len(),
                usize::from(use_unknown_in_catch_variables),
            );
            if use_unknown_in_catch_variables {
                let [diagnostic] = context.diagnostics().as_slice() else {
                    panic!("expected the catch-rest diagnostic")
                };
                assert_eq!(diagnostic.node, Some(name));
                assert_eq!(diagnostic.diagnostic.code(), 2700);
            }
            let state = |context: &CanonicalCheckerContext<'_>| {
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().as_slice().to_vec(),
                )
            };
            let warm = state(&context);
            for _ in 0..2 {
                for location in [element, name] {
                    assert_eq!(context.get_type_at_location(location), Ok(expected));
                    assert_eq!(context.get_symbol_at_location(location), Ok(Some(symbol)));
                    assert!(context.store().type_node_links(location).is_none());
                    assert!(context.store().symbol_node_links(location).is_none());
                }
                assert!(context.store().value_symbol_links(symbol).is_none());
                context.recheck_source_file(file).unwrap();
                assert_eq!(state(&context), warm);
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Check both locations against cold and warm cache failures.
    fn catch_rest_artifacts_reject_poisoned_caches_before_source_writes() {
        let parsed = parse_source_file("try {} catch ({ ...rest }) {}");
        let file = FileId::new(6_211);
        let (element, name) = catch_rest_nodes(&parsed, file);
        for (use_unknown_in_catch_variables, checked_first) in [false, true]
            .into_iter()
            .flat_map(|unknown| [false, true].map(|checked| (unknown, checked)))
        {
            for location in [element, name] {
                for poison in ["type", "metadata", "value", "write", "symbol"] {
                    let mut context = context_with_options(
                        &parsed,
                        file,
                        CanonicalCheckerOptions {
                            use_unknown_in_catch_variables,
                            ..CanonicalCheckerOptions::default()
                        },
                    );
                    if checked_first {
                        context.check_source_file(file).unwrap();
                    }
                    let symbol = context.file(file).unwrap().1.symbol(element).unwrap();
                    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
                    let (expected, wrong) = if use_unknown_in_catch_variables {
                        (bootstrap.error_type, bootstrap.any_type)
                    } else {
                        (bootstrap.any_type, bootstrap.error_type)
                    };
                    let other_symbol = bootstrap.undefined_symbol;
                    match poison {
                        "type" | "metadata" => {
                            assert!(context.store_mut_for_test().set_type_node_links(
                                location,
                                TypeNodeLinks {
                                    resolved_type: (poison == "type").then_some(wrong),
                                    outer_type_parameters:
                                        (poison == "metadata").then(|| vec![expected]),
                                },
                            ));
                        }
                        "value" | "write" => {
                            assert!(context.store_mut_for_test().set_value_symbol_links(
                                symbol,
                                ValueSymbolLinks {
                                    resolved_type: (poison == "value").then_some(expected),
                                    write_type: (poison == "write").then_some(expected),
                                    ..ValueSymbolLinks::default()
                                },
                            ));
                        }
                        "symbol" => {
                            assert!(context.store_mut_for_test().set_symbol_node_links(
                                location,
                                SymbolNodeLinks {
                                    resolved_symbol: Some(other_symbol),
                                },
                            ));
                        }
                        _ => unreachable!(),
                    }
                    let state = |context: &CanonicalCheckerContext<'_>| {
                        (
                            context.store().type_len(),
                            context.store().signature_len(),
                            context.store().checker_link_allocated_lengths(),
                            context.store().type_node_links(location).cloned(),
                            context.store().symbol_node_links(location).cloned(),
                            context.store().value_symbol_links(symbol).cloned(),
                            context
                                .store()
                                .source_file_links(context.source_file(file).unwrap())
                                .cloned(),
                            context.diagnostics().as_slice().to_vec(),
                        )
                    };
                    let poisoned = state(&context);
                    for target in [element, name] {
                        let error = context.get_type_at_location(target).unwrap_err();
                        match poison {
                            "type" | "metadata" => assert!(matches!(
                                error,
                                CanonicalArtifactQueryError::InvalidType { node, .. }
                                    if node == location
                            )),
                            "value" | "write" => assert!(matches!(
                                error,
                                CanonicalArtifactQueryError::SourceCheck(_)
                            )),
                            "symbol" => assert_eq!(
                                error,
                                CanonicalArtifactQueryError::InvalidSymbol {
                                    node: location,
                                    symbol: other_symbol,
                                },
                            ),
                            _ => unreachable!(),
                        }
                        assert_eq!(state(&context), poisoned, "{poison}");
                    }
                    match poison {
                        "type" | "metadata" => assert!(
                            context
                                .store_mut_for_test()
                                .set_type_node_links(location, TypeNodeLinks::default())
                        ),
                        "value" | "write" => assert!(
                            context
                                .store_mut_for_test()
                                .set_value_symbol_links(symbol, ValueSymbolLinks::default())
                        ),
                        "symbol" => assert!(
                            context
                                .store_mut_for_test()
                                .set_symbol_node_links(location, SymbolNodeLinks::default())
                        ),
                        _ => unreachable!(),
                    }
                    assert_eq!(context.get_type_at_location(name), Ok(expected));
                    context.recheck_source_file(file).unwrap();
                    assert_eq!(
                        context.diagnostics().len(),
                        usize::from(use_unknown_in_catch_variables),
                    );
                    assert!(
                        context
                            .store()
                            .value_symbol_links(symbol)
                            .is_none_or(|links| { links == &ValueSymbolLinks::default() })
                    );
                }
            }
        }
    }

    #[test]
    fn catch_rest_artifacts_reject_foreign_nodes_and_changed_owners() {
        let parsed = parse_source_file("try {} catch ({ ...rest }) {}");
        let foreign = parse_source_file("try {} catch ({ ...rest }) {}");
        let file = FileId::new(6_212);
        let (element, name) = catch_rest_nodes(&parsed, file);
        let (_, foreign_name) = catch_rest_nodes(&foreign, file);
        for (use_unknown_in_catch_variables, checked_first) in [false, true]
            .into_iter()
            .flat_map(|unknown| [false, true].map(|checked| (unknown, checked)))
        {
            let mut context = context_with_options(
                &parsed,
                file,
                CanonicalCheckerOptions {
                    use_unknown_in_catch_variables,
                    ..CanonicalCheckerOptions::default()
                },
            );
            if checked_first {
                context.check_source_file(file).unwrap();
            }
            let before = (
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().as_slice().to_vec(),
            );
            assert_eq!(
                context.get_type_at_location(foreign_name),
                Err(CanonicalArtifactQueryError::ForeignNode(foreign_name)),
            );
            let symbol = context.file(file).unwrap().1.symbol(element).unwrap();
            assert!(context.store_mut_for_test().set_symbol_flags(
                symbol,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                CheckFlags::NONE,
            ));
            assert!(matches!(
                context.get_type_at_location(name),
                Err(CanonicalArtifactQueryError::SourceCheck(_)),
            ));
            assert_eq!(
                (
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().as_slice().to_vec(),
                ),
                before,
            );
            assert!(context.store().value_symbol_links(symbol).is_none());
        }
    }

    #[test]
    fn unresolved_namespace_alias_declaration_queries_require_exact_manifest_evidence() {
        let parsed = parse_source_file("import * as s from 'self';\ns;\n");
        let file = FileId::new(6_082);
        let nodes = namespace_alias_nodes(&parsed, file);
        for manifest in [None, Some(CanonicalModuleResolutionManifestInput::new([]))] {
            let mut context = namespace_alias_context(&parsed, file, manifest);
            let before = context.module_resolution(nodes.specifier);
            assert!(context.get_type_at_location(nodes.name).is_err());
            assert_eq!(context.module_resolution(nodes.specifier), before);
        }
        let mut context = namespace_alias_context(
            &parsed,
            file,
            Some(CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::unresolved(nodes.specifier),
            ])),
        );
        let foreign = parse_source_file("import * as s from 'self';\ns;\n");
        let foreign_name = NodeRef::new(foreign.arena.id(), file, nodes.name.node);
        assert_eq!(
            context.get_type_at_location(foreign_name),
            Err(CanonicalArtifactQueryError::ForeignNode(foreign_name))
        );
        assert!(context.store().type_node_links(nodes.read).is_none());

        let unsupported = parse_source_file("import * as s from 'missing';\ns;\n");
        let nodes = namespace_alias_nodes(&unsupported, file);
        let mut context = namespace_alias_context(
            &unsupported,
            file,
            Some(CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::unresolved(nodes.specifier),
            ])),
        );
        assert!(matches!(
            context.get_type_at_location(nodes.name),
            Err(CanonicalArtifactQueryError::SourceCheck(_))
        ));
    }

    #[test]
    fn declaration_method_locations_reject_redirected_source_symbols() {
        for source in [
            "interface A { run(): number; } interface B { run(): string; } interface C { run(): boolean; }",
            "interface A { run(): number; other(): string; last(): boolean; }",
        ] {
            for warm in [false, true] {
                for chained in [false, true] {
                    let parsed = parse_source_file(source);
                    let file = FileId::new(6_131);
                    let mut context = declaration_context(&parsed, file);
                    let locations = declaration_method_nodes(&parsed, file);
                    let symbols = locations
                        .iter()
                        .map(|(declaration, _)| {
                            context.file(file).unwrap().1.symbol(*declaration).unwrap()
                        })
                        .collect::<Vec<_>>();
                    if warm {
                        for (_, name) in &locations {
                            context.get_type_at_location(*name).unwrap();
                        }
                    }
                    context
                        .store_mut_for_test()
                        .record_merged_symbol(symbols[1], symbols[0])
                        .unwrap();
                    if chained {
                        context
                            .store_mut_for_test()
                            .record_merged_symbol(symbols[2], symbols[1])
                            .unwrap();
                    }
                    let before = (
                        context.store().type_len(),
                        context.store().signature_len(),
                        context.store().checker_link_allocated_lengths(),
                        context.store().relation_state_snapshot(),
                    );
                    for node in [locations[0].0, locations[0].1] {
                        let expected = CanonicalArtifactQueryError::InvalidSymbol {
                            node,
                            symbol: symbols[1],
                        };
                        assert_eq!(context.get_type_at_location(node), Err(expected));
                        assert_eq!(context.get_symbol_at_location(node), Err(expected));
                    }
                    assert_eq!(
                        (
                            context.store().type_len(),
                            context.store().signature_len(),
                            context.store().checker_link_allocated_lengths(),
                            context.store().relation_state_snapshot()
                        ),
                        before
                    );
                    assert!(context.diagnostics().is_empty());
                }
            }
        }
    }

    #[test]
    fn declaration_method_locations_require_the_queried_declaration() {
        let parsed =
            parse_source_file("interface A { run(): number; } interface B { run(): string; }");
        let file = FileId::new(6_132);
        let mut context = declaration_context(&parsed, file);
        let locations = declaration_method_nodes(&parsed, file);
        let symbols = locations
            .iter()
            .map(|(declaration, _)| context.file(file).unwrap().1.symbol(*declaration).unwrap())
            .collect::<Vec<_>>();
        let owner = context.store().symbol(symbols[0]).unwrap().parent();
        assert!(
            context
                .store_mut_for_test()
                .set_symbol_relationships(symbols[1], None, None, owner, None)
        );
        context
            .store_mut_for_test()
            .record_merged_symbol(symbols[1], symbols[0])
            .unwrap();
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for node in [locations[0].0, locations[0].1] {
            let expected = CanonicalArtifactQueryError::InvalidSymbol {
                node,
                symbol: symbols[1],
            };
            assert_eq!(context.get_type_at_location(node), Err(expected));
            assert_eq!(context.get_symbol_at_location(node), Err(expected));
        }
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths()
            ),
            before
        );
    }

    #[test]
    fn declaration_method_metadata_only_cache_errors_are_invariants() {
        for source in [
            "interface Shape { run(): string; }",
            "declare const key: unique symbol; interface Shape { [key](): string; }",
        ] {
            let parsed = parse_source_file(source);
            let file = FileId::new(6_133);
            let (declaration, name) = declaration_method_nodes(&parsed, file)[0];
            for warm in [false, true] {
                for node in [declaration, name] {
                    let mut context = declaration_context(&parsed, file);
                    let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
                    if warm {
                        context.get_type_at_location(node).unwrap();
                    }
                    assert!(context.store_mut_for_test().set_type_node_links(
                        node,
                        TypeNodeLinks {
                            resolved_type: None,
                            outer_type_parameters: Some(Vec::new()),
                        }
                    ));
                    let before = (
                        context.store().type_len(),
                        context.store().signature_len(),
                        context.store().checker_link_allocated_lengths(),
                        context.store().relation_state_snapshot(),
                    );
                    assert_eq!(
                        context.get_type_at_location(node),
                        Err(CanonicalArtifactQueryError::InvalidSymbol { node, symbol })
                    );
                    assert_eq!(
                        (
                            context.store().type_len(),
                            context.store().signature_len(),
                            context.store().checker_link_allocated_lengths(),
                            context.store().relation_state_snapshot()
                        ),
                        before
                    );
                    assert!(context.diagnostics().is_empty());
                }
            }
        }
    }

    #[test]
    fn declaration_method_locations_keep_merged_overload_identity() {
        let parsed = parse_source_file(concat!(
            "interface Shape { run(value: number): number; } ",
            "interface Shape { run(value: string): string; }",
        ));
        let file = FileId::new(6_134);
        let mut context = declaration_context(&parsed, file);
        let locations = declaration_method_nodes(&parsed, file);
        let expected = context.get_type_at_location(locations[0].1).unwrap();
        let symbol = context.get_symbol_at_location(locations[0].1).unwrap();
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for (declaration, name) in locations {
            for node in [declaration, name] {
                assert_eq!(context.get_type_at_location(node), Ok(expected));
                assert_eq!(context.get_symbol_at_location(node), Ok(symbol));
            }
        }
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths()
            ),
            before
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn catch_rest_artifacts_require_the_bounded_recovery_context() {
        for text in [
            "try { const value = 1; } catch ({ ...rest }) {}",
            "try {} catch ({ value, ...rest }) {}",
            "try {} catch ({ ...rest }) { rest; }",
            "try {} catch ({ ...rest }) {} finally {}",
        ] {
            let parsed = parse_source_file(text);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(6_213);
            let (_, name) = catch_rest_nodes(&parsed, file);
            let mut context = context(&parsed, file);
            let before = context.store().checker_link_allocated_lengths();
            assert!(matches!(
                context.get_type_at_location(name),
                Err(CanonicalArtifactQueryError::SourceCheck(_)),
            ));
            assert_eq!(context.store().checker_link_allocated_lengths(), before);
            assert!(context.diagnostics().is_empty());
        }
        let parsed = parse_source_file("try {} catch ({ ...rest }) {}");
        let file = FileId::new(6_214);
        let (_, name) = catch_rest_nodes(&parsed, file);
        let mut context = declaration_context(&parsed, file);
        assert_eq!(
            context.get_type_at_location(name),
            Err(CanonicalArtifactQueryError::UnsupportedNode {
                node: name,
                kind: SyntaxKind::Identifier,
            }),
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn declaration_method_location_rejects_cold_and_warm_cache_changes() {
        for warm in [false, true] {
            for paired in [false, true] {
                let parsed = parse_source_file("interface Shape { run(): string; ignored(); }");
                let file = FileId::new(6_130);
                let mut context = declaration_context(&parsed, file);
                let (declaration, name) = parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        let NodeData::MethodSignatureDeclaration(method) = &record.data else {
                            return None;
                        };
                        let NodeData::Identifier(name) = &parsed.arena.get(method.name)?.data
                        else {
                            return None;
                        };
                        (name.text == "run").then_some((
                            NodeRef::new(parsed.arena.id(), file, node),
                            NodeRef::new(parsed.arena.id(), file, method.name),
                        ))
                    })
                    .unwrap();
                let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
                if warm {
                    context.get_type_at_location(name).unwrap();
                }
                let number = context.store().intrinsic_bootstrap().unwrap().number_type;
                assert!(context.store_mut_for_test().set_type_node_links(
                    name,
                    TypeNodeLinks {
                        resolved_type: Some(number),
                        ..TypeNodeLinks::default()
                    },
                ));
                if paired {
                    assert!(context.store_mut_for_test().set_value_symbol_links(
                        symbol,
                        ValueSymbolLinks {
                            resolved_type: Some(number),
                            ..ValueSymbolLinks::default()
                        },
                    ));
                }
                let before = (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                );
                assert!(context.get_type_at_location(name).is_err());
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().signature_len(),
                        context.store().checker_link_allocated_lengths(),
                    ),
                    before,
                );
                assert!(context.diagnostics().is_empty());
            }
        }
    }

    #[test]
    fn anonymous_arrow_and_object_symbols_remain_checker_private() {
        let parsed = parse_source_file(concat!(
            "const run = (value: number): number => value;\n",
            "const object = { value: 1 };\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_000);
        let mut context = context(&parsed, file);
        context.check_source_file(file).unwrap();
        let arrow = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(record.data, NodeData::ArrowFunction(_)).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let internal = context.file(file).unwrap().1.symbol(arrow).unwrap();

        assert_eq!(context.get_symbol_at_location(arrow).unwrap(), None);
        assert_eq!(context.file(file).unwrap().1.symbol(arrow), Some(internal));

        let object =
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(record.data, NodeData::ObjectLiteralExpression(_))
                        .then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
        let internal = context.file(file).unwrap().1.symbol(object).unwrap();
        assert_eq!(context.get_symbol_at_location(object).unwrap(), None);
        assert_eq!(context.file(file).unwrap().1.symbol(object), Some(internal));
    }

    #[test]
    fn arrow_location_queries_preserve_checked_callable_identity() {
        for (text, display) in [
            ("const value = () => 42;", "() => number"),
            (
                "const value = (input: number): number => input;",
                "(input: number) => number",
            ),
            (
                "const value = () => 42 satisfies typeof value;",
                "() => any",
            ),
        ] {
            let parsed = parse_source_file(text);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(6_040);
            let mut context = context_with_options(
                &parsed,
                file,
                CanonicalCheckerOptions {
                    no_implicit_any: true,
                    ..CanonicalCheckerOptions::default()
                },
            );
            let arrow = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(record.data, NodeData::ArrowFunction(_)).then_some(NodeRef::new(
                        parsed.arena.id(),
                        file,
                        node,
                    ))
                })
                .unwrap();
            let type_ = context.get_type_at_location(arrow).unwrap();
            assert_eq!(
                context.store().source_callable_type_for_declaration(arrow),
                Some(type_),
            );
            assert_eq!(context.type_to_string(type_).unwrap(), display);
            assert_eq!(context.get_symbol_at_location(arrow).unwrap(), None);
            let warm = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().len(),
            );
            assert_eq!(context.get_type_at_location(arrow), Ok(type_));
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().len(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn arrow_location_queries_reject_changed_callable_caches_without_writes() {
        for poison in [
            "node",
            "node_metadata",
            "owner",
            "declaration",
            "missing_declaration",
            "return",
        ] {
            let parsed = parse_source_file(if poison == "node_metadata" {
                concat!(
                    "const value = () => 42;\n",
                    "const other = (): string => 'value';\n",
                )
            } else {
                concat!(
                    "const value = () => 42 satisfies typeof value;\n",
                    "const other = (): string => 'value';\n",
                )
            });
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(6_041);
            let mut context = context(&parsed, file);
            context.check_source_file(file).unwrap();
            let arrows = parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    matches!(record.data, NodeData::ArrowFunction(_)).then_some(NodeRef::new(
                        parsed.arena.id(),
                        file,
                        node,
                    ))
                })
                .collect::<Vec<_>>();
            let arrow = arrows[0];
            let type_ = context.get_type_at_location(arrow).unwrap();
            let provenance = context.store().source_callable_provenance(type_).unwrap();
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            match poison {
                "node" => assert!(context.store_mut_for_test().set_type_node_links(
                    arrow,
                    TypeNodeLinks {
                        resolved_type: Some(number),
                        ..TypeNodeLinks::default()
                    },
                )),
                "node_metadata" => assert!(context.store_mut_for_test().set_type_node_links(
                    arrow,
                    TypeNodeLinks {
                        resolved_type: Some(type_),
                        outer_type_parameters: Some(vec![number]),
                    },
                )),
                "owner" => assert!(context.store_mut_for_test().set_value_symbol_links(
                    provenance.owner_symbol,
                    ValueSymbolLinks {
                        resolved_type: Some(number),
                        ..ValueSymbolLinks::default()
                    },
                )),
                "declaration" => {
                    let other = context.get_type_at_location(arrows[1]).unwrap();
                    assert_eq!(
                        context
                            .store_mut_for_test()
                            .replace_source_callable_type_for_declaration_for_test(
                                arrow,
                                Some(other),
                            ),
                        Some(type_),
                    );
                }
                "missing_declaration" => {
                    let other = context.get_type_at_location(arrows[1]).unwrap();
                    assert_eq!(
                        context
                            .store_mut_for_test()
                            .replace_source_callable_type_for_declaration_for_test(arrow, None),
                        Some(type_),
                    );
                    assert!(context.store_mut_for_test().set_type_node_links(
                        arrow,
                        TypeNodeLinks {
                            resolved_type: Some(other),
                            ..TypeNodeLinks::default()
                        },
                    ));
                }
                "return" => assert!(
                    context
                        .store_mut_for_test()
                        .set_signature_resolved_return_type(provenance.signature, Some(number))
                ),
                _ => unreachable!(),
            }
            let poisoned = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().len(),
            );
            assert!(
                matches!(
                    context.get_type_at_location(arrow),
                    Err(CanonicalArtifactQueryError::InvalidType { node, .. }) if node == arrow
                ),
                "{poison}",
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().len(),
                ),
                poisoned,
                "{poison}",
            );
        }
    }

    #[test]
    fn enum_declaration_queries_keep_declared_and_value_types_distinct() {
        for (source, has_reference) in [
            ("enum Kind {}", false),
            (
                "enum Kind { First = 1, Second = 2, Third = Kind.First }",
                true,
            ),
            ("declare namespace Names { enum Kind {} }", false),
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(6_068);
            let mut context = context(&parsed, file);
            let (declaration, name) = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::EnumDeclaration(enumeration) = &record.data else {
                        return None;
                    };
                    Some((
                        NodeRef::new(parsed.arena.id(), file, node),
                        NodeRef::new(parsed.arena.id(), file, enumeration.name),
                    ))
                })
                .unwrap();
            let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
            let declared = context.get_type_at_location(name).unwrap();
            assert_eq!(
                context
                    .store()
                    .declared_type_links(owner)
                    .unwrap()
                    .declared_type,
                Some(declared),
            );
            let value = context
                .store()
                .value_symbol_links(owner)
                .unwrap()
                .resolved_type
                .unwrap();
            assert_ne!(declared, value);
            let reference = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (node != name.node
                        && matches!(&record.data, NodeData::Identifier(identifier) if identifier.text == "Kind"))
                    .then_some(NodeRef::new(parsed.arena.id(), file, node))
                });
            assert_eq!(reference.is_some(), has_reference);
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            );
            for _ in 0..2 {
                assert_eq!(context.get_type_at_location(declaration), Ok(declared));
                assert_eq!(context.get_type_at_location(name), Ok(declared));
                assert_eq!(
                    context.type_of_artifact_symbol(name, owner),
                    Ok(Some(value))
                );
                if let Some(reference) = reference {
                    assert_eq!(context.get_type_at_location(reference), Ok(value));
                }
                assert_eq!(context.get_symbol_at_location(name), Ok(Some(owner)));
            }
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn enum_declaration_queries_reject_bad_caches_before_source_checking() {
        let parsed = parse_source_file("declare enum Kind { First = 1 }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_069);
        let (declaration, name) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::EnumDeclaration(enumeration) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, enumeration.name),
                ))
            })
            .unwrap();
        for declaration_file in [false, true] {
            for warm in [false, true] {
                for location in [declaration, name] {
                    for metadata_only in [false, true] {
                        let mut context = context_with_source_kind(
                            &parsed,
                            file,
                            CanonicalCheckerOptions::default(),
                            declaration_file,
                        );
                        let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
                        if warm {
                            context.get_type_at_location(name).unwrap();
                        }
                        let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
                        let links = TypeNodeLinks {
                            resolved_type: (!metadata_only).then_some(wrong),
                            outer_type_parameters: metadata_only.then(|| vec![wrong]),
                        };
                        assert!(
                            context
                                .store_mut_for_test()
                                .set_type_node_links(location, links.clone())
                        );
                        let source = context.source_file(file).unwrap();
                        let before = (
                            context.store().type_len(),
                            context.store().symbol_len(),
                            context.store().checker_link_allocated_lengths(),
                            context.store().source_file_links(source).cloned(),
                            context.diagnostics().len(),
                        );
                        for _ in 0..2 {
                            assert_eq!(
                                context.get_type_at_location(location),
                                Err(CanonicalArtifactQueryError::DeclaredType(
                                    crate::semantic::DeclaredTypeError::Enum(
                                        crate::semantic::enums::EnumTypeError::Invariant(
                                            crate::semantic::enums::EnumTypeInvariant::InvalidCache(
                                                owner
                                            ),
                                        ),
                                    ),
                                )),
                            );
                        }
                        assert_eq!(context.store().type_node_links(location), Some(&links));
                        assert_eq!(
                            (
                                context.store().type_len(),
                                context.store().symbol_len(),
                                context.store().checker_link_allocated_lengths(),
                                context.store().source_file_links(source).cloned(),
                                context.diagnostics().len(),
                            ),
                            before,
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn enum_declaration_queries_reject_unrelated_merge_redirects() {
        let parsed = parse_source_file("declare enum First {} declare enum Second { Value = 1 }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_070);
        let declarations = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::EnumDeclaration(enumeration) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, enumeration.name),
                ))
            })
            .collect::<Vec<_>>();
        let [(first, first_name), (second, second_name)] = declarations.as_slice() else {
            panic!("expected two enum declarations");
        };
        for declaration_file in [false, true] {
            for warm in [false, true] {
                let mut context = context_with_source_kind(
                    &parsed,
                    file,
                    CanonicalCheckerOptions::default(),
                    declaration_file,
                );
                let first_owner = context.file(file).unwrap().1.symbol(*first).unwrap();
                let second_owner = context.file(file).unwrap().1.symbol(*second).unwrap();
                if warm {
                    context.get_type_at_location(*first_name).unwrap();
                    context.get_type_at_location(*second_name).unwrap();
                }
                context
                    .store_mut_for_test()
                    .record_merged_symbol(second_owner, first_owner)
                    .unwrap();
                let source = context.source_file(file).unwrap();
                let before = (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.store().source_file_links(source).cloned(),
                    context.store().declared_type_links(second_owner).cloned(),
                    context.diagnostics().len(),
                );
                for node in [*first, *first_name] {
                    assert_eq!(
                        context.get_type_at_location(node),
                        Err(CanonicalArtifactQueryError::InvalidSymbol {
                            node,
                            symbol: second_owner,
                        }),
                    );
                }
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().symbol_len(),
                        context.store().checker_link_allocated_lengths(),
                        context.store().source_file_links(source).cloned(),
                        context.store().declared_type_links(second_owner).cloned(),
                        context.diagnostics().len(),
                    ),
                    before,
                );
            }
        }
    }

    #[test]
    fn enum_declaration_queries_reject_changed_dispatch_flags() {
        let parsed = parse_source_file("declare enum Kind { First = 1 }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_071);
        let (declaration, name) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::EnumDeclaration(enumeration) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, enumeration.name),
                ))
            })
            .unwrap();
        for flags in [
            SymbolFlags::PROPERTY,
            SymbolFlags::TYPE_ALIAS,
            SymbolFlags::REGULAR_ENUM | SymbolFlags::INTERFACE,
        ] {
            for warm in [false, true] {
                let mut context = declaration_context(&parsed, file);
                let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
                if warm {
                    context.get_type_at_location(name).unwrap();
                }
                assert!(context.store_mut_for_test().set_symbol_flags(
                    owner,
                    flags,
                    CheckFlags::NONE,
                ));
                let before = (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().len(),
                );
                for location in [declaration, name] {
                    assert_eq!(
                        context.get_type_at_location(location),
                        Err(CanonicalArtifactQueryError::DeclaredType(
                            crate::semantic::DeclaredTypeError::Enum(
                                crate::semantic::enums::EnumTypeError::Invariant(
                                    crate::semantic::enums::EnumTypeInvariant::InvalidOwnerSymbol(
                                        owner
                                    ),
                                ),
                            ),
                        )),
                    );
                }
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().symbol_len(),
                        context.store().checker_link_allocated_lengths(),
                        context.diagnostics().len(),
                    ),
                    before,
                );
            }
        }
    }

    #[test]
    fn enum_declaration_queries_reject_chained_owner_redirects() {
        let parsed = parse_source_file(concat!(
            "declare enum First {} declare enum Bridge {} ",
            "declare enum Last { Value = 1 }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_072);
        for warm in [false, true] {
            let mut context = declaration_context(&parsed, file);
            let owners = parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    let NodeData::EnumDeclaration(enumeration) = &record.data else {
                        return None;
                    };
                    let declaration = NodeRef::new(parsed.arena.id(), file, node);
                    Some((
                        declaration,
                        NodeRef::new(parsed.arena.id(), file, enumeration.name),
                        context.file(file).unwrap().1.symbol(declaration).unwrap(),
                    ))
                })
                .collect::<Vec<_>>();
            let [first, bridge, last] = owners.as_slice() else {
                panic!("expected three enum declarations");
            };
            if warm {
                for (_, name, _) in &owners {
                    context.get_type_at_location(*name).unwrap();
                }
            }
            assert!(context.store_mut_for_test().set_symbol_declarations(
                bridge.2,
                Some(vec![first.0]),
                Some(first.0),
            ));
            context
                .store_mut_for_test()
                .record_merged_symbol(bridge.2, first.2)
                .unwrap();
            context
                .store_mut_for_test()
                .record_merged_symbol(last.2, bridge.2)
                .unwrap();
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().declared_type_links(last.2).cloned(),
                context.diagnostics().len(),
            );
            for node in [first.0, first.1] {
                assert_eq!(
                    context.get_type_at_location(node),
                    Err(CanonicalArtifactQueryError::InvalidSymbol {
                        node,
                        symbol: bridge.2,
                    }),
                );
            }
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.store().declared_type_links(last.2).cloned(),
                    context.diagnostics().len(),
                ),
                before,
            );
        }
    }

    #[test]
    fn class_declaration_queries_preserve_instance_identity_and_reject_forged_caches() {
        let parsed = parse_source_file("class Model {} const constructor = Model;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_028);
        let mut context = context(&parsed, file);
        context.check_source_file(file).unwrap();
        let (declaration, name) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ClassDeclaration(class) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, class.name.unwrap()),
                ))
            })
            .unwrap();
        let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
        let instance = context
            .store()
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            .unwrap();
        let warm = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );

        assert_eq!(context.get_type_at_location(declaration), Ok(instance));
        assert_eq!(context.get_type_at_location(name), Ok(instance));
        assert_eq!(context.type_to_string(instance).unwrap(), "Model");
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm,
        );

        let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_type_node_links(
            name,
            TypeNodeLinks {
                resolved_type: Some(wrong),
                ..TypeNodeLinks::default()
            },
        ));
        assert_eq!(
            context.get_type_at_location(name),
            Err(CanonicalArtifactQueryError::InvalidType {
                node: name,
                type_: wrong,
            }),
        );
        assert_eq!(context.get_type_at_location(declaration), Ok(instance));
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep source value publication and both declaration cache states together.
    fn interface_declaration_queries_keep_instance_and_value_types_separate() {
        let library =
            parse_source_file("interface Packet { original: string; } declare var Packet: number;");
        let augmentation = parse_source_file("interface Packet {}");
        let consumer = parse_source_file("const observed: number = Packet;");
        let library_file = FileId::new(147_201);
        let augmentation_file = FileId::new(147_202);
        let consumer_file = FileId::new(147_203);
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, declaration, default_library) in [
            (library_file, &library, "\"/lib/packet.d.ts\"", true, true),
            (
                augmentation_file,
                &augmentation,
                "\"/project/packet.d.ts\"",
                true,
                false,
            ),
            (
                consumer_file,
                &consumer,
                "\"/project/consumer.ts\"",
                false,
                false,
            ),
        ] {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        declaration,
                        default_library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![
                (library_file, &library.arena),
                (augmentation_file, &augmentation.arena),
                (consumer_file, &consumer.arena),
            ],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let mut locations = Vec::new();
        for (file, parsed) in [(library_file, &library), (augmentation_file, &augmentation)] {
            for (node, record) in parsed.arena.iter() {
                if let NodeData::InterfaceDeclaration(interface) = &record.data {
                    locations.extend([
                        NodeRef::new(parsed.arena.id(), file, node),
                        NodeRef::new(parsed.arena.id(), file, interface.name),
                    ]);
                }
            }
        }
        assert_eq!(locations.len(), 4);
        let raw_owner = context
            .file(library_file)
            .unwrap()
            .1
            .symbol(locations[0])
            .unwrap();
        let owner = context.store().get_merged_symbol(raw_owner).unwrap();
        let (value_name, annotation) = library
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(library.arena.id(), library_file, variable.name),
                    NodeRef::new(library.arena.id(), library_file, variable.type_.unwrap()),
                ))
            })
            .unwrap();
        let value_read = consumer
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(
                    consumer.arena.id(),
                    consumer_file,
                    variable.initializer.unwrap(),
                ))
            })
            .unwrap();
        let source = context.source_file(consumer_file).unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let instance = context.get_declared_type_of_symbol(owner).unwrap();
        assert_ne!(instance, number);
        assert!(context.store().value_symbol_links(owner).is_none());
        assert!(context.store().type_node_links(annotation).is_none());
        let state = |context: &CanonicalCheckerContext<'_>| {
            let store = context.store();
            let TypeData::Interface(data) = store.type_payload(instance).unwrap().data() else {
                panic!("the declaration must keep its interface type");
            };
            (
                [
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                    store.symbol_store().symbol_table_len(),
                ],
                store.checker_link_allocated_lengths().to_vec(),
                data.clone(),
                store.declared_type_links(owner).cloned(),
                store.value_symbol_links(owner).cloned(),
                locations
                    .iter()
                    .copied()
                    .chain([value_name, annotation, value_read])
                    .map(|node| {
                        (
                            node,
                            store.type_node_links(node).cloned(),
                            store.symbol_node_links(node).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                store.source_file_links(source).cloned(),
                context.diagnostics().clone(),
            )
        };
        for publish_value in [false, true] {
            if publish_value {
                context.check_source_file(consumer_file).unwrap();
                assert_eq!(
                    context
                        .store()
                        .value_symbol_links(owner)
                        .and_then(|links| links.resolved_type),
                    Some(number),
                );
                for node in [value_name, value_read] {
                    assert_eq!(context.get_type_at_location(node), Ok(number));
                }
            }
            let warm = state(&context);
            for _ in 0..2 {
                for &node in &locations {
                    assert_eq!(context.get_type_at_location(node), Ok(instance));
                    assert_eq!(context.get_symbol_at_location(node), Ok(Some(owner)));
                }
                assert_eq!(state(&context), warm);
            }
            if !publish_value {
                assert!(context.store().value_symbol_links(owner).is_none());
                assert!(context.store().type_node_links(annotation).is_none());
            }
            for &node in &locations {
                let original = context
                    .store()
                    .type_node_links(node)
                    .cloned()
                    .unwrap_or_default();
                assert!(context.store_mut_for_test().set_type_node_links(
                    node,
                    TypeNodeLinks {
                        resolved_type: Some(number),
                        ..TypeNodeLinks::default()
                    },
                ));
                let damaged = state(&context);
                for _ in 0..2 {
                    assert_eq!(
                        context.get_type_at_location(node),
                        Err(CanonicalArtifactQueryError::InvalidType {
                            node,
                            type_: number,
                        }),
                    );
                    assert_eq!(state(&context), damaged);
                }
                assert!(
                    context
                        .store_mut_for_test()
                        .set_type_node_links(node, original)
                );
                assert_eq!(context.get_type_at_location(node), Ok(instance));
            }
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn interface_declaration_queries_keep_merged_class_cache_proof() {
        for source in [
            "declare class Packet {} interface Packet {}",
            "interface Packet {} declare class Packet {}",
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(147_204);
            let mut context = declaration_context(&parsed, file);
            let locations = parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    let name = match &record.data {
                        NodeData::ClassDeclaration(class) => class.name.unwrap(),
                        NodeData::InterfaceDeclaration(interface) => interface.name,
                        _ => return None,
                    };
                    Some([
                        NodeRef::new(parsed.arena.id(), file, node),
                        NodeRef::new(parsed.arena.id(), file, name),
                    ])
                })
                .flatten()
                .collect::<Vec<_>>();
            assert_eq!(locations.len(), 4);
            let raw_owner = context.file(file).unwrap().1.symbol(locations[0]).unwrap();
            let owner = context.store().get_merged_symbol(raw_owner).unwrap();
            let instance = context.get_declared_type_of_symbol(owner).unwrap();
            assert!(
                context
                    .store()
                    .type_payload(instance)
                    .unwrap()
                    .object_flags()
                    .contains(ObjectFlags::CLASS)
            );
            for &node in &locations {
                assert_eq!(context.get_type_at_location(node), Ok(instance));
                assert_eq!(context.get_symbol_at_location(node), Ok(Some(owner)));
                assert!(context.store_mut_for_test().set_type_node_links(
                    node,
                    TypeNodeLinks {
                        resolved_type: Some(instance),
                        ..TypeNodeLinks::default()
                    },
                ));
            }
            let state = |context: &CanonicalCheckerContext<'_>| {
                let store = context.store();
                (
                    [store.type_len(), store.symbol_len(), store.signature_len()],
                    store.checker_link_allocated_lengths().to_vec(),
                    store.declared_type_links(owner).cloned(),
                    store.value_symbol_links(owner).cloned(),
                    locations
                        .iter()
                        .map(|node| store.type_node_links(*node).cloned())
                        .collect::<Vec<_>>(),
                    context.diagnostics().clone(),
                )
            };
            let warm = state(&context);
            for _ in 0..2 {
                for &node in &locations {
                    assert_eq!(context.get_type_at_location(node), Ok(instance));
                }
                assert_eq!(state(&context), warm);
            }
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn interface_declaration_queries_reject_redirected_symbol_owners() {
        let parsed = parse_source_file("interface Packet {} interface Other {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(147_205);
        let declarations = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::InterfaceDeclaration(interface) = &record.data else {
                    return None;
                };
                Some([
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, interface.name),
                ])
            })
            .collect::<Vec<_>>();
        let [packet, other] = declarations.as_slice() else {
            panic!("expected two interface declarations");
        };
        for warm in [false, true] {
            let mut context = declaration_context(&parsed, file);
            let bound = context.file(file).unwrap().1;
            let packet_symbol = bound.symbol(packet[0]).unwrap();
            let other_symbol = bound.symbol(other[0]).unwrap();
            if warm {
                for node in packet.iter().chain(other) {
                    context.get_type_at_location(*node).unwrap();
                }
            }
            context
                .store_mut_for_test()
                .record_merged_symbol(other_symbol, packet_symbol)
                .unwrap();
            assert_eq!(
                context.store().get_merged_symbol(packet_symbol),
                Some(other_symbol),
            );
            let state = |context: &CanonicalCheckerContext<'_>| {
                let store = context.store();
                (
                    [store.type_len(), store.symbol_len(), store.signature_len()],
                    store.checker_link_allocated_lengths().to_vec(),
                    [packet_symbol, other_symbol]
                        .map(|symbol| store.declared_type_links(symbol).cloned()),
                    packet
                        .iter()
                        .chain(other)
                        .map(|node| {
                            (
                                store.type_node_links(*node).cloned(),
                                store.symbol_node_links(*node).cloned(),
                            )
                        })
                        .collect::<Vec<_>>(),
                    context.diagnostics().clone(),
                )
            };
            let damaged = state(&context);
            for _ in 0..2 {
                for &node in packet {
                    assert_eq!(
                        context.get_type_at_location(node),
                        Err(CanonicalArtifactQueryError::InvalidSymbol {
                            node,
                            symbol: other_symbol,
                        }),
                    );
                    assert_eq!(state(&context), damaged);
                }
            }
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Preserve the class-origin error for both cached declaration locations.
    fn class_declaration_queries_reject_cached_interface_redirects() {
        let parsed = parse_source_file("declare class Model {} interface Other {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(147_206);
        let mut context = declaration_context(&parsed, file);
        let (declaration, name) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ClassDeclaration(class) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, class.name.unwrap()),
                ))
            })
            .unwrap();
        let other =
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(record.data, NodeData::InterfaceDeclaration(_))
                        .then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
        let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
        let other_owner = context.file(file).unwrap().1.symbol(other).unwrap();
        let instance = context.get_type_at_location(declaration).unwrap();
        let other_type = context.get_type_at_location(other).unwrap();
        assert_ne!(instance, other_type);
        assert!(
            context
                .store()
                .symbol(other_owner)
                .unwrap()
                .flags()
                .contains(SymbolFlags::INTERFACE)
        );
        assert!(
            !context
                .store()
                .symbol(other_owner)
                .unwrap()
                .flags()
                .contains(SymbolFlags::CLASS)
        );
        context
            .store_mut_for_test()
            .record_merged_symbol(other_owner, owner)
            .unwrap();
        assert_eq!(context.store().get_merged_symbol(owner), Some(other_owner));
        for node in [declaration, name] {
            assert!(context.store_mut_for_test().set_type_node_links(
                node,
                TypeNodeLinks {
                    resolved_type: Some(other_type),
                    ..TypeNodeLinks::default()
                },
            ));
        }
        let source = context.source_file(file).unwrap();
        let state = |context: &CanonicalCheckerContext<'_>| {
            let store = context.store();
            (
                [
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                ],
                store.checker_link_allocated_lengths().to_vec(),
                [owner, other_owner].map(|symbol| {
                    (
                        store.declared_type_links(symbol).cloned(),
                        store.value_symbol_links(symbol).cloned(),
                    )
                }),
                [declaration, name, other].map(|node| {
                    (
                        store.type_node_links(node).cloned(),
                        store.symbol_node_links(node).cloned(),
                    )
                }),
                store.source_file_links(source).cloned(),
                context.diagnostics().clone(),
            )
        };
        let damaged = state(&context);
        for _ in 0..2 {
            for node in [declaration, name] {
                assert_eq!(
                    context.get_type_at_location(node),
                    Err(CanonicalArtifactQueryError::DeclaredType(
                        crate::semantic::DeclaredTypeError::Unavailable(
                            crate::semantic::DeclaredTypeUnavailable::InvalidCachedDeclaredType {
                                symbol: other_owner,
                                declared_type: other_type,
                            },
                        ),
                    )),
                );
                assert_eq!(state(&context), damaged);
            }
        }
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn cold_class_query_cache_failures_do_not_check_sources_or_allocate_types() {
        let parsed = parse_source_file("class Model {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_034);
        let (declaration, name) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ClassDeclaration(class) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, class.name.unwrap()),
                ))
            })
            .unwrap();
        for declaration_file in [false, true] {
            for poisoned in [declaration, name] {
                let mut context = context_with_source_kind(
                    &parsed,
                    file,
                    CanonicalCheckerOptions::default(),
                    declaration_file,
                );
                let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
                let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
                assert!(context.store_mut_for_test().set_type_node_links(
                    poisoned,
                    TypeNodeLinks {
                        resolved_type: Some(wrong),
                        ..TypeNodeLinks::default()
                    },
                ));
                let source = context.source_file(file).unwrap();
                let before = (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.store().source_file_links(source).cloned(),
                    context.store().declared_type_links(owner).cloned(),
                    context.diagnostics().len(),
                );
                assert_eq!(
                    context.get_type_at_location(poisoned),
                    Err(CanonicalArtifactQueryError::InvalidType {
                        node: poisoned,
                        type_: wrong,
                    }),
                );
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().symbol_len(),
                        context.store().signature_len(),
                        context.store().checker_link_allocated_lengths(),
                        context.store().source_file_links(source).cloned(),
                        context.store().declared_type_links(owner).cloned(),
                        context.diagnostics().len(),
                    ),
                    before,
                );
                assert!(
                    context
                        .store_mut_for_test()
                        .set_type_node_links(poisoned, TypeNodeLinks::default()),
                );
                let instance = context.get_type_at_location(name).unwrap();
                assert_eq!(context.type_to_string(instance).unwrap(), "Model");
                assert_eq!(context.get_type_at_location(declaration), Ok(instance));
            }
        }
    }

    #[test]
    fn checked_conditional_literal_queries_reuse_pairs_without_child_links() {
        for strict_null_checks in [false, true] {
            for (expression, expected) in [
                ("true ? 'left' : 'right'", ["true", "\"left\"", "\"right\""]),
                ("true ? `left` : `right`", ["true", "\"left\"", "\"right\""]),
                ("true ? 1_000 : 2", ["true", "1000", "2"]),
                ("true ? 1n : 2n", ["true", "1n", "2n"]),
                ("true ? true : false", ["true", "true", "false"]),
                ("true ? null : null", ["true", "null", "null"]),
            ] {
                let parsed = parse_source_file(&format!("const value = {expression};"));
                assert!(parsed.diagnostics.is_empty(), "{expression}");
                let file = FileId::new(6_126);
                let mut context = context_with_options(
                    &parsed,
                    file,
                    CanonicalCheckerOptions {
                        intrinsic: IntrinsicBootstrapOptions {
                            strict_null_checks,
                            ..IntrinsicBootstrapOptions::default()
                        },
                        ..CanonicalCheckerOptions::default()
                    },
                );
                context.check_source_file(file).unwrap();
                let children = parsed
                    .arena
                    .iter()
                    .find_map(|(_, record)| {
                        let NodeData::ConditionalExpression(conditional) = &record.data else {
                            return None;
                        };
                        Some(
                            [
                                conditional.condition,
                                conditional.when_true,
                                conditional.when_false,
                            ]
                            .map(|node| NodeRef::new(parsed.arena.id(), file, node)),
                        )
                    })
                    .unwrap();
                let source = context.source_file(file).unwrap();
                let state = |context: &CanonicalCheckerContext<'_>| {
                    let store = context.store();
                    (
                        [
                            store.type_len(),
                            store.symbol_len(),
                            store.signature_len(),
                            store.mapper_len(),
                            store.symbol_store().symbol_table_len(),
                            context.diagnostics().len(),
                        ],
                        store.checker_link_allocated_lengths(),
                        store.source_file_links(source).cloned(),
                        store.relation_state_snapshot(),
                    )
                };
                let before = state(&context);
                for _ in 0..2 {
                    for (node, expected) in children.into_iter().zip(expected) {
                        assert!(context.store().type_node_links(node).is_none());
                        assert!(context.store().symbol_node_links(node).is_none());
                        let type_ = context.get_type_at_location(node).unwrap();
                        assert_eq!(context.type_to_string(type_).unwrap(), expected);
                        if expected == "null" {
                            assert_eq!(
                                type_,
                                context
                                    .store()
                                    .intrinsic_bootstrap()
                                    .unwrap()
                                    .null_widening_type,
                            );
                        } else {
                            let TypeData::Literal(literal) =
                                context.store().type_payload(type_).unwrap().data()
                            else {
                                panic!("the conditional child must keep its literal type")
                            };
                            assert_eq!(literal.fresh_type, Some(type_));
                            assert_ne!(literal.regular_type, type_);
                        }
                        assert_eq!(context.get_symbol_at_location(node), Ok(None));
                        assert!(context.store().type_node_links(node).is_none());
                        assert!(context.store().symbol_node_links(node).is_none());
                    }
                    assert_eq!(state(&context), before, "{expression}");
                }
            }
        }
    }

    #[test]
    fn conditional_literal_readback_requires_a_checked_owner() {
        let parsed = parse_source_file("const value = true ? 'left' : 'right';");
        let file = FileId::new(6_127);
        let mut context = context(&parsed, file);
        let node = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::ConditionalExpression(conditional) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(parsed.arena.id(), file, conditional.when_true))
            })
            .unwrap();
        context
            .store_mut_for_test()
            .regular_string_literal_type("left".to_owned())
            .unwrap();
        let source = context.source_file(file).unwrap();
        let state = |context: &CanonicalCheckerContext<'_>| {
            let store = context.store();
            (
                [store.type_len(), store.symbol_len(), store.signature_len()],
                store.checker_link_allocated_lengths(),
                store.source_file_links(source).cloned(),
                context.diagnostics().len(),
            )
        };
        let before = state(&context);
        for _ in 0..2 {
            assert_eq!(
                context.checked_conditional_literal_artifact_type(node),
                Ok(None)
            );
            assert_eq!(state(&context), before);
            assert!(context.store().type_node_links(node).is_none());
        }
    }

    #[test]
    fn checked_conditional_literal_queries_reject_missing_or_conflicting_caches() {
        for poison in 0..4 {
            let parsed = parse_source_file("const value = true ? 'left' : 'right';");
            let file = FileId::new(6_128);
            let mut context = context(&parsed, file);
            context.check_source_file(file).unwrap();
            let (parent, node) = parsed
                .arena
                .iter()
                .find_map(|(id, record)| {
                    let NodeData::ConditionalExpression(conditional) = &record.data else {
                        return None;
                    };
                    Some((
                        NodeRef::new(parsed.arena.id(), file, id),
                        NodeRef::new(parsed.arena.id(), file, conditional.when_true),
                    ))
                })
                .unwrap();
            let regular_wrong = context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .cached_string_literal_type("right")
                .unwrap();
            let wrong = context
                .store()
                .fresh_type_of_literal_type(regular_wrong)
                .unwrap();
            let expected = context.get_type_at_location(node).unwrap();
            let symbol = context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .unknown_symbol;
            let error = match poison {
                0 => {
                    assert!(
                        context
                            .store_mut_for_test()
                            .set_type_node_links(parent, TypeNodeLinks::default())
                    );
                    CanonicalArtifactQueryError::MissingType {
                        node: parent,
                        kind: SyntaxKind::ConditionalExpression,
                    }
                }
                1 | 2 => {
                    assert!(context.store_mut_for_test().set_type_node_links(
                        node,
                        TypeNodeLinks {
                            resolved_type: (poison == 1).then_some(wrong),
                            outer_type_parameters: (poison == 2).then(Vec::new),
                        },
                    ));
                    CanonicalArtifactQueryError::InvalidType {
                        node,
                        type_: if poison == 1 { wrong } else { expected },
                    }
                }
                3 => {
                    assert!(context.store_mut_for_test().set_symbol_node_links(
                        node,
                        SymbolNodeLinks {
                            resolved_symbol: Some(symbol)
                        },
                    ));
                    CanonicalArtifactQueryError::InvalidSymbol { node, symbol }
                }
                _ => unreachable!(),
            };
            let source = context.source_file(file).unwrap();
            let state = |context: &CanonicalCheckerContext<'_>| {
                let store = context.store();
                (
                    [
                        store.type_len(),
                        store.symbol_len(),
                        store.signature_len(),
                        store.mapper_len(),
                        store.symbol_store().symbol_table_len(),
                        context.diagnostics().len(),
                    ],
                    store.checker_link_allocated_lengths(),
                    store.source_file_links(source).cloned(),
                    store.relation_state_snapshot(),
                    [parent, node].map(|node| store.type_node_links(node).cloned()),
                    store.symbol_node_links(node).cloned(),
                )
            };
            let before = state(&context);
            for _ in 0..2 {
                assert_eq!(
                    context.get_type_at_location(node),
                    Err(error),
                    "poison {poison}"
                );
                assert_eq!(state(&context), before, "poison {poison}");
            }
        }
    }

    #[test]
    fn literal_annotation_queries_reject_conflicting_caches_without_writes() {
        for source in [
            "interface Shape { value: true; }",
            "interface Shape { value: 'ready'; }",
            "interface Shape { value: 42; }",
            "interface Shape { value: -2; }",
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(6_029);
            let (annotation, literal) = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::LiteralTypeNode(literal) = &record.data else {
                        return None;
                    };
                    Some((
                        NodeRef::new(parsed.arena.id(), file, node),
                        NodeRef::new(parsed.arena.id(), file, literal.literal),
                    ))
                })
                .unwrap();

            for poisoned in [literal, annotation] {
                let mut context = declaration_context(&parsed, file);
                let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
                let links = TypeNodeLinks {
                    resolved_type: Some(wrong),
                    ..TypeNodeLinks::default()
                };
                assert!(
                    context
                        .store_mut_for_test()
                        .set_type_node_links(poisoned, links.clone()),
                );
                let before = (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().len(),
                );
                assert_eq!(
                    context.get_type_at_location(literal),
                    Err(CanonicalArtifactQueryError::InvalidType {
                        node: poisoned,
                        type_: wrong,
                    }),
                );
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().symbol_len(),
                        context.store().signature_len(),
                        context.store().checker_link_allocated_lengths(),
                        context.diagnostics().len(),
                    ),
                    before,
                );
                assert_eq!(context.store().type_node_links(poisoned), Some(&links));
                assert!(
                    context
                        .store_mut_for_test()
                        .set_type_node_links(poisoned, TypeNodeLinks::default()),
                );
                let resolved = context.get_type_at_location(literal).unwrap();
                assert_ne!(resolved, wrong);
                assert_eq!(context.get_type_from_type_node(annotation), Ok(resolved));
            }
        }
    }

    #[test]
    fn literal_wrappers_reject_same_store_substitution_before_resolving_the_source() {
        let parsed = parse_source_file("interface Shape { first: 'ready'; second: 'wrong'; }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_031);
        let mut context = context(&parsed, file);
        let annotations = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                matches!(record.data, NodeData::LiteralTypeNode(_)).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .collect::<Vec<_>>();
        let [first, second] = annotations.as_slice() else {
            panic!("expected two literal annotations")
        };
        let wrong = context.get_type_from_type_node(*second).unwrap();
        assert!(context.store_mut_for_test().set_type_node_links(
            *first,
            TypeNodeLinks {
                resolved_type: Some(wrong),
                ..TypeNodeLinks::default()
            },
        ));
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
            context
                .store()
                .source_file_links(context.source_file(file).unwrap())
                .cloned(),
            context.diagnostics().len(),
        );
        assert_eq!(
            context.get_type_at_location(*first),
            Err(CanonicalArtifactQueryError::InvalidType {
                node: *first,
                type_: wrong,
            }),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context
                    .store()
                    .source_file_links(context.source_file(file).unwrap())
                    .cloned(),
                context.diagnostics().len(),
            ),
            before,
        );
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(*first, TypeNodeLinks::default()),
        );
        let ready = context.get_type_at_location(*first).unwrap();
        assert_ne!(ready, wrong);
        assert_eq!(context.type_to_string(ready).unwrap(), "\"ready\"");
    }

    #[test]
    fn negative_literal_operand_cache_failures_leave_cold_annotations_unchanged() {
        for source in [
            "interface Negative { value: -2; }",
            "interface Negative { value: -23n; }",
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(6_033);
            let mut context = context(&parsed, file);
            let source_node = context.source_file(file).unwrap();
            let operand = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::PrefixUnaryExpression(prefix) = &record.data else {
                        return None;
                    };
                    Some(NodeRef::new(parsed.arena.id(), file, prefix.operand))
                })
                .unwrap();
            let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
            assert!(context.store_mut_for_test().set_type_node_links(
                operand,
                TypeNodeLinks {
                    resolved_type: Some(wrong),
                    ..TypeNodeLinks::default()
                },
            ));
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().source_file_links(source_node).cloned(),
                context.diagnostics().len(),
            );
            assert_eq!(
                context.get_type_at_location(operand),
                Err(CanonicalArtifactQueryError::InvalidType {
                    node: operand,
                    type_: wrong,
                }),
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.store().source_file_links(source_node).cloned(),
                    context.diagnostics().len(),
                ),
                before,
            );
            assert!(
                context
                    .store_mut_for_test()
                    .set_type_node_links(operand, TypeNodeLinks::default()),
            );
            assert!(context.get_type_at_location(operand).is_ok());
        }
    }

    #[test]
    fn unsupported_type_locations_do_not_adopt_same_store_caches() {
        let parsed = parse_source_file("interface Shape { value: string; }");
        let file = FileId::new(6_032);
        let mut context = context(&parsed, file);
        let source = NodeRef::new(parsed.arena.id(), file, parsed.source_file);
        let source_file = context.source_file(file).unwrap();
        let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_type_node_links(
            source,
            TypeNodeLinks {
                resolved_type: Some(wrong),
                ..TypeNodeLinks::default()
            },
        ));
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
            context.store().source_file_links(source_file).cloned(),
            context.diagnostics().len(),
        );
        assert_eq!(
            context.get_type_at_location(source),
            Err(CanonicalArtifactQueryError::UnsupportedNode {
                node: source,
                kind: SyntaxKind::SourceFile,
            }),
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().source_file_links(source_file).cloned(),
                context.diagnostics().len(),
            ),
            before,
        );
        assert_eq!(
            context
                .store()
                .type_node_links(source)
                .and_then(|links| links.resolved_type),
            Some(wrong),
        );
    }

    #[test]
    fn expando_symbol_queries_reject_conflicting_reference_caches_without_writes() {
        let parsed = parse_source_file("function foo() {} foo.bar = 42;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_030);
        let (expression, access, name, receiver) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::BinaryExpression(binary) = &record.data else {
                    return None;
                };
                let NodeData::PropertyAccessExpression(access) =
                    &parsed.arena.get(binary.left)?.data
                else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, binary.left),
                    NodeRef::new(parsed.arena.id(), file, access.name),
                    NodeRef::new(parsed.arena.id(), file, access.expression),
                ))
            })
            .unwrap();

        for poisoned in [access, name, receiver] {
            let mut context = context(&parsed, file);
            context.check_source_file(file).unwrap();
            let property = context.file(file).unwrap().1.symbol(expression).unwrap();
            let saved = context
                .store()
                .symbol_node_links(poisoned)
                .cloned()
                .unwrap_or_default();
            let wrong = context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .unknown_symbol;
            assert!(context.store_mut_for_test().set_symbol_node_links(
                poisoned,
                SymbolNodeLinks {
                    resolved_symbol: Some(wrong),
                },
            ));
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().len(),
            );
            let query = if poisoned == name { name } else { access };
            assert!(context.get_symbol_at_location(query).is_err());
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().len(),
                ),
                before,
            );
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(poisoned)
                    .and_then(|links| links.resolved_symbol),
                Some(wrong),
            );
            assert!(
                context
                    .store_mut_for_test()
                    .set_symbol_node_links(poisoned, saved),
            );
            assert_eq!(context.get_symbol_at_location(query), Ok(Some(property)));
        }
    }

    #[test]
    fn class_and_interface_member_names_include_their_owner() {
        let parsed = parse_source_file(concat!(
            "interface Shape { item: string; }\n",
            "class Model { value!: number; }\n",
            "const object = { value: 1 };\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_001);
        let mut context = context(&parsed, file);
        context.check_source_file(file).unwrap();

        let mut names = Vec::new();
        for (node, record) in parsed.arena.iter() {
            if !matches!(
                record.data,
                NodeData::PropertyDeclaration(_) | NodeData::PropertyAssignment(_)
            ) {
                continue;
            }
            let declaration = NodeRef::new(parsed.arena.id(), file, node);
            let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
            names.push(context.symbol_to_string(symbol).unwrap());
        }

        assert_eq!(names, ["Shape.item", "Model.value", "value"]);
    }

    #[test]
    fn private_member_artifacts_use_source_spelling_without_changing_identity() {
        let parsed = parse_source_file("class First { #value = 1; } class Second { #value = 2; }");
        let file = FileId::new(6_116);
        let mut context = context(&parsed, file);
        context.check_source_file(file).unwrap();
        let members = parsed
            .arena
            .iter()
            .filter_map(|(id, record)| {
                let NodeData::PropertyDeclaration(property) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, id),
                    NodeRef::new(parsed.arena.id(), file, property.name),
                ))
            })
            .collect::<Vec<_>>();
        assert_eq!(members.len(), 2);
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for ((declaration, name), expected) in
            members.into_iter().zip(["First.#value", "Second.#value"])
        {
            let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
            let encoded = context.store().symbol(symbol).unwrap().name().to_owned();
            assert!(encoded.as_ref().is_private_identifier());
            for _ in 0..2 {
                assert_eq!(context.symbol_to_string(symbol).unwrap(), expected);
                assert_eq!(
                    context.symbol_to_string_at_location(symbol, name).unwrap(),
                    expected
                );
            }
            assert_eq!(
                context.store().symbol(symbol).unwrap().name(),
                encoded.as_ref()
            );
        }
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths()
            ),
            before
        );
    }

    #[test]
    fn private_member_artifacts_accept_class_namespace_owners_cold_and_warm() {
        for source in [
            "class Model { #value = 1; } namespace Model {}",
            "class Model { static #value = 1; } namespace Model {}",
            "class Model { #value = 1; } namespace Model { export var tag = 2; }",
            "class Model { static #value = 1; } namespace Model { export var tag = 2; }",
            "class Model<First = any, Second = First> { #value = 1; } namespace Model {}",
            concat!(
                "class Model<First = any, Second = First> { #value = 1; } ",
                "namespace Model { export var tag = 2; }",
            ),
            "class Model { #run() {} } namespace Model {}",
            concat!(
                "class Model { get #value(): number { return 1; } set #value(next) {} } ",
                "namespace Model { export var tag = 2; }",
            ),
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{source}");
            let file = FileId::new(6_119);
            let members = parsed
                .arena
                .iter()
                .filter_map(|(id, record)| {
                    let NodeData::PrivateIdentifier(identifier) = &record.data else {
                        return None;
                    };
                    Some((
                        NodeRef::new(parsed.arena.id(), file, record.parent.unwrap()),
                        NodeRef::new(parsed.arena.id(), file, id),
                        format!("Model.{}", identifier.text),
                    ))
                })
                .collect::<Vec<_>>();
            assert!(!members.is_empty(), "{source}");
            for checked_first in [false, true] {
                let mut context = context(&parsed, file);
                if checked_first {
                    context.check_source_file(file).unwrap();
                }
                let source_file = context.source_file(file).unwrap();
                let before = (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().len(),
                    context.store().source_file_links(source_file).cloned(),
                );
                for (declaration, name, expected) in &members {
                    let symbol = context.file(file).unwrap().1.symbol(*declaration).unwrap();
                    let encoded = context.store().symbol(symbol).unwrap().name().to_owned();
                    let declarations = context.get_symbol_declarations(symbol).unwrap().to_vec();
                    for _ in 0..2 {
                        assert_eq!(context.symbol_to_string(symbol).unwrap(), *expected);
                        assert_eq!(
                            context.symbol_to_string_at_location(symbol, *name).unwrap(),
                            *expected,
                        );
                    }
                    assert_eq!(
                        context.file(file).unwrap().1.symbol(*declaration),
                        Some(symbol)
                    );
                    assert_eq!(
                        context.get_symbol_declarations(symbol).unwrap(),
                        declarations
                    );
                    assert_eq!(
                        context.store().symbol(symbol).unwrap().name(),
                        encoded.as_ref(),
                    );
                }
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().symbol_len(),
                        context.store().symbol_store().symbol_table_len(),
                        context.store().checker_link_allocated_lengths(),
                        context.diagnostics().len(),
                        context.store().source_file_links(source_file).cloned(),
                    ),
                    before,
                    "{source}, checked_first {checked_first}",
                );
            }
        }
    }

    #[test]
    fn private_member_artifacts_reject_changed_merged_owner_without_writes() {
        for source in [
            "class Model { #value = 1; } namespace Model {}",
            "class Model { #value = 1; } namespace Model { export var tag = 2; }",
            "class Model<First = any, Second = First> { #value = 1; } namespace Model {}",
        ] {
            for checked_first in [false, true] {
                for poison in 0..5 {
                    let parsed = parse_source_file(source);
                    let file = FileId::new(6_120);
                    let mut context = context(&parsed, file);
                    if checked_first {
                        context.check_source_file(file).unwrap();
                    }
                    let (member, name) = parsed
                        .arena
                        .iter()
                        .find_map(|(id, record)| {
                            let NodeData::PropertyDeclaration(property) = &record.data else {
                                return None;
                            };
                            Some((
                                NodeRef::new(parsed.arena.id(), file, id),
                                NodeRef::new(parsed.arena.id(), file, property.name),
                            ))
                        })
                        .unwrap();
                    let symbol = context.file(file).unwrap().1.symbol(member).unwrap();
                    let owner = context.store().get_parent_of_symbol(symbol).unwrap();
                    let record = context.store().symbol(owner).unwrap();
                    let [class, namespace] = *record.declarations().unwrap() else {
                        panic!("the class and namespace share one owner")
                    };
                    let flags = record.flags();
                    match poison {
                        0 | 1 => {
                            let wrong = if poison == 0 {
                                SymbolFlags::CLASS
                            } else if flags.contains(SymbolFlags::VALUE_MODULE) {
                                SymbolFlags::CLASS | SymbolFlags::NAMESPACE_MODULE
                            } else {
                                SymbolFlags::CLASS | SymbolFlags::VALUE_MODULE
                            };
                            assert!(context.store_mut_for_test().set_symbol_flags(
                                owner,
                                wrong,
                                CheckFlags::NONE,
                            ));
                        }
                        2 => assert!(context.store_mut_for_test().set_symbol_declarations(
                            owner,
                            Some(vec![namespace, class]),
                            Some(class),
                        )),
                        3 => assert!(context.store_mut_for_test().set_symbol_declarations(
                            owner,
                            Some(vec![class]),
                            Some(class),
                        )),
                        4 => assert!(context.store_mut_for_test().set_symbol_declarations(
                            owner,
                            Some(vec![class, namespace]),
                            Some(namespace),
                        )),
                        _ => unreachable!(),
                    }
                    let source_file = context.source_file(file).unwrap();
                    let before = (
                        context.store().type_len(),
                        context.store().symbol_len(),
                        context.store().symbol_store().symbol_table_len(),
                        context.store().checker_link_allocated_lengths(),
                        context.diagnostics().len(),
                        context.store().source_file_links(source_file).cloned(),
                    );
                    assert!(context.symbol_to_string(symbol).is_err());
                    assert!(context.symbol_to_string_at_location(symbol, name).is_err());
                    assert_eq!(
                        (
                            context.store().type_len(),
                            context.store().symbol_len(),
                            context.store().symbol_store().symbol_table_len(),
                            context.store().checker_link_allocated_lengths(),
                            context.diagnostics().len(),
                            context.store().source_file_links(source_file).cloned(),
                        ),
                        before,
                        "{source}, checked_first {checked_first}, poison {poison}",
                    );
                }
            }
        }
    }

    #[test]
    fn private_member_artifacts_reject_changed_class_and_declaration_ownership() {
        for poison in 0..8 {
            let parsed =
                parse_source_file("class First { #value = 1; } class Second { #value = 2; }");
            let file = FileId::new(6_117);
            let mut context = context(&parsed, file);
            context.check_source_file(file).unwrap();
            let members = parsed
                .arena
                .iter()
                .filter_map(|(id, record)| {
                    let NodeData::PropertyDeclaration(property) = &record.data else {
                        return None;
                    };
                    Some((
                        NodeRef::new(parsed.arena.id(), file, id),
                        NodeRef::new(parsed.arena.id(), file, property.name),
                    ))
                })
                .collect::<Vec<_>>();
            let symbol = context.file(file).unwrap().1.symbol(members[0].0).unwrap();
            let other = context.file(file).unwrap().1.symbol(members[1].0).unwrap();
            let owner = context.store().get_parent_of_symbol(symbol).unwrap();
            let other_owner = context.store().get_parent_of_symbol(other).unwrap();
            let class = context
                .store()
                .symbol(owner)
                .unwrap()
                .value_declaration()
                .unwrap();
            let other_class = context
                .store()
                .symbol(other_owner)
                .unwrap()
                .value_declaration()
                .unwrap();
            match poison {
                0 => {
                    assert!(context.store_mut_for_test().set_symbol_relationships(
                        symbol,
                        None,
                        None,
                        Some(other_owner),
                        None
                    ));
                }
                1 => assert!(context.store_mut_for_test().set_symbol_declarations(
                    symbol,
                    Some(vec![members[1].0]),
                    Some(members[1].0)
                )),
                2 => assert!(context.store_mut_for_test().set_symbol_flags(
                    symbol,
                    SymbolFlags::METHOD,
                    CheckFlags::NONE
                )),
                3 => assert!(context.store_mut_for_test().set_symbol_declarations(
                    symbol,
                    Some(Vec::new()),
                    None
                )),
                4 => assert!(context.store_mut_for_test().set_symbol_flags(
                    owner,
                    SymbolFlags::INTERFACE,
                    CheckFlags::NONE
                )),
                5 => assert!(context.store_mut_for_test().set_symbol_declarations(
                    owner,
                    Some(vec![class]),
                    Some(other_class)
                )),
                6 => assert!(context.store_mut_for_test().set_symbol_declarations(
                    symbol,
                    Some(vec![members[0].0, members[0].0]),
                    Some(members[0].0)
                )),
                7 => assert!(context.store_mut_for_test().set_symbol_declarations(
                    owner,
                    Some(vec![other_class]),
                    Some(class)
                )),
                _ => unreachable!(),
            }
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().checker_link_allocated_lengths(),
            );
            assert!(context.symbol_to_string(symbol).is_err(), "poison {poison}");
            assert!(
                context
                    .symbol_to_string_at_location(symbol, members[0].1)
                    .is_err(),
                "poison {poison}"
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths()
                ),
                before
            );
        }
    }

    #[test]
    fn duplicate_member_artifacts_skip_distinct_static_and_instance_members() {
        for source in [
            "declare class Model { static value: number; accessor value: number; }",
            "declare class Model { value: number; static accessor value: number; }",
        ] {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}: {:?}",
                parsed.diagnostics
            );
            let file = FileId::new(6_118);
            let mut context = declaration_context(&parsed, file);
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let members = parsed
                .arena
                .iter()
                .filter_map(|(id, record)| {
                    let NodeData::PropertyDeclaration(property) = &record.data else {
                        return None;
                    };
                    let declaration = NodeRef::new(parsed.arena.id(), file, id);
                    Some((
                        declaration,
                        NodeRef::new(parsed.arena.id(), file, property.name),
                        context.file(file).unwrap().1.symbol(declaration).unwrap(),
                    ))
                })
                .collect::<Vec<_>>();
            assert_eq!(members.len(), 2);
            assert_ne!(members[0].2, members[1].2);
            for (declaration, name, symbol) in members {
                assert_eq!(
                    context.get_type_at_location(name).unwrap(),
                    number,
                    "{source}"
                );
                assert_eq!(
                    context.get_type_at_location(declaration).unwrap(),
                    number,
                    "{source}"
                );
                assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
            }
        }
    }

    #[test]
    fn duplicate_member_artifacts_reuse_source_annotations_and_literal_identities() {
        let parsed =
            parse_source_file("class Model { value: number = 2; accessor value: number = 3; }");
        let file = FileId::new(6_112);
        let mut context = context(&parsed, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2300, 2300]
        );
        let class_name = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::ClassDeclaration(class) = &record.data else {
                    return None;
                };
                class
                    .name
                    .map(|name| NodeRef::new(parsed.arena.id(), file, name))
            })
            .unwrap();
        let instance = context.get_type_at_location(class_name).unwrap();
        assert_eq!(context.type_to_string(instance).unwrap(), "Model");
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let mut results = Vec::new();
        for (id, record) in parsed.arena.iter() {
            let NodeData::PropertyDeclaration(property) = &record.data else {
                continue;
            };
            let declaration = NodeRef::new(parsed.arena.id(), file, id);
            let name = NodeRef::new(parsed.arena.id(), file, property.name);
            let initializer = NodeRef::new(parsed.arena.id(), file, property.initializer.unwrap());
            let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
            assert_eq!(context.get_type_at_location(name).unwrap(), number);
            assert_eq!(context.get_type_at_location(declaration).unwrap(), number);
            assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
            assert_eq!(
                context.symbol_to_string_at_location(symbol, name).unwrap(),
                "Model.value"
            );
            assert_eq!(context.get_symbol_declarations(symbol).unwrap().len(), 2);
            assert!(context.store().value_symbol_links(symbol).is_none());
            let literal = context.get_type_at_location(initializer).unwrap();
            let NodeData::NumericLiteral(source) =
                &parsed.arena.get(initializer.node).unwrap().data
            else {
                panic!("the recovered initializer must remain numeric")
            };
            assert_eq!(context.type_to_string(literal).unwrap(), source.text);
            let TypeData::Literal(data) = context.store().type_payload(literal).unwrap().data()
            else {
                panic!("the initializer must have its own literal type")
            };
            assert_eq!(data.regular_type, literal);
            results.push((declaration, name, initializer, literal));
        }
        assert_eq!(results.len(), 2);
        let before = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
            context.diagnostics().len(),
        );
        for (declaration, name, initializer, literal) in results {
            assert_eq!(context.get_type_at_location(name).unwrap(), number);
            assert_eq!(context.get_type_at_location(declaration).unwrap(), number);
            assert_eq!(context.get_type_at_location(initializer).unwrap(), literal);
        }
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().len()
            ),
            before
        );
    }

    #[test]
    fn duplicate_recovery_queries_replay_without_class_publication() {
        for (source, expected) in [
            (
                "class Model { before = 0; value = 1; middle = 'mid'; accessor value = 2; after = 'end'; }",
                &["number", "number", "string", "number", "string"][..],
            ),
            (
                "class Model { before = 0; value: number = 1; middle = 'mid'; accessor value: string = 'next'; after = 3; }",
                &["number", "string", "string", "string", "number"][..],
            ),
        ] {
            let parsed = parse_source_file(source);
            let file = FileId::new(6_121);
            let members = parsed
                .arena
                .iter()
                .filter_map(|(id, record)| {
                    let NodeData::PropertyDeclaration(property) = &record.data else {
                        return None;
                    };
                    Some((
                        NodeRef::new(parsed.arena.id(), file, id),
                        NodeRef::new(parsed.arena.id(), file, property.name),
                    ))
                })
                .collect::<Vec<_>>();
            for checked_first in [false, true] {
                let mut context = context(&parsed, file);
                if checked_first {
                    context.check_source_file(file).unwrap();
                }
                let first_symbol = context.file(file).unwrap().1.symbol(members[0].0).unwrap();
                let owner = context.store().get_parent_of_symbol(first_symbol).unwrap();
                let mut results = Vec::new();
                for ((declaration, name), expected) in members.iter().zip(expected) {
                    let symbol = context.file(file).unwrap().1.symbol(*declaration).unwrap();
                    let type_ = context.get_type_at_location(*name).unwrap();
                    assert_eq!(
                        context.type_to_string(type_).unwrap(),
                        *expected,
                        "{source}"
                    );
                    assert_eq!(context.get_type_at_location(*declaration).unwrap(), type_);
                    assert_eq!(context.get_symbol_at_location(*name).unwrap(), Some(symbol));
                    results.push(type_);
                }
                assert!(context.store().declared_type_links(owner).is_none());
                assert!(context.store().value_symbol_links(owner).is_none());
                let before = (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().len(),
                );
                for ((_, name), expected) in members.iter().zip(results) {
                    assert_eq!(context.get_type_at_location(*name).unwrap(), expected);
                }
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().symbol_len(),
                        context.store().signature_len(),
                        context.store().checker_link_allocated_lengths(),
                        context.diagnostics().len(),
                    ),
                    before,
                    "{source}, checked_first {checked_first}"
                );
            }
        }
    }

    #[test]
    fn duplicate_recovery_checks_unrelated_caches_before_source_writes() {
        let source = "class Model { before: number = 0; value: number = 1; middle: string = 'mid'; accessor value: number = 2; after: number = 3; }";
        for checked_first in [false, true] {
            for poison in 0..10 {
                let parsed = parse_source_file(source);
                let file = FileId::new(6_122);
                let mut context = context(&parsed, file);
                if checked_first {
                    context.check_source_file(file).unwrap();
                }
                let members = parsed
                    .arena
                    .iter()
                    .filter_map(|(id, record)| {
                        let NodeData::PropertyDeclaration(property) = &record.data else {
                            return None;
                        };
                        Some((
                            NodeRef::new(parsed.arena.id(), file, id),
                            NodeRef::new(parsed.arena.id(), file, property.name),
                            NodeRef::new(parsed.arena.id(), file, property.type_.unwrap()),
                            NodeRef::new(parsed.arena.id(), file, property.initializer.unwrap()),
                        ))
                    })
                    .collect::<Vec<_>>();
                let symbol = context.file(file).unwrap().1.symbol(members[1].0).unwrap();
                let unrelated = context.file(file).unwrap().1.symbol(members[0].0).unwrap();
                let number = context.store().intrinsic_bootstrap().unwrap().number_type;
                let string = context.store().intrinsic_bootstrap().unwrap().string_type;
                match poison {
                    0..=2 => {
                        let (node, wrong) = match poison {
                            0 => (members[0].1, string),
                            1 => (members[2].3, number),
                            _ => (members[4].2, string),
                        };
                        assert!(context.store_mut_for_test().set_type_node_links(
                            node,
                            TypeNodeLinks {
                                resolved_type: Some(wrong),
                                outer_type_parameters: None
                            }
                        ));
                    }
                    3 => assert!(context.store_mut_for_test().set_symbol_node_links(
                        members[3].1,
                        SymbolNodeLinks {
                            resolved_symbol: Some(unrelated)
                        }
                    )),
                    4 => assert!(context.store_mut_for_test().set_symbol_node_links(
                        members[0].3,
                        SymbolNodeLinks {
                            resolved_symbol: Some(unrelated)
                        }
                    )),
                    5 => assert!(context.store_mut_for_test().set_symbol_declarations(
                        symbol,
                        Some(vec![members[1].0]),
                        Some(members[1].0)
                    )),
                    6 => assert!(context.store_mut_for_test().set_symbol_declarations(
                        symbol,
                        Some(vec![members[3].0, members[1].0]),
                        Some(members[1].0)
                    )),
                    7 => assert!(context.store_mut_for_test().set_symbol_flags(
                        symbol,
                        SymbolFlags::PROPERTY,
                        CheckFlags::NONE
                    )),
                    8 => assert!(context.store_mut_for_test().set_type_node_links(
                        members[4].0,
                        TypeNodeLinks {
                            resolved_type: None,
                            outer_type_parameters: Some(vec![number])
                        }
                    )),
                    9 => assert!(context.store_mut_for_test().set_symbol_relationships(
                        symbol,
                        None,
                        None,
                        Some(unrelated),
                        None
                    )),
                    _ => unreachable!(),
                }
                let source_file = context.source_file(file).unwrap();
                let before = (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().len(),
                    context.store().source_file_links(source_file).cloned(),
                );
                for query in [members[1].1, members[0].1] {
                    assert!(
                        context.get_type_at_location(query).is_err(),
                        "checked_first {checked_first}, poison {poison}"
                    );
                }
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().symbol_len(),
                        context.store().signature_len(),
                        context.store().symbol_store().symbol_table_len(),
                        context.store().checker_link_allocated_lengths(),
                        context.diagnostics().len(),
                        context.store().source_file_links(source_file).cloned(),
                    ),
                    before,
                    "checked_first {checked_first}, poison {poison}"
                );
            }
        }
    }

    #[test]
    fn duplicate_recovery_rejects_numeric_text_changed_before_binding() {
        for changed in [0, 3] {
            let mut parsed = parse_source_file(
                "class Model { before: number = 0; value: number = 1; middle: number = 3; accessor value: number = 2; }",
            );
            let file = FileId::new(6_124);
            let members = parsed
                .arena
                .iter()
                .filter_map(|(id, record)| {
                    let NodeData::PropertyDeclaration(property) = &record.data else {
                        return None;
                    };
                    Some((id, property.name, property.initializer.unwrap()))
                })
                .collect::<Vec<_>>();
            // Bind the changed AST so this tests spelling, not a stale arena revision.
            let NodeData::NumericLiteral(literal) =
                &mut parsed.arena.get_mut(members[changed].2).unwrap().data
            else {
                unreachable!()
            };
            literal.text = "9".to_owned();
            let mut context = context(&parsed, file);
            let name = NodeRef::new(parsed.arena.id(), file, members[1].1);
            let source_file = context.source_file(file).unwrap();
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().len(),
                context.store().source_file_links(source_file).cloned(),
            );
            assert!(context.get_type_at_location(name).is_err());
            assert!(context.check_source_file(file).is_err());
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().len(),
                    context.store().source_file_links(source_file).cloned(),
                ),
                before
            );
        }
    }

    #[test]
    fn duplicate_recovery_does_not_complete_unsupported_bodies() {
        for source in [
            "class Model { value: number = 1; run() { missing(); } accessor value: number = 2; }",
            "class Model { before = missing(); value: number = 1; accessor value: number = 2; }",
        ] {
            let parsed = parse_source_file(source);
            let file = FileId::new(6_123);
            let mut context = context(&parsed, file);
            let source_file = context.source_file(file).unwrap();
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.diagnostics().len(),
                context.store().source_file_links(source_file).cloned(),
            );
            assert!(context.check_source_file(file).is_err(), "{source}");
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().len(),
                    context.store().source_file_links(source_file).cloned(),
                ),
                before,
                "{source}"
            );
        }
    }

    #[test]
    fn duplicate_member_artifacts_reject_changed_ownership_and_caches() {
        for checked_first in [false, true] {
            for poison in 0..8 {
                let parsed = parse_source_file(
                    "class Model { value: number = 2; accessor value: number = 3; }",
                );
                let file = FileId::new(6_113);
                let mut context = context(&parsed, file);
                if checked_first {
                    context.check_source_file(file).unwrap();
                }
                let members = parsed
                    .arena
                    .iter()
                    .filter_map(|(id, record)| {
                        let NodeData::PropertyDeclaration(property) = &record.data else {
                            return None;
                        };
                        Some((
                            NodeRef::new(parsed.arena.id(), file, id),
                            NodeRef::new(parsed.arena.id(), file, property.name),
                            NodeRef::new(parsed.arena.id(), file, property.type_.unwrap()),
                            NodeRef::new(parsed.arena.id(), file, property.initializer.unwrap()),
                        ))
                    })
                    .collect::<Vec<_>>();
                let (declaration, name, annotation, initializer) = members[0];
                let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
                let string = context.store().intrinsic_bootstrap().unwrap().string_type;
                match poison {
                    0 | 4 | 5 | 6 | 7 => {
                        let node = match poison {
                            0 => name,
                            4 => annotation,
                            5 => initializer,
                            6 => members[1].3,
                            _ => declaration,
                        };
                        assert!(context.store_mut_for_test().set_type_node_links(
                            node,
                            TypeNodeLinks {
                                resolved_type: Some(string),
                                outer_type_parameters: None
                            }
                        ));
                    }
                    1 => assert!(context.store_mut_for_test().set_value_symbol_links(
                        symbol,
                        ValueSymbolLinks {
                            resolved_type: Some(string),
                            ..ValueSymbolLinks::default()
                        }
                    )),
                    2 => assert!(context.store_mut_for_test().set_symbol_declarations(
                        symbol,
                        Some(vec![members[1].0, declaration]),
                        Some(declaration)
                    )),
                    3 => assert!(context.store_mut_for_test().set_symbol_flags(
                        symbol,
                        SymbolFlags::PROPERTY,
                        CheckFlags::NONE
                    )),
                    _ => unreachable!(),
                }
                let before = (
                    context.store().type_len(),
                    context.store().symbol_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.diagnostics().len(),
                    context
                        .store()
                        .source_file_links(context.source_file(file).unwrap())
                        .cloned(),
                );
                let query = match poison {
                    4 => annotation,
                    5 => initializer,
                    7 => declaration,
                    _ => name,
                };
                assert!(
                    context.get_type_at_location(query).is_err(),
                    "checked_first {checked_first}, poison {poison}"
                );
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().symbol_len(),
                        context.store().signature_len(),
                        context.store().checker_link_allocated_lengths(),
                        context.diagnostics().len(),
                        context
                            .store()
                            .source_file_links(context.source_file(file).unwrap())
                            .cloned(),
                    ),
                    before,
                    "checked_first {checked_first}, poison {poison}"
                );
            }
        }
    }

    #[test]
    fn enum_initializer_artifacts_use_primitive_literals_without_member_symbols() {
        for checked_first in [false, true] {
            let parsed = parse_source_file("enum Choice { First = 'choice', Second = 42 }");
            let file = FileId::new(6_114);
            let mut context = context(&parsed, file);
            if checked_first {
                context.check_source_file(file).unwrap();
            }
            let mut results = Vec::new();
            for (id, record) in parsed.arena.iter() {
                if !matches!(
                    record.data,
                    NodeData::StringLiteral(_) | NodeData::NumericLiteral(_)
                ) {
                    continue;
                }
                let node = NodeRef::new(parsed.arena.id(), file, id);
                let type_ = context.get_type_at_location(node).unwrap();
                let payload = context.store().type_payload(type_).unwrap();
                let TypeData::Literal(literal) = payload.data() else {
                    panic!("an enum initializer must retain its primitive literal type")
                };
                assert_eq!(literal.regular_type, type_);
                assert!(payload.symbol().is_none());
                assert!(!payload.flags().contains(TypeFlags::ENUM_LITERAL));
                assert_eq!(context.get_symbol_at_location(node).unwrap(), None);
                let fresh = context.store().fresh_type_of_literal_type(type_).unwrap();
                assert!(context.store_mut_for_test().set_type_node_links(
                    node,
                    TypeNodeLinks {
                        resolved_type: Some(fresh),
                        outer_type_parameters: None,
                    }
                ));
                results.push((node, type_));
            }
            assert_eq!(results.len(), 2);
            assert_eq!(context.type_to_string(results[0].1).unwrap(), "\"choice\"");
            assert_eq!(context.type_to_string(results[1].1).unwrap(), "42");
            let source_file = context.source_file(file).unwrap();
            assert!(
                context
                    .store()
                    .source_file_links(source_file)
                    .unwrap()
                    .type_checked
            );
            let before = (
                context.store().type_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().source_file_links(source_file).cloned(),
            );
            for (node, type_) in results {
                assert_eq!(context.get_type_at_location(node).unwrap(), type_);
            }
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.store().source_file_links(source_file).cloned(),
                ),
                before,
                "checked_first {checked_first}",
            );
        }
    }

    #[test]
    fn enum_initializer_artifacts_reject_changed_enum_and_literal_caches() {
        for source in [
            "enum Choice { First = 'choice' }",
            "enum Choice { First = 42 }",
        ] {
            for checked_first in [false, true] {
                for poison in 0..5 {
                    let parsed = parse_source_file(source);
                    let file = FileId::new(6_115);
                    let mut context = context(&parsed, file);
                    if checked_first {
                        context.check_source_file(file).unwrap();
                    }
                    let (member, initializer) = parsed
                        .arena
                        .iter()
                        .find_map(|(id, record)| {
                            let NodeData::EnumMember(member) = &record.data else {
                                return None;
                            };
                            Some((
                                NodeRef::new(parsed.arena.id(), file, id),
                                NodeRef::new(parsed.arena.id(), file, member.initializer.unwrap()),
                            ))
                        })
                        .unwrap();
                    let symbol = context.file(file).unwrap().1.symbol(member).unwrap();
                    let owner = context.store().get_parent_of_symbol(symbol).unwrap();
                    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
                    match poison {
                        0 => assert!(context.store_mut_for_test().set_type_node_links(
                            initializer,
                            TypeNodeLinks {
                                resolved_type: Some(number),
                                outer_type_parameters: None
                            }
                        )),
                        1 => assert!(context.store_mut_for_test().set_value_symbol_links(
                            symbol,
                            ValueSymbolLinks {
                                resolved_type: Some(number),
                                ..ValueSymbolLinks::default()
                            }
                        )),
                        2 => assert!(context.store_mut_for_test().set_symbol_node_links(
                            initializer,
                            SymbolNodeLinks {
                                resolved_symbol: Some(symbol)
                            }
                        )),
                        3 => {
                            // Obtain the enum member type without checking its source file.
                            context.get_declared_type_of_symbol(owner).unwrap();
                            let member_type = context
                                .store()
                                .value_symbol_links(symbol)
                                .unwrap()
                                .resolved_type
                                .unwrap();
                            assert!(context.store_mut_for_test().set_type_node_links(
                                initializer,
                                TypeNodeLinks {
                                    resolved_type: Some(member_type),
                                    outer_type_parameters: None,
                                }
                            ));
                        }
                        4 => assert!(context.store_mut_for_test().set_type_node_links(
                            initializer,
                            TypeNodeLinks {
                                resolved_type: None,
                                outer_type_parameters: Some(vec![number]),
                            }
                        )),
                        _ => unreachable!(),
                    }
                    let source_file = context.source_file(file).unwrap();
                    assert_eq!(
                        context
                            .store()
                            .source_file_links(source_file)
                            .is_some_and(|links| links.type_checked),
                        checked_first,
                    );
                    let before = (
                        context.store().type_len(),
                        context.store().symbol_len(),
                        context.store().signature_len(),
                        context.store().checker_link_allocated_lengths(),
                        context.diagnostics().len(),
                        context.store().source_file_links(source_file).cloned(),
                        context.store().declared_type_links(owner).cloned(),
                        context.store().value_symbol_links(symbol).cloned(),
                        context.store().enum_member_links(member).cloned(),
                        context.store().type_node_links(initializer).cloned(),
                        context.store().symbol_node_links(initializer).cloned(),
                    );
                    let result = context.get_type_at_location(initializer);
                    match poison {
                        0 => assert_eq!(
                            result,
                            Err(CanonicalArtifactQueryError::InvalidType {
                                node: initializer,
                                type_: number,
                            })
                        ),
                        2 => assert_eq!(
                            result,
                            Err(CanonicalArtifactQueryError::InvalidSymbol {
                                node: initializer,
                                symbol,
                            })
                        ),
                        _ => assert!(result.is_err(), "{source}, poison {poison}"),
                    }
                    assert_eq!(
                        (
                            context.store().type_len(),
                            context.store().symbol_len(),
                            context.store().signature_len(),
                            context.store().checker_link_allocated_lengths(),
                            context.diagnostics().len(),
                            context.store().source_file_links(source_file).cloned(),
                            context.store().declared_type_links(owner).cloned(),
                            context.store().value_symbol_links(symbol).cloned(),
                            context.store().enum_member_links(member).cloned(),
                            context.store().type_node_links(initializer).cloned(),
                            context.store().symbol_node_links(initializer).cloned(),
                        ),
                        before,
                        "{source}, checked_first {checked_first}, poison {poison}",
                    );
                }
            }
        }
    }

    #[test]
    fn declaration_file_accessors_reuse_getter_and_setter_annotations() {
        let parsed = parse_source_file(concat!(
            "declare class Model { ",
            "get value(): number; set value(next: number); ",
            "get inferred(); set inferred(next: string); ",
            "set label(next: string); get ready(): boolean; ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_027);
        let mut context = declaration_context(&parsed, file);
        let (number, string, boolean) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.boolean_type,
            )
        };
        let mut declarations = Vec::new();

        for (node, record) in parsed.arena.iter() {
            let name = match &record.data {
                NodeData::GetAccessorDeclaration(accessor) => accessor.name,
                NodeData::SetAccessorDeclaration(accessor) => accessor.name,
                _ => continue,
            };
            let declaration = NodeRef::new(parsed.arena.id(), file, node);
            let name = NodeRef::new(parsed.arena.id(), file, name);
            let NodeData::Identifier(identifier) = &parsed.arena.get(name.node).unwrap().data
            else {
                panic!("accessor names must be identifiers")
            };
            let expected = match identifier.text.as_str() {
                "value" => number,
                "inferred" | "label" => string,
                "ready" => boolean,
                _ => panic!("unexpected accessor {}", identifier.text),
            };
            let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();

            assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
            assert_eq!(
                context.get_symbol_at_location(declaration).unwrap(),
                Some(symbol)
            );
            assert_eq!(context.get_type_at_location(name).unwrap(), expected);
            assert_eq!(context.get_type_at_location(declaration).unwrap(), expected);
            assert!(context.store().value_symbol_links(symbol).is_none());
            declarations.push((declaration, name, symbol, expected));
        }
        assert_eq!(declarations.len(), 6);
        assert_eq!(declarations[0].2, declarations[1].2);
        assert_eq!(declarations[2].2, declarations[3].2);

        let warm = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );
        for (declaration, name, symbol, expected) in declarations {
            assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
            assert_eq!(context.get_type_at_location(declaration).unwrap(), expected);
            assert_eq!(context.get_type_at_location(name).unwrap(), expected);
        }
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm
        );
        let source = context.source_file(file).unwrap();
        assert!(
            context
                .store()
                .source_file_links(source)
                .is_none_or(|links| !links.type_checked)
        );
    }

    #[test]
    fn unannotated_declaration_file_accessors_reject_without_changing_caches() {
        let parsed = parse_source_file(concat!(
            "declare class Model { ",
            "get missing(); ",
            "set absent(next); ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_028);
        let mut context = declaration_context(&parsed, file);
        let cold = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().signature_len(),
            context.store().checker_link_allocated_lengths(),
        );

        for (node, record) in parsed.arena.iter() {
            let name = match &record.data {
                NodeData::GetAccessorDeclaration(accessor) => accessor.name,
                NodeData::SetAccessorDeclaration(accessor) => accessor.name,
                _ => continue,
            };
            let declaration = NodeRef::new(parsed.arena.id(), file, node);
            let name = NodeRef::new(parsed.arena.id(), file, name);

            assert_eq!(
                context.get_type_at_location(name),
                Err(CanonicalArtifactQueryError::MissingType {
                    node: name,
                    kind: SyntaxKind::Identifier,
                })
            );
            assert_eq!(
                context.get_type_at_location(declaration),
                Err(CanonicalArtifactQueryError::MissingType {
                    node: declaration,
                    kind: record.kind,
                })
            );
        }

        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            cold
        );
    }

    #[test]
    fn declaration_symbols_take_precedence_over_cached_reference_symbols() {
        let parsed = parse_source_file(concat!(
            "declare namespace Names { ",
            "export namespace Inner {} export import Alias = Inner; }\n",
            "declare enum Kind { First = 1 }\n",
            "declare class Model { static count: number; method(): string; }\n",
            "type Copied<Input> = { [Key in keyof Input]: Input[Key] };\n",
            "interface Factory { new(argument: number): string; }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_021);
        let mut context = declaration_context(&parsed, file);
        let incorrect = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .global_this_symbol;
        let mut declarations = Vec::new();

        for (node, record) in parsed.arena.iter() {
            let name = match &record.data {
                NodeData::EnumMember(declaration) => declaration.name,
                NodeData::ImportEqualsDeclaration(declaration) => declaration.name,
                NodeData::MethodDeclaration(declaration) => declaration.name,
                NodeData::PropertyDeclaration(declaration)
                    if record
                        .parent
                        .and_then(|parent| parsed.arena.get(parent))
                        .is_some_and(|parent| {
                            matches!(parent.data, NodeData::ClassDeclaration(_))
                        }) =>
                {
                    declaration.name
                }
                NodeData::TypeParameterDeclaration(declaration)
                    if record
                        .parent
                        .and_then(|parent| parsed.arena.get(parent))
                        .is_some_and(|parent| {
                            matches!(parent.data, NodeData::MappedTypeNode(_))
                        }) =>
                {
                    declaration.name
                }
                NodeData::ParameterDeclaration(declaration)
                    if record
                        .parent
                        .and_then(|parent| parsed.arena.get(parent))
                        .is_some_and(|parent| {
                            matches!(parent.data, NodeData::ConstructSignatureDeclaration(_))
                        }) =>
                {
                    declaration.name
                }
                _ => continue,
            };
            let declaration = NodeRef::new(parsed.arena.id(), file, node);
            let name = NodeRef::new(parsed.arena.id(), file, name);
            let expected = context.file(file).unwrap().1.symbol(declaration).unwrap();
            declarations.push((declaration, name, expected));
        }
        assert_eq!(declarations.len(), 6);

        for (declaration, name, expected) in declarations {
            assert!(context.store_mut_for_test().set_symbol_node_links(
                name,
                SymbolNodeLinks {
                    resolved_symbol: Some(incorrect),
                },
            ));
            assert_ne!(incorrect, expected);
            assert_eq!(
                context.get_symbol_at_location(name).unwrap(),
                Some(expected)
            );
            assert_eq!(
                context.get_symbol_at_location(declaration).unwrap(),
                Some(expected)
            );
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(name)
                    .and_then(|links| links.resolved_symbol),
                Some(incorrect)
            );
        }

        for (node, record) in parsed.arena.iter() {
            if !matches!(
                record.data,
                NodeData::MappedTypeNode(_) | NodeData::ConstructSignatureDeclaration(_)
            ) {
                continue;
            }
            let declaration = NodeRef::new(parsed.arena.id(), file, node);
            let expected = context.file(file).unwrap().1.symbol(declaration).unwrap();
            assert!(context.store_mut_for_test().set_symbol_node_links(
                declaration,
                SymbolNodeLinks {
                    resolved_symbol: Some(incorrect),
                },
            ));
            assert_eq!(
                context.get_symbol_at_location(declaration).unwrap(),
                Some(expected)
            );
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(declaration)
                    .and_then(|links| links.resolved_symbol),
                Some(incorrect)
            );
        }
    }

    #[test]
    fn cached_reference_symbols_follow_merged_identity_without_rewriting_links() {
        let parsed = parse_source_file("declare const value: number; const copied = value;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_022);
        let mut context = declaration_context(&parsed, file);
        let (declaration, reference) = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data
                else {
                    return None;
                };
                match identifier.text.as_str() {
                    "value" => Some((Some(NodeRef::new(parsed.arena.id(), file, node)), None)),
                    "copied" => Some((
                        None,
                        variable
                            .initializer
                            .map(|node| NodeRef::new(parsed.arena.id(), file, node)),
                    )),
                    _ => None,
                }
            })
            .fold((None, None), |(declaration, reference), (next, read)| {
                (declaration.or(next), reference.or(read))
            });
        let declaration = declaration.unwrap();
        let reference = reference.unwrap();
        let target = context.file(file).unwrap().1.symbol(declaration).unwrap();
        let raw = context.store_mut_for_test().alloc_transient_symbol(
            SymbolFlags::BLOCK_SCOPED_VARIABLE,
            EscapedName::source("raw"),
            CheckFlags::NONE,
        );
        context
            .store_mut_for_test()
            .record_merged_symbol(target, raw)
            .unwrap();
        assert!(context.store_mut_for_test().set_symbol_node_links(
            reference,
            SymbolNodeLinks {
                resolved_symbol: Some(raw),
            },
        ));

        assert_eq!(
            context.get_symbol_at_location(reference).unwrap(),
            Some(target)
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(reference)
                .and_then(|links| links.resolved_symbol),
            Some(raw)
        );

        let unknown = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .unknown_symbol;
        let raw_unknown = context.store_mut_for_test().alloc_transient_symbol(
            SymbolFlags::PROPERTY,
            EscapedName::source("rawUnknown"),
            CheckFlags::NONE,
        );
        context
            .store_mut_for_test()
            .record_merged_symbol(unknown, raw_unknown)
            .unwrap();
        assert!(context.store_mut_for_test().set_symbol_node_links(
            reference,
            SymbolNodeLinks {
                resolved_symbol: Some(raw_unknown),
            },
        ));

        assert_eq!(context.get_symbol_at_location(reference).unwrap(), None);
        assert_eq!(
            context
                .store()
                .symbol_node_links(reference)
                .and_then(|links| links.resolved_symbol),
            Some(raw_unknown)
        );
    }

    #[test]
    fn literal_computed_property_names_reuse_their_bound_symbols_and_source_spelling() {
        let parsed = parse_source_file(concat!(
            "const value: any = { ",
            "['quoted']: 1, [2]: 'two', [`template`]: true, ",
            "\"plain\": 4, 3: 5 };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_015);
        let mut context = declaration_context(&parsed, file);
        let mut names = Vec::new();

        for (node, record) in parsed.arena.iter() {
            let NodeData::PropertyAssignment(property) = &record.data else {
                continue;
            };
            let declaration = NodeRef::new(parsed.arena.id(), file, node);
            let name = NodeRef::new(parsed.arena.id(), file, property.name);
            let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
            assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));

            if let NodeData::ComputedPropertyName(computed) =
                &parsed.arena.get(property.name).unwrap().data
            {
                let literal = NodeRef::new(parsed.arena.id(), file, computed.expression);
                assert_eq!(
                    context.get_symbol_at_location(literal).unwrap(),
                    Some(symbol)
                );
                assert!(context.store().symbol_node_links(literal).is_none());
            }

            names.push(context.symbol_to_string(symbol).unwrap());
        }

        assert_eq!(
            names,
            ["['quoted']", "[2]", "[`template`]", "\"plain\"", "3"]
        );
    }

    #[test]
    fn literal_class_and_interface_members_keep_bracketed_owner_spelling() {
        let parsed = parse_source_file(concat!(
            "interface Shape { 1: string; \"named\": number; [\"computed\"]: boolean; }\n",
            "class Model { [2]!: string; \"literal\"!: number; }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_016);
        let context = declaration_context(&parsed, file);
        let names = parsed
            .arena
            .iter()
            .filter(|(_, record)| matches!(record.data, NodeData::PropertyDeclaration(_)))
            .map(|(node, _)| {
                let declaration = NodeRef::new(parsed.arena.id(), file, node);
                let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
                context.symbol_to_string(symbol).unwrap()
            })
            .collect::<Vec<_>>();

        assert_eq!(
            names,
            [
                "Shape[1]",
                "Shape[\"named\"]",
                "Shape[\"computed\"]",
                "Model[2]",
                "Model[\"literal\"]",
            ]
        );
    }

    #[test]
    fn unicode_escaped_member_names_preserve_declaration_and_owner_spelling() {
        let parsed = parse_source_file(concat!(
            r"enum Kind { \u0041 = 1, Plain = 2 }",
            "\n",
            r"class Holder\u0031 { \u{62}!: number; plain!: number; }",
            "\n",
            r"interface Shape\u0032 { \u0063: string; plain: number; }",
            "\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_018);
        let mut context = declaration_context(&parsed, file);
        let mut names = Vec::new();

        for (node, record) in parsed.arena.iter() {
            let name = match &record.data {
                NodeData::EnumDeclaration(declaration) => declaration.name,
                NodeData::EnumMember(declaration) => declaration.name,
                NodeData::ClassDeclaration(declaration) => declaration.name.unwrap(),
                NodeData::InterfaceDeclaration(declaration) => declaration.name,
                NodeData::PropertyDeclaration(declaration) => declaration.name,
                _ => continue,
            };
            let declaration = NodeRef::new(parsed.arena.id(), file, node);
            let name = NodeRef::new(parsed.arena.id(), file, name);
            let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
            let NodeData::Identifier(identifier) = &parsed.arena.get(name.node).unwrap().data
            else {
                panic!("fixture declarations have identifier names")
            };
            assert_eq!(
                context.store().symbol(symbol).unwrap().name().as_utf8(),
                Some(identifier.text.as_str())
            );
            assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
            names.push(context.symbol_to_string(symbol).unwrap());
        }

        assert_eq!(
            names,
            [
                "Kind[\\u0041]",
                "Kind.Plain",
                "Kind",
                "Holder\\u0031[\\u{62}]",
                "Holder\\u0031.plain",
                "Holder\\u0031",
                "Shape\\u0032[\\u0063]",
                "Shape\\u0032.plain",
                "Shape\\u0032",
            ]
        );
    }

    #[test]
    fn unicode_escaped_standalone_symbols_preserve_original_declaration_spelling() {
        let parsed = parse_source_file(concat!(
            r"const \u0078 = 1;",
            "\n",
            r"const x\u{79} = 2;",
            "\n",
            "const plain = 3;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_019);
        let mut context = declaration_context(&parsed, file);
        let mut names = Vec::new();

        for (node, record) in parsed.arena.iter() {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                continue;
            };
            let declaration = NodeRef::new(parsed.arena.id(), file, node);
            let name = NodeRef::new(parsed.arena.id(), file, variable.name);
            let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
            let NodeData::Identifier(identifier) = &parsed.arena.get(name.node).unwrap().data
            else {
                panic!("fixture variables have identifier names")
            };
            assert_eq!(
                context.store().symbol(symbol).unwrap().name().as_utf8(),
                Some(identifier.text.as_str())
            );
            assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
            names.push(context.symbol_to_string(symbol).unwrap());
        }

        assert_eq!(names, ["\\u0078", "x\\u{79}", "plain"]);
    }

    #[test]
    fn value_type_queries_expose_reference_identity_without_a_wrapper_symbol() {
        let parsed = parse_source_file(concat!(
            "const value: string = 'ready';\n",
            "let result: typeof value;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_020);
        let mut context = declaration_context(&parsed, file);
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                    return None;
                };
                (name.text == "value").then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
        let expected = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(expected),
                ..ValueSymbolLinks::default()
            },
        ));
        let (query, reference) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::TypeQueryNode(query) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, query.expr_name),
                ))
            })
            .unwrap();

        assert!(context.store().symbol_node_links(query).is_none());
        assert!(context.store().symbol_node_links(reference).is_none());
        assert_eq!(context.get_symbol_at_location(query).unwrap(), None);
        assert_eq!(
            context.get_symbol_at_location(reference).unwrap(),
            Some(symbol)
        );
        assert_eq!(context.get_type_at_location(query).unwrap(), expected);
        assert_eq!(context.get_type_at_location(reference).unwrap(), expected);
        assert!(
            context
                .store()
                .symbol_node_links(query)
                .is_none_or(|links| links.resolved_symbol.is_none())
        );
        assert_eq!(
            context
                .store()
                .symbol_node_links(reference)
                .and_then(|links| links.resolved_symbol),
            Some(symbol)
        );
    }

    #[test]
    fn indexed_jsx_symbols_include_the_namespace_and_bracketed_index_name() {
        let parsed = parse_source_file(concat!(
            "declare namespace JSX {\n",
            "  interface IntrinsicElements { [tag: string]: any; }\n",
            "}\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_017);
        let mut context = declaration_context(&parsed, file);
        let interface =
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(record.data, NodeData::InterfaceDeclaration(_))
                        .then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
        let index = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(record.data, NodeData::IndexSignatureDeclaration(_))
                    .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let owner = context.file(file).unwrap().1.symbol(interface).unwrap();
        let symbol = context
            .store_mut_for_test()
            .alloc_symbol(SymbolData {
                flags: SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
                check_flags: CheckFlags::INDEX_SYMBOL,
                name: EscapedName::internal(InternalSymbolName::Index),
                declarations: Some(vec![index]),
                value_declaration: Some(index),
                members: None,
                exports: None,
                parent: Some(owner),
                export_symbol: None,
            })
            .unwrap();

        assert_eq!(
            context.symbol_to_string(symbol).unwrap(),
            "JSX.IntrinsicElements[__index]"
        );
    }

    #[test]
    fn namespace_only_global_augmentation_names_use_the_canonical_error_type() {
        let parsed = parse_source_file(concat!(
            "export {};\n",
            "declare global { interface Marker { value: string; } }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_012);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/global.d.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    true,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let (declaration, name) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                (module.keyword == SyntaxKind::GlobalKeyword).then_some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, module.name),
                ))
            })
            .unwrap();
        let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();

        assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
        assert_eq!(context.symbol_to_string(symbol).unwrap(), "global");
        assert_eq!(
            context.get_type_at_location(name).unwrap(),
            context.store().intrinsic_bootstrap().unwrap().error_type
        );
    }

    #[test]
    fn global_augmentation_value_queries_keep_identity_without_resolving_exports() {
        let parsed = parse_source_file(concat!(
            "export {};\n",
            "declare global { var marker: 'ready'; var unrelated: Missing; }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_062);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/global.d.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    true,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let (declaration, name) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ModuleDeclaration(module) = &record.data else {
                    return None;
                };
                (module.keyword == SyntaxKind::GlobalKeyword).then_some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, module.name),
                ))
            })
            .unwrap();
        let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
        assert!(
            context
                .store()
                .symbol(symbol)
                .unwrap()
                .flags()
                .contains(SymbolFlags::VALUE_MODULE)
        );

        let before_types = context.store().type_len();
        let before_diagnostics = context.diagnostics().len();
        let type_ = context.get_type_at_location(name).unwrap();
        assert_eq!(context.store().type_len(), before_types + 1);
        let record = context.store().type_payload(type_).unwrap();
        assert_eq!(record.symbol(), Some(symbol));
        assert_eq!(record.object_flags(), ObjectFlags::ANONYMOUS);
        assert_ne!(type_, context.global_types().global_this_value_type);
        assert_eq!(context.type_to_string(type_).unwrap(), "typeof global");
        for _ in 0..2 {
            assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
            assert_eq!(context.get_type_at_location(name).unwrap(), type_);
            assert_eq!(context.get_type_at_location(declaration).unwrap(), type_);
            assert_eq!(context.get_type_of_module_value(symbol).unwrap(), type_);
            assert_eq!(context.store().type_len(), before_types + 1);
            assert!(context.store().type_node_links(name).is_none());
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .unwrap()
                    .resolved_type,
                Some(type_)
            );
        }
        for (node, record) in parsed.arena.iter() {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                continue;
            };
            let declaration = NodeRef::new(parsed.arena.id(), file, node);
            let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
            let annotation = NodeRef::new(parsed.arena.id(), file, variable.type_.unwrap());
            assert!(context.store().value_symbol_links(symbol).is_none());
            assert!(context.store().type_node_links(annotation).is_none());
        }
        assert_eq!(context.diagnostics().len(), before_diagnostics);
    }

    #[test]
    fn shorthand_names_expose_property_declarations_without_replacing_value_reads() {
        let parsed = parse_source_file(concat!(
            "const property: string = 'ready';\n",
            "const object: any = { property };\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_013);
        let mut context = declaration_context(&parsed, file);
        let (declaration, name) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ShorthandPropertyAssignment(property) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, property.name),
                ))
            })
            .unwrap();
        let property = context.file(file).unwrap().1.symbol(declaration).unwrap();
        let value = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data
                else {
                    return None;
                };
                (identifier.text == "property").then(|| {
                    context
                        .file(file)
                        .unwrap()
                        .1
                        .symbol(NodeRef::new(parsed.arena.id(), file, node))
                        .unwrap()
                })
            })
            .unwrap();
        assert_ne!(property, value);
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_symbol_node_links(
            name,
            SymbolNodeLinks {
                resolved_symbol: Some(value),
            },
        ));
        assert!(context.store_mut_for_test().set_type_node_links(
            name,
            TypeNodeLinks {
                resolved_type: Some(string),
                outer_type_parameters: None,
            },
        ));

        assert_eq!(
            context.get_symbol_at_location(name).unwrap(),
            Some(property)
        );
        assert_eq!(
            context.get_symbol_at_location(declaration).unwrap(),
            Some(property)
        );
        assert_eq!(context.get_type_at_location(name).unwrap(), string);
        assert_eq!(
            context
                .store()
                .symbol_node_links(name)
                .and_then(|links| links.resolved_symbol),
            Some(value)
        );
    }

    #[test]
    fn jsx_attribute_names_recover_their_bound_declaration_without_cached_symbols() {
        let parsed = parse_jsx_source_file("const value = <div title=\"ready\" />;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_014);
        let mut context = context(&parsed, file);
        context.check_source_file(file).unwrap();
        let (declaration, name) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::JsxAttribute(attribute) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, attribute.name),
                ))
            })
            .unwrap();
        let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
        assert!(
            context
                .store_mut_for_test()
                .set_symbol_node_links(name, SymbolNodeLinks::default())
        );

        assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(symbol));
        assert_eq!(
            context
                .store()
                .symbol_node_links(name)
                .and_then(|links| links.resolved_symbol),
            None
        );
    }

    #[test]
    fn qualified_namespace_names_resolve_nested_exports_without_cached_links() {
        let parsed = parse_source_file(concat!(
            "declare namespace Outer {\n",
            "  export namespace Inner {\n",
            "    export interface Shape { value: string; }\n",
            "    export type Label = string;\n",
            "  }\n",
            "}\n",
            "declare const shape: Outer.Inner.Shape;\n",
            "declare const label: Outer.Inner.Label;\n",
            "declare const missing: Outer.Inner.Missing;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_008);
        let mut context = declaration_context(&parsed, file);

        let declaration_symbol = |name: &str| {
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let identifier = match &record.data {
                        NodeData::ModuleDeclaration(declaration) => declaration.name,
                        NodeData::InterfaceDeclaration(declaration) => declaration.name,
                        NodeData::TypeAliasDeclaration(declaration) => declaration.name,
                        _ => return None,
                    };
                    let NodeData::Identifier(identifier) = &parsed.arena.get(identifier)?.data
                    else {
                        return None;
                    };
                    (identifier.text == name).then(|| {
                        context
                            .file(file)
                            .unwrap()
                            .1
                            .symbol(NodeRef::new(parsed.arena.id(), file, node))
                            .unwrap()
                    })
                })
                .unwrap()
        };
        let outer = declaration_symbol("Outer");
        let inner = declaration_symbol("Inner");
        let shape = declaration_symbol("Shape");
        let label = declaration_symbol("Label");

        let qualified = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                let NodeData::QualifiedName(name) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(right) = &parsed.arena.get(name.right)?.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, name.left),
                    NodeRef::new(parsed.arena.id(), file, name.right),
                    right.text.as_str(),
                ))
            })
            .collect::<Vec<_>>();
        assert_eq!(qualified.len(), 6);

        for (name, left, right, text) in qualified {
            assert!(context.store().symbol_node_links(name).is_none());
            let actual = context.get_symbol_at_location(name).unwrap();
            let expected = match text {
                "Inner" => Some(inner),
                "Shape" => Some(shape),
                "Label" => Some(label),
                "Missing" => context
                    .store()
                    .unresolved_symbol_for_name_path(&[
                        EscapedName::source("Outer"),
                        EscapedName::source("Inner"),
                        EscapedName::source("Missing"),
                    ])
                    .unwrap(),
                _ => panic!("unexpected qualified member {text}"),
            };
            if text == "Inner" {
                assert_eq!(context.get_symbol_at_location(left).unwrap(), Some(outer));
            }
            assert_eq!(actual, expected);
            assert!(actual.is_some());
            assert_eq!(context.get_symbol_at_location(right).unwrap(), expected);
            assert!(context.store().symbol_node_links(name).is_none());
        }
    }

    #[test]
    fn qualified_namespace_imports_keep_alias_roots_and_resolve_exported_members() {
        let importer = parse_source_file(concat!(
            "import * as Types from './target';\n",
            "declare const value: Types.Item;\n",
            "declare const missing: Types.Missing;\n",
        ));
        let target = parse_source_file("export interface Item { value: string; }\n");
        assert!(
            importer.diagnostics.is_empty(),
            "{:?}",
            importer.diagnostics
        );
        assert!(target.diagnostics.is_empty(), "{:?}", target.diagnostics);
        let importer_file = FileId::new(6_009);
        let target_file = FileId::new(6_010);
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path) in [
            (importer_file, &importer, "\"/project/importer.d.ts\""),
            (target_file, &target, "\"/project/target.d.ts\""),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        true,
                        CanonicalModuleState::External,
                    ),
                )
                .unwrap();
        }
        for (file, parsed) in [(importer_file, &importer), (target_file, &target)] {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let specifier = importer
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::ImportDeclaration(import) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(
                    importer.arena.id(),
                    importer_file,
                    import.module_specifier,
                ))
            })
            .unwrap();
        let mut context = CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            vec![
                (importer_file, &importer.arena),
                (target_file, &target.arena),
            ],
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new([
                CanonicalModuleResolutionEntry::resolved(
                    specifier,
                    CanonicalResolvedModuleInput::new(
                        target_file,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                ),
            ]),
        )
        .unwrap();
        let alias = importer
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(record.data, NodeData::NamespaceImport(_)).then(|| {
                    context
                        .file(importer_file)
                        .unwrap()
                        .1
                        .symbol(NodeRef::new(importer.arena.id(), importer_file, node))
                        .unwrap()
                })
            })
            .unwrap();
        let item = target
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(record.data, NodeData::InterfaceDeclaration(_)).then(|| {
                    context
                        .file(target_file)
                        .unwrap()
                        .1
                        .symbol(NodeRef::new(target.arena.id(), target_file, node))
                        .unwrap()
                })
            })
            .unwrap();
        let target_module = context
            .file(target_file)
            .and_then(|(_, bound)| bound.symbol(bound.source_file()))
            .unwrap();
        assert_eq!(
            context.get_symbol_at_location(specifier).unwrap(),
            Some(target_module)
        );

        for (node, record) in importer.arena.iter() {
            let NodeData::QualifiedName(qualified) = &record.data else {
                continue;
            };
            let name = NodeRef::new(importer.arena.id(), importer_file, node);
            let root = NodeRef::new(importer.arena.id(), importer_file, qualified.left);
            let member = NodeRef::new(importer.arena.id(), importer_file, qualified.right);
            let NodeData::Identifier(identifier) =
                &importer.arena.get(qualified.right).unwrap().data
            else {
                unreachable!("qualified namespace members are identifiers")
            };
            assert_eq!(context.get_symbol_at_location(root).unwrap(), Some(alias));
            let actual = context.get_symbol_at_location(name).unwrap();
            let expected = if identifier.text == "Item" {
                Some(item)
            } else {
                let symbol = context
                    .store()
                    .unresolved_symbol_for_name_path(&[
                        EscapedName::source("Types"),
                        EscapedName::source("Missing"),
                    ])
                    .unwrap()
                    .unwrap();
                assert!(context.get_symbol_declarations(symbol).unwrap().is_empty());
                Some(symbol)
            };
            assert_eq!(actual, expected);
            assert_eq!(context.get_symbol_at_location(member).unwrap(), expected);
        }
    }

    #[test]
    fn imported_type_reference_names_preserve_alias_identity_cold_and_warm() {
        for (import, local_name, declaration_file) in [
            ("Item", "Item", false),
            ("Item as Local", "Local", false),
            ("Item", "Item", true),
            ("Item as Local", "Local", true),
        ] {
            let declaration = if declaration_file {
                format!("declare const result: {local_name};")
            } else {
                format!("const result: {local_name} = {{ value: 'ready' }};")
            };
            let importer = parse_source_file(&format!(
                "import type {{ {import} }} from './target';\n{declaration}\n"
            ));
            let target = parse_source_file("export interface Item { value: string; }\n");
            assert!(
                importer.diagnostics.is_empty(),
                "{:?}",
                importer.diagnostics
            );
            assert!(target.diagnostics.is_empty(), "{:?}", target.diagnostics);
            let importer_file = FileId::new(6_060);
            let target_file = FileId::new(6_061);
            let mut binder = CanonicalBinder::new();
            let importer_path = if declaration_file {
                "\"/project/importer.d.ts\""
            } else {
                "\"/project/importer.ts\""
            };
            for (file, parsed, path, declaration_file) in [
                (importer_file, &importer, importer_path, declaration_file),
                (target_file, &target, "\"/project/target.d.ts\"", true),
            ] {
                binder
                    .bind_source_file_with_facts(
                        &parsed.arena,
                        parsed.source_file,
                        file,
                        CanonicalSourceFileFacts::new(
                            EscapedName::source(path),
                            CanonicalSourceLanguage::TypeScript,
                            declaration_file,
                            CanonicalModuleState::External,
                        ),
                    )
                    .unwrap();
            }
            for (file, parsed) in [(importer_file, &importer), (target_file, &target)] {
                binder
                    .bind_typescript_declaration_slice(&parsed.arena, file)
                    .unwrap();
            }
            let specifier = importer
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::ImportDeclaration(import) = &record.data else {
                        return None;
                    };
                    Some(NodeRef::new(
                        importer.arena.id(),
                        importer_file,
                        import.module_specifier,
                    ))
                })
                .unwrap();
            let mut context = CanonicalCheckerContext::new_with_module_resolutions(
                binder.finish(),
                vec![
                    (importer_file, &importer.arena),
                    (target_file, &target.arena),
                ],
                CanonicalCheckerOptions::default(),
                CanonicalModuleResolutionManifestInput::new([
                    CanonicalModuleResolutionEntry::resolved(
                        specifier,
                        CanonicalResolvedModuleInput::new(
                            target_file,
                            CanonicalModuleResolutionMode::Esm,
                            CanonicalModuleResolutionMode::Esm,
                        ),
                    ),
                ]),
            )
            .unwrap();
            let import_declaration = importer
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(record.data, NodeData::ImportSpecifier(_)).then_some(NodeRef::new(
                        importer.arena.id(),
                        importer_file,
                        node,
                    ))
                })
                .unwrap();
            let target_declaration = target
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(record.data, NodeData::InterfaceDeclaration(_))
                        .then_some(NodeRef::new(target.arena.id(), target_file, node))
                })
                .unwrap();
            let alias = context
                .file(importer_file)
                .unwrap()
                .1
                .symbol(import_declaration)
                .unwrap();
            let target_symbol = context
                .file(target_file)
                .unwrap()
                .1
                .symbol(target_declaration)
                .unwrap();
            let (reference, name) = importer
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::TypeReferenceNode(reference) = &record.data else {
                        return None;
                    };
                    Some((
                        NodeRef::new(importer.arena.id(), importer_file, node),
                        NodeRef::new(importer.arena.id(), importer_file, reference.type_name),
                    ))
                })
                .unwrap();

            assert_ne!(alias, target_symbol);
            assert!(context.store().type_node_links(reference).is_none());
            assert!(context.store().symbol_node_links(reference).is_none());
            assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(alias));
            if declaration_file {
                assert!(context.store().type_node_links(reference).is_none());
                assert!(context.store().symbol_node_links(reference).is_none());
                assert!(context.store().symbol_node_links(name).is_none());
                continue;
            }
            let expected = context.get_declared_type_of_symbol(target_symbol).unwrap();
            assert_eq!(context.get_type_at_location(reference).unwrap(), expected);
            assert_eq!(context.get_type_at_location(name).unwrap(), expected);
            let type_links = context.store().type_node_links(reference).cloned();
            let symbol_links = context.store().symbol_node_links(reference).cloned();
            assert_eq!(
                symbol_links
                    .as_ref()
                    .and_then(|links| links.resolved_symbol),
                Some(target_symbol)
            );
            assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(alias));
            assert_eq!(
                context.get_symbol_declarations(alias).unwrap(),
                &[import_declaration]
            );
            assert_eq!(
                context.store().type_node_links(reference),
                type_links.as_ref()
            );
            assert_eq!(
                context.store().symbol_node_links(reference),
                symbol_links.as_ref()
            );
            assert!(context.store().symbol_node_links(name).is_none());
        }
    }

    #[test]
    fn module_aliases_preserve_immediate_targets_and_resolved_exports() {
        let importer = parse_source_file(concat!(
            "import { forwarded as local } from './target';\n",
            "import * as Types from './target';\n",
            "declare const result: typeof Types.Exposed;\n",
        ));
        let target = parse_source_file(concat!(
            "declare const value: number;\n",
            "export { value as forwarded };\n",
        ));
        assert!(
            importer.diagnostics.is_empty(),
            "{:?}",
            importer.diagnostics
        );
        assert!(target.diagnostics.is_empty(), "{:?}", target.diagnostics);
        let importer_file = FileId::new(6_023);
        let target_file = FileId::new(6_024);
        let mut binder = CanonicalBinder::new();

        for (file, parsed, path) in [
            (importer_file, &importer, "\"/project/aliases.d.ts\""),
            (target_file, &target, "\"/project/target.d.ts\""),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        true,
                        CanonicalModuleState::External,
                    ),
                )
                .unwrap();
        }
        for (file, parsed) in [(importer_file, &importer), (target_file, &target)] {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }

        let resolutions = importer
            .arena
            .iter()
            .filter_map(|(_, record)| {
                let NodeData::ImportDeclaration(import) = &record.data else {
                    return None;
                };
                Some(CanonicalModuleResolutionEntry::resolved(
                    NodeRef::new(importer.arena.id(), importer_file, import.module_specifier),
                    CanonicalResolvedModuleInput::new(
                        target_file,
                        CanonicalModuleResolutionMode::Esm,
                        CanonicalModuleResolutionMode::Esm,
                    ),
                ))
            })
            .collect::<Vec<_>>();
        let mut context = CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            vec![
                (importer_file, &importer.arena),
                (target_file, &target.arena),
            ],
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new(resolutions),
        )
        .unwrap();

        let (import_declaration, imported_name, local_name) = importer
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ImportSpecifier(import) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(importer.arena.id(), importer_file, node),
                    NodeRef::new(
                        importer.arena.id(),
                        importer_file,
                        import.property_name.unwrap(),
                    ),
                    NodeRef::new(importer.arena.id(), importer_file, import.name),
                ))
            })
            .unwrap();
        let forwarded_declaration = target
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(record.data, NodeData::ExportSpecifier(_)).then_some(NodeRef::new(
                    target.arena.id(),
                    target_file,
                    node,
                ))
            })
            .unwrap();
        let value_declaration = target
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(record.data, NodeData::VariableDeclaration(_)).then_some(NodeRef::new(
                    target.arena.id(),
                    target_file,
                    node,
                ))
            })
            .unwrap();
        let (local, forwarded, value, target_module) = {
            let importer = context.file(importer_file).unwrap().1;
            let target = context.file(target_file).unwrap().1;
            (
                importer.symbol(import_declaration).unwrap(),
                target.symbol(forwarded_declaration).unwrap(),
                target.symbol(value_declaration).unwrap(),
                target.symbol(target.source_file()).unwrap(),
            )
        };
        assert_ne!(local, forwarded);
        assert_ne!(forwarded, value);
        assert!(context.store_mut_for_test().set_alias_symbol_links(
            local,
            AliasSymbolLinks {
                immediate_target: Some(forwarded),
                alias_target: AliasTargetState::Resolved(value),
                ..AliasSymbolLinks::default()
            },
        ));
        for name in [imported_name, local_name] {
            assert!(context.store_mut_for_test().set_symbol_node_links(
                name,
                SymbolNodeLinks {
                    resolved_symbol: Some(value),
                },
            ));
        }

        assert_eq!(
            context.get_symbol_at_location(imported_name).unwrap(),
            Some(forwarded)
        );
        assert_eq!(
            context.get_symbol_at_location(local_name).unwrap(),
            Some(local)
        );
        for name in [imported_name, local_name] {
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(name)
                    .and_then(|links| links.resolved_symbol),
                Some(value)
            );
        }

        let resolved_exports = context.store_mut_for_test().alloc_symbol_table();
        assert_eq!(
            context.store_mut_for_test().insert_symbol(
                resolved_exports,
                EscapedName::source("Exposed"),
                value,
            ),
            Some(None)
        );
        assert!(context.store_mut_for_test().set_module_symbol_links(
            target_module,
            ModuleSymbolLinks {
                resolved_exports: Some(resolved_exports),
                ..ModuleSymbolLinks::default()
            },
        ));
        let (qualified, name) = importer
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::QualifiedName(qualified) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(importer.arena.id(), importer_file, node),
                    NodeRef::new(importer.arena.id(), importer_file, qualified.right),
                ))
            })
            .unwrap();
        let raw_exports = context
            .store()
            .symbol(target_module)
            .unwrap()
            .exports()
            .unwrap();
        assert!(
            context
                .store()
                .symbol_table(raw_exports)
                .unwrap()
                .get_source("Exposed")
                .is_none()
        );

        assert_eq!(
            context.get_symbol_at_location(qualified).unwrap(),
            Some(value)
        );
        assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(value));
        assert!(context.store().symbol_node_links(qualified).is_none());
    }

    #[test]
    fn qualified_namespace_roots_do_not_replace_cached_unknown_symbols() {
        let parsed = parse_source_file(concat!(
            "declare namespace Visible { export type Label = string; }\n",
            "declare const value: Visible.Label;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_011);
        let mut context = declaration_context(&parsed, file);
        let (qualified, root, member) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::QualifiedName(qualified) = &record.data else {
                    return None;
                };
                Some((
                    NodeRef::new(parsed.arena.id(), file, node),
                    NodeRef::new(parsed.arena.id(), file, qualified.left),
                    NodeRef::new(parsed.arena.id(), file, qualified.right),
                ))
            })
            .unwrap();
        let unknown = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .unknown_symbol;
        assert!(context.store_mut_for_test().set_symbol_node_links(
            root,
            SymbolNodeLinks {
                resolved_symbol: Some(unknown),
            },
        ));

        assert_eq!(context.get_symbol_at_location(root).unwrap(), None);
        assert_eq!(context.get_symbol_at_location(qualified).unwrap(), None);
        assert_eq!(context.get_symbol_at_location(member).unwrap(), None);
        assert_eq!(
            context
                .store()
                .symbol_node_links(root)
                .and_then(|links| links.resolved_symbol),
            Some(unknown)
        );

        assert!(
            context
                .store_mut_for_test()
                .set_symbol_node_links(root, SymbolNodeLinks::default())
        );
        assert!(context.store_mut_for_test().set_symbol_node_links(
            member,
            SymbolNodeLinks {
                resolved_symbol: Some(unknown),
            },
        ));
        assert!(context.get_symbol_at_location(qualified).unwrap().is_some());
        assert_eq!(context.get_symbol_at_location(member).unwrap(), None);
        assert_eq!(
            context
                .store()
                .symbol_node_links(member)
                .and_then(|links| links.resolved_symbol),
            Some(unknown)
        );
    }

    #[test]
    fn heritage_identifiers_reuse_resolved_base_types_and_symbols() {
        let parsed = parse_source_file(concat!(
            "interface Shape { item: string; }\n",
            "interface Child extends Shape { next: number; }\n",
            "class Base { value!: string; }\n",
            "class Derived extends Base { other!: number; }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_002);
        let mut context = context(&parsed, file);
        context.check_source_file(file).unwrap();

        let references = parsed
            .arena
            .iter()
            .filter_map(|(_, record)| {
                let NodeData::ExpressionWithTypeArguments(expression) = &record.data else {
                    return None;
                };
                let name = NodeRef::new(parsed.arena.id(), file, expression.expression);
                let NodeData::Identifier(identifier) = &parsed.arena.get(name.node)?.data else {
                    return None;
                };
                Some((name, identifier.text.as_str()))
            })
            .collect::<Vec<_>>();
        assert_eq!(references.len(), 2);

        for (reference, expected_name) in references {
            let symbol = context.get_symbol_at_location(reference).unwrap().unwrap();
            assert_eq!(context.symbol_to_string(symbol).unwrap(), expected_name);
            let type_ = context.get_type_at_location(reference).unwrap();
            assert_eq!(
                context
                    .store()
                    .declared_type_links(symbol)
                    .and_then(|links| links.declared_type),
                Some(type_)
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep source occurrence order, cache damage, and restored queries together.
    fn merged_heritage_identifiers_keep_source_slots_and_reject_changed_base_caches() {
        let first = parse_source_file(concat!(
            "interface First { first: number; } ",
            "interface Second { second: string; } ",
            "interface Merged extends First { own: boolean; }",
        ));
        let files = [FileId::new(147_220), FileId::new(147_221)];
        for (text, expected_order) in [
            (
                "interface Merged extends Second { added: number; }",
                [0_usize, 1].as_slice(),
            ),
            (
                concat!(
                    "interface Merged extends Second { added: number; } ",
                    "interface Merged extends First {} ",
                    "interface Merged extends Second {}",
                ),
                [0, 1, 0, 1].as_slice(),
            ),
        ] {
            let added = parse_source_file(text);
            let inputs = [(files[0], &first), (files[1], &added)];
            let mut binder = CanonicalBinder::new();
            for (file, parsed) in inputs {
                assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
                binder
                    .bind_source_file_with_facts(
                        &parsed.arena,
                        parsed.source_file,
                        file,
                        CanonicalSourceFileFacts::new(
                            EscapedName::source(if file == files[0] {
                                "\"/project/first.d.ts\""
                            } else {
                                "\"/project/added.d.ts\""
                            }),
                            CanonicalSourceLanguage::TypeScript,
                            true,
                            CanonicalModuleState::Script,
                        ),
                    )
                    .unwrap();
                binder
                    .bind_typescript_declaration_slice(&parsed.arena, file)
                    .unwrap();
            }
            let mut context = CanonicalCheckerContext::new(
                binder.finish(),
                inputs
                    .iter()
                    .map(|(file, parsed)| (*file, &parsed.arena))
                    .collect(),
                CanonicalCheckerOptions::default(),
            )
            .unwrap();
            let owners = ["First", "Second", "Merged"].map(|name| {
                let store = context.store();
                store
                    .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                    .unwrap()
                    .get_source(name)
                    .and_then(|symbol| store.get_merged_symbol(symbol))
                    .unwrap()
            });
            let [_, _, owner] = owners;
            let mut references = Vec::new();
            let mut raw_owners = Vec::new();
            for (file, parsed) in inputs {
                for (node, record) in parsed.arena.iter() {
                    match &record.data {
                        NodeData::InterfaceDeclaration(interface) => {
                            let NodeData::Identifier(name) =
                                &parsed.arena.get(interface.name).unwrap().data
                            else {
                                unreachable!();
                            };
                            if name.text == "Merged" {
                                raw_owners.push(
                                    context
                                        .file(file)
                                        .unwrap()
                                        .1
                                        .symbol(NodeRef::new(parsed.arena.id(), file, node))
                                        .unwrap(),
                                );
                            }
                        }
                        NodeData::ExpressionWithTypeArguments(expression) => {
                            let NodeData::Identifier(name) =
                                &parsed.arena.get(expression.expression).unwrap().data
                            else {
                                unreachable!();
                            };
                            let index = match name.text.as_str() {
                                "First" => 0,
                                "Second" => 1,
                                _ => unreachable!(),
                            };
                            references.push((
                                NodeRef::new(parsed.arena.id(), file, node),
                                NodeRef::new(parsed.arena.id(), file, expression.expression),
                                index,
                            ));
                        }
                        _ => {}
                    }
                }
            }
            assert_eq!(
                references
                    .iter()
                    .map(|(_, _, index)| *index)
                    .collect::<Vec<_>>(),
                expected_order,
            );
            assert_ne!(raw_owners[0], raw_owners[1]);
            for raw in raw_owners {
                assert_eq!(context.store().get_merged_symbol(raw), Some(owner));
            }
            let cold = (
                context.store().type_len(),
                context.store().checker_link_allocated_lengths(),
            );
            for &(_, name, _) in &references {
                assert_eq!(context.heritage_artifact_target(name), Ok(None));
            }
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                cold,
            );
            for file in files {
                context.check_source_file(file).unwrap();
            }
            assert!(context.diagnostics().is_empty());
            let types = owners.map(|symbol| context.get_declared_type_of_symbol(symbol).unwrap());
            let owner_type = types[2];
            let base_types = expected_order
                .iter()
                .map(|index| types[*index])
                .collect::<Vec<_>>();
            let provenance = context
                .store()
                .direct_interface_heritage_provenance(owner_type)
                .unwrap();
            assert_eq!(provenance.owner_symbol, owner);
            assert_eq!(
                provenance.bases,
                expected_order
                    .iter()
                    .map(|index| (owners[*index], types[*index]))
                    .collect::<Vec<_>>(),
            );
            let snapshot = |context: &CanonicalCheckerContext<'_>| {
                let store = context.store();
                let TypeData::Interface(interface) = store.type_payload(owner_type).unwrap().data()
                else {
                    unreachable!();
                };
                (
                    [
                        store.type_len(),
                        store.type_alias_len(),
                        store.symbol_len(),
                        store.signature_len(),
                        store.mapper_len(),
                        store.index_info_len(),
                        store.symbol_store().symbol_table_len(),
                    ],
                    store.checker_link_allocated_lengths().to_vec(),
                    interface.clone(),
                    store
                        .direct_interface_heritage_provenance(owner_type)
                        .cloned(),
                    references
                        .iter()
                        .flat_map(|(reference, name, _)| [reference, name])
                        .map(|node| {
                            (
                                store.type_node_links(*node).cloned(),
                                store.symbol_node_links(*node).cloned(),
                            )
                        })
                        .collect::<Vec<_>>(),
                    files.map(|file| {
                        store
                            .source_file_links(context.source_file(file).unwrap())
                            .cloned()
                    }),
                    context.diagnostics().clone(),
                )
            };
            let warm = snapshot(&context);
            for type_first in [false, true] {
                for &(_, name, index) in &references {
                    if type_first {
                        assert_eq!(context.get_type_at_location(name), Ok(types[index]));
                    }
                    assert_eq!(
                        context.get_symbol_at_location(name),
                        Ok(Some(owners[index]))
                    );
                    assert_eq!(context.get_type_at_location(name), Ok(types[index]));
                }
                assert_eq!(snapshot(&context), warm);
            }

            let mut reordered = base_types.clone();
            reordered.swap(0, 1);
            for damaged_bases in [reordered, base_types[..base_types.len() - 1].to_vec()] {
                assert!(context.store_mut_for_test().set_interface_base_resolution(
                    owner_type,
                    true,
                    None,
                    Some(damaged_bases),
                ));
                let damaged = snapshot(&context);
                for _ in 0..2 {
                    for &(_, name, _) in &references {
                        let error = CanonicalArtifactQueryError::InvalidType {
                            node: name,
                            type_: owner_type,
                        };
                        assert_eq!(context.get_symbol_at_location(name), Err(error));
                        assert_eq!(context.get_type_at_location(name), Err(error));
                    }
                    assert_eq!(snapshot(&context), damaged);
                }
                assert!(context.store_mut_for_test().set_interface_base_resolution(
                    owner_type,
                    true,
                    None,
                    Some(base_types.clone()),
                ));
                for &(_, name, index) in &references {
                    assert_eq!(
                        context.get_symbol_at_location(name),
                        Ok(Some(owners[index]))
                    );
                    assert_eq!(context.get_type_at_location(name), Ok(types[index]));
                }
                assert_eq!(snapshot(&context), warm);
            }
        }
    }

    #[test]
    fn enum_initializers_and_module_aliases_resolve_uncached_lexical_symbols() {
        let parsed = parse_source_file(concat!(
            "declare namespace Outer { ",
            "export namespace Inner {} export import Alias = Inner; }\n",
            "declare enum Kind { First = 1, Second = First, Third = (First) }\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_025);
        let mut context = declaration_context(&parsed, file);
        let (alias_reference, namespace) = {
            let alias = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::ImportEqualsDeclaration(import) = &record.data else {
                        return None;
                    };
                    Some(NodeRef::new(
                        parsed.arena.id(),
                        file,
                        import.module_reference,
                    ))
                })
                .unwrap();
            let namespace = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::ModuleDeclaration(module) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &parsed.arena.get(module.name)?.data else {
                        return None;
                    };
                    (name.text == "Inner").then(|| {
                        context
                            .file(file)
                            .unwrap()
                            .1
                            .symbol(NodeRef::new(parsed.arena.id(), file, node))
                            .unwrap()
                    })
                })
                .unwrap();
            (alias, namespace)
        };
        assert!(context.store().symbol_node_links(alias_reference).is_none());
        assert_eq!(
            context.get_symbol_at_location(alias_reference).unwrap(),
            Some(namespace)
        );
        assert!(context.store().symbol_node_links(alias_reference).is_none());

        let (first, references) = {
            let mut first = None;
            let mut references = Vec::new();
            for (node, record) in parsed.arena.iter() {
                let NodeData::EnumMember(member) = &record.data else {
                    continue;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(member.name).unwrap().data
                else {
                    panic!("enum members have identifier names")
                };
                match name.text.as_str() {
                    "First" => {
                        first = context.file(file).unwrap().1.symbol(NodeRef::new(
                            parsed.arena.id(),
                            file,
                            node,
                        ));
                    }
                    "Second" | "Third" => {
                        let initializer = member.initializer.unwrap();
                        let reference = match &parsed.arena.get(initializer).unwrap().data {
                            NodeData::ParenthesizedExpression(parenthesized) => {
                                parenthesized.expression
                            }
                            _ => initializer,
                        };
                        references.push(NodeRef::new(parsed.arena.id(), file, reference));
                    }
                    _ => unreachable!("the fixture contains only three enum members"),
                }
            }
            (first.unwrap(), references)
        };
        assert_eq!(references.len(), 2);
        let expected = context.get_declared_type_of_symbol(first).unwrap();

        for reference in references {
            assert!(context.store().symbol_node_links(reference).is_none());
            assert_eq!(
                context.get_symbol_at_location(reference).unwrap(),
                Some(first)
            );
            assert_eq!(context.get_type_at_location(reference).unwrap(), expected);
            assert!(context.store().symbol_node_links(reference).is_none());
        }
    }

    #[test]
    fn review_export_equals_artifacts_require_ready_direct_identifiers() {
        for (export, direct) in [
            ("export = value;", true),
            ("export default value;", false),
            ("export = (value);", false),
            ("export = value.member;", false),
            ("export = value();", false),
        ] {
            let parsed = parse_source_file(&format!("declare const value: number; {export}"));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(6_100);
            let mut context = export_equals_declaration_context(&parsed, file);
            let declaration =
                parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        matches!(record.data, NodeData::VariableDeclaration(_))
                            .then_some(NodeRef::new(parsed.arena.id(), file, node))
                    })
                    .unwrap();
            let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
            let reference = parsed.arena.iter().filter_map(|(node, record)| {
                matches!(&record.data, NodeData::Identifier(identifier) if identifier.text == "value")
                    .then_some(NodeRef::new(parsed.arena.id(), file, node))
            }).last().unwrap();
            let source = context.source_file(file).unwrap();
            let snapshot = |context: &CanonicalCheckerContext<'_>| {
                let store = context.store();
                (
                    [
                        store.type_len(),
                        store.symbol_len(),
                        store.signature_len(),
                        store.mapper_len(),
                        store.symbol_store().symbol_table_len(),
                    ],
                    store.checker_link_allocated_lengths(),
                    store.relation_state_snapshot(),
                    store.source_file_links(source).cloned(),
                    store.value_symbol_links(symbol).cloned(),
                    store.symbol_node_links(reference).cloned(),
                    store.type_node_links(reference).cloned(),
                    context.diagnostics().as_slice().to_vec(),
                )
            };
            let cold = snapshot(&context);
            for _ in 0..2 {
                assert_eq!(
                    context.uncached_artifact_reference_symbol(reference),
                    Ok(None),
                    "{export}"
                );
                if direct {
                    assert_eq!(context.get_symbol_at_location(reference), Ok(None));
                    assert!(
                        matches!(context.get_type_at_location(reference), Err(CanonicalArtifactQueryError::MissingType { node, .. }) if node == reference)
                    );
                }
                assert_eq!(snapshot(&context), cold, "{export}");
            }
            let expected = context.store().intrinsic_bootstrap().unwrap().number_type;
            assert!(context.store_mut_for_test().set_value_symbol_links(
                symbol,
                ValueSymbolLinks {
                    resolved_type: Some(expected),
                    ..ValueSymbolLinks::default()
                }
            ));
            let ready = snapshot(&context);
            for _ in 0..2 {
                assert_eq!(
                    context.uncached_artifact_reference_symbol(reference),
                    Ok(direct.then_some(symbol)),
                    "{export}"
                );
                if direct {
                    assert_eq!(context.get_symbol_at_location(reference), Ok(Some(symbol)));
                    assert_eq!(context.get_type_at_location(reference), Ok(expected));
                }
                assert_eq!(snapshot(&context), ready, "{export}");
            }
        }
    }

    fn export_equals_declaration_context(
        parsed: &ParseResult,
        file: FileId,
    ) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/exports.d.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    true,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keep the identity, corruption, and restored read together.
    fn export_equals_class_flags_cannot_select_a_different_cache_route() {
        let parsed = parse_source_file("declare class Value { value: number; } export = Value;");
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(149_510);
        let mut context = export_equals_declaration_context(&parsed, file);
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(record.data, NodeData::ClassDeclaration(_)).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
        let owner = context.store().get_merged_symbol(owner).unwrap();
        let exported = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::ExportAssignment(export) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(parsed.arena.id(), file, export.expression))
            })
            .unwrap();
        let members = context.get_nongeneric_class_members(owner).unwrap();
        assert_eq!(
            context.get_type_at_location(exported),
            Ok(members.shells().instance_type())
        );
        let owner_record = context.store().symbol(owner).unwrap();
        let flags = owner_record.flags();
        let check_flags = owner_record.check_flags();
        let type_links = context
            .store()
            .type_node_links(exported)
            .cloned()
            .unwrap_or_default();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(context.store_mut_for_test().set_symbol_flags(
            owner,
            SymbolFlags::FUNCTION,
            check_flags
        ));
        assert!(context.store_mut_for_test().set_type_node_links(
            exported,
            TypeNodeLinks {
                resolved_type: Some(number),
                ..TypeNodeLinks::default()
            },
        ));
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            let store = context.store();
            (
                [
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                ],
                store.checker_link_allocated_lengths(),
                store.declared_type_links(owner).cloned(),
                store.value_symbol_links(owner).cloned(),
                store.type_node_links(exported).cloned(),
                store.symbol_node_links(exported).cloned(),
                store.relation_state_snapshot(),
            )
        };
        let before = snapshot(&context);
        for _ in 0..2 {
            assert_eq!(context.store().source_symbol_flags(owner), Some(flags));
            assert!(
                context
                    .export_equals_declared_artifact_type(exported)
                    .is_err()
            );
            assert!(context.get_type_at_location(exported).is_err());
            assert_eq!(snapshot(&context), before);
            assert_eq!(
                context.store().symbol(owner).unwrap().flags(),
                SymbolFlags::FUNCTION
            );
        }
        assert!(
            context
                .store_mut_for_test()
                .set_symbol_flags(owner, flags, check_flags)
        );
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(exported, type_links)
        );
        assert_eq!(
            context.get_type_at_location(exported),
            Ok(members.shells().instance_type())
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn review_export_equals_artifacts_keep_the_nearest_lexical_value() {
        let parsed = parse_source_file(concat!(
            "declare const value: number; ",
            "declare module 'pkg' { const value: string; export = value; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_101);
        let mut context = declaration_context(&parsed, file);
        let declarations = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                matches!(record.data, NodeData::VariableDeclaration(_)).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .collect::<Vec<_>>();
        let [outer, inner] = declarations.as_slice() else {
            panic!("expected two scoped declarations")
        };
        let outer = context.file(file).unwrap().1.symbol(*outer).unwrap();
        let inner = context.file(file).unwrap().1.symbol(*inner).unwrap();
        assert_ne!(outer, inner);
        let reference = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::ExportAssignment(export) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(parsed.arena.id(), file, export.expression))
            })
            .unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            outer,
            ValueSymbolLinks {
                resolved_type: Some(number),
                ..ValueSymbolLinks::default()
            }
        ));
        let source = context.source_file(file).unwrap();
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            let store = context.store();
            (
                [
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                    store.symbol_store().symbol_table_len(),
                ],
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
                store.source_file_links(source).cloned(),
                [outer, inner].map(|symbol| store.value_symbol_links(symbol).cloned()),
                store.symbol_node_links(reference).cloned(),
                store.type_node_links(reference).cloned(),
                context.diagnostics().as_slice().to_vec(),
            )
        };
        let cold_inner = snapshot(&context);
        for _ in 0..2 {
            assert_eq!(context.get_symbol_at_location(reference), Ok(None));
            assert!(
                matches!(context.get_type_at_location(reference), Err(CanonicalArtifactQueryError::MissingType { node, .. }) if node == reference)
            );
            assert_eq!(snapshot(&context), cold_inner);
        }
        assert!(context.store_mut_for_test().set_value_symbol_links(
            inner,
            ValueSymbolLinks {
                resolved_type: Some(string),
                ..ValueSymbolLinks::default()
            }
        ));
        let ready = snapshot(&context);
        for _ in 0..2 {
            assert_eq!(context.get_symbol_at_location(reference), Ok(Some(inner)));
            assert_eq!(context.get_type_at_location(reference), Ok(string));
            assert_eq!(snapshot(&context), ready);
        }
    }

    #[test]
    fn review_export_equals_artifacts_keep_alias_identity_without_cold_resolution() {
        let parsed = parse_source_file(concat!(
            "declare namespace Local { export const value: number; } ",
            "import Alias = Local; export = Alias;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_102);
        let mut context = export_equals_declaration_context(&parsed, file);
        let namespace = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(record.data, NodeData::ModuleDeclaration(_)).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let import =
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(record.data, NodeData::ImportEqualsDeclaration(_))
                        .then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
        let reference = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::ExportAssignment(export) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(parsed.arena.id(), file, export.expression))
            })
            .unwrap();
        let namespace = context.file(file).unwrap().1.symbol(namespace).unwrap();
        let alias = context.file(file).unwrap().1.symbol(import).unwrap();
        assert_ne!(alias, namespace);
        assert!(
            context
                .store()
                .symbol(alias)
                .unwrap()
                .flags()
                .contains(SymbolFlags::ALIAS)
        );
        let expected = context.get_type_of_module_value(namespace).unwrap();
        let source = context.source_file(file).unwrap();
        let snapshot = |context: &CanonicalCheckerContext<'_>| {
            let store = context.store();
            (
                [
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                    store.symbol_store().symbol_table_len(),
                ],
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
                store.source_file_links(source).cloned(),
                [alias, namespace].map(|symbol| store.value_symbol_links(symbol).cloned()),
                store.alias_symbol_links(alias).cloned(),
                store.symbol_node_links(reference).cloned(),
                store.type_node_links(reference).cloned(),
                context.diagnostics().as_slice().to_vec(),
            )
        };
        let cold_alias = snapshot(&context);
        for _ in 0..2 {
            assert_eq!(context.get_symbol_at_location(reference), Ok(None));
            assert!(
                matches!(context.get_type_at_location(reference), Err(CanonicalArtifactQueryError::MissingType { node, .. }) if node == reference)
            );
            assert_eq!(snapshot(&context), cold_alias);
        }
        assert!(context.store_mut_for_test().set_value_symbol_links(
            alias,
            ValueSymbolLinks {
                resolved_type: Some(expected),
                ..ValueSymbolLinks::default()
            }
        ));
        let ready = snapshot(&context);
        for _ in 0..2 {
            assert_eq!(context.get_symbol_at_location(reference), Ok(Some(alias)));
            assert_eq!(context.get_type_at_location(reference), Ok(expected));
            assert_eq!(snapshot(&context), ready);
        }
        let foreign_parsed = parse_source_file("");
        let foreign_context = declaration_context(&foreign_parsed, FileId::new(6_103));
        let foreign = foreign_context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        assert_eq!(
            context.validate_artifact_type(reference, foreign),
            Err(CanonicalArtifactQueryError::InvalidType {
                node: reference,
                type_: foreign
            })
        );
        assert!(!context.store_mut_for_test().set_value_symbol_links(
            alias,
            ValueSymbolLinks {
                resolved_type: Some(foreign),
                ..ValueSymbolLinks::default()
            }
        ));
        assert_eq!(snapshot(&context), ready);
        assert_eq!(context.get_symbol_at_location(reference), Ok(Some(alias)));
        assert_eq!(context.get_type_at_location(reference), Ok(expected));
        assert_eq!(snapshot(&context), ready);
    }

    #[test]
    fn lexical_this_queries_reuse_the_canonical_global_symbol_and_type() {
        let parsed = parse_source_file("var _this = 1; var capture = () => this;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_026);
        let mut context = context(&parsed, file);
        let this = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ThisKeyword).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let symbol = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .global_this_symbol;
        let expected = context.global_types().global_this_value_type;

        assert_eq!(context.get_type_at_location(this).unwrap(), expected);
        assert_eq!(context.get_symbol_at_location(this).unwrap(), Some(symbol));
        assert_eq!(
            context
                .store()
                .symbol_node_links(this)
                .and_then(|links| links.resolved_symbol),
            Some(symbol)
        );
        let warm = (
            context.store().type_len(),
            context.store().symbol_len(),
            context.store().checker_link_allocated_lengths(),
        );

        assert_eq!(context.get_type_at_location(this).unwrap(), expected);
        assert_eq!(context.get_symbol_at_location(this).unwrap(), Some(symbol));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            warm
        );
    }

    #[test]
    fn assignment_targets_and_global_undefined_retain_their_public_symbols() {
        let parsed = parse_source_file(concat!(
            "var target: { value: number } = { value: 1 };\n",
            "target = { value: 2 };\n",
            "const missing = undefined;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_003);
        let mut context = context(&parsed, file);
        context.check_source_file(file).unwrap();

        let target = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::BinaryExpression(binary) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(parsed.arena.id(), file, binary.left))
            })
            .unwrap();
        let target_symbol = context
            .file(file)
            .unwrap()
            .1
            .locals(context.source_file(file).unwrap().node_ref())
            .and_then(|locals| context.store().symbol_table(locals))
            .and_then(|locals| locals.get_source("target"))
            .unwrap();
        assert_eq!(
            context.get_symbol_at_location(target).unwrap(),
            Some(target_symbol)
        );

        let undefined = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(&record.data, NodeData::Identifier(identifier) if identifier.text == "undefined")
                    .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        assert_eq!(
            context.get_symbol_at_location(undefined).unwrap(),
            Some(
                context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .undefined_symbol
            )
        );
    }

    #[test]
    fn unresolved_names_hide_unknown_symbols_but_keep_their_error_types() {
        let parsed = parse_source_file("const first = missing; const second = absent;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(6_007);
        let mut context = context(&parsed, file);
        context.check_source_file(file).unwrap();
        let (unknown, error_type) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.unknown_symbol, bootstrap.error_type)
        };

        let unresolved = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                matches!(
                    &record.data,
                    NodeData::Identifier(identifier)
                        if matches!(identifier.text.as_str(), "missing" | "absent")
                )
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .collect::<Vec<_>>();
        assert_eq!(unresolved.len(), 2);
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2304, 2304]
        );

        for node in unresolved {
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(node)
                    .and_then(|links| links.resolved_symbol),
                Some(unknown)
            );
            assert_eq!(context.get_symbol_at_location(node).unwrap(), None);
            assert_eq!(context.get_type_at_location(node).unwrap(), error_type);
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(node)
                    .and_then(|links| links.resolved_symbol),
                Some(unknown)
            );
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Compare cold reads, raw annotations, and warm state in each strictness mode.
    fn declaration_file_optional_property_names_preserve_raw_annotations_and_lazy_siblings() {
        let parsed = parse_source_file(concat!(
            "interface Model<T> { value?: T; fixed?: string; required: T; ",
            "unused?: T extends string ? number : boolean; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);

        for (index, (strict_null_checks, exact_optional_property_types)) in
            [(true, true), (true, false), (false, false)]
                .into_iter()
                .enumerate()
        {
            let file = FileId::new(6_260 + u32::try_from(index).unwrap());
            let mut context = context_with_source_kind(
                &parsed,
                file,
                CanonicalCheckerOptions {
                    intrinsic: IntrinsicBootstrapOptions {
                        strict_null_checks,
                        exact_optional_property_types,
                    },
                    ..CanonicalCheckerOptions::default()
                },
                true,
            );
            let properties = parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    let (name, annotation) = match &record.data {
                        NodeData::PropertySignatureDeclaration(property) => {
                            (property.name, property.type_)
                        }
                        NodeData::PropertyDeclaration(property) => (property.name, property.type_?),
                        _ => return None,
                    };
                    let declaration = NodeRef::new(parsed.arena.id(), file, node);
                    Some((
                        NodeRef::new(parsed.arena.id(), file, name),
                        NodeRef::new(parsed.arena.id(), file, annotation),
                        context.file(file).unwrap().1.symbol(declaration).unwrap(),
                    ))
                })
                .collect::<Vec<_>>();
            assert_eq!(properties.len(), 4);
            let parameter = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == SyntaxKind::TypeParameter).then(|| {
                        context
                            .file(file)
                            .unwrap()
                            .1
                            .symbol(NodeRef::new(parsed.arena.id(), file, node))
                            .unwrap()
                    })
                })
                .unwrap();
            let (string, undefined, missing, sentinel) = {
                let bootstrap = context.store().intrinsic_bootstrap().unwrap();
                (
                    bootstrap.string_type,
                    bootstrap.undefined_type,
                    bootstrap.missing_type,
                    bootstrap.undefined_or_missing_type,
                )
            };
            assert_ne!(undefined, missing);
            assert_eq!(
                sentinel,
                if exact_optional_property_types {
                    missing
                } else {
                    undefined
                }
            );
            for (name, annotation, symbol) in &properties {
                assert!(context.store().type_node_links(*name).is_none());
                assert!(context.store().type_node_links(*annotation).is_none());
                assert!(context.store().value_symbol_links(*symbol).is_none());
            }

            let mut results = Vec::new();
            for (name, annotation, symbol) in &properties[..3] {
                let NodeData::Identifier(identifier) = &parsed.arena.get(name.node).unwrap().data
                else {
                    panic!("the property name must be an identifier")
                };
                let optional = identifier.text != "required";
                let read_type = context.get_type_at_location(*name).unwrap();
                let raw_type = context.get_type_from_type_node(*annotation).unwrap();
                let (expected_raw, expected_text) = if identifier.text == "fixed" {
                    (
                        string,
                        if strict_null_checks {
                            "string | undefined"
                        } else {
                            "string"
                        },
                    )
                } else {
                    (
                        context
                            .store()
                            .declared_type_links(parameter)
                            .unwrap()
                            .declared_type
                            .unwrap(),
                        if strict_null_checks && optional {
                            "T | undefined"
                        } else {
                            "T"
                        },
                    )
                };
                assert_eq!(raw_type, expected_raw);
                assert_eq!(context.type_to_string(read_type).unwrap(), expected_text);
                if strict_null_checks && optional {
                    let TypeData::Union(union) =
                        context.store().type_payload(read_type).unwrap().data()
                    else {
                        panic!("an optional declaration name must have a canonical union")
                    };
                    assert_eq!(union.union.types.len(), 2);
                    assert!(union.union.types.contains(&raw_type));
                    assert!(union.union.types.contains(&sentinel));
                    assert!(
                        !union
                            .union
                            .types
                            .contains(&if exact_optional_property_types {
                                undefined
                            } else {
                                missing
                            })
                    );
                } else {
                    assert_eq!(read_type, raw_type);
                }
                assert!(
                    context
                        .store()
                        .type_node_links(*annotation)
                        .is_none_or(|links| {
                            links.resolved_type == Some(raw_type)
                                && links.outer_type_parameters.is_none()
                        })
                );
                assert!(context.store().value_symbol_links(*symbol).is_none());
                results.push((*name, *annotation, read_type, raw_type));
            }

            let source = context.source_file(file).unwrap();
            let snapshot = |context: &CanonicalCheckerContext<'_>| {
                let store = context.store();
                (
                    [
                        store.type_len(),
                        store.type_alias_len(),
                        store.mapper_len(),
                        store.symbol_len(),
                        store.symbol_store().symbol_table_len(),
                        store.signature_len(),
                        store.index_info_len(),
                        store.intrinsic_bootstrap().unwrap().union_cache_len(),
                    ],
                    store.checker_link_allocated_lengths(),
                    store.source_file_links(source).cloned(),
                    properties
                        .iter()
                        .map(|(name, annotation, symbol)| {
                            (
                                store.type_node_links(*name).cloned(),
                                store.type_node_links(*annotation).cloned(),
                                store.value_symbol_links(*symbol).cloned(),
                            )
                        })
                        .collect::<Vec<_>>(),
                )
            };
            let warm = snapshot(&context);
            for _ in 0..2 {
                for (name, annotation, read_type, raw_type) in &results {
                    assert_eq!(context.get_type_at_location(*name), Ok(*read_type));
                    assert_eq!(context.get_type_from_type_node(*annotation), Ok(*raw_type));
                }
                assert_eq!(snapshot(&context), warm);
            }
            let (unused_name, unused_annotation, unused_symbol) = properties[3];
            assert!(context.store().type_node_links(unused_name).is_none());
            assert!(context.store().type_node_links(unused_annotation).is_none());
            assert!(context.store().value_symbol_links(unused_symbol).is_none());
            assert!(
                context
                    .store()
                    .source_file_links(source)
                    .is_none_or(|links| !links.type_checked)
            );
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn optional_property_queries_build_read_unions_without_changing_write_types() {
        let parsed = parse_source_file(concat!(
            "declare function accept(input: { value?: string }): void;\n",
            "accept({ value: undefined });\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);

        for (index, (strict_null_checks, exact_optional_property_types)) in
            [(true, true), (true, false), (false, false)]
                .into_iter()
                .enumerate()
        {
            let file = FileId::new(6_004 + u32::try_from(index).unwrap());
            let mut context = context_with_options(
                &parsed,
                file,
                CanonicalCheckerOptions {
                    intrinsic: IntrinsicBootstrapOptions {
                        strict_null_checks,
                        exact_optional_property_types,
                    },
                    ..CanonicalCheckerOptions::default()
                },
            );
            context.check_source_file(file).unwrap();
            let (declaration, name) = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::PropertyDeclaration(property) = &record.data else {
                        return None;
                    };
                    let question = property.postfix_token?;
                    (parsed.arena.get(question)?.kind == SyntaxKind::QuestionToken).then_some((
                        NodeRef::new(parsed.arena.id(), file, node),
                        NodeRef::new(parsed.arena.id(), file, property.name),
                    ))
                })
                .unwrap();
            let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
            let write_type = context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type)
                .unwrap();
            let (string, sentinel) = {
                let bootstrap = context.store().intrinsic_bootstrap().unwrap();
                (bootstrap.string_type, bootstrap.undefined_or_missing_type)
            };
            assert_eq!(write_type, string);

            let read_type = context.get_type_at_location(name).unwrap();
            if strict_null_checks {
                let TypeData::Union(union) =
                    context.store().type_payload(read_type).unwrap().data()
                else {
                    panic!("strict optional properties must have a canonical read union")
                };
                assert_eq!(union.union.types.len(), 2);
                assert!(union.union.types.contains(&string));
                assert!(union.union.types.contains(&sentinel));
                assert_eq!(
                    context.type_to_string(read_type).unwrap(),
                    "string | undefined"
                );
            } else {
                assert_eq!(read_type, write_type);
            }
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .and_then(|links| links.resolved_type),
                Some(write_type)
            );

            let warm_counts = (
                context.store().type_len(),
                context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .union_cache_len(),
            );
            assert_eq!(context.get_type_at_location(name).unwrap(), read_type);
            assert_eq!(
                (
                    context.store().type_len(),
                    context
                        .store()
                        .intrinsic_bootstrap()
                        .unwrap()
                        .union_cache_len(),
                ),
                warm_counts
            );
        }
    }
}
