//! Production location queries used by semantic fixture artifacts.
//!
//! The canonical binder attaches declaration symbols to declaration nodes,
//! while checker caches attach reference symbols to expressions and type
//! references. Artifact walkers normally visit the identifier inside those
//! nodes, so these queries preserve the existing graph instead of constructing
//! replacement symbols or types.

use ts_ast::{FileId, Node, NodeArena, NodeArenaRevision, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    BoundFile, CanonicalNameResolver, CanonicalResolutionLocation, InternalSymbolName,
    SemanticSymbolId, SymbolFlags,
};
use ts_jsnum::PseudoBigInt;

use super::{
    AliasTargetState, CanonicalAliasQueryError, CanonicalCheckerContext, DeclaredTypeError,
    SourceCheckError, TypeData, TypeId, TypeNodeLinks,
    source_callables::{StoredSourceCallableValidation, validate_stored_source_callable},
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
        let declaration = self.prepare_artifact_type_location(node)?;

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

        if let Some(type_) = self.literal_annotation_artifact_type(node)? {
            return Ok(type_);
        }

        if let Some(type_) = self.arrow_artifact_type(node)? {
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

        if let Some(LocationParent::Declaration(declaration)) = parent
            && let Some(type_) = self.module_declaration_artifact_type(node, declaration)?
        {
            return Ok(type_);
        }

        if supports_type_location(&self.validated_artifact_node(node)?.2.data)
            && let Some(type_) = self.cached_artifact_type(node)?
        {
            return Ok(type_);
        }

        if let Some((type_, _)) = self.heritage_artifact_target(node)? {
            return self.validate_artifact_type(node, type_);
        }

        if is_type_node {
            return self
                .get_type_from_type_node(node)
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
                        .get_type_from_type_node(parent_node)
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
    ///
    /// # Errors
    ///
    /// Returns an exact provenance or source-checking error when the query
    /// cannot prove that its answer belongs to this checker program.
    pub fn get_symbol_at_location(
        &mut self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        self.prepare_artifact_location(node)?;

        if matches!(
            &self.validated_artifact_node(node)?.2.data,
            NodeData::ArrowFunction(_)
                | NodeData::BinaryExpression(_)
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

        if let Some(symbol) = self.expando_artifact_symbol(node)? {
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
        {
            return Err(CanonicalArtifactQueryError::UnsupportedNode {
                node,
                kind: record.kind,
            });
        }
        let declaration = self.type_declaration_artifact_symbol(node)?;
        self.preflight_literal_annotation_nodes(node)?;
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

    fn type_declaration_artifact_symbol(
        &self,
        node: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, CanonicalArtifactQueryError> {
        let (symbol, declaration, is_enum) = {
            let (arena, bound, record) = self.validated_artifact_node(node)?;
            let declaration = if matches!(
                record.data,
                NodeData::ClassDeclaration(_) | NodeData::EnumDeclaration(_)
            ) {
                node
            } else if let Some(parent) = record.parent {
                let Some(parent_record) = arena.get(parent) else {
                    return Ok(None);
                };
                if !matches!(
                    parent_record.data,
                    NodeData::ClassDeclaration(_) | NodeData::EnumDeclaration(_)
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
        } else if let Some(cached) = cached
            && super::declared::cached_class_type(self.store(), symbol)? != Some(cached)
        {
            return Err(CanonicalArtifactQueryError::InvalidType {
                node,
                type_: cached,
            });
        }
        Ok(Some(symbol))
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
        if !super::source_namespaces::has_pure_module_flags(record.flags()) {
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
        let Some(mut owner) = owner else {
            return Ok(None);
        };

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
            let type_ = self.validate_artifact_type(node, type_)?;
            if !flags.contains(SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL)
                || !self.options().intrinsic.strict_null_checks
            {
                return Ok(Some(type_));
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
                return Ok(Some(type_));
            }

            let read_type = self.artifact_union_type(&[type_, sentinel])?;
            return self.validate_artifact_type(node, read_type).map(Some);
        }

        if flags.intersects(SymbolFlags::PROPERTY)
            && let Some(type_) = self.object_literal_property_type(node, symbol)?
        {
            return Ok(Some(type_));
        }

        if let Some(type_) = self.declaration_file_annotation_type(node, symbol)? {
            return Ok(Some(type_));
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

        if flags.intersects(SymbolFlags::TYPE) {
            return self
                .get_declared_type_of_symbol(symbol)
                .map_err(CanonicalArtifactQueryError::from)
                .and_then(|type_| self.validate_artifact_type(node, type_))
                .map(Some);
        }

        Ok(None)
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
            let (_, bound, record) = self.validated_artifact_node(declaration)?;
            if !bound
                .source_facts()
                .is_some_and(ts_binder::CanonicalSourceFileFacts::is_declaration_file)
            {
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
        let type_ = self.get_type_from_type_node(annotation)?;
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
        CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, IntrinsicBootstrapOptions,
        ModuleSymbolLinks, SymbolNodeLinks, TypeData, TypeNodeLinks, ValueSymbolLinks,
        types::ObjectFlags,
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
            let expected = match text {
                "Inner" => Some(inner),
                "Shape" => Some(shape),
                "Label" => Some(label),
                "Missing" => None,
                _ => panic!("unexpected qualified member {text}"),
            };
            if text == "Inner" {
                assert_eq!(context.get_symbol_at_location(left).unwrap(), Some(outer));
            }
            assert_eq!(context.get_symbol_at_location(name).unwrap(), expected);
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
            let expected = (identifier.text == "Item").then_some(item);

            assert_eq!(context.get_symbol_at_location(root).unwrap(), Some(alias));
            assert_eq!(context.get_symbol_at_location(name).unwrap(), expected);
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
            "declare const result: Types.Exposed;\n",
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
