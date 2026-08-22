//! Production location queries used by semantic fixture artifacts.
//!
//! The canonical binder attaches declaration symbols to declaration nodes,
//! while checker caches attach reference symbols to expressions and type
//! references. Artifact walkers normally visit the identifier inside those
//! nodes, so these queries preserve the existing graph instead of constructing
//! replacement symbols or types.

use ts_ast::{FileId, Node, NodeArena, NodeArenaRevision, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{BoundFile, SemanticSymbolId, SymbolFlags};

use super::{
    AliasTargetState, CanonicalAliasQueryError, CanonicalCheckerContext, DeclaredTypeError,
    SourceCheckError, TypeData, TypeId, type_records::TypeRecord,
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
        }
    }
}

impl std::error::Error for CanonicalArtifactQueryError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::SourceCheck(error) => Some(error),
            Self::DeclaredType(error) => Some(error),
            Self::Alias(error) => Some(error),
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
        self.prepare_artifact_location(node)?;

        if let Some(type_) = self.cached_artifact_type(node)? {
            return Ok(type_);
        }

        if let Some((type_, _)) = self.heritage_artifact_target(node)? {
            return self.validate_artifact_type(node, type_);
        }

        let (kind, is_type_node, parent) = {
            let (arena, bound, record) = self.validated_artifact_node(node)?;
            (
                record.kind,
                is_type_syntax(&record.data),
                location_parent(arena, bound, node, record)?,
            )
        };

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
                | LocationParent::QualifiedName(parent) => Some(parent),
                LocationParent::Declaration(_) | LocationParent::AliasedPropertyName(_) => None,
            };
            if let Some(parent_node) = parent_node {
                if let Some(type_) = self.cached_artifact_type(parent_node)? {
                    return Ok(type_);
                }
                if matches!(parent, LocationParent::TypeReference(_)) {
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
                | NodeData::ObjectLiteralExpression(_)
                | NodeData::JsxElement(_)
                | NodeData::JsxOpeningElement(_)
                | NodeData::JsxClosingElement(_)
                | NodeData::JsxSelfClosingElement(_)
                | NodeData::JsxFragment(_)
                | NodeData::JsxOpeningFragment(_)
                | NodeData::JsxClosingFragment(_)
        ) {
            return Ok(None);
        }

        if let Some(symbol) = self.cached_artifact_symbol(node)? {
            return Ok(Some(symbol));
        }

        if let Some((_, symbol)) = self.heritage_artifact_target(node)? {
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
            Some(
                LocationParent::PropertyAccess(access)
                | LocationParent::ElementAccess(access)
                | LocationParent::QualifiedName(access),
            ) => self.cached_artifact_symbol(access),
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
        let name = record.name().escaped_display().to_string();
        if !record.flags().intersects(
            SymbolFlags::PROPERTY
                | SymbolFlags::METHOD
                | SymbolFlags::ACCESSOR
                | SymbolFlags::ENUM_MEMBER,
        ) {
            return Ok(name);
        }

        let mut names = vec![name];
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
            names.push(record.name().escaped_display().to_string());
            owner = record.parent();
        }
        names.reverse();
        Ok(names.join("."))
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
        if self.store().symbol(symbol).is_none() {
            return Err(CanonicalArtifactQueryError::InvalidSymbol { node, symbol });
        }
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
                NodeData::VariableDeclaration(variable) => variable.type_,
                NodeData::ParameterDeclaration(parameter) => parameter.type_,
                NodeData::PropertyDeclaration(property) => property.type_,
                NodeData::PropertySignatureDeclaration(property) => Some(property.type_),
                _ => None,
            }
            .map(|annotation| NodeRef::new(declaration.arena, declaration.file, annotation))
        };
        let Some(annotation) = annotation else {
            return Ok(None);
        };
        let type_ = self.get_type_from_type_node(annotation)?;
        self.validate_artifact_type(node, type_).map(Some)
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
                | NodeData::BigIntLiteral(_)
                | NodeData::BinaryExpression(_)
                | NodeData::CallExpression(_)
                | NodeData::ClassDeclaration(_)
                | NodeData::ClassExpression(_)
                | NodeData::ConditionalExpression(_)
                | NodeData::ElementAccessExpression(_)
                | NodeData::EnumDeclaration(_)
                | NodeData::EnumMember(_)
                | NodeData::FunctionDeclaration(_)
                | NodeData::FunctionExpression(_)
                | NodeData::Identifier(_)
                | NodeData::ImportClause(_)
                | NodeData::ImportSpecifier(_)
                | NodeData::InterfaceDeclaration(_)
                | NodeData::KeywordExpression(_)
                | NodeData::MethodDeclaration(_)
                | NodeData::MethodSignatureDeclaration(_)
                | NodeData::NewExpression(_)
                | NodeData::NoSubstitutionTemplateLiteral(_)
                | NodeData::NonNullExpression(_)
                | NodeData::NumericLiteral(_)
                | NodeData::ObjectLiteralExpression(_)
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
                | NodeData::SatisfiesExpression(_)
                | NodeData::ShorthandPropertyAssignment(_)
                | NodeData::StringLiteral(_)
                | NodeData::TypeAliasDeclaration(_)
                | NodeData::TypeAssertion(_)
                | NodeData::TypeOfExpression(_)
                | NodeData::TypeParameterDeclaration(_)
                | NodeData::VariableDeclaration(_)
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
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::CanonicalCheckerContext;
    use crate::semantic::{CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData};

    fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        context_with_options(parsed, file, CanonicalCheckerOptions::default())
    }

    fn context_with_options(
        parsed: &ParseResult,
        file: FileId,
        options: CanonicalCheckerOptions,
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
                    false,
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
