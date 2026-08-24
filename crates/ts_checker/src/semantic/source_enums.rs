//! Source-statement planning for canonical top-level and function-local enums.
//!
//! This leaf deliberately does not install source dispatch. The integration
//! hook is small: register this module from `semantic/mod.rs`, retain a
//! [`SourceEnumPlan`] for every `EnumDeclaration` during the source prepass,
//! then call [`execute_top_level_enum`] at that statement. Function-local enums
//! instead use [`plan_local_enum`] and [`execute_local_enum`], retaining their
//! exact function-owned binder scope. Const-only callers use
//! [`plan_local_const_enum`] and [`execute_local_const_enum`]. The returned
//! [`CanonicalEnumSemantics::value_type`] is the value read for the enum name;
//! member reads use each member's `fresh_type`.
//!
//! Planning is allocation-free. It proves the source statement, parser-owned
//! cache slots, binder/export route, and the canonical enum's exact cold or
//! warm state before source execution can write. Execution replans before
//! delegating publication to `enums`, whose publisher atomically materializes
//! the declared/value identities and all enum-member links.

use std::collections::HashSet;

use ts_ast::{Node, NodeData, NodeRef, SyntaxKind};
use ts_binder::{BoundFile, CheckFlags, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost,
    declared::preflight_node,
    enums::{
        self, CanonicalEnumSemantics, EnumMemberDiagnostic, EnumTypeError, EnumTypeInvariant,
        EnumTypeUnsupported,
    },
};

/// Binder route for the enum's value/type owner.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceEnumExportRoute {
    /// A script/global or non-exported external-module declaration.
    Local,
    /// A declaration reached through the binder's export-local symbol.
    Exported {
        local_symbol: SemanticSymbolId,
        source_symbol: SemanticSymbolId,
        /// Distinguishes an `export` token from an implicit ambient export.
        explicitly_exported: bool,
    },
}

/// Immutable syntax and binder identities for one enum member.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceEnumMemberPlan {
    pub(super) declaration: NodeRef,
    pub(super) name: NodeRef,
    /// Symbol recorded directly by the bound declaration.
    pub(super) declaration_symbol: SemanticSymbolId,
    /// Canonical symbol that owns declared/value links.
    pub(super) symbol: SemanticSymbolId,
}

/// Allocation-free plan for one bounded top-level or local enum statement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceEnumPlan {
    pub(super) declaration: NodeRef,
    pub(super) name: NodeRef,
    /// The actual binder locals owner for an admitted function-local enum.
    pub(super) lexical_owner: Option<NodeRef>,
    /// Symbol recorded directly by the bound declaration.
    pub(super) declaration_symbol: SemanticSymbolId,
    /// Canonical enum owner used by declared/value type caches.
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) members: Vec<SourceEnumMemberPlan>,
    pub(super) diagnostics: Vec<EnumMemberDiagnostic>,
    pub(super) export_route: SourceEnumExportRoute,
    pub(super) is_const: bool,
    pub(super) is_ambient: bool,
}

impl SourceEnumPlan {
    /// Returns whether this function-owned enum produces unreachable runtime code.
    pub(super) fn is_unreachable_runtime_declaration(
        &self,
        bound: &BoundFile,
        preserve_const_enums: bool,
    ) -> Result<bool, SourceEnumError> {
        let Some(lexical_owner) = self.lexical_owner else {
            return Ok(false);
        };
        if !self
            .declaration
            .is_for(bound.node_arena_id(), bound.file_id())
            || !bound.contains(self.declaration)
            || bound.container(self.declaration) != Some(lexical_owner)
            || bound.block_scope_container(self.declaration) != Some(lexical_owner)
            || bound.symbol(self.declaration) != Some(self.declaration_symbol)
            || bound.flow_graph().container_is_complete(lexical_owner) != Some(true)
        {
            return Err(invariant(SourceEnumInvariant::InvalidLocalStatement(
                self.declaration,
            )));
        }
        match bound.flow_container(self.declaration) {
            Some(flow_owner) if flow_owner == lexical_owner => {}
            None => return Ok(false),
            Some(_) => {
                return Err(invariant(SourceEnumInvariant::InvalidLocalStatement(
                    self.declaration,
                )));
            }
        }
        let unreachable = bound
            .flow_graph()
            .is_unreachable(self.declaration)
            .ok_or_else(|| {
                invariant(SourceEnumInvariant::InvalidLocalStatement(self.declaration))
            })?;
        Ok(unreachable && !self.is_ambient && (!self.is_const || preserve_const_enums))
    }
}

/// Valid source forms intentionally outside this first enum statement cut.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceEnumUnsupported {
    DeclarationKind {
        node: NodeRef,
        kind: SyntaxKind,
    },
    JavaScriptSource(NodeRef),
    DeclarationFlags(NodeRef),
    IdentifierFlags(NodeRef),
    ModifierFlags(NodeRef),
    MemberFlags(NodeRef),
    LocalDeclaration(NodeRef),
    ExportOutsideExternalModule(NodeRef),
    Canonical {
        declaration: NodeRef,
        reason: EnumTypeUnsupported,
    },
}

/// Malformed AST, binder provenance, plan identity, or semantic cache state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceEnumInvariant {
    InvalidSourceFile(NodeRef),
    MissingSourceFacts(NodeRef),
    InvalidTopLevelStatement(NodeRef),
    InvalidLocalStatement(NodeRef),
    InvalidLexicalOwner(NodeRef),
    InvalidLocalSymbol(NodeRef),
    InvalidDeclaration(NodeRef),
    InvalidIdentifier(NodeRef),
    MissingDeclarationSymbol(NodeRef),
    InvalidMergedSymbol(SemanticSymbolId),
    MissingSourceSymbol(NodeRef),
    InvalidMember(NodeRef),
    MissingMemberSymbol(NodeRef),
    RepeatedMember(NodeRef),
    PlanMismatch(NodeRef),
    InvalidMaterialization(NodeRef),
    Canonical {
        declaration: NodeRef,
        reason: EnumTypeInvariant,
    },
}

/// Exact failure domain for the source enum leaf.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceEnumError {
    Unsupported(SourceEnumUnsupported),
    Invariant(SourceEnumInvariant),
    DeclaredType(DeclaredTypeError),
}

impl SourceEnumError {
    /// Best syntax node for source-level error projection.
    pub(super) const fn node(self) -> Option<NodeRef> {
        match self {
            Self::Unsupported(reason) => match reason {
                SourceEnumUnsupported::DeclarationKind { node, .. }
                | SourceEnumUnsupported::JavaScriptSource(node)
                | SourceEnumUnsupported::DeclarationFlags(node)
                | SourceEnumUnsupported::IdentifierFlags(node)
                | SourceEnumUnsupported::ModifierFlags(node)
                | SourceEnumUnsupported::MemberFlags(node)
                | SourceEnumUnsupported::LocalDeclaration(node)
                | SourceEnumUnsupported::ExportOutsideExternalModule(node) => Some(node),
                SourceEnumUnsupported::Canonical { declaration, .. } => Some(declaration),
            },
            Self::Invariant(reason) => match reason {
                SourceEnumInvariant::InvalidSourceFile(node)
                | SourceEnumInvariant::MissingSourceFacts(node)
                | SourceEnumInvariant::InvalidTopLevelStatement(node)
                | SourceEnumInvariant::InvalidLocalStatement(node)
                | SourceEnumInvariant::InvalidLexicalOwner(node)
                | SourceEnumInvariant::InvalidLocalSymbol(node)
                | SourceEnumInvariant::InvalidDeclaration(node)
                | SourceEnumInvariant::InvalidIdentifier(node)
                | SourceEnumInvariant::MissingDeclarationSymbol(node)
                | SourceEnumInvariant::MissingSourceSymbol(node)
                | SourceEnumInvariant::InvalidMember(node)
                | SourceEnumInvariant::MissingMemberSymbol(node)
                | SourceEnumInvariant::RepeatedMember(node)
                | SourceEnumInvariant::PlanMismatch(node)
                | SourceEnumInvariant::InvalidMaterialization(node) => Some(node),
                SourceEnumInvariant::Canonical { declaration, .. } => Some(declaration),
                SourceEnumInvariant::InvalidMergedSymbol(_) => None,
            },
            Self::DeclaredType(_) => None,
        }
    }
}

impl From<DeclaredTypeError> for SourceEnumError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

fn unsupported(reason: SourceEnumUnsupported) -> SourceEnumError {
    SourceEnumError::Unsupported(reason)
}

fn invariant(reason: SourceEnumInvariant) -> SourceEnumError {
    SourceEnumError::Invariant(reason)
}

fn canonical_error(declaration: NodeRef, error: EnumTypeError) -> SourceEnumError {
    match error {
        EnumTypeError::Unsupported(reason) => unsupported(SourceEnumUnsupported::Canonical {
            declaration,
            reason,
        }),
        EnumTypeError::Invariant(reason) => invariant(SourceEnumInvariant::Canonical {
            declaration,
            reason,
        }),
    }
}

fn range_contains(parent: &Node, child: &Node) -> bool {
    parent.range.start.get() <= child.range.start.get()
        && child.range.start.get() <= child.range.end.get()
        && child.range.end.get() <= parent.range.end.get()
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceEnumPlacement {
    TopLevel,
    Local { lexical_owner: NodeRef },
}

/// Proves one top-level TypeScript enum statement without allocating or
/// publishing semantic state.
pub(super) fn plan_top_level_enum(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
) -> Result<SourceEnumPlan, SourceEnumError> {
    plan_source_enum(store, host, declaration, SourceEnumPlacement::TopLevel)
}

/// Proves one function-local enum and its exact function-owned binder scope.
pub(super) fn plan_local_enum(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    lexical_owner: NodeRef,
) -> Result<SourceEnumPlan, SourceEnumError> {
    plan_source_enum(
        store,
        host,
        declaration,
        SourceEnumPlacement::Local { lexical_owner },
    )
}

/// Proves one function-local const enum and its exact binder scope.
pub(super) fn plan_local_const_enum(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    lexical_owner: NodeRef,
) -> Result<SourceEnumPlan, SourceEnumError> {
    let plan = plan_local_enum(store, host, declaration, lexical_owner)?;
    if !plan.is_const {
        return Err(unsupported(SourceEnumUnsupported::LocalDeclaration(
            declaration,
        )));
    }
    Ok(plan)
}

fn plan_source_enum(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    placement: SourceEnumPlacement,
) -> Result<SourceEnumPlan, SourceEnumError> {
    let record = preflight_node(store, host, declaration)?;
    if record.kind != SyntaxKind::EnumDeclaration {
        return Err(unsupported(SourceEnumUnsupported::DeclarationKind {
            node: declaration,
            kind: record.kind,
        }));
    }
    let NodeData::EnumDeclaration(enumeration) = &record.data else {
        return Err(invariant(SourceEnumInvariant::InvalidDeclaration(
            declaration,
        )));
    };
    if record.flags.0 != 0 {
        return Err(unsupported(SourceEnumUnsupported::DeclarationFlags(
            declaration,
        )));
    }
    if enumeration.flow_node.is_some()
        || enumeration.local_symbol.is_some()
        || enumeration.symbol.is_some()
        || enumeration.facts != 0
    {
        return Err(invariant(SourceEnumInvariant::InvalidDeclaration(
            declaration,
        )));
    }

    let bound = host
        .bound_file(declaration)
        .ok_or_else(|| invariant(SourceEnumInvariant::InvalidDeclaration(declaration)))?;
    let source = bound.source_file();
    let source_record = preflight_node(store, host, source)?;
    let NodeData::SourceFile(source_data) = &source_record.data else {
        return Err(invariant(SourceEnumInvariant::InvalidSourceFile(source)));
    };
    if source_record.kind != SyntaxKind::SourceFile || source_record.parent.is_some() {
        return Err(invariant(SourceEnumInvariant::InvalidSourceFile(source)));
    }
    match placement {
        SourceEnumPlacement::TopLevel => {
            if record.parent != Some(source.node)
                || !range_contains(source_record, record)
                || source_data
                    .statements
                    .nodes
                    .iter()
                    .filter(|node| **node == declaration.node)
                    .count()
                    != 1
            {
                return Err(invariant(SourceEnumInvariant::InvalidTopLevelStatement(
                    declaration,
                )));
            }
        }
        SourceEnumPlacement::Local { lexical_owner } => {
            validate_local_enum_statement(store, host, declaration, lexical_owner)?;
        }
    }
    let facts = bound
        .source_facts()
        .ok_or_else(|| invariant(SourceEnumInvariant::MissingSourceFacts(source)))?;
    if facts.is_javascript_file() {
        return Err(unsupported(SourceEnumUnsupported::JavaScriptSource(source)));
    }

    let name = NodeRef::new(declaration.arena, declaration.file, enumeration.name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(name_data) = &name_record.data else {
        return Err(invariant(SourceEnumInvariant::InvalidIdentifier(name)));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(declaration.node)
        || !range_contains(record, name_record)
    {
        return Err(invariant(SourceEnumInvariant::InvalidIdentifier(name)));
    }
    if name_record.flags.0 != 0 || name_data.flow_node.is_some() {
        return Err(unsupported(SourceEnumUnsupported::IdentifierFlags(name)));
    }

    let declaration_symbol = bound
        .symbol(declaration)
        .ok_or_else(|| invariant(SourceEnumInvariant::MissingDeclarationSymbol(declaration)))?;
    let owner_symbol = store
        .get_merged_symbol(declaration_symbol)
        .ok_or_else(|| invariant(SourceEnumInvariant::InvalidMergedSymbol(declaration_symbol)))?;
    if let SourceEnumPlacement::Local { lexical_owner } = placement {
        validate_local_enum_symbol(
            store,
            host,
            declaration,
            lexical_owner,
            name_data.text.as_str(),
            declaration_symbol,
            owner_symbol,
        )?;
    }
    let diagnostics = enums::preflight_enum_diagnostics(store, host, owner_symbol)
        .map_err(|error| canonical_error(declaration, error))?;

    let mut is_const = false;
    let mut has_declare = false;
    let mut explicitly_exported = false;
    if let Some(modifiers) = &enumeration.modifiers {
        if modifiers.flags.0 != 0 {
            return Err(unsupported(SourceEnumUnsupported::ModifierFlags(
                declaration,
            )));
        }
        if modifiers.list.range.start.get() < record.range.start.get()
            || modifiers.list.range.end.get() > record.range.end.get()
        {
            return Err(invariant(SourceEnumInvariant::InvalidDeclaration(
                declaration,
            )));
        }
        for modifier_id in &modifiers.list.nodes {
            let modifier = NodeRef::new(declaration.arena, declaration.file, *modifier_id);
            let modifier_record = preflight_node(store, host, modifier)?;
            if modifier_record.flags.0 != 0 {
                return Err(unsupported(SourceEnumUnsupported::ModifierFlags(modifier)));
            }
            match modifier_record.kind {
                SyntaxKind::ConstKeyword => is_const = true,
                SyntaxKind::DeclareKeyword => has_declare = true,
                SyntaxKind::ExportKeyword => explicitly_exported = true,
                _ => {
                    // Canonical preflight rejects all other modifier syntax.
                    return Err(invariant(SourceEnumInvariant::InvalidDeclaration(
                        declaration,
                    )));
                }
            }
        }
    }
    if explicitly_exported && !facts.is_external_module() {
        return Err(unsupported(
            SourceEnumUnsupported::ExportOutsideExternalModule(declaration),
        ));
    }
    let is_ambient = has_declare || facts.is_declaration_file();
    if matches!(placement, SourceEnumPlacement::Local { .. }) && (is_ambient || explicitly_exported)
    {
        return Err(unsupported(SourceEnumUnsupported::LocalDeclaration(
            declaration,
        )));
    }
    let export_route = match bound.local_symbol(declaration) {
        None => SourceEnumExportRoute::Local,
        Some(local_symbol) => {
            let raw_source_symbol = bound
                .symbol(source)
                .ok_or_else(|| invariant(SourceEnumInvariant::MissingSourceSymbol(source)))?;
            let source_symbol = store.get_merged_symbol(raw_source_symbol).ok_or_else(|| {
                invariant(SourceEnumInvariant::InvalidMergedSymbol(raw_source_symbol))
            })?;
            SourceEnumExportRoute::Exported {
                local_symbol,
                source_symbol,
                explicitly_exported,
            }
        }
    };

    if enumeration.members.range.start.get() < record.range.start.get()
        || enumeration.members.range.end.get() > record.range.end.get()
    {
        return Err(invariant(SourceEnumInvariant::InvalidDeclaration(
            declaration,
        )));
    }
    let mut seen = HashSet::with_capacity(enumeration.members.nodes.len());
    let mut previous_end = None;
    let mut members = Vec::with_capacity(enumeration.members.nodes.len());
    for member_id in &enumeration.members.nodes {
        let member = NodeRef::new(declaration.arena, declaration.file, *member_id);
        if !seen.insert(member) {
            return Err(invariant(SourceEnumInvariant::RepeatedMember(member)));
        }
        let member_record = preflight_node(store, host, member)?;
        let NodeData::EnumMember(member_data) = &member_record.data else {
            return Err(invariant(SourceEnumInvariant::InvalidMember(member)));
        };
        if member_record.kind != SyntaxKind::EnumMember
            || member_record.parent != Some(declaration.node)
            || !range_contains(record, member_record)
            || previous_end.is_some_and(|end| end > member_record.range.start.get())
            || member_data.postfix_token.is_some()
        {
            return Err(invariant(SourceEnumInvariant::InvalidMember(member)));
        }
        if member_record.flags.0 != 0 {
            return Err(unsupported(SourceEnumUnsupported::MemberFlags(member)));
        }
        if member_data.symbol.is_some() || member_data.facts != 0 {
            return Err(invariant(SourceEnumInvariant::InvalidMember(member)));
        }
        previous_end = Some(member_record.range.end.get());

        let member_name = NodeRef::new(member.arena, member.file, member_data.name);
        let member_name_record = preflight_node(store, host, member_name)?;
        let has_flow_node = match &member_name_record.data {
            NodeData::Identifier(identifier)
                if member_name_record.kind == SyntaxKind::Identifier =>
            {
                identifier.flow_node.is_some()
            }
            NodeData::StringLiteral(_) if member_name_record.kind == SyntaxKind::StringLiteral => {
                false
            }
            NodeData::BigIntLiteral(_) if member_name_record.kind == SyntaxKind::BigIntLiteral => {
                false
            }
            _ => {
                return Err(invariant(SourceEnumInvariant::InvalidIdentifier(
                    member_name,
                )));
            }
        };
        if member_name_record.parent != Some(member.node)
            || !range_contains(member_record, member_name_record)
        {
            return Err(invariant(SourceEnumInvariant::InvalidIdentifier(
                member_name,
            )));
        }
        if member_name_record.flags.0 != 0 || has_flow_node {
            return Err(unsupported(SourceEnumUnsupported::IdentifierFlags(
                member_name,
            )));
        }

        let declaration_symbol = bound
            .symbol(member)
            .ok_or_else(|| invariant(SourceEnumInvariant::MissingMemberSymbol(member)))?;
        let symbol = store.get_merged_symbol(declaration_symbol).ok_or_else(|| {
            invariant(SourceEnumInvariant::InvalidMergedSymbol(declaration_symbol))
        })?;
        members.push(SourceEnumMemberPlan {
            declaration: member,
            name: member_name,
            declaration_symbol,
            symbol,
        });
    }

    Ok(SourceEnumPlan {
        declaration,
        name,
        lexical_owner: match placement {
            SourceEnumPlacement::TopLevel => None,
            SourceEnumPlacement::Local { lexical_owner } => Some(lexical_owner),
        },
        declaration_symbol,
        owner_symbol,
        members,
        diagnostics,
        export_route,
        is_const,
        is_ambient,
    })
}

fn validate_local_enum_statement(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    lexical_owner: NodeRef,
) -> Result<(), SourceEnumError> {
    let record = preflight_node(store, host, declaration)?;
    let NodeData::EnumDeclaration(enumeration) = &record.data else {
        return Err(invariant(SourceEnumInvariant::InvalidDeclaration(
            declaration,
        )));
    };
    if let Some(modifiers) = enumeration.modifiers.as_ref() {
        let [modifier] = modifiers.list.nodes.as_slice() else {
            return Err(unsupported(SourceEnumUnsupported::LocalDeclaration(
                declaration,
            )));
        };
        let modifier = NodeRef::new(declaration.arena, declaration.file, *modifier);
        let modifier_record = preflight_node(store, host, modifier)?;
        if modifiers.flags.0 != 0
            || modifiers.list.has_trailing_comma
            || modifier_record.kind != SyntaxKind::ConstKeyword
            || modifier_record.flags.0 != 0
            || modifier_record.parent != Some(declaration.node)
            || !matches!(modifier_record.data, NodeData::Token(_))
            || !range_contains(record, modifier_record)
        {
            return Err(unsupported(SourceEnumUnsupported::LocalDeclaration(
                declaration,
            )));
        }
    }

    let owner = preflight_node(store, host, lexical_owner)?;
    let NodeData::FunctionDeclaration(function) = &owner.data else {
        return Err(invariant(SourceEnumInvariant::InvalidLexicalOwner(
            lexical_owner,
        )));
    };
    if owner.kind != SyntaxKind::FunctionDeclaration || owner.flags.0 != 0 {
        return Err(invariant(SourceEnumInvariant::InvalidLexicalOwner(
            lexical_owner,
        )));
    }
    let bound = host
        .bound_file(declaration)
        .ok_or_else(|| invariant(SourceEnumInvariant::InvalidDeclaration(declaration)))?;
    if bound.container(declaration) != Some(lexical_owner)
        || bound.block_scope_container(declaration) != Some(lexical_owner)
    {
        return Err(invariant(SourceEnumInvariant::InvalidLexicalOwner(
            lexical_owner,
        )));
    }
    let body = function
        .body
        .map(|node| NodeRef::new(lexical_owner.arena, lexical_owner.file, node))
        .ok_or_else(|| invariant(SourceEnumInvariant::InvalidLexicalOwner(lexical_owner)))?;
    let body_record = preflight_node(store, host, body)?;
    let NodeData::Block(block) = &body_record.data else {
        return Err(invariant(SourceEnumInvariant::InvalidLexicalOwner(
            lexical_owner,
        )));
    };
    if body_record.kind != SyntaxKind::Block
        || body_record.parent != Some(lexical_owner.node)
        || !range_contains(owner, body_record)
    {
        return Err(invariant(SourceEnumInvariant::InvalidLexicalOwner(
            lexical_owner,
        )));
    }

    let parent = record
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| invariant(SourceEnumInvariant::InvalidLocalStatement(declaration)))?;
    let parent_record = preflight_node(store, host, parent)?;
    match &parent_record.data {
        NodeData::Block(_) if parent == body => {
            if parent_record.flags.0 != 0
                || !range_contains(parent_record, record)
                || block
                    .statements
                    .nodes
                    .iter()
                    .filter(|node| **node == declaration.node)
                    .count()
                    != 1
            {
                return Err(invariant(SourceEnumInvariant::InvalidLocalStatement(
                    declaration,
                )));
            }
        }
        NodeData::IfStatement(statement) => {
            if parent_record.kind != SyntaxKind::IfStatement
                || parent_record.flags.0 != 0
                || parent_record.parent != Some(body.node)
                || statement.flow_node.is_some()
                || statement.facts != 0
                || statement.then_statement != declaration.node
                    && statement.else_statement != Some(declaration.node)
                || !range_contains(body_record, parent_record)
                || !range_contains(parent_record, record)
                || block
                    .statements
                    .nodes
                    .iter()
                    .filter(|node| **node == parent.node)
                    .count()
                    != 1
            {
                return Err(invariant(SourceEnumInvariant::InvalidLocalStatement(
                    declaration,
                )));
            }
        }
        _ => {
            return Err(invariant(SourceEnumInvariant::InvalidLocalStatement(
                declaration,
            )));
        }
    }

    if bound.container(parent) != Some(lexical_owner)
        || bound.block_scope_container(parent) != Some(lexical_owner)
    {
        return Err(invariant(SourceEnumInvariant::InvalidLexicalOwner(
            lexical_owner,
        )));
    }
    Ok(())
}

fn validate_local_enum_symbol(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    lexical_owner: NodeRef,
    name: &str,
    declaration_symbol: SemanticSymbolId,
    owner_symbol: SemanticSymbolId,
) -> Result<(), SourceEnumError> {
    let bound = host
        .bound_file(declaration)
        .ok_or_else(|| invariant(SourceEnumInvariant::InvalidDeclaration(declaration)))?;
    let owner = store
        .symbol(owner_symbol)
        .ok_or_else(|| invariant(SourceEnumInvariant::InvalidMergedSymbol(owner_symbol)))?;
    let lexical_symbol = bound
        .locals(lexical_owner)
        .and_then(|locals| store.symbol_table(locals))
        .and_then(|locals| locals.get_source(name));
    if owner_symbol != declaration_symbol
        || lexical_symbol != Some(declaration_symbol)
        || bound.local_symbol(declaration).is_some()
        || !matches!(
            owner.flags(),
            SymbolFlags::CONST_ENUM | SymbolFlags::REGULAR_ENUM
        )
        || owner.check_flags() != CheckFlags::NONE
        || owner.name().as_utf8() != Some(name)
        || owner.declarations() != Some(&[declaration])
        || owner.value_declaration() != Some(declaration)
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
    {
        return Err(invariant(SourceEnumInvariant::InvalidLocalSymbol(
            declaration,
        )));
    }
    Ok(())
}

fn validate_materialization(
    store: &CanonicalTypeMapperStore,
    plan: &SourceEnumPlan,
    result: &CanonicalEnumSemantics,
) -> Result<(), SourceEnumError> {
    let valid_header = result.declaration == plan.declaration
        && result.symbol == plan.owner_symbol
        && result.is_const == plan.is_const
        && result.is_ambient == plan.is_ambient
        && result.members.len() == plan.members.len()
        && store.type_payload(result.declared_type).is_some()
        && store.type_payload(result.value_type).is_some()
        && store
            .declared_type_links(plan.owner_symbol)
            .is_some_and(|links| links.declared_type == Some(result.declared_type))
        && store
            .value_symbol_links(plan.owner_symbol)
            .is_some_and(|links| links.resolved_type == Some(result.value_type));
    let valid_members = plan
        .members
        .iter()
        .zip(&result.members)
        .all(|(planned, materialized)| {
            planned.declaration == materialized.declaration
                && planned.symbol == materialized.symbol
                && store.type_payload(materialized.regular_type).is_some()
                && store.type_payload(materialized.fresh_type).is_some()
                && store
                    .declared_type_links(planned.symbol)
                    .is_some_and(|links| links.declared_type == Some(materialized.fresh_type))
                && store
                    .value_symbol_links(planned.symbol)
                    .is_some_and(|links| links.resolved_type == Some(materialized.fresh_type))
                && store
                    .symbol(planned.symbol)
                    .and_then(|symbol| symbol.name().as_utf8())
                    .is_none_or(|name| {
                        enums::enum_value_member_type(store, result.value_type, name)
                            == Some((planned.symbol, materialized.fresh_type))
                    })
        });
    if valid_header && valid_members {
        Ok(())
    } else {
        Err(invariant(SourceEnumInvariant::InvalidMaterialization(
            plan.declaration,
        )))
    }
}

/// Publishes or validates the enum's canonical declared/value graph.
///
/// The retained plan is re-proved first, so a stale plan or poisoned warm
/// cache fails before the canonical publisher is entered.
pub(super) fn execute_top_level_enum(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceEnumPlan,
) -> Result<CanonicalEnumSemantics, SourceEnumError> {
    let current = plan_top_level_enum(store, host, plan.declaration)?;
    execute_planned_enum(store, host, plan, &current)
}

/// Publishes or validates an admitted function-local enum.
pub(super) fn execute_local_enum(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceEnumPlan,
) -> Result<CanonicalEnumSemantics, SourceEnumError> {
    let lexical_owner = plan
        .lexical_owner
        .ok_or_else(|| invariant(SourceEnumInvariant::PlanMismatch(plan.declaration)))?;
    let current = plan_local_enum(store, host, plan.declaration, lexical_owner)?;
    execute_planned_enum(store, host, plan, &current)
}

/// Publishes or validates an admitted function-local const enum.
pub(super) fn execute_local_const_enum(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceEnumPlan,
) -> Result<CanonicalEnumSemantics, SourceEnumError> {
    if !plan.is_const {
        return Err(unsupported(SourceEnumUnsupported::LocalDeclaration(
            plan.declaration,
        )));
    }
    execute_local_enum(store, host, plan)
}

fn execute_planned_enum(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceEnumPlan,
    current: &SourceEnumPlan,
) -> Result<CanonicalEnumSemantics, SourceEnumError> {
    if current != plan {
        return Err(invariant(SourceEnumInvariant::PlanMismatch(
            plan.declaration,
        )));
    }
    let result = enums::get_enum_semantics(store, host, plan.owner_symbol)
        .map_err(|error| canonical_error(plan.declaration, error))?;
    validate_materialization(store, plan, &result)?;
    Ok(result)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{FileId, NodeArena};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
        CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, SemanticStore, ValueSymbolLinks, mapper::TypeMapper,
        type_records::TypeRecord,
    };

    type TestStore = SemanticStore<TypeRecord, TypeMapper>;

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        files: BTreeMap<FileId, BoundFile>,
        store: TestStore,
    }

    fn fixture(
        source: &str,
        module_state: CanonicalModuleState,
        is_declaration_file: bool,
    ) -> Fixture {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(71);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/source-enums.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    is_declaration_file,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let mut store = TestStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        Fixture {
            parsed,
            file,
            files,
            store,
        }
    }

    fn host<'a>(arena: &'a NodeArena, bound: &'a BoundFile) -> DeclaredTypeHost<'a> {
        DeclaredTypeHost::new([(arena, bound)]).unwrap()
    }

    fn statement(fixture: &Fixture, index: usize) -> NodeRef {
        let source = fixture
            .parsed
            .arena
            .get(fixture.parsed.source_file)
            .unwrap();
        let NodeData::SourceFile(source) = &source.data else {
            panic!("fixture root must be a source file")
        };
        NodeRef::new(
            fixture.parsed.arena.id(),
            fixture.file,
            source.statements.nodes[index],
        )
    }

    fn local_enum(fixture: &Fixture, lexical_owner: NodeRef, expected: &str) -> NodeRef {
        let bound = &fixture.files[&fixture.file];
        fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::EnumDeclaration(enumeration) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &fixture.parsed.arena.get(enumeration.name)?.data
                else {
                    return None;
                };
                let declaration = NodeRef::new(fixture.parsed.arena.id(), fixture.file, node);
                (name.text == expected && bound.container(declaration) == Some(lexical_owner))
                    .then_some(declaration)
            })
            .unwrap_or_else(|| panic!("missing local enum {expected}"))
    }

    #[test]
    fn direct_function_local_enums_preserve_regular_and_const_identities() {
        let mut fixture = fixture(
            concat!(
                "function regular() { ",
                "return Regular.First; enum Regular { First = 1, Second } ",
                "} ",
                "function constant() { ",
                "return Fixed.Ready; const enum Fixed { Ready = 3 } ",
                "}",
            ),
            CanonicalModuleState::Script,
            false,
        );

        for (function_index, name, is_const, member_value) in
            [(0, "Regular", false, 2.0), (1, "Fixed", true, 3.0)]
        {
            let lexical_owner = statement(&fixture, function_index);
            let declaration = local_enum(&fixture, lexical_owner, name);
            let bound = &fixture.files[&fixture.file];
            let host = host(&fixture.parsed.arena, bound);
            let before = (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            );

            let plan = plan_local_enum(&fixture.store, &host, declaration, lexical_owner).unwrap();
            assert_eq!(plan.lexical_owner, Some(lexical_owner));
            assert_eq!(plan.is_const, is_const);
            assert!(plan.diagnostics.is_empty());
            assert_eq!(plan.export_route, SourceEnumExportRoute::Local);
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.type_alias_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                before,
            );

            let materialized = execute_local_enum(&mut fixture.store, &host, &plan).unwrap();
            assert_eq!(materialized.is_const, is_const);
            assert_eq!(
                materialized.members.last().unwrap().value,
                enums::CanonicalEnumMemberValue::Number(ts_jsnum::Number::new(member_value)),
            );
            let warm = (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert_eq!(
                execute_local_enum(&mut fixture.store, &host, &plan),
                Ok(materialized),
            );
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.type_alias_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                warm,
            );
        }
    }

    #[test]
    fn unreachable_local_enums_follow_runtime_preservation() {
        let fixture = fixture(
            concat!(
                "function regular() { ",
                "return Regular.First; enum Regular { First = 1 } ",
                "} ",
                "function constant() { ",
                "return Fixed.Ready; const enum Fixed { Ready = 3 } ",
                "} ",
                "function conditional(value: number) { ",
                "if (value) const enum Active { Ready = 1 } ",
                "}",
            ),
            CanonicalModuleState::Script,
            false,
        );
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let regular_owner = statement(&fixture, 0);
        let regular = plan_local_enum(
            &fixture.store,
            &host,
            local_enum(&fixture, regular_owner, "Regular"),
            regular_owner,
        )
        .unwrap();
        assert_eq!(
            regular.is_unreachable_runtime_declaration(bound, false),
            Ok(true),
        );
        assert_eq!(
            regular.is_unreachable_runtime_declaration(bound, true),
            Ok(true),
        );

        let constant_owner = statement(&fixture, 1);
        let constant = plan_local_const_enum(
            &fixture.store,
            &host,
            local_enum(&fixture, constant_owner, "Fixed"),
            constant_owner,
        )
        .unwrap();
        assert_eq!(
            constant.is_unreachable_runtime_declaration(bound, false),
            Ok(false),
        );
        assert_eq!(
            constant.is_unreachable_runtime_declaration(bound, true),
            Ok(true),
        );

        let conditional_owner = statement(&fixture, 2);
        let conditional = plan_local_const_enum(
            &fixture.store,
            &host,
            local_enum(&fixture, conditional_owner, "Active"),
            conditional_owner,
        )
        .unwrap();
        assert_eq!(bound.flow_container(conditional.declaration), None);
        assert_eq!(
            conditional.is_unreachable_runtime_declaration(bound, true),
            Ok(false),
        );
    }

    #[test]
    fn direct_function_local_const_enum_retains_initializer_diagnostics() {
        let mut fixture = fixture(
            concat!(
                "function invalid() { ",
                "const enum Invalid { Infinite = 1 / 0, Unknown = missing } ",
                "}",
            ),
            CanonicalModuleState::Script,
            false,
        );
        let lexical_owner = statement(&fixture, 0);
        let declaration = local_enum(&fixture, lexical_owner, "Invalid");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let plan =
            plan_local_const_enum(&fixture.store, &host, declaration, lexical_owner).unwrap();
        assert_eq!(
            plan.diagnostics
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2477, 2474],
        );

        let materialized = execute_local_const_enum(&mut fixture.store, &host, &plan).unwrap();
        assert!(matches!(
            materialized.members[0].value,
            enums::CanonicalEnumMemberValue::Number(value) if value.is_infinite()
        ));
        assert_eq!(
            materialized.members[1].value,
            enums::CanonicalEnumMemberValue::Computed,
        );
    }

    #[test]
    fn embedded_const_enum_preserves_lexical_shadowing_and_reuses_warm_caches() {
        let mut fixture = fixture(
            concat!(
                "const enum E { A = 2 } ",
                "function choose(value: number) { ",
                "if (value) const enum E { A = 1 } ",
                "}",
            ),
            CanonicalModuleState::Script,
            false,
        );
        let global_declaration = statement(&fixture, 0);
        let lexical_owner = statement(&fixture, 1);
        let declaration = local_enum(&fixture, lexical_owner, "E");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        let global = plan_top_level_enum(&fixture.store, &host, global_declaration).unwrap();
        let local =
            plan_local_const_enum(&fixture.store, &host, declaration, lexical_owner).unwrap();
        assert_eq!(local.lexical_owner, Some(lexical_owner));
        assert!(local.is_const);
        assert!(!local.is_ambient);
        assert_eq!(local.export_route, SourceEnumExportRoute::Local);
        assert_ne!(local.owner_symbol, global.owner_symbol);
        assert_eq!(
            bound
                .locals(lexical_owner)
                .and_then(|locals| fixture.store.symbol_table(locals))
                .and_then(|locals| locals.get_source("E")),
            Some(local.owner_symbol),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );

        let global_result = execute_top_level_enum(&mut fixture.store, &host, &global).unwrap();
        let local_result = execute_local_const_enum(&mut fixture.store, &host, &local).unwrap();
        assert_ne!(global_result.declared_type, local_result.declared_type);
        assert_ne!(global_result.value_type, local_result.value_type);
        assert_eq!(
            local_result.members[0].value,
            enums::CanonicalEnumMemberValue::Number(ts_jsnum::Number::new(1.0)),
        );
        let warm = (
            fixture.store.type_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            plan_local_const_enum(&fixture.store, &host, declaration, lexical_owner),
            Ok(local.clone()),
        );
        assert_eq!(
            execute_local_const_enum(&mut fixture.store, &host, &local),
            Ok(local_result),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm,
        );
    }

    #[test]
    fn local_const_enum_rejects_foreign_owners_and_poisoned_member_caches() {
        let mut fixture = fixture(
            concat!(
                "function choose(value: number) { ",
                "if (value) const enum E { A = 1 } ",
                "} ",
                "function other() {}",
            ),
            CanonicalModuleState::Script,
            false,
        );
        let lexical_owner = statement(&fixture, 0);
        let foreign_owner = statement(&fixture, 1);
        let declaration = local_enum(&fixture, lexical_owner, "E");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let before = (
            fixture.store.type_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            plan_local_const_enum(&fixture.store, &host, declaration, foreign_owner),
            Err(SourceEnumError::Invariant(
                SourceEnumInvariant::InvalidLexicalOwner(foreign_owner),
            )),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            before,
        );

        let plan =
            plan_local_const_enum(&fixture.store, &host, declaration, lexical_owner).unwrap();
        let materialized = execute_local_const_enum(&mut fixture.store, &host, &plan).unwrap();
        let member = &materialized.members[0];
        assert!(fixture.store.set_value_symbol_links(
            member.symbol,
            ValueSymbolLinks {
                resolved_type: Some(materialized.value_type),
                ..ValueSymbolLinks::default()
            },
        ));
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            plan_local_const_enum(&fixture.store, &host, declaration, lexical_owner),
            Err(SourceEnumError::Invariant(SourceEnumInvariant::Canonical {
                declaration,
                reason: EnumTypeInvariant::InvalidCache(plan.owner_symbol),
            })),
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            poisoned,
        );
        assert!(fixture.store.set_value_symbol_links(
            member.symbol,
            ValueSymbolLinks {
                resolved_type: Some(member.fresh_type),
                ..ValueSymbolLinks::default()
            },
        ));
        assert_eq!(
            execute_local_const_enum(&mut fixture.store, &host, &plan),
            Ok(materialized),
        );
    }

    #[test]
    fn local_enum_planning_keeps_non_const_declarations_unsupported() {
        let fixture = fixture(
            "function choose(value: number) { if (value) enum E { A = 1 } }",
            CanonicalModuleState::Script,
            false,
        );
        let lexical_owner = statement(&fixture, 0);
        let declaration = local_enum(&fixture, lexical_owner, "E");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        assert_eq!(
            plan_local_const_enum(&fixture.store, &host, declaration, lexical_owner),
            Err(SourceEnumError::Unsupported(
                SourceEnumUnsupported::LocalDeclaration(declaration),
            )),
        );
    }

    #[test]
    fn exported_enum_plan_executes_exact_value_and_member_links_and_is_warm() {
        let mut fixture = fixture(
            r#"export enum Status { Ready, Running = 3, Label = "label" }"#,
            CanonicalModuleState::External,
            false,
        );
        let declaration = statement(&fixture, 0);
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_top_level_enum(&fixture.store, &host, declaration).unwrap();
        assert!(!plan.is_const);
        assert!(!plan.is_ambient);
        assert_eq!(plan.members.len(), 3);
        assert!(matches!(
            plan.export_route,
            SourceEnumExportRoute::Exported {
                explicitly_exported: true,
                ..
            }
        ));

        let result = execute_top_level_enum(&mut fixture.store, &host, &plan).unwrap();
        assert_eq!(result.symbol, plan.owner_symbol);
        assert_eq!(
            fixture
                .store
                .value_symbol_links(plan.owner_symbol)
                .and_then(|links| links.resolved_type),
            Some(result.value_type)
        );
        for member in &result.members {
            assert_eq!(
                fixture
                    .store
                    .value_symbol_links(member.symbol)
                    .and_then(|links| links.resolved_type),
                Some(member.fresh_type)
            );
        }
        let warm_state = (
            fixture.store.type_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            plan_top_level_enum(&fixture.store, &host, declaration),
            Ok(plan.clone())
        );
        assert_eq!(
            execute_top_level_enum(&mut fixture.store, &host, &plan),
            Ok(result)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm_state
        );
    }

    #[test]
    fn declaration_file_enum_retains_implicit_export_and_ambient_values() {
        let mut fixture = fixture(
            "enum Ambient { First, Second = 2 }",
            CanonicalModuleState::External,
            true,
        );
        let declaration = statement(&fixture, 0);
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_top_level_enum(&fixture.store, &host, declaration).unwrap();
        assert!(plan.is_ambient);
        assert!(matches!(
            plan.export_route,
            SourceEnumExportRoute::Exported {
                explicitly_exported: false,
                ..
            }
        ));
        let result = execute_top_level_enum(&mut fixture.store, &host, &plan).unwrap();
        assert!(matches!(
            result.members[0].value,
            enums::CanonicalEnumMemberValue::Computed
        ));
    }

    #[test]
    fn quoted_enum_member_names_have_canonical_source_plans() {
        let mut fixture = fixture(
            r#"export enum Named { "non identifier" = 1, "//" = 2, "-Infinity" = 3 }"#,
            CanonicalModuleState::External,
            false,
        );
        let declaration = statement(&fixture, 0);
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let plan = plan_top_level_enum(&fixture.store, &host, declaration).unwrap();
        assert_eq!(plan.members.len(), 3);
        for member in &plan.members {
            assert_eq!(
                fixture.parsed.arena.get(member.name.node).unwrap().kind,
                SyntaxKind::StringLiteral
            );
        }

        let result = execute_top_level_enum(&mut fixture.store, &host, &plan).unwrap();
        assert_eq!(result.members.len(), 3);
    }

    #[test]
    fn numeric_member_name_diagnostic_precedes_ambient_initializer_diagnostic() {
        let mut fixture = fixture(
            r#"declare enum Invalid { "1" = 'value'.length }"#,
            CanonicalModuleState::Script,
            false,
        );
        let declaration = statement(&fixture, 0);
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let plan = plan_top_level_enum(&fixture.store, &host, declaration).unwrap();
        assert_eq!(
            plan.diagnostics
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [2452, 1066]
        );

        let materialized = execute_top_level_enum(&mut fixture.store, &host, &plan).unwrap();
        assert_eq!(
            materialized.members[0].value,
            enums::CanonicalEnumMemberValue::Computed
        );
    }

    #[test]
    fn bigint_member_names_remain_diagnostics_instead_of_invariants() {
        let mut fixture = fixture(
            "enum Invalid { 0n = 0 }",
            CanonicalModuleState::Script,
            false,
        );
        let declaration = statement(&fixture, 0);
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let plan = plan_top_level_enum(&fixture.store, &host, declaration).unwrap();
        assert_eq!(plan.diagnostics.len(), 1);
        assert_eq!(plan.diagnostics[0].code, 2452);
        assert_eq!(
            fixture
                .parsed
                .arena
                .get(plan.members[0].name.node)
                .unwrap()
                .kind,
            SyntaxKind::BigIntLiteral
        );

        let result = execute_top_level_enum(&mut fixture.store, &host, &plan).unwrap();
        assert_eq!(result.members.len(), 1);
    }

    #[test]
    fn ambient_enum_plan_retains_nonconstant_initializer_diagnostics() {
        let mut fixture = fixture(
            "declare enum Ambient { Numeric = 4.23, Computed = 'foo'.length }",
            CanonicalModuleState::Script,
            false,
        );
        let declaration = statement(&fixture, 0);
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let plan = plan_top_level_enum(&fixture.store, &host, declaration).unwrap();
        assert!(plan.is_ambient);
        assert_eq!(plan.diagnostics.len(), 1);
        assert_eq!(plan.diagnostics[0].code, 1066);
        assert_eq!(
            fixture
                .parsed
                .arena
                .get(plan.diagnostics[0].node.node)
                .unwrap()
                .kind,
            SyntaxKind::PropertyAccessExpression
        );

        let materialized = execute_top_level_enum(&mut fixture.store, &host, &plan).unwrap();
        assert_eq!(
            materialized.members[1].value,
            enums::CanonicalEnumMemberValue::Computed
        );
    }

    #[test]
    fn exported_ambient_enum_accepts_global_nan_and_infinity() {
        let mut fixture = fixture(
            "export declare enum E { A = -NaN, B = NaN, C = Infinity, D = -Infinity }",
            CanonicalModuleState::External,
            false,
        );
        let declaration = statement(&fixture, 0);
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);

        let plan = plan_top_level_enum(&fixture.store, &host, declaration).unwrap();
        assert!(plan.diagnostics.is_empty());

        let materialized = execute_top_level_enum(&mut fixture.store, &host, &plan).unwrap();
        assert_eq!(materialized.members.len(), 4);
        assert_eq!(
            materialized.members[0].fresh_type,
            materialized.members[1].fresh_type
        );
    }

    #[test]
    fn unsupported_and_poisoned_plans_are_typed_and_mutation_free() {
        let mut fixture = fixture(
            "enum Unsupported { A = runtime } enum Good { A }",
            CanonicalModuleState::Script,
            false,
        );
        let unsupported = statement(&fixture, 0);
        let good = statement(&fixture, 1);
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let initial = (
            fixture.store.type_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert!(matches!(
            plan_top_level_enum(&fixture.store, &host, unsupported),
            Err(SourceEnumError::Unsupported(
                SourceEnumUnsupported::Canonical {
                    reason: EnumTypeUnsupported::Initializer(_),
                    ..
                }
            ))
        ));
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            initial
        );

        let plan = plan_top_level_enum(&fixture.store, &host, good).unwrap();
        let published = execute_top_level_enum(&mut fixture.store, &host, &plan).unwrap();
        let member = &published.members[0];
        assert!(fixture.store.set_value_symbol_links(
            member.symbol,
            ValueSymbolLinks {
                resolved_type: Some(published.value_type),
                ..ValueSymbolLinks::default()
            }
        ));
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.type_alias_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            plan_top_level_enum(&fixture.store, &host, good),
            Err(SourceEnumError::Invariant(SourceEnumInvariant::Canonical {
                declaration: good,
                reason: EnumTypeInvariant::InvalidCache(plan.owner_symbol),
            }))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.type_alias_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            poisoned
        );
        assert!(fixture.store.set_value_symbol_links(
            member.symbol,
            ValueSymbolLinks {
                resolved_type: Some(member.fresh_type),
                ..ValueSymbolLinks::default()
            }
        ));
        assert_eq!(
            execute_top_level_enum(&mut fixture.store, &host, &plan),
            Ok(published)
        );
    }
}
