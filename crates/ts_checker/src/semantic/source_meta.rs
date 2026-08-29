//! Source-owned import meta-properties and the pinned checker wrapper identity.

use ts_ast::{FileId, NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalSourceFileFacts, CheckFlags, EscapedName, SymbolFlags, semantic::PreparedSymbolTable,
};
use ts_core::TextRange;
use ts_diagnostics::{Diagnostic, message_by_code};
use ts_options::ModuleKind;
use ts_scanner::Scanner;

use super::{
    CanonicalCheckerDiagnostic, CanonicalCheckerDiagnosticRange, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalGlobalTypeInitializationError, CanonicalTypeMapperStore,
    DeclaredTypeError, DeclaredTypeHost, SemanticSymbolId, SymbolNodeLinks, SymbolTableId, TypeId,
    TypeNodeLinks, ValueSymbolLinks,
    declared::preflight_node,
    global_types::resolve_required_global_type,
    source::merge_retry_diagnostic,
    store::SourceNodeParent,
    type_records::{ObjectTypeData, StructuredTypeData, TypeData},
    types::{ObjectFlags, TypeFlags},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceMetaError {
    Unsupported(NodeRef),
    InvalidNode(NodeRef),
    InvalidPlan(NodeRef),
    MissingOptions(NodeRef),
    MissingSourceFacts(FileId),
    MissingImpliedNodeFormat(FileId),
    InvalidImpliedNodeFormat { file: FileId, format: ModuleKind },
    InvalidGlobalCache,
    InvalidWrapper(TypeId),
    InvalidTypeCache(NodeRef),
    InvalidSymbolCache(NodeRef),
    Capacity(NodeRef),
    MissingDiagnostic(u32),
    Global(CanonicalGlobalTypeInitializationError),
    Declared(DeclaredTypeError),
}

impl std::fmt::Display for SourceMetaError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "import meta-property checking failed: {self:?}")
    }
}

impl std::error::Error for SourceMetaError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Global(error) => Some(error),
            Self::Declared(error) => Some(error),
            _ => None,
        }
    }
}

impl From<DeclaredTypeError> for SourceMetaError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::Declared(error)
    }
}

impl From<CanonicalGlobalTypeInitializationError> for SourceMetaError {
    fn from(error: CanonicalGlobalTypeInitializationError) -> Self {
        Self::Global(error)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ImportMetaKind {
    Meta,
    BareDefer,
    InvalidName { text: String, call_callee: bool },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PlannedImportMetaProperty {
    node: NodeRef,
    name: NodeRef,
    kind: ImportMetaKind,
    module_kind: ModuleKind,
    facts: CanonicalSourceFileFacts,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ImportMetaExpressionIdentity {
    pub(super) type_: TypeId,
    pub(super) symbol: SemanticSymbolId,
    pub(super) meta: SemanticSymbolId,
    pub(super) members: SymbolTableId,
    pub(super) import_meta_type: TypeId,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ImportMetaSymbolResult {
    Unrelated,
    Resolved(Option<SemanticSymbolId>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ImportMetaSymbolQuery {
    Name,
    Expression,
}

pub(super) fn plan_import_meta_property(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    options: CanonicalCheckerOptions,
) -> Result<PlannedImportMetaProperty, SourceMetaError> {
    let invalid = || SourceMetaError::InvalidNode(node);
    let record = preflight_node(store, host, node)?;
    let NodeData::MetaProperty(meta) = &record.data else {
        return Err(invalid());
    };
    if meta.keyword_token != SyntaxKind::ImportKeyword {
        return Err(SourceMetaError::Unsupported(node));
    }
    let Some(SourceNodeParent::Parent(parent)) = store.source_node_parent(node) else {
        return Err(invalid());
    };
    let parent_record = preflight_node(store, host, parent)?;
    if record.kind != SyntaxKind::MetaProperty
        || record.flags.0 != 0
        || meta.flow_node.is_some()
        || meta.facts != 0
        || store.source_node_kind(node) != Some(record.kind)
        || store.source_node_start(node) != Some(record.range.start.get())
        || record.parent != Some(parent.node)
        || store.source_node_kind(parent) != Some(parent_record.kind)
        || store.source_node_start(parent) != Some(parent_record.range.start.get())
        || !parent_record.data.matches_syntax_kind(parent_record.kind)
    {
        return Err(invalid());
    }
    let name = NodeRef::new(node.arena, node.file, meta.name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invalid());
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(node.node)
        || name_record.range.start <= record.range.start
        || name_record.range.end != record.range.end
        || identifier.flow_node.is_some()
        || store.source_node_kind(name) != Some(SyntaxKind::Identifier)
        || store.source_node_start(name) != Some(name_record.range.start.get())
        || store.source_identifier_text(name) != Some(identifier.text.as_str())
        || store.source_node_parent(name) != Some(SourceNodeParent::Parent(node))
        || store.source_direct_children(node).as_deref() != Some(&[name])
    {
        return Err(invalid());
    }
    let (arena, bound) = host.source(node).ok_or_else(invalid)?;
    let source = arena.source_text().ok_or_else(invalid)?;
    let start = usize::try_from(record.range.start.get()).map_err(|_| invalid())?;
    let end = usize::try_from(record.range.end.get()).map_err(|_| invalid())?;
    let mut scanner = Scanner::new(source.get(start..end).ok_or_else(invalid)?);
    let keyword = scanner.scan();
    let dot = scanner.scan();
    let token = scanner.scan();
    let token_text = token.value.as_ref().map(ts_ast::encode_js_string);
    if keyword.kind != SyntaxKind::ImportKeyword
        || dot.kind != SyntaxKind::DotToken
        || !(token.kind == SyntaxKind::Identifier || token.kind.is_keyword())
        || token_text.as_deref().unwrap_or(token.text) != identifier.text
        || record
            .range
            .start
            .get()
            .checked_add(token.range.start.get())
            != Some(name_record.range.start.get())
        || record.range.start.get().checked_add(token.range.end.get())
            != Some(name_record.range.end.get())
        || scanner.scan().kind != SyntaxKind::EndOfFile
        || !scanner.diagnostics().is_empty()
    {
        return Err(invalid());
    }
    let call_callee = if let NodeData::CallExpression(call) = &parent_record.data {
        let source_callee = store
            .source_direct_children(parent)
            .ok_or_else(invalid)?
            .into_iter()
            .min_by_key(|child| store.source_node_start(*child))
            .ok_or_else(invalid)?;
        if source_callee.node != call.expression {
            return Err(invalid());
        }
        call.expression == node.node
    } else {
        false
    };
    let kind = match identifier.text.as_str() {
        "meta" => ImportMetaKind::Meta,
        "defer" if call_callee => return Err(SourceMetaError::Unsupported(node)),
        "defer" => ImportMetaKind::BareDefer,
        text => ImportMetaKind::InvalidName {
            text: text.to_owned(),
            call_callee,
        },
    };
    let facts = bound
        .source_facts()
        .ok_or(SourceMetaError::MissingSourceFacts(node.file))?
        .clone();
    let module_kind = options.effective_module_kind();
    if let Some(format) = facts.implied_node_format()
        && !matches!(format, ModuleKind::CommonJs | ModuleKind::EsNext)
    {
        return Err(SourceMetaError::InvalidImpliedNodeFormat {
            file: node.file,
            format,
        });
    }
    if !matches!(kind, ImportMetaKind::BareDefer)
        && is_node_module(module_kind)
        && facts.implied_node_format().is_none()
    {
        return Err(SourceMetaError::MissingImpliedNodeFormat(node.file));
    }
    let plan = PlannedImportMetaProperty {
        node,
        name,
        kind,
        module_kind,
        facts,
    };
    validate_plan_caches(store, host, &plan, false)?;
    Ok(plan)
}

fn is_node_module(module: ModuleKind) -> bool {
    matches!(
        module,
        ModuleKind::Node16 | ModuleKind::Node18 | ModuleKind::Node20 | ModuleKind::NodeNext
    )
}

fn module_diagnostic(plan: &PlannedImportMetaProperty) -> Option<u32> {
    if is_node_module(plan.module_kind) {
        return (plan.facts.implied_node_format() != Some(ModuleKind::EsNext)).then_some(1470);
    }
    (!matches!(
        plan.module_kind,
        ModuleKind::System
            | ModuleKind::Es2020
            | ModuleKind::Es2022
            | ModuleKind::EsNext
            | ModuleKind::Preserve
    ))
    .then_some(1343)
}

pub(super) fn check_import_meta_property(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &PlannedImportMetaProperty,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
) -> Result<TypeId, SourceMetaError> {
    if plan_import_meta_property(store, host, plan.node, options)? != *plan {
        return Err(SourceMetaError::InvalidPlan(plan.node));
    }
    let type_ = if matches!(plan.kind, ImportMetaKind::Meta) {
        import_meta_type(store, host)?
    } else {
        store
            .intrinsic_bootstrap()
            .map(|bootstrap| bootstrap.error_type)
            .ok_or(SourceMetaError::InvalidGlobalCache)?
    };
    match &plan.kind {
        ImportMetaKind::BareDefer => {
            let end = host
                .node(plan.node)
                .ok_or(SourceMetaError::InvalidNode(plan.node))?
                .range
                .end;
            issue_diagnostic(
                diagnostics,
                plan.node,
                Some(CanonicalCheckerDiagnosticRange::new(
                    plan.node,
                    TextRange::new(end, end),
                )),
                1005,
                vec!["(".to_owned()],
            )?;
        }
        ImportMetaKind::InvalidName { text, call_callee } => {
            let (code, arguments) = if *call_callee {
                (18061, vec![text.clone()])
            } else {
                (
                    17012,
                    vec![text.clone(), "import".to_owned(), "meta".to_owned()],
                )
            };
            issue_diagnostic(diagnostics, plan.name, None, code, arguments)?;
        }
        ImportMetaKind::Meta => {}
    }
    if !matches!(plan.kind, ImportMetaKind::BareDefer)
        && let Some(code) = module_diagnostic(plan)
    {
        issue_diagnostic(diagnostics, plan.node, None, code, Vec::new())?;
    }
    Ok(type_)
}

fn issue_diagnostic(
    diagnostics: &mut CanonicalCheckerDiagnostics,
    node: NodeRef,
    range_override: Option<CanonicalCheckerDiagnosticRange>,
    code: u32,
    arguments: Vec<String>,
) -> Result<(), SourceMetaError> {
    merge_retry_diagnostic(
        diagnostics,
        CanonicalCheckerDiagnostic {
            node: Some(node),
            range_override,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(code).ok_or(SourceMetaError::MissingDiagnostic(code))?,
                arguments,
            ),
            related_information: Vec::new(),
        },
    );
    Ok(())
}

fn import_meta_type(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
) -> Result<TypeId, SourceMetaError> {
    if let Some(global) = store.import_meta_global() {
        global.validate(store, host)?;
        return Ok(global.type_());
    }
    let global = resolve_required_global_type(store, host, "ImportMeta", 0)?;
    global.validate(store, host)?;
    let type_ = global.type_();
    if !store.set_import_meta_global(global) {
        return Err(SourceMetaError::InvalidGlobalCache);
    }
    Ok(type_)
}

fn expected_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &PlannedImportMetaProperty,
) -> Result<Option<TypeId>, SourceMetaError> {
    if matches!(plan.kind, ImportMetaKind::Meta) {
        let Some(global) = store.import_meta_global() else {
            return Ok(None);
        };
        global.validate(store, host)?;
        Ok(Some(global.type_()))
    } else {
        Ok(Some(
            store
                .intrinsic_bootstrap()
                .ok_or(SourceMetaError::InvalidGlobalCache)?
                .error_type,
        ))
    }
}

fn validate_plan_caches(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &PlannedImportMetaProperty,
    require_checked: bool,
) -> Result<Option<TypeId>, SourceMetaError> {
    let expected = expected_type(store, host, plan)?;
    for node in [plan.node, plan.name] {
        let links = store.type_node_links(node);
        if links.is_some_and(|links| links.outer_type_parameters.is_some()) {
            return Err(SourceMetaError::InvalidTypeCache(node));
        }
        let cached = links.and_then(|links| links.resolved_type);
        if cached.is_some() && cached != expected
            || require_checked && node == plan.node && cached != expected
        {
            return Err(SourceMetaError::InvalidTypeCache(node));
        }
    }
    if require_checked && expected.is_none() {
        return Err(SourceMetaError::InvalidTypeCache(plan.node));
    }
    let root_symbol = expected.and_then(|type_| {
        store
            .type_payload(type_)
            .and_then(super::type_records::TypeRecord::symbol)
    });
    let wrapper = store.import_meta_expression();
    if let Some(wrapper) = wrapper {
        validate_wrapper(store, host, wrapper)?;
    }
    let name_symbol = if matches!(plan.kind, ImportMetaKind::Meta) {
        wrapper.map(|wrapper| wrapper.meta)
    } else {
        None
    };
    for (node, expected) in [(plan.node, root_symbol), (plan.name, name_symbol)] {
        if store
            .symbol_node_links(node)
            .and_then(|links| links.resolved_symbol)
            .is_some_and(|cached| Some(cached) != expected)
        {
            return Err(SourceMetaError::InvalidSymbolCache(node));
        }
    }
    Ok(expected)
}

fn validate_wrapper(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    identity: ImportMetaExpressionIdentity,
) -> Result<(), SourceMetaError> {
    let invalid = || SourceMetaError::InvalidWrapper(identity.type_);
    let global = store.import_meta_global().ok_or_else(invalid)?;
    global.validate(store, host)?;
    let owner = store.symbol(identity.symbol).ok_or_else(invalid)?;
    let property = store.symbol(identity.meta).ok_or_else(invalid)?;
    let members = store.symbol_table(identity.members).ok_or_else(invalid)?;
    let record = store.type_payload(identity.type_).ok_or_else(invalid)?;
    let TypeData::Object(object) = record.data() else {
        return Err(invalid());
    };
    let allowed = ObjectFlags::ANONYMOUS
        | ObjectFlags::MEMBERS_RESOLVED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
        | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
    let expected_object = ObjectTypeData {
        structured: StructuredTypeData {
            members: Some(identity.members),
            properties: Some(vec![identity.meta]),
            ..StructuredTypeData::default()
        },
        ..ObjectTypeData::default()
    };
    if global.type_() != identity.import_meta_type
        || owner.flags() != SymbolFlags::TRANSIENT
        || owner.check_flags() != CheckFlags::NONE
        || owner.name().as_utf8() != Some("ImportMetaExpression")
        || owner.declarations().is_some()
        || owner.value_declaration().is_some()
        || owner.parent().is_some()
        || owner.exports().is_some()
        || owner.export_symbol().is_some()
        || owner.members() != Some(identity.members)
        || property.flags() != (SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT)
        || property.check_flags() != CheckFlags::READONLY
        || property.name().as_utf8() != Some("meta")
        || property.declarations().is_some()
        || property.value_declaration().is_some()
        || property.parent() != Some(identity.symbol)
        || property.members().is_some()
        || property.exports().is_some()
        || property.export_symbol().is_some()
        || store.get_merged_symbol(identity.symbol) != Some(identity.symbol)
        || store.get_merged_symbol(identity.meta) != Some(identity.meta)
        || members.len() != 1
        || members.get_source("meta") != Some(identity.meta)
        || store.value_symbol_links(identity.meta)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(identity.import_meta_type),
                ..ValueSymbolLinks::default()
            })
        || record.flags() != TypeFlags::OBJECT
        || record.symbol() != Some(identity.symbol)
        || record.alias().is_some()
        || !record
            .object_flags()
            .contains(ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
        || !(record.object_flags() & !allowed).is_empty()
        || object != &expected_object
    {
        return Err(invalid());
    }
    Ok(())
}

fn import_meta_expression(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<ImportMetaExpressionIdentity, SourceMetaError> {
    if let Some(identity) = store.import_meta_expression() {
        validate_wrapper(store, host, identity)?;
        return Ok(identity);
    }
    let import_meta_type = import_meta_type(store, host)?;
    let members = PreparedSymbolTable::new(1).ok_or(SourceMetaError::Capacity(node))?;
    if !store.try_reserve_types(1)
        || !store.try_reserve_checker_symbol_allocations(2, 1)
        || !store.try_reserve_value_symbol_links(1)
    {
        return Err(SourceMetaError::Capacity(node));
    }
    let members = store.alloc_prepared_symbol_table(members);
    let symbol = store.alloc_transient_symbol(
        SymbolFlags::NONE,
        EscapedName::source("ImportMetaExpression"),
        CheckFlags::NONE,
    );
    let meta = store.alloc_transient_symbol(
        SymbolFlags::PROPERTY,
        EscapedName::source("meta"),
        CheckFlags::READONLY,
    );
    assert!(store.set_symbol_relationships(meta, None, None, Some(symbol), None));
    assert!(store.set_symbol_relationships(symbol, Some(members), None, None, None));
    assert_eq!(
        store.insert_symbol(members, EscapedName::source("meta"), meta),
        Some(None)
    );
    assert!(store.set_value_symbol_links(
        meta,
        ValueSymbolLinks {
            resolved_type: Some(import_meta_type),
            ..ValueSymbolLinks::default()
        }
    ));
    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(symbol))
        .ok_or(SourceMetaError::Capacity(node))?;
    assert!(store.set_structured_type_members(
        type_,
        Some(members),
        Some(vec![meta]),
        None,
        None,
        None
    ));
    let identity = ImportMetaExpressionIdentity {
        type_,
        symbol,
        meta,
        members,
        import_meta_type,
    };
    assert!(store.set_import_meta_expression(identity));
    validate_wrapper(store, host, identity)?;
    Ok(identity)
}

fn artifact_plan(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    options: CanonicalCheckerOptions,
    require_checked: bool,
) -> Result<Option<PlannedImportMetaProperty>, SourceMetaError> {
    let (arena, _) = host
        .source(node)
        .ok_or(SourceMetaError::InvalidNode(node))?;
    if !is_import_meta_artifact_node(arena, node) {
        return Ok(None);
    }
    let record = preflight_node(store, host, node)?;
    let owner = if matches!(&record.data, NodeData::MetaProperty(meta) if meta.keyword_token == SyntaxKind::ImportKeyword)
    {
        Some(node)
    } else {
        record.parent.and_then(|parent| {
            let parent = NodeRef::new(node.arena, node.file, parent);
            host.node(parent).filter(|record| {
                matches!(&record.data, NodeData::MetaProperty(meta) if meta.keyword_token == SyntaxKind::ImportKeyword && meta.name == node.node)
            }).map(|_| parent)
        })
    };
    let Some(owner) = owner else {
        return Ok(None);
    };
    let plan = plan_import_meta_property(store, host, owner, options)?;
    validate_plan_caches(store, host, &plan, require_checked)?;
    Ok(Some(plan))
}

pub(super) fn is_import_meta_artifact_node(arena: &NodeArena, node: NodeRef) -> bool {
    if node.arena != arena.id() {
        return false;
    }
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    let (owner_id, owner, meta) = match &record.data {
        NodeData::MetaProperty(meta) if meta.keyword_token == SyntaxKind::ImportKeyword => {
            (node.node, record, meta)
        }
        _ => {
            let Some(parent_id) = record.parent else {
                return false;
            };
            let Some(parent) = arena.get(parent_id) else {
                return false;
            };
            let NodeData::MetaProperty(meta) = &parent.data else {
                return false;
            };
            if meta.keyword_token != SyntaxKind::ImportKeyword || meta.name != node.node {
                return false;
            }
            (parent_id, parent, meta)
        }
    };
    let deferred = matches!(arena.get(meta.name).map(|name| &name.data),
        Some(NodeData::Identifier(name)) if name.text == "defer");
    !deferred || !owner.parent.and_then(|parent| arena.get(parent)).is_some_and(|parent| {
        matches!(&parent.data, NodeData::CallExpression(call) if call.expression == owner_id)
    })
}

pub(super) fn import_meta_type_at_location(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    options: CanonicalCheckerOptions,
) -> Result<Option<TypeId>, SourceMetaError> {
    let Some(plan) = artifact_plan(store, host, node, options, true)? else {
        return Ok(None);
    };
    let type_ =
        expected_type(store, host, &plan)?.ok_or(SourceMetaError::InvalidTypeCache(node))?;
    publish_artifact_links(store, node, type_, None)?;
    Ok(Some(type_))
}

pub(super) fn import_meta_symbol_at_location(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    options: CanonicalCheckerOptions,
) -> Result<ImportMetaSymbolResult, SourceMetaError> {
    let Some(plan) = artifact_plan(store, host, node, options, false)? else {
        return Ok(ImportMetaSymbolResult::Unrelated);
    };
    if node == plan.name {
        if !matches!(plan.kind, ImportMetaKind::Meta) {
            return Ok(ImportMetaSymbolResult::Resolved(None));
        }
        if !store
            .try_reserve_symbol_node_links(usize::from(store.symbol_node_links(node).is_none()))
        {
            return Err(SourceMetaError::Capacity(node));
        }
        let wrapper = import_meta_expression(store, host, node)?;
        let mut links = store.symbol_node_links(node).cloned().unwrap_or_default();
        if links
            .resolved_symbol
            .is_some_and(|symbol| symbol != wrapper.meta)
        {
            return Err(SourceMetaError::InvalidSymbolCache(node));
        }
        links.resolved_symbol = Some(wrapper.meta);
        assert!(store.set_symbol_node_links(node, links));
        return Ok(ImportMetaSymbolResult::Resolved(Some(wrapper.meta)));
    }
    validate_plan_caches(store, host, &plan, true)?;
    let type_ =
        expected_type(store, host, &plan)?.ok_or(SourceMetaError::InvalidTypeCache(node))?;
    let symbol = store
        .type_payload(type_)
        .and_then(super::type_records::TypeRecord::symbol);
    publish_artifact_links(store, node, type_, symbol)?;
    Ok(ImportMetaSymbolResult::Resolved(symbol))
}

fn publish_artifact_links(
    store: &mut CanonicalTypeMapperStore,
    node: NodeRef,
    type_: TypeId,
    symbol: Option<SemanticSymbolId>,
) -> Result<(), SourceMetaError> {
    let mut type_links = store
        .type_node_links(node)
        .cloned()
        .unwrap_or_else(TypeNodeLinks::default);
    if type_links.outer_type_parameters.is_some()
        || type_links
            .resolved_type
            .is_some_and(|cached| cached != type_)
    {
        return Err(SourceMetaError::InvalidTypeCache(node));
    }
    let mut symbol_links = store
        .symbol_node_links(node)
        .cloned()
        .unwrap_or_else(SymbolNodeLinks::default);
    if symbol.is_some()
        && symbol_links
            .resolved_symbol
            .is_some_and(|cached| Some(cached) != symbol)
    {
        return Err(SourceMetaError::InvalidSymbolCache(node));
    }
    if !store.try_reserve_type_node_links(usize::from(store.type_node_links(node).is_none()))
        || symbol.is_some()
            && !store
                .try_reserve_symbol_node_links(usize::from(store.symbol_node_links(node).is_none()))
    {
        return Err(SourceMetaError::Capacity(node));
    }
    type_links.resolved_type = Some(type_);
    assert!(store.set_type_node_links(node, type_links));
    if let Some(symbol) = symbol {
        symbol_links.resolved_symbol = Some(symbol);
        assert!(store.set_symbol_node_links(node, symbol_links));
    }
    Ok(())
}
