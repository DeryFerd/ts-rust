//! Exact local class declaration shells for the first S11a cut.
//!
//! Pinned `getDeclaredTypeOfClassOrInterface` already lives in
//! [`super::declared`]. This module composes that canonical instance identity
//! with the distinct class value identity created by
//! `getTypeOfFuncClassEnumModuleWorker`. The admitted declaration plan also
//! retains the exact split between annotated instance properties
//! (`symbol.members`) and annotated static properties (`symbol.exports`).
//!
//! This is deliberately a shell boundary, not a claim that a class has been
//! checked. Property annotations, readonly publication, structured member
//! tables, the mandatory default construct signature, bodies, heritage, and
//! diagnostics remain for the root-owned adapters and later class stages.

use std::collections::HashSet;

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, SemanticSymbolId, SymbolFlags, SymbolTableId};

use super::{
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, TypeId,
    declared::{preflight_class_or_interface_reference, preflight_node},
    links::ValueSymbolLinks,
    type_records::{ObjectTypeData, TypeData},
    types::{ObjectFlags, TypeFlags},
};

const NODE_FLAG_JSDOC: u32 = 1 << 22;
const NODE_FLAG_HAS_ERROR: u32 = 1 << 15;
const PROTOTYPE_NAME: &str = "prototype";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ClassPropertySide {
    Instance,
    Static,
}

/// One source property whose annotation can be executed by the root query
/// adapter without rediscovering its binder ownership or class side.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ClassPropertyPlan {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    name_node: NodeRef,
    type_node: NodeRef,
    name: String,
    side: ClassPropertySide,
    optional: bool,
    definite: bool,
    readonly: bool,
}

impl ClassPropertyPlan {
    pub(super) const fn declaration(&self) -> NodeRef {
        self.declaration
    }

    pub(super) const fn symbol(&self) -> SemanticSymbolId {
        self.symbol
    }

    pub(super) const fn name_node(&self) -> NodeRef {
        self.name_node
    }

    pub(super) const fn type_node(&self) -> NodeRef {
        self.type_node
    }

    pub(super) fn name(&self) -> &str {
        &self.name
    }

    pub(super) const fn side(&self) -> ClassPropertySide {
        self.side
    }

    pub(super) const fn optional(&self) -> bool {
        self.optional
    }

    pub(super) const fn definite(&self) -> bool {
        self.definite
    }

    pub(super) const fn readonly(&self) -> bool {
        self.readonly
    }
}

/// Opaque, read-only syntax and binder proof for one admitted class.
///
/// This proof is intentionally prepublication: property check flags must
/// still be the binder's `NONE`. The later member stage will need a distinct
/// evolved-state validator after it publishes readonly and annotation caches.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ClassDeclarationPlan {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    instance_members: Option<SymbolTableId>,
    static_members: SymbolTableId,
    properties: Vec<ClassPropertyPlan>,
    instance_properties: Vec<ClassPropertyPlan>,
    static_properties: Vec<ClassPropertyPlan>,
}

impl ClassDeclarationPlan {
    pub(super) const fn declaration(&self) -> NodeRef {
        self.declaration
    }

    pub(super) const fn symbol(&self) -> SemanticSymbolId {
        self.symbol
    }

    pub(super) const fn instance_members(&self) -> Option<SymbolTableId> {
        self.instance_members
    }

    pub(super) const fn static_members(&self) -> SymbolTableId {
        self.static_members
    }

    /// Every admitted property in source declaration order.
    pub(super) fn properties(&self) -> &[ClassPropertyPlan] {
        &self.properties
    }

    pub(super) fn instance_properties(&self) -> &[ClassPropertyPlan] {
        &self.instance_properties
    }

    pub(super) fn static_properties(&self) -> &[ClassPropertyPlan] {
        &self.static_properties
    }

    pub(super) fn property_type_nodes(&self) -> impl ExactSizeIterator<Item = NodeRef> + '_ {
        self.properties.iter().map(ClassPropertyPlan::type_node)
    }
}

/// The two identities installed by the class shell query.
///
/// `instance_type` is the canonical `CLASS | REFERENCE` origin from
/// `declared.rs`; `value_type` is the independent anonymous static side.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ClassShells {
    declaration: NodeRef,
    symbol: SemanticSymbolId,
    instance_type: TypeId,
    value_type: TypeId,
}

impl ClassShells {
    pub(super) const fn declaration(self) -> NodeRef {
        self.declaration
    }

    pub(super) const fn symbol(self) -> SemanticSymbolId {
        self.symbol
    }

    pub(super) const fn instance_type(self) -> TypeId {
        self.instance_type
    }

    pub(super) const fn value_type(self) -> TypeId {
        self.value_type
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ClassInvariant {
    SymbolNotOwned(SemanticSymbolId),
    InvalidOwnerSymbol(SemanticSymbolId),
    InvalidDeclaration(NodeRef),
    InvalidName(NodeRef),
    InvalidProperty(NodeRef),
    InvalidPropertySymbol(NodeRef),
    InvalidPrototype(SemanticSymbolId),
    InvalidPlan(NodeRef),
    InvalidInstanceCache(SemanticSymbolId),
    InvalidValueCache(SemanticSymbolId),
    BootstrapUnavailable(NodeRef),
    Capacity(NodeRef),
    Publication(NodeRef),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ClassUnsupported {
    MergedDeclarations(SemanticSymbolId),
    NestedDeclaration(NodeRef),
    DeclarationModifiers(NodeRef),
    Generic(NodeRef),
    Heritage(NodeRef),
    ClassExpression(NodeRef),
    Member { node: NodeRef, kind: SyntaxKind },
    PropertyInitializer(NodeRef),
    MissingPropertyType(NodeRef),
    PropertyName { node: NodeRef, kind: SyntaxKind },
    PropertyModifiers(NodeRef),
    StaticDefiniteAssignment(NodeRef),
    ReservedStaticProperty(NodeRef),
    DuplicateProperty(NodeRef),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ClassError {
    Unsupported(ClassUnsupported),
    Invariant(ClassInvariant),
    DeclaredType(DeclaredTypeError),
}

impl From<DeclaredTypeError> for ClassError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl ClassError {
    pub(super) const fn node(self) -> Option<NodeRef> {
        match self {
            Self::Unsupported(unsupported) => Some(match unsupported {
                ClassUnsupported::MergedDeclarations(_) => return None,
                ClassUnsupported::NestedDeclaration(node)
                | ClassUnsupported::DeclarationModifiers(node)
                | ClassUnsupported::Generic(node)
                | ClassUnsupported::Heritage(node)
                | ClassUnsupported::ClassExpression(node)
                | ClassUnsupported::PropertyInitializer(node)
                | ClassUnsupported::MissingPropertyType(node)
                | ClassUnsupported::PropertyModifiers(node)
                | ClassUnsupported::StaticDefiniteAssignment(node)
                | ClassUnsupported::ReservedStaticProperty(node)
                | ClassUnsupported::DuplicateProperty(node)
                | ClassUnsupported::Member { node, .. }
                | ClassUnsupported::PropertyName { node, .. } => node,
            }),
            Self::Invariant(invariant) => Some(match invariant {
                ClassInvariant::SymbolNotOwned(_)
                | ClassInvariant::InvalidOwnerSymbol(_)
                | ClassInvariant::InvalidPrototype(_)
                | ClassInvariant::InvalidInstanceCache(_)
                | ClassInvariant::InvalidValueCache(_) => return None,
                ClassInvariant::InvalidDeclaration(node)
                | ClassInvariant::InvalidName(node)
                | ClassInvariant::InvalidProperty(node)
                | ClassInvariant::InvalidPropertySymbol(node)
                | ClassInvariant::InvalidPlan(node)
                | ClassInvariant::BootstrapUnavailable(node)
                | ClassInvariant::Capacity(node)
                | ClassInvariant::Publication(node) => node,
            }),
            Self::DeclaredType(_) => None,
        }
    }
}

const fn invariant(invariant: ClassInvariant) -> ClassError {
    ClassError::Invariant(invariant)
}

const fn unsupported(unsupported: ClassUnsupported) -> ClassError {
    ClassError::Unsupported(unsupported)
}

fn bound_symbol(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Option<SemanticSymbolId> {
    let raw = host.bound_file(node)?.symbol(node)?;
    let symbol = store.get_merged_symbol(raw)?;
    host.symbol_matches(store, node, symbol).then_some(symbol)
}

fn class_property_modifiers(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    name: NodeRef,
    modifiers: Option<&ts_ast::ModifierList>,
) -> Result<(ClassPropertySide, bool), ClassError> {
    let Some(modifiers) = modifiers else {
        return Ok((ClassPropertySide::Instance, false));
    };
    let kinds = modifiers
        .list
        .nodes
        .iter()
        .map(|node| {
            let node = NodeRef::new(declaration.arena, declaration.file, *node);
            preflight_node(store, host, node).map(|record| (node, record))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let supported = match kinds
        .iter()
        .map(|(_, record)| record.kind)
        .collect::<Vec<_>>()
        .as_slice()
    {
        [SyntaxKind::ReadonlyKeyword] => (ClassPropertySide::Instance, true),
        [SyntaxKind::StaticKeyword] => (ClassPropertySide::Static, false),
        [SyntaxKind::StaticKeyword, SyntaxKind::ReadonlyKeyword] => {
            (ClassPropertySide::Static, true)
        }
        _ => {
            return Err(unsupported(ClassUnsupported::PropertyModifiers(
                declaration,
            )));
        }
    };
    let declaration_record = preflight_node(store, host, declaration)?;
    let name_record = preflight_node(store, host, name)?;
    let mut previous_end = modifiers.list.range.start;
    if modifiers.flags.0 != 0
        || modifiers.list.has_trailing_comma
        || modifiers.list.range.start != declaration_record.range.start
        || modifiers.list.range.end > name_record.range.start
        || kinds.iter().any(|(node, record)| {
            let invalid = record.parent != Some(declaration.node)
                || record.flags.0 != 0
                || !matches!(record.data, NodeData::Token(_))
                || record.range.start < previous_end
                || record.range.start < modifiers.list.range.start
                || record.range.end > modifiers.list.range.end;
            previous_end = record.range.end;
            !node.is_for(declaration.arena, declaration.file) || invalid
        })
    {
        return Err(invariant(ClassInvariant::InvalidProperty(declaration)));
    }
    Ok(supported)
}

fn plan_property(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner: SemanticSymbolId,
    member: NodeRef,
    instance_members: Option<SymbolTableId>,
    static_members: SymbolTableId,
) -> Result<ClassPropertyPlan, ClassError> {
    let record = preflight_node(store, host, member)?;
    let NodeData::PropertyDeclaration(property) = &record.data else {
        return Err(unsupported(ClassUnsupported::Member {
            node: member,
            kind: record.kind,
        }));
    };
    if property.initializer.is_some() {
        return Err(unsupported(ClassUnsupported::PropertyInitializer(member)));
    }
    let Some(type_node) = property.type_ else {
        return Err(unsupported(ClassUnsupported::MissingPropertyType(member)));
    };
    if property.symbol.is_some()
        || property.facts != 0
        || record.flags.0 & (NODE_FLAG_JSDOC | NODE_FLAG_HAS_ERROR) != 0
    {
        return Err(invariant(ClassInvariant::InvalidProperty(member)));
    }

    let name = NodeRef::new(member.arena, member.file, property.name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(ClassUnsupported::PropertyName {
            node: name,
            kind: name_record.kind,
        }));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(member.node)
        || name_record.range.start < record.range.start
        || name_record.range.end > record.range.end
    {
        return Err(invariant(ClassInvariant::InvalidName(name)));
    }
    let (side, readonly) =
        class_property_modifiers(store, host, member, name, property.modifiers.as_ref())?;

    let type_node = NodeRef::new(member.arena, member.file, type_node);
    let type_record = preflight_node(store, host, type_node)?;
    if type_record.parent != Some(member.node)
        || type_record.range.start < name_record.range.end
        || type_record.range.end > record.range.end
    {
        return Err(invariant(ClassInvariant::InvalidProperty(member)));
    }

    let (optional, definite) = match property.postfix_token {
        None => (false, false),
        Some(token) => {
            let token = NodeRef::new(member.arena, member.file, token);
            let token_record = preflight_node(store, host, token)?;
            if token_record.parent != Some(member.node)
                || token_record.flags.0 != 0
                || !matches!(token_record.data, NodeData::Token(_))
                || token_record.range.start < name_record.range.end
                || token_record.range.end > type_record.range.start
            {
                return Err(invariant(ClassInvariant::InvalidProperty(member)));
            }
            match token_record.kind {
                SyntaxKind::QuestionToken => (true, false),
                SyntaxKind::ExclamationToken => (false, true),
                _ => return Err(invariant(ClassInvariant::InvalidProperty(member))),
            }
        }
    };
    if side == ClassPropertySide::Static && definite {
        return Err(unsupported(ClassUnsupported::StaticDefiniteAssignment(
            member,
        )));
    }
    if side == ClassPropertySide::Static
        && matches!(
            identifier.text.as_str(),
            "prototype" | "name" | "length" | "caller" | "arguments"
        )
    {
        return Err(unsupported(ClassUnsupported::ReservedStaticProperty(
            member,
        )));
    }

    let symbol = bound_symbol(store, host, member)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPropertySymbol(member)))?;
    let symbol_record = store
        .symbol(symbol)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPropertySymbol(member)))?;
    let expected_flags = SymbolFlags::PROPERTY
        | if optional {
            SymbolFlags::OPTIONAL
        } else {
            SymbolFlags::NONE
        };
    let table = match side {
        ClassPropertySide::Instance => instance_members,
        ClassPropertySide::Static => Some(static_members),
    }
    .and_then(|table| store.symbol_table(table));
    if symbol_record.flags() != expected_flags
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
        || symbol_record.declarations() != Some(&[member])
        || symbol_record.value_declaration() != Some(member)
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent() != Some(owner)
        || symbol_record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || table.and_then(|table| table.get_source(&identifier.text)) != Some(symbol)
    {
        return Err(invariant(ClassInvariant::InvalidPropertySymbol(member)));
    }

    Ok(ClassPropertyPlan {
        declaration: member,
        symbol,
        name_node: name,
        type_node,
        name: identifier.text.clone(),
        side,
        optional,
        definite,
        readonly,
    })
}

fn validate_prototype(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    exports: SymbolTableId,
) -> Result<(), ClassError> {
    let table = store
        .symbol_table(exports)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPrototype(owner)))?;
    let prototype = table
        .get_source(PROTOTYPE_NAME)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPrototype(owner)))?;
    let record = store
        .symbol(prototype)
        .ok_or_else(|| invariant(ClassInvariant::InvalidPrototype(owner)))?;
    if record.flags() != SymbolFlags::PROPERTY | SymbolFlags::PROTOTYPE
        || record.check_flags() != CheckFlags::NONE
        || record.name().as_utf8() != Some(PROTOTYPE_NAME)
        || record.declarations().is_some()
        || record.value_declaration().is_some()
        || record.members().is_some()
        || record.exports().is_some()
        || record.parent() != Some(owner)
        || record.export_symbol().is_some()
        || store.get_merged_symbol(prototype) != Some(prototype)
    {
        return Err(invariant(ClassInvariant::InvalidPrototype(owner)));
    }
    Ok(())
}

/// Produces the opaque syntax/binder proof consumed by the class shell
/// executor and the root annotation adapter.
pub(super) fn plan_nongeneric_class(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> Result<ClassDeclarationPlan, ClassError> {
    let merged = store
        .get_merged_symbol(symbol)
        .ok_or_else(|| invariant(ClassInvariant::SymbolNotOwned(symbol)))?;
    if merged != symbol {
        return Err(unsupported(ClassUnsupported::MergedDeclarations(symbol)));
    }
    let symbol_record = store
        .symbol(symbol)
        .ok_or_else(|| invariant(ClassInvariant::SymbolNotOwned(symbol)))?;
    if symbol_record.flags() != SymbolFlags::CLASS {
        return if symbol_record.flags().contains(SymbolFlags::CLASS) {
            Err(unsupported(ClassUnsupported::MergedDeclarations(symbol)))
        } else {
            Err(invariant(ClassInvariant::InvalidOwnerSymbol(symbol)))
        };
    }
    let Some([declaration]) = symbol_record.declarations() else {
        return Err(unsupported(ClassUnsupported::MergedDeclarations(symbol)));
    };
    let declaration = *declaration;
    if symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.value_declaration() != Some(declaration)
        || symbol_record.parent().is_some()
        || symbol_record.export_symbol().is_some()
    {
        return Err(invariant(ClassInvariant::InvalidOwnerSymbol(symbol)));
    }

    let declaration_record = preflight_node(store, host, declaration)?;
    let class = match &declaration_record.data {
        NodeData::ClassDeclaration(class) => class,
        NodeData::ClassExpression(_) => {
            return Err(unsupported(ClassUnsupported::ClassExpression(declaration)));
        }
        _ => return Err(invariant(ClassInvariant::InvalidDeclaration(declaration))),
    };
    if declaration_record.kind != SyntaxKind::ClassDeclaration
        || declaration_record.flags.0 & (NODE_FLAG_JSDOC | NODE_FLAG_HAS_ERROR) != 0
        || !host.symbol_matches(store, declaration, symbol)
        || class.flow_node.is_some()
        || class.local_symbol.is_some()
        || class.symbol.is_some()
        || class.next_container.is_some()
        || class.facts != 0
        || class.members.has_trailing_comma
        || class.members.range.start < declaration_record.range.start
        || class.members.range.end != declaration_record.range.end
    {
        return Err(invariant(ClassInvariant::InvalidDeclaration(declaration)));
    }
    if class.modifiers.is_some() {
        return Err(unsupported(ClassUnsupported::DeclarationModifiers(
            declaration,
        )));
    }
    if class.type_parameters.is_some() {
        return Err(unsupported(ClassUnsupported::Generic(declaration)));
    }
    if class.heritage_clauses.is_some() {
        return Err(unsupported(ClassUnsupported::Heritage(declaration)));
    }
    let Some(name) = class.name else {
        return Err(invariant(ClassInvariant::InvalidDeclaration(declaration)));
    };
    let name = NodeRef::new(declaration.arena, declaration.file, name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invariant(ClassInvariant::InvalidName(name)));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(declaration.node)
        || name_record.flags.0 != 0
        || name_record.range.start < declaration_record.range.start
        || name_record.range.end > declaration_record.range.end
        || symbol_record.name().as_utf8() != Some(identifier.text.as_str())
    {
        return Err(invariant(ClassInvariant::InvalidName(name)));
    }

    let Some(parent) = declaration_record.parent else {
        return Err(unsupported(ClassUnsupported::NestedDeclaration(
            declaration,
        )));
    };
    let parent = NodeRef::new(declaration.arena, declaration.file, parent);
    let parent_record = preflight_node(store, host, parent)?;
    let NodeData::SourceFile(source) = &parent_record.data else {
        return Err(unsupported(ClassUnsupported::NestedDeclaration(
            declaration,
        )));
    };
    if parent_record.kind != SyntaxKind::SourceFile
        || parent_record.parent.is_some()
        || source
            .statements
            .nodes
            .iter()
            .filter(|node| **node == declaration.node)
            .count()
            != 1
    {
        return Err(invariant(ClassInvariant::InvalidDeclaration(declaration)));
    }

    let instance_members = symbol_record.members();
    let static_members = symbol_record
        .exports()
        .ok_or_else(|| invariant(ClassInvariant::InvalidPrototype(symbol)))?;
    if instance_members.is_some_and(|members| store.symbol_table(members).is_none())
        || store.symbol_table(static_members).is_none()
    {
        return Err(invariant(ClassInvariant::InvalidOwnerSymbol(symbol)));
    }
    validate_prototype(store, symbol, static_members)?;

    let mut instance_properties = Vec::new();
    let mut static_properties = Vec::new();
    let mut properties = Vec::with_capacity(class.members.nodes.len());
    let mut instance_names = HashSet::new();
    let mut static_names = HashSet::new();
    let mut previous_end = class.members.range.start;
    for member in &class.members.nodes {
        let member = NodeRef::new(declaration.arena, declaration.file, *member);
        let member_record = preflight_node(store, host, member)?;
        if member_record.parent != Some(declaration.node)
            || member_record.range.start < previous_end
            || member_record.range.start < class.members.range.start
            || member_record.range.end > class.members.range.end
        {
            return Err(invariant(ClassInvariant::InvalidProperty(member)));
        }
        previous_end = member_record.range.end;
        if member_record.kind != SyntaxKind::PropertyDeclaration {
            return Err(unsupported(ClassUnsupported::Member {
                node: member,
                kind: member_record.kind,
            }));
        }
        let property = plan_property(
            store,
            host,
            symbol,
            member,
            instance_members,
            static_members,
        )?;
        let names = match property.side {
            ClassPropertySide::Instance => &mut instance_names,
            ClassPropertySide::Static => &mut static_names,
        };
        if !names.insert(property.name.clone()) {
            return Err(unsupported(ClassUnsupported::DuplicateProperty(member)));
        }
        properties.push(property.clone());
        match property.side {
            ClassPropertySide::Instance => instance_properties.push(property),
            ClassPropertySide::Static => static_properties.push(property),
        }
    }

    let instance_table = instance_members.and_then(|table| store.symbol_table(table));
    if instance_members.is_some() != !instance_properties.is_empty()
        || instance_table.is_some_and(|table| table.len() != instance_properties.len())
    {
        return Err(invariant(ClassInvariant::InvalidOwnerSymbol(symbol)));
    }
    let static_table = store
        .symbol_table(static_members)
        .expect("the class export table was validated above");
    if static_table.len() != static_properties.len() + 1 {
        return Err(invariant(ClassInvariant::InvalidOwnerSymbol(symbol)));
    }

    let local_arity =
        preflight_class_or_interface_reference(store, host, symbol, SymbolFlags::CLASS)?;
    if local_arity != 0 {
        return Err(unsupported(ClassUnsupported::Generic(declaration)));
    }
    Ok(ClassDeclarationPlan {
        declaration,
        symbol,
        instance_members,
        static_members,
        properties,
        instance_properties,
        static_properties,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StaticShellState {
    Cold,
    Warm(TypeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ClassShellState {
    instance: Option<TypeId>,
    value: StaticShellState,
}

fn exact_static_shell(
    store: &CanonicalTypeMapperStore,
    symbol: SemanticSymbolId,
    type_: TypeId,
) -> bool {
    let Some(record) = store.type_payload(type_) else {
        return false;
    };
    record.flags() == TypeFlags::OBJECT
        && record.object_flags() == ObjectFlags::ANONYMOUS
        && record.symbol() == Some(symbol)
        && record.alias().is_none()
        && matches!(record.data(), TypeData::Object(object) if object == &ObjectTypeData::default())
}

fn shell_state(
    store: &CanonicalTypeMapperStore,
    plan: &ClassDeclarationPlan,
) -> Result<ClassShellState, ClassError> {
    let instance = store
        .declared_type_links(plan.symbol)
        .and_then(|links| links.declared_type);
    let value = match store.value_symbol_links(plan.symbol) {
        None => StaticShellState::Cold,
        Some(links) if links == &ValueSymbolLinks::default() => StaticShellState::Cold,
        Some(links) if links.resolved_type.is_some() => {
            let type_ = links
                .resolved_type
                .expect("the branch checked the resolved identity");
            if links
                != &(ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
                || !exact_static_shell(store, plan.symbol, type_)
            {
                return Err(invariant(ClassInvariant::InvalidValueCache(plan.symbol)));
            }
            StaticShellState::Warm(type_)
        }
        Some(_) => {
            return Err(invariant(ClassInvariant::InvalidValueCache(plan.symbol)));
        }
    };
    let Some(undefined_type) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.undefined_type)
    else {
        return Err(invariant(ClassInvariant::BootstrapUnavailable(
            plan.declaration,
        )));
    };
    if let Some(instance) = instance {
        let Some(TypeData::Interface(interface)) =
            store.type_payload(instance).map(|record| record.data())
        else {
            return Err(invariant(ClassInvariant::InvalidInstanceCache(plan.symbol)));
        };
        if interface.base_types_resolved
            || interface.resolved_base_types.is_some()
            || interface
                .resolved_base_constructor_type
                .is_some_and(|type_| type_ != undefined_type)
            || matches!(value, StaticShellState::Warm(_))
                && interface.resolved_base_constructor_type != Some(undefined_type)
        {
            return Err(invariant(ClassInvariant::InvalidInstanceCache(plan.symbol)));
        }
    } else if matches!(value, StaticShellState::Warm(_)) {
        return Err(invariant(ClassInvariant::InvalidValueCache(plan.symbol)));
    }
    Ok(ClassShellState { instance, value })
}

/// Installs or validates the two exact class identities from a previously
/// produced plan.
///
/// Cold execution allocates exactly the instance origin, its synthetic `this`
/// type, and the anonymous static shell. It then forces the no-heritage base
/// constructor cache to canonical `undefined` before publishing the class
/// value link, matching pinned `getTypeOfFuncClassEnumModuleWorker`.
pub(super) fn execute_nongeneric_class_shells(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &ClassDeclarationPlan,
) -> Result<ClassShells, ClassError> {
    let current = plan_nongeneric_class(store, host, plan.symbol)?;
    if current != *plan {
        return Err(invariant(ClassInvariant::InvalidPlan(plan.declaration)));
    }
    let state = shell_state(store, plan)?;
    if let StaticShellState::Warm(value_type) = state.value {
        let instance_type = state
            .instance
            .expect("a validated warm static shell requires its instance");
        return Ok(ClassShells {
            declaration: plan.declaration,
            symbol: plan.symbol,
            instance_type,
            value_type,
        });
    }

    let cold_instance = state.instance.is_none();
    let additional = 1usize
        .checked_add(usize::from(cold_instance) * 2)
        .ok_or_else(|| invariant(ClassInvariant::Capacity(plan.declaration)))?;
    if !store.try_reserve_types(additional) {
        return Err(invariant(ClassInvariant::Capacity(plan.declaration)));
    }

    // `checkClassLikeDeclaration` asks for the declared instance first.
    let instance_type = store.get_declared_type_of_symbol(host, plan.symbol)?;
    if state.instance.is_some_and(|type_| type_ != instance_type) {
        return Err(invariant(ClassInvariant::InvalidInstanceCache(plan.symbol)));
    }
    // `getTypeOfFuncClassEnumModuleWorker` allocates the value object before
    // forcing the base-constructor cache.
    let value_type = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(plan.symbol))
        .ok_or_else(|| invariant(ClassInvariant::Publication(plan.declaration)))?;

    let undefined_type = store
        .intrinsic_bootstrap()
        .expect("the shell state validated bootstrap")
        .undefined_type;
    let (base_types_resolved, base_constructor, base_types) = {
        let Some(TypeData::Interface(interface)) = store
            .type_payload(instance_type)
            .map(|record| record.data())
        else {
            return Err(invariant(ClassInvariant::InvalidInstanceCache(plan.symbol)));
        };
        (
            interface.base_types_resolved,
            interface.resolved_base_constructor_type,
            interface.resolved_base_types.clone(),
        )
    };
    if base_types_resolved
        || base_types.is_some()
        || base_constructor.is_some_and(|type_| type_ != undefined_type)
    {
        return Err(invariant(ClassInvariant::InvalidInstanceCache(plan.symbol)));
    }
    if base_constructor.is_none() {
        assert!(store.set_interface_base_resolution(
            instance_type,
            base_types_resolved,
            Some(undefined_type),
            base_types,
        ));
    }
    assert!(store.set_value_symbol_links(
        plan.symbol,
        ValueSymbolLinks {
            resolved_type: Some(value_type),
            ..ValueSymbolLinks::default()
        },
    ));

    let resolved = shell_state(store, plan)?;
    if resolved.instance != Some(instance_type)
        || resolved.value != StaticShellState::Warm(value_type)
    {
        return Err(invariant(ClassInvariant::Publication(plan.declaration)));
    }
    Ok(ClassShells {
        declaration: plan.declaration,
        symbol: plan.symbol,
        instance_type,
        value_type,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{FileId, NodeArena, NodeData};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
        CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        IntrinsicBootstrapOptions, SemanticStore,
        declared::type_list_key,
        mapper::TypeMapper,
        type_records::{TypeCacheState, TypeParameterData, TypeRecord},
    };

    type TestStore = SemanticStore<TypeRecord, TypeMapper>;

    struct Fixture {
        parsed: ParseResult,
        file: FileId,
        files: BTreeMap<FileId, BoundFile>,
        store: TestStore,
    }

    fn fixture(source: &str) -> Fixture {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(91);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/classes.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
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

    fn class_node(fixture: &Fixture, name: &str) -> NodeRef {
        let node = fixture
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::ClassDeclaration(class) = &record.data else {
                    return None;
                };
                let name_node = class.name.and_then(|name| fixture.parsed.arena.get(name))?;
                let NodeData::Identifier(identifier) = &name_node.data else {
                    return None;
                };
                (identifier.text == name).then_some(node)
            })
            .unwrap();
        NodeRef::new(fixture.parsed.arena.id(), fixture.file, node)
    }

    fn class_symbol(fixture: &Fixture, name: &str) -> SemanticSymbolId {
        fixture.files[&fixture.file]
            .symbol(class_node(fixture, name))
            .unwrap()
    }

    #[test]
    fn empty_class_installs_exact_instance_and_value_shells_then_replays_warm() {
        let mut fixture = fixture("class Plain {}");
        let symbol = class_symbol(&fixture, "Plain");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class(&fixture.store, &host, symbol).unwrap();
        let type_count = fixture.store.type_len();
        let link_counts = fixture.store.checker_link_allocated_lengths();

        let shells = execute_nongeneric_class_shells(&mut fixture.store, &host, &plan).unwrap();
        assert_eq!(fixture.store.type_len(), type_count + 3);
        assert_eq!(shells.declaration(), class_node(&fixture, "Plain"));
        assert_eq!(shells.symbol(), symbol);
        assert_ne!(shells.instance_type(), shells.value_type());
        assert_eq!(
            fixture
                .store
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type),
            Some(shells.instance_type())
        );
        assert_eq!(
            fixture.store.value_symbol_links(symbol),
            Some(&ValueSymbolLinks {
                resolved_type: Some(shells.value_type()),
                ..ValueSymbolLinks::default()
            })
        );

        let instance_record = fixture.store.type_payload(shells.instance_type()).unwrap();
        assert_eq!(instance_record.flags(), TypeFlags::OBJECT);
        assert_eq!(
            instance_record.object_flags(),
            ObjectFlags::CLASS | ObjectFlags::REFERENCE
        );
        assert_eq!(instance_record.symbol(), Some(symbol));
        let TypeData::Interface(instance) = instance_record.data() else {
            panic!("class instance must use InterfaceTypeData")
        };
        assert_eq!(
            instance.resolved_base_constructor_type,
            Some(fixture.store.intrinsic_bootstrap().unwrap().undefined_type)
        );
        assert!(!instance.base_types_resolved);
        assert_eq!(instance.resolved_base_types, None);
        assert_eq!(
            instance.reference.object.target,
            Some(shells.instance_type())
        );
        assert_eq!(instance.reference.resolved_type_arguments, Some(Vec::new()));
        let all = instance.all_type_parameters.as_deref().unwrap();
        assert_eq!(all.len(), 1);
        assert_eq!(instance.this_type, Some(all[0]));
        let TypeCacheState::Allocated(instantiations) = &instance.reference.object.instantiations
        else {
            panic!("class origin owns its self-instantiation cache")
        };
        assert_eq!(
            instantiations.get(&type_list_key(&[])),
            Some(&shells.instance_type())
        );
        let TypeData::TypeParameter(TypeParameterData {
            constraint,
            is_this_type,
            ..
        }) = fixture.store.type_payload(all[0]).unwrap().data()
        else {
            panic!("class owns a synthetic this parameter")
        };
        assert!(*is_this_type);
        assert_eq!(*constraint, Some(shells.instance_type()));

        let value_record = fixture.store.type_payload(shells.value_type()).unwrap();
        assert_eq!(value_record.flags(), TypeFlags::OBJECT);
        assert_eq!(value_record.object_flags(), ObjectFlags::ANONYMOUS);
        assert_eq!(value_record.symbol(), Some(symbol));
        assert!(matches!(
            value_record.data(),
            TypeData::Object(object) if object == &ObjectTypeData::default()
        ));

        let warm_state = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            execute_nongeneric_class_shells(&mut fixture.store, &host, &plan),
            Ok(shells)
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            warm_state
        );
        assert_ne!(fixture.store.checker_link_allocated_lengths(), link_counts);
    }

    #[test]
    fn annotated_property_plan_preserves_instance_static_and_postfix_split() {
        let fixture = fixture(
            "class Model { readonly value?: string; definite!: number; static readonly count: number; }",
        );
        let symbol = class_symbol(&fixture, "Model");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class(&fixture.store, &host, symbol).unwrap();

        assert_eq!(plan.declaration(), class_node(&fixture, "Model"));
        assert_eq!(plan.symbol(), symbol);
        assert!(plan.instance_members().is_some());
        assert_eq!(plan.instance_properties().len(), 2);
        assert_eq!(plan.static_properties().len(), 1);
        assert_eq!(plan.property_type_nodes().len(), 3);
        assert_eq!(
            plan.properties()
                .iter()
                .map(ClassPropertyPlan::name)
                .collect::<Vec<_>>(),
            vec!["value", "definite", "count"]
        );

        let value = &plan.instance_properties()[0];
        assert_eq!(value.name(), "value");
        assert_eq!(value.side(), ClassPropertySide::Instance);
        assert!(value.optional());
        assert!(!value.definite());
        assert!(value.readonly());

        let definite = &plan.instance_properties()[1];
        assert_eq!(definite.name(), "definite");
        assert!(!definite.optional());
        assert!(definite.definite());
        assert!(!definite.readonly());

        let count = &plan.static_properties()[0];
        assert_eq!(count.name(), "count");
        assert_eq!(count.side(), ClassPropertySide::Static);
        assert!(!count.optional());
        assert!(!count.definite());
        assert!(count.readonly());
        let static_table = fixture.store.symbol_table(plan.static_members()).unwrap();
        assert_eq!(static_table.len(), 2);
        assert!(static_table.get_source(PROTOTYPE_NAME).is_some());
    }

    #[test]
    fn existing_instance_shell_stays_canonical_when_the_static_side_is_cold() {
        let mut fixture = fixture("class Staged {}");
        let symbol = class_symbol(&fixture, "Staged");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let instance = fixture
            .store
            .get_declared_type_of_symbol(&host, symbol)
            .unwrap();
        let TypeData::Interface(data) = fixture.store.type_payload(instance).unwrap().data() else {
            panic!("declared class identity is an interface record")
        };
        assert_eq!(data.resolved_base_constructor_type, None);
        let plan = plan_nongeneric_class(&fixture.store, &host, symbol).unwrap();
        let type_count = fixture.store.type_len();

        let shells = execute_nongeneric_class_shells(&mut fixture.store, &host, &plan).unwrap();
        assert_eq!(shells.instance_type(), instance);
        assert_eq!(fixture.store.type_len(), type_count + 1);
        let TypeData::Interface(data) = fixture.store.type_payload(instance).unwrap().data() else {
            panic!("declared class identity remains an interface record")
        };
        assert_eq!(
            data.resolved_base_constructor_type,
            Some(fixture.store.intrinsic_bootstrap().unwrap().undefined_type)
        );
        assert!(!data.base_types_resolved);
    }

    #[test]
    fn warm_value_without_instance_and_poisoned_value_reject_atomically() {
        let mut fixture = fixture("class Poisoned {}");
        let symbol = class_symbol(&fixture, "Poisoned");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let plan = plan_nongeneric_class(&fixture.store, &host, symbol).unwrap();
        let value = fixture
            .store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(symbol))
            .unwrap();
        assert!(fixture.store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(value),
                ..ValueSymbolLinks::default()
            }
        ));
        let state = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            execute_nongeneric_class_shells(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidValueCache(symbol)))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            state
        );
        assert!(
            fixture
                .store
                .declared_type_links(symbol)
                .and_then(|links| links.declared_type)
                .is_none()
        );

        let wrong = fixture.store.intrinsic_bootstrap().unwrap().string_type;
        assert!(fixture.store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(wrong),
                ..ValueSymbolLinks::default()
            }
        ));
        let poisoned = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            execute_nongeneric_class_shells(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidValueCache(symbol)))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            poisoned
        );
    }

    #[test]
    fn pre_resolved_base_bit_is_not_an_exact_shell_state() {
        let mut fixture = fixture("class BasePoison {}");
        let symbol = class_symbol(&fixture, "BasePoison");
        let bound = &fixture.files[&fixture.file];
        let host = host(&fixture.parsed.arena, bound);
        let instance = fixture
            .store
            .get_declared_type_of_symbol(&host, symbol)
            .unwrap();
        assert!(
            fixture
                .store
                .set_interface_base_resolution(instance, true, None, None)
        );
        let plan = plan_nongeneric_class(&fixture.store, &host, symbol).unwrap();
        let state = (
            fixture.store.type_len(),
            fixture.store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            execute_nongeneric_class_shells(&mut fixture.store, &host, &plan),
            Err(invariant(ClassInvariant::InvalidInstanceCache(symbol)))
        );
        assert_eq!(
            (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            ),
            state
        );
        assert!(
            fixture
                .store
                .value_symbol_links(symbol)
                .is_none_or(|links| links == &ValueSymbolLinks::default())
        );
    }

    #[test]
    fn unsupported_class_families_are_typed_and_do_not_publish_shells() {
        let cases = [
            ("class Generic<T> {}", "Generic"),
            ("class Base {} class Derived extends Base {}", "Derived"),
            ("class Method { method(): void {} }", "Method"),
            ("class Initialized { value = 1; }", "Initialized"),
            ("class Reserved { static prototype: number; }", "Reserved"),
            (
                "class StaticDefinite { static value!: number; }",
                "StaticDefinite",
            ),
        ];
        for (source, name) in cases {
            let fixture = fixture(source);
            let symbol = class_symbol(&fixture, name);
            let bound = &fixture.files[&fixture.file];
            let host = host(&fixture.parsed.arena, bound);
            let state = (
                fixture.store.type_len(),
                fixture.store.checker_link_allocated_lengths(),
            );
            assert!(matches!(
                plan_nongeneric_class(&fixture.store, &host, symbol),
                Err(ClassError::Unsupported(_))
            ));
            assert_eq!(
                (
                    fixture.store.type_len(),
                    fixture.store.checker_link_allocated_lengths(),
                ),
                state
            );
            assert!(
                fixture
                    .store
                    .declared_type_links(symbol)
                    .and_then(|links| links.declared_type)
                    .is_none()
            );
            assert!(
                fixture
                    .store
                    .value_symbol_links(symbol)
                    .is_none_or(|links| links == &ValueSymbolLinks::default())
            );
        }
    }
}
