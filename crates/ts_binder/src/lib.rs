//! Declaration binding and lexical symbol tables.

use std::{
    collections::{BTreeMap, HashMap},
    ops::{BitOr, BitOrAssign},
};

use ts_ast::{
    FileId, NodeArena, NodeData, NodeFlags, NodeId, NodeRef, SymbolId, SyntaxKind,
};
use ts_diagnostics::{Diagnostic, message_by_code};

/// TypeScript symbol meanings. Bit positions match the upstream compiler.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct SymbolFlags(u32);

impl SymbolFlags {
    pub const NONE: Self = Self(0);
    pub const FUNCTION_SCOPED_VARIABLE: Self = Self(1 << 0);
    pub const BLOCK_SCOPED_VARIABLE: Self = Self(1 << 1);
    pub const PROPERTY: Self = Self(1 << 2);
    pub const ENUM_MEMBER: Self = Self(1 << 3);
    pub const FUNCTION: Self = Self(1 << 4);
    pub const CLASS: Self = Self(1 << 5);
    pub const INTERFACE: Self = Self(1 << 6);
    pub const CONST_ENUM: Self = Self(1 << 7);
    pub const REGULAR_ENUM: Self = Self(1 << 8);
    pub const VALUE_MODULE: Self = Self(1 << 9);
    pub const NAMESPACE_MODULE: Self = Self(1 << 10);
    pub const METHOD: Self = Self(1 << 13);
    pub const CONSTRUCTOR: Self = Self(1 << 14);
    pub const GET_ACCESSOR: Self = Self(1 << 15);
    pub const SET_ACCESSOR: Self = Self(1 << 16);
    pub const TYPE_PARAMETER: Self = Self(1 << 18);
    pub const TYPE_ALIAS: Self = Self(1 << 19);
    pub const ALIAS: Self = Self(1 << 21);

    pub const VARIABLE: Self =
        Self(Self::FUNCTION_SCOPED_VARIABLE.0 | Self::BLOCK_SCOPED_VARIABLE.0);
    pub const ENUM: Self = Self(Self::CONST_ENUM.0 | Self::REGULAR_ENUM.0);
    pub const MODULE: Self = Self(Self::VALUE_MODULE.0 | Self::NAMESPACE_MODULE.0);

    #[must_use]
    pub const fn bits(self) -> u32 {
        self.0
    }

    #[must_use]
    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }

    #[must_use]
    pub const fn intersects(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

impl BitOr for SymbolFlags {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for SymbolFlags {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

/// One bound declaration symbol.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Symbol {
    pub id: SymbolId,
    pub name: String,
    pub flags: SymbolFlags,
    pub declarations: Vec<NodeId>,
    pub value_declaration: Option<NodeId>,
    pub parent: Option<SymbolId>,
    pub members: SymbolTable,
    pub target: Option<SymbolId>,
}

/// Stable storage for symbols allocated in binding order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SymbolArena {
    symbols: Vec<Symbol>,
}

impl SymbolArena {
    #[must_use]
    pub fn get(&self, id: SymbolId) -> Option<&Symbol> {
        self.symbols.get(id.0 as usize)
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }

    #[must_use]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &Symbol> {
        self.symbols.iter()
    }

    fn get_mut(&mut self, id: SymbolId) -> Option<&mut Symbol> {
        self.symbols.get_mut(id.0 as usize)
    }

    fn alloc(
        &mut self,
        name: String,
        flags: SymbolFlags,
        declaration: NodeId,
        parent: Option<SymbolId>,
    ) -> SymbolId {
        let id = SymbolId(
            u32::try_from(self.symbols.len()).expect("symbol arena exceeds u32::MAX symbols"),
        );
        self.symbols.push(Symbol {
            id,
            name,
            flags,
            declarations: vec![declaration],
            value_declaration: is_value(flags).then_some(declaration),
            parent,
            members: SymbolTable::default(),
            target: None,
        });
        id
    }
}

/// Deterministic mapping from escaped declaration names to symbols.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SymbolTable(BTreeMap<String, SymbolId>);

impl SymbolTable {
    #[must_use]
    pub fn get(&self, name: &str) -> Option<SymbolId> {
        self.0.get(name).copied()
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    #[must_use]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (&str, SymbolId)> {
        self.0.iter().map(|(name, id)| (name.as_str(), *id))
    }

    fn insert(&mut self, name: String, id: SymbolId) {
        self.0.insert(name, id);
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ScopeId(u32);

impl ScopeId {
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScopeKind {
    SourceFile,
    Block,
    Function,
    Class,
    Interface,
    Enum,
    Module,
    TypeAlias,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Scope {
    pub id: ScopeId,
    pub kind: ScopeKind,
    pub owner: NodeId,
    pub parent: Option<ScopeId>,
    pub symbols: SymbolTable,
}

/// A declaration diagnostic associated with its AST node.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindDiagnostic {
    pub node: NodeId,
    pub diagnostic: Diagnostic,
}

/// Complete binding output for one source-file arena.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BindResult {
    pub file_id: FileId,
    pub symbols: SymbolArena,
    pub scopes: Vec<Scope>,
    pub node_symbols: BTreeMap<NodeId, SymbolId>,
    pub node_scopes: BTreeMap<NodeId, ScopeId>,
    pub containers: BTreeMap<NodeId, NodeId>,
    pub exports: SymbolTable,
    pub diagnostics: Vec<BindDiagnostic>,
}

impl BindResult {
    /// Converts a file-local node ID into a program-wide identity.
    #[must_use]
    pub const fn node_ref(&self, node: NodeId) -> NodeRef {
        NodeRef::new(self.file_id, node)
    }

    #[must_use]
    pub fn root_scope(&self) -> Option<&Scope> {
        self.scopes.first()
    }

    #[must_use]
    pub fn scope(&self, id: ScopeId) -> Option<&Scope> {
        self.scopes.get(id.index())
    }

    /// Resolves a name using the lexical scope containing `node`.
    #[must_use]
    pub fn resolve_name_at(&self, node: NodeId, name: &str) -> Option<SymbolId> {
        if let Some(symbol) = self.node_symbols.get(&node).copied()
            && self
                .symbols
                .get(symbol)
                .is_some_and(|symbol| symbol.name == name)
        {
            return Some(symbol);
        }
        let container = self.containers.get(&node).copied().unwrap_or(node);
        let mut scope = self.node_scopes.get(&container).copied().or_else(|| {
            self.scopes
                .iter()
                .find(|scope| scope.owner == container)
                .map(|scope| scope.id)
        })?;
        loop {
            let current = self.scope(scope)?;
            if let Some(symbol) = current.symbols.get(name) {
                return Some(symbol);
            }
            if current.kind == ScopeKind::Module
                && let Some(symbol) = self.node_symbols.get(&current.owner)
                && let Some(symbol) = self.symbols.get(*symbol)
                && let Some(member) = symbol.members.get(name)
            {
                return Some(member);
            }
            scope = current.parent?;
        }
    }
}

/// Binds declarations reachable from one source-file node.
#[must_use]
pub fn bind_source_file(arena: &NodeArena, source_file: NodeId) -> BindResult {
    bind_source_file_in_file(arena, source_file, FileId::default())
}

/// Binds one source file using its stable identity in a compiler Program.
#[must_use]
pub fn bind_source_file_in_file(
    arena: &NodeArena,
    source_file: NodeId,
    file_id: FileId,
) -> BindResult {
    Binder::new(arena, file_id).bind(source_file)
}

struct Binder<'a> {
    arena: &'a NodeArena,
    result: BindResult,
    children: HashMap<NodeId, Vec<NodeId>>,
    implicit_export_depth: usize,
}

impl<'a> Binder<'a> {
    fn new(arena: &'a NodeArena, file_id: FileId) -> Self {
        let mut children = HashMap::<NodeId, Vec<NodeId>>::new();
        for (id, node) in arena.iter() {
            if let Some(parent) = node.parent {
                children.entry(parent).or_default().push(id);
            }
        }
        Self {
            arena,
            result: BindResult {
                file_id,
                ..BindResult::default()
            },
            children,
            implicit_export_depth: 0,
        }
    }

    fn bind(mut self, source_file: NodeId) -> BindResult {
        let Some(node) = self.arena.get(source_file) else {
            return self.result;
        };
        if !matches!(node.data, NodeData::SourceFile(_)) {
            return self.result;
        }
        let root = self.create_scope(ScopeKind::SourceFile, source_file, None);
        self.result.node_scopes.insert(source_file, root);
        self.result.containers.insert(source_file, source_file);
        self.bind_node(source_file, root, source_file, None);
        self.result
    }

    // Keeping declaration-kind dispatch together makes additions auditable
    // against NodeData as the port expands.
    #[allow(clippy::too_many_lines)]
    fn bind_node(
        &mut self,
        node_id: NodeId,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        self.result.containers.insert(node_id, container);
        let Some(node) = self.arena.get(node_id) else {
            return;
        };
        if self.implicit_export_depth > 0 && self.has_modifier(node_id, SyntaxKind::DeclareKeyword)
        {
            let message = message_by_code(1038).expect("binder diagnostic is in catalog");
            self.result.diagnostics.push(BindDiagnostic {
                node: node_id,
                diagnostic: Diagnostic::new(message),
            });
        }
        match &node.data {
            NodeData::SourceFile(data) => {
                for statement in &data.statements.nodes {
                    self.bind_node(*statement, scope, node_id, parent_symbol);
                }
            }
            NodeData::Block(data) => {
                let block_scope = self.create_scope(ScopeKind::Block, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, block_scope);
                for statement in &data.statements.nodes {
                    self.bind_node(*statement, block_scope, node_id, parent_symbol);
                }
            }
            NodeData::CaseBlock(data) => {
                let case_scope = self.create_scope(ScopeKind::Block, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, case_scope);
                for clause in &data.clauses.nodes {
                    self.bind_node(*clause, case_scope, node_id, parent_symbol);
                }
            }
            NodeData::CatchClause(data) => {
                let catch_scope = self.create_scope(ScopeKind::Block, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, catch_scope);
                if let Some(variable) = data.variable_declaration {
                    self.bind_node(variable, catch_scope, node_id, parent_symbol);
                }
                self.bind_node(data.block, catch_scope, node_id, parent_symbol);
            }
            NodeData::ForStatement(data) => {
                let loop_scope = self.create_scope(ScopeKind::Block, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, loop_scope);
                if let Some(initializer) = data.initializer {
                    self.bind_node(initializer, loop_scope, node_id, parent_symbol);
                }
                if let Some(condition) = data.condition {
                    self.bind_node(condition, loop_scope, node_id, parent_symbol);
                }
                if let Some(incrementor) = data.incrementor {
                    self.bind_node(incrementor, loop_scope, node_id, parent_symbol);
                }
                self.bind_node(data.statement, loop_scope, node_id, parent_symbol);
            }
            NodeData::ForInOrOfStatement(data) => {
                let loop_scope = self.create_scope(ScopeKind::Block, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, loop_scope);
                self.bind_node(data.initializer, loop_scope, node_id, parent_symbol);
                self.bind_node(data.expression, loop_scope, node_id, parent_symbol);
                self.bind_node(data.statement, loop_scope, node_id, parent_symbol);
            }
            NodeData::ModuleBlock(data) => {
                self.result.node_scopes.insert(node_id, scope);
                for statement in &data.statements.nodes {
                    self.bind_node(*statement, scope, node_id, parent_symbol);
                }
            }
            NodeData::FunctionDeclaration(data) => {
                let symbol = data.name.and_then(|name| {
                    self.declare_and_export(
                        scope,
                        node_id,
                        name,
                        SymbolFlags::FUNCTION,
                        parent_symbol,
                    )
                });
                let function_scope = self.create_scope(ScopeKind::Function, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, function_scope);
                self.bind_type_parameters(
                    data.type_parameters.as_ref(),
                    function_scope,
                    node_id,
                    symbol,
                );
                for parameter in &data.parameters.nodes {
                    self.bind_parameter(*parameter, function_scope, node_id, symbol);
                }
                if let Some(return_type) = data.type_ {
                    self.bind_node(return_type, function_scope, node_id, symbol);
                }
                if let Some(body) = data.body {
                    self.bind_node(body, function_scope, node_id, symbol);
                }
            }
            NodeData::ClassDeclaration(data) => {
                let symbol = data.name.and_then(|name| {
                    self.declare_and_export(scope, node_id, name, SymbolFlags::CLASS, parent_symbol)
                });
                let class_scope = self.create_scope(ScopeKind::Class, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, class_scope);
                self.bind_type_parameters(
                    data.type_parameters.as_ref(),
                    class_scope,
                    node_id,
                    symbol,
                );
                for member in &data.members.nodes {
                    self.bind_node(*member, class_scope, node_id, symbol);
                }
                if let Some(heritage) = &data.heritage_clauses {
                    for clause in &heritage.nodes {
                        self.bind_node(*clause, class_scope, node_id, symbol);
                    }
                }
            }
            NodeData::ClassExpression(data) => {
                // A named class expression introduces its name only in the class's own
                // lexical scope. Binding it in the enclosing scope would incorrectly
                // expose the name after the expression, while omitting it leaves static
                // field initializers and methods unable to resolve self references.
                let class_scope = self.create_scope(ScopeKind::Class, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, class_scope);
                let symbol = data.name.and_then(|name| {
                    self.declare_named(
                        class_scope,
                        node_id,
                        name,
                        SymbolFlags::CLASS,
                        parent_symbol,
                    )
                });
                self.bind_type_parameters(
                    data.type_parameters.as_ref(),
                    class_scope,
                    node_id,
                    symbol,
                );
                for member in &data.members.nodes {
                    self.bind_node(*member, class_scope, node_id, symbol);
                }
                if let Some(heritage) = &data.heritage_clauses {
                    for clause in &heritage.nodes {
                        self.bind_node(*clause, class_scope, node_id, symbol);
                    }
                }
            }
            NodeData::InterfaceDeclaration(data) => {
                let symbol = self.declare_and_export(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::INTERFACE,
                    parent_symbol,
                );
                let interface_scope = self.create_scope(ScopeKind::Interface, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, interface_scope);
                self.bind_type_parameters(
                    data.type_parameters.as_ref(),
                    interface_scope,
                    node_id,
                    symbol,
                );
                for member in &data.members.nodes {
                    self.bind_node(*member, interface_scope, node_id, symbol);
                }
                if let Some(heritage) = &data.heritage_clauses {
                    for clause in &heritage.nodes {
                        self.bind_node(*clause, interface_scope, node_id, symbol);
                    }
                }
            }
            NodeData::TypeAliasDeclaration(data) => {
                let symbol = self.declare_and_export(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::TYPE_ALIAS,
                    parent_symbol,
                );
                if data.type_parameters.is_some() {
                    let alias_scope = self.create_scope(ScopeKind::TypeAlias, node_id, Some(scope));
                    self.result.node_scopes.insert(node_id, alias_scope);
                    self.bind_type_parameters(
                        data.type_parameters.as_ref(),
                        alias_scope,
                        node_id,
                        symbol,
                    );
                    self.bind_node(data.type_, alias_scope, node_id, symbol);
                } else {
                    self.bind_node(data.type_, scope, container, symbol);
                }
            }
            NodeData::EnumDeclaration(data) => {
                let flags = if self.has_modifier(node_id, SyntaxKind::ConstKeyword) {
                    SymbolFlags::CONST_ENUM
                } else {
                    SymbolFlags::REGULAR_ENUM
                };
                let symbol =
                    self.declare_and_export(scope, node_id, data.name, flags, parent_symbol);
                let enum_scope = self.create_scope(ScopeKind::Enum, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, enum_scope);
                for member in &data.members.nodes {
                    self.bind_node(*member, enum_scope, node_id, symbol);
                }
            }
            NodeData::ModuleDeclaration(data) => {
                let ambient = self.implicit_export_depth > 0
                    || self.has_modifier(node_id, SyntaxKind::DeclareKeyword);
                let symbol = self.declare_and_export(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::NAMESPACE_MODULE,
                    parent_symbol,
                );
                let module_scope = self.create_scope(ScopeKind::Module, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, module_scope);
                if let Some(body) = data.body {
                    if ambient {
                        self.implicit_export_depth += 1;
                    }
                    self.bind_node(body, module_scope, node_id, symbol);
                    if ambient {
                        self.implicit_export_depth -= 1;
                    }
                }
            }
            NodeData::EnumMember(data) => {
                self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::ENUM_MEMBER,
                    parent_symbol,
                );
            }
            NodeData::VariableStatement(data) => {
                self.bind_variable_list(data.declaration_list, scope, container, parent_symbol);
                if self.should_export(node_id, parent_symbol) {
                    self.export_variable_list(data.declaration_list, parent_symbol);
                }
            }
            NodeData::VariableDeclarationList(_) => {
                self.bind_variable_list(node_id, scope, container, parent_symbol);
            }
            NodeData::VariableDeclaration(data) => {
                self.declare_binding_name(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::BLOCK_SCOPED_VARIABLE,
                    parent_symbol,
                );
            }
            NodeData::PropertyDeclaration(data) => {
                self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::PROPERTY,
                    parent_symbol,
                );
                if let Some(initializer) = data.initializer {
                    self.bind_node(initializer, scope, container, parent_symbol);
                }
                if let Some(type_) = data.type_ {
                    self.bind_node(type_, scope, container, parent_symbol);
                }
            }
            NodeData::PropertySignatureDeclaration(data) => {
                self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::PROPERTY,
                    parent_symbol,
                );
                self.bind_node(data.type_, scope, container, parent_symbol);
            }
            NodeData::MethodDeclaration(data) => {
                let symbol = self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::METHOD,
                    parent_symbol,
                );
                self.bind_function_like(
                    node_id,
                    scope,
                    symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.body,
                );
                if let Some(type_) = data.type_ {
                    self.bind_node(type_, scope, node_id, symbol);
                }
            }
            NodeData::MethodSignatureDeclaration(data) => {
                let symbol = self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::METHOD,
                    parent_symbol,
                );
                self.bind_function_like(
                    node_id,
                    scope,
                    symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    None,
                );
                if let Some(type_) = data.type_ {
                    self.bind_node(type_, scope, node_id, symbol);
                }
            }
            NodeData::GetAccessorDeclaration(data) => {
                let symbol = self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::GET_ACCESSOR,
                    parent_symbol,
                );
                self.bind_function_like(
                    node_id,
                    scope,
                    symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.body,
                );
            }
            NodeData::SetAccessorDeclaration(data) => {
                let symbol = self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::SET_ACCESSOR,
                    parent_symbol,
                );
                self.bind_function_like(
                    node_id,
                    scope,
                    symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.body,
                );
            }
            NodeData::ConstructorDeclaration(data) => {
                let symbol = self.declare_synthetic(
                    scope,
                    node_id,
                    "__constructor",
                    SymbolFlags::CONSTRUCTOR,
                    parent_symbol,
                );
                self.bind_function_like(
                    node_id,
                    scope,
                    Some(symbol),
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.body,
                );
            }
            NodeData::FunctionTypeNode(data) => {
                self.bind_signature_type(
                    node_id,
                    scope,
                    parent_symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.type_,
                );
            }
            NodeData::ConstructorTypeNode(data) => {
                self.bind_signature_type(
                    node_id,
                    scope,
                    parent_symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.type_,
                );
            }
            NodeData::CallSignatureDeclaration(data) => {
                self.bind_signature_type(
                    node_id,
                    scope,
                    parent_symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.type_,
                );
            }
            NodeData::ConstructSignatureDeclaration(data) => {
                self.bind_signature_type(
                    node_id,
                    scope,
                    parent_symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    data.type_,
                );
            }
            NodeData::TypeLiteralNode(_) => {
                let type_scope = self.create_scope(ScopeKind::Interface, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, type_scope);
                self.bind_children(node_id, type_scope, node_id, parent_symbol);
            }
            NodeData::ArrowFunction(data) => {
                self.bind_function_like(
                    node_id,
                    scope,
                    parent_symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    Some(data.body),
                );
            }
            NodeData::FunctionExpression(data) => {
                self.bind_function_like(
                    node_id,
                    scope,
                    parent_symbol,
                    data.type_parameters.as_ref(),
                    &data.parameters.nodes,
                    Some(data.body),
                );
            }
            NodeData::TypeParameterDeclaration(data) => {
                self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::TYPE_PARAMETER,
                    parent_symbol,
                );
                if let Some(constraint) = data.constraint {
                    self.bind_node(constraint, scope, container, parent_symbol);
                }
                if let Some(default_type) = data.default_type {
                    self.bind_node(default_type, scope, container, parent_symbol);
                }
            }
            NodeData::ImportDeclaration(data) => {
                if let Some(clause) = data.import_clause {
                    self.bind_import_clause(clause, scope, container, parent_symbol);
                }
                self.bind_node(data.module_specifier, scope, container, parent_symbol);
            }
            NodeData::ImportEqualsDeclaration(data) => {
                self.declare_and_export(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::ALIAS,
                    parent_symbol,
                );
                self.bind_node(data.module_reference, scope, container, parent_symbol);
            }
            NodeData::ExportDeclaration(data) => {
                if let Some(clause) = data.export_clause {
                    self.bind_export_clause(clause, scope, container, parent_symbol);
                }
                if let Some(module_specifier) = data.module_specifier {
                    self.bind_node(module_specifier, scope, container, parent_symbol);
                }
            }
            NodeData::ExportAssignment(data) => {
                let name = if data.is_export_equals {
                    "export="
                } else {
                    "default"
                };
                self.declare_export_alias(node_id, name, None, parent_symbol);
                self.bind_node(data.expression, scope, container, parent_symbol);
            }
            NodeData::BinaryExpression(_) => {
                self.bind_binary_expression_children(node_id, scope, container, parent_symbol);
            }
            _ => self.bind_children(node_id, scope, container, parent_symbol),
        }
    }

    fn bind_binary_expression_children(
        &mut self,
        node_id: NodeId,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        let mut pending = self
            .children
            .get(&node_id)
            .into_iter()
            .flatten()
            .rev()
            .copied()
            .collect::<Vec<_>>();
        while let Some(child) = pending.pop() {
            if matches!(
                self.arena.get(child).map(|node| &node.data),
                Some(NodeData::BinaryExpression(_))
            ) {
                self.result.containers.insert(child, container);
                if let Some(children) = self.children.get(&child) {
                    pending.extend(children.iter().rev().copied());
                }
            } else {
                self.bind_node(child, scope, container, parent_symbol);
            }
        }
    }

    fn bind_variable_list(
        &mut self,
        list_id: NodeId,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        self.result.containers.insert(list_id, container);
        let Some(node) = self.arena.get(list_id) else {
            return;
        };
        let NodeData::VariableDeclarationList(data) = &node.data else {
            return;
        };
        let block_scoped = node.flags.0 & (NodeFlags(1 << 0).0 | NodeFlags(1 << 1).0) != 0;
        let flags = if block_scoped {
            SymbolFlags::BLOCK_SCOPED_VARIABLE
        } else {
            SymbolFlags::FUNCTION_SCOPED_VARIABLE
        };
        let target_scope = if block_scoped {
            scope
        } else {
            self.nearest_var_scope(scope)
        };
        for declaration in &data.declarations.nodes {
            self.result.containers.insert(*declaration, container);
            if let Some(NodeData::VariableDeclaration(declaration_data)) =
                self.arena.get(*declaration).map(|node| &node.data)
            {
                let name = declaration_data.name;
                let type_ = declaration_data.type_;
                let initializer = declaration_data.initializer;
                self.declare_binding_name(target_scope, *declaration, name, flags, parent_symbol);
                if let Some(type_) = type_ {
                    self.bind_node(type_, scope, container, parent_symbol);
                }
                if let Some(initializer) = initializer {
                    self.bind_node(initializer, scope, container, parent_symbol);
                }
            }
        }
    }

    fn export_variable_list(&mut self, list_id: NodeId, parent_symbol: Option<SymbolId>) {
        let Some(NodeData::VariableDeclarationList(list)) =
            self.arena.get(list_id).map(|node| &node.data)
        else {
            return;
        };
        for declaration in &list.declarations.nodes {
            let Some(symbol_id) = self.result.node_symbols.get(declaration).copied() else {
                continue;
            };
            let Some(symbol) = self.result.symbols.get(symbol_id) else {
                continue;
            };
            let name = symbol.name.clone();
            if let Some(parent) = parent_symbol {
                self.result
                    .symbols
                    .get_mut(parent)
                    .unwrap()
                    .members
                    .insert(name, symbol_id);
            } else {
                self.result.exports.insert(name, symbol_id);
            }
        }
    }

    fn bind_parameter(
        &mut self,
        parameter: NodeId,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        self.result.containers.insert(parameter, container);
        if let Some(NodeData::ParameterDeclaration(data)) =
            self.arena.get(parameter).map(|node| &node.data)
        {
            let name = data.name;
            let type_ = data.type_;
            let initializer = data.initializer;
            let property_name = data
                .modifiers
                .as_ref()
                .filter(|modifiers| {
                    modifiers.list.nodes.iter().any(|modifier| {
                        self.arena.get(*modifier).is_some_and(|modifier| {
                            matches!(
                                modifier.kind,
                                SyntaxKind::OverrideKeyword
                                    | SyntaxKind::PrivateKeyword
                                    | SyntaxKind::ProtectedKeyword
                                    | SyntaxKind::PublicKeyword
                                    | SyntaxKind::ReadonlyKeyword
                            )
                        })
                    })
                })
                .and_then(|_| self.identifier_text(name).map(str::to_owned));
            self.declare_binding_name(
                scope,
                parameter,
                name,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                parent_symbol,
            );
            if let Some(property_name) = property_name
                && self.is_constructor_like(container)
                && let Some(class_scope) = self.result.scopes[scope.index()].parent
                && self.result.scopes[class_scope.index()].kind == ScopeKind::Class
                && let Some(class_symbol) = parent_symbol
                    .and_then(|symbol| self.result.symbols.get(symbol))
                    .and_then(|symbol| symbol.parent)
            {
                self.declare_name(
                    class_scope,
                    parameter,
                    property_name,
                    SymbolFlags::PROPERTY,
                    Some(class_symbol),
                );
            }
            if let Some(type_) = type_ {
                self.bind_node(type_, scope, container, parent_symbol);
            }
            if let Some(initializer) = initializer {
                self.bind_node(initializer, scope, container, parent_symbol);
            }
        }
    }

    fn is_constructor_like(&self, node: NodeId) -> bool {
        match self.arena.get(node).map(|node| &node.data) {
            Some(NodeData::ConstructorDeclaration(_)) => true,
            Some(NodeData::MethodDeclaration(method)) => {
                self.identifier_text(method.name) == Some("constructor")
            }
            _ => false,
        }
    }

    fn bind_type_parameters(
        &mut self,
        type_parameters: Option<&ts_ast::NodeList>,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        if let Some(type_parameters) = type_parameters {
            for type_parameter in &type_parameters.nodes {
                self.bind_node(*type_parameter, scope, container, parent_symbol);
            }
        }
    }

    fn bind_function_like(
        &mut self,
        node_id: NodeId,
        parent_scope: ScopeId,
        parent_symbol: Option<SymbolId>,
        type_parameters: Option<&ts_ast::NodeList>,
        parameters: &[NodeId],
        body: Option<NodeId>,
    ) {
        let function_scope = self.create_scope(ScopeKind::Function, node_id, Some(parent_scope));
        self.result.node_scopes.insert(node_id, function_scope);
        self.bind_type_parameters(type_parameters, function_scope, node_id, parent_symbol);
        for parameter in parameters {
            self.bind_parameter(*parameter, function_scope, node_id, parent_symbol);
        }
        if let Some(body) = body {
            self.bind_node(body, function_scope, node_id, parent_symbol);
        }
    }

    fn bind_signature_type(
        &mut self,
        node_id: NodeId,
        parent_scope: ScopeId,
        parent_symbol: Option<SymbolId>,
        type_parameters: Option<&ts_ast::NodeList>,
        parameters: &[NodeId],
        return_type: Option<NodeId>,
    ) {
        self.bind_function_like(
            node_id,
            parent_scope,
            parent_symbol,
            type_parameters,
            parameters,
            None,
        );
        if let Some(return_type) = return_type {
            let function_scope = self.result.node_scopes[&node_id];
            self.bind_node(return_type, function_scope, node_id, parent_symbol);
        }
    }

    fn bind_import_clause(
        &mut self,
        clause: NodeId,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        self.result.containers.insert(clause, container);
        let Some(NodeData::ImportClause(data)) = self.arena.get(clause).map(|node| &node.data)
        else {
            return;
        };
        if let Some(name) = data.name {
            self.declare_named(scope, clause, name, SymbolFlags::ALIAS, parent_symbol);
        }
        let Some(bindings) = data.named_bindings else {
            return;
        };
        self.result.containers.insert(bindings, container);
        match self.arena.get(bindings).map(|node| &node.data) {
            Some(NodeData::NamedImports(imports)) => {
                let elements = imports.elements.nodes.clone();
                for specifier in elements {
                    self.result.containers.insert(specifier, container);
                    if let Some(NodeData::ImportSpecifier(specifier_data)) =
                        self.arena.get(specifier).map(|node| &node.data)
                    {
                        if let Some(property_name) = specifier_data.property_name {
                            self.result.containers.insert(property_name, container);
                        }
                        self.declare_named(
                            scope,
                            specifier,
                            specifier_data.name,
                            SymbolFlags::ALIAS,
                            parent_symbol,
                        );
                    }
                }
            }
            Some(NodeData::NamespaceImport(import)) => {
                self.declare_named(
                    scope,
                    bindings,
                    import.name,
                    SymbolFlags::ALIAS,
                    parent_symbol,
                );
            }
            _ => {}
        }
    }

    fn bind_export_clause(
        &mut self,
        clause: NodeId,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        self.result.containers.insert(clause, container);
        let Some(NodeData::NamedExports(exports)) = self.arena.get(clause).map(|node| &node.data)
        else {
            return;
        };
        let elements = exports.elements.nodes.clone();
        for specifier in elements {
            self.result.containers.insert(specifier, container);
            let Some(NodeData::ExportSpecifier(data)) =
                self.arena.get(specifier).map(|node| &node.data)
            else {
                continue;
            };
            let Some(name) = self.declaration_name_text(data.name) else {
                continue;
            };
            let local_name_node = data.property_name.unwrap_or(data.name);
            let target = self
                .identifier_text(local_name_node)
                .and_then(|name| self.lookup_symbol(scope, name));
            self.result.containers.insert(local_name_node, container);
            if let Some(target) = target {
                self.result.node_symbols.insert(local_name_node, target);
            }
            let alias = self.declare_export_alias(specifier, &name, target, parent_symbol);
            self.result.node_symbols.insert(data.name, alias);
            self.result.node_symbols.insert(specifier, alias);
        }
    }

    fn declare_binding_name(
        &mut self,
        scope: ScopeId,
        declaration: NodeId,
        name: NodeId,
        flags: SymbolFlags,
        parent_symbol: Option<SymbolId>,
    ) {
        let Some(node) = self.arena.get(name) else {
            return;
        };
        match &node.data {
            NodeData::Identifier(_) => {
                self.declare_named(scope, declaration, name, flags, parent_symbol);
            }
            NodeData::BindingPattern(pattern) => {
                for element in &pattern.elements.nodes {
                    if let Some(NodeData::BindingElement(element_data)) =
                        self.arena.get(*element).map(|node| &node.data)
                        && let Some(element_name) = element_data.name
                    {
                        self.declare_binding_name(
                            scope,
                            declaration,
                            element_name,
                            flags,
                            parent_symbol,
                        );
                    }
                }
            }
            _ => {}
        }
    }

    fn declare_named(
        &mut self,
        scope: ScopeId,
        declaration: NodeId,
        name_node: NodeId,
        flags: SymbolFlags,
        parent_symbol: Option<SymbolId>,
    ) -> Option<SymbolId> {
        let computed_expression = match self.arena.get(name_node).map(|node| &node.data) {
            Some(NodeData::ComputedPropertyName(computed)) => Some(computed.expression),
            _ => None,
        };
        if let Some(expression) = computed_expression {
            let expression_scope = self
                .result
                .scope(scope)
                .and_then(|scope| {
                    matches!(
                        scope.kind,
                        ScopeKind::Class
                            | ScopeKind::Interface
                            | ScopeKind::Enum
                            | ScopeKind::TypeAlias
                    )
                    .then_some(scope.parent)
                    .flatten()
                })
                .unwrap_or(scope);
            let expression_container = self
                .result
                .scope(expression_scope)
                .map_or(declaration, |scope| scope.owner);
            let expression_parent_symbol = self
                .result
                .node_symbols
                .get(&expression_container)
                .copied();
            self.bind_node(
                expression,
                expression_scope,
                expression_container,
                expression_parent_symbol,
            );
        }
        let name = self.declaration_name_text(name_node)?;
        let id = self.declare_name(scope, declaration, name, flags, parent_symbol)?;
        self.result.node_symbols.insert(declaration, id);
        self.result.node_symbols.insert(name_node, id);
        if let Some(container) = self.result.containers.get(&declaration).copied() {
            self.result.containers.insert(name_node, container);
        }
        Some(id)
    }

    fn declare_and_export(
        &mut self,
        scope: ScopeId,
        declaration: NodeId,
        name_node: NodeId,
        flags: SymbolFlags,
        parent_symbol: Option<SymbolId>,
    ) -> Option<SymbolId> {
        let id = self.declare_named(scope, declaration, name_node, flags, parent_symbol)?;
        if self.should_export(declaration, parent_symbol) {
            let export_name = if self.has_modifier(declaration, SyntaxKind::DefaultKeyword) {
                "default".to_owned()
            } else {
                self.identifier_text(name_node)?.to_owned()
            };
            if let Some(parent) = parent_symbol {
                self.result
                    .symbols
                    .get_mut(parent)?
                    .members
                    .insert(export_name, id);
            } else {
                self.result.exports.insert(export_name, id);
            }
        }
        Some(id)
    }

    fn declare_synthetic(
        &mut self,
        scope: ScopeId,
        declaration: NodeId,
        name: &str,
        flags: SymbolFlags,
        parent_symbol: Option<SymbolId>,
    ) -> SymbolId {
        let id = self
            .declare_name(scope, declaration, name.to_owned(), flags, parent_symbol)
            .expect("scope and symbol IDs originate from this binder");
        self.result.node_symbols.insert(declaration, id);
        id
    }

    fn declare_name(
        &mut self,
        scope: ScopeId,
        declaration: NodeId,
        name: String,
        flags: SymbolFlags,
        parent_symbol: Option<SymbolId>,
    ) -> Option<SymbolId> {
        let existing = self.result.scopes[scope.index()].symbols.get(&name);
        let id = if let Some(existing) = existing {
            let existing_flags = self.result.symbols.get(existing)?.flags;
            if !can_merge(existing_flags, flags) {
                if existing_flags.intersects(SymbolFlags::ENUM)
                    || flags.intersects(SymbolFlags::ENUM)
                {
                    let prior_declarations =
                        self.result.symbols.get(existing)?.declarations.clone();
                    for prior in prior_declarations {
                        self.report_enum_merge_error(prior);
                    }
                    self.report_enum_merge_error(declaration);
                } else {
                    let code = if existing_flags.intersects(SymbolFlags::BLOCK_SCOPED_VARIABLE)
                        || flags.intersects(SymbolFlags::BLOCK_SCOPED_VARIABLE)
                    {
                        2451
                    } else {
                        2300
                    };
                    let message = message_by_code(code).expect("binder diagnostic is in catalog");
                    self.result.diagnostics.push(BindDiagnostic {
                        node: declaration,
                        diagnostic: Diagnostic::with_arguments(message, [name.clone()]),
                    });
                }
            }
            let symbol = self.result.symbols.get_mut(existing)?;
            symbol.flags |= flags;
            symbol.declarations.push(declaration);
            if symbol.value_declaration.is_none() && is_value(flags) {
                symbol.value_declaration = Some(declaration);
            }
            existing
        } else {
            let id = self
                .result
                .symbols
                .alloc(name.clone(), flags, declaration, parent_symbol);
            self.result.scopes[scope.index()]
                .symbols
                .insert(name.clone(), id);
            if matches!(
                self.result.scopes[scope.index()].kind,
                ScopeKind::Class | ScopeKind::Interface | ScopeKind::Enum
            ) && let Some(parent) = parent_symbol
                && let Some(parent) = self.result.symbols.get_mut(parent)
            {
                parent.members.insert(name, id);
            }
            id
        };
        Some(id)
    }

    fn report_enum_merge_error(&mut self, declaration: NodeId) {
        if self.result.diagnostics.iter().any(|diagnostic| {
            diagnostic.node == declaration && diagnostic.diagnostic.code() == 2567
        }) {
            return;
        }
        let message = message_by_code(2567).expect("binder diagnostic is in catalog");
        self.result.diagnostics.push(BindDiagnostic {
            node: declaration,
            diagnostic: Diagnostic::new(message),
        });
    }

    fn declare_export_alias(
        &mut self,
        declaration: NodeId,
        name: &str,
        target: Option<SymbolId>,
        parent_symbol: Option<SymbolId>,
    ) -> SymbolId {
        let id = self.result.symbols.alloc(
            name.to_owned(),
            SymbolFlags::ALIAS,
            declaration,
            parent_symbol,
        );
        self.result.symbols.get_mut(id).unwrap().target = target;
        if let Some(parent) = parent_symbol {
            self.result
                .symbols
                .get_mut(parent)
                .unwrap()
                .members
                .insert(name.to_owned(), id);
        } else {
            self.result.exports.insert(name.to_owned(), id);
        }
        id
    }

    fn lookup_symbol(&self, mut scope: ScopeId, name: &str) -> Option<SymbolId> {
        loop {
            let current = self.result.scope(scope)?;
            if let Some(symbol) = current.symbols.get(name) {
                return Some(symbol);
            }
            scope = current.parent?;
        }
    }

    fn has_modifier(&self, declaration: NodeId, modifier: SyntaxKind) -> bool {
        let modifiers = match &self.arena.get(declaration).map(|node| &node.data) {
            Some(NodeData::FunctionDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::ClassDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::InterfaceDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::TypeAliasDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::EnumDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::ImportDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::ImportEqualsDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::ModuleDeclaration(data)) => data.modifiers.as_ref(),
            Some(NodeData::VariableStatement(data)) => data.modifiers.as_ref(),
            _ => None,
        };
        modifiers.is_some_and(|modifiers| {
            modifiers.list.nodes.iter().any(|node| {
                self.arena
                    .get(*node)
                    .is_some_and(|node| node.kind == modifier)
            })
        })
    }

    fn should_export(&self, declaration: NodeId, parent_symbol: Option<SymbolId>) -> bool {
        self.has_modifier(declaration, SyntaxKind::ExportKeyword)
            || (parent_symbol.is_some()
                && self.implicit_export_depth > 0
                && self
                    .result
                    .containers
                    .get(&declaration)
                    .and_then(|container| self.arena.get(*container))
                    .is_some_and(|container| {
                        matches!(
                            container.data,
                            NodeData::ModuleBlock(_) | NodeData::ModuleDeclaration(_)
                        )
                    }))
    }

    fn bind_children(
        &mut self,
        node_id: NodeId,
        scope: ScopeId,
        container: NodeId,
        parent_symbol: Option<SymbolId>,
    ) {
        let children = self.children.get(&node_id).cloned().unwrap_or_default();
        for child in children {
            self.bind_node(child, scope, container, parent_symbol);
        }
    }

    fn create_scope(&mut self, kind: ScopeKind, owner: NodeId, parent: Option<ScopeId>) -> ScopeId {
        let id = ScopeId(
            u32::try_from(self.result.scopes.len()).expect("scope arena exceeds u32::MAX scopes"),
        );
        self.result.scopes.push(Scope {
            id,
            kind,
            owner,
            parent,
            symbols: SymbolTable::default(),
        });
        id
    }

    fn nearest_var_scope(&self, mut scope: ScopeId) -> ScopeId {
        loop {
            let current = &self.result.scopes[scope.index()];
            if matches!(
                current.kind,
                ScopeKind::SourceFile | ScopeKind::Function | ScopeKind::Module
            ) {
                return scope;
            }
            scope = current.parent.unwrap_or(scope);
        }
    }

    fn identifier_text(&self, node: NodeId) -> Option<&str> {
        match &self.arena.get(node)?.data {
            NodeData::Identifier(identifier) => Some(&identifier.text),
            _ => None,
        }
    }

    fn declaration_name_text(&self, node: NodeId) -> Option<String> {
        match &self.arena.get(node)?.data {
            NodeData::Identifier(identifier) => Some(identifier.text.clone()),
            NodeData::PrivateIdentifier(identifier) => Some(identifier.text.clone()),
            NodeData::StringLiteral(literal) => Some(literal.text.clone()),
            NodeData::NumericLiteral(literal) => Some(literal.text.clone()),
            NodeData::NoSubstitutionTemplateLiteral(literal) => Some(literal.text.clone()),
            NodeData::ComputedPropertyName(computed) => {
                self.computed_property_name_text(computed.expression)
            }
            _ => None,
        }
    }

    fn computed_property_name_text(&self, node: NodeId) -> Option<String> {
        match &self.arena.get(node)?.data {
            NodeData::StringLiteral(literal) => Some(literal.text.clone()),
            NodeData::NumericLiteral(literal) => Some(literal.text.clone()),
            NodeData::NoSubstitutionTemplateLiteral(literal) => Some(literal.text.clone()),
            NodeData::ParenthesizedExpression(parenthesized) => {
                self.computed_property_name_text(parenthesized.expression)
            }
            _ => None,
        }
    }
}

fn can_merge(existing: SymbolFlags, new: SymbolFlags) -> bool {
    let existing_has_alias = existing.contains(SymbolFlags::ALIAS);
    let new_has_alias = new.contains(SymbolFlags::ALIAS);
    if new_has_alias {
        return !existing_has_alias;
    }
    if existing_has_alias {
        let existing_without_alias = SymbolFlags(existing.0 & !SymbolFlags::ALIAS.0);
        return existing_without_alias == SymbolFlags::NONE
            || can_merge(existing_without_alias, new);
    }
    (existing.contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
        && new == SymbolFlags::FUNCTION_SCOPED_VARIABLE)
        || (existing.contains(SymbolFlags::FUNCTION) && new == SymbolFlags::FUNCTION)
        || (existing.contains(SymbolFlags::METHOD) && new == SymbolFlags::METHOD)
        || (existing.contains(SymbolFlags::INTERFACE) && new == SymbolFlags::INTERFACE)
        || (existing.intersects(SymbolFlags::INTERFACE | SymbolFlags::TYPE_ALIAS)
            && new.intersects(SymbolFlags::VARIABLE))
        || (new.intersects(SymbolFlags::INTERFACE | SymbolFlags::TYPE_ALIAS)
            && existing.intersects(SymbolFlags::VARIABLE))
        || (existing.contains(SymbolFlags::CONST_ENUM) && new == SymbolFlags::CONST_ENUM)
        || (existing.contains(SymbolFlags::REGULAR_ENUM) && new == SymbolFlags::REGULAR_ENUM)
        || (existing.contains(SymbolFlags::NAMESPACE_MODULE)
            && new == SymbolFlags::NAMESPACE_MODULE)
        || (new == SymbolFlags::NAMESPACE_MODULE
            && existing.intersects(
                SymbolFlags::FUNCTION
                    | SymbolFlags::CLASS
                    | SymbolFlags::ENUM
                    | SymbolFlags::NAMESPACE_MODULE,
            ))
        || (existing.contains(SymbolFlags::NAMESPACE_MODULE)
            && new.intersects(SymbolFlags::FUNCTION | SymbolFlags::CLASS | SymbolFlags::ENUM))
        || (existing == SymbolFlags::GET_ACCESSOR && new == SymbolFlags::SET_ACCESSOR)
        || (existing == SymbolFlags::SET_ACCESSOR && new == SymbolFlags::GET_ACCESSOR)
        || (new == SymbolFlags::CLASS
            && existing.contains(SymbolFlags::INTERFACE)
            && !existing.contains(SymbolFlags::CLASS))
        || (new == SymbolFlags::INTERFACE
            && existing.intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE))
}

fn is_value(flags: SymbolFlags) -> bool {
    flags.intersects(
        SymbolFlags::VARIABLE
            | SymbolFlags::PROPERTY
            | SymbolFlags::ENUM_MEMBER
            | SymbolFlags::FUNCTION
            | SymbolFlags::CLASS
            | SymbolFlags::ENUM
            | SymbolFlags::MODULE
            | SymbolFlags::METHOD
            | SymbolFlags::CONSTRUCTOR
            | SymbolFlags::GET_ACCESSOR
            | SymbolFlags::SET_ACCESSOR,
    )
}

#[cfg(test)]
mod tests {
    use ts_ast::{
        BlockData, ClassDeclarationData, EnumDeclarationData, EnumMemberData,
        FunctionDeclarationData, IdentifierData, InterfaceDeclarationData, Node, NodeArena,
        NodeData, NodeFlags, NodeId, NodeList, SourceFileData, SymbolTable as AstSymbolTable,
        SyntaxKind, TokenData, TypeAliasDeclarationData, VariableDeclarationData,
        VariableDeclarationListData, VariableStatementData,
    };
    use ts_core::TextRange;
    use ts_parser::parse_source_file;

    use super::{ScopeKind, SymbolFlags, bind_source_file};

    struct AstBuilder {
        arena: NodeArena,
    }

    impl AstBuilder {
        fn new() -> Self {
            Self {
                arena: NodeArena::new(),
            }
        }

        fn alloc(
            &mut self,
            kind: SyntaxKind,
            flags: NodeFlags,
            data: NodeData,
            children: &[NodeId],
        ) -> NodeId {
            let id = self.arena.alloc(Node {
                kind,
                flags,
                range: TextRange::default(),
                parent: None,
                data,
            });
            for child in children {
                self.arena.get_mut(*child).unwrap().parent = Some(id);
            }
            id
        }

        fn identifier(&mut self, text: &str) -> NodeId {
            self.alloc(
                SyntaxKind::Identifier,
                NodeFlags::default(),
                NodeData::Identifier(Box::new(IdentifierData {
                    flow_node: None,
                    text: text.to_owned(),
                })),
                &[],
            )
        }

        fn variable_statement(&mut self, name: &str, flags: NodeFlags) -> (NodeId, NodeId) {
            let name = self.identifier(name);
            let declaration = self.alloc(
                SyntaxKind::VariableDeclaration,
                NodeFlags::default(),
                NodeData::VariableDeclaration(Box::new(VariableDeclarationData {
                    exclamation_token: None,
                    initializer: None,
                    local_symbol: None,
                    symbol: None,
                    type_: None,
                    facts: 0,
                    name,
                })),
                &[name],
            );
            let list = self.alloc(
                SyntaxKind::VariableDeclarationList,
                flags,
                NodeData::VariableDeclarationList(Box::new(VariableDeclarationListData {
                    declarations: NodeList {
                        range: TextRange::default(),
                        nodes: vec![declaration],
                        has_trailing_comma: false,
                    },
                    facts: 0,
                })),
                &[declaration],
            );
            let statement = self.alloc(
                SyntaxKind::VariableStatement,
                NodeFlags::default(),
                NodeData::VariableStatement(Box::new(VariableStatementData {
                    declaration_list: list,
                    flow_node: None,
                    facts: 0,
                    modifiers: None,
                })),
                &[list],
            );
            (statement, declaration)
        }

        fn block(&mut self, statements: &[NodeId]) -> NodeId {
            self.alloc(
                SyntaxKind::Block,
                NodeFlags::default(),
                NodeData::Block(Box::new(BlockData {
                    flow_node: None,
                    locals: AstSymbolTable,
                    multi_line: false,
                    next_container: None,
                    statements: NodeList {
                        range: TextRange::default(),
                        nodes: statements.to_owned(),
                        has_trailing_comma: false,
                    },
                    facts: 0,
                })),
                statements,
            )
        }

        fn function(&mut self, name: &str, body: NodeId) -> NodeId {
            let name = self.identifier(name);
            self.alloc(
                SyntaxKind::FunctionDeclaration,
                NodeFlags::default(),
                NodeData::FunctionDeclaration(Box::new(FunctionDeclarationData {
                    asterisk_token: None,
                    body: Some(body),
                    end_flow_node: None,
                    flow_node: None,
                    full_signature: None,
                    local_symbol: None,
                    locals: AstSymbolTable,
                    next_container: None,
                    parameters: NodeList::default(),
                    return_flow_node: None,
                    symbol: None,
                    type_: None,
                    type_parameters: None,
                    facts: 0,
                    modifiers: None,
                    name: Some(name),
                })),
                &[name, body],
            )
        }

        fn class(&mut self, name: &str) -> NodeId {
            let name = self.identifier(name);
            self.alloc(
                SyntaxKind::ClassDeclaration,
                NodeFlags::default(),
                NodeData::ClassDeclaration(Box::new(ClassDeclarationData {
                    flow_node: None,
                    heritage_clauses: None,
                    local_symbol: None,
                    locals: AstSymbolTable,
                    members: NodeList::default(),
                    next_container: None,
                    symbol: None,
                    type_parameters: None,
                    facts: 0,
                    modifiers: None,
                    name: Some(name),
                })),
                &[name],
            )
        }

        fn interface(&mut self, name: &str) -> NodeId {
            let name = self.identifier(name);
            self.alloc(
                SyntaxKind::InterfaceDeclaration,
                NodeFlags::default(),
                NodeData::InterfaceDeclaration(Box::new(InterfaceDeclarationData {
                    flow_node: None,
                    heritage_clauses: None,
                    local_symbol: None,
                    members: NodeList::default(),
                    symbol: None,
                    type_parameters: None,
                    modifiers: None,
                    name,
                })),
                &[name],
            )
        }

        fn type_alias(&mut self, name: &str) -> NodeId {
            let name = self.identifier(name);
            let type_node = self.identifier("string");
            self.alloc(
                SyntaxKind::TypeAliasDeclaration,
                NodeFlags::default(),
                NodeData::TypeAliasDeclaration(Box::new(TypeAliasDeclarationData {
                    flow_node: None,
                    local_symbol: None,
                    locals: AstSymbolTable,
                    next_container: None,
                    symbol: None,
                    type_: type_node,
                    type_parameters: None,
                    modifiers: None,
                    name,
                })),
                &[name, type_node],
            )
        }

        fn enum_declaration(&mut self, name: &str, member: &str) -> (NodeId, NodeId) {
            let member_name = self.identifier(member);
            let member = self.alloc(
                SyntaxKind::EnumMember,
                NodeFlags::default(),
                NodeData::EnumMember(Box::new(EnumMemberData {
                    initializer: None,
                    postfix_token: None,
                    symbol: None,
                    facts: 0,
                    modifiers: None,
                    name: member_name,
                })),
                &[member_name],
            );
            let name = self.identifier(name);
            let declaration = self.alloc(
                SyntaxKind::EnumDeclaration,
                NodeFlags::default(),
                NodeData::EnumDeclaration(Box::new(EnumDeclarationData {
                    flow_node: None,
                    local_symbol: None,
                    members: NodeList {
                        range: TextRange::default(),
                        nodes: vec![member],
                        has_trailing_comma: false,
                    },
                    symbol: None,
                    facts: 0,
                    modifiers: None,
                    name,
                })),
                &[name, member],
            );
            (declaration, member)
        }

        fn source_file(&mut self, statements: Vec<NodeId>) -> NodeId {
            let eof = self.alloc(
                SyntaxKind::EndOfFile,
                NodeFlags::default(),
                NodeData::Token(Box::new(TokenData)),
                &[],
            );
            let mut children = statements.clone();
            children.push(eof);
            self.alloc(
                SyntaxKind::SourceFile,
                NodeFlags::default(),
                NodeData::SourceFile(Box::new(SourceFileData {
                    end_of_file_token: eof,
                    locals: AstSymbolTable,
                    next_container: None,
                    statements: NodeList {
                        range: TextRange::default(),
                        nodes: statements,
                        has_trailing_comma: false,
                    },
                    symbol: None,
                    facts: 0,
                })),
                &children,
            )
        }
    }

    #[test]
    fn binds_var_and_block_scoped_declarations_with_stable_ids() {
        let mut builder = AstBuilder::new();
        let (first_var, first_var_decl) = builder.variable_statement("value", NodeFlags::default());
        let (second_var, _) = builder.variable_statement("value", NodeFlags::default());
        let (first_let, first_let_decl) = builder.variable_statement("value", NodeFlags(1));
        let (second_let, second_let_decl) = builder.variable_statement("value", NodeFlags(1));
        let block = builder.block(&[first_let, second_let]);
        let source = builder.source_file(vec![first_var, second_var, block]);

        let result = bind_source_file(&builder.arena, source);
        let root = result.root_scope().unwrap();
        let root_value = root.symbols.get("value").unwrap();
        assert_eq!(root_value.0, 0);
        assert_eq!(
            result.symbols.get(root_value).unwrap().declarations.len(),
            2
        );

        let block_scope = result
            .scopes
            .iter()
            .find(|scope| scope.owner == block)
            .unwrap();
        assert_eq!(block_scope.kind, ScopeKind::Block);
        let block_value = block_scope.symbols.get("value").unwrap();
        assert_eq!(block_value.0, 1);
        assert_eq!(result.symbols.len(), 2);
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(result.diagnostics[0].node, second_let_decl);
        assert_eq!(result.diagnostics[0].diagnostic.code(), 2451);
        assert_eq!(
            result.diagnostics[0].diagnostic.render().unwrap(),
            "Cannot redeclare block-scoped variable 'value'."
        );
        assert_eq!(result.containers[&first_let_decl], block);
        assert_eq!(result.node_symbols[&first_var_decl], root_value);
    }

    #[test]
    fn binds_named_declaration_kinds_and_enum_members() {
        let mut builder = AstBuilder::new();
        let (local_statement, local_declaration) =
            builder.variable_statement("local", NodeFlags::default());
        let function_body = builder.block(&[local_statement]);
        let function = builder.function("run", function_body);
        let class = builder.class("Model");
        let first_interface = builder.interface("Shape");
        let second_interface = builder.interface("Shape");
        let alias = builder.type_alias("Name");
        let (enum_declaration, enum_member) = builder.enum_declaration("Color", "Red");
        let source = builder.source_file(vec![
            function,
            class,
            first_interface,
            second_interface,
            alias,
            enum_declaration,
        ]);

        let result = bind_source_file(&builder.arena, source);
        assert!(result.diagnostics.is_empty());
        let root = result.root_scope().unwrap();
        assert_eq!(root.symbols.len(), 5);
        assert!(
            result
                .symbols
                .get(root.symbols.get("run").unwrap())
                .unwrap()
                .flags
                .contains(SymbolFlags::FUNCTION)
        );
        assert!(
            result
                .symbols
                .get(root.symbols.get("Model").unwrap())
                .unwrap()
                .flags
                .contains(SymbolFlags::CLASS)
        );
        let shape = result
            .symbols
            .get(root.symbols.get("Shape").unwrap())
            .unwrap();
        assert!(shape.flags.contains(SymbolFlags::INTERFACE));
        assert_eq!(shape.declarations.len(), 2);
        assert!(
            result
                .symbols
                .get(root.symbols.get("Name").unwrap())
                .unwrap()
                .flags
                .contains(SymbolFlags::TYPE_ALIAS)
        );

        let color_id = root.symbols.get("Color").unwrap();
        let color = result.symbols.get(color_id).unwrap();
        assert!(color.flags.contains(SymbolFlags::REGULAR_ENUM));
        let red_id = color.members.get("Red").unwrap();
        let red = result.symbols.get(red_id).unwrap();
        assert_eq!(red.parent, Some(color_id));
        assert!(red.flags.contains(SymbolFlags::ENUM_MEMBER));
        assert_eq!(result.node_symbols[&enum_member], red_id);

        let function_scope = result
            .scopes
            .iter()
            .find(|scope| scope.owner == function)
            .unwrap();
        let local_id = function_scope.symbols.get("local").unwrap();
        assert_eq!(result.node_symbols[&local_declaration], local_id);
        assert_eq!(
            result.symbols.get(local_id).unwrap().parent,
            Some(root.symbols.get("run").unwrap())
        );
    }

    #[test]
    fn binds_literal_and_computed_enum_member_names() {
        let parsed = parse_source_file(
            r#"enum Names { Identifier, "quoted", 2, ["computed"] = 3, [4] = 4 }"#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let root = result.root_scope().unwrap();
        let names = result
            .symbols
            .get(root.symbols.get("Names").unwrap())
            .unwrap();
        assert_eq!(
            names
                .members
                .iter()
                .map(|(name, _)| name)
                .collect::<Vec<_>>(),
            ["2", "4", "Identifier", "computed", "quoted"]
        );

        let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data
        else {
            panic!("expected source file");
        };
        let NodeData::EnumDeclaration(enumeration) =
            &parsed.arena.get(source.statements.nodes[0]).unwrap().data
        else {
            panic!("expected enum declaration");
        };
        for member in &enumeration.members.nodes {
            let NodeData::EnumMember(member_data) = &parsed.arena.get(*member).unwrap().data else {
                panic!("expected enum member");
            };
            assert!(result.node_symbols.contains_key(member));
            assert!(result.node_symbols.contains_key(&member_data.name));
            if let NodeData::ComputedPropertyName(computed) =
                &parsed.arena.get(member_data.name).unwrap().data
            {
                assert_eq!(
                    result.containers.get(&computed.expression),
                    Some(&parsed.source_file)
                );
            }
        }
    }

    #[test]
    fn computed_class_names_resolve_in_the_enclosing_scope() {
        let parsed = parse_source_file(
            "const key = Symbol(), value = 12; export class Foo { [key] = value; }",
        );
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        let key_declaration = parsed
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::VariableDeclaration(declaration) = &node.data else {
                    return None;
                };
                matches!(
                    parsed.arena.get(declaration.name).map(|name| &name.data),
                    Some(NodeData::Identifier(name)) if name.text == "key"
                )
                .then_some(declaration.name)
            })
            .unwrap();
        let computed_name = parsed
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::PropertyDeclaration(property) = &node.data else {
                    return None;
                };
                matches!(
                    parsed.arena.get(property.name).map(|name| &name.data),
                    Some(NodeData::ComputedPropertyName(_))
                )
                .then_some(property.name)
            })
            .unwrap();
        let NodeData::ComputedPropertyName(computed) = &parsed.arena.get(computed_name).unwrap().data
        else {
            unreachable!();
        };
        let computed_expression = computed.expression;
        assert_eq!(
            result.root_scope().unwrap().symbols.get("key"),
            result.node_symbols.get(&key_declaration).copied()
        );
        assert_eq!(
            result.containers.get(&computed_expression),
            Some(&parsed.source_file)
        );
        assert_eq!(
            result.node_scopes.get(&parsed.source_file).copied(),
            result.root_scope().map(|scope| scope.id)
        );
        assert_eq!(
            result.resolve_name_at(computed_expression, "key"),
            result.node_symbols.get(&key_declaration).copied()
        );
    }

    #[test]
    fn reports_incompatible_duplicate_declarations() {
        let mut builder = AstBuilder::new();
        let class = builder.class("Conflict");
        let alias = builder.type_alias("Conflict");
        let source = builder.source_file(vec![class, alias]);

        let result = bind_source_file(&builder.arena, source);
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(result.diagnostics[0].node, alias);
        assert_eq!(result.diagnostics[0].diagnostic.code(), 2300);
        assert_eq!(
            result.diagnostics[0].diagnostic.render().unwrap(),
            "Duplicate identifier 'Conflict'."
        );
    }

    #[test]
    fn isolates_type_literal_and_signature_type_scopes() {
        let parsed = parse_source_file(concat!(
            "declare let first: { value: string; call<T>(input: T): T }; ",
            "declare let second: { value: number; call<T>(input: T): T }; ",
            "declare let generic: <T>(input: T) => T; ",
            "declare let other: <T>(input: T) => T;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    }

    #[test]
    fn binds_parsed_import_and_export_aliases() {
        let parsed = parse_source_file(
            r#"
                import DefaultThing, { source as local, same } from "pkg";
                const value = 1;
                export { value as renamed };
                export default function make<T>(input: T): T { return input; }
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let root = result.root_scope().unwrap();
        for name in ["DefaultThing", "local", "same"] {
            let symbol = result.symbols.get(root.symbols.get(name).unwrap()).unwrap();
            assert!(symbol.flags.contains(SymbolFlags::ALIAS));
            assert!(symbol.target.is_none());
        }
        let value = root.symbols.get("value").unwrap();
        let renamed = result
            .symbols
            .get(result.exports.get("renamed").unwrap())
            .unwrap();
        assert!(renamed.flags.contains(SymbolFlags::ALIAS));
        assert_eq!(renamed.target, Some(value));

        let make = root.symbols.get("make").unwrap();
        assert_eq!(result.exports.get("default"), Some(make));
        let function_scope = result
            .scopes
            .iter()
            .find(|scope| scope.kind == ScopeKind::Function && scope.symbols.get("input").is_some())
            .unwrap();
        assert!(
            result
                .symbols
                .get(function_scope.symbols.get("T").unwrap())
                .unwrap()
                .flags
                .contains(SymbolFlags::TYPE_PARAMETER)
        );
    }

    #[test]
    fn merges_import_aliases_with_type_declarations_in_either_order() {
        for source in [
            r#"export default interface Shape {} import Shape from "pkg";"#,
            r#"interface Shape {} import Shape from "pkg";"#,
            r#"import Shape from "pkg"; interface Shape {}"#,
            r#"type Shape = {}; import Shape from "pkg";"#,
            r#"import Shape from "pkg"; type Shape = {};"#,
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let result = bind_source_file(&parsed.arena, parsed.source_file);
            assert!(
                result.diagnostics.is_empty(),
                "{source}: {:?}",
                result.diagnostics
            );
            let root = result.root_scope().unwrap();
            let symbol_id = root.symbols.get("Shape").unwrap();
            let symbol = result.symbols.get(symbol_id).unwrap();
            assert!(symbol.flags.contains(SymbolFlags::ALIAS), "{source}");
            assert!(
                symbol
                    .flags
                    .intersects(SymbolFlags::INTERFACE | SymbolFlags::TYPE_ALIAS),
                "{source}"
            );
            assert_eq!(symbol.declarations.len(), 2, "{source}");
            if source.starts_with("export default") {
                assert_eq!(result.exports.get("default"), Some(symbol_id));
            }
        }
    }

    #[test]
    fn does_not_merge_two_import_aliases() {
        let parsed = parse_source_file(r#"import Shape from "first"; import Shape from "second";"#);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(result.diagnostics[0].diagnostic.code(), 2300);
    }

    #[test]
    fn binds_parsed_modules_and_class_interface_members() {
        let parsed = parse_source_file(
            r"
                namespace Outer {
                    export function run() {}
                    function hidden() {}
                }
                namespace Outer { export function second() {} }
                class Model<T> {
                    value: T;
                    read(input: T): T { return input; }
                }
                interface Shape {
                    width: number;
                }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let root = result.root_scope().unwrap();
        let outer_id = root.symbols.get("Outer").unwrap();
        let outer = result.symbols.get(outer_id).unwrap();
        assert!(outer.flags.contains(SymbolFlags::NAMESPACE_MODULE));
        assert_eq!(outer.declarations.len(), 2);
        assert!(outer.members.get("run").is_some());
        assert!(outer.members.get("second").is_some());
        assert!(outer.members.get("hidden").is_none());

        let model = result
            .symbols
            .get(root.symbols.get("Model").unwrap())
            .unwrap();
        assert!(
            result
                .symbols
                .get(model.members.get("value").unwrap())
                .unwrap()
                .flags
                .contains(SymbolFlags::PROPERTY)
        );
        let method_id = model.members.get("read").unwrap();
        assert!(
            result
                .symbols
                .get(method_id)
                .unwrap()
                .flags
                .contains(SymbolFlags::METHOD)
        );
        let method_scope = result
            .scopes
            .iter()
            .find(|scope| scope.kind == ScopeKind::Function && scope.symbols.get("input").is_some())
            .unwrap();
        assert_eq!(
            result
                .symbols
                .get(method_scope.symbols.get("input").unwrap())
                .unwrap()
                .parent,
            Some(method_id)
        );

        let shape = result
            .symbols
            .get(root.symbols.get("Shape").unwrap())
            .unwrap();
        assert!(shape.members.get("width").is_some());
        assert!(
            result
                .scopes
                .iter()
                .any(|scope| scope.kind == ScopeKind::Module)
        );
    }

    #[test]
    fn keeps_function_scoped_variables_inside_namespace_scopes() {
        let parsed = parse_source_file(
            r"
                namespace m1 {
                    export var m1 = 10;
                    var local = m1;
                }
                var value = m1.m1;
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let root = result.root_scope().unwrap();
        let namespace_id = root.symbols.get("m1").unwrap();
        let namespace = result.symbols.get(namespace_id).unwrap();
        let exported_id = namespace.members.get("m1").unwrap();
        assert_ne!(namespace_id, exported_id);

        let module_scope = result
            .scopes
            .iter()
            .find(|scope| scope.kind == ScopeKind::Module)
            .unwrap();
        assert_eq!(module_scope.symbols.get("m1"), Some(exported_id));
        assert!(module_scope.symbols.get("local").is_some());
        assert!(root.symbols.get("local").is_none());
    }

    #[test]
    fn binds_namespace_exports_and_ambient_export_contexts() {
        let parsed = parse_source_file(
            r"
                namespace Ordinary {
                    const hidden = 0;
                    function hiddenFunction() {}
                    export const visible = 1;
                    export function visibleFunction() {}
                }
                declare namespace Ambient {
                    namespace Nested {
                        function func(): number;
                        const value: string;
                    }
                }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let root = result.root_scope().unwrap();

        let ordinary = result
            .symbols
            .get(root.symbols.get("Ordinary").unwrap())
            .unwrap();
        assert!(ordinary.members.get("visible").is_some());
        assert!(ordinary.members.get("visibleFunction").is_some());
        assert!(ordinary.members.get("hidden").is_none());
        assert!(ordinary.members.get("hiddenFunction").is_none());

        let ambient = result
            .symbols
            .get(root.symbols.get("Ambient").unwrap())
            .unwrap();
        let nested = result
            .symbols
            .get(ambient.members.get("Nested").unwrap())
            .unwrap();
        assert!(nested.members.get("func").is_some());
        assert!(nested.members.get("value").is_some());
    }

    #[test]
    fn binds_dotted_ambient_namespaces_as_nested_exports() {
        let parsed =
            parse_source_file("declare namespace Foo.Bar { export var foo; }; Foo.Bar.foo = 5;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let root = result.root_scope().unwrap();

        let foo_id = root.symbols.get("Foo").unwrap();
        let foo = result.symbols.get(foo_id).unwrap();
        assert!(foo.flags.contains(SymbolFlags::NAMESPACE_MODULE));
        let bar_id = foo.members.get("Bar").unwrap();
        let bar = result.symbols.get(bar_id).unwrap();
        assert!(bar.flags.contains(SymbolFlags::NAMESPACE_MODULE));
        assert_eq!(bar.parent, Some(foo_id));
        let value_id = bar.members.get("foo").unwrap();
        let value = result.symbols.get(value_id).unwrap();
        assert_eq!(value.parent, Some(bar_id));

        let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data
        else {
            panic!("expected source file");
        };
        assert_eq!(source.statements.nodes.len(), 3);
        let outer_id = source.statements.nodes[0];
        let NodeData::ModuleDeclaration(outer) = &parsed.arena.get(outer_id).unwrap().data else {
            panic!("expected outer namespace");
        };
        let inner_id = outer.body.unwrap();
        assert_eq!(result.node_symbols.get(&outer_id), Some(&foo_id));
        assert_eq!(result.node_symbols.get(&inner_id), Some(&bar_id));
    }

    #[test]
    fn merges_functions_classes_and_enums_with_namespaces() {
        let parsed = parse_source_file(
            r#"
                function Factory() {}
                namespace Factory { export const version = 1; }
                class Model {}
                namespace Model { export const kind = "model"; }
                enum Color { Red }
                namespace Color { export const label = "red"; }
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let root = result.root_scope().unwrap();
        for (name, declaration_flag, member) in [
            ("Factory", SymbolFlags::FUNCTION, "version"),
            ("Model", SymbolFlags::CLASS, "kind"),
            ("Color", SymbolFlags::REGULAR_ENUM, "label"),
        ] {
            let symbol = result.symbols.get(root.symbols.get(name).unwrap()).unwrap();
            assert!(symbol.flags.contains(declaration_flag));
            assert!(symbol.flags.contains(SymbolFlags::NAMESPACE_MODULE));
            assert!(symbol.members.get(member).is_some());
        }
    }

    #[test]
    fn binds_and_merges_const_enums_with_namespaces() {
        let parsed = parse_source_file(
            r"
                export declare const enum Status { Ready }
                export declare const enum Status { Done }
                export declare namespace Status { const label: string; }
                enum Ordinary { Value }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let root = result.root_scope().unwrap();

        let status = result
            .symbols
            .get(root.symbols.get("Status").unwrap())
            .unwrap();
        assert!(status.flags.contains(SymbolFlags::CONST_ENUM));
        assert!(!status.flags.contains(SymbolFlags::REGULAR_ENUM));
        assert!(status.flags.contains(SymbolFlags::NAMESPACE_MODULE));
        assert_eq!(status.declarations.len(), 3);
        assert!(status.members.get("label").is_some());

        let ordinary = result
            .symbols
            .get(root.symbols.get("Ordinary").unwrap())
            .unwrap();
        assert!(ordinary.flags.contains(SymbolFlags::REGULAR_ENUM));
        assert!(!ordinary.flags.contains(SymbolFlags::CONST_ENUM));
    }

    #[test]
    fn exports_import_equals_and_resolves_qualified_references() {
        let parsed = parse_source_file(
            r#"
                import { alias } from "foo";
                export import cls2 = alias.Class;
                namespace M {
                    export import cls = alias.Class;
                    let value = cls;
                }
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let root = result.root_scope().unwrap();
        let alias = root.symbols.get("alias").unwrap();
        let cls2 = root.symbols.get("cls2").unwrap();
        assert_eq!(result.exports.get("cls2"), Some(cls2));

        let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data
        else {
            panic!("expected source file");
        };
        let NodeData::ImportEqualsDeclaration(top_alias) =
            &parsed.arena.get(source.statements.nodes[1]).unwrap().data
        else {
            panic!("expected top-level import-equals declaration");
        };
        let NodeData::QualifiedName(top_reference) =
            &parsed.arena.get(top_alias.module_reference).unwrap().data
        else {
            panic!("expected qualified module reference");
        };
        assert_eq!(
            result.resolve_name_at(top_reference.left, "alias"),
            Some(alias)
        );

        let NodeData::ModuleDeclaration(module) =
            &parsed.arena.get(source.statements.nodes[2]).unwrap().data
        else {
            panic!("expected namespace");
        };
        let module_symbol = result.symbols.get(root.symbols.get("M").unwrap()).unwrap();
        let namespace_alias = module_symbol.members.get("cls").unwrap();
        let NodeData::ModuleBlock(block) = &parsed.arena.get(module.body.unwrap()).unwrap().data
        else {
            panic!("expected namespace block");
        };
        let NodeData::ImportEqualsDeclaration(nested_alias) =
            &parsed.arena.get(block.statements.nodes[0]).unwrap().data
        else {
            panic!("expected namespace import-equals declaration");
        };
        let NodeData::QualifiedName(nested_reference) = &parsed
            .arena
            .get(nested_alias.module_reference)
            .unwrap()
            .data
        else {
            panic!("expected qualified namespace module reference");
        };
        assert_eq!(
            result.resolve_name_at(nested_reference.left, "alias"),
            Some(alias)
        );
        let NodeData::VariableStatement(statement) =
            &parsed.arena.get(block.statements.nodes[1]).unwrap().data
        else {
            panic!("expected namespace variable");
        };
        let NodeData::VariableDeclarationList(list) =
            &parsed.arena.get(statement.declaration_list).unwrap().data
        else {
            panic!("expected declaration list");
        };
        let NodeData::VariableDeclaration(variable) =
            &parsed.arena.get(list.declarations.nodes[0]).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let initializer = variable.initializer.unwrap();
        assert_eq!(
            result.resolve_name_at(initializer, "cls"),
            Some(namespace_alias)
        );
    }

    #[test]
    fn binds_named_class_expression_in_its_own_scope() {
        let parsed =
            parse_source_file("const value = class Inner { static self = Inner; }; Inner;");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert_eq!(result.root_scope().unwrap().symbols.get("Inner"), None);

        let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data
        else {
            panic!("expected source file");
        };
        let NodeData::VariableStatement(statement) =
            &parsed.arena.get(source.statements.nodes[0]).unwrap().data
        else {
            panic!("expected variable statement");
        };
        let NodeData::VariableDeclarationList(list) =
            &parsed.arena.get(statement.declaration_list).unwrap().data
        else {
            panic!("expected declaration list");
        };
        let NodeData::VariableDeclaration(variable) =
            &parsed.arena.get(list.declarations.nodes[0]).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let class_id = variable.initializer.unwrap();
        let NodeData::ClassExpression(class) = &parsed.arena.get(class_id).unwrap().data else {
            panic!("expected class expression");
        };
        let class_symbol = result.node_symbols[&class_id];
        assert_eq!(
            result.node_symbols.get(&class.name.unwrap()),
            Some(&class_symbol)
        );
        let NodeData::PropertyDeclaration(property) =
            &parsed.arena.get(class.members.nodes[0]).unwrap().data
        else {
            panic!("expected property declaration");
        };
        let self_reference = property.initializer.unwrap();
        assert_eq!(
            result.resolve_name_at(self_reference, "Inner"),
            Some(class_symbol)
        );
        let outside_reference = source.statements.nodes[1];
        let NodeData::ExpressionStatement(outside) =
            &parsed.arena.get(outside_reference).unwrap().data
        else {
            panic!("expected expression statement");
        };
        assert_eq!(result.resolve_name_at(outside.expression, "Inner"), None);
    }

    #[test]
    fn rejects_mixed_regular_and_const_enum_merges() {
        let parsed = parse_source_file("enum Mixed { A } const enum Mixed { B }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert_eq!(result.diagnostics.len(), 2);
        assert!(
            result
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.diagnostic.code() == 2567)
        );
        assert_eq!(
            result.diagnostics[0].diagnostic.render().unwrap(),
            "Enum declarations can only merge with namespace or other enum declarations."
        );
    }

    #[test]
    fn reports_enum_merge_diagnostics_for_each_incompatible_declaration() {
        let parsed = parse_source_file(
            r"
                const enum ConstFirst { A }
                class ConstFirst {}
                class ClassFirst {}
                const enum ClassFirst { A }
                const enum MixedFirst { A }
                enum MixedFirst { B }
                enum RegularFirst { A }
                const enum RegularFirst { B }
                declare const enum Legal { A }
                declare const enum Legal { B }
                declare namespace Legal { const label: string; }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert_eq!(result.diagnostics.len(), 8, "{:?}", result.diagnostics);
        assert!(
            result
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.diagnostic.code() == 2567)
        );
        let root = result.root_scope().unwrap();
        let legal = result
            .symbols
            .get(root.symbols.get("Legal").unwrap())
            .unwrap();
        assert!(legal.flags.contains(SymbolFlags::CONST_ENUM));
        assert!(legal.flags.contains(SymbolFlags::NAMESPACE_MODULE));
        assert_eq!(legal.declarations.len(), 3);
    }

    #[test]
    fn binds_modified_arrow_parameters_and_constructor_parameter_properties() {
        let parsed = parse_source_file(
            r"
                var v = (public x: string) => x;
                class C { constructor(public readonly value: string) { value; } }
                class any {}
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);

        let root = result.root_scope().unwrap();
        assert!(root.symbols.get("v").is_some());
        assert!(root.symbols.get("any").is_some());
        let class = result.symbols.get(root.symbols.get("C").unwrap()).unwrap();
        assert!(
            result
                .symbols
                .get(class.members.get("value").unwrap())
                .unwrap()
                .flags
                .contains(SymbolFlags::PROPERTY)
        );
        for parameter in ["x", "value"] {
            assert!(result.scopes.iter().any(|scope| {
                scope.kind == ScopeKind::Function && scope.symbols.get(parameter).is_some()
            }));
        }
    }
}
