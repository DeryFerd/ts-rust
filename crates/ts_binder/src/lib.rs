//! Declaration binding and lexical symbol tables.

use std::{
    collections::{BTreeMap, HashMap},
    ops::{BitOr, BitOrAssign},
};

use ts_ast::{NodeArena, NodeData, NodeFlags, NodeId, SymbolId};
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
    pub const TYPE_PARAMETER: Self = Self(1 << 18);
    pub const TYPE_ALIAS: Self = Self(1 << 19);

    pub const VARIABLE: Self =
        Self(Self::FUNCTION_SCOPED_VARIABLE.0 | Self::BLOCK_SCOPED_VARIABLE.0);
    pub const ENUM: Self = Self(Self::CONST_ENUM.0 | Self::REGULAR_ENUM.0);

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
    pub symbols: SymbolArena,
    pub scopes: Vec<Scope>,
    pub node_symbols: BTreeMap<NodeId, SymbolId>,
    pub node_scopes: BTreeMap<NodeId, ScopeId>,
    pub containers: BTreeMap<NodeId, NodeId>,
    pub diagnostics: Vec<BindDiagnostic>,
}

impl BindResult {
    #[must_use]
    pub fn root_scope(&self) -> Option<&Scope> {
        self.scopes.first()
    }

    #[must_use]
    pub fn scope(&self, id: ScopeId) -> Option<&Scope> {
        self.scopes.get(id.index())
    }
}

/// Binds declarations reachable from one source-file node.
#[must_use]
pub fn bind_source_file(arena: &NodeArena, source_file: NodeId) -> BindResult {
    Binder::new(arena).bind(source_file)
}

struct Binder<'a> {
    arena: &'a NodeArena,
    result: BindResult,
    children: HashMap<NodeId, Vec<NodeId>>,
}

impl<'a> Binder<'a> {
    fn new(arena: &'a NodeArena) -> Self {
        let mut children = HashMap::<NodeId, Vec<NodeId>>::new();
        for (id, node) in arena.iter() {
            if let Some(parent) = node.parent {
                children.entry(parent).or_default().push(id);
            }
        }
        Self {
            arena,
            result: BindResult::default(),
            children,
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
            NodeData::ModuleBlock(data) => {
                let block_scope = self.create_scope(ScopeKind::Block, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, block_scope);
                for statement in &data.statements.nodes {
                    self.bind_node(*statement, block_scope, node_id, parent_symbol);
                }
            }
            NodeData::FunctionDeclaration(data) => {
                let symbol = data.name.and_then(|name| {
                    self.declare_named(scope, node_id, name, SymbolFlags::FUNCTION, parent_symbol)
                });
                let function_scope = self.create_scope(ScopeKind::Function, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, function_scope);
                for parameter in &data.parameters.nodes {
                    self.bind_parameter(*parameter, function_scope, node_id, symbol);
                }
                if let Some(body) = data.body {
                    self.bind_node(body, function_scope, node_id, symbol);
                }
            }
            NodeData::ClassDeclaration(data) => {
                let symbol = data.name.and_then(|name| {
                    self.declare_named(scope, node_id, name, SymbolFlags::CLASS, parent_symbol)
                });
                let class_scope = self.create_scope(ScopeKind::Class, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, class_scope);
                self.bind_children(node_id, class_scope, node_id, symbol);
            }
            NodeData::InterfaceDeclaration(data) => {
                let symbol = self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::INTERFACE,
                    parent_symbol,
                );
                let interface_scope = self.create_scope(ScopeKind::Interface, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, interface_scope);
                self.bind_children(node_id, interface_scope, node_id, symbol);
            }
            NodeData::TypeAliasDeclaration(data) => {
                self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::TYPE_ALIAS,
                    parent_symbol,
                );
            }
            NodeData::EnumDeclaration(data) => {
                let symbol = self.declare_named(
                    scope,
                    node_id,
                    data.name,
                    SymbolFlags::REGULAR_ENUM,
                    parent_symbol,
                );
                let enum_scope = self.create_scope(ScopeKind::Enum, node_id, Some(scope));
                self.result.node_scopes.insert(node_id, enum_scope);
                for member in &data.members.nodes {
                    self.bind_node(*member, enum_scope, node_id, symbol);
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
            _ => self.bind_children(node_id, scope, container, parent_symbol),
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
                self.declare_binding_name(
                    target_scope,
                    *declaration,
                    declaration_data.name,
                    flags,
                    parent_symbol,
                );
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
            self.declare_binding_name(
                scope,
                parameter,
                data.name,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                parent_symbol,
            );
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
        let name = self.identifier_text(name_node)?.to_owned();
        let existing = self.result.scopes[scope.index()].symbols.get(&name);
        let id = if let Some(existing) = existing {
            let existing_flags = self.result.symbols.get(existing)?.flags;
            if !can_merge(existing_flags, flags) {
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
        self.result.node_symbols.insert(declaration, id);
        self.result.node_symbols.insert(name_node, id);
        Some(id)
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
            if matches!(current.kind, ScopeKind::SourceFile | ScopeKind::Function) {
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
}

fn can_merge(existing: SymbolFlags, new: SymbolFlags) -> bool {
    (existing == SymbolFlags::FUNCTION_SCOPED_VARIABLE
        && new == SymbolFlags::FUNCTION_SCOPED_VARIABLE)
        || (existing == SymbolFlags::FUNCTION && new == SymbolFlags::FUNCTION)
        || (existing == SymbolFlags::INTERFACE && new == SymbolFlags::INTERFACE)
        || (existing == SymbolFlags::REGULAR_ENUM && new == SymbolFlags::REGULAR_ENUM)
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
            | SymbolFlags::ENUM,
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
}
