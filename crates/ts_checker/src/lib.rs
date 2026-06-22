//! Initial semantic type checking over the arena-backed TypeScript AST.

use std::collections::{BTreeMap, HashMap};

use ts_ast::{NodeArena, NodeData, NodeId, SymbolId, SyntaxKind};
use ts_binder::BindResult;
use ts_diagnostics::{Diagnostic, message_by_code};

#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TypeId(u32);

impl TypeId {
    #[must_use]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum TypeKind {
    Any,
    Unknown,
    Never,
    Void,
    Undefined,
    Null,
    Boolean,
    Number,
    String,
    BigInt,
    BooleanLiteral(bool),
    NumberLiteral(String),
    StringLiteral(String),
    BigIntLiteral(String),
    TypeParameter {
        name: String,
        constraint: Option<TypeId>,
    },
    Array(TypeId),
    Tuple(Vec<TypeId>),
    Union(Vec<TypeId>),
    Intersection(Vec<TypeId>),
    Object(ObjectType),
    Function(FunctionType),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ObjectType {
    pub properties: BTreeMap<String, TypeId>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FunctionType {
    pub parameters: Vec<TypeId>,
    pub return_type: TypeId,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Type {
    pub id: TypeId,
    pub kind: TypeKind,
}

#[derive(Clone, Debug)]
pub struct TypeArena {
    types: Vec<Type>,
}

impl Default for TypeArena {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeArena {
    #[must_use]
    pub fn new() -> Self {
        let mut arena = Self { types: Vec::new() };
        for kind in [
            TypeKind::Any,
            TypeKind::Unknown,
            TypeKind::Never,
            TypeKind::Void,
            TypeKind::Undefined,
            TypeKind::Null,
            TypeKind::Boolean,
            TypeKind::Number,
            TypeKind::String,
            TypeKind::BigInt,
        ] {
            arena.alloc(kind);
        }
        arena
    }

    #[must_use]
    pub fn get(&self, id: TypeId) -> Option<&Type> {
        self.types.get(id.index())
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.types.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.types.is_empty()
    }

    #[must_use]
    pub const fn any(&self) -> TypeId {
        TypeId(0)
    }
    #[must_use]
    pub const fn unknown(&self) -> TypeId {
        TypeId(1)
    }
    #[must_use]
    pub const fn never(&self) -> TypeId {
        TypeId(2)
    }
    #[must_use]
    pub const fn void(&self) -> TypeId {
        TypeId(3)
    }
    #[must_use]
    pub const fn undefined(&self) -> TypeId {
        TypeId(4)
    }
    #[must_use]
    pub const fn null(&self) -> TypeId {
        TypeId(5)
    }
    #[must_use]
    pub const fn boolean(&self) -> TypeId {
        TypeId(6)
    }
    #[must_use]
    pub const fn number(&self) -> TypeId {
        TypeId(7)
    }
    #[must_use]
    pub const fn string(&self) -> TypeId {
        TypeId(8)
    }
    #[must_use]
    pub const fn bigint(&self) -> TypeId {
        TypeId(9)
    }

    /// Allocates a semantic type with a stable ID.
    ///
    /// # Panics
    ///
    /// Panics if the arena exceeds the maximum number of addressable types.
    pub fn alloc(&mut self, kind: TypeKind) -> TypeId {
        let id =
            TypeId(u32::try_from(self.types.len()).expect("type arena exceeds u32::MAX types"));
        self.types.push(Type { id, kind });
        id
    }

    pub fn union(&mut self, members: impl IntoIterator<Item = TypeId>) -> TypeId {
        let mut flattened = Vec::new();
        for member in members {
            if member == self.any() {
                return self.any();
            }
            if member == self.never() {
                continue;
            }
            match &self.types[member.index()].kind {
                TypeKind::Union(nested) => flattened.extend(nested.iter().copied()),
                _ => flattened.push(member),
            }
        }
        let has_boolean = flattened.iter().any(|member| *member == self.boolean());
        let has_number = flattened.iter().any(|member| *member == self.number());
        let has_string = flattened.iter().any(|member| *member == self.string());
        let has_bigint = flattened.iter().any(|member| *member == self.bigint());
        flattened.retain(|member| {
            !matches!(
                &self.types[member.index()].kind,
                TypeKind::BooleanLiteral(_) if has_boolean
            ) && !matches!(
                &self.types[member.index()].kind,
                TypeKind::NumberLiteral(_) if has_number
            ) && !matches!(
                &self.types[member.index()].kind,
                TypeKind::StringLiteral(_) if has_string
            ) && !matches!(
                &self.types[member.index()].kind,
                TypeKind::BigIntLiteral(_) if has_bigint
            )
        });
        flattened.sort_unstable();
        flattened.dedup();
        match flattened.as_slice() {
            [] => self.never(),
            [single] => *single,
            _ => self.alloc(TypeKind::Union(flattened)),
        }
    }

    pub fn intersection(&mut self, members: impl IntoIterator<Item = TypeId>) -> TypeId {
        let mut flattened = Vec::new();
        for member in members {
            if member == self.never() || member == self.any() {
                return member;
            }
            if member == self.unknown() {
                continue;
            }
            match &self.types[member.index()].kind {
                TypeKind::Intersection(nested) => flattened.extend(nested.iter().copied()),
                _ => flattened.push(member),
            }
        }
        flattened.sort_unstable();
        flattened.dedup();
        match flattened.as_slice() {
            [] => self.unknown(),
            [single] => *single,
            _ => self.alloc(TypeKind::Intersection(flattened)),
        }
    }

    #[must_use]
    pub fn display(&self, id: TypeId) -> String {
        match &self.types[id.index()].kind {
            TypeKind::Any => "any".into(),
            TypeKind::Unknown => "unknown".into(),
            TypeKind::Never => "never".into(),
            TypeKind::Void => "void".into(),
            TypeKind::Undefined => "undefined".into(),
            TypeKind::Null => "null".into(),
            TypeKind::Boolean => "boolean".into(),
            TypeKind::Number => "number".into(),
            TypeKind::String => "string".into(),
            TypeKind::BigInt => "bigint".into(),
            TypeKind::BooleanLiteral(value) => value.to_string(),
            TypeKind::NumberLiteral(value) | TypeKind::BigIntLiteral(value) => value.clone(),
            TypeKind::StringLiteral(value) => format!("{value:?}"),
            TypeKind::TypeParameter { name, .. } => name.clone(),
            TypeKind::Array(element) => format!("{}[]", self.display(*element)),
            TypeKind::Tuple(elements) => format!(
                "[{}]",
                elements
                    .iter()
                    .map(|element| self.display(*element))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            TypeKind::Union(members) => members
                .iter()
                .map(|member| self.display(*member))
                .collect::<Vec<_>>()
                .join(" | "),
            TypeKind::Intersection(members) => members
                .iter()
                .map(|member| self.display(*member))
                .collect::<Vec<_>>()
                .join(" & "),
            TypeKind::Object(object) => format!(
                "{{ {} }}",
                object
                    .properties
                    .iter()
                    .map(|(name, value)| format!("{name}: {}", self.display(*value)))
                    .collect::<Vec<_>>()
                    .join("; ")
            ),
            TypeKind::Function(function) => format!(
                "({}) => {}",
                function
                    .parameters
                    .iter()
                    .enumerate()
                    .map(|(index, value)| format!("arg{index}: {}", self.display(*value)))
                    .collect::<Vec<_>>()
                    .join(", "),
                self.display(function.return_type)
            ),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckDiagnostic {
    pub node: NodeId,
    pub diagnostic: Diagnostic,
}

#[derive(Clone, Debug)]
pub struct CheckResult {
    pub types: TypeArena,
    pub symbol_types: HashMap<SymbolId, TypeId>,
    pub node_types: BTreeMap<NodeId, TypeId>,
    pub diagnostics: Vec<CheckDiagnostic>,
}

impl CheckResult {
    #[must_use]
    pub fn type_of_symbol(&self, symbol: SymbolId) -> Option<TypeId> {
        self.symbol_types.get(&symbol).copied()
    }

    #[must_use]
    pub fn type_of_node(&self, node: NodeId) -> Option<TypeId> {
        self.node_types.get(&node).copied()
    }
}

#[must_use]
pub fn check_source_file(
    arena: &NodeArena,
    source_file: NodeId,
    bindings: &BindResult,
) -> CheckResult {
    Checker::new(arena, bindings).check(source_file)
}

pub struct ProgramSource<'a> {
    pub arena: &'a NodeArena,
    pub source_file: NodeId,
    pub bindings: &'a BindResult,
    pub resolved_modules: &'a BTreeMap<String, usize>,
}

#[derive(Debug)]
pub struct ProgramCheckResult {
    pub files: Vec<CheckResult>,
}

#[must_use]
pub fn check_program(sources: &[ProgramSource<'_>]) -> ProgramCheckResult {
    ProgramChecker::new(sources).check()
}

#[derive(Clone, Debug)]
enum TypeDescriptor {
    Any,
    Unknown,
    Never,
    Void,
    Undefined,
    Null,
    Boolean,
    Number,
    String,
    BigInt,
    BooleanLiteral(bool),
    NumberLiteral(String),
    StringLiteral(String),
    BigIntLiteral(String),
    TypeParameter(String),
    Alias {
        parameters: Vec<String>,
        body: Box<Self>,
    },
    Array(Box<Self>),
    Tuple(Vec<Self>),
    Union(Vec<Self>),
    Intersection(Vec<Self>),
    Object(BTreeMap<String, Self>),
    Function {
        parameters: Vec<Self>,
        return_type: Box<Self>,
    },
}

struct ProgramChecker<'a> {
    sources: &'a [ProgramSource<'a>],
}

type DuplicateGlobal = (usize, NodeId, u32, String);
type GlobalCollection = (BTreeMap<String, TypeDescriptor>, Vec<DuplicateGlobal>);

impl<'a> ProgramChecker<'a> {
    const fn new(sources: &'a [ProgramSource<'a>]) -> Self {
        Self { sources }
    }

    fn check(self) -> ProgramCheckResult {
        let preliminary = self
            .sources
            .iter()
            .map(|source| check_source_file(source.arena, source.source_file, source.bindings))
            .collect::<Vec<_>>();
        let exports = self
            .sources
            .iter()
            .zip(&preliminary)
            .map(|(source, result)| Self::module_exports(source, result))
            .collect::<Vec<_>>();
        let (globals, duplicate_globals) = self.globals(&preliminary);
        let mut files = Vec::with_capacity(self.sources.len());
        for source in self.sources {
            let (external_symbols, mut import_diagnostics) = Self::imports(source, &exports);
            let mut result = Checker::new(source.arena, source.bindings)
                .with_environment(external_symbols, globals.clone())
                .check(source.source_file);
            result.diagnostics.append(&mut import_diagnostics);
            files.push(result);
        }
        for (file_index, node, code, name) in duplicate_globals {
            let message = message_by_code(code).expect("checker diagnostic is in catalog");
            files[file_index].diagnostics.push(CheckDiagnostic {
                node,
                diagnostic: Diagnostic::with_arguments(message, [name]),
            });
        }
        ProgramCheckResult { files }
    }

    fn module_exports(
        source: &ProgramSource<'_>,
        result: &CheckResult,
    ) -> BTreeMap<String, TypeDescriptor> {
        source
            .bindings
            .exports
            .iter()
            .filter_map(|(name, symbol)| {
                Self::describe_symbol(source, result, symbol)
                    .map(|descriptor| (name.to_owned(), descriptor))
            })
            .collect()
    }

    fn globals(&self, results: &[CheckResult]) -> GlobalCollection {
        let mut globals = BTreeMap::new();
        let mut declarations = BTreeMap::<String, (usize, ts_binder::SymbolFlags)>::new();
        let mut duplicates = Vec::new();
        for (file_index, (source, result)) in self.sources.iter().zip(results).enumerate() {
            if is_external_module(source) {
                continue;
            }
            let Some(root) = source.bindings.root_scope() else {
                continue;
            };
            for (name, symbol_id) in root.symbols.iter() {
                let Some(symbol) = source.bindings.symbols.get(symbol_id) else {
                    continue;
                };
                if let Some((_, existing_flags)) = declarations.get(name) {
                    if !global_declarations_merge(*existing_flags, symbol.flags) {
                        let code = if existing_flags
                            .intersects(ts_binder::SymbolFlags::BLOCK_SCOPED_VARIABLE)
                            || symbol
                                .flags
                                .intersects(ts_binder::SymbolFlags::BLOCK_SCOPED_VARIABLE)
                        {
                            2451
                        } else {
                            2300
                        };
                        if let Some(declaration) = symbol.declarations.first() {
                            duplicates.push((file_index, *declaration, code, name.to_owned()));
                        }
                    }
                    continue;
                }
                if let Some(descriptor) = Self::describe_symbol(source, result, symbol_id) {
                    globals.insert(name.to_owned(), descriptor);
                    declarations.insert(name.to_owned(), (file_index, symbol.flags));
                }
            }
        }
        (globals, duplicates)
    }

    fn imports(
        source: &ProgramSource<'_>,
        exports: &[BTreeMap<String, TypeDescriptor>],
    ) -> (HashMap<SymbolId, TypeDescriptor>, Vec<CheckDiagnostic>) {
        let mut symbols = HashMap::new();
        let mut diagnostics = Vec::new();
        let Some(NodeData::SourceFile(file)) =
            source.arena.get(source.source_file).map(|node| &node.data)
        else {
            return (symbols, diagnostics);
        };
        for statement in &file.statements.nodes {
            let Some(NodeData::ImportDeclaration(import)) =
                source.arena.get(*statement).map(|node| &node.data)
            else {
                continue;
            };
            let Some(specifier) = string_literal_text(source.arena, import.module_specifier) else {
                continue;
            };
            let Some(target) = source.resolved_modules.get(specifier).copied() else {
                continue;
            };
            let Some(module_exports) = exports.get(target) else {
                continue;
            };
            let Some(clause) = import.import_clause else {
                continue;
            };
            let Some(NodeData::ImportClause(clause_data)) =
                source.arena.get(clause).map(|node| &node.data)
            else {
                continue;
            };
            if let Some(name) = clause_data.name
                && let Some(symbol) = source.bindings.node_symbols.get(&name)
            {
                Self::bind_import(
                    *symbol,
                    "default",
                    specifier,
                    name,
                    module_exports,
                    &mut symbols,
                    &mut diagnostics,
                );
            }
            if let Some(bindings) = clause_data.named_bindings
                && let Some(NodeData::NamedImports(named)) =
                    source.arena.get(bindings).map(|node| &node.data)
            {
                for specifier_node in &named.elements.nodes {
                    let Some(NodeData::ImportSpecifier(import_specifier)) =
                        source.arena.get(*specifier_node).map(|node| &node.data)
                    else {
                        continue;
                    };
                    let imported_node = import_specifier
                        .property_name
                        .unwrap_or(import_specifier.name);
                    let Some(imported_name) = identifier_text(source.arena, imported_node) else {
                        continue;
                    };
                    let Some(symbol) = source.bindings.node_symbols.get(&import_specifier.name)
                    else {
                        continue;
                    };
                    Self::bind_import(
                        *symbol,
                        imported_name,
                        specifier,
                        *specifier_node,
                        module_exports,
                        &mut symbols,
                        &mut diagnostics,
                    );
                }
            }
        }
        (symbols, diagnostics)
    }

    #[allow(clippy::too_many_arguments)]
    fn bind_import(
        symbol: SymbolId,
        imported_name: &str,
        module_name: &str,
        node: NodeId,
        exports: &BTreeMap<String, TypeDescriptor>,
        symbols: &mut HashMap<SymbolId, TypeDescriptor>,
        diagnostics: &mut Vec<CheckDiagnostic>,
    ) {
        if let Some(descriptor) = exports.get(imported_name) {
            symbols.insert(symbol, descriptor.clone());
        } else {
            let message = message_by_code(2305).expect("checker diagnostic is in catalog");
            diagnostics.push(CheckDiagnostic {
                node,
                diagnostic: Diagnostic::with_arguments(
                    message,
                    [module_name.to_owned(), imported_name.to_owned()],
                ),
            });
        }
    }

    fn describe_symbol(
        source: &ProgramSource<'_>,
        result: &CheckResult,
        symbol_id: SymbolId,
    ) -> Option<TypeDescriptor> {
        let symbol = source.bindings.symbols.get(symbol_id)?;
        let target = symbol.target.unwrap_or(symbol_id);
        let target_symbol = source.bindings.symbols.get(target)?;
        for declaration in &target_symbol.declarations {
            match source.arena.get(*declaration).map(|node| &node.data) {
                Some(NodeData::TypeAliasDeclaration(alias)) => {
                    return Some(describe_alias(source, alias));
                }
                Some(NodeData::ExportAssignment(assignment)) => {
                    if let Some(type_id) = result.type_of_node(assignment.expression) {
                        return Some(describe_type(&result.types, type_id));
                    }
                }
                _ => {}
            }
        }
        result
            .type_of_symbol(target)
            .map(|type_id| describe_type(&result.types, type_id))
    }
}

struct Checker<'a> {
    arena: &'a NodeArena,
    bindings: &'a BindResult,
    result: CheckResult,
    children: HashMap<NodeId, Vec<NodeId>>,
    type_parameter_scopes: Vec<HashMap<String, TypeId>>,
    local_scopes: Vec<HashMap<String, TypeId>>,
    narrowings: Vec<HashMap<SymbolId, TypeId>>,
    alias_stack: Vec<SymbolId>,
    external_symbols: HashMap<SymbolId, TypeDescriptor>,
    external_names: BTreeMap<String, TypeDescriptor>,
    external_aliases: HashMap<SymbolId, TypeDescriptor>,
}

impl<'a> Checker<'a> {
    fn new(arena: &'a NodeArena, bindings: &'a BindResult) -> Self {
        let mut children = HashMap::<NodeId, Vec<NodeId>>::new();
        for (id, node) in arena.iter() {
            if let Some(parent) = node.parent {
                children.entry(parent).or_default().push(id);
            }
        }
        Self {
            arena,
            bindings,
            result: CheckResult {
                types: TypeArena::new(),
                symbol_types: HashMap::new(),
                node_types: BTreeMap::new(),
                diagnostics: Vec::new(),
            },
            children,
            type_parameter_scopes: Vec::new(),
            local_scopes: Vec::new(),
            narrowings: Vec::new(),
            alias_stack: Vec::new(),
            external_symbols: HashMap::new(),
            external_names: BTreeMap::new(),
            external_aliases: HashMap::new(),
        }
    }

    fn with_environment(
        mut self,
        symbols: HashMap<SymbolId, TypeDescriptor>,
        names: BTreeMap<String, TypeDescriptor>,
    ) -> Self {
        self.external_symbols = symbols;
        self.external_names = names;
        self
    }

    fn check(mut self, source_file: NodeId) -> CheckResult {
        self.seed_symbol_types();
        for (symbol, descriptor) in std::mem::take(&mut self.external_symbols) {
            if matches!(descriptor, TypeDescriptor::Alias { .. }) {
                self.external_aliases.insert(symbol, descriptor.clone());
            }
            let type_id = self.import_type(&descriptor);
            self.result.symbol_types.insert(symbol, type_id);
        }
        let mut saw_return = false;
        self.check_node(source_file, None, &mut saw_return);
        self.result
    }

    fn seed_symbol_types(&mut self) {
        for symbol in self.bindings.symbols.iter() {
            let mut symbol_type = None;
            for declaration in &symbol.declarations {
                let Some(node) = self.arena.get(*declaration) else {
                    continue;
                };
                match &node.data {
                    NodeData::VariableDeclaration(data) => {
                        if let Some(annotation) = data.type_ {
                            symbol_type = Some(self.type_from_type_node(annotation));
                            break;
                        }
                    }
                    NodeData::ParameterDeclaration(data) => {
                        symbol_type = Some(match data.type_ {
                            Some(annotation) => self.type_from_type_node(annotation),
                            None => self.result.types.any(),
                        });
                        break;
                    }
                    NodeData::FunctionDeclaration(data) => {
                        symbol_type = Some(self.function_type(data));
                        break;
                    }
                    NodeData::ClassDeclaration(data) => {
                        symbol_type = Some(self.object_type_from_members(&data.members.nodes));
                        break;
                    }
                    NodeData::InterfaceDeclaration(data) => {
                        symbol_type = Some(self.object_type_from_members(&data.members.nodes));
                        break;
                    }
                    NodeData::TypeAliasDeclaration(data) => {
                        symbol_type = Some(self.type_alias_type(data, &[]));
                        break;
                    }
                    _ => {}
                }
            }
            self.result.symbol_types.insert(
                symbol.id,
                symbol_type.unwrap_or_else(|| self.result.types.any()),
            );
        }
    }

    #[allow(clippy::too_many_lines)]
    fn check_node(
        &mut self,
        node_id: NodeId,
        expected_return: Option<TypeId>,
        saw_return: &mut bool,
    ) {
        let Some(node) = self.arena.get(node_id) else {
            return;
        };
        match &node.data {
            NodeData::SourceFile(data) => {
                for statement in &data.statements.nodes {
                    self.check_node(*statement, None, saw_return);
                }
            }
            NodeData::Block(data) => {
                for statement in &data.statements.nodes {
                    self.check_node(*statement, expected_return, saw_return);
                }
            }
            NodeData::ModuleBlock(data) => {
                for statement in &data.statements.nodes {
                    self.check_node(*statement, expected_return, saw_return);
                }
            }
            NodeData::VariableStatement(data) => {
                self.check_node(data.declaration_list, expected_return, saw_return);
            }
            NodeData::VariableDeclarationList(data) => {
                for declaration in &data.declarations.nodes {
                    self.check_node(*declaration, expected_return, saw_return);
                }
            }
            NodeData::VariableDeclaration(data) => {
                let annotation = data.type_.map(|node| self.type_from_type_node(node));
                let initializer = data
                    .initializer
                    .map(|node| self.type_of_expression_context(node, annotation));
                if let (Some(actual), Some(expected)) = (initializer, annotation)
                    && !self.is_assignable(actual, expected)
                {
                    self.assignability_error(node_id, actual, expected);
                }
                if let Some(symbol) = self.bindings.node_symbols.get(&node_id) {
                    let inferred = annotation
                        .or(initializer.map(|value| {
                            if self.is_const_declaration(node_id)
                                && matches!(
                                    self.result.types.get(value).map(|value| &value.kind),
                                    Some(
                                        TypeKind::NumberLiteral(_)
                                            | TypeKind::StringLiteral(_)
                                            | TypeKind::BigIntLiteral(_)
                                            | TypeKind::BooleanLiteral(_)
                                    )
                                )
                            {
                                value
                            } else {
                                self.widen_literal(value)
                            }
                        }))
                        .unwrap_or_else(|| self.result.types.any());
                    self.result.symbol_types.insert(*symbol, inferred);
                }
            }
            NodeData::FunctionDeclaration(data) => {
                self.check_function(node_id, data);
            }
            NodeData::ClassDeclaration(data) => {
                self.check_class_members(&data.members.nodes);
            }
            NodeData::IfStatement(data) => {
                self.type_of_expression(data.expression);
                let then_narrowing = self.condition_narrowing(data.expression, true);
                self.narrowings.push(then_narrowing);
                self.check_node(data.then_statement, expected_return, saw_return);
                self.narrowings.pop();
                if let Some(else_statement) = data.else_statement {
                    let else_narrowing = self.condition_narrowing(data.expression, false);
                    self.narrowings.push(else_narrowing);
                    self.check_node(else_statement, expected_return, saw_return);
                    self.narrowings.pop();
                }
            }
            NodeData::ReturnStatement(data) => {
                *saw_return = true;
                if let Some(expected) = expected_return {
                    let actual = match data.expression {
                        Some(expression) => self.type_of_expression(expression),
                        None => self.result.types.undefined(),
                    };
                    if !self.is_assignable(actual, expected) {
                        self.assignability_error(node_id, actual, expected);
                    }
                }
            }
            NodeData::ExpressionStatement(data) => {
                self.type_of_expression(data.expression);
            }
            NodeData::ExportAssignment(data) => {
                self.type_of_expression(data.expression);
            }
            _ => {
                let children = self.children.get(&node_id).cloned().unwrap_or_default();
                for child in children {
                    self.check_node(child, expected_return, saw_return);
                }
            }
        }
    }

    fn check_function(&mut self, node_id: NodeId, data: &ts_ast::FunctionDeclarationData) {
        let function_type = self
            .bindings
            .node_symbols
            .get(&node_id)
            .and_then(|symbol| self.result.symbol_types.get(symbol))
            .copied()
            .unwrap_or_else(|| self.function_type(data));
        let signature = match &self.result.types.get(function_type).unwrap().kind {
            TypeKind::Function(function) => Some(function.clone()),
            _ => None,
        };
        let return_type = signature
            .as_ref()
            .map_or_else(|| self.result.types.any(), |function| function.return_type);
        for parameter in &data.parameters.nodes {
            self.check_parameter(*parameter);
        }
        let mut local_scope = HashMap::new();
        for (index, parameter) in data.parameters.nodes.iter().enumerate() {
            let Some(NodeData::ParameterDeclaration(parameter_data)) =
                self.arena.get(*parameter).map(|node| &node.data)
            else {
                continue;
            };
            if let Some(name) = self.property_name(parameter_data.name) {
                let type_id = signature
                    .as_ref()
                    .and_then(|signature| signature.parameters.get(index))
                    .copied()
                    .unwrap_or_else(|| self.result.types.any());
                local_scope.insert(name, type_id);
            }
        }
        self.local_scopes.push(local_scope);
        let mut saw_return = false;
        if let Some(body) = data.body {
            self.check_node(body, Some(return_type), &mut saw_return);
        }
        self.local_scopes.pop();
        if data.body.is_some()
            && !saw_return
            && !matches!(
                self.result.types.get(return_type).map(|value| &value.kind),
                Some(TypeKind::Any | TypeKind::Void | TypeKind::Undefined)
            )
        {
            self.error(node_id, 2355, std::iter::empty());
        }
    }

    fn check_parameter(&mut self, parameter: NodeId) {
        let Some(NodeData::ParameterDeclaration(data)) =
            self.arena.get(parameter).map(|node| &node.data)
        else {
            return;
        };
        if let Some(initializer) = data.initializer {
            let actual = self.type_of_expression(initializer);
            let expected = match data.type_ {
                Some(node) => self.type_from_type_node(node),
                None => self.result.types.any(),
            };
            if !self.is_assignable(actual, expected) {
                self.assignability_error(parameter, actual, expected);
            }
        }
    }

    fn object_type_from_members(&mut self, members: &[NodeId]) -> TypeId {
        let mut properties = BTreeMap::new();
        for member in members {
            let Some(node) = self.arena.get(*member) else {
                continue;
            };
            match &node.data {
                NodeData::PropertyDeclaration(data) => {
                    if let Some(name) = self.property_name(data.name) {
                        let property_type = data
                            .type_
                            .map(|type_node| self.type_from_type_node(type_node))
                            .or_else(|| {
                                data.initializer.map(|value| self.type_of_expression(value))
                            })
                            .unwrap_or_else(|| self.result.types.any());
                        properties.insert(name, property_type);
                    }
                }
                NodeData::PropertySignatureDeclaration(data) => {
                    if let Some(name) = self.property_name(data.name) {
                        let property_type = self.type_from_type_node(data.type_);
                        properties.insert(name, property_type);
                    }
                }
                NodeData::MethodDeclaration(data) => {
                    if let Some(name) = self.property_name(data.name) {
                        let method_type = self.signature_type(
                            &data.parameters.nodes,
                            data.type_,
                            data.type_parameters.as_ref(),
                        );
                        properties.insert(name, method_type);
                    }
                }
                NodeData::MethodSignatureDeclaration(data) => {
                    if let Some(name) = self.property_name(data.name) {
                        let method_type = self.signature_type(
                            &data.parameters.nodes,
                            data.type_,
                            data.type_parameters.as_ref(),
                        );
                        properties.insert(name, method_type);
                    }
                }
                _ => {}
            }
        }
        self.result
            .types
            .alloc(TypeKind::Object(ObjectType { properties }))
    }

    fn check_class_members(&mut self, members: &[NodeId]) {
        for member in members {
            let Some(node) = self.arena.get(*member) else {
                continue;
            };
            match &node.data {
                NodeData::PropertyDeclaration(data) => {
                    if let Some(initializer) = data.initializer {
                        let expected = data.type_.map(|node| self.type_from_type_node(node));
                        let actual = self.type_of_expression_context(initializer, expected);
                        if let Some(expected) = expected
                            && !self.is_assignable(actual, expected)
                        {
                            self.assignability_error(*member, actual, expected);
                        }
                    }
                }
                NodeData::MethodDeclaration(data) => {
                    let return_type = match data.type_ {
                        Some(node) => self.type_from_type_node(node),
                        None => self.result.types.any(),
                    };
                    let local_scope = self.parameter_scope(&data.parameters.nodes);
                    self.local_scopes.push(local_scope);
                    let mut saw_return = false;
                    if let Some(body) = data.body {
                        self.check_node(body, Some(return_type), &mut saw_return);
                    }
                    self.local_scopes.pop();
                }
                _ => {}
            }
        }
    }

    fn parameter_scope(&mut self, parameters: &[NodeId]) -> HashMap<String, TypeId> {
        let mut scope = HashMap::new();
        for parameter in parameters {
            let Some(NodeData::ParameterDeclaration(data)) =
                self.arena.get(*parameter).map(|node| &node.data)
            else {
                continue;
            };
            let Some(name) = self.property_name(data.name) else {
                continue;
            };
            let type_id = match data.type_ {
                Some(node) => self.type_from_type_node(node),
                None => self.result.types.any(),
            };
            scope.insert(name, type_id);
        }
        scope
    }

    fn condition_narrowing(
        &mut self,
        expression: NodeId,
        truthy: bool,
    ) -> HashMap<SymbolId, TypeId> {
        let mut result = HashMap::new();
        let Some(NodeData::BinaryExpression(binary)) =
            self.arena.get(expression).map(|node| &node.data)
        else {
            return result;
        };
        let operator = self
            .arena
            .get(binary.operator_token)
            .map_or(SyntaxKind::Unknown, |node| node.kind);
        let equality = matches!(
            operator,
            SyntaxKind::EqualsEqualsToken | SyntaxKind::EqualsEqualsEqualsToken
        );
        let inequality = matches!(
            operator,
            SyntaxKind::ExclamationEqualsToken | SyntaxKind::ExclamationEqualsEqualsToken
        );
        if !equality && !inequality {
            return result;
        }
        let include_match = if inequality { !truthy } else { truthy };
        let (subject, comparison) = match (
            self.narrowing_subject(binary.left),
            self.narrowing_comparison(binary.right),
        ) {
            (Some(subject), Some(comparison)) => (subject, comparison),
            _ => match (
                self.narrowing_subject(binary.right),
                self.narrowing_comparison(binary.left),
            ) {
                (Some(subject), Some(comparison)) => (subject, comparison),
                _ => return result,
            },
        };
        let Some(original) = self.result.symbol_types.get(&subject).copied() else {
            return result;
        };
        let loose_null = matches!(
            operator,
            SyntaxKind::EqualsEqualsToken | SyntaxKind::ExclamationEqualsToken
        ) && matches!(
            comparison,
            NarrowingComparison::Null | NarrowingComparison::Undefined
        );
        let narrowed = self.filter_type(original, include_match, |kind| {
            if loose_null {
                matches!(kind, TypeKind::Null | TypeKind::Undefined)
            } else {
                comparison.matches(kind)
            }
        });
        result.insert(subject, narrowed);
        result
    }

    fn narrowing_subject(&self, node: NodeId) -> Option<SymbolId> {
        match &self.arena.get(node)?.data {
            NodeData::Identifier(data) => self.resolve_identifier(node, &data.text),
            NodeData::TypeOfExpression(data) => {
                let NodeData::Identifier(identifier) = &self.arena.get(data.expression)?.data
                else {
                    return None;
                };
                self.resolve_identifier(data.expression, &identifier.text)
            }
            _ => None,
        }
    }

    fn narrowing_comparison(&self, node: NodeId) -> Option<NarrowingComparison> {
        let node = self.arena.get(node)?;
        match &node.data {
            NodeData::KeywordExpression(_) if node.kind == SyntaxKind::NullKeyword => {
                Some(NarrowingComparison::Null)
            }
            NodeData::Identifier(data) if data.text == "undefined" => {
                Some(NarrowingComparison::Undefined)
            }
            NodeData::StringLiteral(data) => Some(match data.text.as_str() {
                "string" => NarrowingComparison::String,
                "number" => NarrowingComparison::Number,
                "bigint" => NarrowingComparison::BigInt,
                "boolean" => NarrowingComparison::Boolean,
                "undefined" => NarrowingComparison::Undefined,
                "function" => NarrowingComparison::Function,
                "object" => NarrowingComparison::Object,
                _ => return None,
            }),
            _ => None,
        }
    }

    fn filter_type(
        &mut self,
        original: TypeId,
        include_match: bool,
        predicate: impl Fn(&TypeKind) -> bool,
    ) -> TypeId {
        let members = match self.result.types.get(original).unwrap().kind.clone() {
            TypeKind::Union(members) => members,
            _ => vec![original],
        };
        let filtered = members
            .into_iter()
            .filter(|member| {
                predicate(&self.result.types.get(*member).unwrap().kind) == include_match
            })
            .collect::<Vec<_>>();
        self.result.types.union(filtered)
    }

    fn type_of_expression(&mut self, node_id: NodeId) -> TypeId {
        self.type_of_expression_context(node_id, None)
    }

    #[allow(clippy::too_many_lines)]
    fn type_of_expression_context(
        &mut self,
        node_id: NodeId,
        contextual_type: Option<TypeId>,
    ) -> TypeId {
        if let Some(existing) = self.result.node_types.get(&node_id) {
            return *existing;
        }
        let Some(node) = self.arena.get(node_id) else {
            return self.result.types.unknown();
        };
        let result = match &node.data {
            NodeData::NumericLiteral(data) => self
                .result
                .types
                .alloc(TypeKind::NumberLiteral(data.text.clone())),
            NodeData::BigIntLiteral(data) => self
                .result
                .types
                .alloc(TypeKind::BigIntLiteral(data.text.clone())),
            NodeData::StringLiteral(data) => self
                .result
                .types
                .alloc(TypeKind::StringLiteral(data.text.clone())),
            NodeData::NoSubstitutionTemplateLiteral(data) => self
                .result
                .types
                .alloc(TypeKind::StringLiteral(data.text.clone())),
            NodeData::KeywordExpression(_) => match node.kind {
                SyntaxKind::TrueKeyword => self.result.types.alloc(TypeKind::BooleanLiteral(true)),
                SyntaxKind::FalseKeyword => {
                    self.result.types.alloc(TypeKind::BooleanLiteral(false))
                }
                SyntaxKind::NullKeyword => self.result.types.null(),
                _ => self.result.types.unknown(),
            },
            NodeData::Identifier(identifier) => self.identifier_type(node_id, &identifier.text),
            NodeData::ParenthesizedExpression(data) => {
                self.type_of_expression_context(data.expression, contextual_type)
            }
            NodeData::BinaryExpression(data) => {
                let left = self.type_of_expression(data.left);
                let right = self.type_of_expression(data.right);
                let operator = self
                    .arena
                    .get(data.operator_token)
                    .map_or(SyntaxKind::Unknown, |node| node.kind);
                self.check_binary(node_id, operator, left, right)
            }
            NodeData::ObjectLiteralExpression(data) => {
                let contextual_properties = contextual_type.and_then(|type_id| {
                    match &self.result.types.get(type_id)?.kind {
                        TypeKind::Object(object) => Some(object.properties.clone()),
                        _ => None,
                    }
                });
                let mut properties = BTreeMap::new();
                for property in &data.properties.nodes {
                    if let Some(NodeData::PropertyAssignment(property_data)) =
                        self.arena.get(*property).map(|node| &node.data)
                        && let Some(name) = self.property_name(property_data.name)
                    {
                        let expected = contextual_properties
                            .as_ref()
                            .and_then(|properties| properties.get(&name))
                            .copied();
                        let actual =
                            self.type_of_expression_context(property_data.initializer, expected);
                        if let Some(expected) = expected
                            && !self.is_assignable(actual, expected)
                        {
                            self.assignability_error(*property, actual, expected);
                        }
                        properties.insert(name, actual);
                    }
                }
                self.result
                    .types
                    .alloc(TypeKind::Object(ObjectType { properties }))
            }
            NodeData::ArrayLiteralExpression(data) => {
                let expected_tuple = contextual_type.and_then(|type_id| {
                    match &self.result.types.get(type_id)?.kind {
                        TypeKind::Tuple(elements) => Some(elements.clone()),
                        _ => None,
                    }
                });
                let expected_element = contextual_type.and_then(|type_id| {
                    match self.result.types.get(type_id)?.kind {
                        TypeKind::Array(element) => Some(element),
                        _ => None,
                    }
                });
                let mut element_types = Vec::with_capacity(data.elements.nodes.len());
                for (index, element) in data.elements.nodes.iter().enumerate() {
                    let expected = expected_tuple
                        .as_ref()
                        .and_then(|elements| elements.get(index))
                        .copied()
                        .or(expected_element);
                    let actual = self.type_of_expression_context(*element, expected);
                    if let Some(expected) = expected
                        && !self.is_assignable(actual, expected)
                    {
                        self.assignability_error(*element, actual, expected);
                    }
                    element_types.push(self.widen_literal(actual));
                }
                if let Some(expected) = expected_tuple {
                    if expected.len() == element_types.len() {
                        self.result.types.alloc(TypeKind::Tuple(expected))
                    } else {
                        self.result.types.alloc(TypeKind::Tuple(element_types))
                    }
                } else {
                    let element = expected_element.unwrap_or_else(|| {
                        if element_types.is_empty() {
                            self.result.types.never()
                        } else {
                            self.result.types.union(element_types)
                        }
                    });
                    self.result.types.alloc(TypeKind::Array(element))
                }
            }
            NodeData::ArrowFunction(data) => self.arrow_type(data, contextual_type),
            NodeData::PropertyAccessExpression(data) => {
                let receiver = self.type_of_expression(data.expression);
                let name = self.property_name(data.name).unwrap_or_default();
                self.property_access_type(node_id, receiver, &name)
            }
            NodeData::ElementAccessExpression(data) => {
                let receiver = self.type_of_expression(data.expression);
                let index = self.type_of_expression(data.argument_expression);
                self.element_access_type(node_id, receiver, index)
            }
            NodeData::CallExpression(data) => {
                let callee = self.type_of_expression(data.expression);
                self.call_expression_type(node_id, callee, &data.arguments.nodes, false)
            }
            NodeData::NewExpression(data) => {
                let callee = self.type_of_expression(data.expression);
                let arguments = data.arguments.as_ref().map_or(&[][..], |list| &list.nodes);
                self.call_expression_type(node_id, callee, arguments, true)
            }
            NodeData::TypeOfExpression(_) => self.result.types.string(),
            NodeData::FunctionDeclaration(data) => self.function_type(data),
            _ => self.result.types.unknown(),
        };
        self.result.node_types.insert(node_id, result);
        result
    }

    fn identifier_type(&mut self, node: NodeId, name: &str) -> TypeId {
        if name == "undefined" {
            return self.result.types.undefined();
        }
        for scope in self.local_scopes.iter().rev() {
            if let Some(type_id) = scope.get(name) {
                return *type_id;
            }
        }
        if let Some(symbol) = self.resolve_identifier(node, name) {
            for narrowing in self.narrowings.iter().rev() {
                if let Some(type_id) = narrowing.get(&symbol) {
                    return *type_id;
                }
            }
            return self
                .result
                .symbol_types
                .get(&symbol)
                .copied()
                .unwrap_or_else(|| self.result.types.any());
        }
        if let Some(descriptor) = self.external_names.get(name).cloned() {
            return self.import_type(&descriptor);
        }
        self.error(node, 2304, [name.to_owned()]);
        self.result.types.any()
    }

    fn arrow_type(
        &mut self,
        data: &ts_ast::ArrowFunctionData,
        contextual_type: Option<TypeId>,
    ) -> TypeId {
        let contextual_signature =
            contextual_type.and_then(|type_id| match &self.result.types.get(type_id)?.kind {
                TypeKind::Function(signature) => Some(signature.clone()),
                _ => None,
            });
        let mut parameters = Vec::with_capacity(data.parameters.nodes.len());
        let mut local_scope = HashMap::new();
        for (index, parameter) in data.parameters.nodes.iter().enumerate() {
            let Some(NodeData::ParameterDeclaration(parameter_data)) =
                self.arena.get(*parameter).map(|node| &node.data)
            else {
                parameters.push(self.result.types.any());
                continue;
            };
            let parameter_type = parameter_data
                .type_
                .map(|node| self.type_from_type_node(node))
                .or_else(|| {
                    contextual_signature
                        .as_ref()
                        .and_then(|signature| signature.parameters.get(index))
                        .copied()
                })
                .unwrap_or_else(|| self.result.types.any());
            if let Some(name) = self.property_name(parameter_data.name) {
                local_scope.insert(name, parameter_type);
            }
            parameters.push(parameter_type);
        }
        self.local_scopes.push(local_scope);
        let expected_return = data
            .type_
            .map(|node| self.type_from_type_node(node))
            .or_else(|| {
                contextual_signature
                    .as_ref()
                    .map(|signature| signature.return_type)
            });
        let return_type = if matches!(
            self.arena.get(data.body).map(|node| node.kind),
            Some(SyntaxKind::Block)
        ) {
            let mut saw_return = false;
            self.check_node(data.body, expected_return, &mut saw_return);
            expected_return.unwrap_or_else(|| self.result.types.any())
        } else {
            let actual = self.type_of_expression_context(data.body, expected_return);
            if let Some(expected) = expected_return
                && !self.is_assignable(actual, expected)
            {
                self.assignability_error(data.body, actual, expected);
            }
            expected_return.unwrap_or_else(|| self.widen_literal(actual))
        };
        self.local_scopes.pop();
        self.result.types.alloc(TypeKind::Function(FunctionType {
            parameters,
            return_type,
        }))
    }

    fn property_access_type(&mut self, node: NodeId, receiver: TypeId, name: &str) -> TypeId {
        if let Some(property) = self.lookup_property_type(receiver, name) {
            property
        } else {
            self.error(
                node,
                2339,
                [name.to_owned(), self.result.types.display(receiver)],
            );
            self.result.types.any()
        }
    }

    fn lookup_property_type(&mut self, receiver: TypeId, name: &str) -> Option<TypeId> {
        match self.result.types.get(receiver)?.kind.clone() {
            TypeKind::Any => Some(self.result.types.any()),
            TypeKind::Object(object) => object.properties.get(name).copied(),
            TypeKind::Array(_) if name == "length" => Some(self.result.types.number()),
            TypeKind::Tuple(elements) if name == "length" => Some(
                self.result
                    .types
                    .alloc(TypeKind::NumberLiteral(elements.len().to_string())),
            ),
            TypeKind::String | TypeKind::StringLiteral(_) if name == "length" => {
                Some(self.result.types.number())
            }
            TypeKind::Union(members) => {
                let properties = members
                    .into_iter()
                    .map(|member| self.lookup_property_type(member, name))
                    .collect::<Option<Vec<_>>>()?;
                Some(self.result.types.union(properties))
            }
            TypeKind::Intersection(members) => {
                let properties = members
                    .into_iter()
                    .filter_map(|member| self.lookup_property_type(member, name))
                    .collect::<Vec<_>>();
                (!properties.is_empty()).then(|| self.result.types.intersection(properties))
            }
            _ => None,
        }
    }

    fn element_access_type(&mut self, node: NodeId, receiver: TypeId, index: TypeId) -> TypeId {
        if let TypeKind::Tuple(elements) = self.result.types.get(receiver).unwrap().kind.clone()
            && let TypeKind::NumberLiteral(value) =
                self.result.types.get(index).unwrap().kind.clone()
            && let Ok(position) = value.parse::<usize>()
            && position >= elements.len()
        {
            self.error(
                node,
                2493,
                [
                    self.result.types.display(receiver),
                    elements.len().to_string(),
                    position.to_string(),
                ],
            );
            return self.result.types.undefined();
        }
        self.lookup_indexed_type(receiver, index)
            .unwrap_or_else(|| {
                self.error(
                    node,
                    7053,
                    [
                        self.result.types.display(index),
                        self.result.types.display(receiver),
                    ],
                );
                self.result.types.any()
            })
    }

    fn indexed_access_type(&mut self, _node: NodeId, object: TypeId, index: TypeId) -> TypeId {
        self.lookup_indexed_type(object, index)
            .unwrap_or_else(|| self.result.types.unknown())
    }

    fn lookup_indexed_type(&mut self, object: TypeId, index: TypeId) -> Option<TypeId> {
        let index_kind = self.result.types.get(index)?.kind.clone();
        if let TypeKind::Union(indices) = index_kind {
            let values = indices
                .into_iter()
                .map(|index| self.lookup_indexed_type(object, index))
                .collect::<Option<Vec<_>>>()?;
            return Some(self.result.types.union(values));
        }
        match self.result.types.get(object)?.kind.clone() {
            TypeKind::Any => Some(self.result.types.any()),
            TypeKind::Array(element) if self.is_number_like(index) => Some(element),
            TypeKind::Tuple(elements) => match index_kind {
                TypeKind::NumberLiteral(value) => value
                    .parse::<usize>()
                    .ok()
                    .and_then(|position| elements.get(position).copied()),
                TypeKind::Number => Some(self.result.types.union(elements)),
                TypeKind::StringLiteral(name) => self.lookup_property_type(object, &name),
                _ => None,
            },
            TypeKind::Object(object_type) => match index_kind {
                TypeKind::StringLiteral(name) | TypeKind::NumberLiteral(name) => {
                    object_type.properties.get(&name).copied()
                }
                _ => None,
            },
            TypeKind::String | TypeKind::StringLiteral(_) if self.is_number_like(index) => {
                Some(self.result.types.string())
            }
            TypeKind::Union(members) => {
                let values = members
                    .into_iter()
                    .map(|member| self.lookup_indexed_type(member, index))
                    .collect::<Option<Vec<_>>>()?;
                Some(self.result.types.union(values))
            }
            TypeKind::Intersection(members) => {
                let values = members
                    .into_iter()
                    .filter_map(|member| self.lookup_indexed_type(member, index))
                    .collect::<Vec<_>>();
                (!values.is_empty()).then(|| self.result.types.intersection(values))
            }
            _ => None,
        }
    }

    fn call_expression_type(
        &mut self,
        node: NodeId,
        callee: TypeId,
        arguments: &[NodeId],
        construct: bool,
    ) -> TypeId {
        let callee_kind = self.result.types.get(callee).unwrap().kind.clone();
        if construct && let TypeKind::Object(_) = callee_kind {
            for argument in arguments {
                self.type_of_expression(*argument);
            }
            return callee;
        }
        if matches!(callee_kind, TypeKind::Any) {
            for argument in arguments {
                self.type_of_expression(*argument);
            }
            return self.result.types.any();
        }
        let TypeKind::Function(signature) = callee_kind else {
            self.error(
                node,
                if construct { 2351 } else { 2349 },
                std::iter::empty(),
            );
            return self.result.types.any();
        };
        if signature.parameters.len() != arguments.len() {
            self.error(
                node,
                2554,
                [
                    signature.parameters.len().to_string(),
                    arguments.len().to_string(),
                ],
            );
        }
        let mut inference = HashMap::new();
        for (argument, parameter) in arguments.iter().zip(&signature.parameters) {
            let actual = self.type_of_expression_context(*argument, Some(*parameter));
            self.infer_type_parameters(*parameter, actual, &mut inference);
            let expected = self.substitute_type(*parameter, &inference);
            if !self.is_assignable(actual, expected) {
                self.error(
                    *argument,
                    2345,
                    [
                        self.result.types.display(actual),
                        self.result.types.display(expected),
                    ],
                );
            }
        }
        self.substitute_type(signature.return_type, &inference)
    }

    fn infer_type_parameters(
        &mut self,
        parameter: TypeId,
        actual: TypeId,
        inference: &mut HashMap<TypeId, TypeId>,
    ) {
        match self.result.types.get(parameter).unwrap().kind.clone() {
            TypeKind::TypeParameter { .. } => {
                let actual = self.widen_literal(actual);
                inference
                    .entry(parameter)
                    .and_modify(|current| *current = self.result.types.union([*current, actual]))
                    .or_insert(actual);
            }
            TypeKind::Array(parameter_element) => {
                if let TypeKind::Array(actual_element) =
                    self.result.types.get(actual).unwrap().kind.clone()
                {
                    self.infer_type_parameters(parameter_element, actual_element, inference);
                }
            }
            _ => {}
        }
    }

    fn substitute_type(&mut self, type_id: TypeId, inference: &HashMap<TypeId, TypeId>) -> TypeId {
        if let Some(inferred) = inference.get(&type_id) {
            return *inferred;
        }
        match self.result.types.get(type_id).unwrap().kind.clone() {
            TypeKind::Array(element) => {
                let element = self.substitute_type(element, inference);
                self.result.types.alloc(TypeKind::Array(element))
            }
            TypeKind::Union(members) => {
                let substituted = members
                    .into_iter()
                    .map(|member| self.substitute_type(member, inference))
                    .collect::<Vec<_>>();
                self.result.types.union(substituted)
            }
            _ => type_id,
        }
    }

    fn check_binary(
        &mut self,
        node: NodeId,
        operator: SyntaxKind,
        left: TypeId,
        right: TypeId,
    ) -> TypeId {
        match operator {
            SyntaxKind::PlusToken => {
                if self.is_string_like(left) || self.is_string_like(right) {
                    self.result.types.string()
                } else {
                    self.numeric_binary(node, operator, left, right)
                }
            }
            SyntaxKind::MinusToken
            | SyntaxKind::AsteriskToken
            | SyntaxKind::AsteriskAsteriskToken
            | SyntaxKind::SlashToken
            | SyntaxKind::PercentToken => self.numeric_binary(node, operator, left, right),
            SyntaxKind::LessThanToken
            | SyntaxKind::LessThanEqualsToken
            | SyntaxKind::GreaterThanToken
            | SyntaxKind::GreaterThanEqualsToken => {
                if !((self.is_number_like(left) && self.is_number_like(right))
                    || (self.is_string_like(left) && self.is_string_like(right)))
                {
                    self.operator_error(node, operator, left, right);
                }
                self.result.types.boolean()
            }
            SyntaxKind::EqualsEqualsToken
            | SyntaxKind::EqualsEqualsEqualsToken
            | SyntaxKind::ExclamationEqualsToken
            | SyntaxKind::ExclamationEqualsEqualsToken => self.result.types.boolean(),
            SyntaxKind::AmpersandAmpersandToken
            | SyntaxKind::BarBarToken
            | SyntaxKind::QuestionQuestionToken => self.result.types.union([left, right]),
            SyntaxKind::EqualsToken => {
                if !self.is_assignable(right, left) {
                    self.assignability_error(node, right, left);
                }
                left
            }
            _ => {
                self.operator_error(node, operator, left, right);
                self.result.types.any()
            }
        }
    }

    fn numeric_binary(
        &mut self,
        node: NodeId,
        operator: SyntaxKind,
        left: TypeId,
        right: TypeId,
    ) -> TypeId {
        if self.is_number_like(left) && self.is_number_like(right) {
            self.result.types.number()
        } else if self.is_bigint_like(left) && self.is_bigint_like(right) {
            self.result.types.bigint()
        } else {
            self.operator_error(node, operator, left, right);
            self.result.types.any()
        }
    }

    fn function_type(&mut self, data: &ts_ast::FunctionDeclarationData) -> TypeId {
        self.signature_type(
            &data.parameters.nodes,
            data.type_,
            data.type_parameters.as_ref(),
        )
    }

    fn signature_type(
        &mut self,
        parameters: &[NodeId],
        return_annotation: Option<NodeId>,
        type_parameters: Option<&ts_ast::NodeList>,
    ) -> TypeId {
        let mut type_parameter_scope = HashMap::new();
        if let Some(type_parameters) = type_parameters {
            for type_parameter in &type_parameters.nodes {
                let Some(NodeData::TypeParameterDeclaration(data)) =
                    self.arena.get(*type_parameter).map(|node| &node.data)
                else {
                    continue;
                };
                let Some(name) = self.property_name(data.name) else {
                    continue;
                };
                let constraint = data
                    .constraint
                    .map(|constraint| self.type_from_type_node(constraint));
                let semantic_type = self.result.types.alloc(TypeKind::TypeParameter {
                    name: name.clone(),
                    constraint,
                });
                type_parameter_scope.insert(name, semantic_type);
            }
        }
        self.type_parameter_scopes.push(type_parameter_scope);
        let mut parameter_types = Vec::with_capacity(parameters.len());
        for parameter in parameters {
            let parameter_type = match self.arena.get(*parameter).map(|node| &node.data) {
                Some(NodeData::ParameterDeclaration(data)) => {
                    let base = match data.type_ {
                        Some(node) => self.type_from_type_node(node),
                        None => self.result.types.any(),
                    };
                    if data.question_token.is_some() {
                        let undefined = self.result.types.undefined();
                        self.result.types.union([base, undefined])
                    } else {
                        base
                    }
                }
                _ => self.result.types.any(),
            };
            parameter_types.push(parameter_type);
        }
        let return_type = match return_annotation {
            Some(node) => self.type_from_type_node(node),
            None => self.result.types.any(),
        };
        self.type_parameter_scopes.pop();
        self.result.types.alloc(TypeKind::Function(FunctionType {
            parameters: parameter_types,
            return_type,
        }))
    }

    #[allow(clippy::too_many_lines)]
    fn type_from_type_node(&mut self, node_id: NodeId) -> TypeId {
        let Some(node) = self.arena.get(node_id) else {
            return self.result.types.unknown();
        };
        match &node.data {
            NodeData::KeywordTypeNode(_) => match node.kind {
                SyntaxKind::AnyKeyword => self.result.types.any(),
                SyntaxKind::NeverKeyword => self.result.types.never(),
                SyntaxKind::VoidKeyword => self.result.types.void(),
                SyntaxKind::UndefinedKeyword => self.result.types.undefined(),
                SyntaxKind::NullKeyword => self.result.types.null(),
                SyntaxKind::BooleanKeyword => self.result.types.boolean(),
                SyntaxKind::NumberKeyword => self.result.types.number(),
                SyntaxKind::StringKeyword => self.result.types.string(),
                SyntaxKind::BigIntKeyword => self.result.types.bigint(),
                _ => self.result.types.unknown(),
            },
            NodeData::LiteralTypeNode(data) => self.type_of_expression(data.literal),
            NodeData::ParenthesizedTypeNode(data) => self.type_from_type_node(data.type_),
            NodeData::OptionalTypeNode(data) => {
                let type_ = self.type_from_type_node(data.type_);
                let undefined = self.result.types.undefined();
                self.result.types.union([type_, undefined])
            }
            NodeData::RestTypeNode(data) => self.type_from_type_node(data.type_),
            NodeData::NamedTupleMember(data) => {
                let type_ = self.type_from_type_node(data.type_);
                if data.question_token.is_some() {
                    let undefined = self.result.types.undefined();
                    self.result.types.union([type_, undefined])
                } else {
                    type_
                }
            }
            NodeData::ArrayTypeNode(data) => {
                let element = self.type_from_type_node(data.element_type);
                self.result.types.alloc(TypeKind::Array(element))
            }
            NodeData::TypeReferenceNode(data) => {
                let Some(name) = self.property_name(data.type_name) else {
                    return self.result.types.unknown();
                };
                for scope in self.type_parameter_scopes.iter().rev() {
                    if let Some(type_id) = scope.get(&name) {
                        return *type_id;
                    }
                }
                if name == "Array"
                    && let Some(argument) = data
                        .type_arguments
                        .as_ref()
                        .and_then(|arguments| arguments.nodes.first())
                {
                    let element = self.type_from_type_node(*argument);
                    return self.result.types.alloc(TypeKind::Array(element));
                }
                let arguments = data
                    .type_arguments
                    .as_ref()
                    .map(|arguments| {
                        arguments
                            .nodes
                            .iter()
                            .map(|argument| self.type_from_type_node(*argument))
                            .collect::<Vec<_>>()
                    })
                    .unwrap_or_default();
                let Some(symbol) = self.resolve_identifier(data.type_name, &name) else {
                    if let Some(descriptor) = self.external_names.get(&name).cloned() {
                        return self.import_alias(&descriptor, &arguments);
                    }
                    return self.result.types.unknown();
                };
                if let Some(descriptor) = self.external_aliases.get(&symbol).cloned() {
                    return self.import_alias(&descriptor, &arguments);
                }
                self.instantiate_alias(symbol, &arguments)
                    .unwrap_or_else(|| {
                        self.result
                            .symbol_types
                            .get(&symbol)
                            .copied()
                            .unwrap_or_else(|| self.result.types.unknown())
                    })
            }
            NodeData::UnionTypeNode(data) => {
                let members = data
                    .types
                    .nodes
                    .iter()
                    .map(|node| self.type_from_type_node(*node))
                    .collect::<Vec<_>>();
                self.result.types.union(members)
            }
            NodeData::IntersectionTypeNode(data) => {
                let members = data
                    .types
                    .nodes
                    .iter()
                    .map(|node| self.type_from_type_node(*node))
                    .collect::<Vec<_>>();
                self.result.types.intersection(members)
            }
            NodeData::TupleTypeNode(data) => {
                let elements = data
                    .elements
                    .nodes
                    .iter()
                    .map(|node| self.type_from_type_node(*node))
                    .collect::<Vec<_>>();
                self.result.types.alloc(TypeKind::Tuple(elements))
            }
            NodeData::TypeLiteralNode(data) => self.object_type_from_members(&data.members.nodes),
            NodeData::IndexedAccessTypeNode(data) => {
                let object = self.type_from_type_node(data.object_type);
                let index = self.type_from_type_node(data.index_type);
                self.indexed_access_type(node_id, object, index)
            }
            _ => self.result.types.unknown(),
        }
    }

    fn instantiate_alias(&mut self, symbol: SymbolId, arguments: &[TypeId]) -> Option<TypeId> {
        if self.alias_stack.contains(&symbol) {
            return Some(self.result.types.any());
        }
        let declaration = self
            .bindings
            .symbols
            .get(symbol)?
            .declarations
            .iter()
            .find_map(|declaration| match &self.arena.get(*declaration)?.data {
                NodeData::TypeAliasDeclaration(data) => Some(data.as_ref()),
                _ => None,
            })?;
        self.alias_stack.push(symbol);
        let result = self.type_alias_type(declaration, arguments);
        self.alias_stack.pop();
        Some(result)
    }

    fn type_alias_type(
        &mut self,
        data: &ts_ast::TypeAliasDeclarationData,
        arguments: &[TypeId],
    ) -> TypeId {
        self.type_parameter_scopes.push(HashMap::new());
        if let Some(parameters) = &data.type_parameters {
            for (index, parameter) in parameters.nodes.iter().enumerate() {
                let Some(NodeData::TypeParameterDeclaration(parameter)) =
                    self.arena.get(*parameter).map(|node| &node.data)
                else {
                    continue;
                };
                let Some(name) = self.property_name(parameter.name) else {
                    continue;
                };
                let type_id = arguments.get(index).copied().unwrap_or_else(|| {
                    parameter
                        .default_type
                        .map(|default| self.type_from_type_node(default))
                        .or_else(|| {
                            parameter
                                .constraint
                                .map(|constraint| self.type_from_type_node(constraint))
                        })
                        .unwrap_or_else(|| self.result.types.any())
                });
                self.type_parameter_scopes
                    .last_mut()
                    .unwrap()
                    .insert(name, type_id);
            }
        }
        let result = self.type_from_type_node(data.type_);
        self.type_parameter_scopes.pop();
        result
    }

    fn is_assignable(&self, source: TypeId, target: TypeId) -> bool {
        if source == target || source == self.result.types.never() {
            return true;
        }
        let source_kind = &self.result.types.get(source).unwrap().kind;
        let target_kind = &self.result.types.get(target).unwrap().kind;
        if matches!(source_kind, TypeKind::Any)
            || matches!(target_kind, TypeKind::Any | TypeKind::Unknown)
        {
            return true;
        }
        if let TypeKind::Object(target_object) = target_kind {
            return target_object.properties.iter().all(|(name, target_type)| {
                self.property_types(source, name)
                    .into_iter()
                    .any(|source_type| self.is_assignable(source_type, *target_type))
            });
        }
        match (source_kind, target_kind) {
            (TypeKind::NumberLiteral(_), TypeKind::Number)
            | (TypeKind::StringLiteral(_), TypeKind::String)
            | (TypeKind::BigIntLiteral(_), TypeKind::BigInt)
            | (TypeKind::BooleanLiteral(_), TypeKind::Boolean)
            | (TypeKind::Undefined, TypeKind::Void) => true,
            (TypeKind::Union(sources), _) => sources
                .iter()
                .all(|source| self.is_assignable(*source, target)),
            (_, TypeKind::Union(targets)) => targets
                .iter()
                .any(|target| self.is_assignable(source, *target)),
            (TypeKind::Intersection(sources), _) => sources
                .iter()
                .any(|source| self.is_assignable(*source, target)),
            (_, TypeKind::Intersection(targets)) => targets
                .iter()
                .all(|target| self.is_assignable(source, *target)),
            (TypeKind::Array(source), TypeKind::Array(target)) => {
                self.is_assignable(*source, *target)
            }
            (TypeKind::Tuple(sources), TypeKind::Tuple(targets)) => {
                sources.len() == targets.len()
                    && sources
                        .iter()
                        .zip(targets)
                        .all(|(source, target)| self.is_assignable(*source, *target))
            }
            (TypeKind::Tuple(sources), TypeKind::Array(target)) => sources
                .iter()
                .all(|source| self.is_assignable(*source, *target)),
            (TypeKind::TypeParameter { constraint, .. }, _) => {
                constraint.is_none_or(|constraint| self.is_assignable(constraint, target))
            }
            (_, TypeKind::TypeParameter { constraint, .. }) => {
                constraint.is_none_or(|constraint| self.is_assignable(source, constraint))
            }
            (TypeKind::Function(source), TypeKind::Function(target)) => {
                source.parameters.len() == target.parameters.len()
                    && source
                        .parameters
                        .iter()
                        .zip(&target.parameters)
                        .all(|(source, target)| self.is_assignable(*target, *source))
                    && self.is_assignable(source.return_type, target.return_type)
            }
            _ => false,
        }
    }

    fn property_types(&self, type_id: TypeId, name: &str) -> Vec<TypeId> {
        let Some(type_) = self.result.types.get(type_id) else {
            return Vec::new();
        };
        match &type_.kind {
            TypeKind::Object(object) => object.properties.get(name).copied().into_iter().collect(),
            TypeKind::Intersection(members) => members
                .iter()
                .flat_map(|member| self.property_types(*member, name))
                .collect(),
            _ => Vec::new(),
        }
    }

    fn import_type(&mut self, descriptor: &TypeDescriptor) -> TypeId {
        match descriptor {
            TypeDescriptor::Any | TypeDescriptor::TypeParameter(_) => self.result.types.any(),
            TypeDescriptor::Unknown => self.result.types.unknown(),
            TypeDescriptor::Never => self.result.types.never(),
            TypeDescriptor::Void => self.result.types.void(),
            TypeDescriptor::Undefined => self.result.types.undefined(),
            TypeDescriptor::Null => self.result.types.null(),
            TypeDescriptor::Boolean => self.result.types.boolean(),
            TypeDescriptor::Number => self.result.types.number(),
            TypeDescriptor::String => self.result.types.string(),
            TypeDescriptor::BigInt => self.result.types.bigint(),
            TypeDescriptor::BooleanLiteral(value) => {
                self.result.types.alloc(TypeKind::BooleanLiteral(*value))
            }
            TypeDescriptor::NumberLiteral(value) => self
                .result
                .types
                .alloc(TypeKind::NumberLiteral(value.clone())),
            TypeDescriptor::StringLiteral(value) => self
                .result
                .types
                .alloc(TypeKind::StringLiteral(value.clone())),
            TypeDescriptor::BigIntLiteral(value) => self
                .result
                .types
                .alloc(TypeKind::BigIntLiteral(value.clone())),
            TypeDescriptor::Alias { .. } => self.import_alias(descriptor, &[]),
            TypeDescriptor::Array(element) => {
                let element = self.import_type(element);
                self.result.types.alloc(TypeKind::Array(element))
            }
            TypeDescriptor::Tuple(elements) => {
                let elements = elements
                    .iter()
                    .map(|element| self.import_type(element))
                    .collect();
                self.result.types.alloc(TypeKind::Tuple(elements))
            }
            TypeDescriptor::Union(members) => {
                let members = members
                    .iter()
                    .map(|member| self.import_type(member))
                    .collect::<Vec<_>>();
                self.result.types.union(members)
            }
            TypeDescriptor::Intersection(members) => {
                let members = members
                    .iter()
                    .map(|member| self.import_type(member))
                    .collect::<Vec<_>>();
                self.result.types.intersection(members)
            }
            TypeDescriptor::Object(properties) => {
                let properties = properties
                    .iter()
                    .map(|(name, property)| (name.clone(), self.import_type(property)))
                    .collect();
                self.result
                    .types
                    .alloc(TypeKind::Object(ObjectType { properties }))
            }
            TypeDescriptor::Function {
                parameters,
                return_type,
            } => {
                let parameters = parameters
                    .iter()
                    .map(|parameter| self.import_type(parameter))
                    .collect();
                let return_type = self.import_type(return_type);
                self.result.types.alloc(TypeKind::Function(FunctionType {
                    parameters,
                    return_type,
                }))
            }
        }
    }

    fn import_alias(&mut self, descriptor: &TypeDescriptor, arguments: &[TypeId]) -> TypeId {
        let TypeDescriptor::Alias { parameters, body } = descriptor else {
            return self.import_type(descriptor);
        };
        let substitutions = parameters
            .iter()
            .zip(arguments)
            .map(|(name, argument)| (name.clone(), describe_type(&self.result.types, *argument)))
            .collect::<BTreeMap<_, _>>();
        let instantiated = substitute_descriptor(body, &substitutions);
        self.import_type(&instantiated)
    }

    fn widen_literal(&mut self, type_id: TypeId) -> TypeId {
        match self
            .result
            .types
            .get(type_id)
            .map(|value| value.kind.clone())
        {
            Some(TypeKind::NumberLiteral(_)) => self.result.types.number(),
            Some(TypeKind::StringLiteral(_)) => self.result.types.string(),
            Some(TypeKind::BigIntLiteral(_)) => self.result.types.bigint(),
            Some(TypeKind::BooleanLiteral(_)) => self.result.types.boolean(),
            Some(TypeKind::Array(element)) => {
                let element = self.widen_literal(element);
                self.result.types.alloc(TypeKind::Array(element))
            }
            Some(TypeKind::Tuple(elements)) => {
                let elements = elements
                    .into_iter()
                    .map(|element| self.widen_literal(element))
                    .collect();
                self.result.types.alloc(TypeKind::Tuple(elements))
            }
            Some(TypeKind::Union(members)) => {
                let members = members
                    .into_iter()
                    .map(|member| self.widen_literal(member))
                    .collect::<Vec<_>>();
                self.result.types.union(members)
            }
            Some(TypeKind::Intersection(members)) => {
                let members = members
                    .into_iter()
                    .map(|member| self.widen_literal(member))
                    .collect::<Vec<_>>();
                self.result.types.intersection(members)
            }
            Some(TypeKind::Object(object)) => {
                let properties = object
                    .properties
                    .into_iter()
                    .map(|(name, property)| (name, self.widen_literal(property)))
                    .collect();
                self.result
                    .types
                    .alloc(TypeKind::Object(ObjectType { properties }))
            }
            _ => type_id,
        }
    }

    fn is_const_declaration(&self, declaration: NodeId) -> bool {
        self.arena
            .get(declaration)
            .and_then(|node| node.parent)
            .and_then(|parent| self.arena.get(parent))
            .is_some_and(|list| list.flags.0 & (1 << 1) != 0)
    }

    fn is_number_like(&self, type_id: TypeId) -> bool {
        matches!(
            self.result.types.get(type_id).map(|value| &value.kind),
            Some(TypeKind::Number | TypeKind::NumberLiteral(_))
        )
    }

    fn is_string_like(&self, type_id: TypeId) -> bool {
        matches!(
            self.result.types.get(type_id).map(|value| &value.kind),
            Some(TypeKind::String | TypeKind::StringLiteral(_))
        )
    }

    fn is_bigint_like(&self, type_id: TypeId) -> bool {
        matches!(
            self.result.types.get(type_id).map(|value| &value.kind),
            Some(TypeKind::BigInt | TypeKind::BigIntLiteral(_))
        )
    }

    fn resolve_identifier(&self, node: NodeId, name: &str) -> Option<SymbolId> {
        if let Some(symbol) = self.bindings.node_symbols.get(&node) {
            return Some(*symbol);
        }
        if let Some(container) = self.bindings.containers.get(&node)
            && let Some(mut scope) =
                self.bindings
                    .node_scopes
                    .get(container)
                    .copied()
                    .or_else(|| {
                        self.bindings
                            .scopes
                            .iter()
                            .find(|scope| scope.owner == *container)
                            .map(|scope| scope.id)
                    })
        {
            loop {
                let current = self.bindings.scope(scope)?;
                if let Some(symbol) = current.symbols.get(name) {
                    return Some(symbol);
                }
                let Some(parent) = current.parent else {
                    break;
                };
                scope = parent;
            }
        }
        self.bindings
            .scopes
            .iter()
            .find_map(|scope| scope.symbols.get(name))
    }

    fn property_name(&self, node: NodeId) -> Option<String> {
        match &self.arena.get(node)?.data {
            NodeData::Identifier(data) => Some(data.text.clone()),
            NodeData::StringLiteral(data) => Some(data.text.clone()),
            NodeData::NumericLiteral(data) => Some(data.text.clone()),
            _ => None,
        }
    }

    fn assignability_error(&mut self, node: NodeId, actual: TypeId, expected: TypeId) {
        self.error(
            node,
            2322,
            [
                self.result.types.display(actual),
                self.result.types.display(expected),
            ],
        );
    }

    fn operator_error(&mut self, node: NodeId, operator: SyntaxKind, left: TypeId, right: TypeId) {
        self.error(
            node,
            2365,
            [
                operator_text(operator).to_owned(),
                self.result.types.display(left),
                self.result.types.display(right),
            ],
        );
    }

    fn error(&mut self, node: NodeId, code: u32, arguments: impl IntoIterator<Item = String>) {
        let message = message_by_code(code).expect("checker diagnostic is in catalog");
        self.result.diagnostics.push(CheckDiagnostic {
            node,
            diagnostic: Diagnostic::with_arguments(message, arguments),
        });
    }
}

fn describe_alias(
    source: &ProgramSource<'_>,
    alias: &ts_ast::TypeAliasDeclarationData,
) -> TypeDescriptor {
    let mut checker = Checker::new(source.arena, source.bindings);
    checker.seed_symbol_types();
    let mut parameter_scope = HashMap::new();
    let mut parameters = Vec::new();
    if let Some(type_parameters) = &alias.type_parameters {
        for parameter in &type_parameters.nodes {
            let Some(NodeData::TypeParameterDeclaration(data)) =
                source.arena.get(*parameter).map(|node| &node.data)
            else {
                continue;
            };
            let Some(name) = checker.property_name(data.name) else {
                continue;
            };
            let type_id = checker.result.types.alloc(TypeKind::TypeParameter {
                name: name.clone(),
                constraint: None,
            });
            parameter_scope.insert(name.clone(), type_id);
            parameters.push(name);
        }
    }
    checker.type_parameter_scopes.push(parameter_scope);
    let body = checker.type_from_type_node(alias.type_);
    checker.type_parameter_scopes.pop();
    TypeDescriptor::Alias {
        parameters,
        body: Box::new(describe_type(&checker.result.types, body)),
    }
}

fn describe_type(types: &TypeArena, type_id: TypeId) -> TypeDescriptor {
    match &types
        .get(type_id)
        .expect("type ID originates from arena")
        .kind
    {
        TypeKind::Any => TypeDescriptor::Any,
        TypeKind::Unknown => TypeDescriptor::Unknown,
        TypeKind::Never => TypeDescriptor::Never,
        TypeKind::Void => TypeDescriptor::Void,
        TypeKind::Undefined => TypeDescriptor::Undefined,
        TypeKind::Null => TypeDescriptor::Null,
        TypeKind::Boolean => TypeDescriptor::Boolean,
        TypeKind::Number => TypeDescriptor::Number,
        TypeKind::String => TypeDescriptor::String,
        TypeKind::BigInt => TypeDescriptor::BigInt,
        TypeKind::BooleanLiteral(value) => TypeDescriptor::BooleanLiteral(*value),
        TypeKind::NumberLiteral(value) => TypeDescriptor::NumberLiteral(value.clone()),
        TypeKind::StringLiteral(value) => TypeDescriptor::StringLiteral(value.clone()),
        TypeKind::BigIntLiteral(value) => TypeDescriptor::BigIntLiteral(value.clone()),
        TypeKind::TypeParameter { name, .. } => TypeDescriptor::TypeParameter(name.clone()),
        TypeKind::Array(element) => TypeDescriptor::Array(Box::new(describe_type(types, *element))),
        TypeKind::Tuple(elements) => TypeDescriptor::Tuple(
            elements
                .iter()
                .map(|element| describe_type(types, *element))
                .collect(),
        ),
        TypeKind::Union(members) => TypeDescriptor::Union(
            members
                .iter()
                .map(|member| describe_type(types, *member))
                .collect(),
        ),
        TypeKind::Intersection(members) => TypeDescriptor::Intersection(
            members
                .iter()
                .map(|member| describe_type(types, *member))
                .collect(),
        ),
        TypeKind::Object(object) => TypeDescriptor::Object(
            object
                .properties
                .iter()
                .map(|(name, property)| (name.clone(), describe_type(types, *property)))
                .collect(),
        ),
        TypeKind::Function(function) => TypeDescriptor::Function {
            parameters: function
                .parameters
                .iter()
                .map(|parameter| describe_type(types, *parameter))
                .collect(),
            return_type: Box::new(describe_type(types, function.return_type)),
        },
    }
}

fn substitute_descriptor(
    descriptor: &TypeDescriptor,
    substitutions: &BTreeMap<String, TypeDescriptor>,
) -> TypeDescriptor {
    match descriptor {
        TypeDescriptor::TypeParameter(name) => substitutions
            .get(name)
            .cloned()
            .unwrap_or(TypeDescriptor::Any),
        TypeDescriptor::Array(element) => {
            TypeDescriptor::Array(Box::new(substitute_descriptor(element, substitutions)))
        }
        TypeDescriptor::Tuple(elements) => TypeDescriptor::Tuple(
            elements
                .iter()
                .map(|element| substitute_descriptor(element, substitutions))
                .collect(),
        ),
        TypeDescriptor::Union(members) => TypeDescriptor::Union(
            members
                .iter()
                .map(|member| substitute_descriptor(member, substitutions))
                .collect(),
        ),
        TypeDescriptor::Intersection(members) => TypeDescriptor::Intersection(
            members
                .iter()
                .map(|member| substitute_descriptor(member, substitutions))
                .collect(),
        ),
        TypeDescriptor::Object(properties) => TypeDescriptor::Object(
            properties
                .iter()
                .map(|(name, property)| {
                    (name.clone(), substitute_descriptor(property, substitutions))
                })
                .collect(),
        ),
        TypeDescriptor::Function {
            parameters,
            return_type,
        } => TypeDescriptor::Function {
            parameters: parameters
                .iter()
                .map(|parameter| substitute_descriptor(parameter, substitutions))
                .collect(),
            return_type: Box::new(substitute_descriptor(return_type, substitutions)),
        },
        TypeDescriptor::Alias { parameters, body } => TypeDescriptor::Alias {
            parameters: parameters.clone(),
            body: Box::new(substitute_descriptor(body, substitutions)),
        },
        primitive => primitive.clone(),
    }
}

fn is_external_module(source: &ProgramSource<'_>) -> bool {
    if !source.bindings.exports.is_empty() {
        return true;
    }
    let Some(NodeData::SourceFile(file)) =
        source.arena.get(source.source_file).map(|node| &node.data)
    else {
        return false;
    };
    file.statements.nodes.iter().any(|statement| {
        matches!(
            source.arena.get(*statement).map(|node| &node.data),
            Some(NodeData::ImportDeclaration(_) | NodeData::ImportEqualsDeclaration(_))
        )
    })
}

fn global_declarations_merge(
    existing: ts_binder::SymbolFlags,
    new: ts_binder::SymbolFlags,
) -> bool {
    (existing == ts_binder::SymbolFlags::INTERFACE && new == ts_binder::SymbolFlags::INTERFACE)
        || (existing == ts_binder::SymbolFlags::FUNCTION && new == ts_binder::SymbolFlags::FUNCTION)
        || (existing == ts_binder::SymbolFlags::FUNCTION_SCOPED_VARIABLE
            && new == ts_binder::SymbolFlags::FUNCTION_SCOPED_VARIABLE)
}

fn string_literal_text(arena: &NodeArena, node: NodeId) -> Option<&str> {
    match &arena.get(node)?.data {
        NodeData::StringLiteral(literal) => Some(&literal.text),
        _ => None,
    }
}

fn identifier_text(arena: &NodeArena, node: NodeId) -> Option<&str> {
    match &arena.get(node)?.data {
        NodeData::Identifier(identifier) => Some(&identifier.text),
        _ => None,
    }
}

#[derive(Clone, Copy)]
enum NarrowingComparison {
    Null,
    Undefined,
    String,
    Number,
    BigInt,
    Boolean,
    Function,
    Object,
}

impl NarrowingComparison {
    fn matches(self, kind: &TypeKind) -> bool {
        match self {
            Self::Null => matches!(kind, TypeKind::Null),
            Self::Undefined => matches!(kind, TypeKind::Undefined),
            Self::String => matches!(kind, TypeKind::String | TypeKind::StringLiteral(_)),
            Self::Number => matches!(kind, TypeKind::Number | TypeKind::NumberLiteral(_)),
            Self::BigInt => matches!(kind, TypeKind::BigInt | TypeKind::BigIntLiteral(_)),
            Self::Boolean => matches!(kind, TypeKind::Boolean | TypeKind::BooleanLiteral(_)),
            Self::Function => matches!(kind, TypeKind::Function(_)),
            Self::Object => matches!(
                kind,
                TypeKind::Object(_) | TypeKind::Array(_) | TypeKind::Null
            ),
        }
    }
}

fn operator_text(operator: SyntaxKind) -> &'static str {
    match operator {
        SyntaxKind::PlusToken => "+",
        SyntaxKind::MinusToken => "-",
        SyntaxKind::AsteriskToken => "*",
        SyntaxKind::AsteriskAsteriskToken => "**",
        SyntaxKind::SlashToken => "/",
        SyntaxKind::PercentToken => "%",
        SyntaxKind::LessThanToken => "<",
        SyntaxKind::LessThanEqualsToken => "<=",
        SyntaxKind::GreaterThanToken => ">",
        SyntaxKind::GreaterThanEqualsToken => ">=",
        SyntaxKind::EqualsEqualsToken => "==",
        SyntaxKind::EqualsEqualsEqualsToken => "===",
        SyntaxKind::ExclamationEqualsToken => "!=",
        SyntaxKind::ExclamationEqualsEqualsToken => "!==",
        SyntaxKind::AmpersandAmpersandToken => "&&",
        SyntaxKind::BarBarToken => "||",
        SyntaxKind::QuestionQuestionToken => "??",
        SyntaxKind::EqualsToken => "=",
        _ => "<operator>",
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use ts_ast::{
        ArrayLiteralExpressionData, BlockData, ElementAccessExpressionData,
        ExpressionStatementData, FunctionDeclarationData, IdentifierData, IfStatementData,
        IndexedAccessTypeNodeData, KeywordExpressionData, KeywordTypeNodeData, LiteralTypeNodeData,
        Node, NodeArena, NodeData, NodeFlags, NodeId, NodeList, NumericLiteralData,
        PropertyAccessExpressionData, ReturnStatementData, SourceFileData, StringLiteralData,
        SymbolTable as AstSymbolTable, SyntaxKind, TokenData, TokenFlags, TupleTypeNodeData,
        TypeOfExpressionData, UnionTypeNodeData, VariableDeclarationData,
        VariableDeclarationListData, VariableStatementData,
    };
    use ts_binder::{BindResult, bind_source_file};
    use ts_core::TextRange;
    use ts_parser::parse_source_file;

    use super::{Checker, ObjectType, TypeKind, check_source_file};

    struct Builder {
        arena: NodeArena,
    }

    impl Builder {
        fn new() -> Self {
            Self {
                arena: NodeArena::new(),
            }
        }

        fn alloc(&mut self, kind: SyntaxKind, data: NodeData, children: &[NodeId]) -> NodeId {
            let id = self.arena.alloc(Node {
                kind,
                flags: NodeFlags::default(),
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
                NodeData::Identifier(Box::new(IdentifierData {
                    flow_node: None,
                    text: text.into(),
                })),
                &[],
            )
        }

        fn keyword_type(&mut self, kind: SyntaxKind) -> NodeId {
            self.alloc(
                kind,
                NodeData::KeywordTypeNode(Box::new(KeywordTypeNodeData)),
                &[],
            )
        }

        fn number(&mut self, text: &str) -> NodeId {
            self.alloc(
                SyntaxKind::NumericLiteral,
                NodeData::NumericLiteral(Box::new(NumericLiteralData {
                    text: text.into(),
                    token_flags: TokenFlags::default(),
                })),
                &[],
            )
        }

        fn null(&mut self) -> NodeId {
            self.alloc(
                SyntaxKind::NullKeyword,
                NodeData::KeywordExpression(Box::new(KeywordExpressionData { flow_node: None })),
                &[],
            )
        }

        fn union_type(&mut self, types: &[NodeId]) -> NodeId {
            self.alloc(
                SyntaxKind::UnionType,
                NodeData::UnionTypeNode(Box::new(UnionTypeNodeData {
                    types: NodeList {
                        range: TextRange::default(),
                        nodes: types.to_vec(),
                        has_trailing_comma: false,
                    },
                })),
                types,
            )
        }

        fn property_access(&mut self, expression: NodeId, name: &str) -> NodeId {
            let name = self.identifier(name);
            self.alloc(
                SyntaxKind::PropertyAccessExpression,
                NodeData::PropertyAccessExpression(Box::new(PropertyAccessExpressionData {
                    expression,
                    flow_node: None,
                    question_dot_token: None,
                    facts: 0,
                    name,
                })),
                &[expression, name],
            )
        }

        fn type_of(&mut self, expression: NodeId) -> NodeId {
            self.alloc(
                SyntaxKind::TypeOfExpression,
                NodeData::TypeOfExpression(Box::new(TypeOfExpressionData { expression })),
                &[expression],
            )
        }

        fn if_statement(
            &mut self,
            expression: NodeId,
            then_statement: NodeId,
            else_statement: Option<NodeId>,
        ) -> NodeId {
            let mut children = vec![expression, then_statement];
            children.extend(else_statement);
            self.alloc(
                SyntaxKind::IfStatement,
                NodeData::IfStatement(Box::new(IfStatementData {
                    expression,
                    then_statement,
                    else_statement,
                    flow_node: None,
                    facts: 0,
                })),
                &children,
            )
        }

        fn string(&mut self, text: &str) -> NodeId {
            self.alloc(
                SyntaxKind::StringLiteral,
                NodeData::StringLiteral(Box::new(StringLiteralData {
                    text: text.into(),
                    token_flags: TokenFlags::default(),
                })),
                &[],
            )
        }

        fn array(&mut self, elements: &[NodeId]) -> NodeId {
            self.alloc(
                SyntaxKind::ArrayLiteralExpression,
                NodeData::ArrayLiteralExpression(Box::new(ArrayLiteralExpressionData {
                    elements: NodeList {
                        range: TextRange::default(),
                        nodes: elements.to_vec(),
                        has_trailing_comma: false,
                    },
                    multi_line: false,
                    facts: 0,
                })),
                elements,
            )
        }

        fn tuple_type(&mut self, elements: &[NodeId]) -> NodeId {
            self.alloc(
                SyntaxKind::TupleType,
                NodeData::TupleTypeNode(Box::new(TupleTypeNodeData {
                    elements: NodeList {
                        range: TextRange::default(),
                        nodes: elements.to_vec(),
                        has_trailing_comma: false,
                    },
                })),
                elements,
            )
        }

        fn literal_type(&mut self, literal: NodeId) -> NodeId {
            self.alloc(
                SyntaxKind::LiteralType,
                NodeData::LiteralTypeNode(Box::new(LiteralTypeNodeData { literal })),
                &[literal],
            )
        }

        fn indexed_access_type(&mut self, object_type: NodeId, index_type: NodeId) -> NodeId {
            self.alloc(
                SyntaxKind::IndexedAccessType,
                NodeData::IndexedAccessTypeNode(Box::new(IndexedAccessTypeNodeData {
                    index_type,
                    object_type,
                })),
                &[object_type, index_type],
            )
        }

        fn element_access(&mut self, expression: NodeId, argument_expression: NodeId) -> NodeId {
            self.alloc(
                SyntaxKind::ElementAccessExpression,
                NodeData::ElementAccessExpression(Box::new(ElementAccessExpressionData {
                    argument_expression,
                    expression,
                    flow_node: None,
                    question_dot_token: None,
                    facts: 0,
                })),
                &[expression, argument_expression],
            )
        }

        fn binary(&mut self, left: NodeId, operator: SyntaxKind, right: NodeId) -> NodeId {
            let operator_node = self.alloc(operator, NodeData::Token(Box::new(TokenData)), &[]);
            self.alloc(
                SyntaxKind::BinaryExpression,
                NodeData::BinaryExpression(Box::new(ts_ast::BinaryExpressionData {
                    left,
                    operator_token: operator_node,
                    right,
                    symbol: None,
                    type_: None,
                    facts: 0,
                    modifiers: None,
                })),
                &[left, operator_node, right],
            )
        }

        fn variable(
            &mut self,
            name: &str,
            annotation: Option<NodeId>,
            initializer: Option<NodeId>,
        ) -> (NodeId, NodeId) {
            let name = self.identifier(name);
            let mut children = vec![name];
            children.extend(annotation);
            children.extend(initializer);
            let declaration = self.alloc(
                SyntaxKind::VariableDeclaration,
                NodeData::VariableDeclaration(Box::new(VariableDeclarationData {
                    exclamation_token: None,
                    initializer,
                    local_symbol: None,
                    symbol: None,
                    type_: annotation,
                    facts: 0,
                    name,
                })),
                &children,
            );
            let list = self.alloc(
                SyntaxKind::VariableDeclarationList,
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

        fn expression_statement(&mut self, expression: NodeId) -> NodeId {
            self.alloc(
                SyntaxKind::ExpressionStatement,
                NodeData::ExpressionStatement(Box::new(ExpressionStatementData {
                    expression,
                    flow_node: None,
                })),
                &[expression],
            )
        }

        fn block(&mut self, statements: &[NodeId]) -> NodeId {
            self.alloc(
                SyntaxKind::Block,
                NodeData::Block(Box::new(BlockData {
                    flow_node: None,
                    locals: AstSymbolTable,
                    multi_line: false,
                    next_container: None,
                    statements: NodeList {
                        range: TextRange::default(),
                        nodes: statements.to_vec(),
                        has_trailing_comma: false,
                    },
                    facts: 0,
                })),
                statements,
            )
        }

        fn return_statement(&mut self, expression: NodeId) -> NodeId {
            self.alloc(
                SyntaxKind::ReturnStatement,
                NodeData::ReturnStatement(Box::new(ReturnStatementData {
                    expression: Some(expression),
                    flow_node: None,
                    facts: 0,
                })),
                &[expression],
            )
        }

        fn function(&mut self, name: &str, return_type: NodeId, body: NodeId) -> NodeId {
            let name = self.identifier(name);
            self.alloc(
                SyntaxKind::FunctionDeclaration,
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
                    type_: Some(return_type),
                    type_parameters: None,
                    facts: 0,
                    modifiers: None,
                    name: Some(name),
                })),
                &[name, return_type, body],
            )
        }

        fn source(&mut self, statements: Vec<NodeId>) -> NodeId {
            let eof = self.alloc(
                SyntaxKind::EndOfFile,
                NodeData::Token(Box::new(TokenData)),
                &[],
            );
            let mut children = statements.clone();
            children.push(eof);
            self.alloc(
                SyntaxKind::SourceFile,
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
    fn checks_variables_names_and_binary_operators() {
        let mut builder = Builder::new();
        let number_type = builder.keyword_type(SyntaxKind::NumberKeyword);
        let bad_value = builder.string("wrong");
        let (bad_statement, bad_declaration) =
            builder.variable("count", Some(number_type), Some(bad_value));

        let one = builder.number("1");
        let (good_statement, good_declaration) = builder.variable("value", None, Some(one));

        let missing = builder.identifier("missing");
        let missing_statement = builder.expression_statement(missing);

        let left = builder.string("x");
        let right = builder.number("1");
        let invalid_binary = builder.binary(left, SyntaxKind::MinusToken, right);
        let invalid_statement = builder.expression_statement(invalid_binary);

        let plus_left = builder.string("x");
        let plus_right = builder.number("1");
        let plus = builder.binary(plus_left, SyntaxKind::PlusToken, plus_right);
        let plus_statement = builder.expression_statement(plus);

        let source = builder.source(vec![
            bad_statement,
            good_statement,
            missing_statement,
            invalid_statement,
            plus_statement,
        ]);
        let bindings = bind_source_file(&builder.arena, source);
        let result = check_source_file(&builder.arena, source, &bindings);

        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2322, 2304, 2365]
        );
        assert_eq!(
            result.diagnostics[0].diagnostic.render().unwrap(),
            "Type '\"wrong\"' is not assignable to type 'number'."
        );
        assert_eq!(
            result.diagnostics[1].diagnostic.render().unwrap(),
            "Cannot find name 'missing'."
        );
        assert_eq!(
            result.diagnostics[2].diagnostic.render().unwrap(),
            "Operator '-' cannot be applied to types '\"x\"' and '1'."
        );
        let good_symbol = bindings.node_symbols[&good_declaration];
        let good_type = result.type_of_symbol(good_symbol).unwrap();
        assert_eq!(result.types.get(good_type).unwrap().kind, TypeKind::Number);
        assert_eq!(
            result
                .types
                .get(result.type_of_node(plus).unwrap())
                .unwrap()
                .kind,
            TypeKind::String
        );
        assert!(bindings.node_symbols.contains_key(&bad_declaration));
    }

    #[test]
    fn checks_function_return_signatures_and_missing_returns() {
        let mut builder = Builder::new();
        let bad_return_value = builder.string("bad");
        let return_statement = builder.return_statement(bad_return_value);
        let body = builder.block(&[return_statement]);
        let number_type = builder.keyword_type(SyntaxKind::NumberKeyword);
        let function = builder.function("compute", number_type, body);

        let empty_body = builder.block(&[]);
        let other_number_type = builder.keyword_type(SyntaxKind::NumberKeyword);
        let missing_return = builder.function("missing", other_number_type, empty_body);
        let source = builder.source(vec![function, missing_return]);

        let bindings = bind_source_file(&builder.arena, source);
        let result = check_source_file(&builder.arena, source, &bindings);
        assert_eq!(result.diagnostics.len(), 2);
        assert_eq!(result.diagnostics[0].diagnostic.code(), 2322);
        assert_eq!(
            result.diagnostics[0].diagnostic.render().unwrap(),
            "Type '\"bad\"' is not assignable to type 'number'."
        );
        assert_eq!(result.diagnostics[1].diagnostic.code(), 2355);
        assert_eq!(
            result.diagnostics[1].diagnostic.render().unwrap(),
            "A function whose declared type is neither 'undefined', 'void', nor 'any' must return a value."
        );

        let symbol = bindings.node_symbols[&function];
        let function_type = result.type_of_symbol(symbol).unwrap();
        let TypeKind::Function(signature) = &result.types.get(function_type).unwrap().kind else {
            panic!("expected function type");
        };
        assert_eq!(
            result.types.get(signature.return_type).unwrap().kind,
            TypeKind::Number
        );
    }

    #[test]
    fn narrows_nullish_unions_across_if_branches() {
        let mut builder = Builder::new();
        let string_type = builder.keyword_type(SyntaxKind::StringKeyword);
        let null_type = builder.keyword_type(SyntaxKind::NullKeyword);
        let value_type = builder.union_type(&[string_type, null_type]);
        let initializer = builder.null();
        let (declaration, _) = builder.variable("value", Some(value_type), Some(initializer));

        let condition_value = builder.identifier("value");
        let condition_null = builder.null();
        let condition = builder.binary(
            condition_value,
            SyntaxKind::ExclamationEqualsEqualsToken,
            condition_null,
        );
        let then_value = builder.identifier("value");
        let then_access = builder.property_access(then_value, "length");
        let then_statement = builder.expression_statement(then_access);
        let then_block = builder.block(&[then_statement]);
        let else_value = builder.identifier("value");
        let else_access = builder.property_access(else_value, "length");
        let else_statement = builder.expression_statement(else_access);
        let else_block = builder.block(&[else_statement]);
        let if_statement = builder.if_statement(condition, then_block, Some(else_block));
        let source = builder.source(vec![declaration, if_statement]);

        let bindings = bind_source_file(&builder.arena, source);
        let result = check_source_file(&builder.arena, source, &bindings);
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(result.diagnostics[0].diagnostic.code(), 2339);
        assert_eq!(
            result.diagnostics[0].diagnostic.render().unwrap(),
            "Property 'length' does not exist on type 'null'."
        );
    }

    #[test]
    fn narrows_typeof_checks_inside_if_branches() {
        let mut builder = Builder::new();
        let string_type = builder.keyword_type(SyntaxKind::StringKeyword);
        let number_type = builder.keyword_type(SyntaxKind::NumberKeyword);
        let value_type = builder.union_type(&[string_type, number_type]);
        let initializer = builder.number("1");
        let (declaration, _) = builder.variable("value", Some(value_type), Some(initializer));

        let condition_value = builder.identifier("value");
        let type_of_value = builder.type_of(condition_value);
        let string_name = builder.string("string");
        let condition = builder.binary(
            type_of_value,
            SyntaxKind::EqualsEqualsEqualsToken,
            string_name,
        );
        let narrowed_value = builder.identifier("value");
        let access = builder.property_access(narrowed_value, "length");
        let statement = builder.expression_statement(access);
        let block = builder.block(&[statement]);
        let if_statement = builder.if_statement(condition, block, None);
        let source = builder.source(vec![declaration, if_statement]);

        let bindings = bind_source_file(&builder.arena, source);
        let result = check_source_file(&builder.arena, source, &bindings);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    }

    #[test]
    fn checks_tuple_and_indexed_access_types() {
        let mut builder = Builder::new();
        let first_type = builder.keyword_type(SyntaxKind::StringKeyword);
        let second_type = builder.keyword_type(SyntaxKind::NumberKeyword);
        let tuple_type = builder.tuple_type(&[first_type, second_type]);
        let first_value = builder.string("name");
        let second_value = builder.number("1");
        let tuple_value = builder.array(&[first_value, second_value]);
        let (tuple_statement, _) = builder.variable("pair", Some(tuple_type), Some(tuple_value));

        let pair = builder.identifier("pair");
        let zero = builder.number("0");
        let first_access = builder.element_access(pair, zero);
        let first_statement = builder.expression_statement(first_access);
        let other_pair = builder.identifier("pair");
        let two = builder.number("2");
        let out_of_bounds = builder.element_access(other_pair, two);
        let out_of_bounds_statement = builder.expression_statement(out_of_bounds);

        let indexed_string = builder.keyword_type(SyntaxKind::StringKeyword);
        let indexed_number = builder.keyword_type(SyntaxKind::NumberKeyword);
        let indexed_tuple = builder.tuple_type(&[indexed_string, indexed_number]);
        let index_literal = builder.number("0");
        let index_type = builder.literal_type(index_literal);
        let indexed_type = builder.indexed_access_type(indexed_tuple, index_type);
        let indexed_initializer = builder.string("indexed");
        let (indexed_statement, _) =
            builder.variable("first", Some(indexed_type), Some(indexed_initializer));
        let source = builder.source(vec![
            tuple_statement,
            first_statement,
            out_of_bounds_statement,
            indexed_statement,
        ]);

        let bindings = bind_source_file(&builder.arena, source);
        let result = check_source_file(&builder.arena, source, &bindings);
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(result.diagnostics[0].diagnostic.code(), 2493);
        assert_eq!(
            result
                .types
                .get(result.type_of_node(first_access).unwrap())
                .unwrap()
                .kind,
            TypeKind::String
        );
        assert_eq!(
            result.diagnostics[0].diagnostic.render().unwrap(),
            "Tuple type '[string, number]' of length '2' has no element at index '2'."
        );
    }

    #[test]
    fn constructs_and_assigns_unions_intersections_and_tuples() {
        let arena = NodeArena::new();
        let bindings = BindResult::default();
        let mut checker = Checker::new(&arena, &bindings);
        let string = checker.result.types.string();
        let number = checker.result.types.number();
        let left = checker.result.types.alloc(TypeKind::Object(ObjectType {
            properties: BTreeMap::from([("left".into(), string)]),
        }));
        let right = checker.result.types.alloc(TypeKind::Object(ObjectType {
            properties: BTreeMap::from([("right".into(), number)]),
        }));
        let intersection = checker.result.types.intersection([left, right]);
        let target = checker.result.types.alloc(TypeKind::Object(ObjectType {
            properties: BTreeMap::from([("left".into(), string), ("right".into(), number)]),
        }));
        assert!(checker.is_assignable(intersection, target));
        assert_eq!(
            checker.lookup_property_type(intersection, "left"),
            Some(string)
        );
        assert_eq!(
            checker.lookup_property_type(intersection, "right"),
            Some(number)
        );

        let tuple = checker
            .result
            .types
            .alloc(TypeKind::Tuple(vec![string, string]));
        let string_array = checker.result.types.alloc(TypeKind::Array(string));
        assert!(checker.is_assignable(tuple, string_array));
        let union = checker.result.types.union([string, number]);
        assert!(checker.is_assignable(string, union));
        assert!(!checker.is_assignable(intersection, string));
    }

    #[test]
    fn checks_parsed_typescript_end_to_end() {
        let parsed = parse_source_file(
            r#"
                interface Point { x: number; }
                const point: Point = { x: 1 };
                point.x;
                point.missing;

                function identity<T>(value: T): T { return value; }
                const answer: number = identity(1);
                const bad: string = identity(1);

                const add = (value: number): number => value + value;
                add(1);
                add("x");
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let result = check_source_file(&parsed.arena, parsed.source_file, &bindings);

        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2339, 2322, 2345]
        );
        assert_eq!(
            result.diagnostics[0].diagnostic.render().unwrap(),
            "Property 'missing' does not exist on type '{ x: number }'."
        );
        assert_eq!(
            result.diagnostics[1].diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        assert_eq!(
            result.diagnostics[2].diagnostic.render().unwrap(),
            "Argument of type '\"x\"' is not assignable to parameter of type 'number'."
        );
    }

    #[test]
    fn checks_parsed_classes_calls_and_contextual_arrays() {
        let parsed = parse_source_file(
            r#"
                class Greeter {
                    value: number = 1;
                    greet(input: string): string { return input; }
                }
                const greeter = new Greeter();
                greeter.value;
                greeter.greet("hello");
                greeter.greet(1);

                const values: Array<number> = [1, "wrong"];
                const mapper = (value: number): number => value;
                mapper();
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let result = check_source_file(&parsed.arena, parsed.source_file, &bindings);

        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2345, 2322, 2554]
        );
        assert_eq!(
            result.diagnostics[2].diagnostic.render().unwrap(),
            "Expected 1 arguments, but got 0."
        );
    }

    #[test]
    fn instantiates_parsed_generic_and_non_generic_aliases() {
        let parsed = parse_source_file(
            r#"
                type List<T> = Array<T>;
                type Name = string;
                const good: List<number> = [1, 2];
                const bad: List<string> = ["ok", 1];
                const badName: Name = 1;
                const literal = 1;
                let widened = 1;
                const record = { value: 1 };
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let result = check_source_file(&parsed.arena, parsed.source_file, &bindings);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2322, 2322]
        );

        let root = bindings.root_scope().unwrap();
        let literal = result
            .type_of_symbol(root.symbols.get("literal").unwrap())
            .unwrap();
        assert_eq!(
            result.types.get(literal).unwrap().kind,
            TypeKind::NumberLiteral("1".into())
        );
        let widened = result
            .type_of_symbol(root.symbols.get("widened").unwrap())
            .unwrap();
        assert_eq!(result.types.get(widened).unwrap().kind, TypeKind::Number);
        let object = result
            .type_of_symbol(root.symbols.get("record").unwrap())
            .unwrap();
        let TypeKind::Object(object) = &result.types.get(object).unwrap().kind else {
            panic!("expected object type");
        };
        assert_eq!(
            result.types.get(object.properties["value"]).unwrap().kind,
            TypeKind::Number
        );
    }
}
