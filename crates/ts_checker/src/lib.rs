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
    Union(Vec<TypeId>),
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
        flattened.sort_unstable();
        flattened.dedup();
        match flattened.as_slice() {
            [] => self.never(),
            [single] => *single,
            _ => self.alloc(TypeKind::Union(flattened)),
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
            TypeKind::Union(members) => members
                .iter()
                .map(|member| self.display(*member))
                .collect::<Vec<_>>()
                .join(" | "),
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

struct Checker<'a> {
    arena: &'a NodeArena,
    bindings: &'a BindResult,
    result: CheckResult,
    children: HashMap<NodeId, Vec<NodeId>>,
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
        }
    }

    fn check(mut self, source_file: NodeId) -> CheckResult {
        self.seed_symbol_types();
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
                let initializer = data.initializer.map(|node| self.type_of_expression(node));
                if let (Some(actual), Some(expected)) = (initializer, annotation)
                    && !self.is_assignable(actual, expected)
                {
                    self.assignability_error(node_id, actual, expected);
                }
                if let Some(symbol) = self.bindings.node_symbols.get(&node_id) {
                    let inferred = annotation
                        .or(initializer.map(|value| self.widen_literal(value)))
                        .unwrap_or_else(|| self.result.types.any());
                    self.result.symbol_types.insert(*symbol, inferred);
                }
            }
            NodeData::FunctionDeclaration(data) => {
                self.check_function(node_id, data);
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
        let return_type = match &self.result.types.get(function_type).unwrap().kind {
            TypeKind::Function(function) => function.return_type,
            _ => self.result.types.any(),
        };
        for parameter in &data.parameters.nodes {
            self.check_parameter(*parameter);
        }
        let mut saw_return = false;
        if let Some(body) = data.body {
            self.check_node(body, Some(return_type), &mut saw_return);
        }
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

    fn type_of_expression(&mut self, node_id: NodeId) -> TypeId {
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
            NodeData::ParenthesizedExpression(data) => self.type_of_expression(data.expression),
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
                let mut properties = BTreeMap::new();
                for property in &data.properties.nodes {
                    if let Some(NodeData::PropertyAssignment(property_data)) =
                        self.arena.get(*property).map(|node| &node.data)
                        && let Some(name) = self.property_name(property_data.name)
                    {
                        properties.insert(name, self.type_of_expression(property_data.initializer));
                    }
                }
                self.result
                    .types
                    .alloc(TypeKind::Object(ObjectType { properties }))
            }
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
        if let Some(symbol) = self.resolve_identifier(node, name) {
            return self
                .result
                .symbol_types
                .get(&symbol)
                .copied()
                .unwrap_or_else(|| self.result.types.any());
        }
        self.error(node, 2304, [name.to_owned()]);
        self.result.types.any()
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
        let annotations = data
            .parameters
            .nodes
            .iter()
            .map(|parameter| {
                self.arena
                    .get(*parameter)
                    .and_then(|node| match &node.data {
                        NodeData::ParameterDeclaration(data) => data.type_,
                        _ => None,
                    })
            })
            .collect::<Vec<_>>();
        let parameters = annotations
            .into_iter()
            .map(|annotation| match annotation {
                Some(node) => self.type_from_type_node(node),
                None => self.result.types.any(),
            })
            .collect();
        let return_type = match data.type_ {
            Some(node) => self.type_from_type_node(node),
            None => self.result.types.any(),
        };
        self.result.types.alloc(TypeKind::Function(FunctionType {
            parameters,
            return_type,
        }))
    }

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
                SyntaxKind::BooleanKeyword => self.result.types.boolean(),
                SyntaxKind::NumberKeyword => self.result.types.number(),
                SyntaxKind::StringKeyword => self.result.types.string(),
                SyntaxKind::BigIntKeyword => self.result.types.bigint(),
                _ => self.result.types.unknown(),
            },
            NodeData::LiteralTypeNode(data) => self.type_of_expression(data.literal),
            NodeData::ParenthesizedTypeNode(data) => self.type_from_type_node(data.type_),
            NodeData::UnionTypeNode(data) => {
                let members = data
                    .types
                    .nodes
                    .iter()
                    .map(|node| self.type_from_type_node(*node))
                    .collect::<Vec<_>>();
                self.result.types.union(members)
            }
            _ => self.result.types.unknown(),
        }
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
            (TypeKind::Object(source), TypeKind::Object(target)) => {
                target.properties.iter().all(|(name, target_type)| {
                    source
                        .properties
                        .get(name)
                        .is_some_and(|source_type| self.is_assignable(*source_type, *target_type))
                })
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

    fn widen_literal(&self, type_id: TypeId) -> TypeId {
        match self.result.types.get(type_id).map(|value| &value.kind) {
            Some(TypeKind::NumberLiteral(_)) => self.result.types.number(),
            Some(TypeKind::StringLiteral(_)) => self.result.types.string(),
            Some(TypeKind::BigIntLiteral(_)) => self.result.types.bigint(),
            Some(TypeKind::BooleanLiteral(_)) => self.result.types.boolean(),
            _ => type_id,
        }
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
        let container = self.bindings.containers.get(&node)?;
        let mut scope = self
            .bindings
            .node_scopes
            .get(container)
            .copied()
            .or_else(|| {
                self.bindings
                    .scopes
                    .iter()
                    .find(|scope| scope.owner == *container)
                    .map(|scope| scope.id)
            })?;
        loop {
            let current = self.bindings.scope(scope)?;
            if let Some(symbol) = current.symbols.get(name) {
                return Some(symbol);
            }
            scope = current.parent?;
        }
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
    use ts_ast::{
        BlockData, ExpressionStatementData, FunctionDeclarationData, IdentifierData,
        KeywordTypeNodeData, Node, NodeArena, NodeData, NodeFlags, NodeId, NodeList,
        NumericLiteralData, ReturnStatementData, SourceFileData, StringLiteralData,
        SymbolTable as AstSymbolTable, SyntaxKind, TokenData, TokenFlags, VariableDeclarationData,
        VariableDeclarationListData, VariableStatementData,
    };
    use ts_binder::bind_source_file;
    use ts_core::TextRange;

    use super::{TypeKind, check_source_file};

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
}
