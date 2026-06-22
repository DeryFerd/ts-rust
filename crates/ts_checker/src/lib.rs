//! Initial semantic type checking over the arena-backed TypeScript AST.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use ts_ast::{NodeArena, NodeData, NodeId, SymbolId, SyntaxKind};
use ts_binder::BindResult;
use ts_diagnostics::{Diagnostic, message_by_code};
use ts_evaluator::{Evaluation, EvaluationOutcome, UnknownReason, Value, evaluate_with};
use ts_jsnum::Number;

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
    Constructor(FunctionType),
    Overload(Vec<FunctionType>),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ObjectType {
    pub properties: BTreeMap<String, TypeId>,
    pub optional_properties: BTreeSet<String>,
    pub readonly_properties: BTreeSet<String>,
    pub getter_properties: BTreeSet<String>,
    pub setter_properties: BTreeSet<String>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FunctionType {
    pub parameters: Vec<TypeId>,
    pub return_type: TypeId,
    pub parameters_optional: bool,
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
            TypeKind::Constructor(constructor) => format!(
                "new ({}) => {}",
                constructor
                    .parameters
                    .iter()
                    .enumerate()
                    .map(|(index, value)| format!("arg{index}: {}", self.display(*value)))
                    .collect::<Vec<_>>()
                    .join(", "),
                self.display(constructor.return_type)
            ),
            TypeKind::Overload(signatures) => signatures
                .iter()
                .map(|signature| {
                    format!(
                        "({}) => {}",
                        signature
                            .parameters
                            .iter()
                            .enumerate()
                            .map(|(index, value)| {
                                format!("arg{index}: {}", self.display(*value))
                            })
                            .collect::<Vec<_>>()
                            .join(", "),
                        self.display(signature.return_type)
                    )
                })
                .collect::<Vec<_>>()
                .join(" | "),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckDiagnostic {
    pub node: NodeId,
    pub diagnostic: Diagnostic,
}

/// A compile-time value assigned to an enum member.
#[derive(Clone, Debug, PartialEq)]
pub enum EnumConstantValue {
    Number(f64),
    String(String),
}

#[derive(Clone, Debug)]
pub struct CheckResult {
    pub types: TypeArena,
    pub symbol_types: HashMap<SymbolId, TypeId>,
    /// Expression and declaration types, stable after checking completes.
    pub node_types: BTreeMap<NodeId, TypeId>,
    pub enum_member_values: BTreeMap<NodeId, EnumConstantValue>,
    pub enum_access_values: BTreeMap<NodeId, EnumConstantValue>,
    /// Declaration statements retained for emit, keyed by source file or module block.
    pub declaration_reachability: BTreeMap<NodeId, BTreeSet<NodeId>>,
    pub diagnostics: Vec<CheckDiagnostic>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(clippy::struct_excessive_bools)]
pub struct CheckerOptions {
    pub allow_unreachable_code: Option<bool>,
    pub exact_optional_property_types: bool,
    pub is_declaration_file: bool,
    pub is_javascript_file: bool,
    pub no_fallthrough_cases_in_switch: bool,
    pub strict_null_checks: bool,
    pub no_implicit_any: bool,
    pub no_implicit_returns: bool,
    pub no_unused_locals: bool,
    pub no_unused_parameters: bool,
    pub use_unknown_in_catch_variables: bool,
}

impl Default for CheckerOptions {
    fn default() -> Self {
        Self {
            allow_unreachable_code: None,
            exact_optional_property_types: false,
            is_declaration_file: false,
            is_javascript_file: false,
            no_fallthrough_cases_in_switch: false,
            strict_null_checks: true,
            no_implicit_any: false,
            no_implicit_returns: false,
            no_unused_locals: false,
            no_unused_parameters: false,
            use_unknown_in_catch_variables: false,
        }
    }
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

    #[must_use]
    pub fn declarations_to_emit(&self, scope: NodeId) -> Option<&BTreeSet<NodeId>> {
        self.declaration_reachability.get(&scope)
    }
}

#[must_use]
pub fn check_source_file(
    arena: &NodeArena,
    source_file: NodeId,
    bindings: &BindResult,
) -> CheckResult {
    check_source_file_with_options(arena, source_file, bindings, CheckerOptions::default())
}

#[must_use]
pub fn check_source_file_with_options(
    arena: &NodeArena,
    source_file: NodeId,
    bindings: &BindResult,
    options: CheckerOptions,
) -> CheckResult {
    Checker::new(arena, bindings)
        .with_options(options)
        .check(source_file)
}

#[must_use]
pub fn empty_check_result() -> CheckResult {
    CheckResult {
        types: TypeArena::new(),
        symbol_types: HashMap::new(),
        node_types: BTreeMap::new(),
        enum_member_values: BTreeMap::new(),
        enum_access_values: BTreeMap::new(),
        declaration_reachability: BTreeMap::new(),
        diagnostics: Vec::new(),
    }
}

pub struct ProgramSource<'a> {
    pub arena: &'a NodeArena,
    pub source_file: NodeId,
    pub bindings: &'a BindResult,
    pub resolved_modules: &'a BTreeMap<String, usize>,
    pub is_default_library: bool,
    pub skip_diagnostics: bool,
    pub checker_options: CheckerOptions,
}

#[derive(Debug)]
pub struct ProgramCheckResult {
    pub files: Vec<CheckResult>,
}

#[must_use]
pub fn check_program(sources: &[ProgramSource<'_>]) -> ProgramCheckResult {
    ProgramChecker::new(sources).check()
}

#[derive(Clone, Debug, PartialEq)]
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
    ConstEnum(Box<Self>),
    TypeParameter(String),
    Alias {
        parameters: Vec<String>,
        body: Box<Self>,
    },
    Array(Box<Self>),
    Tuple(Vec<Self>),
    Union(Vec<Self>),
    Intersection(Vec<Self>),
    Object {
        properties: BTreeMap<String, Self>,
        optional_properties: BTreeSet<String>,
        readonly_properties: BTreeSet<String>,
        getter_properties: BTreeSet<String>,
    },
    Function {
        parameters: Vec<Self>,
        return_type: Box<Self>,
        parameters_optional: bool,
    },
    Constructor {
        parameters: Vec<Self>,
        return_type: Box<Self>,
        parameters_optional: bool,
    },
    Overload(Vec<Self>),
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
            .map(|source| {
                if source.is_default_library {
                    empty_check_result()
                } else {
                    check_source_file_with_options(
                        source.arena,
                        source.source_file,
                        source.bindings,
                        source.checker_options,
                    )
                }
            })
            .collect::<Vec<_>>();
        let exports = self
            .sources
            .iter()
            .zip(&preliminary)
            .map(|(source, result)| Self::module_exports(source, result))
            .collect::<Vec<_>>();
        let (globals, duplicate_globals) = self.globals(&preliminary);
        let mut files = Vec::with_capacity(self.sources.len());
        for (file_index, source) in self.sources.iter().enumerate() {
            let (external_symbols, mut import_diagnostics) = Self::imports(source, &exports);
            let mut result = if source.is_default_library {
                preliminary[file_index].clone()
            } else {
                Checker::new(source.arena, source.bindings)
                    .with_options(source.checker_options)
                    .with_environment(external_symbols, globals.clone())
                    .check(source.source_file)
            };
            if source.is_default_library || source.skip_diagnostics {
                result.diagnostics.clear();
            }
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
                if symbol.declarations.iter().all(|declaration| {
                    matches!(
                        source.arena.get(*declaration).map(|node| &node.data),
                        Some(NodeData::ModuleDeclaration(module))
                            if matches!(
                                source.arena.get(module.name).map(|node| &node.data),
                                Some(NodeData::StringLiteral(_))
                            )
                    )
                }) {
                    continue;
                }
                if let Some((existing_file, existing_flags)) = declarations.get(name) {
                    let both_default_libraries = source.is_default_library
                        && self.sources[*existing_file].is_default_library;
                    if !both_default_libraries
                        && !global_declarations_merge(*existing_flags, symbol.flags)
                    {
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
                    if ((existing_flags.contains(ts_binder::SymbolFlags::INTERFACE)
                        && symbol.flags.contains(ts_binder::SymbolFlags::INTERFACE))
                        || (existing_flags.contains(ts_binder::SymbolFlags::NAMESPACE_MODULE)
                            && symbol
                                .flags
                                .contains(ts_binder::SymbolFlags::NAMESPACE_MODULE)))
                        && let Some(descriptor) = if source.is_default_library {
                            Self::describe_default_library_symbol(source, symbol_id)
                        } else {
                            Self::describe_symbol(source, result, symbol_id)
                        }
                        && let Some(existing) = globals.get_mut(name)
                    {
                        merge_global_descriptor(existing, descriptor);
                    }
                    continue;
                }
                let descriptor = if source.is_default_library {
                    Self::describe_default_library_symbol(source, symbol_id)
                } else {
                    Self::describe_symbol(source, result, symbol_id)
                };
                if let Some(descriptor) = descriptor {
                    globals.insert(name.to_owned(), descriptor);
                    declarations.insert(name.to_owned(), (file_index, symbol.flags));
                }
            }
        }
        (globals, duplicates)
    }

    fn describe_default_library_symbol(
        source: &ProgramSource<'_>,
        symbol_id: SymbolId,
    ) -> Option<TypeDescriptor> {
        let symbol = source.bindings.symbols.get(symbol_id)?;
        let core_name = is_core_library_name(&symbol.name);
        let preserve = symbol.declarations.iter().any(|declaration| {
            match source.arena.get(*declaration).map(|node| &node.data) {
                Some(NodeData::TypeAliasDeclaration(_)) => core_name,
                Some(NodeData::InterfaceDeclaration(_) | NodeData::ClassDeclaration(_)) => {
                    core_name
                }
                Some(NodeData::FunctionDeclaration(_)) => {
                    core_name && symbol.declarations.len() > 1
                }
                _ => false,
            }
        });
        if !preserve {
            return Some(TypeDescriptor::Any);
        }
        describe_declaration_symbol(source, symbol_id).or(Some(TypeDescriptor::Any))
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
            } else if let Some(bindings) = clause_data.named_bindings
                && let Some(NodeData::NamespaceImport(namespace)) =
                    source.arena.get(bindings).map(|node| &node.data)
                && let Some(symbol) = source
                    .bindings
                    .node_symbols
                    .get(&bindings)
                    .or_else(|| source.bindings.node_symbols.get(&namespace.name))
            {
                symbols.insert(
                    *symbol,
                    TypeDescriptor::Object {
                        properties: module_exports.clone(),
                        optional_properties: BTreeSet::new(),
                        readonly_properties: BTreeSet::new(),
                        getter_properties: BTreeSet::new(),
                    },
                );
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
        let namespace = symbol
            .flags
            .contains(ts_binder::SymbolFlags::NAMESPACE_MODULE)
            .then(|| {
                let properties = symbol
                    .members
                    .iter()
                    .filter_map(|(name, member)| {
                        Self::describe_symbol(source, result, member)
                            .map(|descriptor| (name.to_owned(), descriptor))
                    })
                    .collect();
                TypeDescriptor::Object {
                    properties,
                    optional_properties: BTreeSet::new(),
                    readonly_properties: BTreeSet::new(),
                    getter_properties: BTreeSet::new(),
                }
            });
        if let Some(declaration) = describe_declaration_symbol(source, symbol_id) {
            return Some(namespace.map_or(declaration.clone(), |namespace| {
                TypeDescriptor::Intersection(vec![declaration, namespace])
            }));
        }
        if namespace.is_some() {
            return namespace;
        }
        let target = symbol.target.unwrap_or(symbol_id);
        let target_symbol = source.bindings.symbols.get(target)?;
        for declaration in &target_symbol.declarations {
            if let Some(NodeData::ExportAssignment(assignment)) =
                source.arena.get(*declaration).map(|node| &node.data)
                && let Some(type_id) = result.type_of_node(assignment.expression)
            {
                return Some(describe_type(&result.types, type_id));
            }
        }
        let descriptor = result
            .type_of_symbol(target)
            .map(|type_id| describe_type(&result.types, type_id))?;
        Some(
            if target_symbol
                .flags
                .contains(ts_binder::SymbolFlags::CONST_ENUM)
            {
                TypeDescriptor::ConstEnum(Box::new(descriptor))
            } else {
                descriptor
            },
        )
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
    flow_types: HashMap<SymbolId, TypeId>,
    alias_stack: Vec<SymbolId>,
    external_symbols: HashMap<SymbolId, TypeDescriptor>,
    external_names: BTreeMap<String, TypeDescriptor>,
    external_aliases: HashMap<SymbolId, TypeDescriptor>,
    imported_type_parameters: HashMap<String, TypeId>,
    options: CheckerOptions,
    symbol_reads: HashMap<SymbolId, usize>,
    enum_member_owners: HashMap<TypeId, TypeId>,
    enum_types: BTreeSet<TypeId>,
    const_enum_types: BTreeSet<TypeId>,
    checked_overload_symbols: HashSet<SymbolId>,
    reported_unresolved_type_names: HashSet<NodeId>,
    this_types: Vec<TypeId>,
}

enum DeclaredObject {
    Class(ts_ast::ClassDeclarationData),
    Interface(ts_ast::InterfaceDeclarationData),
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
                enum_member_values: BTreeMap::new(),
                enum_access_values: BTreeMap::new(),
                declaration_reachability: BTreeMap::new(),
                diagnostics: Vec::new(),
            },
            children,
            type_parameter_scopes: Vec::new(),
            local_scopes: Vec::new(),
            narrowings: Vec::new(),
            flow_types: HashMap::new(),
            alias_stack: Vec::new(),
            external_symbols: HashMap::new(),
            external_names: BTreeMap::new(),
            external_aliases: HashMap::new(),
            imported_type_parameters: HashMap::new(),
            options: CheckerOptions::default(),
            symbol_reads: HashMap::new(),
            enum_member_owners: HashMap::new(),
            enum_types: BTreeSet::new(),
            const_enum_types: BTreeSet::new(),
            checked_overload_symbols: HashSet::new(),
            reported_unresolved_type_names: HashSet::new(),
            this_types: Vec::new(),
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

    const fn with_options(mut self, options: CheckerOptions) -> Self {
        self.options = options;
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
        self.check_unused_symbols();
        self.result.declaration_reachability = DeclarationReachability::analyze(
            self.arena,
            self.bindings,
            source_file,
            self.options.is_declaration_file,
        );
        self.result
    }

    fn seed_symbol_types(&mut self) {
        for symbol in self.bindings.symbols.iter() {
            if self.result.symbol_types.contains_key(&symbol.id) {
                continue;
            }
            let function_declarations = symbol
                .declarations
                .iter()
                .filter_map(|declaration| {
                    let NodeData::FunctionDeclaration(data) = &self.arena.get(*declaration)?.data
                    else {
                        return None;
                    };
                    Some(data.as_ref().clone())
                })
                .collect::<Vec<_>>();
            if !function_declarations.is_empty() {
                let overloads = function_declarations
                    .iter()
                    .filter(|declaration| {
                        function_declarations.len() == 1 || declaration.body.is_none()
                    })
                    .map(|declaration| self.function_signature(declaration))
                    .collect::<Vec<_>>();
                let symbol_type = if overloads.len() == 1 {
                    self.result
                        .types
                        .alloc(TypeKind::Function(overloads[0].clone()))
                } else {
                    self.result.types.alloc(TypeKind::Overload(overloads))
                };
                self.result.symbol_types.insert(symbol.id, symbol_type);
                continue;
            }
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
                    NodeData::ClassDeclaration(data) => {
                        symbol_type = Some(self.declared_object_type(
                            data.type_parameters.as_ref(),
                            data.heritage_clauses.as_ref(),
                            &data.members.nodes,
                            &[],
                        ));
                        break;
                    }
                    NodeData::InterfaceDeclaration(data) => {
                        symbol_type = Some(self.declared_object_type(
                            data.type_parameters.as_ref(),
                            data.heritage_clauses.as_ref(),
                            &data.members.nodes,
                            &[],
                        ));
                        break;
                    }
                    NodeData::TypeAliasDeclaration(data) => {
                        symbol_type = Some(self.type_alias_type(data, &[]));
                        break;
                    }
                    NodeData::EnumDeclaration(data) => {
                        symbol_type = Some(self.enum_type(data));
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
        self.seed_namespace_types();
        self.seed_import_equals_types();
    }

    fn seed_namespace_types(&mut self) {
        let namespaces = self
            .bindings
            .symbols
            .iter()
            .filter(|symbol| {
                symbol
                    .flags
                    .contains(ts_binder::SymbolFlags::NAMESPACE_MODULE)
            })
            .map(|symbol| symbol.id)
            .collect::<Vec<_>>();
        for symbol_id in namespaces.into_iter().rev() {
            let Some(symbol) = self.bindings.symbols.get(symbol_id) else {
                continue;
            };
            let properties = symbol
                .members
                .iter()
                .filter_map(|(name, member)| {
                    self.result
                        .symbol_types
                        .get(&member)
                        .copied()
                        .map(|type_id| (name.to_owned(), type_id))
                })
                .collect::<BTreeMap<_, _>>();
            let namespace_type = self.result.types.alloc(TypeKind::Object(ObjectType {
                properties,
                ..ObjectType::default()
            }));
            let existing = self
                .result
                .symbol_types
                .get(&symbol_id)
                .copied()
                .unwrap_or_else(|| self.result.types.any());
            let combined = if existing == self.result.types.any() {
                namespace_type
            } else {
                self.result.types.intersection([existing, namespace_type])
            };
            self.result.symbol_types.insert(symbol_id, combined);
        }
    }

    fn seed_import_equals_types(&mut self) {
        let aliases = self
            .bindings
            .symbols
            .iter()
            .filter(|symbol| symbol.flags.contains(ts_binder::SymbolFlags::ALIAS))
            .filter_map(|symbol| {
                symbol.declarations.iter().find_map(|declaration| {
                    let NodeData::ImportEqualsDeclaration(import) =
                        &self.arena.get(*declaration)?.data
                    else {
                        return None;
                    };
                    Some((symbol.id, import.module_reference))
                })
            })
            .collect::<Vec<_>>();
        for (symbol, reference) in aliases {
            if let Some(type_id) = self.entity_name_type(reference) {
                self.result.symbol_types.insert(symbol, type_id);
            }
        }
    }

    fn entity_name_type(&mut self, node: NodeId) -> Option<TypeId> {
        match self.arena.get(node)?.data.clone() {
            NodeData::Identifier(identifier) => Some(self.identifier_type(node, &identifier.text)),
            NodeData::QualifiedName(name) => {
                let receiver = self.entity_name_type(name.left)?;
                let property = self.property_name(name.right)?;
                self.lookup_property_type(receiver, &property)
            }
            _ => None,
        }
    }

    fn entity_name_text(&self, node: NodeId) -> Option<String> {
        match &self.arena.get(node)?.data {
            NodeData::Identifier(identifier) => Some(identifier.text.clone()),
            NodeData::QualifiedName(name) => Some(format!(
                "{}.{}",
                self.entity_name_text(name.left)?,
                self.property_name(name.right)?
            )),
            _ => None,
        }
    }

    fn type_entity_name_type(&mut self, node: NodeId) -> Option<TypeId> {
        match self.arena.get(node)?.data.clone() {
            NodeData::Identifier(identifier) => {
                for scope in self.type_parameter_scopes.iter().rev() {
                    if let Some(type_id) = scope.get(&identifier.text) {
                        return Some(*type_id);
                    }
                }
                if let Some(symbol) = self.resolve_identifier(node, &identifier.text) {
                    if let Some(descriptor) = self.external_aliases.get(&symbol).cloned() {
                        return Some(self.import_alias(&descriptor, &[]));
                    }
                    return Some(
                        self.result
                            .symbol_types
                            .get(&symbol)
                            .copied()
                            .unwrap_or_else(|| self.result.types.any()),
                    );
                }
                let descriptor = self.external_names.get(&identifier.text)?.clone();
                Some(self.import_type(&descriptor))
            }
            NodeData::QualifiedName(name) => {
                let receiver = self.type_entity_name_type(name.left)?;
                let property = self.property_name(name.right)?;
                self.lookup_property_type(receiver, &property)
            }
            _ => None,
        }
    }

    fn unresolved_type_name(&mut self, node: NodeId, name: String) -> TypeId {
        if self.reported_unresolved_type_names.insert(node) {
            self.error(node, 2304, [name]);
        }
        self.result.types.unknown()
    }

    fn enum_type(&mut self, data: &ts_ast::EnumDeclarationData) -> TypeId {
        let mut properties = BTreeMap::new();
        let mut resolved_values = BTreeMap::<String, Value>::new();
        let member_names = data
            .members
            .nodes
            .iter()
            .filter_map(|member_id| {
                let NodeData::EnumMember(member) = &self.arena.get(*member_id)?.data else {
                    return None;
                };
                self.property_name(member.name)
            })
            .collect::<BTreeSet<_>>();
        let enum_name = self.property_name(data.name).unwrap_or_default();
        let is_const = self.has_ast_modifier(data.modifiers.as_ref(), SyntaxKind::ConstKeyword);
        let mut next_numeric_value = Some(0.0_f64);
        for member_id in &data.members.nodes {
            let Some(NodeData::EnumMember(member)) =
                self.arena.get(*member_id).map(|node| &node.data)
            else {
                continue;
            };
            let Some(name) = self.property_name(member.name) else {
                continue;
            };
            let initializer = member.initializer;
            let constant = initializer.and_then(|initializer| {
                self.evaluate_enum_initializer(
                    initializer,
                    is_const,
                    &enum_name,
                    &member_names,
                    &resolved_values,
                )
            });
            let member_type = if let Some(value) = constant {
                let member_type = self.enum_constant_type(&value);
                next_numeric_value = match &value {
                    Value::Number(value) => Some(value.value() + 1.0),
                    _ => None,
                };
                resolved_values.insert(name.clone(), value.clone());
                self.record_enum_constant(*member_id, &value);
                member_type
            } else if let Some(initializer) = initializer {
                next_numeric_value = None;
                self.type_of_expression(initializer)
            } else if let Some(value) = next_numeric_value {
                next_numeric_value = Some(value + 1.0);
                let value = Value::Number(Number::new(value));
                let member_type = self.enum_constant_type(&value);
                resolved_values.insert(name.clone(), value.clone());
                self.record_enum_constant(*member_id, &value);
                member_type
            } else {
                self.error(*member_id, 1061, std::iter::empty());
                self.result.types.number()
            };
            if let Some(symbol) = self.bindings.node_symbols.get(member_id).copied() {
                self.result.symbol_types.insert(symbol, member_type);
            }
            properties.insert(name, member_type);
        }
        let enum_type = self.result.types.alloc(TypeKind::Object(ObjectType {
            properties: properties.clone(),
            optional_properties: BTreeSet::new(),
            readonly_properties: properties.keys().cloned().collect(),
            getter_properties: BTreeSet::new(),
            setter_properties: BTreeSet::new(),
        }));
        for member_type in properties.values() {
            self.enum_member_owners.insert(*member_type, enum_type);
        }
        self.enum_types.insert(enum_type);
        if is_const {
            self.const_enum_types.insert(enum_type);
        }
        enum_type
    }

    fn evaluate_enum_initializer(
        &mut self,
        initializer: NodeId,
        is_const: bool,
        enum_name: &str,
        member_names: &BTreeSet<String>,
        resolved_values: &BTreeMap<String, Value>,
    ) -> Option<Value> {
        if is_const && !is_const_enum_expression(self.arena, initializer) {
            self.error(initializer, 2474, std::iter::empty());
            return None;
        }
        let mut forward_reference = false;
        let evaluation = evaluate_with(self.arena, initializer, &mut |reference| {
            let Some(reference_name) = enum_member_reference_name(self.arena, reference, enum_name)
            else {
                return Evaluation::unknown(UnknownReason::UnresolvedEntity(reference));
            };
            if let Some(value) = resolved_values.get(&reference_name) {
                Evaluation::known(value.clone())
            } else {
                forward_reference |= member_names.contains(&reference_name);
                Evaluation::unknown(UnknownReason::UnresolvedEntity(reference))
            }
        });
        match evaluation.outcome {
            EvaluationOutcome::Value(Value::Number(value)) if value.is_nan() => {
                if is_const {
                    self.error(initializer, 2478, std::iter::empty());
                }
                None
            }
            EvaluationOutcome::Value(Value::Number(value)) if value.is_infinite() => {
                if is_const {
                    self.error(initializer, 2477, std::iter::empty());
                }
                None
            }
            EvaluationOutcome::Value(value @ (Value::Number(_) | Value::String(_))) => Some(value),
            _ if is_const && forward_reference => {
                self.error(initializer, 2651, std::iter::empty());
                None
            }
            _ if is_const => {
                self.error(initializer, 2474, std::iter::empty());
                None
            }
            _ => None,
        }
    }

    fn enum_constant_type(&mut self, value: &Value) -> TypeId {
        match value {
            Value::Number(value) => self
                .result
                .types
                .alloc(TypeKind::NumberLiteral(value.to_string())),
            Value::String(value) => self
                .result
                .types
                .alloc(TypeKind::StringLiteral(value.clone())),
            _ => unreachable!("enum constants are numeric or string values"),
        }
    }

    fn record_enum_constant(&mut self, member: NodeId, value: &Value) {
        let value = match value {
            Value::Number(value) => EnumConstantValue::Number(value.value()),
            Value::String(value) => EnumConstantValue::String(value.clone()),
            _ => return,
        };
        self.result.enum_member_values.insert(member, value);
    }

    fn record_const_enum_access(&mut self, node: NodeId, receiver: TypeId, value: TypeId) {
        if !self.const_enum_types.contains(&receiver) {
            return;
        }
        let constant = match &self
            .result
            .types
            .get(value)
            .expect("expression type originates from arena")
            .kind
        {
            TypeKind::NumberLiteral(value) => {
                value.parse::<f64>().ok().map(EnumConstantValue::Number)
            }
            TypeKind::StringLiteral(value) => Some(EnumConstantValue::String(value.clone())),
            _ => None,
        };
        if let Some(constant) = constant {
            self.result.enum_access_values.insert(node, constant);
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
                let mut terminated = false;
                for statement in &data.statements.nodes {
                    if terminated && self.options.allow_unreachable_code == Some(false) {
                        self.error(*statement, 7027, std::iter::empty());
                    }
                    self.check_node(*statement, expected_return, saw_return);
                    terminated |= self.statement_definitely_terminates(*statement);
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
                self.result.node_types.insert(node_id, inferred);
                if let Some(symbol) = self.bindings.node_symbols.get(&node_id) {
                    self.result.symbol_types.insert(*symbol, inferred);
                }
            }
            NodeData::CatchClause(data) => {
                if let Some(variable) = data.variable_declaration
                    && let Some(NodeData::VariableDeclaration(declaration)) =
                        self.arena.get(variable).map(|node| &node.data)
                {
                    let symbol = self
                        .bindings
                        .node_symbols
                        .get(&variable)
                        .copied()
                        .or(declaration.symbol)
                        .or(declaration.local_symbol);
                    if let Some(symbol) = symbol {
                        let type_id = if let Some(annotation) = declaration.type_ {
                            self.type_from_type_node(annotation)
                        } else if self.options.use_unknown_in_catch_variables {
                            self.result.types.unknown()
                        } else {
                            self.result.types.any()
                        };
                        self.result.node_types.insert(variable, type_id);
                        self.result.symbol_types.insert(symbol, type_id);
                    }
                }
                self.check_node(data.block, expected_return, saw_return);
            }
            NodeData::FunctionDeclaration(data) => {
                self.check_function(node_id, data);
            }
            NodeData::ClassDeclaration(data) => {
                let instance_type = self
                    .bindings
                    .node_symbols
                    .get(&node_id)
                    .and_then(|symbol| self.result.symbol_types.get(symbol))
                    .copied();
                if let Some(instance_type) = instance_type {
                    self.this_types.push(instance_type);
                }
                self.check_class_members(&data.members.nodes);
                self.check_class_abstract_members(data);
                if instance_type.is_some() {
                    self.this_types.pop();
                }
            }
            NodeData::IfStatement(data) => {
                self.type_of_expression(data.expression);
                let before = self.flow_types.clone();
                let then_narrowing = self.condition_narrowing(data.expression, true);
                self.narrowings.push(then_narrowing);
                self.check_node(data.then_statement, expected_return, saw_return);
                self.narrowings.pop();
                let then_flow = self.flow_types.clone();
                self.flow_types.clone_from(&before);
                if let Some(else_statement) = data.else_statement {
                    let else_narrowing = self.condition_narrowing(data.expression, false);
                    self.narrowings.push(else_narrowing);
                    self.check_node(else_statement, expected_return, saw_return);
                    self.narrowings.pop();
                }
                let else_flow = self.flow_types.clone();
                self.flow_types = self.join_flow_types(&then_flow, &else_flow);
                let then_terminates = self.statement_definitely_terminates(data.then_statement);
                let else_terminates = data
                    .else_statement
                    .is_some_and(|statement| self.statement_definitely_terminates(statement));
                if then_terminates && !else_terminates {
                    let narrowing = self.condition_narrowing(data.expression, false);
                    self.flow_types.extend(narrowing);
                } else if else_terminates && !then_terminates {
                    let narrowing = self.condition_narrowing(data.expression, true);
                    self.flow_types.extend(narrowing);
                }
            }
            NodeData::WhileStatement(data) => {
                self.type_of_expression(data.expression);
                let before = self.flow_types.clone();
                let narrowing = self.condition_narrowing(data.expression, true);
                self.narrowings.push(narrowing);
                self.check_node(data.statement, expected_return, saw_return);
                self.narrowings.pop();
                let after = self.flow_types.clone();
                self.flow_types = self.join_flow_types(&before, &after);
            }
            NodeData::ForStatement(data) => {
                if let Some(initializer) = data.initializer {
                    self.check_node(initializer, expected_return, saw_return);
                    self.type_of_expression(initializer);
                }
                if let Some(condition) = data.condition {
                    self.type_of_expression(condition);
                }
                let before = self.flow_types.clone();
                self.check_node(data.statement, expected_return, saw_return);
                if let Some(incrementor) = data.incrementor {
                    self.type_of_expression(incrementor);
                }
                let after = self.flow_types.clone();
                self.flow_types = self.join_flow_types(&before, &after);
            }
            NodeData::SwitchStatement(data) => {
                self.check_switch(data, expected_return, saw_return);
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

    fn join_flow_types(
        &mut self,
        left: &HashMap<SymbolId, TypeId>,
        right: &HashMap<SymbolId, TypeId>,
    ) -> HashMap<SymbolId, TypeId> {
        let mut symbols = left.keys().chain(right.keys()).copied().collect::<Vec<_>>();
        symbols.sort_by_key(|symbol| symbol.0);
        symbols.dedup();
        symbols
            .into_iter()
            .map(|symbol| {
                let original = self
                    .result
                    .symbol_types
                    .get(&symbol)
                    .copied()
                    .unwrap_or_else(|| self.result.types.any());
                let left = left.get(&symbol).copied().unwrap_or(original);
                let right = right.get(&symbol).copied().unwrap_or(original);
                (symbol, self.result.types.union([left, right]))
            })
            .collect()
    }

    fn statement_definitely_terminates(&self, statement: NodeId) -> bool {
        let Some(node) = self.arena.get(statement) else {
            return false;
        };
        match &node.data {
            NodeData::ReturnStatement(_) | NodeData::ThrowStatement(_) => true,
            NodeData::Block(block) => block
                .statements
                .nodes
                .iter()
                .any(|statement| self.statement_definitely_terminates(*statement)),
            NodeData::IfStatement(statement) => statement.else_statement.is_some_and(|other| {
                self.statement_definitely_terminates(statement.then_statement)
                    && self.statement_definitely_terminates(other)
            }),
            NodeData::WhileStatement(statement) => {
                self.expression_is_always_truthy(statement.expression)
            }
            NodeData::SwitchStatement(statement) => {
                let Some(NodeData::CaseBlock(block)) =
                    self.arena.get(statement.case_block).map(|node| &node.data)
                else {
                    return false;
                };
                let has_default = block.clauses.nodes.iter().any(|clause| {
                    self.arena
                        .get(*clause)
                        .is_some_and(|node| node.kind == SyntaxKind::DefaultClause)
                });
                (has_default || self.switch_is_exhaustive(statement))
                    && !block.clauses.nodes.is_empty()
                    && block.clauses.nodes.iter().all(|clause| {
                        let Some(NodeData::CaseOrDefaultClause(clause)) =
                            self.arena.get(*clause).map(|node| &node.data)
                        else {
                            return false;
                        };
                        clause
                            .statements
                            .nodes
                            .iter()
                            .any(|statement| self.statement_definitely_terminates(*statement))
                    })
            }
            _ => false,
        }
    }

    fn expression_is_always_truthy(&self, expression: NodeId) -> bool {
        let Some(node) = self.arena.get(expression) else {
            return false;
        };
        match &node.data {
            NodeData::KeywordExpression(_) => node.kind == SyntaxKind::TrueKeyword,
            NodeData::NumericLiteral(value) => value.text != "0",
            _ => false,
        }
    }

    fn switch_is_exhaustive(&self, statement: &ts_ast::SwitchStatementData) -> bool {
        let Some(subject) = self.result.node_types.get(&statement.expression).copied() else {
            return false;
        };
        let Some(NodeData::CaseBlock(block)) =
            self.arena.get(statement.case_block).map(|node| &node.data)
        else {
            return false;
        };
        let cases = block
            .clauses
            .nodes
            .iter()
            .filter_map(|clause| {
                let node = self.arena.get(*clause)?;
                if node.kind == SyntaxKind::DefaultClause {
                    return None;
                }
                let NodeData::CaseOrDefaultClause(clause) = &node.data else {
                    return None;
                };
                self.result.node_types.get(&clause.expression).copied()
            })
            .collect::<Vec<_>>();
        self.union_members(subject).iter().all(|member| {
            cases.iter().any(|case| {
                self.is_assignable(*member, *case) && self.is_assignable(*case, *member)
            })
        })
    }

    fn check_switch(
        &mut self,
        data: &ts_ast::SwitchStatementData,
        expected_return: Option<TypeId>,
        saw_return: &mut bool,
    ) {
        let subject_type = self.type_of_expression(data.expression);
        let subject = self.narrowing_subject(data.expression);
        let property_subject = self.property_narrowing_subject(data.expression);
        let Some(NodeData::CaseBlock(block)) = self
            .arena
            .get(data.case_block)
            .map(|node| node.data.clone())
        else {
            return;
        };
        let before = self.flow_types.clone();
        let mut exits = Vec::new();
        let mut case_types = Vec::new();
        let mut has_default = false;
        let clause_count = block.clauses.nodes.len();
        for (clause_index, clause_id) in block.clauses.nodes.into_iter().enumerate() {
            let Some(clause_node) = self.arena.get(clause_id).cloned() else {
                continue;
            };
            let NodeData::CaseOrDefaultClause(clause) = clause_node.data else {
                continue;
            };
            self.flow_types.clone_from(&before);
            let mut narrowing = HashMap::new();
            if clause_node.kind == SyntaxKind::DefaultClause {
                has_default = true;
            } else {
                let case_type = self.type_of_expression(clause.expression);
                case_types.push(case_type);
                if let Some(subject) = subject {
                    let narrowed = self.narrow_to_comparison(subject, case_type, true);
                    narrowing.insert(subject, narrowed);
                } else if let Some((subject, ref property)) = property_subject {
                    let narrowed = self.narrow_discriminant(subject, property, case_type, true);
                    narrowing.insert(subject, narrowed);
                }
            }
            self.narrowings.push(narrowing);
            let mut terminated = false;
            let statements = clause.statements.nodes;
            for statement in &statements {
                if terminated && self.options.allow_unreachable_code == Some(false) {
                    self.error(*statement, 7027, std::iter::empty());
                }
                self.check_node(*statement, expected_return, saw_return);
                terminated |= self.statement_definitely_terminates(*statement);
            }
            if self.options.no_fallthrough_cases_in_switch
                && clause_index + 1 < clause_count
                && !statements.is_empty()
                && !statements
                    .iter()
                    .any(|statement| self.statement_prevents_fallthrough(*statement))
            {
                self.error(clause_id, 7029, std::iter::empty());
            }
            self.narrowings.pop();
            exits.push(self.flow_types.clone());
        }
        let exhaustive = has_default
            || self.union_members(subject_type).iter().all(|member| {
                case_types.iter().any(|case| {
                    self.is_assignable(*member, *case) && self.is_assignable(*case, *member)
                })
            });
        if !exhaustive {
            exits.push(before.clone());
        }
        self.flow_types = exits
            .into_iter()
            .reduce(|left, right| self.join_flow_types(&left, &right))
            .unwrap_or(before);
    }

    fn statement_prevents_fallthrough(&self, statement: NodeId) -> bool {
        let Some(node) = self.arena.get(statement) else {
            return false;
        };
        matches!(
            node.kind,
            SyntaxKind::BreakStatement | SyntaxKind::ContinueStatement
        ) || self.statement_definitely_terminates(statement)
    }

    fn narrow_to_comparison(
        &mut self,
        subject: SymbolId,
        comparison: TypeId,
        include_match: bool,
    ) -> TypeId {
        let original = self.current_symbol_type(subject);
        let members = self.union_members(original);
        let filtered = members.into_iter().filter(|member| {
            let matches =
                self.is_assignable(*member, comparison) && self.is_assignable(comparison, *member);
            matches == include_match
        });
        self.result.types.union(filtered.collect::<Vec<_>>())
    }

    fn check_function(&mut self, node_id: NodeId, data: &ts_ast::FunctionDeclarationData) {
        self.check_function_overload_group(node_id);
        let function_type = self
            .bindings
            .node_symbols
            .get(&node_id)
            .and_then(|symbol| self.result.symbol_types.get(symbol))
            .copied()
            .unwrap_or_else(|| self.function_type(data));
        let signature = match &self.result.types.get(function_type).unwrap().kind {
            TypeKind::Function(function) => Some(function.clone()),
            TypeKind::Overload(_) => {
                let implementation = self.function_type(data);
                let TypeKind::Function(function) =
                    &self.result.types.get(implementation).unwrap().kind
                else {
                    unreachable!("function_type always creates a function type");
                };
                Some(function.clone())
            }
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
        let has_implicit_return = data
            .body
            .is_some_and(|body| !self.statement_definitely_terminates(body));
        let requires_value_return = !matches!(
            self.result.types.get(return_type).map(|value| &value.kind),
            Some(TypeKind::Any | TypeKind::Void | TypeKind::Undefined)
        );
        if has_implicit_return && requires_value_return {
            self.error(node_id, 2355, std::iter::empty());
        } else if has_implicit_return && saw_return && self.options.no_implicit_returns {
            self.error(data.name.unwrap_or(node_id), 7030, std::iter::empty());
        }
    }

    fn check_function_overload_group(&mut self, node_id: NodeId) {
        let Some(symbol) = self.bindings.node_symbols.get(&node_id).copied() else {
            return;
        };
        if !self.checked_overload_symbols.insert(symbol) {
            return;
        }
        let declarations = self
            .bindings
            .symbols
            .get(symbol)
            .map(|symbol| symbol.declarations.clone())
            .unwrap_or_default();
        let functions = declarations
            .into_iter()
            .filter_map(|declaration| {
                let NodeData::FunctionDeclaration(function) = &self.arena.get(declaration)?.data
                else {
                    return None;
                };
                Some((declaration, function.as_ref().clone()))
            })
            .collect::<Vec<_>>();

        if let Some((signature, _)) = functions.iter().rev().find(|(declaration, function)| {
            function.body.is_none() && !self.function_is_ambient(*declaration, function)
        }) {
            let immediately_following_implementation =
                self.next_statement(*signature).is_some_and(|next| {
                    self.bindings.node_symbols.get(&next) == Some(&symbol)
                        && matches!(
                            self.arena.get(next).map(|node| &node.data),
                            Some(NodeData::FunctionDeclaration(function)) if function.body.is_some()
                        )
                });
            if !immediately_following_implementation {
                let location = self
                    .arena
                    .get(*signature)
                    .and_then(|node| match &node.data {
                        NodeData::FunctionDeclaration(function) => function.name,
                        _ => None,
                    })
                    .unwrap_or(*signature);
                self.error(location, 2391, std::iter::empty());
            }
        }

        if self.options.no_implicit_any {
            for (declaration, function) in &functions {
                if function.body.is_none() && function.type_.is_none() {
                    let location = function.name.unwrap_or(*declaration);
                    let name = function
                        .name
                        .and_then(|name| self.property_name(name))
                        .unwrap_or_else(|| "function".into());
                    self.error(location, 7010, [name, "any".into()]);
                }
            }
        }
    }

    fn function_is_ambient(
        &self,
        declaration: NodeId,
        function: &ts_ast::FunctionDeclarationData,
    ) -> bool {
        if self.options.is_declaration_file
            || self.has_ast_modifier(function.modifiers.as_ref(), SyntaxKind::DeclareKeyword)
        {
            return true;
        }
        let mut parent = self.arena.get(declaration).and_then(|node| node.parent);
        while let Some(node_id) = parent {
            let Some(node) = self.arena.get(node_id) else {
                break;
            };
            if let NodeData::ModuleDeclaration(module) = &node.data
                && self.has_ast_modifier(module.modifiers.as_ref(), SyntaxKind::DeclareKeyword)
            {
                return true;
            }
            parent = node.parent;
        }
        false
    }

    fn next_statement(&self, declaration: NodeId) -> Option<NodeId> {
        let parent = self.arena.get(declaration)?.parent?;
        let statements = match &self.arena.get(parent)?.data {
            NodeData::SourceFile(source) => &source.statements.nodes,
            NodeData::ModuleBlock(block) => &block.statements.nodes,
            NodeData::Block(block) => &block.statements.nodes,
            _ => return None,
        };
        let index = statements
            .iter()
            .position(|statement| *statement == declaration)?;
        statements.get(index + 1).copied()
    }

    fn check_parameter(&mut self, parameter: NodeId) {
        let Some(NodeData::ParameterDeclaration(data)) =
            self.arena.get(parameter).map(|node| &node.data)
        else {
            return;
        };
        if self.options.no_implicit_any && data.type_.is_none() {
            let name = self
                .property_name(data.name)
                .unwrap_or_else(|| "parameter".into());
            self.error(parameter, 7006, [name, "any".into()]);
        }
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

    #[allow(clippy::too_many_lines)]
    fn object_type_from_members(&mut self, members: &[NodeId]) -> TypeId {
        let mut properties = BTreeMap::new();
        let mut optional_properties = BTreeSet::new();
        let mut readonly_properties = BTreeSet::new();
        let mut getter_properties = BTreeSet::new();
        let mut setter_properties = BTreeSet::new();
        for member in members {
            let Some(node) = self.arena.get(*member) else {
                continue;
            };
            match &node.data {
                NodeData::PropertyDeclaration(data) => {
                    if let Some(name) = self.property_name(data.name) {
                        let mut property_type = data
                            .type_
                            .map(|type_node| self.type_from_type_node(type_node))
                            .or_else(|| {
                                data.initializer.map(|value| self.type_of_expression(value))
                            })
                            .unwrap_or_else(|| self.result.types.any());
                        if self.is_question_token(data.postfix_token) {
                            optional_properties.insert(name.clone());
                            if !self.options.exact_optional_property_types {
                                let undefined = self.result.types.undefined();
                                property_type = self.result.types.union([property_type, undefined]);
                            }
                        }
                        if self
                            .has_ast_modifier(data.modifiers.as_ref(), SyntaxKind::ReadonlyKeyword)
                        {
                            readonly_properties.insert(name.clone());
                        }
                        properties.insert(name, property_type);
                    }
                }
                NodeData::PropertySignatureDeclaration(data) => {
                    if let Some(name) = self.property_name(data.name) {
                        let mut property_type = self.type_from_type_node(data.type_);
                        if self.is_question_token(data.postfix_token) {
                            optional_properties.insert(name.clone());
                            if !self.options.exact_optional_property_types {
                                let undefined = self.result.types.undefined();
                                property_type = self.result.types.union([property_type, undefined]);
                            }
                        }
                        if self
                            .has_ast_modifier(data.modifiers.as_ref(), SyntaxKind::ReadonlyKeyword)
                        {
                            readonly_properties.insert(name.clone());
                        }
                        properties.insert(name, property_type);
                    }
                }
                NodeData::MethodDeclaration(data) => {
                    for parameter in &data.parameters.nodes {
                        self.check_parameter(*parameter);
                    }
                    if let Some(name) = self.property_name(data.name) {
                        if name == "constructor" {
                            self.add_parameter_properties(
                                &data.parameters.nodes,
                                &mut properties,
                                &mut optional_properties,
                                &mut readonly_properties,
                            );
                            continue;
                        }
                        let method_type = self.signature_type(
                            &data.parameters.nodes,
                            data.type_,
                            data.type_parameters.as_ref(),
                        );
                        let optional = self.is_question_token(data.postfix_token);
                        if optional {
                            optional_properties.insert(name.clone());
                        }
                        self.insert_callable_property(&mut properties, name.clone(), method_type);
                        if optional && !self.options.exact_optional_property_types {
                            let method = properties[&name];
                            let undefined = self.result.types.undefined();
                            properties.insert(name, self.result.types.union([method, undefined]));
                        }
                    }
                }
                NodeData::ConstructorDeclaration(data) => {
                    self.add_parameter_properties(
                        &data.parameters.nodes,
                        &mut properties,
                        &mut optional_properties,
                        &mut readonly_properties,
                    );
                }
                NodeData::MethodSignatureDeclaration(data) => {
                    if let Some(name) = self.property_name(data.name) {
                        let method_type = self.signature_type(
                            &data.parameters.nodes,
                            data.type_,
                            data.type_parameters.as_ref(),
                        );
                        let optional = self.is_question_token(data.postfix_token);
                        if optional {
                            optional_properties.insert(name.clone());
                        }
                        self.insert_callable_property(&mut properties, name.clone(), method_type);
                        if optional && !self.options.exact_optional_property_types {
                            let method = properties[&name];
                            let undefined = self.result.types.undefined();
                            properties.insert(name, self.result.types.union([method, undefined]));
                        }
                    }
                }
                NodeData::GetAccessorDeclaration(data) => {
                    if let Some(name) = self.property_name(data.name) {
                        let property_type = self.getter_property_type(data.type_, data.body);
                        self.result.node_types.insert(*member, property_type);
                        properties.insert(name.clone(), property_type);
                        getter_properties.insert(name);
                    }
                }
                NodeData::SetAccessorDeclaration(data) => {
                    if let Some(name) = self.property_name(data.name) {
                        setter_properties.insert(name.clone());
                        let type_node = data
                            .parameters
                            .nodes
                            .first()
                            .and_then(|parameter| self.arena.get(*parameter))
                            .and_then(|parameter| match &parameter.data {
                                NodeData::ParameterDeclaration(parameter) => parameter.type_,
                                _ => None,
                            });
                        let property_type = if let Some(type_node) = type_node {
                            self.type_from_type_node(type_node)
                        } else {
                            self.result.types.any()
                        };
                        self.result.node_types.insert(*member, property_type);
                        if !getter_properties.contains(&name) {
                            properties.insert(name, property_type);
                        }
                    }
                }
                _ => {}
            }
        }
        self.result.types.alloc(TypeKind::Object(ObjectType {
            properties,
            optional_properties,
            readonly_properties,
            getter_properties,
            setter_properties,
        }))
    }

    fn add_parameter_properties(
        &mut self,
        parameters: &[NodeId],
        properties: &mut BTreeMap<String, TypeId>,
        optional_properties: &mut BTreeSet<String>,
        readonly_properties: &mut BTreeSet<String>,
    ) {
        for parameter in parameters {
            let Some(NodeData::ParameterDeclaration(data)) =
                self.arena.get(*parameter).map(|node| &node.data)
            else {
                continue;
            };
            let is_property = data.modifiers.as_ref().is_some_and(|modifiers| {
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
            });
            let Some(name) = is_property.then(|| self.property_name(data.name)).flatten() else {
                continue;
            };
            let mut property_type = data
                .type_
                .map(|type_node| self.type_from_type_node(type_node))
                .or_else(|| {
                    data.initializer
                        .map(|initializer| self.type_of_expression(initializer))
                })
                .unwrap_or_else(|| self.result.types.any());
            if self.is_question_token(data.question_token) {
                optional_properties.insert(name.clone());
                if !self.options.exact_optional_property_types {
                    let undefined = self.result.types.undefined();
                    property_type = self.result.types.union([property_type, undefined]);
                }
            }
            if self.has_ast_modifier(data.modifiers.as_ref(), SyntaxKind::ReadonlyKeyword) {
                readonly_properties.insert(name.clone());
            }
            properties.insert(name, property_type);
        }
    }

    fn is_question_token(&self, token: Option<NodeId>) -> bool {
        token
            .and_then(|token| self.arena.get(token))
            .is_some_and(|token| token.kind == SyntaxKind::QuestionToken)
    }

    fn has_ast_modifier(&self, modifiers: Option<&ts_ast::ModifierList>, kind: SyntaxKind) -> bool {
        modifiers.is_some_and(|modifiers| {
            modifiers.list.nodes.iter().any(|modifier| {
                self.arena
                    .get(*modifier)
                    .is_some_and(|modifier| modifier.kind == kind)
            })
        })
    }

    fn insert_callable_property(
        &mut self,
        properties: &mut BTreeMap<String, TypeId>,
        name: String,
        method_type: TypeId,
    ) {
        let TypeKind::Function(signature) =
            self.result.types.get(method_type).unwrap().kind.clone()
        else {
            properties.insert(name, method_type);
            return;
        };
        let Some(existing) = properties.get(&name).copied() else {
            properties.insert(name, method_type);
            return;
        };
        let mut signatures = match self.result.types.get(existing).unwrap().kind.clone() {
            TypeKind::Function(existing) => vec![existing],
            TypeKind::Overload(existing) => existing,
            _ => {
                properties.insert(name, method_type);
                return;
            }
        };
        signatures.push(signature);
        let overload = self.result.types.alloc(TypeKind::Overload(signatures));
        properties.insert(name, overload);
    }

    fn declared_object_type(
        &mut self,
        type_parameters: Option<&ts_ast::NodeList>,
        heritage_clauses: Option<&ts_ast::NodeList>,
        members: &[NodeId],
        arguments: &[TypeId],
    ) -> TypeId {
        let mut scope = HashMap::new();
        if let Some(parameters) = type_parameters {
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
                    self.result.types.alloc(TypeKind::TypeParameter {
                        name: name.clone(),
                        constraint: None,
                    })
                });
                scope.insert(name, type_id);
            }
        }
        self.type_parameter_scopes.push(scope);
        let mut properties = BTreeMap::new();
        let mut optional_properties = BTreeSet::new();
        let mut readonly_properties = BTreeSet::new();
        let mut getter_properties = BTreeSet::new();
        let mut setter_properties = BTreeSet::new();
        if let Some(clauses) = heritage_clauses {
            for clause in &clauses.nodes {
                let Some(NodeData::HeritageClause(clause)) =
                    self.arena.get(*clause).map(|node| &node.data)
                else {
                    continue;
                };
                for heritage_type in &clause.types.nodes {
                    let Some(NodeData::ExpressionWithTypeArguments(heritage)) =
                        self.arena.get(*heritage_type).map(|node| &node.data)
                    else {
                        continue;
                    };
                    let Some(name) = self.property_name(heritage.expression) else {
                        continue;
                    };
                    let arguments = heritage
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
                    let Some(symbol) = self.resolve_identifier(heritage.expression, &name) else {
                        continue;
                    };
                    let Some(base) = self.instantiate_declared_object(symbol, &arguments) else {
                        continue;
                    };
                    if let TypeKind::Object(base) =
                        self.result.types.get(base).unwrap().kind.clone()
                    {
                        properties.extend(base.properties);
                        optional_properties.extend(base.optional_properties);
                        readonly_properties.extend(base.readonly_properties);
                        getter_properties.extend(base.getter_properties);
                        setter_properties.extend(base.setter_properties);
                    }
                }
            }
        }
        let own = self.object_type_from_members(members);
        if let TypeKind::Object(own) = self.result.types.get(own).unwrap().kind.clone() {
            properties.extend(own.properties);
            optional_properties.extend(own.optional_properties);
            readonly_properties.extend(own.readonly_properties);
            getter_properties.extend(own.getter_properties);
            setter_properties.extend(own.setter_properties);
        }
        let result = self.result.types.alloc(TypeKind::Object(ObjectType {
            properties,
            optional_properties,
            readonly_properties,
            getter_properties,
            setter_properties,
        }));
        self.type_parameter_scopes.pop();
        result
    }

    fn instantiate_declared_object(
        &mut self,
        symbol: SymbolId,
        arguments: &[TypeId],
    ) -> Option<TypeId> {
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
                NodeData::ClassDeclaration(data) => {
                    Some(DeclaredObject::Class(data.as_ref().clone()))
                }
                NodeData::InterfaceDeclaration(data) => {
                    Some(DeclaredObject::Interface(data.as_ref().clone()))
                }
                _ => None,
            })?;
        self.alias_stack.push(symbol);
        let result = match declaration {
            DeclaredObject::Class(data) => self.declared_object_type(
                data.type_parameters.as_ref(),
                data.heritage_clauses.as_ref(),
                &data.members.nodes,
                arguments,
            ),
            DeclaredObject::Interface(data) => self.declared_object_type(
                data.type_parameters.as_ref(),
                data.heritage_clauses.as_ref(),
                &data.members.nodes,
                arguments,
            ),
        };
        self.alias_stack.pop();
        Some(result)
    }

    fn getter_property_type(&mut self, annotation: Option<NodeId>, body: Option<NodeId>) -> TypeId {
        if let Some(annotation) = annotation {
            return self.type_from_type_node(annotation);
        }
        let Some(NodeData::Block(block)) = body
            .and_then(|body| self.arena.get(body))
            .map(|node| &node.data)
        else {
            return self.result.types.any();
        };
        let expressions = block
            .statements
            .nodes
            .iter()
            .filter_map(|statement| {
                let NodeData::ReturnStatement(statement) = &self.arena.get(*statement)?.data else {
                    return None;
                };
                statement.expression
            })
            .collect::<Vec<_>>();
        if expressions.is_empty() {
            return self.result.types.any();
        }
        let types = expressions
            .into_iter()
            .map(|expression| {
                let type_id = self.type_of_expression(expression);
                self.widen_literal(type_id)
            })
            .collect::<Vec<_>>();
        self.result.types.union(types)
    }

    fn object_literal_type(
        &mut self,
        object: &ts_ast::ObjectLiteralExpressionData,
        contextual_type: Option<TypeId>,
    ) -> TypeId {
        let object_type = self.collect_object_literal_properties(object, contextual_type);
        let mut properties = object_type.properties.clone();
        let readonly_properties = object_type.readonly_properties.clone();
        let getter_properties = object_type.getter_properties.clone();
        let setter_properties = object_type.setter_properties.clone();
        let type_id = self.result.types.alloc(TypeKind::Object(object_type));
        self.this_types.push(type_id);
        for property in &object.properties.nodes {
            let Some(node) = self.arena.get(*property).cloned() else {
                continue;
            };
            match &node.data {
                NodeData::GetAccessorDeclaration(data) => {
                    self.check_object_literal_getter(*property, data, &mut properties);
                }
                NodeData::SetAccessorDeclaration(data) => {
                    let property_type = self.object_literal_setter_type(data);
                    self.result.node_types.insert(*property, property_type);
                    let local_scope = self.parameter_scope(&data.parameters.nodes);
                    self.local_scopes.push(local_scope);
                    let mut saw_return = false;
                    if let Some(body) = data.body {
                        self.check_node(body, None, &mut saw_return);
                    }
                    self.local_scopes.pop();
                }
                _ => {}
            }
        }
        self.this_types.pop();
        self.result.types.types[type_id.index()].kind = TypeKind::Object(ObjectType {
            properties,
            readonly_properties,
            getter_properties,
            setter_properties,
            ..ObjectType::default()
        });
        type_id
    }

    fn collect_object_literal_properties(
        &mut self,
        object: &ts_ast::ObjectLiteralExpressionData,
        contextual_type: Option<TypeId>,
    ) -> ObjectType {
        let contextual_object =
            contextual_type.and_then(|type_id| match &self.result.types.get(type_id)?.kind {
                TypeKind::Object(object) => Some(object.clone()),
                _ => None,
            });
        let mut properties = BTreeMap::new();
        let mut getter_properties = BTreeSet::new();
        let mut setter_properties = BTreeSet::new();
        for property in &object.properties.nodes {
            let Some(node) = self.arena.get(*property).cloned() else {
                continue;
            };
            match &node.data {
                NodeData::PropertyAssignment(data) => {
                    let Some(name) = self.property_name(data.name) else {
                        continue;
                    };
                    let expected = contextual_object
                        .as_ref()
                        .and_then(|object| object.properties.get(&name))
                        .copied();
                    if expected.is_none() && contextual_object.is_some() {
                        self.error(
                            *property,
                            2353,
                            [
                                name.clone(),
                                self.result.types.display(
                                    contextual_type.expect("contextual object has a type"),
                                ),
                            ],
                        );
                    }
                    let actual = self.type_of_expression_context(data.initializer, expected);
                    if let Some(expected) = expected
                        && !self.is_assignable(actual, expected)
                        && !(self.options.exact_optional_property_types
                            && contextual_object.as_ref().is_some_and(|object| {
                                object.optional_properties.contains(&name)
                                    && self.type_includes_undefined(actual)
                            }))
                    {
                        self.assignability_error(*property, actual, expected);
                    }
                    properties.insert(name, actual);
                }
                NodeData::GetAccessorDeclaration(data) => {
                    let Some(name) = self.property_name(data.name) else {
                        continue;
                    };
                    let type_id = match data.type_ {
                        Some(annotation) => self.type_from_type_node(annotation),
                        None => self.result.types.any(),
                    };
                    properties.insert(name.clone(), type_id);
                    getter_properties.insert(name);
                }
                NodeData::SetAccessorDeclaration(data) => {
                    let Some(name) = self.property_name(data.name) else {
                        continue;
                    };
                    let type_id = self.object_literal_setter_type(data);
                    properties.entry(name.clone()).or_insert(type_id);
                    setter_properties.insert(name);
                }
                _ => {}
            }
        }
        ObjectType {
            properties,
            readonly_properties: getter_properties
                .difference(&setter_properties)
                .cloned()
                .collect(),
            getter_properties,
            setter_properties,
            ..ObjectType::default()
        }
    }

    fn check_object_literal_getter(
        &mut self,
        getter_node: NodeId,
        getter: &ts_ast::GetAccessorDeclarationData,
        properties: &mut BTreeMap<String, TypeId>,
    ) {
        let Some(name) = self.property_name(getter.name) else {
            return;
        };
        let expected = match getter.type_ {
            Some(annotation) => self.type_from_type_node(annotation),
            None => self.result.types.any(),
        };
        let local_scope = self.parameter_scope(&getter.parameters.nodes);
        self.local_scopes.push(local_scope);
        let diagnostics_start = self.result.diagnostics.len();
        let mut saw_return = false;
        if let Some(body) = getter.body {
            self.check_node(body, Some(expected), &mut saw_return);
        }
        self.local_scopes.pop();
        if getter.type_.is_some() {
            self.result.node_types.insert(getter_node, expected);
            properties.insert(name, expected);
            return;
        }
        let returns = getter
            .body
            .into_iter()
            .flat_map(|body| self.getter_return_expressions(body))
            .collect::<Vec<_>>();
        let inferred = if returns.is_empty() {
            self.result.types.any()
        } else {
            let types = returns
                .into_iter()
                .map(|expression| {
                    let type_id = self.type_of_expression(expression);
                    self.widen_literal(type_id)
                })
                .collect::<Vec<_>>();
            self.result.types.union(types)
        };
        if self.options.no_implicit_any
            && inferred == self.result.types.any()
            && getter
                .body
                .is_some_and(|body| self.subtree_contains_kind(body, SyntaxKind::ThisKeyword))
        {
            let message = message_by_code(7023).expect("checker diagnostic is in catalog");
            self.result.diagnostics.insert(
                diagnostics_start,
                CheckDiagnostic {
                    node: getter.name,
                    diagnostic: Diagnostic::with_arguments(message, [name.clone()]),
                },
            );
        }
        self.result.node_types.insert(getter_node, inferred);
        properties.insert(name, inferred);
    }

    fn object_literal_setter_type(
        &mut self,
        setter: &ts_ast::SetAccessorDeclarationData,
    ) -> TypeId {
        let annotation = setter
            .parameters
            .nodes
            .first()
            .and_then(|parameter| self.arena.get(*parameter))
            .and_then(|parameter| match &parameter.data {
                NodeData::ParameterDeclaration(parameter) => parameter.type_,
                _ => None,
            });
        match annotation {
            Some(annotation) => self.type_from_type_node(annotation),
            None => self.result.types.any(),
        }
    }

    fn class_expression_type(&mut self, class: &ts_ast::ClassExpressionData) -> TypeId {
        let instance_type = self.declared_object_type(
            class.type_parameters.as_ref(),
            class.heritage_clauses.as_ref(),
            &class.members.nodes,
            &[],
        );
        self.this_types.push(instance_type);
        self.check_class_members(&class.members.nodes);
        self.this_types.pop();
        let signature = self.class_constructor_signature(&class.members.nodes, instance_type);
        let constructor_type = self.result.types.alloc(TypeKind::Constructor(signature));
        if let Some(symbol) = class.symbol.or(class.local_symbol) {
            self.result.symbol_types.insert(symbol, constructor_type);
        }
        constructor_type
    }

    fn class_constructor_signature(
        &mut self,
        members: &[NodeId],
        instance_type: TypeId,
    ) -> FunctionType {
        for member in members {
            let Some(node) = self.arena.get(*member).cloned() else {
                continue;
            };
            let parameters = match &node.data {
                NodeData::ConstructorDeclaration(constructor) => Some(&constructor.parameters),
                NodeData::MethodDeclaration(method)
                    if self.property_name(method.name).as_deref() == Some("constructor") =>
                {
                    Some(&method.parameters)
                }
                _ => None,
            };
            let Some(parameters) = parameters else {
                continue;
            };
            let signature_type = self.signature_type(&parameters.nodes, None, None);
            let Some(TypeKind::Function(mut signature)) = self
                .result
                .types
                .get(signature_type)
                .map(|type_| type_.kind.clone())
            else {
                continue;
            };
            signature.return_type = instance_type;
            return signature;
        }
        FunctionType {
            parameters: Vec::new(),
            return_type: instance_type,
            parameters_optional: false,
        }
    }

    fn getter_return_expressions(&self, body: NodeId) -> Vec<NodeId> {
        let Some(NodeData::Block(block)) = self.arena.get(body).map(|node| &node.data) else {
            return Vec::new();
        };
        block
            .statements
            .nodes
            .iter()
            .filter_map(|statement| {
                let NodeData::ReturnStatement(statement) = &self.arena.get(*statement)?.data else {
                    return None;
                };
                statement.expression
            })
            .collect()
    }

    fn subtree_contains_kind(&self, root: NodeId, kind: SyntaxKind) -> bool {
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            if self.arena.get(node).is_some_and(|node| node.kind == kind) {
                return true;
            }
            if let Some(children) = self.children.get(&node) {
                pending.extend(children.iter().copied());
            }
        }
        false
    }

    fn check_class_abstract_members(&mut self, class: &ts_ast::ClassDeclarationData) {
        let class_is_abstract =
            self.has_ast_modifier(class.modifiers.as_ref(), SyntaxKind::AbstractKeyword);
        let class_name = class
            .name
            .and_then(|name| self.property_name(name))
            .unwrap_or_else(|| "class".into());
        if let Some((base_name, base)) = self.direct_base_class(class) {
            self.check_base_member_types(
                &class_name,
                &base_name,
                &base.members.nodes,
                &class.members.nodes,
            );
            if !class_is_abstract {
                self.check_missing_abstract_members(class, &class_name, &base_name, &base);
            }
        }
        if !class_is_abstract {
            for member in &class.members.nodes {
                let Some(node) = self.arena.get(*member) else {
                    continue;
                };
                if matches!(node.data, NodeData::PropertyDeclaration(_))
                    && self.member_is_abstract(*member)
                {
                    self.error(
                        self.member_modifier(*member, SyntaxKind::AbstractKeyword)
                            .unwrap_or(*member),
                        1253,
                        std::iter::empty(),
                    );
                }
            }
        }
        self.check_accessor_abstract_consistency(&class.members.nodes);
    }

    fn check_missing_abstract_members(
        &mut self,
        class: &ts_ast::ClassDeclarationData,
        class_name: &str,
        base_name: &str,
        base: &ts_ast::ClassDeclarationData,
    ) {
        let concrete = class
            .members
            .nodes
            .iter()
            .filter(|member| !self.member_is_abstract(**member))
            .filter_map(|member| self.class_member_name(*member))
            .collect::<BTreeSet<_>>();
        let mut missing = Vec::new();
        for member in &base.members.nodes {
            if self.member_is_abstract(*member)
                && let Some(name) = self.class_member_name(*member)
                && !concrete.contains(&name)
                && !missing.contains(&name)
            {
                missing.push(name);
            }
        }
        if missing.is_empty() {
            return;
        }
        let Some(location) = class.name.or_else(|| class.members.nodes.first().copied()) else {
            return;
        };
        if missing.len() == 1 {
            self.error(
                location,
                2515,
                [
                    class_name.to_owned(),
                    format!("'{}'", missing[0]),
                    base_name.to_owned(),
                ],
            );
        } else {
            self.error(
                location,
                2654,
                [
                    class_name.to_owned(),
                    base_name.to_owned(),
                    missing
                        .iter()
                        .map(|name| format!("'{name}'"))
                        .collect::<Vec<_>>()
                        .join(", "),
                ],
            );
        }
    }

    fn direct_base_class(
        &self,
        class: &ts_ast::ClassDeclarationData,
    ) -> Option<(String, ts_ast::ClassDeclarationData)> {
        let clauses = class.heritage_clauses.as_ref()?;
        for clause in &clauses.nodes {
            let NodeData::HeritageClause(clause) = &self.arena.get(*clause)?.data else {
                continue;
            };
            if clause.token != SyntaxKind::ExtendsKeyword {
                continue;
            }
            let heritage = clause.types.nodes.first()?;
            let NodeData::ExpressionWithTypeArguments(heritage) = &self.arena.get(*heritage)?.data
            else {
                continue;
            };
            let name = self.property_name(heritage.expression)?;
            let symbol = self.resolve_identifier(heritage.expression, &name)?;
            let declaration = self
                .bindings
                .symbols
                .get(symbol)?
                .declarations
                .iter()
                .find_map(|declaration| {
                    let NodeData::ClassDeclaration(class) = &self.arena.get(*declaration)?.data
                    else {
                        return None;
                    };
                    Some(class.as_ref().clone())
                })?;
            return Some((name, declaration));
        }
        None
    }

    fn check_base_member_types(
        &mut self,
        class_name: &str,
        base_name: &str,
        base_members: &[NodeId],
        members: &[NodeId],
    ) {
        let base_types = self.class_member_types(base_members);
        let member_types = self.class_member_types(members);
        for member in members {
            let Some(name) = self.class_member_name(*member) else {
                continue;
            };
            let (Some(actual), Some(expected)) = (
                member_types.get(&name).copied(),
                base_types.get(&name).copied(),
            ) else {
                continue;
            };
            if !self.is_assignable(actual, expected) {
                let location = self.class_member_name_node(*member).unwrap_or(*member);
                self.error(
                    location,
                    2416,
                    [name, class_name.to_owned(), base_name.to_owned()],
                );
            }
        }
    }

    fn class_member_types(&mut self, members: &[NodeId]) -> BTreeMap<String, TypeId> {
        let mut properties = BTreeMap::new();
        for member in members {
            let Some(node) = self.arena.get(*member).cloned() else {
                continue;
            };
            match &node.data {
                NodeData::PropertyDeclaration(property) => {
                    let Some(name) = self.property_name(property.name) else {
                        continue;
                    };
                    let inferred = property
                        .type_
                        .map(|type_node| self.type_from_type_node(type_node))
                        .or_else(|| {
                            property
                                .initializer
                                .map(|value| self.type_of_expression(value))
                        });
                    let type_id = match inferred {
                        Some(type_id) => self.widen_literal(type_id),
                        None => self.result.types.any(),
                    };
                    properties.insert(name, type_id);
                }
                NodeData::MethodDeclaration(method) => {
                    if let Some(name) = self.property_name(method.name) {
                        let type_id = self.signature_type(
                            &method.parameters.nodes,
                            method.type_,
                            method.type_parameters.as_ref(),
                        );
                        properties.insert(name, type_id);
                    }
                }
                NodeData::GetAccessorDeclaration(accessor) => {
                    if let Some(name) = self.property_name(accessor.name) {
                        let type_id = self.getter_property_type(accessor.type_, accessor.body);
                        properties.insert(name, type_id);
                    }
                }
                NodeData::SetAccessorDeclaration(accessor) => {
                    let Some(name) = self.property_name(accessor.name) else {
                        continue;
                    };
                    if properties.contains_key(&name) {
                        continue;
                    }
                    let annotation = accessor
                        .parameters
                        .nodes
                        .first()
                        .and_then(|parameter| self.arena.get(*parameter))
                        .and_then(|parameter| match &parameter.data {
                            NodeData::ParameterDeclaration(parameter) => parameter.type_,
                            _ => None,
                        });
                    let type_id = match annotation {
                        Some(type_node) => self.type_from_type_node(type_node),
                        None => self.result.types.any(),
                    };
                    properties.insert(name, type_id);
                }
                _ => {}
            }
        }
        properties
    }

    fn check_accessor_abstract_consistency(&mut self, members: &[NodeId]) {
        let mut accessors = BTreeMap::<String, Vec<(NodeId, bool)>>::new();
        for member in members {
            let Some(node) = self.arena.get(*member) else {
                continue;
            };
            let name = match &node.data {
                NodeData::GetAccessorDeclaration(accessor) => self.property_name(accessor.name),
                NodeData::SetAccessorDeclaration(accessor) => self.property_name(accessor.name),
                _ => None,
            };
            if let Some(name) = name {
                accessors
                    .entry(name)
                    .or_default()
                    .push((*member, self.member_is_abstract(*member)));
            }
        }
        for declarations in accessors.values() {
            let has_abstract = declarations.iter().any(|(_, abstract_)| *abstract_);
            let has_concrete = declarations.iter().any(|(_, abstract_)| !abstract_);
            if has_abstract && has_concrete {
                for (member, _) in declarations {
                    self.error(
                        self.class_member_name_node(*member).unwrap_or(*member),
                        2676,
                        std::iter::empty(),
                    );
                }
            }
        }
    }

    fn member_is_abstract(&self, member: NodeId) -> bool {
        let modifiers = match &self.arena.get(member).map(|node| &node.data) {
            Some(NodeData::PropertyDeclaration(member)) => member.modifiers.as_ref(),
            Some(NodeData::MethodDeclaration(member)) => member.modifiers.as_ref(),
            Some(NodeData::GetAccessorDeclaration(member)) => member.modifiers.as_ref(),
            Some(NodeData::SetAccessorDeclaration(member)) => member.modifiers.as_ref(),
            _ => None,
        };
        self.has_ast_modifier(modifiers, SyntaxKind::AbstractKeyword)
    }

    fn member_modifier(&self, member: NodeId, kind: SyntaxKind) -> Option<NodeId> {
        let modifiers = match &self.arena.get(member)?.data {
            NodeData::PropertyDeclaration(member) => member.modifiers.as_ref(),
            NodeData::MethodDeclaration(member) => member.modifiers.as_ref(),
            NodeData::GetAccessorDeclaration(member) => member.modifiers.as_ref(),
            NodeData::SetAccessorDeclaration(member) => member.modifiers.as_ref(),
            _ => None,
        }?;
        modifiers.list.nodes.iter().copied().find(|modifier| {
            self.arena
                .get(*modifier)
                .is_some_and(|modifier| modifier.kind == kind)
        })
    }

    fn class_member_name_node(&self, member: NodeId) -> Option<NodeId> {
        match &self.arena.get(member)?.data {
            NodeData::PropertyDeclaration(member) => Some(member.name),
            NodeData::MethodDeclaration(member) => Some(member.name),
            NodeData::GetAccessorDeclaration(member) => Some(member.name),
            NodeData::SetAccessorDeclaration(member) => Some(member.name),
            _ => None,
        }
    }

    fn class_member_name(&self, member: NodeId) -> Option<String> {
        self.class_member_name_node(member)
            .and_then(|name| self.property_name(name))
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
                NodeData::ConstructorDeclaration(data) => {
                    for parameter in &data.parameters.nodes {
                        self.check_parameter(*parameter);
                    }
                    let local_scope = self.parameter_scope(&data.parameters.nodes);
                    self.local_scopes.push(local_scope);
                    let mut saw_return = false;
                    if let Some(body) = data.body {
                        self.check_node(body, None, &mut saw_return);
                    }
                    self.local_scopes.pop();
                }
                NodeData::GetAccessorDeclaration(data) => {
                    if !data.parameters.nodes.is_empty() {
                        self.error(*member, 1054, std::iter::empty());
                    }
                    let return_type = if let Some(type_node) = data.type_ {
                        self.type_from_type_node(type_node)
                    } else {
                        self.result.types.any()
                    };
                    let local_scope = self.parameter_scope(&data.parameters.nodes);
                    self.local_scopes.push(local_scope);
                    let mut saw_return = false;
                    if let Some(body) = data.body {
                        self.check_node(body, Some(return_type), &mut saw_return);
                    }
                    self.local_scopes.pop();
                }
                NodeData::SetAccessorDeclaration(data) => {
                    if data.parameters.nodes.len() != 1 {
                        self.error(*member, 1049, std::iter::empty());
                    }
                    if data.type_.is_some() {
                        self.error(*member, 1095, std::iter::empty());
                    }
                    for parameter_id in &data.parameters.nodes {
                        if let Some(NodeData::ParameterDeclaration(parameter)) =
                            self.arena.get(*parameter_id).map(|node| &node.data)
                        {
                            if parameter.question_token.is_some() {
                                self.error(*parameter_id, 1051, std::iter::empty());
                            }
                            if parameter.initializer.is_some() {
                                self.error(*parameter_id, 1052, std::iter::empty());
                            }
                            if parameter.dot_dot_dot_token.is_some() {
                                self.error(*parameter_id, 1053, std::iter::empty());
                            }
                        }
                        self.check_parameter(*parameter_id);
                    }
                    let local_scope = self.parameter_scope(&data.parameters.nodes);
                    self.local_scopes.push(local_scope);
                    let mut saw_return = false;
                    if let Some(body) = data.body {
                        self.check_node(body, None, &mut saw_return);
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

    #[allow(clippy::too_many_lines)]
    fn condition_narrowing(
        &mut self,
        expression: NodeId,
        truthy: bool,
    ) -> HashMap<SymbolId, TypeId> {
        if let Some(NodeData::ParenthesizedExpression(parenthesized)) =
            self.arena.get(expression).map(|node| &node.data)
        {
            return self.condition_narrowing(parenthesized.expression, truthy);
        }
        if let Some(NodeData::PrefixUnaryExpression(prefix)) =
            self.arena.get(expression).map(|node| &node.data)
            && prefix.operator == SyntaxKind::ExclamationToken
        {
            return self.condition_narrowing(prefix.operand, !truthy);
        }
        let mut result = HashMap::new();
        if let Some(subject) = self.narrowing_subject(expression) {
            let original = self.current_symbol_type(subject);
            let narrowed = self.narrow_truthiness(original, truthy);
            result.insert(subject, narrowed);
            return result;
        }
        let Some(NodeData::BinaryExpression(binary)) =
            self.arena.get(expression).map(|node| node.data.clone())
        else {
            return result;
        };
        let operator = self
            .arena
            .get(binary.operator_token)
            .map_or(SyntaxKind::Unknown, |node| node.kind);
        if operator == SyntaxKind::InKeyword {
            let Some(property) = self.literal_expression_name(binary.left) else {
                return result;
            };
            let Some(subject) = self.narrowing_subject(binary.right) else {
                return result;
            };
            let narrowed = self.narrow_by_property(subject, &property, truthy);
            result.insert(subject, narrowed);
            return result;
        }
        if operator == SyntaxKind::InstanceOfKeyword {
            let Some(subject) = self.narrowing_subject(binary.left) else {
                return result;
            };
            let Some(name) = self.property_name(binary.right) else {
                return result;
            };
            let Some(target_symbol) = self.resolve_identifier(binary.right, &name) else {
                return result;
            };
            let Some(target) = self.result.symbol_types.get(&target_symbol).copied() else {
                return result;
            };
            let narrowed = self.narrow_by_assignability(subject, target, truthy);
            result.insert(subject, narrowed);
            return result;
        }
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
        if let Some((subject, property)) = self.property_narrowing_subject(binary.left) {
            let comparison = self.type_of_expression(binary.right);
            let narrowed = self.narrow_discriminant(subject, &property, comparison, include_match);
            result.insert(subject, narrowed);
            return result;
        }
        if let Some((subject, property)) = self.property_narrowing_subject(binary.right) {
            let comparison = self.type_of_expression(binary.left);
            let narrowed = self.narrow_discriminant(subject, &property, comparison, include_match);
            result.insert(subject, narrowed);
            return result;
        }
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
        let original = self.current_symbol_type(subject);
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

    fn current_symbol_type(&self, symbol: SymbolId) -> TypeId {
        self.flow_types
            .get(&symbol)
            .or_else(|| self.result.symbol_types.get(&symbol))
            .copied()
            .unwrap_or_else(|| self.result.types.any())
    }

    fn is_truthy_type(kind: &TypeKind) -> bool {
        match kind {
            TypeKind::Undefined | TypeKind::Null | TypeKind::BooleanLiteral(false) => false,
            TypeKind::NumberLiteral(value) => value != "0",
            TypeKind::StringLiteral(value) => !value.is_empty(),
            _ => true,
        }
    }

    fn narrow_truthiness(&mut self, original: TypeId, truthy: bool) -> TypeId {
        let mut filtered = Vec::new();
        for member in self.union_members(original) {
            match self.result.types.get(member).unwrap().kind.clone() {
                TypeKind::Boolean => {
                    filtered.push(self.result.types.alloc(TypeKind::BooleanLiteral(truthy)));
                }
                TypeKind::Number | TypeKind::String | TypeKind::BigInt => filtered.push(member),
                kind if Self::is_truthy_type(&kind) == truthy => filtered.push(member),
                _ => {}
            }
        }
        self.result.types.union(filtered)
    }

    fn property_narrowing_subject(&self, node: NodeId) -> Option<(SymbolId, String)> {
        let NodeData::PropertyAccessExpression(access) = &self.arena.get(node)?.data else {
            return None;
        };
        let subject = self.narrowing_subject(access.expression)?;
        Some((subject, self.property_name(access.name)?))
    }

    fn literal_expression_name(&self, node: NodeId) -> Option<String> {
        match &self.arena.get(node)?.data {
            NodeData::StringLiteral(value) => Some(value.text.clone()),
            NodeData::NumericLiteral(value) => Some(value.text.clone()),
            _ => None,
        }
    }

    fn narrow_discriminant(
        &mut self,
        subject: SymbolId,
        property: &str,
        comparison: TypeId,
        include_match: bool,
    ) -> TypeId {
        let original = self.current_symbol_type(subject);
        let members = self.union_members(original);
        let filtered = members
            .into_iter()
            .filter(|member| {
                let matches =
                    self.lookup_property_type(*member, property)
                        .is_some_and(|property_type| {
                            self.is_assignable(property_type, comparison)
                                && self.is_assignable(comparison, property_type)
                        });
                matches == include_match
            })
            .collect::<Vec<_>>();
        self.result.types.union(filtered)
    }

    fn narrow_by_property(
        &mut self,
        subject: SymbolId,
        property: &str,
        include_match: bool,
    ) -> TypeId {
        let original = self.current_symbol_type(subject);
        let members = self.union_members(original);
        let filtered = members
            .into_iter()
            .filter(|member| {
                self.lookup_property_type(*member, property).is_some() == include_match
            })
            .collect::<Vec<_>>();
        self.result.types.union(filtered)
    }

    fn narrow_by_assignability(
        &mut self,
        subject: SymbolId,
        target: TypeId,
        include_match: bool,
    ) -> TypeId {
        let original = self.current_symbol_type(subject);
        let filtered = self
            .union_members(original)
            .into_iter()
            .filter(|member| self.is_assignable(*member, target) == include_match)
            .collect::<Vec<_>>();
        self.result.types.union(filtered)
    }

    fn union_members(&self, type_id: TypeId) -> Vec<TypeId> {
        match &self.result.types.get(type_id).unwrap().kind {
            TypeKind::Union(members) => members.clone(),
            _ => vec![type_id],
        }
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
                SyntaxKind::UndefinedKeyword => self.result.types.undefined(),
                SyntaxKind::ThisKeyword => self
                    .this_types
                    .last()
                    .copied()
                    .unwrap_or_else(|| self.result.types.unknown()),
                _ => self.result.types.unknown(),
            },
            NodeData::Identifier(identifier) => {
                let type_id = self.identifier_type(node_id, &identifier.text);
                if self.const_enum_types.contains(&type_id)
                    && !self.const_enum_value_usage_permitted(node_id)
                {
                    self.error(node_id, 2475, std::iter::empty());
                }
                type_id
            }
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
                let assignment_target = (operator == SyntaxKind::EqualsToken)
                    .then(|| self.assignment_target_type(data.left))
                    .flatten()
                    .unwrap_or(left);
                if operator == SyntaxKind::EqualsToken
                    && let Some(symbol) = self.narrowing_subject(data.left)
                {
                    let declared = self
                        .result
                        .symbol_types
                        .get(&symbol)
                        .copied()
                        .unwrap_or(left);
                    if !self.is_assignable(right, declared) {
                        self.assignability_error(node_id, right, declared);
                    }
                    self.flow_types.insert(symbol, right);
                    right
                } else if operator == SyntaxKind::EqualsToken
                    && let Some(name) = self.readonly_assignment_name(data.left)
                {
                    self.error(node_id, 2540, [name]);
                    if !self.is_assignable(right, assignment_target) {
                        self.assignment_target_error(data.left, right, assignment_target);
                    }
                    right
                } else if operator == SyntaxKind::EqualsToken
                    && !self.is_assignable(right, assignment_target)
                {
                    self.assignment_target_error(data.left, right, assignment_target);
                    assignment_target
                } else {
                    self.check_binary(node_id, operator, assignment_target, right)
                }
            }
            NodeData::ObjectLiteralExpression(data) => {
                self.object_literal_type(data, contextual_type)
            }
            NodeData::ClassExpression(data) => self.class_expression_type(data),
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
            NodeData::FunctionExpression(data) => {
                self.function_expression_type(data, contextual_type)
            }
            NodeData::PropertyAccessExpression(data) => {
                let receiver = self.type_of_expression(data.expression);
                if matches!(
                    self.result.types.get(receiver).map(|type_| &type_.kind),
                    Some(TypeKind::Unknown)
                ) {
                    let name = self
                        .property_name(data.expression)
                        .unwrap_or_else(|| "value".into());
                    self.error(data.expression, 18046, [name]);
                    return self.result.types.any();
                }
                let name = self.property_name(data.name).unwrap_or_default();
                let value = self.property_access_type(node_id, receiver, &name);
                self.record_const_enum_access(node_id, receiver, value);
                value
            }
            NodeData::ElementAccessExpression(data) => {
                let receiver = self.type_of_expression(data.expression);
                if self.const_enum_types.contains(&receiver)
                    && !matches!(
                        self.arena
                            .get(data.argument_expression)
                            .map(|argument| argument.kind),
                        Some(SyntaxKind::StringLiteral | SyntaxKind::NoSubstitutionTemplateLiteral)
                    )
                {
                    self.type_of_expression(data.argument_expression);
                    self.error(node_id, 2476, std::iter::empty());
                    return self.result.types.any();
                }
                let index = self.type_of_expression(data.argument_expression);
                let value = self.element_access_type(node_id, receiver, index);
                self.record_const_enum_access(node_id, receiver, value);
                value
            }
            NodeData::CallExpression(data) => {
                let getter_call = self.property_access_is_getter(data.expression);
                let callee = self.type_of_expression(data.expression);
                if getter_call && !self.type_is_callable(callee) {
                    for argument in &data.arguments.nodes {
                        self.type_of_expression(*argument);
                    }
                    self.error(data.expression, 6234, std::iter::empty());
                    self.result.types.any()
                } else {
                    self.call_expression_type(node_id, callee, &data.arguments.nodes, false)
                }
            }
            NodeData::NewExpression(data) => {
                let type_arguments = data
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
                let callee = if let Some(name) = self.property_name(data.expression)
                    && let Some(symbol) = self.resolve_identifier(data.expression, &name)
                {
                    self.instantiate_declared_object(symbol, &type_arguments)
                        .unwrap_or_else(|| self.type_of_expression(data.expression))
                } else {
                    self.type_of_expression(data.expression)
                };
                let arguments = data.arguments.as_ref().map_or(&[][..], |list| &list.nodes);
                self.call_expression_type(node_id, callee, arguments, true)
            }
            NodeData::DeleteExpression(data) => {
                let operand = self.type_of_expression(data.expression);
                self.check_delete_expression(data.expression, operand);
                self.result.types.boolean()
            }
            NodeData::TypeOfExpression(_) => self.result.types.string(),
            NodeData::FunctionDeclaration(data) => self.function_type(data),
            _ => self.result.types.unknown(),
        };
        self.result.node_types.insert(node_id, result);
        result
    }

    fn check_delete_expression(&mut self, expression: NodeId, operand: TypeId) {
        if !self.options.strict_null_checks || self.delete_operand_type_is_permitted(operand) {
            return;
        }
        if self.options.exact_optional_property_types {
            if self.property_target_is_optional(expression) != Some(true) {
                self.error(expression, 2790, std::iter::empty());
            }
        } else if !self.type_includes_undefined(operand) {
            self.error(expression, 2790, std::iter::empty());
        }
    }

    fn const_enum_value_usage_permitted(&self, expression: NodeId) -> bool {
        let mut current = expression;
        loop {
            let Some(parent) = self.arena.get(current).and_then(|node| node.parent) else {
                return false;
            };
            match &self.arena.get(parent).expect("parent node exists").data {
                NodeData::ParenthesizedExpression(data) if data.expression == current => {
                    current = parent;
                }
                NodeData::PropertyAccessExpression(access) => {
                    return access.expression == current;
                }
                NodeData::ElementAccessExpression(access) => {
                    return access.expression == current;
                }
                _ => return false,
            }
        }
    }

    fn delete_operand_type_is_permitted(&self, operand: TypeId) -> bool {
        matches!(
            self.result.types.get(operand).map(|type_| &type_.kind),
            Some(TypeKind::Any | TypeKind::Unknown | TypeKind::Never)
        )
    }

    fn property_target_is_optional(&mut self, expression: NodeId) -> Option<bool> {
        match self.arena.get(expression).map(|node| node.data.clone())? {
            NodeData::PropertyAccessExpression(access) => {
                let receiver = self.type_of_expression(access.expression);
                let name = self.property_name(access.name)?;
                self.property_is_optional(receiver, &name)
            }
            NodeData::ElementAccessExpression(access) => {
                let receiver = self.type_of_expression(access.expression);
                let index = self.type_of_expression(access.argument_expression);
                let name = match &self.result.types.get(index)?.kind {
                    TypeKind::StringLiteral(name) | TypeKind::NumberLiteral(name) => name.clone(),
                    _ => return None,
                };
                self.property_is_optional(receiver, &name)
            }
            _ => None,
        }
    }

    fn property_access_is_getter(&mut self, expression: NodeId) -> bool {
        let Some(NodeData::PropertyAccessExpression(access)) =
            self.arena.get(expression).map(|node| node.data.clone())
        else {
            return false;
        };
        let receiver = self.type_of_expression(access.expression);
        let Some(name) = self.property_name(access.name) else {
            return false;
        };
        self.property_is_getter(receiver, &name)
    }

    fn property_is_getter(&self, receiver: TypeId, name: &str) -> bool {
        match &self.result.types.get(receiver).unwrap().kind {
            TypeKind::Object(object) => object.getter_properties.contains(name),
            TypeKind::Union(members) | TypeKind::Intersection(members) => members
                .iter()
                .any(|member| self.property_is_getter(*member, name)),
            TypeKind::TypeParameter {
                constraint: Some(constraint),
                ..
            } => self.property_is_getter(*constraint, name),
            _ => false,
        }
    }

    fn type_is_callable(&self, type_id: TypeId) -> bool {
        match &self.result.types.get(type_id).unwrap().kind {
            TypeKind::Any | TypeKind::Function(_) | TypeKind::Overload(_) => true,
            TypeKind::Union(members) | TypeKind::Intersection(members) => {
                members.iter().all(|member| self.type_is_callable(*member))
            }
            _ => false,
        }
    }

    fn property_is_optional(&self, receiver: TypeId, name: &str) -> Option<bool> {
        match &self.result.types.get(receiver)?.kind {
            TypeKind::Object(object) => object
                .properties
                .contains_key(name)
                .then(|| object.optional_properties.contains(name)),
            TypeKind::Union(members) => members
                .iter()
                .map(|member| self.property_is_optional(*member, name))
                .collect::<Option<Vec<_>>>()
                .map(|members| members.into_iter().any(std::convert::identity)),
            TypeKind::Intersection(members) => members
                .iter()
                .filter_map(|member| self.property_is_optional(*member, name))
                .reduce(|left, right| left && right),
            TypeKind::TypeParameter {
                constraint: Some(constraint),
                ..
            } => self.property_is_optional(*constraint, name),
            _ => None,
        }
    }

    fn assignment_target_error(&mut self, left: NodeId, actual: TypeId, expected: TypeId) {
        let exact_optional_mismatch = self.options.exact_optional_property_types
            && self.type_includes_undefined(actual)
            && !self.type_includes_undefined(expected)
            && self.property_target_is_optional(left) == Some(true);
        if exact_optional_mismatch {
            self.error(
                left,
                2412,
                [
                    self.result.types.display(actual),
                    self.result.types.display(expected),
                ],
            );
        } else {
            self.assignability_error(left, actual, expected);
        }
    }

    fn identifier_type(&mut self, node: NodeId, name: &str) -> TypeId {
        if name == "undefined" {
            return self.result.types.undefined();
        }
        let symbol = self.resolve_identifier(node, name);
        if let Some(symbol) = symbol {
            *self.symbol_reads.entry(symbol).or_default() += 1;
            for narrowing in self.narrowings.iter().rev() {
                if let Some(type_id) = narrowing.get(&symbol) {
                    return *type_id;
                }
            }
            if let Some(type_id) = self.flow_types.get(&symbol) {
                return *type_id;
            }
        }
        for scope in self.local_scopes.iter().rev() {
            if let Some(type_id) = scope.get(name) {
                return *type_id;
            }
        }
        if let Some(symbol) = symbol {
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

    fn readonly_assignment_name(&mut self, left: NodeId) -> Option<String> {
        let NodeData::PropertyAccessExpression(access) =
            self.arena.get(left).map(|node| node.data.clone())?
        else {
            return None;
        };
        let name = self.property_name(access.name)?;
        let receiver = self.type_of_expression(access.expression);
        let readonly = self.union_members(receiver).iter().any(|member| {
            matches!(
                &self.result.types.get(*member).unwrap().kind,
                TypeKind::Object(object) if object.readonly_properties.contains(&name)
            )
        });
        readonly.then_some(name)
    }

    fn arrow_type(
        &mut self,
        data: &ts_ast::ArrowFunctionData,
        contextual_type: Option<TypeId>,
    ) -> TypeId {
        let contextual_signature =
            contextual_type.and_then(|type_id| match &self.result.types.get(type_id)?.kind {
                TypeKind::Function(signature) => Some(signature.clone()),
                TypeKind::Overload(signatures) => signatures.first().cloned(),
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
            if self.options.no_implicit_any
                && parameter_data.type_.is_none()
                && contextual_signature.is_none()
            {
                let name = self
                    .property_name(parameter_data.name)
                    .unwrap_or_else(|| "parameter".into());
                self.error(*parameter, 7006, [name, "any".into()]);
            }
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
            let return_context = expected_return.filter(|expected| {
                !matches!(
                    self.result.types.get(*expected).map(|type_| &type_.kind),
                    Some(TypeKind::TypeParameter { .. })
                )
            });
            let actual = self.type_of_expression_context(data.body, return_context);
            if let Some(expected) = expected_return
                && !self.is_assignable(actual, expected)
            {
                self.assignability_error(data.body, actual, expected);
            }
            if expected_return.is_some_and(|expected| {
                matches!(
                    self.result.types.get(expected).map(|type_| &type_.kind),
                    Some(TypeKind::TypeParameter { .. })
                )
            }) {
                self.widen_literal(actual)
            } else {
                expected_return.unwrap_or_else(|| self.widen_literal(actual))
            }
        };
        self.local_scopes.pop();
        self.result.types.alloc(TypeKind::Function(FunctionType {
            parameters,
            return_type,
            parameters_optional: self.options.is_javascript_file,
        }))
    }

    fn function_expression_type(
        &mut self,
        data: &ts_ast::FunctionExpressionData,
        contextual_type: Option<TypeId>,
    ) -> TypeId {
        let contextual_signature =
            contextual_type.and_then(|type_id| match &self.result.types.get(type_id)?.kind {
                TypeKind::Function(signature) => Some(signature.clone()),
                TypeKind::Overload(signatures) => signatures.first().cloned(),
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
            if self.options.no_implicit_any
                && parameter_data.type_.is_none()
                && contextual_signature.is_none()
            {
                let name = self
                    .property_name(parameter_data.name)
                    .unwrap_or_else(|| "parameter".into());
                self.error(*parameter, 7006, [name, "any".into()]);
            }
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
        let return_type = data
            .type_
            .map(|node| self.type_from_type_node(node))
            .or_else(|| {
                contextual_signature
                    .as_ref()
                    .map(|signature| signature.return_type)
            })
            .unwrap_or_else(|| self.result.types.any());
        let mut saw_return = false;
        self.check_node(data.body, Some(return_type), &mut saw_return);
        self.local_scopes.pop();
        self.result.types.alloc(TypeKind::Function(FunctionType {
            parameters,
            return_type,
            parameters_optional: self.options.is_javascript_file,
        }))
    }

    fn property_access_type(&mut self, node: NodeId, receiver: TypeId, name: &str) -> TypeId {
        if let Some(property) = self.lookup_property_type(receiver, name) {
            property
        } else {
            self.error(
                node,
                2339,
                [name.to_owned(), self.property_receiver_display(receiver)],
            );
            self.result.types.any()
        }
    }

    fn property_receiver_display(&self, receiver: TypeId) -> String {
        let Some(TypeKind::Object(object)) =
            self.result.types.get(receiver).map(|type_| &type_.kind)
        else {
            return self.result.types.display(receiver);
        };
        if object.getter_properties.is_empty() {
            return self.result.types.display(receiver);
        }
        format!(
            "{{ {} }}",
            object
                .properties
                .iter()
                .map(|(name, value)| {
                    let readonly = if object.readonly_properties.contains(name) {
                        "readonly "
                    } else {
                        ""
                    };
                    format!("{readonly}{name}: {}", self.result.types.display(*value))
                })
                .collect::<Vec<_>>()
                .join("; ")
        )
    }

    fn lookup_property_type(&mut self, receiver: TypeId, name: &str) -> Option<TypeId> {
        match self.result.types.get(receiver)?.kind.clone() {
            TypeKind::Any => Some(self.result.types.any()),
            TypeKind::Object(object) => self.object_property_type(&object, name, true),
            TypeKind::Array(_) if name == "length" => Some(self.result.types.number()),
            TypeKind::Array(element) => {
                let descriptor = self.external_names.get("Array")?.clone();
                let array = self.import_alias(&descriptor, &[element]);
                match self.result.types.get(array)?.kind.clone() {
                    TypeKind::Object(object) => self.object_property_type(&object, name, true),
                    _ => None,
                }
            }
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

    fn lookup_property_write_type(&mut self, receiver: TypeId, name: &str) -> Option<TypeId> {
        match self.result.types.get(receiver)?.kind.clone() {
            TypeKind::Any => Some(self.result.types.any()),
            TypeKind::Object(object) => self.object_property_type(&object, name, false),
            TypeKind::Union(members) => {
                let properties = members
                    .into_iter()
                    .map(|member| self.lookup_property_write_type(member, name))
                    .collect::<Option<Vec<_>>>()?;
                Some(self.result.types.union(properties))
            }
            TypeKind::Intersection(members) => {
                let properties = members
                    .into_iter()
                    .filter_map(|member| self.lookup_property_write_type(member, name))
                    .collect::<Vec<_>>();
                (!properties.is_empty()).then(|| self.result.types.intersection(properties))
            }
            _ => self.lookup_property_type(receiver, name),
        }
    }

    fn object_property_type(
        &mut self,
        object: &ObjectType,
        name: &str,
        read: bool,
    ) -> Option<TypeId> {
        let property = object.properties.get(name).copied()?;
        if read && object.optional_properties.contains(name) {
            let undefined = self.result.types.undefined();
            Some(self.result.types.union([property, undefined]))
        } else {
            Some(property)
        }
    }

    fn assignment_target_type(&mut self, node: NodeId) -> Option<TypeId> {
        match self.arena.get(node).map(|node| node.data.clone())? {
            NodeData::PropertyAccessExpression(access) => {
                let receiver = self.type_of_expression(access.expression);
                let name = self.property_name(access.name)?;
                self.lookup_property_write_type(receiver, &name)
            }
            NodeData::ElementAccessExpression(access) => {
                let receiver = self.type_of_expression(access.expression);
                let index = self.type_of_expression(access.argument_expression);
                self.lookup_indexed_write_type(receiver, index)
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
                    self.object_property_type(&object_type, &name, true)
                }
                _ => None,
            },
            TypeKind::TypeParameter {
                constraint: Some(constraint),
                ..
            } => self.lookup_indexed_type(constraint, index),
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

    fn lookup_indexed_write_type(&mut self, object: TypeId, index: TypeId) -> Option<TypeId> {
        let index_kind = self.result.types.get(index)?.kind.clone();
        if let TypeKind::Union(indices) = index_kind {
            let values = indices
                .into_iter()
                .map(|index| self.lookup_indexed_write_type(object, index))
                .collect::<Option<Vec<_>>>()?;
            return Some(self.result.types.union(values));
        }
        match self.result.types.get(object)?.kind.clone() {
            TypeKind::Object(object_type) => match index_kind {
                TypeKind::StringLiteral(name) | TypeKind::NumberLiteral(name) => {
                    self.object_property_type(&object_type, &name, false)
                }
                _ => None,
            },
            TypeKind::Union(members) => {
                let values = members
                    .into_iter()
                    .map(|member| self.lookup_indexed_write_type(member, index))
                    .collect::<Option<Vec<_>>>()?;
                Some(self.result.types.union(values))
            }
            TypeKind::Intersection(members) => {
                let values = members
                    .into_iter()
                    .filter_map(|member| self.lookup_indexed_write_type(member, index))
                    .collect::<Vec<_>>();
                (!values.is_empty()).then(|| self.result.types.intersection(values))
            }
            _ => self.lookup_indexed_type(object, index),
        }
    }

    fn callable_signatures(&self, kind: TypeKind) -> Option<Vec<FunctionType>> {
        match kind {
            TypeKind::Function(signature) => Some(vec![signature]),
            TypeKind::Overload(signatures) => Some(signatures),
            TypeKind::Intersection(members) => members.into_iter().find_map(|member| {
                self.result
                    .types
                    .get(member)
                    .and_then(|type_| self.callable_signatures(type_.kind.clone()))
            }),
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
        let signatures = if construct {
            match callee_kind {
                TypeKind::Constructor(signature) => Some(vec![signature]),
                other => self.callable_signatures(other),
            }
        } else {
            self.callable_signatures(callee_kind)
        };
        let Some(signatures) = signatures else {
            self.error(
                node,
                if construct { 2351 } else { 2349 },
                std::iter::empty(),
            );
            return self.result.types.any();
        };
        if signatures.len() > 1 {
            let actuals = arguments
                .iter()
                .map(|argument| self.type_of_expression(*argument))
                .collect::<Vec<_>>();
            if let Some((signature, inference)) = signatures.iter().find_map(|signature| {
                if actuals.len() < self.minimum_parameter_count(signature)
                    || actuals.len() > signature.parameters.len()
                {
                    return None;
                }
                let mut inference = HashMap::new();
                for (actual, parameter) in actuals.iter().zip(&signature.parameters) {
                    self.infer_type_parameters(*parameter, *actual, &mut inference);
                    let expected = self.substitute_type(*parameter, &inference);
                    if !self.is_assignable(*actual, expected) {
                        return None;
                    }
                }
                Some((signature, inference))
            }) {
                return self.substitute_type(signature.return_type, &inference);
            }
        }
        let Some(signature) = signatures.first() else {
            self.error(
                node,
                if construct { 2351 } else { 2349 },
                std::iter::empty(),
            );
            return self.result.types.any();
        };
        let minimum_parameters = self.minimum_parameter_count(signature);
        if arguments.len() < minimum_parameters || arguments.len() > signature.parameters.len() {
            let expected = if minimum_parameters == signature.parameters.len() {
                minimum_parameters.to_string()
            } else {
                format!("{minimum_parameters}-{}", signature.parameters.len())
            };
            self.error(node, 2554, [expected, arguments.len().to_string()]);
        }
        let mut inference = HashMap::new();
        for (argument, parameter) in arguments.iter().zip(&signature.parameters) {
            let actual = self.type_of_expression_context(*argument, Some(*parameter));
            self.infer_type_parameters(*parameter, actual, &mut inference);
            let expected = self.substitute_type(*parameter, &inference);
            if !self.is_assignable(actual, expected) {
                let code = if self.exact_optional_property_mismatch(actual, expected) {
                    2379
                } else {
                    2345
                };
                self.error(
                    *argument,
                    code,
                    [
                        self.result.types.display(actual),
                        self.result.types.display(expected),
                    ],
                );
            }
        }
        self.substitute_type(signature.return_type, &inference)
    }

    fn minimum_parameter_count(&self, signature: &FunctionType) -> usize {
        if signature.parameters_optional {
            return 0;
        }
        signature
            .parameters
            .iter()
            .rposition(|parameter| !self.type_includes_undefined(*parameter))
            .map_or(0, |index| index + 1)
    }

    fn type_includes_undefined(&self, type_id: TypeId) -> bool {
        if type_id == self.result.types.undefined() {
            return true;
        }
        matches!(
            &self.result.types.get(type_id).unwrap().kind,
            TypeKind::Union(members) if members.iter().any(|member| self.type_includes_undefined(*member))
        )
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
            TypeKind::Tuple(parameter_elements) => {
                if let TypeKind::Tuple(actual_elements) =
                    self.result.types.get(actual).unwrap().kind.clone()
                {
                    for (parameter, actual) in parameter_elements.iter().zip(&actual_elements) {
                        self.infer_type_parameters(*parameter, *actual, inference);
                    }
                }
            }
            TypeKind::Object(parameter_object) => {
                if let TypeKind::Object(actual_object) =
                    self.result.types.get(actual).unwrap().kind.clone()
                {
                    for (name, parameter) in parameter_object.properties {
                        if let Some(actual) = actual_object.properties.get(&name) {
                            self.infer_type_parameters(parameter, *actual, inference);
                        }
                    }
                }
            }
            TypeKind::Function(parameter_signature) => {
                if let TypeKind::Function(actual_signature) =
                    self.result.types.get(actual).unwrap().kind.clone()
                {
                    for (parameter, actual) in parameter_signature
                        .parameters
                        .iter()
                        .zip(&actual_signature.parameters)
                    {
                        self.infer_type_parameters(*parameter, *actual, inference);
                    }
                    self.infer_type_parameters(
                        parameter_signature.return_type,
                        actual_signature.return_type,
                        inference,
                    );
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
            TypeKind::Function(signature) => {
                let parameters = signature
                    .parameters
                    .into_iter()
                    .map(|parameter| self.substitute_type(parameter, inference))
                    .collect();
                let return_type = self.substitute_type(signature.return_type, inference);
                self.result.types.alloc(TypeKind::Function(FunctionType {
                    parameters,
                    return_type,
                    parameters_optional: signature.parameters_optional,
                }))
            }
            TypeKind::Tuple(elements) => {
                let elements = elements
                    .into_iter()
                    .map(|element| self.substitute_type(element, inference))
                    .collect();
                self.result.types.alloc(TypeKind::Tuple(elements))
            }
            TypeKind::Object(object) => {
                let properties = object
                    .properties
                    .into_iter()
                    .map(|(name, property)| (name, self.substitute_type(property, inference)))
                    .collect();
                self.result.types.alloc(TypeKind::Object(ObjectType {
                    properties,
                    optional_properties: object.optional_properties,
                    readonly_properties: object.readonly_properties,
                    getter_properties: object.getter_properties,
                    setter_properties: object.setter_properties,
                }))
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
        if matches!(
            self.result.types.get(left).map(|type_| &type_.kind),
            Some(TypeKind::Any)
        ) || matches!(
            self.result.types.get(right).map(|type_| &type_.kind),
            Some(TypeKind::Any)
        ) {
            return if matches!(
                operator,
                SyntaxKind::LessThanToken
                    | SyntaxKind::LessThanEqualsToken
                    | SyntaxKind::GreaterThanToken
                    | SyntaxKind::GreaterThanEqualsToken
                    | SyntaxKind::EqualsEqualsToken
                    | SyntaxKind::EqualsEqualsEqualsToken
                    | SyntaxKind::ExclamationEqualsToken
                    | SyntaxKind::ExclamationEqualsEqualsToken
                    | SyntaxKind::InKeyword
                    | SyntaxKind::InstanceOfKeyword
            ) {
                self.result.types.boolean()
            } else {
                self.result.types.any()
            };
        }
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
            | SyntaxKind::ExclamationEqualsEqualsToken
            | SyntaxKind::InKeyword
            | SyntaxKind::InstanceOfKeyword => self.result.types.boolean(),
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

    fn function_signature(&mut self, data: &ts_ast::FunctionDeclarationData) -> FunctionType {
        let type_id = self.function_type(data);
        let TypeKind::Function(signature) = self.result.types.get(type_id).unwrap().kind.clone()
        else {
            unreachable!("function_type always creates a function type");
        };
        signature
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
                        if base == self.result.types.any() {
                            self.result
                                .types
                                .alloc(TypeKind::Union(vec![base, undefined]))
                        } else {
                            self.result.types.union([base, undefined])
                        }
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
            parameters_optional: self.options.is_javascript_file,
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
                if matches!(
                    self.arena.get(data.type_name).map(|node| &node.data),
                    Some(NodeData::QualifiedName(_))
                ) {
                    if let Some(arguments) = &data.type_arguments {
                        for argument in &arguments.nodes {
                            self.type_from_type_node(*argument);
                        }
                    }
                    if let Some(type_id) = self.type_entity_name_type(data.type_name) {
                        return type_id;
                    }
                    let name = self
                        .entity_name_text(data.type_name)
                        .unwrap_or_else(|| "type".into());
                    return self.unresolved_type_name(data.type_name, name);
                }
                let Some(name) = self.property_name(data.type_name) else {
                    return self.result.types.unknown();
                };
                for scope in self.type_parameter_scopes.iter().rev() {
                    if let Some(type_id) = scope.get(&name) {
                        return *type_id;
                    }
                }
                if matches!(name.as_str(), "Array" | "ReadonlyArray")
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
                    return self.unresolved_type_name(data.type_name, name);
                };
                if let Some(descriptor) = self.external_aliases.get(&symbol).cloned() {
                    return self.import_alias(&descriptor, &arguments);
                }
                self.instantiate_alias(symbol, &arguments)
                    .or_else(|| self.instantiate_declared_object(symbol, &arguments))
                    .unwrap_or_else(|| {
                        self.result
                            .symbol_types
                            .get(&symbol)
                            .copied()
                            .unwrap_or_else(|| self.result.types.unknown())
                    })
            }
            NodeData::TypeQueryNode(data) => self.type_of_expression(data.expr_name),
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
            NodeData::TypeOperatorNode(data) => {
                let operand = self.type_from_type_node(data.type_);
                if data.operator == SyntaxKind::KeyOfKeyword {
                    self.keyof_type(operand)
                } else {
                    operand
                }
            }
            NodeData::ConditionalTypeNode(data) => self.conditional_type(data),
            NodeData::InferTypeNode(data) => {
                let Some(NodeData::TypeParameterDeclaration(parameter)) =
                    self.arena.get(data.type_parameter).map(|node| &node.data)
                else {
                    return self.result.types.unknown();
                };
                let Some(name) = self.property_name(parameter.name) else {
                    return self.result.types.unknown();
                };
                self.type_parameter_scopes
                    .iter()
                    .rev()
                    .find_map(|scope| scope.get(&name).copied())
                    .unwrap_or_else(|| self.result.types.unknown())
            }
            NodeData::MappedTypeNode(data) => self.mapped_type(data),
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
            NodeData::FunctionTypeNode(data) => self.signature_type(
                &data.parameters.nodes,
                data.type_,
                data.type_parameters.as_ref(),
            ),
            NodeData::ConstructorTypeNode(data) => self.signature_type(
                &data.parameters.nodes,
                data.type_,
                data.type_parameters.as_ref(),
            ),
            NodeData::IndexedAccessTypeNode(data) => {
                let object = self.type_from_type_node(data.object_type);
                let index = self.type_from_type_node(data.index_type);
                self.indexed_access_type(node_id, object, index)
            }
            _ => self.result.types.unknown(),
        }
    }

    fn keyof_type(&mut self, type_id: TypeId) -> TypeId {
        let kind = self.result.types.get(type_id).unwrap().kind.clone();
        match kind {
            TypeKind::Any => self.result.types.any(),
            TypeKind::Object(object) => {
                let mut keys = Vec::with_capacity(object.properties.len());
                for name in object.properties.keys() {
                    keys.push(
                        self.result
                            .types
                            .alloc(TypeKind::StringLiteral(name.clone())),
                    );
                }
                self.result.types.union(keys)
            }
            TypeKind::Tuple(_) | TypeKind::Array(_) => {
                let length = self
                    .result
                    .types
                    .alloc(TypeKind::StringLiteral("length".into()));
                let number = self.result.types.number();
                self.result.types.union([number, length])
            }
            TypeKind::Union(members) => {
                let mut common = self.type_keys(members[0]);
                for member in members.into_iter().skip(1) {
                    let keys = self.type_keys(member);
                    common.retain(|key| keys.contains(key));
                }
                self.key_union(common)
            }
            TypeKind::Intersection(members) => {
                let keys = members
                    .into_iter()
                    .flat_map(|member| self.type_keys(member))
                    .collect();
                self.key_union(keys)
            }
            TypeKind::TypeParameter {
                constraint: Some(constraint),
                ..
            } => self.keyof_type(constraint),
            _ => self.result.types.never(),
        }
    }

    fn conditional_type(&mut self, data: &ts_ast::ConditionalTypeNodeData) -> TypeId {
        let check = self.type_from_type_node(data.check_type);
        if let Some(name) = self.type_reference_name(data.check_type)
            && self
                .type_parameter_scopes
                .iter()
                .rev()
                .any(|scope| scope.contains_key(&name))
            && let TypeKind::Union(members) = self.result.types.get(check).unwrap().kind.clone()
        {
            let results = members
                .into_iter()
                .map(|member| {
                    self.type_parameter_scopes
                        .push(HashMap::from([(name.clone(), member)]));
                    let result = self.conditional_type_branch(data, member);
                    self.type_parameter_scopes.pop();
                    result
                })
                .collect::<Vec<_>>();
            return self.result.types.union(results);
        }
        self.conditional_type_branch(data, check)
    }

    fn conditional_type_branch(
        &mut self,
        data: &ts_ast::ConditionalTypeNodeData,
        check: TypeId,
    ) -> TypeId {
        let mut inference = HashMap::new();
        if self.infer_conditional_type(data.extends_type, check, &mut inference) {
            self.type_parameter_scopes.push(inference);
            let result = self.type_from_type_node(data.true_type);
            self.type_parameter_scopes.pop();
            result
        } else {
            self.type_from_type_node(data.false_type)
        }
    }

    #[allow(clippy::too_many_lines)]
    fn infer_conditional_type(
        &mut self,
        pattern: NodeId,
        actual: TypeId,
        inference: &mut HashMap<String, TypeId>,
    ) -> bool {
        let Some(node) = self.arena.get(pattern) else {
            return false;
        };
        match &node.data {
            NodeData::InferTypeNode(data) => {
                let Some(NodeData::TypeParameterDeclaration(parameter)) =
                    self.arena.get(data.type_parameter).map(|node| &node.data)
                else {
                    return false;
                };
                let Some(name) = self.property_name(parameter.name) else {
                    return false;
                };
                inference
                    .entry(name)
                    .and_modify(|current| *current = self.result.types.union([*current, actual]))
                    .or_insert(actual);
                true
            }
            NodeData::ParenthesizedTypeNode(data) => {
                self.infer_conditional_type(data.type_, actual, inference)
            }
            NodeData::TypeOperatorNode(data) if data.operator == SyntaxKind::ReadonlyKeyword => {
                self.infer_conditional_type(data.type_, actual, inference)
            }
            NodeData::ArrayTypeNode(data) => {
                let element = match self.result.types.get(actual).unwrap().kind.clone() {
                    TypeKind::Array(element) => element,
                    TypeKind::Tuple(elements) => self.result.types.union(elements),
                    _ => return false,
                };
                self.infer_conditional_type(data.element_type, element, inference)
            }
            NodeData::TypeReferenceNode(data)
                if self.property_name(data.type_name).as_deref() == Some("Array")
                    || self.property_name(data.type_name).as_deref() == Some("ReadonlyArray") =>
            {
                let Some(argument) = data
                    .type_arguments
                    .as_ref()
                    .and_then(|arguments| arguments.nodes.first())
                else {
                    return false;
                };
                let element = match self.result.types.get(actual).unwrap().kind.clone() {
                    TypeKind::Array(element) => element,
                    TypeKind::Tuple(elements) => self.result.types.union(elements),
                    _ => return false,
                };
                self.infer_conditional_type(*argument, element, inference)
            }
            NodeData::TupleTypeNode(data) => {
                let TypeKind::Tuple(elements) = self.result.types.get(actual).unwrap().kind.clone()
                else {
                    return false;
                };
                data.elements.nodes.len() == elements.len()
                    && data
                        .elements
                        .nodes
                        .iter()
                        .zip(elements)
                        .all(|(pattern, actual)| {
                            self.infer_conditional_type(*pattern, actual, inference)
                        })
            }
            NodeData::FunctionTypeNode(data) => {
                let TypeKind::Function(signature) =
                    self.result.types.get(actual).unwrap().kind.clone()
                else {
                    return false;
                };
                data.type_.is_none_or(|return_type| {
                    self.infer_conditional_type(return_type, signature.return_type, inference)
                })
            }
            NodeData::TypeLiteralNode(data) => data.members.nodes.iter().all(|member| {
                let Some(NodeData::PropertySignatureDeclaration(property)) =
                    self.arena.get(*member).map(|node| &node.data)
                else {
                    return true;
                };
                let Some(name) = self.property_name(property.name) else {
                    return false;
                };
                let Some(actual_property) = self.lookup_property_type(actual, &name) else {
                    return false;
                };
                self.infer_conditional_type(property.type_, actual_property, inference)
            }),
            NodeData::UnionTypeNode(data) => data.types.nodes.iter().any(|candidate| {
                let mut candidate_inference = inference.clone();
                if self.infer_conditional_type(*candidate, actual, &mut candidate_inference) {
                    *inference = candidate_inference;
                    true
                } else {
                    false
                }
            }),
            _ => {
                self.type_parameter_scopes.push(inference.clone());
                let expected = self.type_from_type_node(pattern);
                self.type_parameter_scopes.pop();
                self.is_assignable(actual, expected)
            }
        }
    }

    fn type_reference_name(&self, node: NodeId) -> Option<String> {
        let NodeData::TypeReferenceNode(reference) = &self.arena.get(node)?.data else {
            return None;
        };
        self.property_name(reference.type_name)
    }

    fn type_keys(&self, type_id: TypeId) -> Vec<String> {
        match &self.result.types.get(type_id).unwrap().kind {
            TypeKind::Object(object) => object.properties.keys().cloned().collect(),
            TypeKind::Tuple(_) | TypeKind::Array(_) => vec!["length".into()],
            TypeKind::Intersection(members) => members
                .iter()
                .flat_map(|member| self.type_keys(*member))
                .collect(),
            _ => Vec::new(),
        }
    }

    fn key_union(&mut self, mut keys: Vec<String>) -> TypeId {
        keys.sort();
        keys.dedup();
        let types = keys
            .into_iter()
            .map(|key| self.result.types.alloc(TypeKind::StringLiteral(key)))
            .collect::<Vec<_>>();
        self.result.types.union(types)
    }

    fn mapped_type(&mut self, data: &ts_ast::MappedTypeNodeData) -> TypeId {
        let Some(NodeData::TypeParameterDeclaration(parameter)) =
            self.arena.get(data.type_parameter).map(|node| &node.data)
        else {
            return self.result.types.unknown();
        };
        let Some(name) = self.property_name(parameter.name) else {
            return self.result.types.unknown();
        };
        let Some(constraint) = parameter.constraint else {
            return self.result.types.unknown();
        };
        let constraint = self.type_from_type_node(constraint);
        let keys = self.literal_keys(constraint);
        let homomorphic_object = self.mapped_source_object(parameter.constraint.unwrap());
        let mut properties = BTreeMap::new();
        let mut optional_properties = BTreeSet::new();
        let mut readonly_properties = BTreeSet::new();
        for (property_name, key_type) in keys {
            self.type_parameter_scopes
                .push(HashMap::from([(name.clone(), key_type)]));
            let output_names = data.name_type.map_or_else(
                || vec![property_name.clone()],
                |node| {
                    let mapped = self.type_from_type_node(node);
                    self.literal_keys(mapped)
                        .into_iter()
                        .map(|(name, _)| name)
                        .collect()
                },
            );
            let mut property_type = match data.type_ {
                Some(node) => self.type_from_type_node(node),
                None => self.result.types.any(),
            };
            let preserve_optional = homomorphic_object
                .as_ref()
                .is_some_and(|object| object.optional_properties.contains(&property_name));
            let optional_modifier = self.mapped_modifier(data.question_token);
            let is_optional = match optional_modifier {
                Some(true) => true,
                Some(false) => false,
                None => preserve_optional,
            };
            if optional_modifier == Some(false)
                && preserve_optional
                && !self.options.exact_optional_property_types
            {
                property_type = self.without_undefined(property_type);
            }
            if is_optional
                && !self.options.exact_optional_property_types
                && !self.type_includes_undefined(property_type)
            {
                let undefined = self.result.types.undefined();
                property_type = self.result.types.union([property_type, undefined]);
            }
            let preserve_readonly = homomorphic_object
                .as_ref()
                .is_some_and(|object| object.readonly_properties.contains(&property_name));
            let readonly_modifier = self.mapped_modifier(data.readonly_token);
            let is_readonly = match readonly_modifier {
                Some(true) => true,
                Some(false) => false,
                None => preserve_readonly,
            };
            self.type_parameter_scopes.pop();
            for output_name in output_names {
                if is_optional {
                    optional_properties.insert(output_name.clone());
                }
                if is_readonly {
                    readonly_properties.insert(output_name.clone());
                }
                properties.insert(output_name, property_type);
            }
        }
        self.result.types.alloc(TypeKind::Object(ObjectType {
            properties,
            optional_properties,
            readonly_properties,
            getter_properties: BTreeSet::new(),
            setter_properties: BTreeSet::new(),
        }))
    }

    fn mapped_source_object(&mut self, constraint: NodeId) -> Option<ObjectType> {
        let NodeData::TypeOperatorNode(operator) = &self.arena.get(constraint)?.data else {
            return None;
        };
        if operator.operator != SyntaxKind::KeyOfKeyword {
            return None;
        }
        let source = self.type_from_type_node(operator.type_);
        let TypeKind::Object(object) = self.result.types.get(source)?.kind.clone() else {
            return None;
        };
        Some(object)
    }

    fn mapped_modifier(&self, token: Option<NodeId>) -> Option<bool> {
        token.map(|token| self.arena.get(token).unwrap().kind != SyntaxKind::MinusToken)
    }

    fn without_undefined(&mut self, type_id: TypeId) -> TypeId {
        let TypeKind::Union(members) = self.result.types.get(type_id).unwrap().kind.clone() else {
            return type_id;
        };
        let undefined = self.result.types.undefined();
        self.result
            .types
            .union(members.into_iter().filter(|member| *member != undefined))
    }

    fn literal_keys(&self, type_id: TypeId) -> Vec<(String, TypeId)> {
        match &self.result.types.get(type_id).unwrap().kind {
            TypeKind::StringLiteral(name) | TypeKind::NumberLiteral(name) => {
                vec![(name.clone(), type_id)]
            }
            TypeKind::Union(members) => members
                .iter()
                .flat_map(|member| self.literal_keys(*member))
                .collect(),
            _ => Vec::new(),
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

    #[allow(clippy::too_many_lines)]
    fn is_assignable(&self, source: TypeId, target: TypeId) -> bool {
        if source == target || source == self.result.types.never() {
            return true;
        }
        if self.enum_member_owners.get(&source) == Some(&target) {
            return true;
        }
        if self.enum_types.contains(&target) {
            return false;
        }
        let source_kind = &self.result.types.get(source).unwrap().kind;
        let target_kind = &self.result.types.get(target).unwrap().kind;
        if !self.options.strict_null_checks
            && matches!(source_kind, TypeKind::Null | TypeKind::Undefined)
        {
            return true;
        }
        if matches!(source_kind, TypeKind::Any)
            || matches!(target_kind, TypeKind::Any | TypeKind::Unknown)
        {
            return true;
        }
        if let TypeKind::Object(target_object) = target_kind {
            return target_object.properties.iter().all(|(name, target_type)| {
                let source_types = self.property_types(source, name);
                (source_types.is_empty() && target_object.optional_properties.contains(name))
                    || source_types
                        .into_iter()
                        .any(|source_type| self.is_assignable(source_type, *target_type))
            });
        }
        match (source_kind, target_kind) {
            (TypeKind::NumberLiteral(source), TypeKind::NumberLiteral(target))
            | (TypeKind::StringLiteral(source), TypeKind::StringLiteral(target))
            | (TypeKind::BigIntLiteral(source), TypeKind::BigIntLiteral(target)) => {
                source == target
            }
            (TypeKind::BooleanLiteral(source), TypeKind::BooleanLiteral(target)) => {
                source == target
            }
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
                source.parameters.len() <= target.parameters.len()
                    && source
                        .parameters
                        .iter()
                        .zip(&target.parameters)
                        .all(|(source, target)| self.is_assignable(*target, *source))
                    && self.is_assignable(source.return_type, target.return_type)
            }
            (TypeKind::Function(source), TypeKind::Overload(targets)) => {
                targets.iter().any(|target| {
                    source.parameters.len() == target.parameters.len()
                        && source
                            .parameters
                            .iter()
                            .zip(&target.parameters)
                            .all(|(source, target)| self.is_assignable(*target, *source))
                        && self.is_assignable(source.return_type, target.return_type)
                })
            }
            (TypeKind::Overload(sources), TypeKind::Function(target)) => {
                sources.iter().any(|source| {
                    source.parameters.len() == target.parameters.len()
                        && source
                            .parameters
                            .iter()
                            .zip(&target.parameters)
                            .all(|(source, target)| self.is_assignable(*target, *source))
                        && self.is_assignable(source.return_type, target.return_type)
                })
            }
            (TypeKind::Overload(sources), TypeKind::Overload(targets)) => {
                targets.iter().all(|target| {
                    sources.iter().any(|source| {
                        source.parameters.len() == target.parameters.len()
                            && source
                                .parameters
                                .iter()
                                .zip(&target.parameters)
                                .all(|(source, target)| self.is_assignable(*target, *source))
                            && self.is_assignable(source.return_type, target.return_type)
                    })
                })
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

    fn exact_optional_property_mismatch(&self, source: TypeId, target: TypeId) -> bool {
        if !self.options.exact_optional_property_types {
            return false;
        }
        let Some(Type {
            kind: TypeKind::Object(target),
            ..
        }) = self.result.types.get(target)
        else {
            return false;
        };
        target.optional_properties.iter().any(|name| {
            let Some(target_type) = target.properties.get(name) else {
                return false;
            };
            self.property_types(source, name)
                .into_iter()
                .any(|source_type| {
                    self.type_includes_undefined(source_type)
                        && !self.is_assignable(source_type, *target_type)
                })
        })
    }

    #[allow(clippy::too_many_lines)]
    fn import_type(&mut self, descriptor: &TypeDescriptor) -> TypeId {
        match descriptor {
            TypeDescriptor::Any => self.result.types.any(),
            TypeDescriptor::TypeParameter(name) => {
                if let Some(type_id) = self.imported_type_parameters.get(name) {
                    *type_id
                } else {
                    let type_id = self.result.types.alloc(TypeKind::TypeParameter {
                        name: name.clone(),
                        constraint: None,
                    });
                    self.imported_type_parameters.insert(name.clone(), type_id);
                    type_id
                }
            }
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
            TypeDescriptor::ConstEnum(enum_type) => {
                let type_id = self.import_type(enum_type);
                self.const_enum_types.insert(type_id);
                type_id
            }
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
                if members.contains(&self.result.types.any())
                    && members.contains(&self.result.types.undefined())
                {
                    self.result.types.alloc(TypeKind::Union(members))
                } else {
                    self.result.types.union(members)
                }
            }
            TypeDescriptor::Intersection(members) => {
                let members = members
                    .iter()
                    .map(|member| self.import_type(member))
                    .collect::<Vec<_>>();
                self.result.types.intersection(members)
            }
            TypeDescriptor::Object {
                properties,
                optional_properties,
                readonly_properties,
                getter_properties,
            } => {
                let properties = properties
                    .iter()
                    .map(|(name, property)| (name.clone(), self.import_type(property)))
                    .collect();
                self.result.types.alloc(TypeKind::Object(ObjectType {
                    properties,
                    optional_properties: optional_properties.clone(),
                    readonly_properties: readonly_properties.clone(),
                    getter_properties: getter_properties.clone(),
                    setter_properties: BTreeSet::new(),
                }))
            }
            TypeDescriptor::Function {
                parameters,
                return_type,
                parameters_optional,
            } => {
                let parameters = parameters
                    .iter()
                    .map(|parameter| self.import_type(parameter))
                    .collect();
                let return_type = self.import_type(return_type);
                self.result.types.alloc(TypeKind::Function(FunctionType {
                    parameters,
                    return_type,
                    parameters_optional: *parameters_optional,
                }))
            }
            TypeDescriptor::Constructor {
                parameters,
                return_type,
                parameters_optional,
            } => {
                let parameters = parameters
                    .iter()
                    .map(|parameter| self.import_type(parameter))
                    .collect();
                let return_type = self.import_type(return_type);
                self.result.types.alloc(TypeKind::Constructor(FunctionType {
                    parameters,
                    return_type,
                    parameters_optional: *parameters_optional,
                }))
            }
            TypeDescriptor::Overload(signatures) => {
                let signatures = signatures
                    .iter()
                    .filter_map(|signature| {
                        let TypeDescriptor::Function {
                            parameters,
                            return_type,
                            parameters_optional,
                        } = signature
                        else {
                            return None;
                        };
                        Some(FunctionType {
                            parameters: parameters
                                .iter()
                                .map(|parameter| self.import_type(parameter))
                                .collect(),
                            return_type: self.import_type(return_type),
                            parameters_optional: *parameters_optional,
                        })
                    })
                    .collect();
                self.result.types.alloc(TypeKind::Overload(signatures))
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
                let optional_properties = object.optional_properties;
                let readonly_properties = object.readonly_properties;
                let getter_properties = object.getter_properties;
                let setter_properties = object.setter_properties;
                let properties = object
                    .properties
                    .into_iter()
                    .map(|(name, property)| (name, self.widen_literal(property)))
                    .collect();
                self.result.types.alloc(TypeKind::Object(ObjectType {
                    properties,
                    optional_properties,
                    readonly_properties,
                    getter_properties,
                    setter_properties,
                }))
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
        let code = if self.exact_optional_property_mismatch(actual, expected) {
            2375
        } else {
            2322
        };
        self.error(
            node,
            code,
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

    fn check_unused_symbols(&mut self) {
        if !self.options.no_unused_locals && !self.options.no_unused_parameters {
            return;
        }
        let diagnostics = self
            .bindings
            .symbols
            .iter()
            .filter(|symbol| self.symbol_reads.get(&symbol.id).copied().unwrap_or(0) == 0)
            .filter(|symbol| {
                !self
                    .bindings
                    .exports
                    .iter()
                    .any(|(_, export)| export == symbol.id)
            })
            .filter_map(|symbol| {
                let declaration = *symbol.declarations.first()?;
                let node = self.arena.get(declaration)?;
                let is_parameter = matches!(node.data, NodeData::ParameterDeclaration(_));
                if is_parameter {
                    if !self.options.no_unused_parameters || symbol.name.starts_with('_') {
                        return None;
                    }
                } else if !self.options.no_unused_locals
                    || !matches!(node.data, NodeData::VariableDeclaration(_))
                    || !self.is_local_declaration(declaration)
                {
                    return None;
                }
                Some((declaration, symbol.name.clone()))
            })
            .collect::<Vec<_>>();
        for (node, name) in diagnostics {
            self.error(node, 6133, [name]);
        }
    }

    fn is_local_declaration(&self, declaration: NodeId) -> bool {
        let mut parent = self.arena.get(declaration).and_then(|node| node.parent);
        while let Some(node_id) = parent {
            let Some(node) = self.arena.get(node_id) else {
                break;
            };
            if matches!(
                node.data,
                NodeData::FunctionDeclaration(_)
                    | NodeData::MethodDeclaration(_)
                    | NodeData::ArrowFunction(_)
            ) {
                return true;
            }
            parent = node.parent;
        }
        false
    }
}

struct DeclarationReachability<'a> {
    arena: &'a NodeArena,
    bindings: &'a BindResult,
    children: HashMap<NodeId, Vec<NodeId>>,
    scopes: BTreeMap<NodeId, Vec<NodeId>>,
    retained: BTreeMap<NodeId, BTreeSet<NodeId>>,
    pending: VecDeque<NodeId>,
}

impl<'a> DeclarationReachability<'a> {
    fn analyze(
        arena: &'a NodeArena,
        bindings: &'a BindResult,
        source_file: NodeId,
        is_declaration_file: bool,
    ) -> BTreeMap<NodeId, BTreeSet<NodeId>> {
        let mut children = HashMap::<NodeId, Vec<NodeId>>::new();
        for (id, node) in arena.iter() {
            if let Some(parent) = node.parent {
                children.entry(parent).or_default().push(id);
            }
        }
        let mut analyzer = Self {
            arena,
            bindings,
            children,
            scopes: BTreeMap::new(),
            retained: BTreeMap::new(),
            pending: VecDeque::new(),
        };
        let Some(NodeData::SourceFile(source)) = arena.get(source_file).map(|node| &node.data)
        else {
            return BTreeMap::new();
        };
        let external = !bindings.exports.is_empty()
            || source.statements.nodes.iter().any(|statement| {
                arena.get(*statement).is_some_and(|statement| {
                    matches!(
                        statement.data,
                        NodeData::ImportDeclaration(_)
                            | NodeData::ImportEqualsDeclaration(_)
                            | NodeData::ExportDeclaration(_)
                            | NodeData::ExportAssignment(_)
                    )
                })
            });
        analyzer.collect_scope(
            source_file,
            &source.statements.nodes,
            is_declaration_file || !external,
            is_declaration_file,
        );
        analyzer.seed_roots();
        analyzer.trace_dependencies();
        analyzer.retained
    }

    fn collect_scope(
        &mut self,
        scope: NodeId,
        statements: &[NodeId],
        root_all: bool,
        implicit_ambient: bool,
    ) {
        self.scopes.insert(scope, statements.to_vec());
        self.retained.entry(scope).or_default();
        for statement in statements {
            let Some(NodeData::ModuleDeclaration(module)) =
                self.arena.get(*statement).map(|node| &node.data)
            else {
                continue;
            };
            let ambient =
                implicit_ambient || self.node_has_modifier(*statement, SyntaxKind::DeclareKeyword);
            let Some(body) = module.body else {
                continue;
            };
            match &self.arena.get(body).map(|node| &node.data) {
                Some(NodeData::ModuleBlock(block)) => {
                    self.collect_scope(body, &block.statements.nodes, ambient, ambient);
                }
                Some(NodeData::ModuleDeclaration(_)) => {
                    self.collect_scope(body, &[body], ambient, ambient);
                }
                _ => {}
            }
        }
        if root_all {
            for statement in statements {
                if self.is_declaration_statement(*statement) {
                    self.retain(*statement);
                }
            }
        }
    }

    fn seed_roots(&mut self) {
        let scopes = self.scopes.clone();
        for (scope, statements) in scopes {
            let already_rooted = self
                .retained
                .get(&scope)
                .is_some_and(|retained| !retained.is_empty());
            if already_rooted {
                continue;
            }
            for statement in statements {
                if self.node_has_modifier(statement, SyntaxKind::ExportKeyword)
                    || matches!(
                        self.arena.get(statement).map(|node| &node.data),
                        Some(NodeData::ExportDeclaration(_) | NodeData::ExportAssignment(_))
                    )
                {
                    self.retain(statement);
                }
            }
        }
    }

    fn trace_dependencies(&mut self) {
        while let Some(declaration) = self.pending.pop_front() {
            let mut stack = vec![declaration];
            while let Some(node_id) = stack.pop() {
                let Some(node) = self.arena.get(node_id) else {
                    continue;
                };
                match &node.data {
                    NodeData::TypeReferenceNode(reference) => {
                        self.retain_entity(reference.type_name);
                    }
                    NodeData::TypeQueryNode(query) => self.retain_entity(query.expr_name),
                    NodeData::ExpressionWithTypeArguments(expression) => {
                        self.retain_entity(expression.expression);
                    }
                    NodeData::ImportEqualsDeclaration(import) => {
                        self.retain_entity(import.module_reference);
                    }
                    NodeData::Block(_) | NodeData::ModuleBlock(_) if node_id != declaration => {
                        continue;
                    }
                    NodeData::ModuleDeclaration(_) if node_id != declaration => continue,
                    _ => {}
                }
                if let Some(children) = self.children.get(&node_id) {
                    stack.extend(children.iter().copied());
                }
            }
        }
    }

    fn retain_entity(&mut self, entity: NodeId) {
        let Some((identifier, name)) = self.leftmost_entity_name(entity) else {
            return;
        };
        let Some(symbol) = self.bindings.resolve_name_at(identifier, &name) else {
            return;
        };
        let target = self
            .bindings
            .symbols
            .get(symbol)
            .and_then(|symbol| symbol.target)
            .unwrap_or(symbol);
        let declarations = self
            .bindings
            .symbols
            .get(target)
            .map(|symbol| symbol.declarations.clone())
            .unwrap_or_default();
        for declaration in declarations {
            if let Some(statement) = self.declaration_statement(declaration) {
                self.retain(statement);
            }
        }
    }

    fn retain(&mut self, statement: NodeId) {
        let Some(scope) = self
            .arena
            .get(statement)
            .and_then(|node| node.parent)
            .filter(|parent| self.scopes.contains_key(parent))
        else {
            return;
        };
        if self.retained.entry(scope).or_default().insert(statement) {
            self.pending.push_back(statement);
        }
    }

    fn declaration_statement(&self, declaration: NodeId) -> Option<NodeId> {
        let mut current = declaration;
        loop {
            let parent = self.arena.get(current)?.parent?;
            if self.scopes.contains_key(&parent) {
                return Some(current);
            }
            current = parent;
        }
    }

    fn leftmost_entity_name(&self, entity: NodeId) -> Option<(NodeId, String)> {
        match &self.arena.get(entity)?.data {
            NodeData::Identifier(identifier) => Some((entity, identifier.text.clone())),
            NodeData::QualifiedName(name) => self.leftmost_entity_name(name.left),
            NodeData::PropertyAccessExpression(access) => {
                self.leftmost_entity_name(access.expression)
            }
            _ => None,
        }
    }

    fn node_has_modifier(&self, node: NodeId, kind: SyntaxKind) -> bool {
        let modifiers = match &self.arena.get(node).map(|node| &node.data) {
            Some(NodeData::VariableStatement(declaration)) => declaration.modifiers.as_ref(),
            Some(NodeData::FunctionDeclaration(declaration)) => declaration.modifiers.as_ref(),
            Some(NodeData::ClassDeclaration(declaration)) => declaration.modifiers.as_ref(),
            Some(NodeData::InterfaceDeclaration(declaration)) => declaration.modifiers.as_ref(),
            Some(NodeData::TypeAliasDeclaration(declaration)) => declaration.modifiers.as_ref(),
            Some(NodeData::EnumDeclaration(declaration)) => declaration.modifiers.as_ref(),
            Some(NodeData::ModuleDeclaration(declaration)) => declaration.modifiers.as_ref(),
            Some(NodeData::ImportEqualsDeclaration(declaration)) => declaration.modifiers.as_ref(),
            _ => None,
        };
        modifiers.is_some_and(|modifiers| {
            modifiers.list.nodes.iter().any(|modifier| {
                self.arena
                    .get(*modifier)
                    .is_some_and(|modifier| modifier.kind == kind)
            })
        })
    }

    fn is_declaration_statement(&self, statement: NodeId) -> bool {
        matches!(
            self.arena.get(statement).map(|node| &node.data),
            Some(
                NodeData::VariableStatement(_)
                    | NodeData::FunctionDeclaration(_)
                    | NodeData::ClassDeclaration(_)
                    | NodeData::InterfaceDeclaration(_)
                    | NodeData::TypeAliasDeclaration(_)
                    | NodeData::EnumDeclaration(_)
                    | NodeData::ModuleDeclaration(_)
                    | NodeData::ImportDeclaration(_)
                    | NodeData::ImportEqualsDeclaration(_)
                    | NodeData::ExportDeclaration(_)
                    | NodeData::ExportAssignment(_)
            )
        )
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

fn describe_declaration_symbol(
    source: &ProgramSource<'_>,
    symbol_id: SymbolId,
) -> Option<TypeDescriptor> {
    let symbol = source.bindings.symbols.get(symbol_id)?;
    let declarations = symbol
        .declarations
        .iter()
        .filter_map(|declaration| source.arena.get(*declaration))
        .collect::<Vec<_>>();
    if let Some(NodeData::TypeAliasDeclaration(alias)) = declarations.iter().find_map(|node| {
        matches!(&node.data, NodeData::TypeAliasDeclaration(_)).then_some(&node.data)
    }) {
        return Some(describe_alias(source, alias));
    }
    let function_declarations = declarations
        .iter()
        .filter_map(|node| {
            let NodeData::FunctionDeclaration(data) = &node.data else {
                return None;
            };
            Some(data.as_ref())
        })
        .collect::<Vec<_>>();
    if !function_declarations.is_empty() {
        let mut checker = Checker::new(source.arena, source.bindings);
        let signatures = function_declarations
            .iter()
            .filter(|declaration| function_declarations.len() == 1 || declaration.body.is_none())
            .map(|declaration| {
                let type_id = checker.function_type(declaration);
                describe_type(&checker.result.types, type_id)
            })
            .collect::<Vec<_>>();
        return if signatures.len() == 1 {
            signatures.into_iter().next()
        } else {
            Some(TypeDescriptor::Overload(signatures))
        };
    }
    let first_interface = declarations.iter().find_map(|node| {
        let NodeData::InterfaceDeclaration(data) = &node.data else {
            return None;
        };
        Some(data.as_ref())
    });
    if let Some(first) = first_interface {
        let mut checker = Checker::new(source.arena, source.bindings);
        let (parameters, arguments) =
            descriptor_parameters(&mut checker, first.type_parameters.as_ref());
        let mut properties = BTreeMap::new();
        for declaration in declarations {
            let NodeData::InterfaceDeclaration(data) = &declaration.data else {
                continue;
            };
            let object = checker.declared_object_type(
                data.type_parameters.as_ref(),
                data.heritage_clauses.as_ref(),
                &data.members.nodes,
                &arguments,
            );
            if let TypeKind::Object(object) = checker.result.types.get(object)?.kind.clone() {
                properties.extend(object.properties);
            }
        }
        let body = checker.result.types.alloc(TypeKind::Object(ObjectType {
            properties,
            ..ObjectType::default()
        }));
        let body = describe_type(&checker.result.types, body);
        return Some(if parameters.is_empty() {
            body
        } else {
            TypeDescriptor::Alias {
                parameters,
                body: Box::new(body),
            }
        });
    }
    let class = declarations.iter().find_map(|node| {
        let NodeData::ClassDeclaration(data) = &node.data else {
            return None;
        };
        Some(data.as_ref())
    })?;
    let mut checker = Checker::new(source.arena, source.bindings);
    let (parameters, arguments) =
        descriptor_parameters(&mut checker, class.type_parameters.as_ref());
    let object = checker.declared_object_type(
        class.type_parameters.as_ref(),
        class.heritage_clauses.as_ref(),
        &class.members.nodes,
        &arguments,
    );
    let body = describe_type(&checker.result.types, object);
    Some(if parameters.is_empty() {
        body
    } else {
        TypeDescriptor::Alias {
            parameters,
            body: Box::new(body),
        }
    })
}

fn descriptor_parameters(
    checker: &mut Checker<'_>,
    type_parameters: Option<&ts_ast::NodeList>,
) -> (Vec<String>, Vec<TypeId>) {
    let mut names = Vec::new();
    let mut types = Vec::new();
    if let Some(parameters) = type_parameters {
        for parameter in &parameters.nodes {
            let Some(NodeData::TypeParameterDeclaration(parameter)) =
                checker.arena.get(*parameter).map(|node| &node.data)
            else {
                continue;
            };
            let Some(name) = checker.property_name(parameter.name) else {
                continue;
            };
            types.push(checker.result.types.alloc(TypeKind::TypeParameter {
                name: name.clone(),
                constraint: None,
            }));
            names.push(name);
        }
    }
    (names, types)
}

fn is_core_library_name(name: &str) -> bool {
    matches!(
        name,
        "Array"
            | "ReadonlyArray"
            | "Promise"
            | "PromiseLike"
            | "PromiseConstructor"
            | "String"
            | "StringConstructor"
            | "ArrayConstructor"
            | "Object"
            | "Function"
            | "CallableFunction"
            | "NewableFunction"
            | "IArguments"
            | "RegExp"
            | "Awaited"
            | "Partial"
            | "Required"
            | "Readonly"
            | "Pick"
            | "Record"
            | "Exclude"
            | "Extract"
            | "Omit"
            | "NonNullable"
            | "Parameters"
            | "ConstructorParameters"
            | "ReturnType"
            | "InstanceType"
    )
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
        TypeKind::Object(object) => TypeDescriptor::Object {
            properties: object
                .properties
                .iter()
                .map(|(name, property)| (name.clone(), describe_type(types, *property)))
                .collect(),
            optional_properties: object.optional_properties.clone(),
            readonly_properties: object.readonly_properties.clone(),
            getter_properties: object.getter_properties.clone(),
        },
        TypeKind::Function(function) => TypeDescriptor::Function {
            parameters: function
                .parameters
                .iter()
                .map(|parameter| describe_type(types, *parameter))
                .collect(),
            return_type: Box::new(describe_type(types, function.return_type)),
            parameters_optional: function.parameters_optional,
        },
        TypeKind::Constructor(constructor) => TypeDescriptor::Constructor {
            parameters: constructor
                .parameters
                .iter()
                .map(|parameter| describe_type(types, *parameter))
                .collect(),
            return_type: Box::new(describe_type(types, constructor.return_type)),
            parameters_optional: constructor.parameters_optional,
        },
        TypeKind::Overload(signatures) => TypeDescriptor::Overload(
            signatures
                .iter()
                .map(|signature| TypeDescriptor::Function {
                    parameters: signature
                        .parameters
                        .iter()
                        .map(|parameter| describe_type(types, *parameter))
                        .collect(),
                    return_type: Box::new(describe_type(types, signature.return_type)),
                    parameters_optional: signature.parameters_optional,
                })
                .collect(),
        ),
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
            .unwrap_or_else(|| descriptor.clone()),
        TypeDescriptor::ConstEnum(enum_type) => {
            TypeDescriptor::ConstEnum(Box::new(substitute_descriptor(enum_type, substitutions)))
        }
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
        TypeDescriptor::Object {
            properties,
            optional_properties,
            readonly_properties,
            getter_properties,
        } => TypeDescriptor::Object {
            properties: properties
                .iter()
                .map(|(name, property)| {
                    (name.clone(), substitute_descriptor(property, substitutions))
                })
                .collect(),
            optional_properties: optional_properties.clone(),
            readonly_properties: readonly_properties.clone(),
            getter_properties: getter_properties.clone(),
        },
        TypeDescriptor::Function {
            parameters,
            return_type,
            parameters_optional,
        } => TypeDescriptor::Function {
            parameters: parameters
                .iter()
                .map(|parameter| substitute_descriptor(parameter, substitutions))
                .collect(),
            return_type: Box::new(substitute_descriptor(return_type, substitutions)),
            parameters_optional: *parameters_optional,
        },
        TypeDescriptor::Constructor {
            parameters,
            return_type,
            parameters_optional,
        } => TypeDescriptor::Constructor {
            parameters: parameters
                .iter()
                .map(|parameter| substitute_descriptor(parameter, substitutions))
                .collect(),
            return_type: Box::new(substitute_descriptor(return_type, substitutions)),
            parameters_optional: *parameters_optional,
        },
        TypeDescriptor::Overload(signatures) => TypeDescriptor::Overload(
            signatures
                .iter()
                .map(|signature| substitute_descriptor(signature, substitutions))
                .collect(),
        ),
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
        || (existing.contains(ts_binder::SymbolFlags::NAMESPACE_MODULE)
            && new.contains(ts_binder::SymbolFlags::NAMESPACE_MODULE))
}

fn merge_global_descriptor(existing: &mut TypeDescriptor, new: TypeDescriptor) {
    match (existing, new) {
        (
            TypeDescriptor::Object {
                properties: existing,
                optional_properties: existing_optional,
                readonly_properties: existing_readonly,
                getter_properties: existing_getters,
            },
            TypeDescriptor::Object {
                properties: new,
                optional_properties: new_optional,
                readonly_properties: new_readonly,
                getter_properties: new_getters,
            },
        ) => {
            for (name, descriptor) in new {
                if let Some(existing) = existing.get_mut(&name) {
                    merge_global_descriptor(existing, descriptor);
                } else {
                    existing.insert(name, descriptor);
                }
            }
            existing_optional.extend(new_optional);
            existing_readonly.extend(new_readonly);
            existing_getters.extend(new_getters);
        }
        (
            TypeDescriptor::Alias {
                parameters: existing_parameters,
                body: existing_body,
            },
            TypeDescriptor::Alias {
                parameters: new_parameters,
                body: new_body,
            },
        ) if *existing_parameters == new_parameters => {
            if let (
                TypeDescriptor::Object {
                    properties: existing,
                    optional_properties: existing_optional,
                    readonly_properties: existing_readonly,
                    getter_properties: existing_getters,
                },
                TypeDescriptor::Object {
                    properties: new,
                    optional_properties: new_optional,
                    readonly_properties: new_readonly,
                    getter_properties: new_getters,
                },
            ) = (existing_body.as_mut(), *new_body)
            {
                for (name, descriptor) in new {
                    if let Some(existing) = existing.get_mut(&name) {
                        merge_global_descriptor(existing, descriptor);
                    } else {
                        existing.insert(name, descriptor);
                    }
                }
                existing_optional.extend(new_optional);
                existing_readonly.extend(new_readonly);
                existing_getters.extend(new_getters);
            }
        }
        _ => {}
    }
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
            Self::Function => matches!(kind, TypeKind::Function(_) | TypeKind::Overload(_)),
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

fn enum_member_reference_name(
    arena: &NodeArena,
    reference: NodeId,
    enum_name: &str,
) -> Option<String> {
    match &arena.get(reference)?.data {
        NodeData::Identifier(identifier) => Some(identifier.text.clone()),
        NodeData::PropertyAccessExpression(access)
            if identifier_text(arena, access.expression) == Some(enum_name) =>
        {
            property_name_text(arena, access.name)
        }
        NodeData::ElementAccessExpression(access)
            if identifier_text(arena, access.expression) == Some(enum_name) =>
        {
            property_name_text(arena, access.argument_expression)
        }
        _ => None,
    }
}

fn is_const_enum_expression(arena: &NodeArena, expression: NodeId) -> bool {
    let Some(node) = arena.get(expression) else {
        return false;
    };
    match &node.data {
        NodeData::NumericLiteral(_)
        | NodeData::StringLiteral(_)
        | NodeData::NoSubstitutionTemplateLiteral(_)
        | NodeData::Identifier(_)
        | NodeData::PropertyAccessExpression(_)
        | NodeData::ElementAccessExpression(_) => true,
        NodeData::ParenthesizedExpression(data) => is_const_enum_expression(arena, data.expression),
        NodeData::PrefixUnaryExpression(data) => {
            matches!(
                data.operator,
                SyntaxKind::PlusToken | SyntaxKind::MinusToken | SyntaxKind::TildeToken
            ) && is_const_enum_expression(arena, data.operand)
        }
        NodeData::BinaryExpression(data) => {
            let operator = arena.get(data.operator_token).map(|token| token.kind);
            matches!(
                operator,
                Some(
                    SyntaxKind::BarToken
                        | SyntaxKind::AmpersandToken
                        | SyntaxKind::CaretToken
                        | SyntaxKind::GreaterThanGreaterThanToken
                        | SyntaxKind::GreaterThanGreaterThanGreaterThanToken
                        | SyntaxKind::LessThanLessThanToken
                        | SyntaxKind::AsteriskToken
                        | SyntaxKind::SlashToken
                        | SyntaxKind::PlusToken
                        | SyntaxKind::MinusToken
                        | SyntaxKind::PercentToken
                        | SyntaxKind::AsteriskAsteriskToken
                )
            ) && is_const_enum_expression(arena, data.left)
                && is_const_enum_expression(arena, data.right)
        }
        _ => false,
    }
}

fn property_name_text(arena: &NodeArena, node: NodeId) -> Option<String> {
    match &arena.get(node)?.data {
        NodeData::Identifier(identifier) => Some(identifier.text.clone()),
        NodeData::StringLiteral(literal) => Some(literal.text.clone()),
        NodeData::NoSubstitutionTemplateLiteral(literal) => Some(literal.text.clone()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

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

    use super::{
        Checker, CheckerOptions, EnumConstantValue, ObjectType, ProgramSource, TypeKind,
        check_program, check_source_file, check_source_file_with_options,
    };

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
            ..ObjectType::default()
        }));
        let right = checker.result.types.alloc(TypeKind::Object(ObjectType {
            properties: BTreeMap::from([("right".into(), number)]),
            ..ObjectType::default()
        }));
        let intersection = checker.result.types.intersection([left, right]);
        let target = checker.result.types.alloc(TypeKind::Object(ObjectType {
            properties: BTreeMap::from([("left".into(), string), ("right".into(), number)]),
            ..ObjectType::default()
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
    fn evaluates_const_enum_members_and_publishes_their_values() {
        let parsed = parse_source_file(
            r#"
                const enum E {
                    A = 2,
                    B = A + 3,
                    C,
                    Complement = ~C,
                    Shift = Complement << 1,
                    Qualified = E["B"],
                    Text = "ok",
                }
                const b: 5 = E.B;
                const c: 6 = E.C;
                const shift: -14 = E.Shift;
                const qualified: 5 = E.Qualified;
                const text: "ok" = E.Text;
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let result = check_source_file(&parsed.arena, parsed.source_file, &bindings);

        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert_eq!(
            result
                .enum_member_values
                .values()
                .cloned()
                .collect::<Vec<_>>(),
            [
                EnumConstantValue::Number(2.0),
                EnumConstantValue::Number(5.0),
                EnumConstantValue::Number(6.0),
                EnumConstantValue::Number(-7.0),
                EnumConstantValue::Number(-14.0),
                EnumConstantValue::Number(5.0),
                EnumConstantValue::String("ok".into()),
            ]
        );
    }

    #[test]
    fn publishes_const_enum_access_values_for_local_forms_and_aliases() {
        let parsed = parse_source_file(
            r#"
                const enum E { A = 3, Text = "text" }
                namespace N { export const enum Inner { B = 4 } }
                import Alias = N.Inner;
                const dot = E.A;
                const bracket = E["A"];
                const template = E[`A`];
                const nested = N.Inner.B;
                const alias = Alias.B;
                const text = E.Text;
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let result = check_source_file(&parsed.arena, parsed.source_file, &bindings);

        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert_eq!(result.enum_access_values.len(), 6);
        assert_eq!(
            result
                .enum_access_values
                .values()
                .filter(|value| **value == EnumConstantValue::Number(3.0))
                .count(),
            3
        );
        assert_eq!(
            result
                .enum_access_values
                .values()
                .filter(|value| **value == EnumConstantValue::Number(4.0))
                .count(),
            2
        );
        assert!(
            result
                .enum_access_values
                .values()
                .any(|value| value == &EnumConstantValue::String("text".into()))
        );
        assert!(result.enum_access_values.keys().all(|node| matches!(
            parsed.arena.get(*node).map(|node| &node.data),
            Some(NodeData::PropertyAccessExpression(_) | NodeData::ElementAccessExpression(_))
        )));
    }

    #[test]
    fn publishes_const_enum_access_values_across_imports() {
        let dependency = parse_source_file(r#"export const enum E { A = 7, Text = "imported" }"#);
        let consumer = parse_source_file(
            r#"
                import { E } from "./dependency";
                import * as ns from "./dependency";
                const direct = E.A;
                const text = E["Text"];
                const namespaced = ns.E.A;
            "#,
        );
        assert!(
            dependency.diagnostics.is_empty(),
            "{:?}",
            dependency.diagnostics
        );
        assert!(
            consumer.diagnostics.is_empty(),
            "{:?}",
            consumer.diagnostics
        );
        let dependency_bindings = bind_source_file(&dependency.arena, dependency.source_file);
        let consumer_bindings = bind_source_file(&consumer.arena, consumer.source_file);
        let dependency_modules = BTreeMap::new();
        let consumer_modules = BTreeMap::from([("./dependency".into(), 0)]);
        let checked = check_program(&[
            ProgramSource {
                arena: &dependency.arena,
                source_file: dependency.source_file,
                bindings: &dependency_bindings,
                resolved_modules: &dependency_modules,
                is_default_library: false,
                skip_diagnostics: false,
                checker_options: CheckerOptions::default(),
            },
            ProgramSource {
                arena: &consumer.arena,
                source_file: consumer.source_file,
                bindings: &consumer_bindings,
                resolved_modules: &consumer_modules,
                is_default_library: false,
                skip_diagnostics: false,
                checker_options: CheckerOptions::default(),
            },
        ]);

        assert!(
            checked.files[1].diagnostics.is_empty(),
            "{:?}",
            checked.files[1].diagnostics
        );
        assert_eq!(
            checked.files[1]
                .enum_access_values
                .values()
                .cloned()
                .collect::<Vec<_>>(),
            [
                EnumConstantValue::Number(7.0),
                EnumConstantValue::String("imported".into()),
                EnumConstantValue::Number(7.0),
            ]
        );
    }

    #[test]
    fn reports_invalid_const_enum_initializers() {
        let parsed = parse_source_file(
            r"
                declare function runtime(): number;
                const enum Bad {
                    Forward = Later,
                    Later = 1,
                    Runtime = runtime(),
                    Conditional = (true ? 1 : 2),
                    Infinite = 1 / 0,
                    NotNumber = 0 / 0,
                }
            ",
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
            [2651, 2474, 2474, 2477, 2478]
        );
    }

    #[test]
    fn restricts_const_enum_object_and_element_access_usage() {
        let parsed = parse_source_file(
            r#"
                const enum E { A, Text = "text", MissingInitializer }
                declare const key: string;
                const object = E;
                const dynamic = E[key];
                const numeric = E[0];
                const valid = E["A"];
                const template = E[`A`];
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
            [1061, 2475, 2476, 2476]
        );
    }

    #[test]
    fn checks_modified_arrow_parameters_and_constructor_parameter_properties() {
        let parsed = parse_source_file(
            r"
                const v = (public x: string) => x;
                v(1);
                class C { constructor(public readonly value: string) {} }
                declare const c: C;
                const text: string = c.value;
                const bad: number = c.value;
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(
            bindings.diagnostics.is_empty(),
            "{:?}",
            bindings.diagnostics
        );
        let result = check_source_file(&parsed.arena, parsed.source_file, &bindings);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2345, 2322]
        );
    }

    #[test]
    fn infers_class_expression_constructor_and_instance_types() {
        let parsed = parse_source_file(
            r#"
                const Box = class NamedBox {
                    constructor(public readonly value: string) {}
                    method(): string { return this.value; }
                };
                const Empty = class {};
                const box = new Box("ok");
                const text: string = box.value;
                box.value = "changed";
                new Box(1);
                Box();
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(
            bindings.diagnostics.is_empty(),
            "{:?}",
            bindings.diagnostics
        );
        let result = check_source_file(&parsed.arena, parsed.source_file, &bindings);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2540, 2345, 2349]
        );

        let box_symbol = bindings.root_scope().unwrap().symbols.get("Box").unwrap();
        let constructor_type = result.type_of_symbol(box_symbol).unwrap();
        let TypeKind::Constructor(constructor) = &result.types.get(constructor_type).unwrap().kind
        else {
            panic!("expected constructor type");
        };
        assert_eq!(constructor.parameters, [result.types.string()]);
        let TypeKind::Object(instance) = &result.types.get(constructor.return_type).unwrap().kind
        else {
            panic!("expected instance type");
        };
        assert!(instance.properties.contains_key("value"));
        assert!(instance.properties.contains_key("method"));
        assert!(instance.readonly_properties.contains("value"));
        let empty_symbol = bindings.root_scope().unwrap().symbols.get("Empty").unwrap();
        let empty_type = result.type_of_symbol(empty_symbol).unwrap();
        let TypeKind::Constructor(empty_constructor) = &result.types.get(empty_type).unwrap().kind
        else {
            panic!("expected anonymous class constructor type");
        };
        assert!(empty_constructor.parameters.is_empty());
        assert!(matches!(
            result
                .types
                .get(empty_constructor.return_type)
                .unwrap()
                .kind,
            TypeKind::Object(_)
        ));

        let declaration = bindings.symbols.get(box_symbol).unwrap().declarations[0];
        assert_eq!(result.type_of_node(declaration), Some(constructor_type));
        let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        assert_eq!(
            result.type_of_node(variable.initializer.unwrap()),
            Some(constructor_type)
        );
    }

    #[test]
    fn checks_contextual_this_for_classes_in_nested_control_flow() {
        let parsed = parse_source_file(
            r#"
                while (0) {
                    class A { methodA() { this; } }
                    class B {
                        methodB() {
                            this.methodA;
                            this.methodB;
                        }
                    }
                }
                function f() {
                    return typeof class {} === "function";
                }
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
            [2339]
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
    fn javascript_function_parameters_are_optional_for_minimum_arity() {
        let parsed = parse_source_file(
            r"
                function f2(x) {}
                f2();
                f2(1, 2, 3);
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);

        let javascript = check_source_file_with_options(
            &parsed.arena,
            parsed.source_file,
            &bindings,
            CheckerOptions {
                is_javascript_file: true,
                ..CheckerOptions::default()
            },
        );
        assert_eq!(javascript.diagnostics.len(), 1);
        assert_eq!(javascript.diagnostics[0].diagnostic.code(), 2554);
        assert_eq!(
            javascript.diagnostics[0].diagnostic.render().unwrap(),
            "Expected 0-1 arguments, but got 3."
        );

        let typescript = check_source_file(&parsed.arena, parsed.source_file, &bindings);
        assert_eq!(
            typescript
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.render().unwrap())
                .collect::<Vec<_>>(),
            [
                "Expected 1 arguments, but got 0.",
                "Expected 1 arguments, but got 3."
            ]
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

    #[test]
    fn evaluates_advanced_types_and_generic_heritage() {
        let parsed = parse_source_file(
            r#"
                interface Box<T> { value: T; }
                interface NamedBox<T> extends Box<T> { name: string; }
                class Model<T> extends Box<T> { value: T; extra: T; }
                interface ReadonlyArray<T> { readonly length: number; readonly [n: number]: T; }
                interface PromiseLike<T> { value: T; }

                type Keys<T> = keyof T;
                type Value<T, K extends keyof T> = T[K];
                type Optional<T> = { [K in keyof T]?: T[K] };
                type Kind<T> = T extends string ? number : boolean;

                const key: Keys<NamedBox<number>> = "value";
                const badKey: Keys<NamedBox<number>> = "missing";
                const value: Value<NamedBox<number>, "value"> = 1;
                const badValue: Value<NamedBox<number>, "value"> = "wrong";
                const optional: Optional<NamedBox<number>> = { name: "box", value: 1 };
                const model: Model<number> = { value: 1, extra: 2 };
                const item: ReadonlyArray<string>[number] = "item";
                const promised: PromiseLike<number> = { value: 1 };
                const stringKind: Kind<string> = 1;
                const numberKind: Kind<number> = true;
                const badKind: Kind<string> = false;
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
            [2322, 2322, 2322],
            "{:?}",
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.render().unwrap())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn evaluates_enums_structural_operators_mapped_types_and_conditional_infer() {
        let parsed = parse_source_file(
            r#"
                enum Direction { Up, Down = 4, Next, Label = "label" }
                const direction: Direction = Direction.Next;
                const nextValue: 5 = Direction.Next;
                type DirectionKey = keyof typeof Direction;
                const directionKey: DirectionKey = "Label";
                const badDirectionKey: DirectionKey = "Missing";
                const badDirection: Direction = "label";
                const badMember: 4 = Direction.Next;

                type Model = { readonly id: number; name?: string; active: boolean };
                type ModelKey = keyof Model;
                type ModelValue = Model[ModelKey];
                type MutableRequired<T> = { -readonly [K in keyof T]-?: T[K] };
                type WithoutId<T> = {
                    [K in keyof T as K extends "id" ? never : K]: T[K]
                };
                const key: ModelKey = "name";
                const badKey: ModelKey = "missing";
                const value: ModelValue = true;
                const required: MutableRequired<Model> = {
                    id: 1, name: "model", active: true
                };
                const missingRequired: MutableRequired<Model> = { id: 1, active: true };
                const withoutId: WithoutId<Model> = { name: "model", active: true };
                const badWithoutId: WithoutId<Model> = { active: true, id: 1 };

                type Element<T> = T extends readonly (infer U)[] ? U : never;
                type Result<T> = T extends (...inputs: any[]) => infer R ? R : never;
                type Strings<T> = T extends string ? T : never;
                const element: Element<readonly number[]> = 1;
                const badElement: Element<string[]> = 1;
                const result: Result<(input: number) => string> = "ok";
                const badResult: Result<() => boolean> = "wrong";
                const distributed: Strings<string | number> = "ok";
                const badDistributed: Strings<string | number> = 1;
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(
            bindings.diagnostics.is_empty(),
            "{:?}",
            bindings.diagnostics
        );
        let result = check_source_file(&parsed.arena, parsed.source_file, &bindings);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2322, 2322, 2322, 2322, 2322, 2353, 2322, 2322, 2322],
            "{:?}",
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.render().unwrap())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn selects_parsed_overload_signatures() {
        let parsed = parse_source_file(
            r#"
                function pick(value: string): string;
                function pick(value: number): number;
                function pick(value: string | number): string | number { return value; }
                const text: string = pick("text");
                const count: number = pick(1);
                const bad: boolean = pick(1);
                pick(true);
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
            [2322, 2345]
        );
    }

    #[test]
    fn reports_missing_overload_implementations_and_implicit_any_returns() {
        let parsed = parse_source_file(
            r"
                namespace M { function missing(); }

                function valid(value: string): string;
                function valid(value: number): number;
                function valid(value: string | number): string | number { return value; }

                function misplaced(value: string): string;
                const gap = 1;
                function misplaced(value: string): string { return value; }

                declare function ambient();
                declare namespace Ambient { function nested(); }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let result = check_source_file_with_options(
            &parsed.arena,
            parsed.source_file,
            &bindings,
            CheckerOptions {
                no_implicit_any: true,
                ..CheckerOptions::default()
            },
        );
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2391, 7010, 2391, 7010, 7010],
            "{:?}",
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.render().unwrap())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn resolves_ambient_namespace_members_as_object_properties() {
        let parsed = parse_source_file(
            r"
                declare namespace A {
                    namespace AA {
                        function func(): number;
                        const value: string;
                    }
                }
                const numberValue: number = A.AA.func();
                const stringValue: string = A.AA.value;
                const bad: string = A.AA.func();
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(
            bindings.diagnostics.is_empty(),
            "{:?}",
            bindings.diagnostics
        );
        let result = check_source_file(&parsed.arena, parsed.source_file, &bindings);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2322]
        );
    }

    #[test]
    fn preserves_callable_types_when_functions_merge_with_namespaces() {
        let parsed = parse_source_file(
            r"
                function Factory(): number { return 1; }
                namespace Factory { export const version: number = 1; }
                const value: number = Factory();
                const version: number = Factory.version;
                const bad: string = Factory.version;
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        assert!(
            bindings.diagnostics.is_empty(),
            "{:?}",
            bindings.diagnostics
        );
        let result = check_source_file(&parsed.arena, parsed.source_file, &bindings);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2322]
        );
    }

    #[test]
    fn narrows_truthiness_discriminants_in_and_instanceof() {
        let parsed = parse_source_file(
            r#"
                type Shape =
                    { kind: "circle"; radius: number } |
                    { kind: "square"; side: number };
                function area(shape: Shape): number {
                    if (shape.kind === "circle") { return shape.radius; }
                    return shape.side;
                }

                type TextOrCount = { text: string } | { count: number };
                function inspect(value: TextOrCount): void {
                    if ("text" in value) {
                        const text: string = value.text;
                    } else {
                        const count: number = value.count;
                    }
                }

                class Dog { bark: string; }
                class Cat { meow: string; }
                function pet(value: Dog | Cat): void {
                    if (value instanceof Dog) {
                        value.bark;
                        value.meow;
                    } else {
                        value.meow;
                    }
                }

                function truthy(value: string | null): void {
                    if (value) {
                        const text: string = value;
                    } else {
                        const bad: number = value;
                    }
                }
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
            [2339, 2322],
            "{:?}",
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.render().unwrap())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn joins_assignments_and_checks_switch_returns_and_unreachable_code() {
        let parsed = parse_source_file(
            r#"
                function assign(flag: boolean): void {
                    let value: string | number = "start";
                    value = 1;
                    const numberValue: number = value;
                    if (flag) { value = "next"; } else { value = 2; }
                    const joined: string | number = value;
                    const bad: boolean = value;
                    while (flag) { value = 3; }
                    const loopJoined: string | number = value;
                }

                type Token = { kind: "a"; a: number } | { kind: "b"; b: string };
                function exhaustive(token: Token): string | number {
                    switch (token.kind) {
                        case "a": return token.a;
                        case "b": return token.b;
                    }
                }
                function incomplete(token: Token): string | number {
                    switch (token.kind) {
                        case "a": return token.a;
                    }
                }
                function unreachable(): number {
                    return 1;
                    const after = 2;
                }
                function thrown(): number { throw "done"; }
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
            [2322, 2355]
        );
    }

    #[test]
    fn enforces_control_flow_compiler_options() {
        let parsed = parse_source_file(
            r"
                function choose(value: boolean) { if (value) return 1; }
                function cases(value: number) {
                    switch (value) { case 1: value++; case 2: break; }
                }
                function unreachable() { return; const after = 1; }
                try { throw 1; } catch (error) { error.toFixed(); }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let result = check_source_file_with_options(
            &parsed.arena,
            parsed.source_file,
            &bindings,
            CheckerOptions {
                allow_unreachable_code: Some(false),
                no_fallthrough_cases_in_switch: true,
                no_implicit_returns: true,
                use_unknown_in_catch_variables: true,
                ..CheckerOptions::default()
            },
        );
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [7030, 7029, 7027, 18046]
        );
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.render().unwrap())
                .collect::<Vec<_>>(),
            [
                "Not all code paths return a value.",
                "Fallthrough case in switch.",
                "Unreachable code detected.",
                "'error' is of type 'unknown'.",
            ]
        );
    }

    #[test]
    fn checks_structural_optional_readonly_excess_and_generic_inference() {
        let parsed = parse_source_file(
            r#"
                interface Base { readonly id: number; label?: string; }
                interface Child extends Base { value: string; }
                const good: Child = { id: 1, value: "ok" };
                const missing: Child = { id: 1 };
                const excess: Child = { id: 1, value: "ok", extra: true };
                good.id = 2;

                function unwrap<T>(box: { value: T }): T { return box.value; }
                const inferred: number = unwrap({ value: 1 });
                const wrong: string = unwrap({ value: 1 });
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
            [2322, 2353, 2540, 2322]
        );
        assert_eq!(
            result.diagnostics[1].diagnostic.render().unwrap(),
            "Object literal may only specify known properties, and 'extra' does not exist in type '{ id: number; label: undefined | string; value: string }'."
        );
    }

    #[test]
    fn checks_accessor_property_types_and_accidental_calls() {
        let parsed = parse_source_file(
            r"
                class Model {
                    get value(): number { return 1; }
                    set label(value: string) {}
                    get callback(): () => number { return () => 1; }
                }
                declare const model: Model;
                const value: number = model.value;
                const label: string = model.label;
                const structural: { value: number } = model;
                const bad: { value: string } = model;
                model.value();
                model.label();
                const result: number = model.callback();
            ",
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
            [2322, 6234, 2349],
            "{:?}",
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.render().unwrap())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn models_abstract_properties_and_accessors_without_runtime_bodies() {
        let parsed = parse_source_file(
            r#"
                interface A {
                    prop: string;
                    raw: string;
                    m(): void;
                }
                abstract class B implements A {
                    abstract prop: string;
                    abstract raw: string;
                    abstract readonly ro: string;
                    abstract get readonlyProp(): string;
                    abstract set readonlyProp(value: string);
                    abstract m(): void;
                }
                class C extends B {
                    get prop() { return "foo"; }
                    set prop(value) {}
                    raw = "edge";
                    readonly ro = "readonly";
                    readonlyProp: string;
                    m() {}
                }
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let result = check_source_file(&parsed.arena, parsed.source_file, &bindings);

        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    }

    #[test]
    fn reports_abstract_property_inheritance_and_accessor_diagnostics() {
        let parsed = parse_source_file(
            r#"
                abstract class B {
                    abstract prop: string;
                    public abstract readonly ro: string;
                    abstract get readonlyProp(): string;
                    abstract m(): string;
                    abstract get mismatch(): string;
                    abstract set mismatch(value: number);
                }
                class C extends B {
                    readonly ro = "readonly";
                    abstract notAllowed: string;
                }
                let c = new C();
                c.ro = "error";

                abstract class WrongTypeProperty { abstract num: number; }
                class WrongTypePropertyImpl extends WrongTypeProperty {
                    num = "wrong";
                }
                abstract class WrongTypeAccessor { abstract get num(): number; }
                class WrongTypeAccessorImpl extends WrongTypeAccessor {
                    get num() { return "wrong"; }
                }
                class WrongTypeAccessorImpl2 extends WrongTypeAccessor {
                    num = "wrong";
                }

                abstract class AbstractAccessorMismatch {
                    abstract get p1(): string;
                    set p1(value: string) {}
                    get p2(): string { return "ok"; }
                    abstract set p2(value: string);
                }
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
            [2654, 1253, 2540, 2416, 2416, 2416, 2676, 2676, 2676, 2676]
        );
    }

    #[test]
    fn checks_contextual_this_in_object_literal_getter_inference() {
        let parsed = parse_source_file(
            r"
                export var basePrototype = {
                    get primaryPath() {
                        var self = this;
                        return self.collection.schema.primaryPath;
                    },
                };
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let result = check_source_file_with_options(
            &parsed.arena,
            parsed.source_file,
            &bindings,
            CheckerOptions {
                no_implicit_any: true,
                ..CheckerOptions::default()
            },
        );

        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [7023, 2339]
        );
        assert_eq!(
            result.diagnostics[1].diagnostic.render().unwrap(),
            "Property 'collection' does not exist on type '{ readonly primaryPath: any }'."
        );
        let symbol = bindings
            .root_scope()
            .unwrap()
            .symbols
            .get("basePrototype")
            .unwrap();
        let type_id = result.type_of_symbol(symbol).unwrap();
        let declaration = bindings.symbols.get(symbol).unwrap().declarations[0];
        assert_eq!(result.type_of_node(declaration), Some(type_id));
        let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let initializer = variable.initializer.unwrap();
        let initializer_type = result.type_of_node(initializer).unwrap();
        assert!(matches!(
            result.types.get(initializer_type).unwrap().kind,
            TypeKind::Object(_)
        ));
        let NodeData::ObjectLiteralExpression(literal) =
            &parsed.arena.get(initializer).unwrap().data
        else {
            panic!("expected object literal");
        };
        let getter = literal.properties.nodes[0];
        assert_eq!(result.type_of_node(getter), Some(result.types.any()));
        let TypeKind::Object(object) = &result.types.get(type_id).unwrap().kind else {
            panic!("expected object type");
        };
        assert!(object.getter_properties.contains("primaryPath"));
        assert!(object.readonly_properties.contains("primaryPath"));
        assert!(!object.setter_properties.contains("primaryPath"));
        assert_eq!(object.properties["primaryPath"], result.types.any());
    }

    #[test]
    fn describes_object_literal_getter_and_setter_properties() {
        let parsed = parse_source_file(
            r#"
                const value = {
                    get readonlyValue() { return "read"; },
                    set writeOnly(input: number) {},
                    get paired() { return "paired"; },
                    set paired(input: string) {},
                };
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let result = check_source_file(&parsed.arena, parsed.source_file, &bindings);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let symbol = bindings.root_scope().unwrap().symbols.get("value").unwrap();
        let type_id = result.type_of_symbol(symbol).unwrap();
        let TypeKind::Object(object) = &result.types.get(type_id).unwrap().kind else {
            panic!("expected object type");
        };

        assert_eq!(
            object.getter_properties,
            BTreeSet::from(["paired".into(), "readonlyValue".into()])
        );
        assert_eq!(
            object.setter_properties,
            BTreeSet::from(["paired".into(), "writeOnly".into()])
        );
        assert_eq!(
            object.readonly_properties,
            BTreeSet::from(["readonlyValue".into()])
        );
        assert!(matches!(
            result
                .types
                .get(object.properties["readonlyValue"])
                .unwrap()
                .kind,
            TypeKind::String
        ));
        assert!(matches!(
            result
                .types
                .get(object.properties["writeOnly"])
                .unwrap()
                .kind,
            TypeKind::Number
        ));
        assert!(matches!(
            result.types.get(object.properties["paired"]).unwrap().kind,
            TypeKind::String
        ));

        let declaration = bindings.symbols.get(symbol).unwrap().declarations[0];
        let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration).unwrap().data
        else {
            panic!("expected variable declaration");
        };
        let NodeData::ObjectLiteralExpression(literal) = &parsed
            .arena
            .get(variable.initializer.unwrap())
            .unwrap()
            .data
        else {
            panic!("expected object literal");
        };
        let accessor_types = literal
            .properties
            .nodes
            .iter()
            .map(|accessor| result.type_of_node(*accessor).unwrap())
            .collect::<Vec<_>>();
        assert!(matches!(
            result.types.get(accessor_types[0]).unwrap().kind,
            TypeKind::String
        ));
        assert!(matches!(
            result.types.get(accessor_types[1]).unwrap().kind,
            TypeKind::Number
        ));
        assert!(matches!(
            result.types.get(accessor_types[2]).unwrap().kind,
            TypeKind::String
        ));
        assert!(matches!(
            result.types.get(accessor_types[3]).unwrap().kind,
            TypeKind::String
        ));
    }

    #[test]
    fn reports_unresolved_type_references_once_in_annotated_declarations() {
        let parsed = parse_source_file(
            r"
                export class Q {
                    set bet(argument: DoesNotExist) {}
                }
                let value: MissingVariable;
                declare function take(argument: MissingParameter): MissingReturn;
                type MissingAliasUse = MissingAlias;
            ",
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
            [2304, 2304, 2304, 2304, 2304]
        );
        assert_eq!(
            result.diagnostics[0].diagnostic.render().unwrap(),
            "Cannot find name 'DoesNotExist'."
        );
    }

    #[test]
    fn resolves_local_namespace_generic_and_imported_type_references() {
        let dependency = parse_source_file("export interface Imported { value: string }");
        let consumer = parse_source_file(
            r#"
                import { Imported } from "./dependency";
                interface Local { value: string }
                namespace N { export interface Member { value: string } }
                class Valid<T> {
                    local: Local;
                    namespaced: N.Member;
                    values: Array<Local>;
                    set imported(value: Imported) {}
                    method(value: T): T { return value; }
                }
            "#,
        );
        assert!(
            dependency.diagnostics.is_empty(),
            "{:?}",
            dependency.diagnostics
        );
        assert!(
            consumer.diagnostics.is_empty(),
            "{:?}",
            consumer.diagnostics
        );
        let dependency_bindings = bind_source_file(&dependency.arena, dependency.source_file);
        let consumer_bindings = bind_source_file(&consumer.arena, consumer.source_file);
        let dependency_modules = BTreeMap::new();
        let consumer_modules = BTreeMap::from([("./dependency".into(), 0)]);
        let checked = check_program(&[
            ProgramSource {
                arena: &dependency.arena,
                source_file: dependency.source_file,
                bindings: &dependency_bindings,
                resolved_modules: &dependency_modules,
                is_default_library: false,
                skip_diagnostics: false,
                checker_options: CheckerOptions::default(),
            },
            ProgramSource {
                arena: &consumer.arena,
                source_file: consumer.source_file,
                bindings: &consumer_bindings,
                resolved_modules: &consumer_modules,
                is_default_library: false,
                skip_diagnostics: false,
                checker_options: CheckerOptions::default(),
            },
        ]);

        assert!(
            checked.files[1].diagnostics.is_empty(),
            "{:?}",
            checked.files[1].diagnostics
        );
    }

    #[test]
    fn retains_private_declarations_referenced_by_exported_types() {
        let parsed = parse_source_file(
            r"
                type T = { x: number };
                type Unused = { hidden: string };
                export interface I { value: T; }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let result = check_source_file(&parsed.arena, parsed.source_file, &bindings);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data
        else {
            panic!("expected source file");
        };
        let retained = result.declarations_to_emit(parsed.source_file).unwrap();

        assert_eq!(retained.len(), 2);
        assert!(retained.contains(&source.statements.nodes[0]));
        assert!(!retained.contains(&source.statements.nodes[1]));
        assert!(retained.contains(&source.statements.nodes[2]));
    }

    #[test]
    fn retains_transitive_namespace_alias_dependencies_but_not_their_private_members() {
        let parsed = parse_source_file(
            r"
                namespace M {
                    namespace N { class Hidden {} }
                    import R = N;
                    export import X = R;
                }
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let result = check_source_file(&parsed.arena, parsed.source_file, &bindings);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data
        else {
            panic!("expected source file");
        };
        let module_id = source.statements.nodes[0];
        let NodeData::ModuleDeclaration(module) = &parsed.arena.get(module_id).unwrap().data else {
            panic!("expected namespace");
        };
        let module_body = module.body.unwrap();
        let NodeData::ModuleBlock(block) = &parsed.arena.get(module_body).unwrap().data else {
            panic!("expected namespace body");
        };
        let nested_module = block.statements.nodes[0];
        let NodeData::ModuleDeclaration(nested) = &parsed.arena.get(nested_module).unwrap().data
        else {
            panic!("expected nested namespace");
        };
        let nested_body = nested.body.unwrap();

        assert_eq!(
            result
                .declarations_to_emit(parsed.source_file)
                .unwrap()
                .iter()
                .copied()
                .collect::<Vec<_>>(),
            [module_id]
        );
        assert_eq!(
            result
                .declarations_to_emit(module_body)
                .unwrap()
                .iter()
                .copied()
                .collect::<Vec<_>>(),
            block.statements.nodes
        );
        assert!(result.declarations_to_emit(nested_body).unwrap().is_empty());
    }

    #[test]
    fn checks_accessor_parameter_grammar() {
        let parsed = parse_source_file(
            r#"
                class InvalidAccessors {
                    get withParameter(value: number): number { return value; }
                    set none() {}
                    set optional(value?: string) {}
                    set initialized(value: string = "value") {}
                    set rest(...value: string[]) {}
                    set returns(value: string): void {}
                }
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
            [1054, 1049, 1051, 1052, 1053, 1095]
        );
    }

    #[test]
    fn enforces_exact_optional_property_write_types() {
        let parsed = parse_source_file(
            r#"
                declare function take(value: { text?: string }): void;
                take({ text: undefined });

                declare let options: {
                    text?: string;
                    explicit?: string | undefined;
                };
                const read: string | undefined = options.text;
                options.text = undefined;
                options["text"] = undefined;
                options.explicit = undefined;
                options["explicit"] = undefined;
                options.explicit = true;
            "#,
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let exact = check_source_file_with_options(
            &parsed.arena,
            parsed.source_file,
            &bindings,
            CheckerOptions {
                exact_optional_property_types: true,
                ..CheckerOptions::default()
            },
        );
        assert_eq!(
            exact
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2379, 2412, 2412, 2322],
            "{:?}",
            exact
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.render().unwrap())
                .collect::<Vec<_>>()
        );

        let legacy = check_source_file_with_options(
            &parsed.arena,
            parsed.source_file,
            &bindings,
            CheckerOptions::default(),
        );
        assert_eq!(
            legacy
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2322]
        );
    }

    #[test]
    fn reports_exact_optional_structural_assignment_diagnostics() {
        let parsed = parse_source_file(
            r"
                type Options = { text?: string };
                const initialized: Options = { text: undefined };
                let assigned: Options = {};
                assigned = { text: undefined };
                function take(value: Options): void {}
                take({ text: undefined });
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let exact = check_source_file_with_options(
            &parsed.arena,
            parsed.source_file,
            &bindings,
            CheckerOptions {
                exact_optional_property_types: true,
                ..CheckerOptions::default()
            },
        );
        assert_eq!(
            exact
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2375, 2375, 2379],
            "{:?}",
            exact
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.render().unwrap())
                .collect::<Vec<_>>()
        );

        let legacy = check_source_file_with_options(
            &parsed.arena,
            parsed.source_file,
            &bindings,
            CheckerOptions::default(),
        );
        assert!(legacy.diagnostics.is_empty(), "{:?}", legacy.diagnostics);
    }

    #[test]
    fn requires_delete_operands_to_be_optional() {
        let parsed = parse_source_file(
            r"
                interface Foo {
                    a: number;
                    b: number | undefined;
                    c: number | null;
                    d?: number;
                    e: number | undefined | null;
                    f?: number | undefined | null;
                    g: unknown;
                    h: any;
                    i: never;
                }
                declare const value: Foo;
                delete value.a;
                delete value.b;
                delete value.c;
                delete value.d;
                delete value.e;
                delete value.f;
                delete value.g;
                delete value.h;
                delete value.i;
            ",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);

        let exact = check_source_file_with_options(
            &parsed.arena,
            parsed.source_file,
            &bindings,
            CheckerOptions {
                exact_optional_property_types: true,
                strict_null_checks: true,
                ..CheckerOptions::default()
            },
        );
        assert_eq!(
            exact
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2790, 2790, 2790, 2790]
        );

        let legacy = check_source_file_with_options(
            &parsed.arena,
            parsed.source_file,
            &bindings,
            CheckerOptions {
                strict_null_checks: true,
                ..CheckerOptions::default()
            },
        );
        assert_eq!(
            legacy
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2790, 2790]
        );

        let loose = check_source_file_with_options(
            &parsed.arena,
            parsed.source_file,
            &bindings,
            CheckerOptions {
                strict_null_checks: false,
                ..CheckerOptions::default()
            },
        );
        assert!(loose.diagnostics.is_empty(), "{:?}", loose.diagnostics);
    }
}
