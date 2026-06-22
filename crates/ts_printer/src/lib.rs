//! Deterministic modern-JavaScript emission from the generated TypeScript AST.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::error::Error;
use std::fmt;

use ts_ast::{Node, NodeArena, NodeData, NodeId, NodeList, SyntaxKind};
use ts_binder::{BindResult, bind_source_file};
use ts_options::{JsxEmit, ModuleKind, PrinterSettings, ScriptTarget};
use ts_sourcemap::{SourceMap, SourceMapBuilder};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct EmitResult {
    pub code: String,
    pub source_map: Option<SourceMap>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EmitError {
    pub node: NodeId,
    pub kind: SyntaxKind,
}

/// One parsed AMD dependency pragma supplied by the compiler.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AmdDependency<'a> {
    pub path: &'a str,
    pub name: Option<&'a str>,
    pub comment_start: u32,
    pub comment_end: u32,
}

/// A checker-evaluated enum constant supplied for emission.
#[derive(Clone, Debug, PartialEq)]
pub enum EmitConstantValue {
    Number(f64),
    String(String),
}

/// Semantic and source-file metadata used while emitting one file.
#[derive(Debug)]
pub struct EmitContext<'a> {
    pub bindings: &'a BindResult,
    pub amd_module_name: Option<&'a str>,
    pub amd_dependencies: &'a [AmdDependency<'a>],
    pub enum_member_values: &'a BTreeMap<NodeId, EmitConstantValue>,
    pub enum_access_values: &'a BTreeMap<NodeId, EmitConstantValue>,
    pub preserve_const_enums: bool,
    pub inline_const_enums: bool,
}

#[derive(Clone, Copy)]
enum ConstEnumEmitMode {
    EraseAndInline,
    PreserveAndInline,
    PreserveRuntime,
}

impl ConstEnumEmitMode {
    const fn new(preserve: bool, inline: bool) -> Self {
        match (preserve, inline) {
            (false, _) => Self::EraseAndInline,
            (true, true) => Self::PreserveAndInline,
            (true, false) => Self::PreserveRuntime,
        }
    }

    const fn preserves_declarations(self) -> bool {
        !matches!(self, Self::EraseAndInline)
    }

    const fn inlines_accesses(self) -> bool {
        !matches!(self, Self::PreserveRuntime)
    }
}

impl fmt::Display for EmitError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "unsupported {:?} node at {:?}",
            self.kind, self.node
        )
    }
}

impl Error for EmitError {}

/// Emits one parsed source file as modern JavaScript.
///
/// # Errors
///
/// Returns an error when the tree contains a node not supported by the initial
/// emitter layer or references a missing arena node.
pub fn emit_source_file(arena: &NodeArena, source_file: NodeId) -> Result<EmitResult, EmitError> {
    emit_source_file_with_settings(
        arena,
        source_file,
        "source.ts",
        "",
        PrinterSettings {
            always_strict: false,
            target: ScriptTarget::EsNext,
            module: ModuleKind::EsNext,
            jsx: ts_options::JsxEmit::Preserve,
            emit_javascript: true,
            emit_declarations: false,
            source_map: false,
            inline_source_map: false,
        },
    )
}

/// Emits one source file using target, module, and source-map settings.
///
/// # Errors
///
/// Returns an error when the tree contains an unsupported or missing node.
#[allow(clippy::too_many_lines)]
pub fn emit_source_file_with_settings(
    arena: &NodeArena,
    source_file: NodeId,
    source_name: &str,
    source_text: &str,
    settings: PrinterSettings,
) -> Result<EmitResult, EmitError> {
    let bindings = bind_source_file(arena, source_file);
    emit_source_file_with_settings_and_bindings(
        arena,
        source_file,
        source_name,
        source_text,
        settings,
        &bindings,
    )
}

/// Emits one source file using existing binding information.
///
/// # Errors
///
/// Returns an error when the tree contains an unsupported or missing node.
#[allow(clippy::too_many_lines)]
pub fn emit_source_file_with_settings_and_bindings(
    arena: &NodeArena,
    source_file: NodeId,
    source_name: &str,
    source_text: &str,
    settings: PrinterSettings,
    bindings: &BindResult,
) -> Result<EmitResult, EmitError> {
    let empty_enum_values = BTreeMap::new();
    emit_source_file_with_context(
        arena,
        source_file,
        source_name,
        source_text,
        settings,
        &EmitContext {
            bindings,
            amd_module_name: None,
            amd_dependencies: &[],
            enum_member_values: &empty_enum_values,
            enum_access_values: &empty_enum_values,
            preserve_const_enums: true,
            inline_const_enums: false,
        },
    )
}

/// Emits one source file using existing bindings and parsed emit metadata.
///
/// # Errors
///
/// Returns an error when the tree contains an unsupported or missing node.
#[allow(clippy::too_many_lines)]
pub fn emit_source_file_with_context(
    arena: &NodeArena,
    source_file: NodeId,
    source_name: &str,
    source_text: &str,
    settings: PrinterSettings,
    context: &EmitContext<'_>,
) -> Result<EmitResult, EmitError> {
    if !settings.emit_javascript {
        return Ok(EmitResult::default());
    }
    let automatic_jsx = AutomaticJsxUsage::analyze(arena, settings.jsx);
    let enum_access_fallbacks = const_enum_access_fallbacks(
        arena,
        context.bindings,
        context.enum_member_values,
        context.enum_access_values,
    );
    let mut printer = Printer {
        arena,
        writer: Writer::default(),
        settings,
        source_map: settings.source_map.then(SourceMapBuilder::new),
        source_text,
        source_name,
        source_line_starts: settings.source_map.then(|| line_starts(source_text)),
        automatic_jsx,
        this_alias: None,
        namespace_containers: Vec::new(),
        namespace_declarations: vec![HashSet::new()],
        runtime_identifier_uses: HashSet::new(),
        commonjs_default_imports: HashMap::new(),
        has_runtime_export_equals: false,
        bindings: context.bindings,
        identifier_rewrites: HashMap::new(),
        system_predeclared_names: HashSet::new(),
        commonjs_module_transform: settings.module == ModuleKind::CommonJs,
        enum_member_values: context.enum_member_values,
        enum_access_values: context.enum_access_values,
        const_enum_emit_mode: ConstEnumEmitMode::new(
            context.preserve_const_enums,
            context.inline_const_enums,
        ),
        enum_access_fallbacks,
    };
    let node = printer.node(source_file)?.clone();
    let NodeData::SourceFile(data) = &node.data else {
        return Err(Printer::unsupported(source_file, node.kind));
    };
    let source_end = node.range.end.get();
    printer.runtime_identifier_uses = runtime_identifier_uses(arena, source_file);
    if settings.module == ModuleKind::CommonJs {
        printer.commonjs_default_imports =
            commonjs_default_imports(arena, &data.statements, &printer.runtime_identifier_uses);
    }
    let is_external_module = data.statements.nodes.iter().any(|statement| {
        arena
            .get(*statement)
            .is_some_and(|statement| declaration_is_module_indicator(arena, statement))
    });
    if settings.module == ModuleKind::System && is_external_module {
        return printer.emit_system_source_file(data);
    }
    if settings.module == ModuleKind::Amd && is_external_module {
        return printer.emit_amd_source_file(data, context);
    }
    let has_use_strict = data.statements.nodes.first().is_some_and(|statement| {
        let Some(NodeData::ExpressionStatement(statement)) =
            arena.get(*statement).map(|node| &node.data)
        else {
            return false;
        };
        matches!(
            arena.get(statement.expression).map(|node| &node.data),
            Some(NodeData::StringLiteral(literal)) if literal.text == "use strict"
        )
    });
    if !has_use_strict
        && (settings.always_strict
            || (settings.module == ModuleKind::CommonJs && is_external_module))
    {
        printer.writer.write("\"use strict\";");
        printer.writer.newline();
    }
    if let Some(first_statement) = data.statements.nodes.first()
        && let Some(node) = arena.get(*first_statement)
    {
        printer.emit_leading_source_comments(node.range.start.get());
    }
    if settings.target < ScriptTarget::Es2015 && source_needs_extends_helper(arena) {
        printer.emit_extends_helper();
    }
    let export_equals_expression = runtime_export_equals_expression(arena, &data.statements);
    printer.has_runtime_export_equals = export_equals_expression.is_some();
    if settings.module == ModuleKind::CommonJs && is_external_module {
        if source_needs_import_star_helper(
            arena,
            &data.statements,
            &printer.runtime_identifier_uses,
        ) {
            printer.emit_import_star_helper();
        }
        if !printer.commonjs_default_imports.is_empty() {
            printer.emit_import_default_helper();
        }
        if export_equals_expression.is_none() {
            printer
                .writer
                .write("Object.defineProperty(exports, \"__esModule\", { value: true });");
            printer.writer.newline();
        }
        let preinitialized_exports = commonjs_preinitialized_export_names(
            arena,
            &data.statements,
            context.preserve_const_enums,
        );
        if !preinitialized_exports.is_empty() {
            for name in preinitialized_exports.iter().rev() {
                printer.writer.write("exports.");
                printer.writer.write(name);
                printer.writer.write(" = ");
            }
            printer.writer.write("void 0;");
            printer.writer.newline();
        }
        if export_equals_expression.is_none() {
            for statement in &data.statements.nodes {
                let Some(node) = arena.get(*statement) else {
                    continue;
                };
                let NodeData::FunctionDeclaration(function) = &node.data else {
                    continue;
                };
                if !declaration_has_modifier(arena, node, SyntaxKind::ExportKeyword) {
                    continue;
                }
                let Some(name) = function
                    .name
                    .and_then(|name| declaration_name_text(arena, name))
                else {
                    continue;
                };
                printer.writer.write("exports.");
                printer.writer.write(name);
                printer.writer.write(" = ");
                printer.writer.write(name);
                printer.writer.write(";");
                printer.writer.newline();
            }
        }
    }
    printer.emit_automatic_jsx_prelude();
    let mut previous_end = data
        .statements
        .nodes
        .first()
        .and_then(|statement| arena.get(*statement))
        .map_or(0, |node| node.range.start.get());
    let mut previous_emitted = false;
    for statement in &data.statements.nodes {
        if let Some(node) = arena.get(*statement) {
            printer.emit_source_comments_between_with_trailing(
                previous_end,
                node.range.start.get(),
                previous_emitted,
            );
            previous_emitted = statement_emits_javascript(arena, node);
            previous_end = node.range.end.get();
        }
        printer.emit_statement(*statement)?;
    }
    printer.emit_source_comments_between_with_trailing(previous_end, source_end, previous_emitted);
    if settings.module == ModuleKind::CommonJs
        && let Some(expression) = export_equals_expression
    {
        printer.writer.write("module.exports = ");
        printer.emit_expression(expression, 0)?;
        printer.writer.write(";");
        printer.writer.newline();
    }
    let source_map = printer
        .source_map
        .map(|builder| builder.finish(None, vec![source_name.to_owned()]));
    Ok(EmitResult {
        code: printer.writer.finish(),
        source_map,
    })
}

fn source_needs_extends_helper(arena: &NodeArena) -> bool {
    arena.iter().any(|(_, node)| {
        let NodeData::ClassDeclaration(class) = &node.data else {
            return false;
        };
        class.heritage_clauses.as_ref().is_some_and(|clauses| {
            clauses.nodes.iter().any(|clause| {
                matches!(
                    arena.get(*clause).map(|node| &node.data),
                    Some(NodeData::HeritageClause(clause))
                        if clause.token == SyntaxKind::ExtendsKeyword
                )
            })
        })
    })
}

fn source_needs_import_star_helper(
    arena: &NodeArena,
    statements: &NodeList,
    runtime_identifier_uses: &HashSet<String>,
) -> bool {
    statements.nodes.iter().any(|statement| {
        let Some(NodeData::ImportDeclaration(import)) =
            arena.get(*statement).map(|node| &node.data)
        else {
            return false;
        };
        let Some(NodeData::ImportClause(clause)) = import
            .import_clause
            .and_then(|clause| arena.get(clause))
            .map(|node| &node.data)
        else {
            return false;
        };
        clause.phase_modifier != Some(SyntaxKind::TypeKeyword)
            && clause.named_bindings.is_some_and(|bindings| {
                let Some(NodeData::NamespaceImport(namespace)) =
                    arena.get(bindings).map(|node| &node.data)
                else {
                    return false;
                };
                declaration_name_text(arena, namespace.name)
                    .is_some_and(|name| runtime_identifier_uses.contains(name))
            })
    })
}

fn commonjs_default_imports(
    arena: &NodeArena,
    statements: &NodeList,
    runtime_identifier_uses: &HashSet<String>,
) -> HashMap<String, String> {
    let mut imports = HashMap::new();
    let mut module_name_counts = HashMap::<String, usize>::new();
    for statement in &statements.nodes {
        let Some(NodeData::ImportDeclaration(import)) =
            arena.get(*statement).map(|node| &node.data)
        else {
            continue;
        };
        let Some(NodeData::ImportClause(clause)) = import
            .import_clause
            .and_then(|clause| arena.get(clause))
            .map(|node| &node.data)
        else {
            continue;
        };
        if clause.phase_modifier == Some(SyntaxKind::TypeKeyword) {
            continue;
        }
        let mut local_names = Vec::new();
        if let Some(name) = clause.name
            && let Some(name) = declaration_name_text(arena, name)
            && runtime_identifier_uses.contains(name)
        {
            local_names.push(name.to_owned());
        }
        if let Some(NodeData::NamedImports(bindings)) = clause
            .named_bindings
            .and_then(|bindings| arena.get(bindings))
            .map(|node| &node.data)
        {
            for element in &bindings.elements.nodes {
                let Some(NodeData::ImportSpecifier(specifier)) =
                    arena.get(*element).map(|node| &node.data)
                else {
                    continue;
                };
                if specifier.is_type_only
                    || !specifier.property_name.is_some_and(|property| {
                        declaration_name_text(arena, property) == Some("default")
                    })
                {
                    continue;
                }
                if let Some(name) = declaration_name_text(arena, specifier.name)
                    && runtime_identifier_uses.contains(name)
                {
                    local_names.push(name.to_owned());
                }
            }
        }
        if local_names.is_empty() {
            continue;
        }
        let base = commonjs_module_temp_base(arena, import.module_specifier);
        let count = module_name_counts.entry(base.clone()).or_default();
        *count += 1;
        let temp = format!("{base}_{count}");
        for local_name in local_names {
            imports.insert(local_name, temp.clone());
        }
    }
    imports
}

fn commonjs_module_temp_base(arena: &NodeArena, module_specifier: NodeId) -> String {
    let text = match arena.get(module_specifier).map(|node| &node.data) {
        Some(NodeData::StringLiteral(literal)) => literal.text.as_str(),
        _ => "module",
    };
    let segment = text
        .rsplit('/')
        .find(|segment| !segment.is_empty())
        .unwrap_or("module");
    let stem = segment.split('.').next().unwrap_or(segment);
    let mut base = String::new();
    for (index, character) in stem.chars().enumerate() {
        if character == '_' || character == '$' || character.is_ascii_alphanumeric() {
            if index == 0 && character.is_ascii_digit() {
                base.push('_');
            }
            base.push(character);
        } else if !base.ends_with('_') {
            base.push('_');
        }
    }
    if base.is_empty() {
        "module".to_owned()
    } else {
        base
    }
}

fn commonjs_preinitialized_export_names(
    arena: &NodeArena,
    statements: &NodeList,
    preserve_const_enums: bool,
) -> Vec<String> {
    let mut names = Vec::new();
    let mut seen = HashSet::new();
    for statement in &statements.nodes {
        let Some(node) = arena.get(*statement) else {
            continue;
        };
        if !declaration_has_modifier(arena, node, SyntaxKind::ExportKeyword) {
            continue;
        }
        if is_const_enum_declaration(arena, node) && !preserve_const_enums {
            continue;
        }
        let default_export = declaration_has_modifier(arena, node, SyntaxKind::DefaultKeyword);
        match &node.data {
            NodeData::ClassDeclaration(class) => {
                let name = if default_export {
                    Some("default")
                } else {
                    class
                        .name
                        .and_then(|name| declaration_name_text(arena, name))
                };
                if let Some(name) = name
                    && seen.insert(name.to_owned())
                {
                    names.push(name.to_owned());
                }
            }
            NodeData::EnumDeclaration(enumeration) => {
                if let Some(name) = declaration_name_text(arena, enumeration.name)
                    && seen.insert(name.to_owned())
                {
                    names.push(name.to_owned());
                }
            }
            NodeData::VariableStatement(statement) => {
                let Some(NodeData::VariableDeclarationList(list)) =
                    arena.get(statement.declaration_list).map(|node| &node.data)
                else {
                    continue;
                };
                for declaration in &list.declarations.nodes {
                    let Some(NodeData::VariableDeclaration(declaration)) =
                        arena.get(*declaration).map(|node| &node.data)
                    else {
                        continue;
                    };
                    let Some(name) = declaration_name_text(arena, declaration.name) else {
                        continue;
                    };
                    if seen.insert(name.to_owned()) {
                        names.push(name.to_owned());
                    }
                }
            }
            _ => {}
        }
    }
    names
}

fn runtime_export_equals_expression(arena: &NodeArena, statements: &NodeList) -> Option<NodeId> {
    let mut type_only_names = HashSet::new();
    let mut runtime_names = HashSet::new();
    for statement in &statements.nodes {
        let Some(node) = arena.get(*statement) else {
            continue;
        };
        match &node.data {
            NodeData::InterfaceDeclaration(declaration) => {
                if let Some(name) = declaration_name_text(arena, declaration.name) {
                    type_only_names.insert(name.to_owned());
                }
            }
            NodeData::TypeAliasDeclaration(declaration) => {
                if let Some(name) = declaration_name_text(arena, declaration.name) {
                    type_only_names.insert(name.to_owned());
                }
            }
            NodeData::ClassDeclaration(declaration) => {
                if let Some(name) = declaration
                    .name
                    .and_then(|name| declaration_name_text(arena, name))
                {
                    runtime_names.insert(name.to_owned());
                }
            }
            NodeData::FunctionDeclaration(declaration) => {
                if let Some(name) = declaration
                    .name
                    .and_then(|name| declaration_name_text(arena, name))
                {
                    runtime_names.insert(name.to_owned());
                }
            }
            NodeData::EnumDeclaration(declaration) => {
                if let Some(name) = declaration_name_text(arena, declaration.name) {
                    runtime_names.insert(name.to_owned());
                }
            }
            NodeData::ModuleDeclaration(declaration) => {
                if let Some(name) = declaration_name_text(arena, declaration.name) {
                    runtime_names.insert(name.to_owned());
                }
            }
            NodeData::VariableStatement(statement) => {
                let Some(NodeData::VariableDeclarationList(list)) =
                    arena.get(statement.declaration_list).map(|node| &node.data)
                else {
                    continue;
                };
                for declaration in &list.declarations.nodes {
                    let Some(NodeData::VariableDeclaration(declaration)) =
                        arena.get(*declaration).map(|node| &node.data)
                    else {
                        continue;
                    };
                    if let Some(name) = declaration_name_text(arena, declaration.name) {
                        runtime_names.insert(name.to_owned());
                    }
                }
            }
            _ => {}
        }
    }
    statements.nodes.iter().find_map(|statement| {
        let NodeData::ExportAssignment(assignment) = &arena.get(*statement)?.data else {
            return None;
        };
        if !assignment.is_export_equals {
            return None;
        }
        let type_only = declaration_name_text(arena, assignment.expression)
            .is_some_and(|name| type_only_names.contains(name) && !runtime_names.contains(name));
        (!type_only).then_some(assignment.expression)
    })
}

fn statement_emits_javascript(arena: &NodeArena, node: &Node) -> bool {
    if declaration_has_modifier(arena, node, SyntaxKind::DeclareKeyword) {
        return false;
    }
    match &node.data {
        NodeData::InterfaceDeclaration(_) | NodeData::TypeAliasDeclaration(_) => false,
        NodeData::FunctionDeclaration(function) => function.body.is_some(),
        _ => true,
    }
}

fn runtime_identifier_uses(arena: &NodeArena, source_file: NodeId) -> HashSet<String> {
    arena
        .iter()
        .filter_map(|(id, node)| {
            let NodeData::Identifier(identifier) = &node.data else {
                return None;
            };
            identifier_is_runtime_use(arena, id, source_file).then(|| identifier.text.clone())
        })
        .collect()
}

fn identifier_is_runtime_use(arena: &NodeArena, id: NodeId, source_file: NodeId) -> bool {
    let mut child = id;
    while let Some(parent_id) = arena.get(child).and_then(|node| node.parent) {
        if parent_id == source_file {
            return true;
        }
        let Some(parent) = arena.get(parent_id) else {
            return false;
        };
        if node_is_erased_type_context(parent)
            || declaration_has_modifier(arena, parent, SyntaxKind::DeclareKeyword)
            || identifier_is_declaration_name(child, parent)
        {
            return false;
        }
        child = parent_id;
    }
    false
}

fn node_is_erased_type_context(node: &Node) -> bool {
    matches!(
        node.data,
        NodeData::ImportDeclaration(_)
            | NodeData::ImportEqualsDeclaration(_)
            | NodeData::ImportClause(_)
            | NodeData::NamespaceImport(_)
            | NodeData::NamedImports(_)
            | NodeData::ImportSpecifier(_)
            | NodeData::InterfaceDeclaration(_)
            | NodeData::TypeAliasDeclaration(_)
            | NodeData::PropertySignatureDeclaration(_)
            | NodeData::MethodSignatureDeclaration(_)
            | NodeData::CallSignatureDeclaration(_)
            | NodeData::ConstructSignatureDeclaration(_)
            | NodeData::IndexSignatureDeclaration(_)
            | NodeData::TypeParameterDeclaration(_)
            | NodeData::KeywordTypeNode(_)
            | NodeData::TypeReferenceNode(_)
            | NodeData::ArrayTypeNode(_)
            | NodeData::UnionTypeNode(_)
            | NodeData::IntersectionTypeNode(_)
            | NodeData::TupleTypeNode(_)
            | NodeData::ParenthesizedTypeNode(_)
            | NodeData::LiteralTypeNode(_)
            | NodeData::TypeLiteralNode(_)
            | NodeData::FunctionTypeNode(_)
            | NodeData::ConstructorTypeNode(_)
            | NodeData::IndexedAccessTypeNode(_)
            | NodeData::TypeOperatorNode(_)
            | NodeData::OptionalTypeNode(_)
            | NodeData::RestTypeNode(_)
            | NodeData::NamedTupleMember(_)
            | NodeData::TypeQueryNode(_)
            | NodeData::ThisTypeNode(_)
            | NodeData::ConditionalTypeNode(_)
            | NodeData::InferTypeNode(_)
            | NodeData::MappedTypeNode(_)
            | NodeData::ImportTypeNode(_)
            | NodeData::TypePredicateNode(_)
            | NodeData::TemplateLiteralTypeNode(_)
            | NodeData::TemplateLiteralTypeSpan(_)
    ) || matches!(
        &node.data,
        NodeData::FunctionDeclaration(function) if function.body.is_none()
    ) || matches!(
        &node.data,
        NodeData::MethodDeclaration(method) if method.body.is_none()
    )
}

fn identifier_is_declaration_name(child: NodeId, parent: &Node) -> bool {
    match &parent.data {
        NodeData::VariableDeclaration(declaration) => declaration.name == child,
        NodeData::ParameterDeclaration(declaration) => declaration.name == child,
        NodeData::PropertyDeclaration(declaration) => declaration.name == child,
        NodeData::MethodDeclaration(declaration) => declaration.name == child,
        NodeData::GetAccessorDeclaration(declaration) => declaration.name == child,
        NodeData::SetAccessorDeclaration(declaration) => declaration.name == child,
        NodeData::FunctionDeclaration(declaration) => declaration.name == Some(child),
        NodeData::FunctionExpression(declaration) => declaration.name == Some(child),
        NodeData::ClassDeclaration(declaration) => declaration.name == Some(child),
        NodeData::EnumDeclaration(declaration) => declaration.name == child,
        NodeData::EnumMember(declaration) => declaration.name == child,
        NodeData::ModuleDeclaration(declaration) => declaration.name == child,
        NodeData::BindingElement(declaration) => declaration.name == Some(child),
        NodeData::ImportSpecifier(_) => true,
        _ => false,
    }
}

/// Emits one source file as a TypeScript declaration file.
///
/// # Errors
///
/// Returns an error when a declaration contains an unsupported or missing node.
pub fn emit_declaration_file(
    arena: &NodeArena,
    source_file: NodeId,
    source_name: &str,
    source_text: &str,
    declaration_map: bool,
) -> Result<EmitResult, EmitError> {
    emit_declaration_file_with_reachability(
        arena,
        source_file,
        source_name,
        source_text,
        declaration_map,
        None,
        None,
    )
}

/// Emits one source file as declarations, retaining the statements selected by checking.
///
/// # Errors
///
/// Returns an error when a declaration contains an unsupported or missing node.
pub fn emit_declaration_file_with_reachability(
    arena: &NodeArena,
    source_file: NodeId,
    source_name: &str,
    source_text: &str,
    declaration_map: bool,
    declaration_reachability: Option<&BTreeMap<NodeId, BTreeSet<NodeId>>>,
    enum_member_values: Option<&BTreeMap<NodeId, EmitConstantValue>>,
) -> Result<EmitResult, EmitError> {
    let mut printer = DeclarationPrinter {
        arena,
        writer: Writer::default(),
        source_map: declaration_map.then(SourceMapBuilder::new),
        source_text,
        source_line_starts: declaration_map.then(|| line_starts(source_text)),
        module_file: false,
        overload_names: HashSet::new(),
        declaration_reachability,
        enum_member_values,
    };
    let node = printer.node(source_file)?.clone();
    let NodeData::SourceFile(data) = &node.data else {
        return Err(DeclarationPrinter::unsupported(source_file, node.kind));
    };
    printer.module_file = data.statements.nodes.iter().any(|statement| {
        printer
            .node(*statement)
            .is_ok_and(|node| declaration_is_module_indicator(printer.arena, node))
    });
    for statement in &data.statements.nodes {
        printer.emit_statement(*statement, false, source_file)?;
    }
    if printer.scope_needs_seal(source_file) {
        printer.writer.write("export {};");
        printer.writer.newline();
    }
    let source_map = printer
        .source_map
        .map(|builder| builder.finish(None, vec![source_name.to_owned()]));
    Ok(EmitResult {
        code: printer.writer.finish(),
        source_map,
    })
}

struct DeclarationPrinter<'a> {
    arena: &'a NodeArena,
    writer: Writer,
    source_map: Option<SourceMapBuilder>,
    source_text: &'a str,
    source_line_starts: Option<Vec<usize>>,
    module_file: bool,
    overload_names: HashSet<String>,
    declaration_reachability: Option<&'a BTreeMap<NodeId, BTreeSet<NodeId>>>,
    enum_member_values: Option<&'a BTreeMap<NodeId, EmitConstantValue>>,
}

impl DeclarationPrinter<'_> {
    fn node(&self, id: NodeId) -> Result<&Node, EmitError> {
        self.arena.get(id).ok_or(EmitError {
            node: id,
            kind: SyntaxKind::Unknown,
        })
    }

    const fn unsupported(id: NodeId, kind: SyntaxKind) -> EmitError {
        EmitError { node: id, kind }
    }

    fn record_mapping(&mut self, node: &Node) {
        let Some(line_starts) = self.source_line_starts.as_deref() else {
            return;
        };
        let (line, column) = self.writer.position();
        let (original_line, original_column) =
            original_position(self.source_text, line_starts, node.range.start.get());
        if let Some(builder) = &mut self.source_map {
            let _ = builder.add_mapping(line, column, 0, original_line, original_column);
        }
    }

    #[allow(clippy::too_many_lines)]
    fn emit_statement(
        &mut self,
        id: NodeId,
        in_namespace: bool,
        scope: NodeId,
    ) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        if let Some(retained) = self
            .declaration_reachability
            .and_then(|reachability| reachability.get(&scope))
            && !retained.contains(&id)
        {
            return Ok(());
        }
        if let NodeData::FunctionDeclaration(function) = &node.data
            && let Some(name) = function.name
            && let Some(name) = declaration_name_text(self.arena, name)
        {
            if function.body.is_none() {
                self.overload_names.insert(name.to_owned());
            } else if self.overload_names.contains(name) {
                return Ok(());
            }
        }
        let exported = declaration_has_modifier(self.arena, &node, SyntaxKind::ExportKeyword);
        if self.declaration_reachability.is_none()
            && self.module_file
            && !in_namespace
            && !exported
            && !matches!(
                node.data,
                NodeData::ImportDeclaration(_)
                    | NodeData::ImportEqualsDeclaration(_)
                    | NodeData::ExportDeclaration(_)
                    | NodeData::ExportAssignment(_)
            )
        {
            return Ok(());
        }
        self.record_mapping(&node);
        match &node.data {
            NodeData::VariableStatement(data) => {
                self.emit_declaration_prefix(&node, !in_namespace);
                self.emit_variable_declarations(data.declaration_list)?;
                self.writer.write(";");
            }
            NodeData::FunctionDeclaration(data) => {
                self.emit_declaration_prefix(&node, !in_namespace);
                self.writer.write("function ");
                if let Some(name) = data.name {
                    self.emit_name(name)?;
                }
                self.emit_type_parameters(data.type_parameters.as_ref())?;
                self.emit_parameters(&data.parameters)?;
                self.emit_return_type(data.type_)?;
                self.writer.write(";");
            }
            NodeData::ClassDeclaration(data) => {
                self.emit_declaration_prefix(&node, !in_namespace);
                self.writer.write("class");
                if let Some(name) = data.name {
                    self.writer.write(" ");
                    self.emit_name(name)?;
                }
                self.emit_type_parameters(data.type_parameters.as_ref())?;
                self.emit_heritage(data.heritage_clauses.as_ref())?;
                self.writer.write(" {");
                self.writer.newline();
                self.writer.indent += 1;
                for member in &data.members.nodes {
                    self.emit_member(*member)?;
                }
                self.writer.indent -= 1;
                self.writer.write("}");
            }
            NodeData::InterfaceDeclaration(data) => {
                self.emit_declaration_prefix(&node, false);
                self.writer.write("interface ");
                self.emit_name(data.name)?;
                self.emit_type_parameters(data.type_parameters.as_ref())?;
                self.emit_heritage(data.heritage_clauses.as_ref())?;
                self.writer.write(" {");
                self.writer.newline();
                self.writer.indent += 1;
                for member in &data.members.nodes {
                    self.emit_member(*member)?;
                }
                self.writer.indent -= 1;
                self.writer.write("}");
            }
            NodeData::TypeAliasDeclaration(data) => {
                self.emit_declaration_prefix(&node, false);
                self.writer.write("type ");
                self.emit_name(data.name)?;
                self.emit_type_parameters(data.type_parameters.as_ref())?;
                self.writer.write(" = ");
                self.emit_type(data.type_)?;
                self.writer.write(";");
            }
            NodeData::EnumDeclaration(data) => {
                self.emit_declaration_prefix(&node, !in_namespace);
                let is_const =
                    declaration_has_modifier(self.arena, &node, SyntaxKind::ConstKeyword);
                if is_const {
                    self.writer.write("const ");
                }
                self.writer.write("enum ");
                self.emit_name(data.name)?;
                self.writer.write(" {");
                self.writer.newline();
                self.writer.indent += 1;
                for (index, member) in data.members.nodes.iter().enumerate() {
                    let member_id = *member;
                    let member_node = self.node(*member)?.clone();
                    let NodeData::EnumMember(member) = &member_node.data else {
                        return Err(Self::unsupported(*member, member_node.kind));
                    };
                    self.emit_name(member.name)?;
                    if let Some(value) = is_const
                        .then(|| {
                            self.enum_member_values
                                .and_then(|values| values.get(&member_id))
                        })
                        .flatten()
                    {
                        self.writer.write(" = ");
                        write_enum_constant(&mut self.writer, value);
                    } else if let Some(initializer) = member.initializer {
                        self.writer.write(" = ");
                        self.emit_literal_expression(initializer)?;
                    }
                    if !is_const || index + 1 != data.members.nodes.len() {
                        self.writer.write(",");
                    }
                    self.writer.newline();
                }
                self.writer.indent -= 1;
                self.writer.write("}");
            }
            NodeData::ModuleDeclaration(data) => {
                self.emit_declaration_prefix(&node, !in_namespace);
                self.writer.write("namespace ");
                self.emit_name(data.name)?;
                self.writer.write(" {");
                self.writer.newline();
                self.writer.indent += 1;
                if let Some(body) = data.body {
                    self.emit_module_body(body)?;
                }
                self.writer.indent -= 1;
                self.writer.write("}");
            }
            NodeData::ImportDeclaration(data) => self.emit_import(data)?,
            NodeData::ImportEqualsDeclaration(data) => {
                if declaration_has_modifier(self.arena, &node, SyntaxKind::ExportKeyword) {
                    self.writer.write("export ");
                }
                self.writer.write("import ");
                self.emit_name(data.name)?;
                self.writer.write(" = ");
                self.emit_name(data.module_reference)?;
                self.writer.write(";");
            }
            NodeData::ExportDeclaration(data) => self.emit_export(data)?,
            NodeData::ExportAssignment(data) => {
                if data.is_export_equals {
                    self.writer.write("export = ");
                } else {
                    self.writer.write("export default ");
                }
                self.emit_name(data.expression)?;
                self.writer.write(";");
            }
            _ => return Ok(()),
        }
        self.writer.newline();
        Ok(())
    }

    fn emit_declaration_prefix(&mut self, node: &Node, ambient: bool) {
        if declaration_has_modifier(self.arena, node, SyntaxKind::ExportKeyword) {
            self.writer.write("export ");
        }
        if declaration_has_modifier(self.arena, node, SyntaxKind::DefaultKeyword) {
            self.writer.write("default ");
        }
        if ambient && !declaration_has_modifier(self.arena, node, SyntaxKind::DefaultKeyword) {
            self.writer.write("declare ");
        }
    }

    fn emit_variable_declarations(&mut self, list: NodeId) -> Result<(), EmitError> {
        let node = self.node(list)?.clone();
        let NodeData::VariableDeclarationList(data) = &node.data else {
            return Err(Self::unsupported(list, node.kind));
        };
        let keyword = if node.flags.0 & (1 << 1) != 0 {
            "const"
        } else if node.flags.0 & 1 != 0 {
            "let"
        } else {
            "var"
        };
        self.writer.write(keyword);
        self.writer.write(" ");
        for (index, declaration) in data.declarations.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            let declaration_node = self.node(*declaration)?.clone();
            let NodeData::VariableDeclaration(declaration) = &declaration_node.data else {
                return Err(Self::unsupported(*declaration, declaration_node.kind));
            };
            self.emit_name(declaration.name)?;
            if let Some(type_) = declaration.type_ {
                self.writer.write(": ");
                self.emit_type(type_)?;
            } else if keyword == "const"
                && declaration
                    .initializer
                    .is_some_and(|value| self.is_literal_expression(value))
            {
                self.writer.write(" = ");
                self.emit_literal_expression(declaration.initializer.unwrap())?;
            } else {
                self.writer.write(": any");
            }
        }
        Ok(())
    }

    fn emit_parameters(&mut self, parameters: &NodeList) -> Result<(), EmitError> {
        self.writer.write("(");
        for (index, parameter) in parameters.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            let node = self.node(*parameter)?.clone();
            let NodeData::ParameterDeclaration(data) = &node.data else {
                return Err(Self::unsupported(*parameter, node.kind));
            };
            if data.dot_dot_dot_token.is_some() {
                self.writer.write("...");
            }
            self.emit_name(data.name)?;
            if data.question_token.is_some() {
                self.writer.write("?");
            }
            self.writer.write(": ");
            if let Some(type_) = data.type_ {
                self.emit_type(type_)?;
            } else {
                self.writer.write("any");
            }
        }
        self.writer.write(")");
        Ok(())
    }

    fn emit_return_type(&mut self, type_: Option<NodeId>) -> Result<(), EmitError> {
        self.writer.write(": ");
        if let Some(type_) = type_ {
            self.emit_type(type_)
        } else {
            self.writer.write("any");
            Ok(())
        }
    }

    #[allow(clippy::too_many_lines)]
    fn emit_member(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        match &node.data {
            NodeData::PropertyDeclaration(data) => {
                self.emit_name(data.name)?;
                if data.postfix_token.is_some() {
                    self.writer.write("?");
                }
                self.writer.write(": ");
                if let Some(type_) = data.type_ {
                    self.emit_type(type_)?;
                } else {
                    self.writer.write("any");
                }
                self.writer.write(";");
            }
            NodeData::PropertySignatureDeclaration(data) => {
                self.emit_name(data.name)?;
                if data.postfix_token.is_some() {
                    self.writer.write("?");
                }
                self.writer.write(": ");
                self.emit_type(data.type_)?;
                self.writer.write(";");
            }
            NodeData::MethodDeclaration(data) => {
                self.emit_name(data.name)?;
                if data.postfix_token.is_some() {
                    self.writer.write("?");
                }
                self.emit_type_parameters(data.type_parameters.as_ref())?;
                self.emit_parameters(&data.parameters)?;
                self.emit_return_type(data.type_)?;
                self.writer.write(";");
            }
            NodeData::MethodSignatureDeclaration(data) => {
                self.emit_name(data.name)?;
                if data.postfix_token.is_some() {
                    self.writer.write("?");
                }
                self.emit_type_parameters(data.type_parameters.as_ref())?;
                self.emit_parameters(&data.parameters)?;
                self.emit_return_type(data.type_)?;
                self.writer.write(";");
            }
            NodeData::ConstructorDeclaration(data) => {
                self.writer.write("constructor");
                self.emit_parameters(&data.parameters)?;
                self.writer.write(";");
            }
            NodeData::GetAccessorDeclaration(data) => {
                self.writer.write("get ");
                self.emit_name(data.name)?;
                self.emit_parameters(&data.parameters)?;
                self.emit_return_type(data.type_)?;
                self.writer.write(";");
            }
            NodeData::SetAccessorDeclaration(data) => {
                self.writer.write("set ");
                self.emit_name(data.name)?;
                self.emit_parameters(&data.parameters)?;
                self.writer.write(";");
            }
            NodeData::CallSignatureDeclaration(data) => {
                self.emit_type_parameters(data.type_parameters.as_ref())?;
                self.emit_parameters(&data.parameters)?;
                self.emit_return_type(data.type_)?;
                self.writer.write(";");
            }
            NodeData::ConstructSignatureDeclaration(data) => {
                self.writer.write("new ");
                self.emit_type_parameters(data.type_parameters.as_ref())?;
                self.emit_parameters(&data.parameters)?;
                self.emit_return_type(data.type_)?;
                self.writer.write(";");
            }
            NodeData::IndexSignatureDeclaration(data) => {
                self.writer.write("[");
                for (index, parameter) in data.parameters.nodes.iter().enumerate() {
                    if index != 0 {
                        self.writer.write(", ");
                    }
                    let parameter_node = self.node(*parameter)?.clone();
                    let NodeData::ParameterDeclaration(parameter) = &parameter_node.data else {
                        return Err(Self::unsupported(*parameter, parameter_node.kind));
                    };
                    self.emit_name(parameter.name)?;
                    self.writer.write(": ");
                    if let Some(type_) = parameter.type_ {
                        self.emit_type(type_)?;
                    } else {
                        self.writer.write("any");
                    }
                }
                self.writer.write("]: ");
                self.emit_type(data.type_)?;
                self.writer.write(";");
            }
            NodeData::SemicolonClassElement(_) => self.writer.write(";"),
            NodeData::ClassStaticBlockDeclaration(_) => return Ok(()),
            _ => return Err(Self::unsupported(id, node.kind)),
        }
        self.writer.newline();
        Ok(())
    }

    fn emit_type_parameters(&mut self, parameters: Option<&NodeList>) -> Result<(), EmitError> {
        let Some(parameters) = parameters else {
            return Ok(());
        };
        self.writer.write("<");
        for (index, parameter) in parameters.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            let node = self.node(*parameter)?.clone();
            let NodeData::TypeParameterDeclaration(data) = &node.data else {
                return Err(Self::unsupported(*parameter, node.kind));
            };
            self.emit_name(data.name)?;
            if let Some(constraint) = data.constraint {
                self.writer.write(" extends ");
                self.emit_type(constraint)?;
            }
            if let Some(default_type) = data.default_type {
                self.writer.write(" = ");
                self.emit_type(default_type)?;
            }
        }
        self.writer.write(">");
        Ok(())
    }

    fn emit_heritage(&mut self, clauses: Option<&NodeList>) -> Result<(), EmitError> {
        let Some(clauses) = clauses else {
            return Ok(());
        };
        for clause in &clauses.nodes {
            let node = self.node(*clause)?.clone();
            let NodeData::HeritageClause(data) = &node.data else {
                return Err(Self::unsupported(*clause, node.kind));
            };
            self.writer.write(match data.token {
                SyntaxKind::ExtendsKeyword => " extends ",
                SyntaxKind::ImplementsKeyword => " implements ",
                _ => " ",
            });
            for (index, type_) in data.types.nodes.iter().enumerate() {
                if index != 0 {
                    self.writer.write(", ");
                }
                let type_node = self.node(*type_)?.clone();
                if let NodeData::ExpressionWithTypeArguments(expression) = &type_node.data {
                    self.emit_name(expression.expression)?;
                    self.emit_type_arguments(expression.type_arguments.as_ref())?;
                } else {
                    self.emit_type(*type_)?;
                }
            }
        }
        Ok(())
    }

    fn emit_type_arguments(&mut self, arguments: Option<&NodeList>) -> Result<(), EmitError> {
        let Some(arguments) = arguments else {
            return Ok(());
        };
        self.writer.write("<");
        for (index, argument) in arguments.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            self.emit_type(*argument)?;
        }
        self.writer.write(">");
        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    fn emit_type(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        match &node.data {
            NodeData::KeywordTypeNode(_) => self.writer.write(keyword_type_text(node.kind)),
            NodeData::TypeReferenceNode(data) => {
                self.emit_name(data.type_name)?;
                self.emit_type_arguments(data.type_arguments.as_ref())?;
            }
            NodeData::ArrayTypeNode(data) => {
                self.emit_type(data.element_type)?;
                self.writer.write("[]");
            }
            NodeData::UnionTypeNode(data) => self.emit_type_list(&data.types, " | ")?,
            NodeData::IntersectionTypeNode(data) => self.emit_type_list(&data.types, " & ")?,
            NodeData::TupleTypeNode(data) => {
                self.writer.write("[");
                self.emit_type_list(&data.elements, ", ")?;
                self.writer.write("]");
            }
            NodeData::ParenthesizedTypeNode(data) => {
                self.writer.write("(");
                self.emit_type(data.type_)?;
                self.writer.write(")");
            }
            NodeData::LiteralTypeNode(data) => self.emit_literal_expression(data.literal)?,
            NodeData::TypeLiteralNode(data) => {
                self.writer.write("{");
                if !data.members.nodes.is_empty() {
                    self.writer.newline();
                    self.writer.indent += 1;
                    for member in &data.members.nodes {
                        self.emit_member(*member)?;
                    }
                    self.writer.indent -= 1;
                }
                self.writer.write("}");
            }
            NodeData::FunctionTypeNode(data) => {
                self.emit_type_parameters(data.type_parameters.as_ref())?;
                self.emit_parameters(&data.parameters)?;
                self.writer.write(" => ");
                if let Some(type_) = data.type_ {
                    self.emit_type(type_)?;
                } else {
                    self.writer.write("any");
                }
            }
            NodeData::ConstructorTypeNode(data) => {
                self.writer.write("new ");
                self.emit_type_parameters(data.type_parameters.as_ref())?;
                self.emit_parameters(&data.parameters)?;
                self.writer.write(" => ");
                if let Some(type_) = data.type_ {
                    self.emit_type(type_)?;
                } else {
                    self.writer.write("any");
                }
            }
            NodeData::IndexedAccessTypeNode(data) => {
                self.emit_type(data.object_type)?;
                self.writer.write("[");
                self.emit_type(data.index_type)?;
                self.writer.write("]");
            }
            NodeData::TypeOperatorNode(data) => {
                self.writer.write(match data.operator {
                    SyntaxKind::KeyOfKeyword => "keyof ",
                    SyntaxKind::ReadonlyKeyword => "readonly ",
                    SyntaxKind::UniqueKeyword => "unique ",
                    _ => "",
                });
                self.emit_type(data.type_)?;
            }
            NodeData::OptionalTypeNode(data) => {
                self.emit_type(data.type_)?;
                self.writer.write("?");
            }
            NodeData::RestTypeNode(data) => {
                self.writer.write("...");
                self.emit_type(data.type_)?;
            }
            NodeData::NamedTupleMember(data) => {
                if data.dot_dot_dot_token.is_some() {
                    self.writer.write("...");
                }
                self.emit_name(data.name)?;
                if data.question_token.is_some() {
                    self.writer.write("?");
                }
                self.writer.write(": ");
                self.emit_type(data.type_)?;
            }
            NodeData::TypeQueryNode(data) => {
                self.writer.write("typeof ");
                self.emit_name(data.expr_name)?;
                self.emit_type_arguments(data.type_arguments.as_ref())?;
            }
            NodeData::ThisTypeNode(_) => self.writer.write("this"),
            _ => self.emit_source_slice(&node),
        }
        Ok(())
    }

    fn emit_type_list(&mut self, list: &NodeList, separator: &str) -> Result<(), EmitError> {
        for (index, type_) in list.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(separator);
            }
            self.emit_type(*type_)?;
        }
        Ok(())
    }

    fn emit_name(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        match &node.data {
            NodeData::Identifier(data) => self.writer.write(&data.text),
            NodeData::PrivateIdentifier(data) => self.writer.write(&data.text),
            NodeData::StringLiteral(data) => write_quoted(&mut self.writer, &data.text),
            NodeData::NumericLiteral(data) => self.writer.write(&data.text),
            NodeData::QualifiedName(data) => {
                self.emit_name(data.left)?;
                self.writer.write(".");
                self.emit_name(data.right)?;
            }
            NodeData::ExternalModuleReference(data) => {
                self.writer.write("require(");
                self.emit_name(data.expression)?;
                self.writer.write(")");
            }
            _ => self.emit_source_slice(&node),
        }
        Ok(())
    }

    fn is_literal_expression(&self, id: NodeId) -> bool {
        self.node(id).is_ok_and(|node| {
            matches!(
                node.data,
                NodeData::NumericLiteral(_)
                    | NodeData::BigIntLiteral(_)
                    | NodeData::StringLiteral(_)
                    | NodeData::NoSubstitutionTemplateLiteral(_)
                    | NodeData::KeywordExpression(_)
            )
        })
    }

    fn emit_literal_expression(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        match &node.data {
            NodeData::NumericLiteral(data) => self.writer.write(&data.text),
            NodeData::BigIntLiteral(data) => self.writer.write(&data.text),
            NodeData::StringLiteral(data) => write_quoted(&mut self.writer, &data.text),
            NodeData::RegularExpressionLiteral(data) => self.writer.write(&data.text),
            NodeData::NoSubstitutionTemplateLiteral(data) => {
                self.writer.write("`");
                self.writer.write(&data.raw_text);
                self.writer.write("`");
            }
            NodeData::KeywordExpression(_) => self.writer.write(match node.kind {
                SyntaxKind::TrueKeyword => "true",
                SyntaxKind::FalseKeyword => "false",
                SyntaxKind::NullKeyword => "null",
                _ => "undefined",
            }),
            NodeData::Identifier(_) | NodeData::QualifiedName(_) => self.emit_name(id)?,
            _ => return Err(Self::unsupported(id, node.kind)),
        }
        Ok(())
    }

    fn emit_source_slice(&mut self, node: &Node) {
        let start = usize::try_from(node.range.start.get()).unwrap_or(self.source_text.len());
        let end = usize::try_from(node.range.end.get()).unwrap_or(self.source_text.len());
        if let Some(text) = self.source_text.get(start..end) {
            self.writer.write(text);
        } else {
            self.writer.write("any");
        }
    }

    fn emit_module_body(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        match &node.data {
            NodeData::ModuleBlock(data) => {
                for statement in &data.statements.nodes {
                    self.emit_statement(*statement, true, id)?;
                }
                if self.scope_needs_seal(id) {
                    self.writer.write("export {};");
                    self.writer.newline();
                }
            }
            NodeData::ModuleDeclaration(_) => self.emit_statement(id, true, id)?,
            _ => return Err(Self::unsupported(id, node.kind)),
        }
        Ok(())
    }

    fn scope_needs_seal(&self, scope: NodeId) -> bool {
        let Some(retained) = self
            .declaration_reachability
            .and_then(|reachability| reachability.get(&scope))
        else {
            return false;
        };
        let has_export = retained.iter().any(|statement| {
            self.arena.get(*statement).is_some_and(|node| {
                declaration_has_modifier(self.arena, node, SyntaxKind::ExportKeyword)
                    || matches!(
                        node.data,
                        NodeData::ExportDeclaration(_) | NodeData::ExportAssignment(_)
                    )
            })
        });
        let has_private_declaration = retained.iter().any(|statement| {
            self.arena.get(*statement).is_some_and(|node| {
                !declaration_has_modifier(self.arena, node, SyntaxKind::ExportKeyword)
                    && matches!(
                        node.data,
                        NodeData::VariableStatement(_)
                            | NodeData::FunctionDeclaration(_)
                            | NodeData::ClassDeclaration(_)
                            | NodeData::InterfaceDeclaration(_)
                            | NodeData::TypeAliasDeclaration(_)
                            | NodeData::EnumDeclaration(_)
                            | NodeData::ModuleDeclaration(_)
                            | NodeData::ImportEqualsDeclaration(_)
                    )
            })
        });
        has_export && has_private_declaration
    }

    fn emit_import(&mut self, data: &ts_ast::ImportDeclarationData) -> Result<(), EmitError> {
        self.writer.write("import ");
        if let Some(clause) = data.import_clause {
            let node = self.node(clause)?.clone();
            let NodeData::ImportClause(clause) = &node.data else {
                return Err(Self::unsupported(clause, node.kind));
            };
            if let Some(name) = clause.name {
                self.emit_name(name)?;
                if clause.named_bindings.is_some() {
                    self.writer.write(", ");
                }
            }
            if let Some(bindings) = clause.named_bindings {
                self.emit_import_bindings(bindings)?;
            }
            self.writer.write(" from ");
        }
        self.emit_name(data.module_specifier)?;
        self.writer.write(";");
        Ok(())
    }

    fn emit_import_bindings(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        match &node.data {
            NodeData::NamedImports(data) => {
                self.writer.write("{ ");
                for (index, specifier) in data.elements.nodes.iter().enumerate() {
                    if index != 0 {
                        self.writer.write(", ");
                    }
                    let specifier_node = self.node(*specifier)?.clone();
                    let NodeData::ImportSpecifier(specifier) = &specifier_node.data else {
                        return Err(Self::unsupported(*specifier, specifier_node.kind));
                    };
                    if specifier.is_type_only {
                        self.writer.write("type ");
                    }
                    if let Some(property_name) = specifier.property_name {
                        self.emit_name(property_name)?;
                        self.writer.write(" as ");
                    }
                    self.emit_name(specifier.name)?;
                }
                self.writer.write(" }");
            }
            NodeData::NamespaceImport(data) => {
                self.writer.write("* as ");
                self.emit_name(data.name)?;
            }
            _ => return Err(Self::unsupported(id, node.kind)),
        }
        Ok(())
    }

    fn emit_export(&mut self, data: &ts_ast::ExportDeclarationData) -> Result<(), EmitError> {
        self.writer.write("export ");
        if data.is_type_only {
            self.writer.write("type ");
        }
        if let Some(clause) = data.export_clause {
            let node = self.node(clause)?.clone();
            match &node.data {
                NodeData::NamedExports(named) => {
                    self.writer.write("{ ");
                    for (index, specifier) in named.elements.nodes.iter().enumerate() {
                        if index != 0 {
                            self.writer.write(", ");
                        }
                        let specifier_node = self.node(*specifier)?.clone();
                        let NodeData::ExportSpecifier(specifier) = &specifier_node.data else {
                            return Err(Self::unsupported(*specifier, specifier_node.kind));
                        };
                        if specifier.is_type_only {
                            self.writer.write("type ");
                        }
                        if let Some(property_name) = specifier.property_name {
                            self.emit_name(property_name)?;
                            self.writer.write(" as ");
                        }
                        self.emit_name(specifier.name)?;
                    }
                    self.writer.write(" }");
                }
                NodeData::NamespaceExport(namespace) => {
                    self.writer.write("* as ");
                    self.emit_name(namespace.name)?;
                }
                _ => return Err(Self::unsupported(clause, node.kind)),
            }
        } else {
            self.writer.write("*");
        }
        if let Some(module_specifier) = data.module_specifier {
            self.writer.write(" from ");
            self.emit_name(module_specifier)?;
        }
        self.writer.write(";");
        Ok(())
    }
}

fn declaration_is_module_indicator(arena: &NodeArena, node: &Node) -> bool {
    match &node.data {
        NodeData::ImportDeclaration(_)
        | NodeData::ExportDeclaration(_)
        | NodeData::ExportAssignment(_) => true,
        NodeData::ImportEqualsDeclaration(import) => matches!(
            arena
                .get(import.module_reference)
                .map(|reference| &reference.data),
            Some(NodeData::ExternalModuleReference(_))
        ),
        _ => declaration_has_modifier(arena, node, SyntaxKind::ExportKeyword),
    }
}

fn declaration_has_modifier(arena: &NodeArena, node: &Node, kind: SyntaxKind) -> bool {
    declaration_modifiers(node).is_some_and(|modifiers| {
        modifiers
            .list
            .nodes
            .iter()
            .any(|modifier| arena.get(*modifier).is_some_and(|node| node.kind == kind))
    })
}

fn is_const_enum_declaration(arena: &NodeArena, node: &Node) -> bool {
    matches!(node.data, NodeData::EnumDeclaration(_))
        && declaration_has_modifier(arena, node, SyntaxKind::ConstKeyword)
}

fn write_enum_constant(writer: &mut Writer, value: &EmitConstantValue) {
    match value {
        EmitConstantValue::Number(value) => writer.write(&value.to_string()),
        EmitConstantValue::String(value) => write_quoted(writer, value),
    }
}

fn const_enum_access_fallbacks(
    arena: &NodeArena,
    bindings: &BindResult,
    member_values: &BTreeMap<NodeId, EmitConstantValue>,
    access_values: &BTreeMap<NodeId, EmitConstantValue>,
) -> HashMap<NodeId, EmitConstantValue> {
    let mut members = HashMap::new();
    for (_, declaration) in arena.iter() {
        let NodeData::EnumDeclaration(enumeration) = &declaration.data else {
            continue;
        };
        if !is_const_enum_declaration(arena, declaration) {
            continue;
        }
        let Some(enum_name) = declaration_name_text(arena, enumeration.name) else {
            continue;
        };
        for member_id in &enumeration.members.nodes {
            let Some(value) = member_values.get(member_id) else {
                continue;
            };
            let Some(NodeData::EnumMember(member)) = arena.get(*member_id).map(|node| &node.data)
            else {
                continue;
            };
            let Some(name) = declaration_name_text(arena, member.name) else {
                continue;
            };
            members.insert((enum_name.to_owned(), name.to_owned()), value.clone());
        }
    }
    let mut fallbacks = HashMap::new();
    for (id, node) in arena.iter() {
        if access_values.contains_key(&id) {
            continue;
        }
        let (receiver, member) = match &node.data {
            NodeData::PropertyAccessExpression(access) => {
                let Some(member) = declaration_name_text(arena, access.name) else {
                    continue;
                };
                (access.expression, member)
            }
            NodeData::ElementAccessExpression(access) => {
                let Some(member) = string_literal_text(arena, access.argument_expression) else {
                    continue;
                };
                (access.expression, member)
            }
            _ => continue,
        };
        let Some(receiver_name) = declaration_name_text(arena, receiver) else {
            continue;
        };
        let resolved_name = bindings
            .resolve_name_at(receiver, receiver_name)
            .and_then(|symbol| bindings.symbols.get(symbol))
            .map_or(receiver_name, |symbol| symbol.name.as_str());
        if let Some(value) = members.get(&(resolved_name.to_owned(), member.to_owned())) {
            fallbacks.insert(id, value.clone());
        }
    }
    fallbacks
}

fn declaration_modifiers(node: &Node) -> Option<&ts_ast::ModifierList> {
    match &node.data {
        NodeData::VariableStatement(data) => data.modifiers.as_ref(),
        NodeData::FunctionDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ClassDeclaration(data) => data.modifiers.as_ref(),
        NodeData::InterfaceDeclaration(data) => data.modifiers.as_ref(),
        NodeData::TypeAliasDeclaration(data) => data.modifiers.as_ref(),
        NodeData::EnumDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ModuleDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ImportEqualsDeclaration(data) => data.modifiers.as_ref(),
        _ => None,
    }
}

fn declaration_name_text(arena: &NodeArena, id: NodeId) -> Option<&str> {
    match &arena.get(id)?.data {
        NodeData::Identifier(identifier) => Some(&identifier.text),
        _ => None,
    }
}

fn keyword_type_text(kind: SyntaxKind) -> &'static str {
    match kind {
        SyntaxKind::UnknownKeyword => "unknown",
        SyntaxKind::NeverKeyword => "never",
        SyntaxKind::VoidKeyword => "void",
        SyntaxKind::UndefinedKeyword => "undefined",
        SyntaxKind::NullKeyword => "null",
        SyntaxKind::BooleanKeyword => "boolean",
        SyntaxKind::NumberKeyword => "number",
        SyntaxKind::StringKeyword => "string",
        SyntaxKind::BigIntKeyword => "bigint",
        SyntaxKind::ObjectKeyword => "object",
        SyntaxKind::SymbolKeyword => "symbol",
        _ => "any",
    }
}

#[derive(Default)]
struct Writer {
    output: String,
    indent: usize,
    line_start: bool,
    line: u32,
    column: u32,
}

impl Writer {
    fn write(&mut self, text: &str) {
        if self.line_start {
            for _ in 0..self.indent {
                self.output.push_str("    ");
                self.column += 4;
            }
            self.line_start = false;
        }
        self.output.push_str(text);
        self.column += u32::try_from(text.len()).unwrap_or(u32::MAX);
    }

    fn newline(&mut self) {
        while self.output.ends_with(' ') {
            self.output.pop();
        }
        self.output.push('\n');
        self.line_start = true;
        self.line += 1;
        self.column = 0;
    }

    fn remove_trailing_newline(&mut self) {
        if !self.output.ends_with('\n') {
            return;
        }
        self.output.pop();
        self.line_start = false;
        self.line = self.line.saturating_sub(1);
        self.column = u32::try_from(
            self.output
                .rsplit_once('\n')
                .map_or(self.output.len(), |(_, line)| line.len()),
        )
        .unwrap_or(u32::MAX);
    }

    fn finish(mut self) -> String {
        while self.output.ends_with('\n') {
            self.output.pop();
        }
        if !self.output.is_empty() {
            self.output.push('\n');
        }
        self.output
    }

    fn position(&self) -> (u32, u32) {
        let column = if self.line_start {
            u32::try_from(self.indent)
                .unwrap_or(u32::MAX)
                .saturating_mul(4)
        } else {
            self.column
        };
        (self.line, column)
    }
}

fn line_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0];
    starts.extend(
        source
            .bytes()
            .enumerate()
            .filter_map(|(index, byte)| (byte == b'\n').then_some(index + 1)),
    );
    starts
}

fn original_position(source: &str, line_starts: &[usize], byte_offset: u32) -> (u32, u32) {
    let offset = usize::try_from(byte_offset)
        .unwrap_or(source.len())
        .min(source.len());
    let line = line_starts
        .partition_point(|line_start| *line_start <= offset)
        .saturating_sub(1);
    let column = source[line_starts[line]..offset].encode_utf16().count();
    (
        u32::try_from(line).unwrap_or(u32::MAX),
        u32::try_from(column).unwrap_or(u32::MAX),
    )
}

#[derive(Clone, Copy, Debug, Default)]
struct AutomaticJsxUsage {
    jsx: bool,
    jsxs: bool,
    fragment: bool,
}

impl AutomaticJsxUsage {
    fn analyze(arena: &NodeArena, mode: JsxEmit) -> Self {
        if !matches!(mode, JsxEmit::ReactJsx | JsxEmit::ReactJsxDev) {
            return Self::default();
        }
        let mut usage = Self::default();
        for (_, node) in arena.iter() {
            let children = match &node.data {
                NodeData::JsxElement(element) => {
                    arena
                        .get(element.opening_element)
                        .and_then(|opening| match &opening.data {
                            NodeData::JsxOpeningElement(_) => Some(&element.children),
                            _ => None,
                        })
                }
                NodeData::JsxSelfClosingElement(_) => None,
                NodeData::JsxFragment(fragment) => {
                    usage.fragment = true;
                    Some(&fragment.children)
                }
                _ => continue,
            };
            let child_count =
                children.map_or(0, |children| semantic_jsx_children(arena, children).len());
            if child_count > 1 {
                usage.jsxs = true;
            } else {
                usage.jsx = true;
            }
        }
        usage
    }

    const fn any(self) -> bool {
        self.jsx || self.jsxs || self.fragment
    }
}

struct SystemDependency {
    specifier: String,
    storage: String,
    parameter: String,
}

struct AmdRuntimeDependency {
    path: String,
    parameter: Option<String>,
}

struct SystemModulePlan {
    export_function: String,
    context_object: String,
    dependencies: Vec<SystemDependency>,
    hoisted_names: Vec<String>,
    identifier_rewrites: HashMap<ts_ast::SymbolId, String>,
}

struct GeneratedNames {
    used: HashSet<String>,
}

impl GeneratedNames {
    fn new(arena: &NodeArena) -> Self {
        Self {
            used: arena
                .iter()
                .filter_map(|(_, node)| match &node.data {
                    NodeData::Identifier(identifier) => Some(identifier.text.clone()),
                    _ => None,
                })
                .collect(),
        }
    }

    fn generate(&mut self, base: &str) -> String {
        let mut index = 1_u32;
        loop {
            let candidate = format!("{base}_{index}");
            if self.used.insert(candidate.clone()) {
                return candidate;
            }
            index += 1;
        }
    }
}

impl SystemModulePlan {
    #[allow(clippy::too_many_lines)]
    fn analyze(arena: &NodeArena, bindings: &BindResult, data: &ts_ast::SourceFileData) -> Self {
        let mut names = GeneratedNames::new(arena);
        let export_function = names.generate("exports");
        let context_object = names.generate("context");
        let mut dependencies = Vec::new();
        let mut hoisted_names = Vec::new();
        let mut identifier_rewrites = HashMap::new();
        for statement in &data.statements.nodes {
            let Some(node) = arena.get(*statement) else {
                continue;
            };
            match &node.data {
                NodeData::ImportEqualsDeclaration(import) => {
                    let Some(local) = declaration_name_text(arena, import.name) else {
                        continue;
                    };
                    if let Some(specifier) =
                        external_module_reference_text(arena, import.module_reference)
                    {
                        let parameter = names.generate(local);
                        dependencies.push(SystemDependency {
                            specifier: specifier.to_owned(),
                            storage: local.to_owned(),
                            parameter,
                        });
                        push_unique(&mut hoisted_names, local);
                    } else {
                        push_unique(&mut hoisted_names, local);
                    }
                }
                NodeData::ImportDeclaration(import) => {
                    let Some(clause) = import.import_clause else {
                        continue;
                    };
                    let Some(NodeData::ImportClause(clause)) =
                        arena.get(clause).map(|node| &node.data)
                    else {
                        continue;
                    };
                    let Some(specifier) = string_literal_text(arena, import.module_specifier)
                    else {
                        continue;
                    };
                    let base = module_identifier_base(specifier);
                    let storage = if let Some(bindings_id) = clause.named_bindings
                        && let Some(NodeData::NamespaceImport(namespace)) =
                            arena.get(bindings_id).map(|node| &node.data)
                    {
                        declaration_name_text(arena, namespace.name)
                            .unwrap_or(&base)
                            .to_owned()
                    } else {
                        names.generate(&base)
                    };
                    let parameter = names.generate(&storage);
                    dependencies.push(SystemDependency {
                        specifier: specifier.to_owned(),
                        storage: storage.clone(),
                        parameter,
                    });
                    push_unique(&mut hoisted_names, &storage);
                    if let Some(name) = clause.name
                        && let Some(symbol) = bindings.node_symbols.get(&name)
                    {
                        identifier_rewrites.insert(*symbol, format!("{storage}.default"));
                    }
                    if let Some(bindings_id) = clause.named_bindings {
                        match arena.get(bindings_id).map(|node| &node.data) {
                            Some(NodeData::NamedImports(imports)) => {
                                for specifier_id in &imports.elements.nodes {
                                    let Some(NodeData::ImportSpecifier(import)) =
                                        arena.get(*specifier_id).map(|node| &node.data)
                                    else {
                                        continue;
                                    };
                                    let imported = import.property_name.unwrap_or(import.name);
                                    let Some(imported) = declaration_name_text(arena, imported)
                                    else {
                                        continue;
                                    };
                                    if let Some(symbol) = bindings.node_symbols.get(&import.name) {
                                        identifier_rewrites
                                            .insert(*symbol, format!("{storage}.{imported}"));
                                    }
                                }
                            }
                            Some(NodeData::NamespaceImport(namespace)) => {
                                if let Some(symbol) = bindings.node_symbols.get(&namespace.name) {
                                    identifier_rewrites.insert(*symbol, storage.clone());
                                }
                            }
                            _ => {}
                        }
                    }
                }
                NodeData::VariableStatement(statement) => {
                    for name in simple_variable_names(arena, statement.declaration_list) {
                        push_unique(&mut hoisted_names, &name);
                    }
                }
                NodeData::ModuleDeclaration(module)
                    if !declaration_has_modifier(arena, node, SyntaxKind::DeclareKeyword) =>
                {
                    if let Some(name) = declaration_name_text(arena, module.name) {
                        push_unique(&mut hoisted_names, name);
                        collect_namespace_alias_rewrites(
                            arena,
                            bindings,
                            module,
                            name,
                            &mut identifier_rewrites,
                        );
                    }
                }
                _ => {}
            }
        }
        Self {
            export_function,
            context_object,
            dependencies,
            hoisted_names,
            identifier_rewrites,
        }
    }
}

fn push_unique(names: &mut Vec<String>, name: &str) {
    if !names.iter().any(|existing| existing == name) {
        names.push(name.to_owned());
    }
}

fn string_literal_text(arena: &NodeArena, node: NodeId) -> Option<&str> {
    match &arena.get(node)?.data {
        NodeData::StringLiteral(literal) => Some(&literal.text),
        _ => None,
    }
}

fn external_module_reference_text(arena: &NodeArena, node: NodeId) -> Option<&str> {
    let NodeData::ExternalModuleReference(reference) = &arena.get(node)?.data else {
        return None;
    };
    string_literal_text(arena, reference.expression)
}

fn module_identifier_base(specifier: &str) -> String {
    let last = specifier.rsplit(['/', '\\']).next().unwrap_or(specifier);
    let mut value = last
        .chars()
        .map(|character| {
            if character.is_ascii_alphanumeric() || character == '_' {
                character
            } else {
                '_'
            }
        })
        .collect::<String>();
    if value.is_empty() || value.as_bytes()[0].is_ascii_digit() {
        value.insert(0, '_');
    }
    value
}

fn simple_variable_names(arena: &NodeArena, list: NodeId) -> Vec<String> {
    let Some(NodeData::VariableDeclarationList(list)) = arena.get(list).map(|node| &node.data)
    else {
        return Vec::new();
    };
    list.declarations
        .nodes
        .iter()
        .filter_map(|declaration| {
            let NodeData::VariableDeclaration(declaration) = &arena.get(*declaration)?.data else {
                return None;
            };
            declaration_name_text(arena, declaration.name).map(str::to_owned)
        })
        .collect()
}

fn collect_namespace_alias_rewrites(
    arena: &NodeArena,
    bindings: &BindResult,
    module: &ts_ast::ModuleDeclarationData,
    container: &str,
    rewrites: &mut HashMap<ts_ast::SymbolId, String>,
) {
    let Some(NodeData::ModuleBlock(block)) = module
        .body
        .and_then(|body| arena.get(body))
        .map(|node| &node.data)
    else {
        return;
    };
    for statement in &block.statements.nodes {
        let Some(node) = arena.get(*statement) else {
            continue;
        };
        let NodeData::ImportEqualsDeclaration(import) = &node.data else {
            continue;
        };
        if !declaration_has_modifier(arena, node, SyntaxKind::ExportKeyword) {
            continue;
        }
        let Some(name) = declaration_name_text(arena, import.name) else {
            continue;
        };
        if let Some(symbol) = bindings.node_symbols.get(statement) {
            rewrites.insert(*symbol, format!("{container}.{name}"));
        }
    }
}

struct Printer<'a> {
    arena: &'a NodeArena,
    writer: Writer,
    settings: PrinterSettings,
    source_map: Option<SourceMapBuilder>,
    source_text: &'a str,
    source_name: &'a str,
    source_line_starts: Option<Vec<usize>>,
    automatic_jsx: AutomaticJsxUsage,
    this_alias: Option<&'static str>,
    namespace_containers: Vec<String>,
    namespace_declarations: Vec<HashSet<String>>,
    runtime_identifier_uses: HashSet<String>,
    commonjs_default_imports: HashMap<String, String>,
    has_runtime_export_equals: bool,
    bindings: &'a BindResult,
    identifier_rewrites: HashMap<ts_ast::SymbolId, String>,
    system_predeclared_names: HashSet<String>,
    commonjs_module_transform: bool,
    enum_member_values: &'a BTreeMap<NodeId, EmitConstantValue>,
    enum_access_values: &'a BTreeMap<NodeId, EmitConstantValue>,
    const_enum_emit_mode: ConstEnumEmitMode,
    enum_access_fallbacks: HashMap<NodeId, EmitConstantValue>,
}

impl Printer<'_> {
    #[allow(clippy::too_many_lines)]
    fn emit_amd_source_file(
        &mut self,
        data: &ts_ast::SourceFileData,
        context: &EmitContext<'_>,
    ) -> Result<EmitResult, EmitError> {
        self.commonjs_module_transform = true;
        self.commonjs_default_imports =
            commonjs_default_imports(self.arena, &data.statements, &self.runtime_identifier_uses);
        let mut dependencies = context
            .amd_dependencies
            .iter()
            .filter_map(|dependency| {
                dependency.name.map(|name| AmdRuntimeDependency {
                    path: dependency.path.to_owned(),
                    parameter: Some(name.to_owned()),
                })
            })
            .collect::<Vec<_>>();
        for statement in &data.statements.nodes {
            let Some(NodeData::ImportEqualsDeclaration(import)) =
                self.arena.get(*statement).map(|node| &node.data)
            else {
                continue;
            };
            if import.is_type_only
                || (!self.has_modifier(import.modifiers.as_ref(), SyntaxKind::ExportKeyword)
                    && !self.import_binding_is_used(import.name))
            {
                continue;
            }
            let Some(path) = external_module_reference_text(self.arena, import.module_reference)
            else {
                continue;
            };
            dependencies.push(AmdRuntimeDependency {
                path: path.to_owned(),
                parameter: Some(self.identifier_text(import.name)?.to_owned()),
            });
        }
        dependencies.extend(
            context
                .amd_dependencies
                .iter()
                .filter(|dependency| dependency.name.is_none())
                .map(|dependency| AmdRuntimeDependency {
                    path: dependency.path.to_owned(),
                    parameter: None,
                }),
        );

        for dependency in context.amd_dependencies {
            let start = usize::try_from(dependency.comment_start).unwrap_or(usize::MAX);
            let end = usize::try_from(dependency.comment_end).unwrap_or(usize::MAX);
            if let Some(comment) = self.source_text.get(start..end) {
                self.writer.write(comment);
                self.writer.newline();
            }
        }
        self.writer.write("define(");
        if let Some(name) = context.amd_module_name {
            write_quoted(&mut self.writer, name);
            self.writer.write(", ");
        }
        self.writer.write("[\"require\", \"exports\"");
        for dependency in &dependencies {
            self.writer.write(", ");
            write_quoted(&mut self.writer, &dependency.path);
        }
        self.writer.write("], function (require, exports");
        for dependency in &dependencies {
            if let Some(parameter) = &dependency.parameter {
                self.writer.write(", ");
                self.writer.write(parameter);
            }
        }
        self.writer.write(") {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("\"use strict\";");
        self.writer.newline();
        if let Some(first_statement) = data.statements.nodes.first()
            && let Some(node) = self.arena.get(*first_statement)
        {
            let excluded = context
                .amd_dependencies
                .iter()
                .map(|dependency| (dependency.comment_start, dependency.comment_end))
                .collect::<Vec<_>>();
            self.emit_leading_source_comments_excluding(node.range.start.get(), &excluded);
        }
        if self.settings.target < ScriptTarget::Es2015 && source_needs_extends_helper(self.arena) {
            self.emit_extends_helper();
        }
        let export_equals_expression =
            runtime_export_equals_expression(self.arena, &data.statements);
        self.has_runtime_export_equals = export_equals_expression.is_some();
        if source_needs_import_star_helper(
            self.arena,
            &data.statements,
            &self.runtime_identifier_uses,
        ) {
            self.emit_import_star_helper();
        }
        if !self.commonjs_default_imports.is_empty() {
            self.emit_import_default_helper();
        }
        if export_equals_expression.is_none() {
            self.writer
                .write("Object.defineProperty(exports, \"__esModule\", { value: true });");
            self.writer.newline();
        }
        self.emit_automatic_jsx_prelude();
        let mut previous_end = data
            .statements
            .nodes
            .first()
            .and_then(|statement| self.arena.get(*statement))
            .map_or(0, |node| node.range.start.get());
        for statement in &data.statements.nodes {
            if let Some(node) = self.arena.get(*statement) {
                if statement_emits_javascript(self.arena, node) {
                    self.emit_source_comments_between(previous_end, node.range.start.get());
                }
                previous_end = node.range.end.get();
            }
            if matches!(
                self.arena.get(*statement).map(|node| &node.data),
                Some(NodeData::ImportEqualsDeclaration(import))
                    if external_module_reference_text(self.arena, import.module_reference).is_some()
            ) {
                continue;
            }
            self.emit_statement(*statement)?;
        }
        if let Some(expression) = export_equals_expression {
            self.writer.write("return ");
            self.emit_expression(expression, 0)?;
            self.writer.write(";");
            self.writer.newline();
        }
        self.writer.indent -= 1;
        self.writer.write("});");
        self.writer.newline();
        let source_map = self
            .source_map
            .take()
            .map(|builder| builder.finish(None, vec![self.source_name.to_owned()]));
        Ok(EmitResult {
            code: std::mem::take(&mut self.writer).finish(),
            source_map,
        })
    }

    fn emit_system_source_file(
        &mut self,
        data: &ts_ast::SourceFileData,
    ) -> Result<EmitResult, EmitError> {
        let plan = SystemModulePlan::analyze(self.arena, self.bindings, data);
        self.identifier_rewrites = plan.identifier_rewrites;
        self.system_predeclared_names
            .extend(plan.hoisted_names.iter().cloned());
        self.writer.write("System.register([");
        for (index, dependency) in plan.dependencies.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            write_quoted(&mut self.writer, &dependency.specifier);
        }
        self.writer.write("], function (");
        self.writer.write(&plan.export_function);
        self.writer.write(", ");
        self.writer.write(&plan.context_object);
        self.writer.write(") {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("\"use strict\";");
        self.writer.newline();
        if !plan.hoisted_names.is_empty() {
            self.writer.write("var ");
            self.writer.write(&plan.hoisted_names.join(", "));
            self.writer.write(";");
            self.writer.newline();
        }
        self.writer.write("var __moduleName = ");
        self.writer.write(&plan.context_object);
        self.writer.write(" && ");
        self.writer.write(&plan.context_object);
        self.writer.write(".id;");
        self.writer.newline();
        self.writer.write("return {");
        self.writer.newline();
        self.writer.indent += 1;
        if plan.dependencies.is_empty() {
            self.writer.write("setters: [],");
            self.writer.newline();
        } else {
            self.writer.write("setters: [");
            self.writer.newline();
            self.writer.indent += 1;
            for (index, dependency) in plan.dependencies.iter().enumerate() {
                self.writer.write("function (");
                self.writer.write(&dependency.parameter);
                self.writer.write(") {");
                self.writer.newline();
                self.writer.indent += 1;
                self.writer.write(&dependency.storage);
                self.writer.write(" = ");
                self.writer.write(&dependency.parameter);
                self.writer.write(";");
                self.writer.newline();
                self.writer.indent -= 1;
                self.writer.write("}");
                if index + 1 != plan.dependencies.len() {
                    self.writer.write(",");
                }
                self.writer.newline();
            }
            self.writer.indent -= 1;
            self.writer.write("],");
            self.writer.newline();
        }
        self.writer.write("execute: function () {");
        self.writer.newline();
        self.writer.indent += 1;
        for statement in &data.statements.nodes {
            self.emit_system_execute_statement(*statement, &plan.export_function)?;
        }
        self.writer.indent -= 1;
        self.writer.write("}");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("};");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("});");
        self.writer.newline();
        let source_map = self
            .source_map
            .take()
            .map(|builder| builder.finish(None, vec![self.source_name.to_owned()]));
        Ok(EmitResult {
            code: std::mem::take(&mut self.writer).finish(),
            source_map,
        })
    }

    fn emit_system_execute_statement(
        &mut self,
        statement: NodeId,
        export_function: &str,
    ) -> Result<(), EmitError> {
        let node = self.node(statement)?.clone();
        match &node.data {
            NodeData::ImportDeclaration(_)
            | NodeData::ExportDeclaration(_)
            | NodeData::ExportAssignment(_) => Ok(()),
            NodeData::ImportEqualsDeclaration(import) => {
                if external_module_reference_text(self.arena, import.module_reference).is_some() {
                    return Ok(());
                }
                let name = self.identifier_text(import.name)?.to_owned();
                if self.has_modifier(import.modifiers.as_ref(), SyntaxKind::ExportKeyword) {
                    self.writer.write(export_function);
                    self.writer.write("(");
                    write_quoted(&mut self.writer, &name);
                    self.writer.write(", ");
                }
                self.writer.write(&name);
                self.writer.write(" = ");
                self.emit_expression(import.module_reference, 1)?;
                if self.has_modifier(import.modifiers.as_ref(), SyntaxKind::ExportKeyword) {
                    self.writer.write(")");
                }
                self.writer.write(";");
                self.writer.newline();
                Ok(())
            }
            NodeData::VariableStatement(variable) => {
                let list_node = self.node(variable.declaration_list)?.clone();
                let NodeData::VariableDeclarationList(list) = &list_node.data else {
                    return Err(Self::unsupported(variable.declaration_list, list_node.kind));
                };
                for declaration in &list.declarations.nodes {
                    let declaration_node = self.node(*declaration)?.clone();
                    let NodeData::VariableDeclaration(declaration) = &declaration_node.data else {
                        return Err(Self::unsupported(*declaration, declaration_node.kind));
                    };
                    let Some(initializer) = declaration.initializer else {
                        continue;
                    };
                    self.emit_expression(declaration.name, 1)?;
                    self.writer.write(" = ");
                    self.emit_expression(initializer, 1)?;
                    self.writer.write(";");
                    self.writer.newline();
                }
                Ok(())
            }
            _ => self.emit_statement(statement),
        }
    }

    fn emit_source_comments_between(&mut self, start: u32, end: u32) {
        self.emit_source_comments_between_with_trailing(start, end, true);
    }

    fn emit_source_comments_between_with_trailing(
        &mut self,
        start: u32,
        end: u32,
        preserve_immediate_trailing: bool,
    ) {
        let start = usize::try_from(start).unwrap_or(usize::MAX);
        let end = usize::try_from(end).unwrap_or(usize::MAX);
        let Some(trivia) = self.source_text.get(start..end) else {
            return;
        };
        let bytes = trivia.as_bytes();
        let mut index = 0;
        while index < bytes.len() {
            if bytes[index..].starts_with(b"//") {
                let comment_end = bytes[index..]
                    .iter()
                    .position(|byte| *byte == b'\n' || *byte == b'\r')
                    .map_or(bytes.len(), |offset| index + offset);
                let immediate_trailing = !trivia[..index].contains(['\n', '\r']);
                if !immediate_trailing || preserve_immediate_trailing {
                    if immediate_trailing {
                        self.writer.remove_trailing_newline();
                        self.writer.write(" ");
                    }
                    self.writer.write(&trivia[index..comment_end]);
                    self.writer.newline();
                }
                index = comment_end;
            } else if bytes[index..].starts_with(b"/*") {
                let comment_end = bytes[index + 2..]
                    .windows(2)
                    .position(|window| window == b"*/")
                    .map_or(bytes.len(), |offset| index + 2 + offset + 2);
                let immediate_trailing = !trivia[..index].contains(['\n', '\r']);
                if !immediate_trailing || preserve_immediate_trailing {
                    if immediate_trailing {
                        self.writer.remove_trailing_newline();
                        self.writer.write(" ");
                    }
                    for line in trivia[index..comment_end]
                        .replace("\r\n", "\n")
                        .replace('\r', "\n")
                        .split('\n')
                    {
                        self.writer.write(line);
                        self.writer.newline();
                    }
                }
                index = comment_end;
            } else {
                index += 1;
            }
        }
    }

    fn emit_leading_source_comments(&mut self, end: u32) {
        self.emit_leading_source_comments_excluding(end, &[]);
    }

    fn emit_leading_source_comments_excluding(&mut self, end: u32, excluded: &[(u32, u32)]) {
        let end = usize::try_from(end).unwrap_or(usize::MAX);
        let Some(prefix) = self.source_text.get(..end) else {
            return;
        };
        let bytes = prefix.as_bytes();
        let mut index = 0;
        while index < bytes.len() {
            if bytes[index..].starts_with(b"//") {
                let comment_end = bytes[index..]
                    .iter()
                    .position(|byte| *byte == b'\n' || *byte == b'\r')
                    .map_or(bytes.len(), |offset| index + offset);
                if !excluded.iter().any(|(start, end)| {
                    usize::try_from(*start) == Ok(index) && usize::try_from(*end) == Ok(comment_end)
                }) {
                    self.writer.write(&prefix[index..comment_end]);
                    self.writer.newline();
                }
                index = comment_end;
            } else if bytes[index..].starts_with(b"/*") {
                let comment_end = bytes[index + 2..]
                    .windows(2)
                    .position(|window| window == b"*/")
                    .map_or(bytes.len(), |offset| index + 2 + offset + 2);
                for line in prefix[index..comment_end]
                    .replace("\r\n", "\n")
                    .replace('\r', "\n")
                    .split('\n')
                {
                    self.writer.write(line);
                    self.writer.newline();
                }
                index = comment_end;
            } else {
                index += 1;
            }
        }
    }

    fn emit_import_star_helper(&mut self) {
        for line in [
            "var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {",
            "    if (k2 === undefined) k2 = k;",
            "    var desc = Object.getOwnPropertyDescriptor(m, k);",
            "    if (!desc || (\"get\" in desc ? !m.__esModule : desc.writable || desc.configurable)) {",
            "      desc = { enumerable: true, get: function() { return m[k]; } };",
            "    }",
            "    Object.defineProperty(o, k2, desc);",
            "}) : (function(o, m, k, k2) {",
            "    if (k2 === undefined) k2 = k;",
            "    o[k2] = m[k];",
            "}));",
            "var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {",
            "    Object.defineProperty(o, \"default\", { enumerable: true, value: v });",
            "}) : function(o, v) {",
            "    o[\"default\"] = v;",
            "});",
            "var __importStar = (this && this.__importStar) || (function () {",
            "    var ownKeys = function(o) {",
            "        ownKeys = Object.getOwnPropertyNames || function (o) {",
            "            var ar = [];",
            "            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;",
            "            return ar;",
            "        };",
            "        return ownKeys(o);",
            "    };",
            "    return function (mod) {",
            "        if (mod && mod.__esModule) return mod;",
            "        var result = {};",
            "        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== \"default\") __createBinding(result, mod, k[i]);",
            "        __setModuleDefault(result, mod);",
            "        return result;",
            "    };",
            "})();",
        ] {
            self.writer.write(line);
            self.writer.newline();
        }
    }

    fn emit_import_default_helper(&mut self) {
        for line in [
            "var __importDefault = (this && this.__importDefault) || function (mod) {",
            "    return (mod && mod.__esModule) ? mod : { \"default\": mod };",
            "};",
        ] {
            self.writer.write(line);
            self.writer.newline();
        }
    }

    fn emit_extends_helper(&mut self) {
        self.writer
            .write("var __extends = (this && this.__extends) || (function () {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("var extendStatics = function (d, b) {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer
            .write("extendStatics = Object.setPrototypeOf ||");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write(
            "({ __proto__: [] } instanceof Array && function (d, b) { d.__proto__ = b; }) ||",
        );
        self.writer.newline();
        self.writer.write(
            "function (d, b) { for (var p in b) if (Object.prototype.hasOwnProperty.call(b, p)) d[p] = b[p]; };",
        );
        self.writer.indent -= 1;
        self.writer.newline();
        self.writer.write("return extendStatics(d, b);");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("};");
        self.writer.newline();
        self.writer.write("return function (d, b) {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer
            .write("if (typeof b !== \"function\" && b !== null)");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write(
            "throw new TypeError(\"Class extends value \" + String(b) + \" is not a constructor or null\");",
        );
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("extendStatics(d, b);");
        self.writer.newline();
        self.writer.write("function __() { this.constructor = d; }");
        self.writer.newline();
        self.writer.write(
            "d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());",
        );
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("};");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("})();");
        self.writer.newline();
    }

    fn emit_automatic_jsx_prelude(&mut self) {
        if !self.automatic_jsx.any() {
            return;
        }
        let development = self.settings.jsx == JsxEmit::ReactJsxDev;
        let runtime = if development {
            "react/jsx-dev-runtime"
        } else {
            "react/jsx-runtime"
        };
        if self.commonjs_module_transform {
            self.writer.write("const jsx_runtime_1 = require(");
            write_quoted(&mut self.writer, runtime);
            self.writer.write(");");
            self.writer.newline();
        } else {
            self.writer.write("import { ");
            let mut first = true;
            for (used, imported, local) in [
                (development, "jsxDEV", "_jsxDEV"),
                (!development && self.automatic_jsx.jsx, "jsx", "_jsx"),
                (!development && self.automatic_jsx.jsxs, "jsxs", "_jsxs"),
                (self.automatic_jsx.fragment, "Fragment", "_Fragment"),
            ] {
                if !used {
                    continue;
                }
                if !first {
                    self.writer.write(", ");
                }
                first = false;
                self.writer.write(imported);
                self.writer.write(" as ");
                self.writer.write(local);
            }
            self.writer.write(" } from ");
            write_quoted(&mut self.writer, runtime);
            self.writer.write(";");
            self.writer.newline();
        }
        if development {
            self.writer.write("const _jsxFileName = ");
            write_quoted(&mut self.writer, self.source_name);
            self.writer.write(";");
            self.writer.newline();
        }
    }

    fn node(&self, id: NodeId) -> Result<&Node, EmitError> {
        self.arena.get(id).ok_or(EmitError {
            node: id,
            kind: SyntaxKind::Unknown,
        })
    }

    const fn unsupported(id: NodeId, kind: SyntaxKind) -> EmitError {
        EmitError { node: id, kind }
    }

    fn record_mapping(&mut self, node: &Node) {
        if self.source_map.is_none() {
            return;
        }
        let (line, column) = self.writer.position();
        let (original_line, original_column) = original_position(
            self.source_text,
            self.source_line_starts
                .as_deref()
                .expect("source line starts exist when source maps are enabled"),
            node.range.start.get(),
        );
        if let Some(builder) = &mut self.source_map {
            let _ = builder.add_mapping(line, column, 0, original_line, original_column);
        }
    }

    #[allow(clippy::too_many_lines)]
    fn emit_statement(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        if declaration_has_modifier(self.arena, &node, SyntaxKind::DeclareKeyword) {
            return Ok(());
        }
        if is_const_enum_declaration(self.arena, &node)
            && !self.const_enum_emit_mode.preserves_declarations()
        {
            return Ok(());
        }
        if matches!(
            &node.data,
            NodeData::ExportAssignment(assignment) if assignment.is_export_equals
        ) {
            return Ok(());
        }
        if self.settings.module == ModuleKind::System
            && let Some(container) = self.namespace_containers.last().cloned()
            && let NodeData::ImportEqualsDeclaration(import) = &node.data
            && self.has_modifier(import.modifiers.as_ref(), SyntaxKind::ExportKeyword)
        {
            let name = self.identifier_text(import.name)?.to_owned();
            self.writer.write(&container);
            self.writer.write(".");
            self.writer.write(&name);
            self.writer.write(" = ");
            self.emit_expression(import.module_reference, 1)?;
            self.writer.write(";");
            self.writer.newline();
            return Ok(());
        }
        match &node.data {
            NodeData::ImportDeclaration(import) if !self.import_has_runtime_use(import) => {
                return Ok(());
            }
            NodeData::ImportEqualsDeclaration(import)
                if import.is_type_only
                    || (!self
                        .has_modifier(import.modifiers.as_ref(), SyntaxKind::ExportKeyword)
                        && !self.import_binding_is_used(import.name)) =>
            {
                return Ok(());
            }
            _ => {}
        }
        if self.commonjs_module_transform
            && declaration_has_modifier(self.arena, &node, SyntaxKind::ExportKeyword)
            && let NodeData::VariableStatement(statement) = &node.data
            && self.variable_list_is_uninitialized(statement.declaration_list)
        {
            return Ok(());
        }
        match &node.data {
            NodeData::InterfaceDeclaration(_) | NodeData::TypeAliasDeclaration(_) => return Ok(()),
            NodeData::FunctionDeclaration(data) if data.body.is_none() => return Ok(()),
            _ => {}
        }
        self.record_mapping(&node);
        match &node.data {
            NodeData::Block(_) => self.emit_block(id)?,
            NodeData::EmptyStatement(_) => self.writer.write(";"),
            NodeData::VariableStatement(data) => {
                if !self.emit_commonjs_default_import_export_variable(data)? {
                    self.emit_runtime_declaration_modifiers(data.modifiers.as_ref());
                    self.emit_variable_list(data.declaration_list)?;
                    self.writer.write(";");
                    let names = self.variable_declaration_names(data.declaration_list)?;
                    self.emit_commonjs_declaration_exports(data.modifiers.as_ref(), &names);
                }
            }
            NodeData::FunctionDeclaration(data) => {
                self.emit_runtime_declaration_modifiers(data.modifiers.as_ref());
                if self.has_modifier(data.modifiers.as_ref(), SyntaxKind::AsyncKeyword) {
                    self.writer.write("async ");
                }
                self.writer.write("function");
                if data.asterisk_token.is_some() {
                    self.writer.write("*");
                }
                self.writer.write(" ");
                if let Some(name) = data.name {
                    self.emit_expression(name, 0)?;
                }
                self.emit_parameters(&data.parameters)?;
                self.writer.write(" ");
                self.emit_function_body(data.body.expect("body checked above"))?;
            }
            NodeData::ClassDeclaration(data) => {
                self.emit_runtime_declaration_modifiers(data.modifiers.as_ref());
                self.emit_class(data)?;
                if let Some(name) = data.name {
                    let names = self.declaration_names(&[name]);
                    if let Some(container) = self.namespace_containers.last().cloned() {
                        if self.has_modifier(data.modifiers.as_ref(), SyntaxKind::ExportKeyword)
                            && let Some(name) = names.first()
                        {
                            self.writer.newline();
                            self.writer.write(&container);
                            self.writer.write(".");
                            self.writer.write(name);
                            self.writer.write(" = ");
                            self.writer.write(name);
                            self.writer.write(";");
                        }
                    } else {
                        self.emit_commonjs_declaration_exports(data.modifiers.as_ref(), &names);
                    }
                }
            }
            NodeData::EnumDeclaration(data) => {
                self.emit_runtime_declaration_modifiers(data.modifiers.as_ref());
                self.emit_enum(data)?;
                let names = self.declaration_names(&[data.name]);
                self.emit_commonjs_declaration_exports(data.modifiers.as_ref(), &names);
            }
            NodeData::ModuleDeclaration(data) => self.emit_namespace(data)?,
            NodeData::ReturnStatement(data) => {
                self.writer.write("return");
                if let Some(expression) = data.expression {
                    self.writer.write(" ");
                    self.emit_expression(expression, 0)?;
                }
                self.writer.write(";");
            }
            NodeData::IfStatement(data) => {
                self.writer.write("if (");
                self.emit_expression(data.expression, 0)?;
                self.writer.write(") ");
                self.emit_embedded(data.then_statement)?;
                if let Some(otherwise) = data.else_statement {
                    self.writer.newline();
                    self.writer.write("else ");
                    self.emit_embedded(otherwise)?;
                }
            }
            NodeData::WhileStatement(data) => {
                self.writer.write("while (");
                self.emit_expression(data.expression, 0)?;
                self.writer.write(") ");
                self.emit_embedded(data.statement)?;
            }
            NodeData::DoStatement(data) => {
                self.writer.write("do ");
                self.emit_embedded(data.statement)?;
                self.writer.write(" while (");
                self.emit_expression(data.expression, 0)?;
                self.writer.write(");");
            }
            NodeData::ForStatement(data) => {
                self.writer.write("for (");
                if let Some(initializer) = data.initializer {
                    if matches!(
                        &self.node(initializer)?.data,
                        NodeData::VariableDeclarationList(_)
                    ) {
                        self.emit_variable_list(initializer)?;
                    } else {
                        self.emit_expression(initializer, 0)?;
                    }
                }
                self.writer.write(";");
                if let Some(condition) = data.condition {
                    self.writer.write(" ");
                    self.emit_expression(condition, 0)?;
                }
                self.writer.write(";");
                if let Some(incrementor) = data.incrementor {
                    self.writer.write(" ");
                    self.emit_expression(incrementor, 0)?;
                }
                self.writer.write(") ");
                self.emit_embedded(data.statement)?;
            }
            NodeData::ForInOrOfStatement(data) => {
                self.writer.write("for");
                if data.await_modifier.is_some() {
                    self.writer.write(" await");
                }
                self.writer.write(" (");
                if matches!(
                    &self.node(data.initializer)?.data,
                    NodeData::VariableDeclarationList(_)
                ) {
                    self.emit_variable_list(data.initializer)?;
                } else {
                    self.emit_expression(data.initializer, 0)?;
                }
                self.writer
                    .write(if node.kind == SyntaxKind::ForInStatement {
                        " in "
                    } else {
                        " of "
                    });
                self.emit_expression(data.expression, 0)?;
                self.writer.write(") ");
                self.emit_embedded(data.statement)?;
            }
            NodeData::SwitchStatement(data) => self.emit_switch(data)?,
            NodeData::TryStatement(data) => self.emit_try(data)?,
            NodeData::ThrowStatement(data) => {
                self.writer.write("throw ");
                self.emit_expression(data.expression, 0)?;
                self.writer.write(";");
            }
            NodeData::BreakStatement(data) => {
                self.writer.write("break");
                if let Some(label) = data.label {
                    self.writer.write(" ");
                    self.emit_expression(label, 0)?;
                }
                self.writer.write(";");
            }
            NodeData::ContinueStatement(data) => {
                self.writer.write("continue");
                if let Some(label) = data.label {
                    self.writer.write(" ");
                    self.emit_expression(label, 0)?;
                }
                self.writer.write(";");
            }
            NodeData::DebuggerStatement(_) => self.writer.write("debugger;"),
            NodeData::LabeledStatement(data) => {
                self.emit_expression(data.label, 0)?;
                self.writer.write(": ");
                self.emit_statement(data.statement)?;
                return Ok(());
            }
            NodeData::WithStatement(data) => {
                self.writer.write("with (");
                self.emit_expression(data.expression, 0)?;
                self.writer.write(") ");
                self.emit_embedded(data.statement)?;
            }
            NodeData::ImportDeclaration(data) => self.emit_import(data)?,
            NodeData::ImportEqualsDeclaration(data) => self.emit_import_equals(data)?,
            NodeData::ExportAssignment(data) => {
                if self.commonjs_module_transform {
                    self.writer.write("exports.default = ");
                } else {
                    self.writer.write("export default ");
                }
                self.emit_expression(data.expression, 0)?;
                self.writer.write(";");
            }
            NodeData::ExportDeclaration(data) => self.emit_export(data)?,
            NodeData::ExpressionStatement(data) => {
                self.emit_expression(data.expression, 0)?;
                self.writer.write(";");
            }
            _ => return Err(Self::unsupported(id, node.kind)),
        }
        self.writer.newline();
        Ok(())
    }

    fn emit_switch(&mut self, data: &ts_ast::SwitchStatementData) -> Result<(), EmitError> {
        self.writer.write("switch (");
        self.emit_expression(data.expression, 0)?;
        self.writer.write(") {");
        self.writer.newline();
        let block = self.node(data.case_block)?.clone();
        let NodeData::CaseBlock(block) = &block.data else {
            return Err(Self::unsupported(data.case_block, block.kind));
        };
        self.writer.indent += 1;
        for clause_id in &block.clauses.nodes {
            let clause_node = self.node(*clause_id)?.clone();
            let NodeData::CaseOrDefaultClause(clause) = &clause_node.data else {
                return Err(Self::unsupported(*clause_id, clause_node.kind));
            };
            if clause_node.kind == SyntaxKind::DefaultClause {
                self.writer.write("default:");
            } else {
                self.writer.write("case ");
                self.emit_expression(clause.expression, 0)?;
                self.writer.write(":");
            }
            self.writer.newline();
            self.writer.indent += 1;
            for statement in &clause.statements.nodes {
                self.emit_statement(*statement)?;
            }
            self.writer.indent -= 1;
        }
        self.writer.indent -= 1;
        self.writer.write("}");
        Ok(())
    }

    fn emit_try(&mut self, data: &ts_ast::TryStatementData) -> Result<(), EmitError> {
        self.writer.write("try ");
        self.emit_block(data.try_block)?;
        if let Some(catch_id) = data.catch_clause {
            let catch_node = self.node(catch_id)?.clone();
            let NodeData::CatchClause(catch) = &catch_node.data else {
                return Err(Self::unsupported(catch_id, catch_node.kind));
            };
            self.writer.write(" catch");
            if let Some(variable_id) = catch.variable_declaration {
                let variable_node = self.node(variable_id)?.clone();
                let NodeData::VariableDeclaration(variable) = &variable_node.data else {
                    return Err(Self::unsupported(variable_id, variable_node.kind));
                };
                self.writer.write(" (");
                self.emit_expression(variable.name, 0)?;
                self.writer.write(")");
            }
            self.writer.write(" ");
            self.emit_block(catch.block)?;
        }
        if let Some(finally_block) = data.finally_block {
            self.writer.write(" finally ");
            self.emit_block(finally_block)?;
        }
        Ok(())
    }

    fn emit_block(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        let NodeData::Block(data) = &node.data else {
            return Err(Self::unsupported(id, node.kind));
        };
        let source_multiline = self.node_source_is_multiline(id);
        if data.statements.nodes.is_empty() && !source_multiline {
            self.writer.write("{ }");
            return Ok(());
        }
        self.writer.write("{");
        self.writer.newline();
        self.writer.indent += 1;
        let mut previous_end = node.range.start.get().saturating_add(1);
        let mut previous_emitted = false;
        for statement in &data.statements.nodes {
            let statement_node = self.node(*statement)?.clone();
            self.emit_source_comments_between_with_trailing(
                previous_end,
                statement_node.range.start.get(),
                previous_emitted,
            );
            self.emit_statement(*statement)?;
            previous_end = statement_node.range.end.get();
            previous_emitted = statement_emits_javascript(self.arena, &statement_node);
        }
        self.emit_source_comments_between_with_trailing(
            previous_end,
            node.range.end.get().saturating_sub(1),
            previous_emitted,
        );
        self.writer.indent -= 1;
        self.writer.write("}");
        Ok(())
    }

    fn emit_function_body(&mut self, body: NodeId) -> Result<(), EmitError> {
        if self.commonjs_module_transform
            && let Some(statement) = self.single_line_body_statement(body)?
        {
            self.writer.write("{ ");
            self.emit_statement(statement)?;
            self.writer.remove_trailing_newline();
            self.writer.write(" }");
            Ok(())
        } else {
            self.emit_block(body)
        }
    }

    fn emit_accessor_body(&mut self, body: Option<NodeId>) -> Result<(), EmitError> {
        let Some(body) = body else {
            self.writer.write("{ }");
            return Ok(());
        };
        if let Some(expression) = self.single_line_return_expression(body)? {
            self.writer.write("{ return ");
            self.emit_expression(expression, 0)?;
            self.writer.write("; }");
        } else if let Some(statement) = self.single_line_body_statement(body)? {
            self.writer.write("{ ");
            self.emit_statement(statement)?;
            self.writer.remove_trailing_newline();
            self.writer.write(" }");
        } else {
            self.emit_block(body)?;
        }
        Ok(())
    }

    fn emit_embedded(&mut self, id: NodeId) -> Result<(), EmitError> {
        if matches!(&self.node(id)?.data, NodeData::Block(_)) {
            return self.emit_block(id);
        }
        self.writer.newline();
        self.writer.indent += 1;
        self.emit_statement(id)?;
        self.writer.indent -= 1;
        self.writer.remove_trailing_newline();
        Ok(())
    }

    fn emit_variable_list(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        let NodeData::VariableDeclarationList(data) = &node.data else {
            return Err(Self::unsupported(id, node.kind));
        };
        let keyword = if self.settings.target < ScriptTarget::Es2015 {
            "var"
        } else if node.flags.0 & (1 << 1) != 0 {
            "const"
        } else if node.flags.0 & 1 != 0 {
            "let"
        } else {
            "var"
        };
        self.writer.write(keyword);
        self.writer.write(" ");
        for (index, declaration) in data.declarations.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            let declaration_node = self.node(*declaration)?.clone();
            let NodeData::VariableDeclaration(declaration) = &declaration_node.data else {
                return Err(Self::unsupported(*declaration, declaration_node.kind));
            };
            self.emit_expression(declaration.name, 0)?;
            if let Some(initializer) = declaration.initializer {
                self.writer.write(" = ");
                self.emit_expression(initializer, 1)?;
            }
        }
        Ok(())
    }

    fn emit_parameters(&mut self, parameters: &NodeList) -> Result<(), EmitError> {
        self.writer.write("(");
        let mut emitted = 0;
        for parameter in &parameters.nodes {
            let node = self.node(*parameter)?.clone();
            let NodeData::ParameterDeclaration(data) = &node.data else {
                return Err(Self::unsupported(*parameter, node.kind));
            };
            if self.identifier_text(data.name).ok() == Some("this") {
                continue;
            }
            if emitted != 0 {
                self.writer.write(", ");
            }
            emitted += 1;
            if data.dot_dot_dot_token.is_some() {
                self.writer.write("...");
            }
            self.emit_expression(data.name, 0)?;
            if let Some(initializer) = data.initializer {
                self.writer.write(" = ");
                self.emit_expression(initializer, 1)?;
            }
        }
        self.writer.write(")");
        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    fn emit_class(&mut self, data: &ts_ast::ClassDeclarationData) -> Result<(), EmitError> {
        if self.settings.target < ScriptTarget::Es2015 {
            return self.emit_downlevel_class(data);
        }
        let lower_fields = self.settings.target < ScriptTarget::Es2022;
        let has_base = self.class_base_expression(data)?.is_some();
        self.writer.write("class");
        if let Some(name) = data.name {
            self.writer.write(" ");
            self.emit_expression(name, 0)?;
        }
        if let Some(clauses) = &data.heritage_clauses {
            for clause in &clauses.nodes {
                let node = self.node(*clause)?.clone();
                if let NodeData::HeritageClause(clause) = &node.data
                    && clause.token == SyntaxKind::ExtendsKeyword
                    && let Some(base) = clause.types.nodes.first()
                {
                    self.writer.write(" extends ");
                    let base_node = self.node(*base)?.clone();
                    if let NodeData::ExpressionWithTypeArguments(base) = &base_node.data {
                        self.emit_expression(base.expression, 0)?;
                    }
                }
            }
        }
        self.writer.write(" {");
        self.writer.newline();
        self.writer.indent += 1;
        let has_constructor = data.members.nodes.iter().any(|member| {
            let Some(node) = self.arena.get(*member) else {
                return false;
            };
            let NodeData::MethodDeclaration(method) = &node.data else {
                return false;
            };
            !self.class_member_is_abstract(node)
                && method.body.is_some()
                && self.is_constructor_name(method.name)
        });
        if lower_fields && self.has_instance_field_initializers(data) && !has_constructor {
            self.emit_synthesized_native_constructor(data, has_base)?;
        }
        let mut previous_end = data.members.range.start.get();
        let mut previous_emitted = false;
        for member in &data.members.nodes {
            let node = self.node(*member)?.clone();
            self.emit_source_comments_between_with_trailing(
                previous_end,
                node.range.start.get(),
                previous_emitted,
            );
            if previous_emitted {
                self.emit_class_empty_elements_between(previous_end, node.range.start.get());
            }
            let current_emitted = !self.class_member_is_abstract(&node)
                && match &node.data {
                    NodeData::MethodDeclaration(method) => method.body.is_some(),
                    NodeData::PropertyDeclaration(_) => !lower_fields,
                    NodeData::GetAccessorDeclaration(accessor) => accessor.body.is_some(),
                    NodeData::SetAccessorDeclaration(accessor) => accessor.body.is_some(),
                    NodeData::ClassStaticBlockDeclaration(_) => true,
                    _ => false,
                };
            previous_end = node.range.end.get();
            previous_emitted = current_emitted;
            if self.class_member_is_abstract(&node) {
                continue;
            }
            match &node.data {
                NodeData::MethodDeclaration(method) if method.body.is_some() => {
                    if lower_fields && self.is_constructor_name(method.name) {
                        self.emit_native_constructor(method, data, has_base)?;
                        continue;
                    }
                    if self.has_modifier(method.modifiers.as_ref(), SyntaxKind::StaticKeyword) {
                        self.writer.write("static ");
                    }
                    if self.has_modifier(method.modifiers.as_ref(), SyntaxKind::AsyncKeyword) {
                        self.writer.write("async ");
                    }
                    if method.asterisk_token.is_some() {
                        self.writer.write("*");
                    }
                    self.emit_expression(method.name, 0)?;
                    self.emit_parameters(&method.parameters)?;
                    self.writer.write(" ");
                    self.emit_block(method.body.expect("body checked above"))?;
                    self.writer.newline();
                }
                NodeData::MethodDeclaration(_) => {}
                NodeData::PropertyDeclaration(_) if lower_fields => {}
                NodeData::PropertyDeclaration(property) => {
                    if self.has_modifier(property.modifiers.as_ref(), SyntaxKind::StaticKeyword) {
                        self.writer.write("static ");
                    }
                    self.emit_expression(property.name, 0)?;
                    if let Some(initializer) = property.initializer {
                        self.writer.write(" = ");
                        self.emit_expression(initializer, 1)?;
                    }
                    self.writer.write(";");
                    self.writer.newline();
                }
                NodeData::GetAccessorDeclaration(accessor) => {
                    if self.has_modifier(accessor.modifiers.as_ref(), SyntaxKind::StaticKeyword) {
                        self.writer.write("static ");
                    }
                    self.writer.write("get ");
                    self.emit_expression(accessor.name, 0)?;
                    self.emit_parameters(&accessor.parameters)?;
                    self.writer.write(" ");
                    self.emit_accessor_body(accessor.body)?;
                    self.writer.newline();
                }
                NodeData::SetAccessorDeclaration(accessor) => {
                    if self.has_modifier(accessor.modifiers.as_ref(), SyntaxKind::StaticKeyword) {
                        self.writer.write("static ");
                    }
                    self.writer.write("set ");
                    self.emit_expression(accessor.name, 0)?;
                    self.emit_parameters(&accessor.parameters)?;
                    self.writer.write(" ");
                    self.emit_accessor_body(accessor.body)?;
                    self.writer.newline();
                }
                NodeData::ClassStaticBlockDeclaration(block) => {
                    self.writer.write("static ");
                    self.emit_block(block.body)?;
                    self.writer.newline();
                }
                _ => return Err(Self::unsupported(*member, node.kind)),
            }
        }
        self.emit_source_comments_between_with_trailing(
            previous_end,
            data.members.range.end.get(),
            previous_emitted,
        );
        if previous_emitted {
            self.emit_class_empty_elements_between(previous_end, data.members.range.end.get());
        }
        self.writer.indent -= 1;
        self.writer.write("}");
        if lower_fields {
            self.emit_native_static_fields(data)?;
        }
        Ok(())
    }

    fn emit_synthesized_native_constructor(
        &mut self,
        data: &ts_ast::ClassDeclarationData,
        has_base: bool,
    ) -> Result<(), EmitError> {
        if has_base {
            self.writer.write("constructor() {");
            self.writer.newline();
            self.writer.indent += 1;
            self.writer.write("super(...arguments);");
            self.writer.newline();
        } else {
            self.writer.write("constructor() {");
            self.writer.newline();
            self.writer.indent += 1;
        }
        self.emit_instance_fields(data, "this")?;
        self.writer.indent -= 1;
        self.writer.write("}");
        self.writer.newline();
        Ok(())
    }

    fn emit_native_constructor(
        &mut self,
        method: &ts_ast::MethodDeclarationData,
        data: &ts_ast::ClassDeclarationData,
        has_base: bool,
    ) -> Result<(), EmitError> {
        let body_id = method.body.expect("constructor body checked");
        let body_node = self.node(body_id)?.clone();
        let NodeData::Block(body) = &body_node.data else {
            return Err(Self::unsupported(body_id, body_node.kind));
        };
        self.writer.write("constructor");
        self.emit_parameters(&method.parameters)?;
        if body.statements.nodes.is_empty()
            && !self.node_source_is_multiline(body_id)
            && !self.has_instance_field_initializers(data)
            && !self.has_parameter_properties(&method.parameters)
        {
            self.writer.write(" { }");
            self.writer.newline();
            return Ok(());
        }
        self.writer.write(" {");
        self.writer.newline();
        self.writer.indent += 1;
        if !has_base {
            self.emit_instance_fields(data, "this")?;
            self.emit_parameter_properties(&method.parameters, "this")?;
        }
        let mut emitted_fields = !has_base;
        let mut previous_end = body_node.range.start.get().saturating_add(1);
        let mut previous_emitted = false;
        for statement in &body.statements.nodes {
            let statement_node = self.node(*statement)?.clone();
            self.emit_source_comments_between_with_trailing(
                previous_end,
                statement_node.range.start.get(),
                previous_emitted,
            );
            self.emit_statement(*statement)?;
            if has_base && !emitted_fields && self.is_super_call_statement(*statement)? {
                self.emit_instance_fields(data, "this")?;
                self.emit_parameter_properties(&method.parameters, "this")?;
                emitted_fields = true;
            }
            previous_end = statement_node.range.end.get();
            previous_emitted = statement_emits_javascript(self.arena, &statement_node);
        }
        self.emit_source_comments_between_with_trailing(
            previous_end,
            body_node.range.end.get().saturating_sub(1),
            previous_emitted,
        );
        if !emitted_fields {
            self.emit_instance_fields(data, "this")?;
            self.emit_parameter_properties(&method.parameters, "this")?;
        }
        self.writer.indent -= 1;
        self.writer.write("}");
        self.writer.newline();
        Ok(())
    }

    fn has_parameter_properties(&self, parameters: &NodeList) -> bool {
        parameters.nodes.iter().any(|parameter| {
            let Some(NodeData::ParameterDeclaration(parameter)) =
                self.arena.get(*parameter).map(|node| &node.data)
            else {
                return false;
            };
            self.parameter_is_property(parameter)
        })
    }

    fn parameter_is_property(&self, parameter: &ts_ast::ParameterDeclarationData) -> bool {
        [
            SyntaxKind::PublicKeyword,
            SyntaxKind::PrivateKeyword,
            SyntaxKind::ProtectedKeyword,
            SyntaxKind::ReadonlyKeyword,
        ]
        .into_iter()
        .any(|kind| self.has_modifier(parameter.modifiers.as_ref(), kind))
    }

    fn emit_parameter_properties(
        &mut self,
        parameters: &NodeList,
        receiver: &str,
    ) -> Result<(), EmitError> {
        for parameter in &parameters.nodes {
            let node = self.node(*parameter)?.clone();
            let NodeData::ParameterDeclaration(parameter) = &node.data else {
                return Err(Self::unsupported(*parameter, node.kind));
            };
            if !self.parameter_is_property(parameter) {
                continue;
            }
            self.writer.write(receiver);
            self.emit_downlevel_member_access(parameter.name)?;
            self.writer.write(" = ");
            self.emit_expression(parameter.name, 0)?;
            self.writer.write(";");
            self.writer.newline();
        }
        Ok(())
    }

    fn emit_native_static_fields(
        &mut self,
        data: &ts_ast::ClassDeclarationData,
    ) -> Result<(), EmitError> {
        let Some(name) = data.name else {
            return Ok(());
        };
        for member in &data.members.nodes {
            let node = self.node(*member)?.clone();
            if self.class_member_is_abstract(&node) {
                continue;
            }
            let NodeData::PropertyDeclaration(property) = &node.data else {
                continue;
            };
            if !self.has_modifier(property.modifiers.as_ref(), SyntaxKind::StaticKeyword) {
                continue;
            }
            let Some(initializer) = property.initializer else {
                continue;
            };
            self.writer.newline();
            self.emit_expression(name, 0)?;
            self.emit_downlevel_member_access(property.name)?;
            self.writer.write(" = ");
            self.emit_expression(initializer, 1)?;
            self.writer.write(";");
        }
        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    fn emit_downlevel_class(
        &mut self,
        data: &ts_ast::ClassDeclarationData,
    ) -> Result<(), EmitError> {
        let name = data
            .name
            .and_then(|name| self.identifier_text(name).ok())
            .unwrap_or("_class")
            .to_owned();
        let base = self.class_base_expression(data)?;
        self.writer.write("var ");
        self.writer.write(&name);
        self.writer.write(" = /** @class */ (function (");
        if base.is_some() {
            self.writer.write("_super");
        }
        self.writer.write(") {");
        self.writer.newline();
        self.writer.indent += 1;
        if base.is_some() {
            self.writer.write("__extends(");
            self.writer.write(&name);
            self.writer.write(", _super);");
            self.writer.newline();
        }

        let constructor = data.members.nodes.iter().find_map(|member| {
            let node = self.arena.get(*member)?;
            let NodeData::MethodDeclaration(method) = &node.data else {
                return None;
            };
            (!self.class_member_is_abstract(node)
                && method.body.is_some()
                && self.is_constructor_name(method.name))
            .then_some(method.as_ref())
        });
        self.writer.write("function ");
        self.writer.write(&name);
        if let Some(constructor) = constructor {
            self.emit_parameters(&constructor.parameters)?;
            self.writer.write(" {");
            self.writer.newline();
            self.writer.indent += 1;
            if base.is_none() {
                self.emit_instance_fields(data, "this")?;
            }
            let mut emitted_fields = base.is_none();
            let previous_this_alias = self.this_alias;
            let mut uses_this_alias = false;
            if let Some(body) = constructor.body {
                let body_node = self.node(body)?.clone();
                let NodeData::Block(body) = &body_node.data else {
                    return Err(Self::unsupported(
                        constructor.body.expect("body"),
                        body_node.kind,
                    ));
                };
                let mut previous_end = body_node.range.start.get().saturating_add(1);
                let mut previous_emitted = false;
                for statement in &body.statements.nodes {
                    let statement_node = self.node(*statement)?.clone();
                    self.emit_source_comments_between_with_trailing(
                        previous_end,
                        statement_node.range.start.get(),
                        previous_emitted,
                    );
                    if base.is_some() && self.emit_super_statement(*statement)? {
                        self.this_alias = Some("_this");
                        uses_this_alias = true;
                        if !emitted_fields {
                            self.emit_instance_fields(data, "_this")?;
                            emitted_fields = true;
                        }
                    } else {
                        self.emit_statement(*statement)?;
                    }
                    previous_end = statement_node.range.end.get();
                    previous_emitted = statement_emits_javascript(self.arena, &statement_node);
                }
                self.emit_source_comments_between_with_trailing(
                    previous_end,
                    body_node.range.end.get().saturating_sub(1),
                    previous_emitted,
                );
            }
            if !emitted_fields {
                self.emit_instance_fields(data, "this")?;
            }
            if uses_this_alias {
                self.writer.write("return _this;");
                self.writer.newline();
            }
            self.this_alias = previous_this_alias;
            self.writer.indent -= 1;
            self.writer.write("}");
            self.writer.newline();
        } else if base.is_some() {
            self.emit_parameters(&NodeList::default())?;
            self.writer.write(" {");
            self.writer.newline();
            self.writer.indent += 1;
            let has_fields = self.has_instance_field_initializers(data);
            if has_fields {
                self.writer
                    .write("var _this = _super !== null && _super.apply(this, arguments) || this;");
                self.writer.newline();
                self.emit_instance_fields(data, "_this")?;
                self.writer.write("return _this;");
            } else {
                self.writer
                    .write("return _super !== null && _super.apply(this, arguments) || this;");
            }
            self.writer.newline();
            self.writer.indent -= 1;
            self.writer.write("}");
            self.writer.newline();
        } else {
            self.writer.write("() {");
            self.writer.newline();
            self.writer.indent += 1;
            self.emit_instance_fields(data, "this")?;
            self.writer.indent -= 1;
            self.writer.write("}");
            self.writer.newline();
        }

        let mut previous_end = data.members.range.start.get();
        let mut previous_emitted = false;
        for (index, member) in data.members.nodes.iter().enumerate() {
            let node = self.node(*member)?.clone();
            self.emit_source_comments_between_with_trailing(
                previous_end,
                node.range.start.get(),
                previous_emitted,
            );
            if previous_emitted {
                self.emit_class_empty_elements_between(previous_end, node.range.start.get());
            }
            let current_emitted = !self.class_member_is_abstract(&node)
                && (matches!(
                    &node.data,
                    NodeData::MethodDeclaration(method) if method.body.is_some()
                ) || matches!(
                    &node.data,
                    NodeData::GetAccessorDeclaration(accessor) if accessor.body.is_some()
                ) || matches!(
                    &node.data,
                    NodeData::SetAccessorDeclaration(accessor) if accessor.body.is_some()
                ));
            previous_end = node.range.end.get();
            previous_emitted = current_emitted;
            if self.class_member_is_abstract(&node) {
                // Abstract members have no runtime representation.
            } else {
                match &node.data {
                    NodeData::MethodDeclaration(method)
                        if method.body.is_some() && !self.is_constructor_name(method.name) =>
                    {
                        self.writer.write(&name);
                        if !self.has_modifier(method.modifiers.as_ref(), SyntaxKind::StaticKeyword)
                        {
                            self.writer.write(".prototype");
                        }
                        self.emit_downlevel_member_access(method.name)?;
                        self.writer.write(" = ");
                        if self.has_modifier(method.modifiers.as_ref(), SyntaxKind::AsyncKeyword) {
                            self.writer.write("async ");
                        }
                        self.writer.write("function");
                        if method.asterisk_token.is_some() {
                            self.writer.write("*");
                        }
                        self.writer.write(" ");
                        self.emit_parameters(&method.parameters)?;
                        self.writer.write(" ");
                        self.emit_block(method.body.expect("body checked"))?;
                        self.writer.write(";");
                        self.writer.newline();
                    }
                    NodeData::GetAccessorDeclaration(_) | NodeData::SetAccessorDeclaration(_) => {
                        self.emit_downlevel_accessor(data, &name, index)?;
                    }
                    _ => {}
                }
            }
        }
        self.emit_source_comments_between_with_trailing(
            previous_end,
            data.members.range.end.get(),
            previous_emitted,
        );
        if previous_emitted {
            self.emit_class_empty_elements_between(previous_end, data.members.range.end.get());
        }
        self.emit_static_fields(data, &name)?;
        self.writer.write("return ");
        self.writer.write(&name);
        self.writer.write(";");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("}(");
        if let Some(base) = base {
            self.emit_expression(base, 0)?;
        }
        self.writer.write("));");
        Ok(())
    }

    fn emit_downlevel_accessor(
        &mut self,
        class: &ts_ast::ClassDeclarationData,
        class_name: &str,
        index: usize,
    ) -> Result<(), EmitError> {
        let member = class.members.nodes[index];
        let Some((_, name, is_static, key)) = self.accessor_info(member) else {
            return Ok(());
        };
        if class.members.nodes[..index].iter().any(|previous| {
            self.accessor_info(*previous)
                .is_some_and(|(_, _, previous_static, previous_key)| {
                    previous_static == is_static && previous_key == key
                })
        }) {
            return Ok(());
        }
        let mut getter = None;
        let mut setter = None;
        for candidate in &class.members.nodes {
            let Some((is_getter, _, candidate_static, candidate_key)) =
                self.accessor_info(*candidate)
            else {
                continue;
            };
            if candidate_static == is_static && candidate_key == key {
                if is_getter {
                    getter = Some(*candidate);
                } else {
                    setter = Some(*candidate);
                }
            }
        }
        self.writer.write("Object.defineProperty(");
        self.writer.write(class_name);
        if !is_static {
            self.writer.write(".prototype");
        }
        self.writer.write(", ");
        self.emit_downlevel_property_name(name)?;
        self.writer.write(", {");
        self.writer.newline();
        self.writer.indent += 1;
        if let Some(getter) = getter {
            self.writer.write("get: ");
            self.emit_downlevel_accessor_function(getter)?;
            self.writer.write(",");
            self.writer.newline();
        }
        if let Some(setter) = setter {
            self.writer.write("set: ");
            self.emit_downlevel_accessor_function(setter)?;
            self.writer.write(",");
            self.writer.newline();
        }
        self.writer.write("enumerable: false,");
        self.writer.newline();
        self.writer.write("configurable: true");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("});");
        self.writer.newline();
        Ok(())
    }

    fn accessor_info(&self, id: NodeId) -> Option<(bool, NodeId, bool, String)> {
        let node = self.arena.get(id)?;
        if self.class_member_is_abstract(node) {
            return None;
        }
        let (is_getter, name, modifiers) = match &node.data {
            NodeData::GetAccessorDeclaration(accessor) => {
                (true, accessor.name, accessor.modifiers.as_ref())
            }
            NodeData::SetAccessorDeclaration(accessor) => {
                (false, accessor.name, accessor.modifiers.as_ref())
            }
            _ => return None,
        };
        let is_static = self.has_modifier(modifiers, SyntaxKind::StaticKeyword);
        Some((is_getter, name, is_static, self.accessor_key(name)?))
    }

    fn accessor_key(&self, name: NodeId) -> Option<String> {
        let node = self.arena.get(name)?;
        match &node.data {
            NodeData::Identifier(name) => Some(name.text.clone()),
            NodeData::StringLiteral(name) => Some(name.text.clone()),
            NodeData::NumericLiteral(name) => Some(name.text.clone()),
            NodeData::ComputedPropertyName(_) => {
                let start = usize::try_from(node.range.start.get()).ok()?;
                let end = usize::try_from(node.range.end.get()).ok()?;
                self.source_text.get(start..end).map(str::to_owned)
            }
            _ => None,
        }
    }

    fn emit_downlevel_property_name(&mut self, name: NodeId) -> Result<(), EmitError> {
        let node = self.node(name)?.clone();
        match &node.data {
            NodeData::Identifier(name) => write_quoted(&mut self.writer, &name.text),
            NodeData::StringLiteral(name) => write_quoted(&mut self.writer, &name.text),
            NodeData::NumericLiteral(name) => write_quoted(&mut self.writer, &name.text),
            NodeData::ComputedPropertyName(name) => self.emit_expression(name.expression, 0)?,
            _ => self.emit_expression(name, 0)?,
        }
        Ok(())
    }

    fn emit_downlevel_accessor_function(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        let (parameters, body) = match &node.data {
            NodeData::GetAccessorDeclaration(accessor) => (&accessor.parameters, accessor.body),
            NodeData::SetAccessorDeclaration(accessor) => (&accessor.parameters, accessor.body),
            _ => return Err(Self::unsupported(id, node.kind)),
        };
        self.writer.write("function ");
        self.emit_parameter_names(parameters)?;
        self.writer.write(" ");
        self.emit_downlevel_accessor_body(parameters, body)
    }

    fn emit_parameter_names(&mut self, parameters: &NodeList) -> Result<(), EmitError> {
        self.writer.write("(");
        for (index, parameter) in parameters.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            let node = self.node(*parameter)?.clone();
            let NodeData::ParameterDeclaration(parameter) = &node.data else {
                return Err(Self::unsupported(*parameter, node.kind));
            };
            if parameter.dot_dot_dot_token.is_some() {
                self.writer.write("...");
            }
            self.emit_expression(parameter.name, 0)?;
        }
        self.writer.write(")");
        Ok(())
    }

    fn emit_downlevel_accessor_body(
        &mut self,
        parameters: &NodeList,
        body: Option<NodeId>,
    ) -> Result<(), EmitError> {
        let has_defaults = parameters.nodes.iter().any(|parameter| {
            matches!(
                self.arena.get(*parameter).map(|node| &node.data),
                Some(NodeData::ParameterDeclaration(parameter)) if parameter.initializer.is_some()
            )
        });
        if !has_defaults {
            return self.emit_accessor_body(body);
        }
        self.writer.write("{");
        self.writer.newline();
        self.writer.indent += 1;
        for parameter in &parameters.nodes {
            let node = self.node(*parameter)?.clone();
            let NodeData::ParameterDeclaration(parameter) = &node.data else {
                return Err(Self::unsupported(*parameter, node.kind));
            };
            let Some(initializer) = parameter.initializer else {
                continue;
            };
            self.writer.write("if (");
            self.emit_expression(parameter.name, 0)?;
            self.writer.write(" === void 0) { ");
            self.emit_expression(parameter.name, 0)?;
            self.writer.write(" = ");
            self.emit_expression(initializer, 1)?;
            self.writer.write("; }");
            self.writer.newline();
        }
        if let Some(body) = body {
            let body_node = self.node(body)?.clone();
            let NodeData::Block(block) = &body_node.data else {
                return Err(Self::unsupported(body, body_node.kind));
            };
            for statement in &block.statements.nodes {
                self.emit_statement(*statement)?;
            }
        }
        self.writer.indent -= 1;
        self.writer.write("}");
        Ok(())
    }

    fn class_base_expression(
        &self,
        data: &ts_ast::ClassDeclarationData,
    ) -> Result<Option<NodeId>, EmitError> {
        let Some(clauses) = &data.heritage_clauses else {
            return Ok(None);
        };
        for clause in &clauses.nodes {
            let node = self.node(*clause)?;
            if let NodeData::HeritageClause(clause) = &node.data
                && clause.token == SyntaxKind::ExtendsKeyword
                && let Some(base) = clause.types.nodes.first()
            {
                let base_node = self.node(*base)?;
                if let NodeData::ExpressionWithTypeArguments(base) = &base_node.data {
                    return Ok(Some(base.expression));
                }
            }
        }
        Ok(None)
    }

    fn has_instance_field_initializers(&self, data: &ts_ast::ClassDeclarationData) -> bool {
        data.members.nodes.iter().any(|member| {
            let Some(node) = self.arena.get(*member) else {
                return false;
            };
            !self.class_member_is_abstract(node)
                && matches!(
                    &node.data,
                    NodeData::PropertyDeclaration(property)
                        if property.initializer.is_some()
                            && !self.has_modifier(property.modifiers.as_ref(), SyntaxKind::StaticKeyword)
                )
        })
    }

    fn emit_instance_fields(
        &mut self,
        data: &ts_ast::ClassDeclarationData,
        receiver: &str,
    ) -> Result<(), EmitError> {
        for member in &data.members.nodes {
            let node = self.node(*member)?.clone();
            if self.class_member_is_abstract(&node) {
                continue;
            }
            let NodeData::PropertyDeclaration(property) = &node.data else {
                continue;
            };
            if self.has_modifier(property.modifiers.as_ref(), SyntaxKind::StaticKeyword) {
                continue;
            }
            let Some(initializer) = property.initializer else {
                continue;
            };
            self.writer.write(receiver);
            self.emit_downlevel_member_access(property.name)?;
            self.writer.write(" = ");
            self.emit_expression(initializer, 1)?;
            self.writer.write(";");
            self.writer.newline();
        }
        Ok(())
    }

    fn emit_static_fields(
        &mut self,
        data: &ts_ast::ClassDeclarationData,
        name: &str,
    ) -> Result<(), EmitError> {
        for member in &data.members.nodes {
            let node = self.node(*member)?.clone();
            if self.class_member_is_abstract(&node) {
                continue;
            }
            let NodeData::PropertyDeclaration(property) = &node.data else {
                continue;
            };
            if !self.has_modifier(property.modifiers.as_ref(), SyntaxKind::StaticKeyword) {
                continue;
            }
            let Some(initializer) = property.initializer else {
                continue;
            };
            self.writer.write(name);
            self.emit_downlevel_member_access(property.name)?;
            self.writer.write(" = ");
            self.emit_expression(initializer, 1)?;
            self.writer.write(";");
            self.writer.newline();
        }
        Ok(())
    }

    fn emit_downlevel_member_access(&mut self, name: NodeId) -> Result<(), EmitError> {
        let node = self.node(name)?.clone();
        match &node.data {
            NodeData::Identifier(identifier) => {
                self.writer.write(".");
                self.writer.write(&identifier.text);
            }
            NodeData::PrivateIdentifier(identifier) => {
                self.writer.write(".");
                self.writer.write(identifier.text.trim_start_matches('#'));
            }
            NodeData::ComputedPropertyName(computed) => {
                self.writer.write("[");
                self.emit_expression(computed.expression, 0)?;
                self.writer.write("]");
            }
            _ => {
                self.writer.write("[");
                self.emit_expression(name, 0)?;
                self.writer.write("]");
            }
        }
        Ok(())
    }

    fn emit_super_statement(&mut self, statement: NodeId) -> Result<bool, EmitError> {
        let statement_node = self.node(statement)?.clone();
        let NodeData::ExpressionStatement(expression) = &statement_node.data else {
            return Ok(false);
        };
        let call_node = self.node(expression.expression)?.clone();
        let NodeData::CallExpression(call) = &call_node.data else {
            return Ok(false);
        };
        let callee = self.node(call.expression)?;
        if callee.kind != SyntaxKind::SuperKeyword {
            return Ok(false);
        }
        self.writer.write("var _this = _super.call(this");
        for argument in &call.arguments.nodes {
            self.writer.write(", ");
            self.emit_expression(*argument, 0)?;
        }
        self.writer.write(") || this;");
        self.writer.newline();
        Ok(true)
    }

    fn is_super_call_statement(&self, statement: NodeId) -> Result<bool, EmitError> {
        let statement_node = self.node(statement)?;
        let NodeData::ExpressionStatement(expression) = &statement_node.data else {
            return Ok(false);
        };
        let call_node = self.node(expression.expression)?;
        let NodeData::CallExpression(call) = &call_node.data else {
            return Ok(false);
        };
        Ok(self.node(call.expression)?.kind == SyntaxKind::SuperKeyword)
    }

    fn emit_namespace(&mut self, data: &ts_ast::ModuleDeclarationData) -> Result<(), EmitError> {
        let name = self.identifier_text(data.name)?.to_owned();
        let exported = self.has_modifier(data.modifiers.as_ref(), SyntaxKind::ExportKeyword);
        let parent_container = self.namespace_containers.last().cloned();
        let first_declaration = self
            .namespace_declarations
            .last_mut()
            .expect("every namespace has a lexical declaration scope")
            .insert(name.clone());

        if first_declaration && !self.system_predeclared_names.contains(&name) {
            if parent_container.is_some() && self.settings.target >= ScriptTarget::Es2015 {
                self.writer.write("let ");
            } else {
                self.writer.write("var ");
            }
            self.writer.write(&name);
            self.writer.write(";");
            self.writer.newline();
        }

        self.writer.write("(function (");
        self.writer.write(&name);
        self.writer.write(") {");
        self.writer.newline();
        self.writer.indent += 1;
        self.namespace_containers.push(name.clone());
        self.namespace_declarations.push(HashSet::new());

        if let Some(body) = data.body {
            let body_node = self.node(body)?.clone();
            match &body_node.data {
                NodeData::ModuleBlock(block) => {
                    let mut previous_end = body_node.range.start.get().saturating_add(1);
                    let mut previous_emitted = false;
                    for statement in &block.statements.nodes {
                        let statement_node = self.node(*statement)?.clone();
                        self.emit_source_comments_between_with_trailing(
                            previous_end,
                            statement_node.range.start.get(),
                            previous_emitted,
                        );
                        self.emit_statement(*statement)?;
                        previous_end = statement_node.range.end.get();
                        previous_emitted = statement_emits_javascript(self.arena, &statement_node);
                    }
                    self.emit_source_comments_between_with_trailing(
                        previous_end,
                        body_node.range.end.get().saturating_sub(1),
                        previous_emitted,
                    );
                }
                NodeData::ModuleDeclaration(module) => self.emit_namespace(module)?,
                _ => return Err(Self::unsupported(body, body_node.kind)),
            }
        }

        self.namespace_declarations.pop();
        self.namespace_containers.pop();
        self.writer.indent -= 1;
        self.writer.write("})(");
        if let Some(parent) = parent_container {
            if exported {
                self.writer.write(&name);
                self.writer.write(" = ");
                self.writer.write(&parent);
                self.writer.write(".");
                self.writer.write(&name);
                self.writer.write(" || (");
                self.writer.write(&parent);
                self.writer.write(".");
                self.writer.write(&name);
                self.writer.write(" = {})");
            } else {
                self.writer.write(&name);
                self.writer.write(" || (");
                self.writer.write(&name);
                self.writer.write(" = {})");
            }
        } else if exported && self.commonjs_module_transform {
            self.writer.write(&name);
            self.writer.write(" || (exports.");
            self.writer.write(&name);
            self.writer.write(" = ");
            self.writer.write(&name);
            self.writer.write(" = {})");
        } else {
            self.writer.write(&name);
            self.writer.write(" || (");
            self.writer.write(&name);
            self.writer.write(" = {})");
        }
        self.writer.write(");");
        Ok(())
    }

    fn emit_enum(&mut self, data: &ts_ast::EnumDeclarationData) -> Result<(), EmitError> {
        let name = self.identifier_text(data.name)?.to_owned();
        self.writer.write("var ");
        self.writer.write(&name);
        self.writer.write(";");
        self.writer.newline();
        self.writer.write("(function (");
        self.writer.write(&name);
        self.writer.write(") {");
        self.writer.newline();
        self.writer.indent += 1;
        let mut next_number = 0_i64;
        for member in &data.members.nodes {
            let member_id = *member;
            let node = self.node(*member)?.clone();
            let NodeData::EnumMember(member) = &node.data else {
                return Err(Self::unsupported(*member, node.kind));
            };
            let member_name = self.identifier_text(member.name)?.to_owned();
            let constant = self.enum_member_values.get(&member_id);
            self.writer.write(&name);
            self.writer.write("[");
            let is_string_member = matches!(constant, Some(EmitConstantValue::String(_)))
                || member.initializer.is_some_and(|initializer| {
                    matches!(
                        self.arena.get(initializer).map(|node| &node.data),
                        Some(
                            NodeData::StringLiteral(_) | NodeData::NoSubstitutionTemplateLiteral(_)
                        )
                    )
                });
            if is_string_member {
                write_quoted(&mut self.writer, &member_name);
                self.writer.write("] = ");
                if let Some(constant) = constant {
                    write_enum_constant(&mut self.writer, constant);
                } else {
                    self.emit_expression(
                        member.initializer.expect("initializer checked above"),
                        1,
                    )?;
                }
            } else {
                self.writer.write(&name);
                self.writer.write("[");
                write_quoted(&mut self.writer, &member_name);
                self.writer.write("] = ");
                if let Some(constant) = constant {
                    write_enum_constant(&mut self.writer, constant);
                } else if let Some(initializer) = member.initializer {
                    self.emit_expression(initializer, 1)?;
                    if let NodeData::NumericLiteral(literal) = &self.node(initializer)?.data
                        && let Ok(value) = literal.text.parse::<i64>()
                    {
                        next_number = value.saturating_add(1);
                    }
                } else {
                    self.writer.write(&next_number.to_string());
                    next_number = next_number.saturating_add(1);
                }
                self.writer.write("] = ");
                write_quoted(&mut self.writer, &member_name);
            }
            self.writer.write(";");
            self.writer.newline();
        }
        self.writer.indent -= 1;
        self.writer.write("})(");
        self.writer.write(&name);
        self.writer.write(" || (");
        self.writer.write(&name);
        self.writer.write(" = {}));");
        Ok(())
    }

    fn emit_import(&mut self, data: &ts_ast::ImportDeclarationData) -> Result<(), EmitError> {
        if self.commonjs_module_transform {
            return self.emit_commonjs_import(data);
        }
        self.writer.write("import ");
        if let Some(clause) = data.import_clause {
            let clause_node = self.node(clause)?.clone();
            let NodeData::ImportClause(clause) = &clause_node.data else {
                return Err(Self::unsupported(clause, clause_node.kind));
            };
            if let Some(name) = clause.name {
                self.emit_expression(name, 0)?;
                if clause.named_bindings.is_some() {
                    self.writer.write(", ");
                }
            }
            if let Some(bindings) = clause.named_bindings {
                self.emit_named_imports(bindings)?;
            }
            self.writer.write(" from ");
        }
        self.emit_expression(data.module_specifier, 0)?;
        if let Some(attributes) = data.attributes {
            self.emit_import_attributes(attributes)?;
        }
        self.writer.write(";");
        Ok(())
    }

    fn emit_import_equals(
        &mut self,
        data: &ts_ast::ImportEqualsDeclarationData,
    ) -> Result<(), EmitError> {
        if data.is_type_only {
            return Ok(());
        }
        self.writer.write(self.variable_keyword());
        self.writer.write(" ");
        self.emit_expression(data.name, 0)?;
        self.writer.write(" = ");
        let reference = self.node(data.module_reference)?.clone();
        match &reference.data {
            NodeData::ExternalModuleReference(reference) => {
                self.writer.write("require(");
                self.emit_expression(reference.expression, 0)?;
                self.writer.write(")");
            }
            NodeData::Identifier(_) => self.emit_expression(data.module_reference, 0)?,
            NodeData::QualifiedName(reference) => {
                self.emit_qualified_name(reference)?;
            }
            _ => return Err(Self::unsupported(data.module_reference, reference.kind)),
        }
        self.writer.write(";");
        Ok(())
    }

    fn emit_qualified_name(&mut self, data: &ts_ast::QualifiedNameData) -> Result<(), EmitError> {
        let left = self.node(data.left)?.clone();
        match &left.data {
            NodeData::Identifier(_) => self.emit_expression(data.left, 0)?,
            NodeData::QualifiedName(left) => self.emit_qualified_name(left)?,
            _ => return Err(Self::unsupported(data.left, left.kind)),
        }
        self.writer.write(".");
        self.emit_expression(data.right, 0)
    }

    fn emit_import_attributes(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        let NodeData::ImportAttributes(data) = &node.data else {
            return Err(Self::unsupported(id, node.kind));
        };
        self.writer
            .write(if data.token == SyntaxKind::AssertKeyword {
                " assert { "
            } else {
                " with { "
            });
        for (index, attribute) in data.attributes.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            let node = self.node(*attribute)?.clone();
            let NodeData::ImportAttribute(attribute) = &node.data else {
                return Err(Self::unsupported(*attribute, node.kind));
            };
            self.emit_expression(attribute.name, 0)?;
            self.writer.write(": ");
            self.emit_expression(attribute.value, 0)?;
        }
        self.writer.write(" }");
        Ok(())
    }

    fn emit_commonjs_import(
        &mut self,
        data: &ts_ast::ImportDeclarationData,
    ) -> Result<(), EmitError> {
        let Some(clause_id) = data.import_clause else {
            self.writer.write("require(");
            self.emit_expression(data.module_specifier, 0)?;
            self.writer.write(");");
            return Ok(());
        };
        let clause_node = self.node(clause_id)?.clone();
        let NodeData::ImportClause(clause) = &clause_node.data else {
            return Err(Self::unsupported(clause_id, clause_node.kind));
        };
        let default_local = clause
            .name
            .and_then(|name| self.identifier_text(name).ok())
            .map(str::to_owned)
            .or_else(|| self.commonjs_named_default_local(clause.named_bindings));
        let default_temp = default_local
            .as_ref()
            .and_then(|name| self.commonjs_default_imports.get(name))
            .cloned();
        if let Some(temp) = default_temp.as_deref() {
            self.writer.write(self.variable_keyword());
            self.writer.write(" ");
            self.writer.write(temp);
            self.writer.write(" = __importDefault(require(");
            self.emit_expression(data.module_specifier, 0)?;
            self.writer.write("));");
            if self.commonjs_has_non_default_bindings(clause.named_bindings) {
                self.writer.newline();
            }
        }
        if let Some(bindings) = clause.named_bindings {
            let bindings_node = self.node(bindings)?.clone();
            let is_namespace_import = matches!(bindings_node.data, NodeData::NamespaceImport(_));
            if matches!(&bindings_node.data, NodeData::NamedImports(imports) if imports.elements.nodes.iter().all(|element| self.commonjs_import_specifier_is_default(*element)))
            {
                return Ok(());
            }
            self.writer.write(self.variable_keyword());
            self.writer.write(" ");
            if let NodeData::NamespaceImport(namespace) = &bindings_node.data {
                self.emit_expression(namespace.name, 0)?;
                self.writer.write(" = __importStar(require(");
            } else {
                self.writer.write("{ ");
                self.emit_commonjs_named_imports(bindings)?;
                self.writer.write(" } = require(");
            }
            self.emit_expression(data.module_specifier, 0)?;
            self.writer
                .write(if is_namespace_import { "));" } else { ");" });
        }
        Ok(())
    }

    fn commonjs_named_default_local(&self, bindings: Option<NodeId>) -> Option<String> {
        let NodeData::NamedImports(imports) = &self.arena.get(bindings?)?.data else {
            return None;
        };
        imports.elements.nodes.iter().find_map(|element| {
            let NodeData::ImportSpecifier(specifier) = &self.arena.get(*element)?.data else {
                return None;
            };
            (self.commonjs_import_specifier_is_default(*element) && !specifier.is_type_only)
                .then(|| declaration_name_text(self.arena, specifier.name).map(str::to_owned))
                .flatten()
        })
    }

    fn commonjs_import_specifier_is_default(&self, specifier: NodeId) -> bool {
        let Some(NodeData::ImportSpecifier(specifier)) =
            self.arena.get(specifier).map(|node| &node.data)
        else {
            return false;
        };
        specifier
            .property_name
            .is_some_and(|property| declaration_name_text(self.arena, property) == Some("default"))
    }

    fn commonjs_has_non_default_bindings(&self, bindings: Option<NodeId>) -> bool {
        let Some(bindings) = bindings.and_then(|bindings| self.arena.get(bindings)) else {
            return false;
        };
        match &bindings.data {
            NodeData::NamespaceImport(_) => true,
            NodeData::NamedImports(imports) => imports
                .elements
                .nodes
                .iter()
                .any(|element| !self.commonjs_import_specifier_is_default(*element)),
            _ => false,
        }
    }

    fn emit_commonjs_named_imports(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        let NodeData::NamedImports(data) = &node.data else {
            return Err(Self::unsupported(id, node.kind));
        };
        let mut emitted = false;
        for specifier in &data.elements.nodes {
            if self.commonjs_import_specifier_is_default(*specifier) {
                continue;
            }
            if emitted {
                self.writer.write(", ");
            }
            let node = self.node(*specifier)?.clone();
            let NodeData::ImportSpecifier(specifier) = &node.data else {
                return Err(Self::unsupported(*specifier, node.kind));
            };
            if let Some(property) = specifier.property_name {
                self.emit_expression(property, 0)?;
                self.writer.write(": ");
            }
            self.emit_expression(specifier.name, 0)?;
            emitted = true;
        }
        Ok(())
    }

    fn emit_named_imports(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        if let NodeData::NamespaceImport(data) = &node.data {
            self.writer.write("* as ");
            return self.emit_expression(data.name, 0);
        }
        let NodeData::NamedImports(data) = &node.data else {
            return Err(Self::unsupported(id, node.kind));
        };
        self.writer.write("{ ");
        for (index, specifier) in data.elements.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            let node = self.node(*specifier)?.clone();
            let NodeData::ImportSpecifier(specifier) = &node.data else {
                return Err(Self::unsupported(*specifier, node.kind));
            };
            if let Some(property) = specifier.property_name {
                self.emit_expression(property, 0)?;
                self.writer.write(" as ");
            }
            self.emit_expression(specifier.name, 0)?;
        }
        self.writer.write(" }");
        Ok(())
    }

    fn emit_export(&mut self, data: &ts_ast::ExportDeclarationData) -> Result<(), EmitError> {
        if self.commonjs_module_transform {
            return self.emit_commonjs_export(data);
        }
        self.writer.write("export ");
        if let Some(clause) = data.export_clause {
            let node = self.node(clause)?.clone();
            let NodeData::NamedExports(exports) = &node.data else {
                return Err(Self::unsupported(clause, node.kind));
            };
            self.writer.write("{ ");
            for (index, specifier) in exports.elements.nodes.iter().enumerate() {
                if index != 0 {
                    self.writer.write(", ");
                }
                let node = self.node(*specifier)?.clone();
                let NodeData::ExportSpecifier(specifier) = &node.data else {
                    return Err(Self::unsupported(*specifier, node.kind));
                };
                if let Some(property) = specifier.property_name {
                    self.emit_expression(property, 0)?;
                    self.writer.write(" as ");
                }
                self.emit_expression(specifier.name, 0)?;
            }
            self.writer.write(" }");
        } else {
            self.writer.write("*");
        }
        if let Some(module) = data.module_specifier {
            self.writer.write(" from ");
            self.emit_expression(module, 0)?;
        }
        if let Some(attributes) = data.attributes {
            self.emit_import_attributes(attributes)?;
        }
        self.writer.write(";");
        Ok(())
    }

    fn emit_commonjs_export(
        &mut self,
        data: &ts_ast::ExportDeclarationData,
    ) -> Result<(), EmitError> {
        let Some(clause) = data.export_clause else {
            self.writer.write("Object.assign(exports, require(");
            if let Some(module) = data.module_specifier {
                self.emit_expression(module, 0)?;
            } else {
                write_quoted(&mut self.writer, "");
            }
            self.writer.write("));");
            return Ok(());
        };
        let node = self.node(clause)?.clone();
        let NodeData::NamedExports(exports) = &node.data else {
            return Err(Self::unsupported(clause, node.kind));
        };
        for (index, specifier_id) in exports.elements.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.newline();
            }
            let node = self.node(*specifier_id)?.clone();
            let NodeData::ExportSpecifier(specifier) = &node.data else {
                return Err(Self::unsupported(*specifier_id, node.kind));
            };
            self.writer.write("exports.");
            self.emit_expression(specifier.name, 0)?;
            self.writer.write(" = ");
            if let Some(module) = data.module_specifier {
                self.writer.write("require(");
                self.emit_expression(module, 0)?;
                self.writer.write(").");
            }
            self.emit_expression(specifier.property_name.unwrap_or(specifier.name), 0)?;
            self.writer.write(";");
        }
        Ok(())
    }

    fn variable_keyword(&self) -> &'static str {
        if self.settings.target < ScriptTarget::Es2015 {
            "var"
        } else {
            "const"
        }
    }

    fn has_modifier(&self, modifiers: Option<&ts_ast::ModifierList>, kind: SyntaxKind) -> bool {
        modifiers.is_some_and(|modifiers| {
            modifiers.list.nodes.iter().any(|modifier| {
                self.arena
                    .get(*modifier)
                    .is_some_and(|node| node.kind == kind)
            })
        })
    }

    fn class_member_is_abstract(&self, node: &Node) -> bool {
        let modifiers = match &node.data {
            NodeData::MethodDeclaration(member) => member.modifiers.as_ref(),
            NodeData::PropertyDeclaration(member) => member.modifiers.as_ref(),
            NodeData::GetAccessorDeclaration(member) => member.modifiers.as_ref(),
            NodeData::SetAccessorDeclaration(member) => member.modifiers.as_ref(),
            _ => None,
        };
        self.has_modifier(modifiers, SyntaxKind::AbstractKeyword)
    }

    fn emit_class_empty_elements_between(&mut self, start: u32, end: u32) {
        let start = usize::try_from(start).unwrap_or(usize::MAX);
        let end = usize::try_from(end).unwrap_or(usize::MAX);
        let Some(trivia) = self.source_text.get(start..end) else {
            return;
        };
        let bytes = trivia.as_bytes();
        let mut index = 0;
        while index < bytes.len() {
            if bytes[index..].starts_with(b"//") {
                index = bytes[index..]
                    .iter()
                    .position(|byte| *byte == b'\n' || *byte == b'\r')
                    .map_or(bytes.len(), |offset| index + offset);
            } else if bytes[index..].starts_with(b"/*") {
                index = bytes[index + 2..]
                    .windows(2)
                    .position(|window| window == b"*/")
                    .map_or(bytes.len(), |offset| index + offset + 4);
            } else {
                if bytes[index] == b';' {
                    self.writer.write(";");
                    self.writer.newline();
                }
                index += 1;
            }
        }
    }

    fn emit_runtime_declaration_modifiers(&mut self, modifiers: Option<&ts_ast::ModifierList>) {
        if self.commonjs_module_transform || !self.namespace_containers.is_empty() {
            return;
        }
        if self.has_modifier(modifiers, SyntaxKind::ExportKeyword) {
            self.writer.write("export ");
        }
        if self.has_modifier(modifiers, SyntaxKind::DefaultKeyword) {
            self.writer.write("default ");
        }
    }

    fn variable_declaration_names(&self, list: NodeId) -> Result<Vec<String>, EmitError> {
        let node = self.node(list)?;
        let NodeData::VariableDeclarationList(data) = &node.data else {
            return Err(Self::unsupported(list, node.kind));
        };
        Ok(self.declaration_names(
            &data
                .declarations
                .nodes
                .iter()
                .filter_map(|declaration| {
                    let NodeData::VariableDeclaration(data) = &self.arena.get(*declaration)?.data
                    else {
                        return None;
                    };
                    Some(data.name)
                })
                .collect::<Vec<_>>(),
        ))
    }

    fn variable_list_is_uninitialized(&self, list: NodeId) -> bool {
        let Some(NodeData::VariableDeclarationList(list)) =
            self.arena.get(list).map(|node| &node.data)
        else {
            return false;
        };
        !list.declarations.nodes.is_empty()
            && list.declarations.nodes.iter().all(|declaration| {
                matches!(
                    self.arena.get(*declaration).map(|node| &node.data),
                    Some(NodeData::VariableDeclaration(declaration))
                        if declaration.initializer.is_none()
                )
            })
    }

    fn emit_commonjs_default_import_export_variable(
        &mut self,
        statement: &ts_ast::VariableStatementData,
    ) -> Result<bool, EmitError> {
        if !self.commonjs_module_transform
            || self.commonjs_default_imports.is_empty()
            || !self.has_modifier(statement.modifiers.as_ref(), SyntaxKind::ExportKeyword)
        {
            return Ok(false);
        }
        let list_node = self.node(statement.declaration_list)?.clone();
        let NodeData::VariableDeclarationList(list) = &list_node.data else {
            return Ok(false);
        };
        let [declaration] = list.declarations.nodes.as_slice() else {
            return Ok(false);
        };
        let declaration_node = self.node(*declaration)?.clone();
        let NodeData::VariableDeclaration(declaration) = &declaration_node.data else {
            return Ok(false);
        };
        let Some(initializer) = declaration.initializer else {
            return Ok(false);
        };
        let Some(name) = declaration_name_text(self.arena, declaration.name) else {
            return Ok(false);
        };
        if !self.expression_uses_commonjs_default_import(initializer) {
            return Ok(false);
        }
        self.writer.write("exports.");
        self.writer.write(name);
        self.writer.write(" = ");
        self.emit_expression(initializer, 1)?;
        self.writer.write(";");
        Ok(true)
    }

    fn expression_uses_commonjs_default_import(&self, expression: NodeId) -> bool {
        self.arena.iter().any(|(id, node)| {
            let NodeData::Identifier(identifier) = &node.data else {
                return false;
            };
            if !self.commonjs_default_imports.contains_key(&identifier.text) {
                return false;
            }
            let mut current = id;
            while let Some(parent) = self.arena.get(current).and_then(|node| node.parent) {
                if parent == expression {
                    return true;
                }
                current = parent;
            }
            false
        })
    }

    fn import_binding_is_used(&self, name: NodeId) -> bool {
        self.identifier_text(name)
            .is_ok_and(|name| self.runtime_identifier_uses.contains(name))
    }

    fn import_has_runtime_use(&self, import: &ts_ast::ImportDeclarationData) -> bool {
        if import.attributes.is_some() {
            return true;
        }
        let Some(clause_id) = import.import_clause else {
            return true;
        };
        let Some(NodeData::ImportClause(clause)) = self.arena.get(clause_id).map(|node| &node.data)
        else {
            return true;
        };
        if clause.phase_modifier == Some(SyntaxKind::TypeKeyword) {
            return false;
        }
        let mut saw_binding = false;
        if let Some(name) = clause.name {
            saw_binding = true;
            if self.import_binding_is_used(name) {
                return true;
            }
        }
        let Some(bindings) = clause.named_bindings else {
            return !saw_binding;
        };
        match self.arena.get(bindings).map(|node| &node.data) {
            Some(NodeData::NamespaceImport(namespace)) => {
                saw_binding = true;
                if self.import_binding_is_used(namespace.name) {
                    return true;
                }
            }
            Some(NodeData::NamedImports(imports)) => {
                for specifier in &imports.elements.nodes {
                    let Some(NodeData::ImportSpecifier(specifier)) =
                        self.arena.get(*specifier).map(|node| &node.data)
                    else {
                        continue;
                    };
                    saw_binding = true;
                    if !specifier.is_type_only && self.import_binding_is_used(specifier.name) {
                        return true;
                    }
                }
            }
            _ => return true,
        }
        !saw_binding
    }

    fn declaration_names(&self, nodes: &[NodeId]) -> Vec<String> {
        nodes
            .iter()
            .filter_map(|node| match &self.arena.get(*node)?.data {
                NodeData::Identifier(identifier) => Some(identifier.text.clone()),
                _ => None,
            })
            .collect()
    }

    fn emit_commonjs_declaration_exports(
        &mut self,
        modifiers: Option<&ts_ast::ModifierList>,
        names: &[String],
    ) {
        if !self.commonjs_module_transform
            || self.has_runtime_export_equals
            || !self.has_modifier(modifiers, SyntaxKind::ExportKeyword)
        {
            return;
        }
        for (index, name) in names.iter().enumerate() {
            self.writer.newline();
            let exported = if index == 0 && self.has_modifier(modifiers, SyntaxKind::DefaultKeyword)
            {
                "default"
            } else {
                name
            };
            self.writer.write("exports.");
            self.writer.write(exported);
            self.writer.write(" = ");
            self.writer.write(name);
            self.writer.write(";");
        }
    }

    #[allow(clippy::too_many_lines)]
    fn emit_expression(&mut self, id: NodeId, parent_precedence: u8) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        if self.const_enum_emit_mode.inlines_accesses()
            && let Some(value) = self
                .enum_access_values
                .get(&id)
                .or_else(|| self.enum_access_fallbacks.get(&id))
        {
            let wrap = matches!(value, EmitConstantValue::Number(value) if value.is_sign_negative())
                && parent_precedence > 15;
            if wrap {
                self.writer.write("(");
            }
            write_enum_constant(&mut self.writer, value);
            let start = usize::try_from(node.range.start.get()).unwrap_or(usize::MAX);
            let end = usize::try_from(node.range.end.get()).unwrap_or(usize::MAX);
            if let Some(text) = self.source_text.get(start..end) {
                self.writer.write(" /* ");
                self.writer.write(&text.replace("*/", "*_/"));
                self.writer.write(" */");
            }
            if wrap {
                self.writer.write(")");
            }
            return Ok(());
        }
        match &node.data {
            NodeData::Identifier(data) => {
                if let Some(rewrite) = self
                    .bindings
                    .resolve_name_at(id, &data.text)
                    .and_then(|symbol| self.identifier_rewrites.get(&symbol))
                {
                    self.writer.write(rewrite);
                } else if let Some(temp) = self.commonjs_default_imports.get(&data.text) {
                    self.writer.write(temp);
                    self.writer.write(".default");
                } else {
                    self.writer.write(&data.text);
                }
            }
            NodeData::QualifiedName(data) => self.emit_qualified_name(data)?,
            NodeData::PrivateIdentifier(data) => self.writer.write(&data.text),
            NodeData::NumericLiteral(data) => self.writer.write(&data.text),
            NodeData::BigIntLiteral(data) => self.writer.write(&data.text),
            NodeData::StringLiteral(data) => self.write_source_quoted_string(id, &data.text),
            NodeData::RegularExpressionLiteral(data) => self.writer.write(&data.text),
            NodeData::KeywordExpression(_) => {
                if node.kind == SyntaxKind::ThisKeyword
                    && let Some(alias) = self.this_alias
                {
                    self.writer.write(alias);
                } else {
                    self.writer.write(match node.kind {
                        SyntaxKind::NullKeyword => "null",
                        SyntaxKind::TrueKeyword => "true",
                        SyntaxKind::FalseKeyword => "false",
                        SyntaxKind::UndefinedKeyword => "undefined",
                        SyntaxKind::ThisKeyword => "this",
                        SyntaxKind::SuperKeyword => "super",
                        _ => return Err(Self::unsupported(id, node.kind)),
                    });
                }
            }
            NodeData::BindingPattern(data) => {
                let object = node.kind != SyntaxKind::ArrayBindingPattern;
                self.writer.write(if object { "{" } else { "[" });
                if object && !data.elements.nodes.is_empty() {
                    self.writer.write(" ");
                }
                self.emit_expression_list(&data.elements)?;
                if object && !data.elements.nodes.is_empty() {
                    self.writer.write(" ");
                }
                self.writer.write(if object { "}" } else { "]" });
            }
            NodeData::BindingElement(data) => {
                if data.dot_dot_dot_token.is_some() {
                    self.writer.write("...");
                }
                if let Some(property_name) = data.property_name {
                    self.emit_expression(property_name, 0)?;
                    self.writer.write(": ");
                }
                if let Some(name) = data.name {
                    self.emit_expression(name, 0)?;
                }
                if let Some(initializer) = data.initializer {
                    self.writer.write(" = ");
                    self.emit_expression(initializer, 1)?;
                }
            }
            NodeData::ComputedPropertyName(data) => {
                self.writer.write("[");
                self.emit_expression(data.expression, 0)?;
                self.writer.write("]");
            }
            NodeData::ParenthesizedExpression(data) => {
                let erases_to_inner_expression = matches!(
                    self.node(data.expression)?.data,
                    NodeData::AsExpression(_)
                        | NodeData::SatisfiesExpression(_)
                        | NodeData::TypeAssertion(_)
                );
                if erases_to_inner_expression {
                    self.emit_expression(data.expression, parent_precedence)?;
                } else {
                    self.writer.write("(");
                    self.emit_expression(data.expression, 0)?;
                    self.writer.write(")");
                }
            }
            NodeData::BinaryExpression(data) => {
                let operator = self.node(data.operator_token)?.kind;
                if operator == SyntaxKind::QuestionQuestionToken
                    && self.settings.target < ScriptTarget::Es2020
                {
                    self.emit_downlevel_nullish(data.left, data.right, parent_precedence)?;
                    return Ok(());
                }
                let (precedence, right_associative) = binary_precedence(operator)
                    .ok_or_else(|| Self::unsupported(data.operator_token, operator))?;
                let wrap = precedence < parent_precedence;
                if wrap {
                    self.writer.write("(");
                }
                self.emit_expression(data.left, precedence)?;
                self.writer.write(" ");
                self.writer.write(
                    operator_text(operator)
                        .ok_or_else(|| Self::unsupported(data.operator_token, operator))?,
                );
                let line_break_after_operator =
                    self.source_has_known_line_break_between(data.operator_token, data.right);
                if line_break_after_operator {
                    self.writer.indent += 1;
                    self.writer.newline();
                } else {
                    self.writer.write(" ");
                }
                self.emit_expression(
                    data.right,
                    if right_associative {
                        precedence
                    } else {
                        precedence + 1
                    },
                )?;
                if line_break_after_operator {
                    self.writer.indent -= 1;
                }
                if wrap {
                    self.writer.write(")");
                }
            }
            NodeData::PropertyAccessExpression(data) => {
                if data.question_dot_token.is_some() && self.settings.target < ScriptTarget::Es2020
                {
                    self.emit_downlevel_optional_property(
                        data.expression,
                        data.name,
                        parent_precedence,
                    )?;
                } else {
                    self.emit_expression(data.expression, 18)?;
                    let break_before_dot =
                        self.source_has_line_break_before_property(data.expression, data.name);
                    let break_after_dot =
                        self.source_has_line_break_after_property_dot(data.expression, data.name);
                    if break_before_dot {
                        self.writer.indent += 1;
                        self.writer.newline();
                    }
                    self.writer.write(if data.question_dot_token.is_some() {
                        "?."
                    } else {
                        "."
                    });
                    if break_before_dot {
                        self.writer.indent -= 1;
                    }
                    if break_after_dot {
                        self.writer.indent += 1;
                        self.writer.newline();
                    }
                    self.emit_expression(data.name, 18)?;
                    if break_after_dot {
                        self.writer.indent -= 1;
                    }
                }
            }
            NodeData::ElementAccessExpression(data) => {
                if data.question_dot_token.is_some() && self.settings.target < ScriptTarget::Es2020
                {
                    self.emit_downlevel_optional_element(
                        data.expression,
                        data.argument_expression,
                        parent_precedence,
                    )?;
                } else {
                    self.emit_expression(data.expression, 18)?;
                    if data.question_dot_token.is_some() {
                        self.writer.write("?.");
                    }
                    self.writer.write("[");
                    self.emit_expression(data.argument_expression, 0)?;
                    self.writer.write("]");
                }
            }
            NodeData::CallExpression(data) => {
                if data.question_dot_token.is_some() && self.settings.target < ScriptTarget::Es2020
                {
                    self.emit_downlevel_optional_call(
                        data.expression,
                        &data.arguments,
                        parent_precedence,
                    )?;
                } else {
                    self.emit_expression(data.expression, 18)?;
                    if data.question_dot_token.is_some() {
                        self.writer.write("?.");
                    }
                    self.writer.write("(");
                    self.emit_expression_list(&data.arguments)?;
                    self.writer.write(")");
                }
            }
            NodeData::ArrayLiteralExpression(data) => {
                if self.settings.target < ScriptTarget::Es2015
                    && data.elements.nodes.iter().any(|element| {
                        self.arena
                            .get(*element)
                            .is_some_and(|node| matches!(node.data, NodeData::SpreadElement(_)))
                    })
                {
                    self.emit_downlevel_array_spread(data)?;
                    return Ok(());
                }
                self.writer.write("[");
                self.emit_expression_list(&data.elements)?;
                self.writer.write("]");
            }
            NodeData::SpreadElement(data) => {
                self.writer.write("...");
                self.emit_expression(data.expression, 1)?;
            }
            NodeData::AwaitExpression(data) => {
                self.writer.write("await ");
                self.emit_expression(data.expression, 2)?;
            }
            NodeData::YieldExpression(data) => {
                self.writer.write("yield");
                if data.asterisk_token.is_some() {
                    self.writer.write("*");
                }
                if let Some(expression) = data.expression {
                    self.writer.write(" ");
                    self.emit_expression(expression, 2)?;
                }
            }
            NodeData::NonNullExpression(data) => {
                let parenthesized_assertion = match &self.node(data.expression)?.data {
                    NodeData::ParenthesizedExpression(parenthesized) => matches!(
                        self.node(parenthesized.expression)?.data,
                        NodeData::AsExpression(_)
                            | NodeData::SatisfiesExpression(_)
                            | NodeData::TypeAssertion(_)
                    ),
                    _ => false,
                };
                if parenthesized_assertion {
                    self.writer.write("(");
                    self.emit_expression(data.expression, parent_precedence)?;
                    self.writer.write(")");
                } else {
                    self.emit_expression(data.expression, parent_precedence)?;
                }
            }
            NodeData::AsExpression(data) => {
                self.emit_expression(data.expression, parent_precedence)?;
            }
            NodeData::SatisfiesExpression(data) => {
                self.emit_expression(data.expression, parent_precedence)?;
            }
            NodeData::TypeAssertion(data) => {
                self.emit_expression(data.expression, parent_precedence)?;
            }
            NodeData::NewExpression(data) => {
                self.writer.write("new ");
                self.emit_expression(data.expression, 18)?;
                if let Some(arguments) = &data.arguments {
                    self.writer.write("(");
                    self.emit_expression_list(arguments)?;
                    self.writer.write(")");
                }
            }
            NodeData::ConditionalExpression(data) => {
                let wrap = parent_precedence > 2;
                if wrap {
                    self.writer.write("(");
                }
                self.emit_expression(data.condition, 3)?;
                self.writer.write(" ? ");
                self.emit_expression(data.when_true, 2)?;
                self.writer.write(" : ");
                self.emit_expression(data.when_false, 2)?;
                if wrap {
                    self.writer.write(")");
                }
            }
            NodeData::PrefixUnaryExpression(data) => {
                self.writer.write(
                    operator_text(data.operator).ok_or_else(|| Self::unsupported(id, node.kind))?,
                );
                self.emit_expression(data.operand, 16)?;
            }
            NodeData::PostfixUnaryExpression(data) => {
                self.emit_expression(data.operand, 17)?;
                self.writer.write(
                    operator_text(data.operator).ok_or_else(|| Self::unsupported(id, node.kind))?,
                );
            }
            NodeData::ObjectLiteralExpression(data) => {
                if self.settings.target < ScriptTarget::Es2018
                    && data.properties.nodes.iter().any(|property| {
                        self.arena
                            .get(*property)
                            .is_some_and(|node| matches!(node.data, NodeData::SpreadAssignment(_)))
                    })
                {
                    self.emit_downlevel_object_spread(data)?;
                    return Ok(());
                }
                if data.properties.nodes.is_empty() {
                    self.writer.write("{}");
                    return Ok(());
                }
                let multiline = self.node_source_is_multiline(id);
                self.writer.write("{");
                if multiline {
                    self.writer.newline();
                    self.writer.indent += 1;
                } else {
                    self.writer.write(" ");
                }
                for (index, property) in data.properties.nodes.iter().enumerate() {
                    if index != 0 {
                        if multiline {
                            let previous = data.properties.nodes[index - 1];
                            if self.source_has_line_break_between(previous, *property) {
                                self.writer.newline();
                            } else {
                                self.writer.write(" ");
                            }
                        } else {
                            self.writer.write(", ");
                        }
                    }
                    let node = self.node(*property)?.clone();
                    match &node.data {
                        NodeData::PropertyAssignment(property) => {
                            self.emit_expression(property.name, 0)?;
                            self.writer.write(": ");
                            self.emit_expression(property.initializer, 1)?;
                        }
                        NodeData::ShorthandPropertyAssignment(property) => {
                            self.emit_expression(property.name, 0)?;
                        }
                        NodeData::SpreadAssignment(property) => {
                            self.writer.write("...");
                            self.emit_expression(property.expression, 1)?;
                        }
                        NodeData::MethodDeclaration(method) if method.body.is_some() => {
                            if self
                                .has_modifier(method.modifiers.as_ref(), SyntaxKind::AsyncKeyword)
                            {
                                self.writer.write("async ");
                            }
                            if method.asterisk_token.is_some() {
                                self.writer.write("*");
                            }
                            self.emit_expression(method.name, 0)?;
                            self.emit_parameters(&method.parameters)?;
                            self.writer.write(" ");
                            self.emit_block(method.body.expect("body checked above"))?;
                        }
                        NodeData::GetAccessorDeclaration(accessor) => {
                            self.writer.write("get ");
                            self.emit_expression(accessor.name, 0)?;
                            self.emit_parameters(&accessor.parameters)?;
                            self.writer.write(" ");
                            self.emit_accessor_body(accessor.body)?;
                        }
                        NodeData::SetAccessorDeclaration(accessor) => {
                            self.writer.write("set ");
                            self.emit_expression(accessor.name, 0)?;
                            self.emit_parameters(&accessor.parameters)?;
                            self.writer.write(" ");
                            self.emit_accessor_body(accessor.body)?;
                        }
                        _ => return Err(Self::unsupported(*property, node.kind)),
                    }
                    if multiline
                        && (index + 1 < data.properties.nodes.len()
                            || data.properties.has_trailing_comma)
                    {
                        self.writer.write(",");
                    }
                }
                if multiline {
                    self.writer.newline();
                    self.writer.indent -= 1;
                    self.writer.write("}");
                } else {
                    self.writer.write(" }");
                }
            }
            NodeData::ArrowFunction(data) => {
                let is_async = self.has_modifier(data.modifiers.as_ref(), SyntaxKind::AsyncKeyword);
                if self.settings.target < ScriptTarget::Es2015 && !is_async {
                    let wrap = parent_precedence > 2;
                    if wrap {
                        self.writer.write("(");
                    }
                    self.writer.write("function ");
                    self.emit_parameters(&data.parameters)?;
                    self.writer.write(" ");
                    if matches!(&self.node(data.body)?.data, NodeData::Block(_)) {
                        self.emit_block(data.body)?;
                    } else {
                        self.writer.write("{ return ");
                        self.emit_expression(data.body, 0)?;
                        self.writer.write("; }");
                    }
                    if wrap {
                        self.writer.write(")");
                    }
                    return Ok(());
                }
                let wrap = parent_precedence > 2;
                if wrap {
                    self.writer.write("(");
                }
                if is_async {
                    self.writer.write("async ");
                }
                if self.arrow_uses_bare_parameter(id, data) {
                    let parameter_id = data.parameters.nodes[0];
                    let parameter_node = self.node(parameter_id)?.clone();
                    let NodeData::ParameterDeclaration(parameter) = &parameter_node.data else {
                        return Err(Self::unsupported(parameter_id, parameter_node.kind));
                    };
                    self.emit_expression(parameter.name, 0)?;
                } else {
                    self.emit_parameters(&data.parameters)?;
                }
                self.writer.write(" => ");
                if matches!(&self.node(data.body)?.data, NodeData::Block(_)) {
                    self.emit_block(data.body)?;
                } else {
                    self.emit_expression(data.body, 1)?;
                }
                if wrap {
                    self.writer.write(")");
                }
            }
            NodeData::FunctionExpression(data) => {
                let wrap = parent_precedence > 1;
                if wrap {
                    self.writer.write("(");
                }
                self.writer.write("function");
                if data.asterisk_token.is_some() {
                    self.writer.write("*");
                }
                if let Some(name) = data.name {
                    self.writer.write(" ");
                    self.emit_expression(name, 0)?;
                } else {
                    self.writer.write(" ");
                }
                self.emit_parameters(&data.parameters)?;
                self.writer.write(" ");
                if let Some(expression) = self.single_line_return_expression(data.body)? {
                    self.writer.write("{ return ");
                    self.emit_expression(expression, 0)?;
                    self.writer.write("; }");
                } else {
                    self.emit_block(data.body)?;
                }
                if wrap {
                    self.writer.write(")");
                }
            }
            NodeData::NoSubstitutionTemplateLiteral(data) => {
                if self.settings.target < ScriptTarget::Es2015 {
                    write_quoted(&mut self.writer, &data.text);
                } else {
                    self.writer.write("`");
                    write_template_text(&mut self.writer, &data.text);
                    self.writer.write("`");
                }
            }
            NodeData::TemplateExpression(data) => {
                if self.settings.target < ScriptTarget::Es2015 {
                    self.emit_downlevel_template(data, parent_precedence)?;
                } else {
                    self.emit_template(data)?;
                }
            }
            NodeData::JsxElement(data) => self.emit_jsx_element(data)?,
            NodeData::JsxSelfClosingElement(data) => self.emit_jsx_self_closing(data)?,
            NodeData::JsxFragment(data) => self.emit_jsx_fragment(data)?,
            _ => return Err(Self::unsupported(id, node.kind)),
        }
        Ok(())
    }

    fn emit_jsx_element(&mut self, data: &ts_ast::JsxElementData) -> Result<(), EmitError> {
        let opening_node = self.node(data.opening_element)?.clone();
        let NodeData::JsxOpeningElement(opening) = &opening_node.data else {
            return Err(Self::unsupported(data.opening_element, opening_node.kind));
        };
        if matches!(self.settings.jsx, JsxEmit::Preserve | JsxEmit::ReactNative) {
            self.writer.write("<");
            self.emit_expression(opening.tag_name, 0)?;
            self.emit_jsx_attributes(opening.attributes, true)?;
            self.writer.write(">");
            for child in &data.children.nodes {
                self.emit_jsx_child(*child, true)?;
            }
            let closing_node = self.node(data.closing_element)?.clone();
            let NodeData::JsxClosingElement(closing) = &closing_node.data else {
                return Err(Self::unsupported(data.closing_element, closing_node.kind));
            };
            self.writer.write("</");
            self.emit_expression(closing.tag_name, 0)?;
            self.writer.write(">");
            return Ok(());
        }
        if self.settings.jsx == JsxEmit::React {
            self.emit_react_create_element(
                opening.tag_name,
                opening.attributes,
                Some(&data.children),
            )
        } else {
            self.emit_automatic_jsx(
                opening.tag_name,
                opening.attributes,
                Some(&data.children),
                self.node(data.opening_element)?.range.start.get(),
            )
        }
    }

    fn emit_jsx_self_closing(
        &mut self,
        data: &ts_ast::JsxSelfClosingElementData,
    ) -> Result<(), EmitError> {
        if matches!(self.settings.jsx, JsxEmit::Preserve | JsxEmit::ReactNative) {
            self.writer.write("<");
            self.emit_expression(data.tag_name, 0)?;
            self.emit_jsx_attributes(data.attributes, true)?;
            self.writer.write(" />");
            return Ok(());
        }
        if self.settings.jsx == JsxEmit::React {
            self.emit_react_create_element(data.tag_name, data.attributes, None)
        } else {
            self.emit_automatic_jsx(
                data.tag_name,
                data.attributes,
                None,
                self.node(data.tag_name)?
                    .range
                    .start
                    .get()
                    .saturating_sub(1),
            )
        }
    }

    fn emit_jsx_fragment(&mut self, data: &ts_ast::JsxFragmentData) -> Result<(), EmitError> {
        if matches!(self.settings.jsx, JsxEmit::Preserve | JsxEmit::ReactNative) {
            self.writer.write("<>");
            for child in &data.children.nodes {
                self.emit_jsx_child(*child, true)?;
            }
            self.writer.write("</>");
            return Ok(());
        }
        if self.settings.jsx == JsxEmit::React {
            self.writer
                .write("React.createElement(React.Fragment, null");
            for child in &data.children.nodes {
                self.writer.write(", ");
                self.emit_jsx_child(*child, false)?;
            }
            self.writer.write(")");
            return Ok(());
        }
        self.emit_automatic_fragment(
            &data.children,
            self.node(data.opening_fragment)?.range.start.get(),
        )
    }

    fn emit_react_create_element(
        &mut self,
        tag_name: NodeId,
        attributes: NodeId,
        children: Option<&NodeList>,
    ) -> Result<(), EmitError> {
        self.writer.write("React.createElement(");
        let tag = self.node(tag_name)?.clone();
        if let NodeData::Identifier(identifier) = &tag.data
            && identifier
                .text
                .chars()
                .next()
                .is_some_and(char::is_lowercase)
        {
            write_quoted(&mut self.writer, &identifier.text);
        } else {
            self.emit_expression(tag_name, 0)?;
        }
        self.writer.write(", ");
        self.emit_jsx_attributes(attributes, false)?;
        if let Some(children) = children {
            for child in &children.nodes {
                self.writer.write(", ");
                self.emit_jsx_child(*child, false)?;
            }
        }
        self.writer.write(")");
        Ok(())
    }

    fn emit_automatic_jsx(
        &mut self,
        tag_name: NodeId,
        attributes: NodeId,
        children: Option<&NodeList>,
        location: u32,
    ) -> Result<(), EmitError> {
        let children = children
            .map(|children| semantic_jsx_children(self.arena, children))
            .unwrap_or_default();
        self.emit_automatic_helper(children.len() > 1);
        self.writer.write("(");
        self.emit_jsx_tag(tag_name)?;
        self.writer.write(", ");
        let key = self.emit_automatic_props(attributes, &children)?;
        self.emit_automatic_tail(key, children.len() > 1, location)?;
        self.writer.write(")");
        Ok(())
    }

    fn emit_automatic_fragment(
        &mut self,
        children: &NodeList,
        location: u32,
    ) -> Result<(), EmitError> {
        let children = semantic_jsx_children(self.arena, children);
        self.emit_automatic_helper(children.len() > 1);
        self.writer.write("(");
        self.emit_automatic_fragment_reference();
        self.writer.write(", {");
        if !children.is_empty() {
            self.writer.write(" children: ");
            self.emit_automatic_children(&children)?;
            self.writer.write(" ");
        }
        self.writer.write("}");
        self.emit_automatic_tail(None, children.len() > 1, location)?;
        self.writer.write(")");
        Ok(())
    }

    fn emit_automatic_helper(&mut self, static_children: bool) {
        if self.commonjs_module_transform {
            self.writer.write("(0, jsx_runtime_1.");
            self.writer
                .write(if self.settings.jsx == JsxEmit::ReactJsxDev {
                    "jsxDEV"
                } else if static_children {
                    "jsxs"
                } else {
                    "jsx"
                });
            self.writer.write(")");
        } else if self.settings.jsx == JsxEmit::ReactJsxDev {
            self.writer.write("_jsxDEV");
        } else if static_children {
            self.writer.write("_jsxs");
        } else {
            self.writer.write("_jsx");
        }
    }

    fn emit_automatic_fragment_reference(&mut self) {
        if self.commonjs_module_transform {
            self.writer.write("jsx_runtime_1.Fragment");
        } else {
            self.writer.write("_Fragment");
        }
    }

    fn emit_jsx_tag(&mut self, tag_name: NodeId) -> Result<(), EmitError> {
        let tag = self.node(tag_name)?.clone();
        if let NodeData::Identifier(identifier) = &tag.data
            && identifier
                .text
                .chars()
                .next()
                .is_some_and(char::is_lowercase)
        {
            write_quoted(&mut self.writer, &identifier.text);
        } else {
            self.emit_expression(tag_name, 0)?;
        }
        Ok(())
    }

    fn emit_automatic_props(
        &mut self,
        attributes: NodeId,
        children: &[NodeId],
    ) -> Result<Option<NodeId>, EmitError> {
        let node = self.node(attributes)?.clone();
        let NodeData::JsxAttributes(attributes) = &node.data else {
            return Err(Self::unsupported(attributes, node.kind));
        };
        let key = attributes.properties.nodes.iter().find_map(|attribute| {
            let node = self.arena.get(*attribute)?;
            let NodeData::JsxAttribute(attribute) = &node.data else {
                return None;
            };
            (self.identifier_text(attribute.name).ok() == Some("key"))
                .then_some(attribute.initializer)
                .flatten()
        });
        let has_properties = !children.is_empty()
            || attributes.properties.nodes.iter().any(|attribute| {
                self.arena
                    .get(*attribute)
                    .is_some_and(|node| match &node.data {
                        NodeData::JsxSpreadAttribute(_) => true,
                        NodeData::JsxAttribute(attribute) => {
                            self.identifier_text(attribute.name).ok() != Some("key")
                        }
                        _ => false,
                    })
            });
        self.writer.write("{");
        if has_properties {
            self.writer.write(" ");
        }
        let mut wrote = false;
        for attribute in &attributes.properties.nodes {
            let node = self.node(*attribute)?.clone();
            match &node.data {
                NodeData::JsxSpreadAttribute(attribute) => {
                    if wrote {
                        self.writer.write(", ");
                    }
                    wrote = true;
                    self.writer.write("...");
                    self.emit_expression(attribute.expression, 0)?;
                }
                NodeData::JsxAttribute(attribute) => {
                    if self.identifier_text(attribute.name).ok() == Some("key") {
                        continue;
                    }
                    if wrote {
                        self.writer.write(", ");
                    }
                    wrote = true;
                    self.emit_expression(attribute.name, 0)?;
                    self.writer.write(": ");
                    self.emit_jsx_attribute_initializer(attribute.initializer)?;
                }
                _ => return Err(Self::unsupported(*attribute, node.kind)),
            }
        }
        if !children.is_empty() {
            if wrote {
                self.writer.write(", ");
            }
            self.writer.write("children: ");
            self.emit_automatic_children(children)?;
        }
        if has_properties {
            self.writer.write(" ");
        }
        self.writer.write("}");
        Ok(key)
    }

    fn emit_jsx_attribute_initializer(
        &mut self,
        initializer: Option<NodeId>,
    ) -> Result<(), EmitError> {
        let Some(initializer) = initializer else {
            self.writer.write("true");
            return Ok(());
        };
        let node = self.node(initializer)?.clone();
        match &node.data {
            NodeData::StringLiteral(value) => write_quoted(&mut self.writer, &value.text),
            NodeData::JsxExpression(value) => {
                if let Some(expression) = value.expression {
                    self.emit_expression(expression, 0)?;
                } else {
                    self.writer.write("true");
                }
            }
            _ => return Err(Self::unsupported(initializer, node.kind)),
        }
        Ok(())
    }

    fn emit_automatic_children(&mut self, children: &[NodeId]) -> Result<(), EmitError> {
        if children.len() == 1 {
            return self.emit_automatic_child(children[0]);
        }
        self.writer.write("[");
        for (index, child) in children.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            self.emit_automatic_child(*child)?;
        }
        self.writer.write("]");
        Ok(())
    }

    fn emit_automatic_child(&mut self, child: NodeId) -> Result<(), EmitError> {
        let node = self.node(child)?.clone();
        match &node.data {
            NodeData::JsxText(text) => {
                write_quoted(&mut self.writer, &normalize_jsx_text(&text.text));
            }
            NodeData::JsxExpression(expression) => {
                if let Some(expression) = expression.expression {
                    self.emit_expression(expression, 0)?;
                }
            }
            NodeData::JsxElement(element) => self.emit_jsx_element(element)?,
            NodeData::JsxSelfClosingElement(element) => self.emit_jsx_self_closing(element)?,
            NodeData::JsxFragment(fragment) => self.emit_jsx_fragment(fragment)?,
            _ => return Err(Self::unsupported(child, node.kind)),
        }
        Ok(())
    }

    fn emit_automatic_tail(
        &mut self,
        key: Option<NodeId>,
        static_children: bool,
        location: u32,
    ) -> Result<(), EmitError> {
        if let Some(key) = key {
            self.writer.write(", ");
            self.emit_jsx_attribute_initializer(Some(key))?;
        }
        if self.settings.jsx != JsxEmit::ReactJsxDev {
            return Ok(());
        }
        if key.is_none() {
            self.writer.write(", void 0");
        }
        self.writer.write(if static_children {
            ", true, { fileName: _jsxFileName, lineNumber: "
        } else {
            ", false, { fileName: _jsxFileName, lineNumber: "
        });
        let starts = line_starts(self.source_text);
        let (line, column) = original_position(self.source_text, &starts, location);
        self.writer.write(&(line + 1).to_string());
        self.writer.write(", columnNumber: ");
        self.writer.write(&(column + 1).to_string());
        self.writer.write(" }, this");
        Ok(())
    }

    fn emit_jsx_attributes(&mut self, id: NodeId, preserve: bool) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        let NodeData::JsxAttributes(attributes) = &node.data else {
            return Err(Self::unsupported(id, node.kind));
        };
        if preserve {
            for attribute in &attributes.properties.nodes {
                let node = self.node(*attribute)?.clone();
                match &node.data {
                    NodeData::JsxAttribute(attribute) => {
                        self.writer.write(" ");
                        self.emit_expression(attribute.name, 0)?;
                        if let Some(initializer) = attribute.initializer {
                            self.writer.write("=");
                            let initializer_node = self.node(initializer)?.clone();
                            match &initializer_node.data {
                                NodeData::StringLiteral(value) => {
                                    write_quoted(&mut self.writer, &value.text);
                                }
                                NodeData::JsxExpression(value) => {
                                    self.writer.write("{");
                                    if let Some(expression) = value.expression {
                                        self.emit_expression(expression, 0)?;
                                    }
                                    self.writer.write("}");
                                }
                                _ => {
                                    return Err(Self::unsupported(
                                        initializer,
                                        initializer_node.kind,
                                    ));
                                }
                            }
                        }
                    }
                    NodeData::JsxSpreadAttribute(attribute) => {
                        self.writer.write(" {...");
                        self.emit_expression(attribute.expression, 0)?;
                        self.writer.write("}");
                    }
                    _ => return Err(Self::unsupported(*attribute, node.kind)),
                }
            }
            return Ok(());
        }
        if attributes.properties.nodes.is_empty() {
            self.writer.write("null");
            return Ok(());
        }
        self.writer.write("{");
        for (index, attribute) in attributes.properties.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            let node = self.node(*attribute)?.clone();
            if let NodeData::JsxSpreadAttribute(attribute) = &node.data {
                self.writer.write("...");
                self.emit_expression(attribute.expression, 0)?;
                continue;
            }
            let NodeData::JsxAttribute(attribute) = &node.data else {
                return Err(Self::unsupported(*attribute, node.kind));
            };
            self.emit_expression(attribute.name, 0)?;
            self.writer.write(": ");
            if let Some(initializer) = attribute.initializer {
                let initializer_node = self.node(initializer)?.clone();
                match &initializer_node.data {
                    NodeData::StringLiteral(value) => write_quoted(&mut self.writer, &value.text),
                    NodeData::JsxExpression(value) => {
                        if let Some(expression) = value.expression {
                            self.emit_expression(expression, 0)?;
                        } else {
                            self.writer.write("undefined");
                        }
                    }
                    _ => return Err(Self::unsupported(initializer, initializer_node.kind)),
                }
            } else {
                self.writer.write("true");
            }
        }
        self.writer.write("}");
        Ok(())
    }

    fn emit_jsx_child(&mut self, id: NodeId, preserve: bool) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        match &node.data {
            NodeData::JsxText(text) if preserve => self.writer.write(&text.text),
            NodeData::JsxText(text) => write_quoted(&mut self.writer, &text.text),
            NodeData::JsxExpression(expression) if preserve => {
                self.writer.write("{");
                if let Some(expression) = expression.expression {
                    self.emit_expression(expression, 0)?;
                }
                self.writer.write("}");
            }
            NodeData::JsxExpression(expression) => {
                if let Some(expression) = expression.expression {
                    self.emit_expression(expression, 0)?;
                } else {
                    self.writer.write("undefined");
                }
            }
            NodeData::JsxElement(element) => self.emit_jsx_element(element)?,
            NodeData::JsxSelfClosingElement(element) => self.emit_jsx_self_closing(element)?,
            NodeData::JsxFragment(fragment) => self.emit_jsx_fragment(fragment)?,
            _ => return Err(Self::unsupported(id, node.kind)),
        }
        Ok(())
    }

    fn emit_downlevel_nullish(
        &mut self,
        left: NodeId,
        right: NodeId,
        parent_precedence: u8,
    ) -> Result<(), EmitError> {
        let wrap = parent_precedence > 2;
        if wrap {
            self.writer.write("(");
        }
        self.emit_expression(left, 10)?;
        self.writer.write(" !== null && ");
        self.emit_expression(left, 10)?;
        self.writer.write(" !== void 0 ? ");
        self.emit_expression(left, 2)?;
        self.writer.write(" : ");
        self.emit_expression(right, 2)?;
        if wrap {
            self.writer.write(")");
        }
        Ok(())
    }

    fn emit_downlevel_optional_property(
        &mut self,
        expression: NodeId,
        name: NodeId,
        parent_precedence: u8,
    ) -> Result<(), EmitError> {
        let wrap = parent_precedence > 2;
        if wrap {
            self.writer.write("(");
        }
        self.emit_expression(expression, 10)?;
        self.writer.write(" === null || ");
        self.emit_expression(expression, 10)?;
        self.writer.write(" === void 0 ? void 0 : ");
        self.emit_expression(expression, 18)?;
        self.writer.write(".");
        self.emit_expression(name, 18)?;
        if wrap {
            self.writer.write(")");
        }
        Ok(())
    }

    fn emit_downlevel_optional_call(
        &mut self,
        expression: NodeId,
        arguments: &NodeList,
        parent_precedence: u8,
    ) -> Result<(), EmitError> {
        let wrap = parent_precedence > 2;
        if wrap {
            self.writer.write("(");
        }
        self.emit_expression(expression, 10)?;
        self.writer.write(" === null || ");
        self.emit_expression(expression, 10)?;
        self.writer.write(" === void 0 ? void 0 : ");
        self.emit_expression(expression, 18)?;
        self.writer.write("(");
        self.emit_expression_list(arguments)?;
        self.writer.write(")");
        if wrap {
            self.writer.write(")");
        }
        Ok(())
    }

    fn emit_downlevel_optional_element(
        &mut self,
        expression: NodeId,
        argument: NodeId,
        parent_precedence: u8,
    ) -> Result<(), EmitError> {
        let wrap = parent_precedence > 2;
        if wrap {
            self.writer.write("(");
        }
        self.emit_expression(expression, 10)?;
        self.writer.write(" === null || ");
        self.emit_expression(expression, 10)?;
        self.writer.write(" === void 0 ? void 0 : ");
        self.emit_expression(expression, 18)?;
        self.writer.write("[");
        self.emit_expression(argument, 0)?;
        self.writer.write("]");
        if wrap {
            self.writer.write(")");
        }
        Ok(())
    }

    fn emit_downlevel_object_spread(
        &mut self,
        data: &ts_ast::ObjectLiteralExpressionData,
    ) -> Result<(), EmitError> {
        self.writer.write("Object.assign({}");
        let mut object_open = false;
        let mut properties_in_object = 0_usize;
        for property in &data.properties.nodes {
            let node = self.node(*property)?.clone();
            if let NodeData::SpreadAssignment(spread) = &node.data {
                if object_open {
                    self.writer.write(" }");
                    object_open = false;
                }
                self.writer.write(", ");
                self.emit_expression(spread.expression, 1)?;
                continue;
            }
            if !object_open {
                self.writer.write(", ");
                self.writer.write("{ ");
                object_open = true;
                properties_in_object = 0;
            }
            if properties_in_object != 0 {
                self.writer.write(", ");
            }
            self.emit_object_property(*property, &node)?;
            properties_in_object += 1;
        }
        if object_open {
            self.writer.write(" }");
        }
        self.writer.write(")");
        Ok(())
    }

    fn emit_downlevel_array_spread(
        &mut self,
        data: &ts_ast::ArrayLiteralExpressionData,
    ) -> Result<(), EmitError> {
        self.writer.write("[].concat([]");
        let mut array_open = false;
        let mut elements_in_array = 0_usize;
        for element in &data.elements.nodes {
            let node = self.node(*element)?.clone();
            if let NodeData::SpreadElement(spread) = &node.data {
                if array_open {
                    self.writer.write("]");
                    array_open = false;
                }
                self.writer.write(", ");
                self.emit_expression(spread.expression, 1)?;
                continue;
            }
            if !array_open {
                self.writer.write(", [");
                array_open = true;
                elements_in_array = 0;
            }
            if elements_in_array != 0 {
                self.writer.write(", ");
            }
            self.emit_expression(*element, 0)?;
            elements_in_array += 1;
        }
        if array_open {
            self.writer.write("]");
        }
        self.writer.write(")");
        Ok(())
    }

    fn emit_object_property(&mut self, id: NodeId, node: &Node) -> Result<(), EmitError> {
        match &node.data {
            NodeData::PropertyAssignment(property) => {
                self.emit_expression(property.name, 0)?;
                self.writer.write(": ");
                self.emit_expression(property.initializer, 1)?;
            }
            NodeData::ShorthandPropertyAssignment(property) => {
                self.emit_expression(property.name, 0)?;
            }
            NodeData::MethodDeclaration(method) if method.body.is_some() => {
                if self.has_modifier(method.modifiers.as_ref(), SyntaxKind::AsyncKeyword) {
                    self.writer.write("async ");
                }
                if method.asterisk_token.is_some() {
                    self.writer.write("*");
                }
                self.emit_expression(method.name, 0)?;
                self.emit_parameters(&method.parameters)?;
                self.writer.write(" ");
                self.emit_block(method.body.expect("body checked above"))?;
            }
            NodeData::GetAccessorDeclaration(accessor) => {
                self.writer.write("get ");
                self.emit_expression(accessor.name, 0)?;
                self.emit_parameters(&accessor.parameters)?;
                self.writer.write(" ");
                self.emit_accessor_body(accessor.body)?;
            }
            NodeData::SetAccessorDeclaration(accessor) => {
                self.writer.write("set ");
                self.emit_expression(accessor.name, 0)?;
                self.emit_parameters(&accessor.parameters)?;
                self.writer.write(" ");
                self.emit_accessor_body(accessor.body)?;
            }
            _ => return Err(Self::unsupported(id, node.kind)),
        }
        Ok(())
    }

    fn emit_downlevel_template(
        &mut self,
        data: &ts_ast::TemplateExpressionData,
        parent_precedence: u8,
    ) -> Result<(), EmitError> {
        let wrap = parent_precedence > 12;
        if wrap {
            self.writer.write("(");
        }
        let head = self.node(data.head)?.clone();
        let NodeData::TemplateHead(head) = &head.data else {
            return Err(Self::unsupported(data.head, head.kind));
        };
        write_quoted(&mut self.writer, &head.text);
        for span_id in &data.template_spans.nodes {
            let node = self.node(*span_id)?.clone();
            let NodeData::TemplateSpan(span) = &node.data else {
                return Err(Self::unsupported(*span_id, node.kind));
            };
            self.writer.write(" + ");
            self.emit_expression(span.expression, 13)?;
            self.writer.write(" + ");
            let literal = self.node(span.literal)?.clone();
            match &literal.data {
                NodeData::TemplateMiddle(data) => write_quoted(&mut self.writer, &data.text),
                NodeData::TemplateTail(data) => write_quoted(&mut self.writer, &data.text),
                _ => return Err(Self::unsupported(span.literal, literal.kind)),
            }
        }
        if wrap {
            self.writer.write(")");
        }
        Ok(())
    }

    fn emit_template(&mut self, data: &ts_ast::TemplateExpressionData) -> Result<(), EmitError> {
        let head = self.node(data.head)?.clone();
        let NodeData::TemplateHead(head) = &head.data else {
            return Err(Self::unsupported(data.head, head.kind));
        };
        self.writer.write("`");
        write_template_text(&mut self.writer, &head.text);
        for span in &data.template_spans.nodes {
            let node = self.node(*span)?.clone();
            let NodeData::TemplateSpan(span) = &node.data else {
                return Err(Self::unsupported(*span, node.kind));
            };
            self.writer.write("${");
            self.emit_expression(span.expression, 0)?;
            self.writer.write("}");
            let literal = self.node(span.literal)?.clone();
            match &literal.data {
                NodeData::TemplateMiddle(data) => write_template_text(&mut self.writer, &data.text),
                NodeData::TemplateTail(data) => write_template_text(&mut self.writer, &data.text),
                _ => return Err(Self::unsupported(span.literal, literal.kind)),
            }
        }
        self.writer.write("`");
        Ok(())
    }

    fn emit_expression_list(&mut self, list: &NodeList) -> Result<(), EmitError> {
        let mut previous_end = list.range.start.get();
        for (index, expression) in list.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            let expression_start = self.node(*expression)?.range.start.get();
            self.emit_inline_block_comments(previous_end, expression_start);
            self.emit_expression(*expression, 1)?;
            previous_end = self.node(*expression)?.range.end.get();
        }
        Ok(())
    }

    fn emit_inline_block_comments(&mut self, start: u32, end: u32) {
        let start = usize::try_from(start).unwrap_or(usize::MAX);
        let end = usize::try_from(end).unwrap_or(usize::MAX);
        let Some(trivia) = self.source_text.get(start..end) else {
            return;
        };
        let bytes = trivia.as_bytes();
        let mut index = 0;
        while index + 1 < bytes.len() {
            if bytes[index..].starts_with(b"/*") {
                let comment_end = bytes[index + 2..]
                    .windows(2)
                    .position(|window| window == b"*/")
                    .map_or(bytes.len(), |offset| index + 2 + offset + 2);
                self.writer.write(&trivia[index..comment_end]);
                self.writer.write(" ");
                index = comment_end;
            } else {
                index += 1;
            }
        }
    }

    fn single_line_return_expression(&self, block: NodeId) -> Result<Option<NodeId>, EmitError> {
        let node = self.node(block)?;
        let NodeData::Block(data) = &node.data else {
            return Err(Self::unsupported(block, node.kind));
        };
        let [statement] = data.statements.nodes.as_slice() else {
            return Ok(None);
        };
        if !self.source_text.is_empty() {
            let start = usize::try_from(node.range.start.get()).unwrap_or(usize::MAX);
            let end = usize::try_from(node.range.end.get()).unwrap_or(usize::MAX);
            let Some(text) = self.source_text.get(start..end) else {
                return Ok(None);
            };
            if text.contains('\n') || text.contains('\r') {
                return Ok(None);
            }
        }
        Ok(match &self.node(*statement)?.data {
            NodeData::ReturnStatement(data) => data.expression,
            _ => None,
        })
    }

    fn single_line_body_statement(&self, block: NodeId) -> Result<Option<NodeId>, EmitError> {
        if self.source_text.is_empty() {
            return Ok(None);
        }
        let node = self.node(block)?;
        let NodeData::Block(data) = &node.data else {
            return Err(Self::unsupported(block, node.kind));
        };
        let [statement] = data.statements.nodes.as_slice() else {
            return Ok(None);
        };
        if self.node_source_is_multiline(block) {
            return Ok(None);
        }
        Ok(matches!(
            &self.node(*statement)?.data,
            NodeData::ExpressionStatement(_)
                | NodeData::ReturnStatement(_)
                | NodeData::ThrowStatement(_)
        )
        .then_some(*statement))
    }

    fn node_source_is_multiline(&self, id: NodeId) -> bool {
        let Some(node) = self.arena.get(id) else {
            return false;
        };
        let start = usize::try_from(node.range.start.get()).unwrap_or(usize::MAX);
        let end = usize::try_from(node.range.end.get()).unwrap_or(usize::MAX);
        self.source_text
            .get(start..end)
            .is_some_and(|text| text.contains('\n') || text.contains('\r'))
    }

    fn source_has_line_break_between(&self, left: NodeId, right: NodeId) -> bool {
        let Some(left) = self.arena.get(left) else {
            return true;
        };
        let Some(right) = self.arena.get(right) else {
            return true;
        };
        let start = usize::try_from(left.range.end.get()).unwrap_or(usize::MAX);
        let end = usize::try_from(right.range.start.get()).unwrap_or(usize::MAX);
        self.source_text
            .get(start..end)
            .is_none_or(|text| text.contains('\n') || text.contains('\r'))
    }

    fn source_has_known_line_break_between(&self, left: NodeId, right: NodeId) -> bool {
        let Some(left) = self.arena.get(left) else {
            return false;
        };
        let Some(right) = self.arena.get(right) else {
            return false;
        };
        let start = usize::try_from(left.range.end.get()).unwrap_or(usize::MAX);
        let end = usize::try_from(right.range.start.get()).unwrap_or(usize::MAX);
        self.source_text
            .get(start..end)
            .is_some_and(|text| text.contains('\n') || text.contains('\r'))
    }

    fn source_has_line_break_before_property(&self, expression: NodeId, name: NodeId) -> bool {
        self.source_property_separator(expression, name)
            .is_some_and(|separator| {
                let dot = separator.find('.').unwrap_or(separator.len());
                separator[..dot].contains(['\n', '\r'])
            })
    }

    fn source_has_line_break_after_property_dot(&self, expression: NodeId, name: NodeId) -> bool {
        self.source_property_separator(expression, name)
            .is_some_and(|separator| {
                let Some(dot) = separator.find('.') else {
                    return false;
                };
                separator[dot + 1..].contains(['\n', '\r'])
            })
    }

    fn source_property_separator(&self, expression: NodeId, name: NodeId) -> Option<&str> {
        let expression = self.arena.get(expression)?;
        let name = self.arena.get(name)?;
        let start = usize::try_from(expression.range.end.get()).unwrap_or(usize::MAX);
        let end = usize::try_from(name.range.start.get()).unwrap_or(usize::MAX);
        self.source_text.get(start..end)
    }

    fn write_source_quoted_string(&mut self, id: NodeId, text: &str) {
        let quote = self
            .arena
            .get(id)
            .and_then(|node| {
                let start = usize::try_from(node.range.start.get()).ok()?;
                self.source_text.as_bytes().get(start).copied()
            })
            .filter(|quote| matches!(quote, b'\'' | b'"'))
            .unwrap_or(b'"');
        write_quoted_with(&mut self.writer, text, char::from(quote));
    }

    fn arrow_uses_bare_parameter(&self, id: NodeId, data: &ts_ast::ArrowFunctionData) -> bool {
        if self.source_text.is_empty() || data.parameters.nodes.len() != 1 {
            return false;
        }
        let Some(node) = self.arena.get(id) else {
            return false;
        };
        let Some(arrow) = self.arena.get(data.equals_greater_than_token) else {
            return false;
        };
        let start = usize::try_from(node.range.start.get()).unwrap_or(usize::MAX);
        let end = usize::try_from(arrow.range.start.get()).unwrap_or(usize::MAX);
        self.source_text
            .get(start..end)
            .is_some_and(|parameters| !parameters.contains('('))
    }

    fn identifier_text(&self, id: NodeId) -> Result<&str, EmitError> {
        let node = self.node(id)?;
        if let NodeData::Identifier(data) = &node.data {
            Ok(&data.text)
        } else {
            Err(Self::unsupported(id, node.kind))
        }
    }

    fn is_constructor_name(&self, id: NodeId) -> bool {
        self.arena.get(id).is_some_and(
            |node| matches!(&node.data, NodeData::Identifier(data) if data.text == "constructor"),
        )
    }
}

fn semantic_jsx_children(arena: &NodeArena, children: &NodeList) -> Vec<NodeId> {
    children
        .nodes
        .iter()
        .copied()
        .filter(|child| match arena.get(*child).map(|node| &node.data) {
            Some(NodeData::JsxExpression(expression)) => expression.expression.is_some(),
            Some(NodeData::JsxText(text)) => !text.contains_only_trivia_white_spaces,
            Some(_) => true,
            None => false,
        })
        .collect()
}

fn normalize_jsx_text(text: &str) -> String {
    if !text.contains(['\n', '\r']) {
        return text.to_owned();
    }
    let lines = text.split('\n').collect::<Vec<_>>();
    let last = lines.len().saturating_sub(1);
    lines
        .into_iter()
        .enumerate()
        .map(|(index, line)| {
            let line = line.strip_suffix('\r').unwrap_or(line);
            if index == 0 {
                line.trim_end()
            } else if index == last {
                line.trim_start()
            } else {
                line.trim()
            }
        })
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>()
        .join(" ")
}

fn write_quoted(writer: &mut Writer, text: &str) {
    write_quoted_with(writer, text, '"');
}

fn write_quoted_with(writer: &mut Writer, text: &str, quote: char) {
    writer.write(&quote.to_string());
    for ch in text.chars() {
        match ch {
            '\\' => writer.write("\\\\"),
            ch if ch == quote => {
                writer.write("\\");
                writer.write(&ch.to_string());
            }
            '\n' => writer.write("\\n"),
            '\r' => writer.write("\\r"),
            '\t' => writer.write("\\t"),
            ch if ch.is_control() => writer.write(&format!("\\u{:04x}", u32::from(ch))),
            ch => writer.write(&ch.to_string()),
        }
    }
    writer.write(&quote.to_string());
}

fn write_template_text(writer: &mut Writer, text: &str) {
    for ch in text.chars() {
        match ch {
            '`' => writer.write("\\`"),
            '\\' => writer.write("\\\\"),
            ch => writer.write(&ch.to_string()),
        }
    }
}

fn operator_text(kind: SyntaxKind) -> Option<&'static str> {
    Some(match kind {
        SyntaxKind::CommaToken => ",",
        SyntaxKind::EqualsToken => "=",
        SyntaxKind::PlusEqualsToken => "+=",
        SyntaxKind::MinusEqualsToken => "-=",
        SyntaxKind::AsteriskEqualsToken => "*=",
        SyntaxKind::AsteriskAsteriskEqualsToken => "**=",
        SyntaxKind::SlashEqualsToken => "/=",
        SyntaxKind::PercentEqualsToken => "%=",
        SyntaxKind::LessThanLessThanEqualsToken => "<<=",
        SyntaxKind::GreaterThanGreaterThanEqualsToken => ">>=",
        SyntaxKind::GreaterThanGreaterThanGreaterThanEqualsToken => ">>>=",
        SyntaxKind::AmpersandEqualsToken => "&=",
        SyntaxKind::BarEqualsToken => "|=",
        SyntaxKind::CaretEqualsToken => "^=",
        SyntaxKind::BarBarEqualsToken => "||=",
        SyntaxKind::AmpersandAmpersandEqualsToken => "&&=",
        SyntaxKind::QuestionQuestionEqualsToken => "??=",
        SyntaxKind::PlusToken => "+",
        SyntaxKind::MinusToken => "-",
        SyntaxKind::PlusPlusToken => "++",
        SyntaxKind::MinusMinusToken => "--",
        SyntaxKind::ExclamationToken => "!",
        SyntaxKind::TildeToken => "~",
        SyntaxKind::TypeOfKeyword => "typeof ",
        SyntaxKind::VoidKeyword => "void ",
        SyntaxKind::DeleteKeyword => "delete ",
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
        SyntaxKind::AmpersandToken => "&",
        SyntaxKind::BarToken => "|",
        SyntaxKind::CaretToken => "^",
        SyntaxKind::AmpersandAmpersandToken => "&&",
        SyntaxKind::BarBarToken => "||",
        SyntaxKind::QuestionQuestionToken => "??",
        SyntaxKind::LessThanLessThanToken => "<<",
        SyntaxKind::GreaterThanGreaterThanToken => ">>",
        SyntaxKind::GreaterThanGreaterThanGreaterThanToken => ">>>",
        SyntaxKind::InKeyword => "in",
        SyntaxKind::InstanceOfKeyword => "instanceof",
        _ => return None,
    })
}

fn binary_precedence(kind: SyntaxKind) -> Option<(u8, bool)> {
    let result = match kind {
        SyntaxKind::CommaToken => (1, false),
        SyntaxKind::EqualsToken
        | SyntaxKind::PlusEqualsToken
        | SyntaxKind::MinusEqualsToken
        | SyntaxKind::AsteriskEqualsToken
        | SyntaxKind::AsteriskAsteriskEqualsToken
        | SyntaxKind::SlashEqualsToken
        | SyntaxKind::PercentEqualsToken
        | SyntaxKind::LessThanLessThanEqualsToken
        | SyntaxKind::GreaterThanGreaterThanEqualsToken
        | SyntaxKind::GreaterThanGreaterThanGreaterThanEqualsToken
        | SyntaxKind::AmpersandEqualsToken
        | SyntaxKind::BarEqualsToken
        | SyntaxKind::CaretEqualsToken
        | SyntaxKind::BarBarEqualsToken
        | SyntaxKind::AmpersandAmpersandEqualsToken
        | SyntaxKind::QuestionQuestionEqualsToken => (2, true),
        SyntaxKind::QuestionQuestionToken => (3, false),
        SyntaxKind::BarBarToken => (4, false),
        SyntaxKind::AmpersandAmpersandToken => (5, false),
        SyntaxKind::BarToken => (6, false),
        SyntaxKind::CaretToken => (7, false),
        SyntaxKind::AmpersandToken => (8, false),
        SyntaxKind::EqualsEqualsToken
        | SyntaxKind::ExclamationEqualsToken
        | SyntaxKind::EqualsEqualsEqualsToken
        | SyntaxKind::ExclamationEqualsEqualsToken => (9, false),
        SyntaxKind::LessThanToken
        | SyntaxKind::LessThanEqualsToken
        | SyntaxKind::GreaterThanToken
        | SyntaxKind::GreaterThanEqualsToken
        | SyntaxKind::InKeyword
        | SyntaxKind::InstanceOfKeyword => (10, false),
        SyntaxKind::LessThanLessThanToken
        | SyntaxKind::GreaterThanGreaterThanToken
        | SyntaxKind::GreaterThanGreaterThanGreaterThanToken => (11, false),
        SyntaxKind::PlusToken | SyntaxKind::MinusToken => (12, false),
        SyntaxKind::AsteriskToken | SyntaxKind::SlashToken | SyntaxKind::PercentToken => {
            (13, false)
        }
        SyntaxKind::AsteriskAsteriskToken => (14, true),
        _ => return None,
    };
    Some(result)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use ts_ast::NodeData;
    use ts_binder::bind_source_file;
    use ts_options::{JsxEmit, ModuleKind, PrinterSettings, ScriptTarget};
    use ts_parser::{parse_jsx_source_file, parse_source_file};

    use super::{
        AmdDependency, EmitConstantValue, EmitContext, emit_declaration_file,
        emit_declaration_file_with_reachability, emit_source_file, emit_source_file_with_context,
        emit_source_file_with_settings, original_position,
    };

    fn emit(source: &str) -> String {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        emit_source_file(&parsed.arena, parsed.source_file)
            .unwrap()
            .code
    }

    fn emit_with(source: &str, target: ScriptTarget, module: ModuleKind) -> super::EmitResult {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        emit_source_file_with_settings(
            &parsed.arena,
            parsed.source_file,
            "input.ts",
            source,
            PrinterSettings {
                always_strict: false,
                target,
                module,
                jsx: JsxEmit::Preserve,
                emit_javascript: true,
                emit_declarations: false,
                source_map: true,
                inline_source_map: false,
            },
        )
        .unwrap()
    }

    fn emit_amd(source: &str) -> super::EmitResult {
        let parsed = parse_source_file(source);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let dependencies = parsed
            .amd_dependencies
            .iter()
            .map(|dependency| AmdDependency {
                path: &dependency.path,
                name: dependency.name.as_deref(),
                comment_start: dependency.range.start.get(),
                comment_end: dependency.range.end.get(),
            })
            .collect::<Vec<_>>();
        let enum_values = BTreeMap::new();
        emit_source_file_with_context(
            &parsed.arena,
            parsed.source_file,
            "input.ts",
            source,
            PrinterSettings {
                always_strict: false,
                target: ScriptTarget::Es2015,
                module: ModuleKind::Amd,
                jsx: JsxEmit::Preserve,
                emit_javascript: true,
                emit_declarations: false,
                source_map: true,
                inline_source_map: false,
            },
            &EmitContext {
                bindings: &bindings,
                amd_module_name: parsed.amd_module_name.as_deref(),
                amd_dependencies: &dependencies,
                enum_member_values: &enum_values,
                enum_access_values: &enum_values,
                preserve_const_enums: true,
                inline_const_enums: false,
            },
        )
        .unwrap()
    }

    fn emit_jsx(source: &str, jsx: JsxEmit) -> String {
        let parsed = parse_jsx_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        emit_source_file_with_settings(
            &parsed.arena,
            parsed.source_file,
            "input.tsx",
            source,
            PrinterSettings {
                always_strict: false,
                target: ScriptTarget::EsNext,
                module: ModuleKind::EsNext,
                jsx,
                emit_javascript: true,
                emit_declarations: false,
                source_map: false,
                inline_source_map: false,
            },
        )
        .unwrap()
        .code
    }

    #[test]
    fn erases_types_and_prints_declarations() {
        assert_eq!(
            emit(
                "interface Shape { area(): number; } type Id<T> = T; const answer: number = 42; function add<T>(a: number, b?: number): number { return a + b; }"
            ),
            "const answer = 42;\nfunction add(a, b) {\n    return a + b;\n}\n"
        );
    }

    #[test]
    fn prints_classes_and_control_flow() {
        assert_eq!(
            emit(
                "class Counter extends Base implements Shape { value: number = 0; inc(step: number) { value = value + step; } } let i: number = 0; while (i < 2) { i = i + 1; } for (let j: number = 0; j < 2; j = j + 1) { i = i + j; }"
            ),
            "class Counter extends Base {\n    value = 0;\n    inc(step) {\n        value = value + step;\n    }\n}\nlet i = 0;\nwhile (i < 2) {\n    i = i + 1;\n}\nfor (let j = 0; j < 2; j = j + 1) {\n    i = i + j;\n}\n"
        );
    }

    #[test]
    fn emits_qualified_names_in_class_heritage_expressions() {
        let source = "class VisualizationModel extends Backbone.Model {}";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::EsNext).code,
            "class VisualizationModel extends Backbone.Model {\n}\n"
        );
        let es5 = emit_with(source, ScriptTarget::Es5, ModuleKind::EsNext).code;
        assert!(es5.contains("}(Backbone.Model));"), "{es5}");
    }

    #[test]
    fn prints_switch_try_and_loop_control_statements() {
        assert_eq!(
            emit(
                "let i = 0; do { i++; if (i === 1) continue; } while (i < 2); switch (i) { case 2: i = 3; break; default: i = 4; } try { throw i; } catch (error: unknown) { i = 5; } finally { i = 6; }"
            ),
            "let i = 0;\ndo {\n    i++;\n    if (i === 1)\n        continue;\n} while (i < 2);\nswitch (i) {\n    case 2:\n        i = 3;\n        break;\n    default:\n        i = 4;\n}\ntry {\n    throw i;\n} catch (error) {\n    i = 5;\n} finally {\n    i = 6;\n}\n"
        );
    }

    #[test]
    fn prints_labeled_debugger_and_with_statements() {
        assert_eq!(
            emit("outer: while (value) { debugger; break outer; } with (obj) value;"),
            "outer: while (value) {\n    debugger;\n    break outer;\n}\nwith (obj)\n    value;\n"
        );
    }

    #[test]
    fn prints_modules_expressions_and_templates() {
        assert_eq!(
            emit(
                "import main, { read as load, write } from 'pkg'; import 'side'; const value = load({ x: 1 }, [2, 3]); const message = `value=${value}`; export { value as result }; export * from 'other'; export default value;"
            ),
            "import main, { read as load, write } from \"pkg\";\nimport \"side\";\nconst value = load({ x: 1 }, [2, 3]);\nconst message = `value=${value}`;\nexport { value as result };\nexport * from \"other\";\nexport default value;\n"
        );
    }

    #[test]
    fn preserves_and_transforms_jsx_elements() {
        let source = "const view = <Panel enabled {...props} title='hello'><span>{value}</span><Icon /></Panel>;";
        assert_eq!(
            emit_jsx(source, JsxEmit::Preserve),
            "const view = <Panel enabled {...props} title=\"hello\"><span>{value}</span><Icon /></Panel>;\n"
        );
        assert_eq!(
            emit_jsx(source, JsxEmit::React),
            "const view = React.createElement(Panel, {enabled: true, ...props, title: \"hello\"}, React.createElement(\"span\", null, value), React.createElement(Icon, null));\n"
        );
        let fragment = "const view = <><span />{value}</>;";
        assert_eq!(
            emit_jsx(fragment, JsxEmit::Preserve),
            "const view = <><span />{value}</>;\n"
        );
        assert_eq!(
            emit_jsx(fragment, JsxEmit::React),
            "const view = React.createElement(React.Fragment, null, React.createElement(\"span\", null), value);\n"
        );
    }

    #[test]
    fn emits_automatic_jsx_runtime_calls() {
        let source = "const view = <><div id='root'>hello <Widget /></div><UI.Button>{value}</UI.Button></>;";
        assert_eq!(
            emit_jsx(source, JsxEmit::ReactJsx),
            "import { jsx as _jsx, jsxs as _jsxs, Fragment as _Fragment } from \"react/jsx-runtime\";\nconst view = _jsxs(_Fragment, { children: [_jsxs(\"div\", { id: \"root\", children: [\"hello \", _jsx(Widget, {})] }), _jsx(UI.Button, { children: value })] });\n"
        );
        assert_eq!(
            emit_jsx(source, JsxEmit::ReactJsxDev),
            "import { jsxDEV as _jsxDEV, Fragment as _Fragment } from \"react/jsx-dev-runtime\";\nconst _jsxFileName = \"input.tsx\";\nconst view = _jsxDEV(_Fragment, { children: [_jsxDEV(\"div\", { id: \"root\", children: [\"hello \", _jsxDEV(Widget, {}, void 0, false, { fileName: _jsxFileName, lineNumber: 1, columnNumber: 37 }, this)] }, void 0, true, { fileName: _jsxFileName, lineNumber: 1, columnNumber: 16 }, this), _jsxDEV(UI.Button, { children: value }, void 0, false, { fileName: _jsxFileName, lineNumber: 1, columnNumber: 53 }, this)] }, void 0, true, { fileName: _jsxFileName, lineNumber: 1, columnNumber: 14 }, this);\n"
        );
    }

    #[test]
    fn automatic_jsx_extracts_key_and_uses_single_child_props() {
        let source = "const item = <Component key='item' value={count}>text</Component>;";
        assert_eq!(
            emit_jsx(source, JsxEmit::ReactJsx),
            "import { jsx as _jsx } from \"react/jsx-runtime\";\nconst item = _jsx(Component, { value: count, children: \"text\" }, \"item\");\n"
        );
    }

    #[test]
    fn preserves_regular_expression_literals() {
        assert_eq!(
            emit("const first = /a[b\\/]c+/giu; const second = /=foo/;"),
            "const first = /a[b\\/]c+/giu;\nconst second = /=foo/;\n"
        );
    }

    #[test]
    fn preserves_function_expressions_and_erases_their_types() {
        assert_eq!(
            emit(
                "const callback = function (value: number): number { return value; }; const result = (function* named() { yield 1; })();"
            ),
            "const callback = function (value) { return value; };\nconst result = (function* named() {\n    yield 1;\n})();\n"
        );
    }

    #[test]
    fn preserves_compact_and_multiline_function_bodies() {
        let source = "function compact() { return 1; }\nfunction multiline() {\n}\nclass Box { constructor(public value: number) {} set item(next) { next = 1; } }";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::CommonJs).code,
            "function compact() { return 1; }\nfunction multiline() {\n}\nclass Box {\n    constructor(value) {\n        this.value = value;\n    }\n    set item(next) { next = 1; }\n}\n"
        );
    }

    #[test]
    fn emits_and_recovers_object_literal_accessors() {
        let source = "var value = { get item(), set item(next: number) };";
        let parsed = parse_source_file(source);
        assert_eq!(parsed.diagnostics.len(), 2, "{:?}", parsed.diagnostics);
        assert!(
            parsed
                .diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code == Some(1005))
        );
        assert_eq!(
            emit_source_file(&parsed.arena, parsed.source_file)
                .unwrap()
                .code,
            "var value = { get item() { }, set item(next) { } };\n"
        );
    }

    #[test]
    fn emits_native_and_downlevel_class_accessors() {
        let source =
            "class C { get X() { return 1; } set X(v = 0) { } static get Y() { return 2; } }";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::EsNext).code,
            "class C {\n    get X() { return 1; }\n    set X(v = 0) { }\n    static get Y() { return 2; }\n}\n"
        );
        assert_eq!(
            emit_with(source, ScriptTarget::Es5, ModuleKind::EsNext).code,
            "var C = /** @class */ (function () {\n    function C() {\n    }\n    Object.defineProperty(C.prototype, \"X\", {\n        get: function () { return 1; },\n        set: function (v) {\n            if (v === void 0) { v = 0; }\n        },\n        enumerable: false,\n        configurable: true\n    });\n    Object.defineProperty(C, \"Y\", {\n        get: function () { return 2; },\n        enumerable: false,\n        configurable: true\n    });\n    return C;\n}());\n"
        );
    }

    #[test]
    fn erases_abstract_members_and_preserves_concrete_accessor_halves() {
        let source = "abstract class A { abstract prop: string; abstract get erased(): number; abstract get mixed(): number; set mixed(v: number) {} get recovered(): number; get paired() { return 1; } abstract set paired(v: number); }";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::EsNext).code,
            "class A {\n    set mixed(v) { }\n    get recovered() { }\n    get paired() { return 1; }\n}\n"
        );
        assert_eq!(
            emit_with(source, ScriptTarget::Es5, ModuleKind::EsNext).code,
            "var A = /** @class */ (function () {\n    function A() {\n    }\n    Object.defineProperty(A.prototype, \"mixed\", {\n        set: function (v) { },\n        enumerable: false,\n        configurable: true\n    });\n    Object.defineProperty(A.prototype, \"recovered\", {\n        get: function () { },\n        enumerable: false,\n        configurable: true\n    });\n    Object.defineProperty(A.prototype, \"paired\", {\n        get: function () { return 1; },\n        enumerable: false,\n        configurable: true\n    });\n    return A;\n}());\n"
        );
    }

    #[test]
    fn erases_this_parameters_and_redundant_type_assertion_parentheses() {
        assert_eq!(
            emit(
                "function read(this: Context,\n              candidate: Symbol,\n              value: number) { if (!candidate) return; return (value as NumberBox).amount; }"
            ),
            "function read(candidate, value) {\n    if (!candidate)\n        return;\n    return value.amount;\n}\n"
        );
    }

    #[test]
    fn preserves_multiline_call_chain_layout() {
        let source = "function read() { let values = source.first()\n    .concat(source.second())\n    .concat(source.third()); }";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::EsNext).code,
            "function read() {\n    let values = source.first()\n        .concat(source.second())\n        .concat(source.third());\n}\n"
        );
    }

    #[test]
    fn places_else_on_a_new_line() {
        assert_eq!(
            emit("if (value) { read(); } else { write(); }"),
            "if (value) {\n    read();\n}\nelse {\n    write();\n}\n"
        );
    }

    #[test]
    fn emits_enums_deterministically() {
        assert_eq!(
            emit("enum Color { Red, Green = 4, Blue, Label = 'blue' }"),
            "var Color;\n(function (Color) {\n    Color[Color[\"Red\"] = 0] = \"Red\";\n    Color[Color[\"Green\"] = 4] = \"Green\";\n    Color[Color[\"Blue\"] = 5] = \"Blue\";\n    Color[\"Label\"] = \"blue\";\n})(Color || (Color = {}));\n"
        );
    }

    #[test]
    fn inlines_negative_const_enum_values_with_expression_precedence() {
        let source = concat!(
            "const enum E { A = -1 }\n",
            "const product = E.A * 2;\n",
            "const text = E.A.toString();\n",
        );
        let parsed = parse_source_file(source);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let accesses = parsed
            .arena
            .iter()
            .filter_map(|(id, node)| {
                let NodeData::PropertyAccessExpression(access) = &node.data else {
                    return None;
                };
                (super::declaration_name_text(&parsed.arena, access.name) == Some("A"))
                    .then_some((id, EmitConstantValue::Number(-1.0)))
            })
            .collect::<BTreeMap<_, _>>();
        let member_values = BTreeMap::new();
        let emitted = emit_source_file_with_context(
            &parsed.arena,
            parsed.source_file,
            "input.ts",
            source,
            PrinterSettings {
                always_strict: false,
                target: ScriptTarget::Es2015,
                module: ModuleKind::EsNext,
                jsx: JsxEmit::Preserve,
                emit_javascript: true,
                emit_declarations: false,
                source_map: false,
                inline_source_map: false,
            },
            &EmitContext {
                bindings: &bindings,
                amd_module_name: None,
                amd_dependencies: &[],
                enum_member_values: &member_values,
                enum_access_values: &accesses,
                preserve_const_enums: false,
                inline_const_enums: true,
            },
        )
        .unwrap();
        assert_eq!(
            emitted.code,
            concat!(
                "const product = -1 /* E.A */ * 2;\n",
                "const text = (-1 /* E.A */).toString();\n",
            )
        );
    }

    #[test]
    fn emits_global_namespace_iife_and_erases_ambient_namespaces() {
        assert_eq!(
            emit_with(
                "namespace M { function foo(); }",
                ScriptTarget::Es2015,
                ModuleKind::EsNext,
            )
            .code,
            "var M;\n(function (M) {\n})(M || (M = {}));\n"
        );
        assert_eq!(
            emit_with(
                "declare namespace Types { function read(): string; }",
                ScriptTarget::Es2015,
                ModuleKind::EsNext,
            )
            .code,
            ""
        );
    }

    #[test]
    fn emits_exported_namespace_class_for_es2015_and_es5() {
        let source = r"
            namespace C {
                export class Name {
                    static funcData = A.AA.func();
                    static someConst = A.AA.foo;
                    constructor(parameters) {}
                }
            }
        ";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::Amd).code,
            "var C;\n(function (C) {\n    class Name {\n        constructor(parameters) { }\n    }\n    Name.funcData = A.AA.func();\n    Name.someConst = A.AA.foo;\n    C.Name = Name;\n})(C || (C = {}));\n"
        );
        assert_eq!(
            emit_with(source, ScriptTarget::Es5, ModuleKind::Amd).code,
            "var C;\n(function (C) {\n    var Name = /** @class */ (function () {\n        function Name(parameters) {\n        }\n        Name.funcData = A.AA.func();\n        Name.someConst = A.AA.foo;\n        return Name;\n    }());\n    C.Name = Name;\n})(C || (C = {}));\n"
        );
    }

    #[test]
    fn emits_named_amd_modules_and_returns_export_equals() {
        let first = concat!(
            "///<amd-module name='NamedModule'/>\n",
            "class Foo {\n",
            "    x: number;\n",
            "    constructor() {\n",
            "        this.x = 5;\n",
            "    }\n",
            "}\n",
            "export = Foo;\n",
        );
        assert_eq!(
            emit_amd(first).code,
            concat!(
                "define(\"NamedModule\", [\"require\", \"exports\"], function (require, exports) {\n",
                "    \"use strict\";\n",
                "    ///<amd-module name='NamedModule'/>\n",
                "    class Foo {\n",
                "        constructor() {\n",
                "            this.x = 5;\n",
                "        }\n",
                "    }\n",
                "    return Foo;\n",
                "});\n",
            )
        );

        let duplicate = concat!(
            "///<amd-module name='FirstModuleName'/>\n",
            "///<amd-module name='SecondModuleName'/>\n",
            "class Foo {\n",
            "    x: number;\n",
            "    constructor() {\n",
            "        this.x = 5;\n",
            "    }\n",
            "}\n",
            "export = Foo;\n",
        );
        assert_eq!(
            emit_amd(duplicate).code,
            concat!(
                "define(\"SecondModuleName\", [\"require\", \"exports\"], function (require, exports) {\n",
                "    \"use strict\";\n",
                "    ///<amd-module name='FirstModuleName'/>\n",
                "    ///<amd-module name='SecondModuleName'/>\n",
                "    class Foo {\n",
                "        constructor() {\n",
                "            this.x = 5;\n",
                "        }\n",
                "    }\n",
                "    return Foo;\n",
                "});\n",
            )
        );
    }

    #[test]
    fn orders_amd_dependency_pragmas_around_import_equals() {
        let source = concat!(
            "///<amd-dependency path='bar' name='b'/>\n",
            "///<amd-dependency path='foo'/>\n",
            "///<amd-dependency path='goo' name='c'/>\n",
            "\n",
            "import m1 = require(\"m2\")\n",
            "m1.f();",
        );
        assert_eq!(
            emit_amd(source).code,
            concat!(
                "///<amd-dependency path='bar' name='b'/>\n",
                "///<amd-dependency path='foo'/>\n",
                "///<amd-dependency path='goo' name='c'/>\n",
                "define([\"require\", \"exports\", \"bar\", \"goo\", \"m2\", \"foo\"], function (require, exports, b, c, m1) {\n",
                "    \"use strict\";\n",
                "    Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "    m1.f();\n",
                "});\n",
            )
        );
    }

    #[test]
    fn appends_unnamed_amd_dependency_after_import_equals() {
        let source = concat!(
            "///<amd-dependency path='bar'/>\n",
            "\n",
            "import m1 = require(\"m2\")\n",
            "m1.f();",
        );
        assert_eq!(
            emit_amd(source).code,
            concat!(
                "///<amd-dependency path='bar'/>\n",
                "define([\"require\", \"exports\", \"m2\", \"bar\"], function (require, exports, m1) {\n",
                "    \"use strict\";\n",
                "    Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "    m1.f();\n",
                "});\n",
            )
        );
    }

    #[test]
    fn prepends_named_amd_dependency_before_import_equals() {
        let source = concat!(
            "///<amd-dependency path='bar' name='b'/>\n",
            "\n",
            "import m1 = require(\"m2\")\n",
            "m1.f();",
        );
        assert_eq!(
            emit_amd(source).code,
            concat!(
                "///<amd-dependency path='bar' name='b'/>\n",
                "define([\"require\", \"exports\", \"bar\", \"m2\"], function (require, exports, b, m1) {\n",
                "    \"use strict\";\n",
                "    Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "    m1.f();\n",
                "});\n",
            )
        );
    }

    #[test]
    fn emits_system_module_for_statements_with_omitted_clauses() {
        let source = r"
            export { };
            let i = 0;
            let limit = 10;
            for (; i < limit; ++i) { break; }
            for (; ; ++i) { break; }
            for (; ;) { break; }
        ";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::System).code,
            concat!(
                "System.register([], function (exports_1, context_1) {\n",
                "    \"use strict\";\n",
                "    var i, limit;\n",
                "    var __moduleName = context_1 && context_1.id;\n",
                "    return {\n",
                "        setters: [],\n",
                "        execute: function () {\n",
                "            i = 0;\n",
                "            limit = 10;\n",
                "            for (; i < limit; ++i) {\n",
                "                break;\n",
                "            }\n",
                "            for (;; ++i) {\n",
                "                break;\n",
                "            }\n",
                "            for (;;) {\n",
                "                break;\n",
                "            }\n",
                "        }\n",
                "    };\n",
                "});\n",
            )
        );
    }

    #[test]
    fn emits_system_import_equals_aliases() {
        let source = r#"
            import alias = require("foo");
            import cls = alias.Class;
            export import cls2 = alias.Class;
            let x = new alias.Class();
            let y = new cls();
            let z = new cls2();
            namespace M {
                export import cls = alias.Class;
                let x = new alias.Class();
                let y = new cls();
                let z = new cls2();
            }
        "#;
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::System).code,
            concat!(
                "System.register([\"foo\"], function (exports_1, context_1) {\n",
                "    \"use strict\";\n",
                "    var alias, cls, cls2, x, y, z, M;\n",
                "    var __moduleName = context_1 && context_1.id;\n",
                "    return {\n",
                "        setters: [\n",
                "            function (alias_1) {\n",
                "                alias = alias_1;\n",
                "            }\n",
                "        ],\n",
                "        execute: function () {\n",
                "            cls = alias.Class;\n",
                "            exports_1(\"cls2\", cls2 = alias.Class);\n",
                "            x = new alias.Class();\n",
                "            y = new cls();\n",
                "            z = new cls2();\n",
                "            (function (M) {\n",
                "                M.cls = alias.Class;\n",
                "                let x = new alias.Class();\n",
                "                let y = new M.cls();\n",
                "                let z = new cls2();\n",
                "            })(M || (M = {}));\n",
                "        }\n",
                "    };\n",
                "});\n",
            )
        );
    }

    #[test]
    fn emits_system_named_import_aliases_through_module_storage() {
        let source = r#"
            import { alias } from "foo";
            import cls = alias.Class;
            export import cls2 = alias.Class;
            let x = new alias.Class();
            let y = new cls();
            let z = new cls2();
            namespace M {
                export import cls = alias.Class;
                let x = new alias.Class();
                let y = new cls();
                let z = new cls2();
            }
        "#;
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::System).code,
            concat!(
                "System.register([\"foo\"], function (exports_1, context_1) {\n",
                "    \"use strict\";\n",
                "    var foo_1, cls, cls2, x, y, z, M;\n",
                "    var __moduleName = context_1 && context_1.id;\n",
                "    return {\n",
                "        setters: [\n",
                "            function (foo_1_1) {\n",
                "                foo_1 = foo_1_1;\n",
                "            }\n",
                "        ],\n",
                "        execute: function () {\n",
                "            cls = foo_1.alias.Class;\n",
                "            exports_1(\"cls2\", cls2 = foo_1.alias.Class);\n",
                "            x = new foo_1.alias.Class();\n",
                "            y = new cls();\n",
                "            z = new cls2();\n",
                "            (function (M) {\n",
                "                M.cls = foo_1.alias.Class;\n",
                "                let x = new foo_1.alias.Class();\n",
                "                let y = new M.cls();\n",
                "                let z = new cls2();\n",
                "            })(M || (M = {}));\n",
                "        }\n",
                "    };\n",
                "});\n",
            )
        );
    }

    #[test]
    fn downlevels_es2015_and_es2020_expressions_for_es5() {
        let result = emit_with(
            "const greet = (name: string) => `hi ${name}`; let result = value ?? fallback;",
            ScriptTarget::Es5,
            ModuleKind::EsNext,
        );
        assert_eq!(
            result.code,
            "var greet = function (name) { return \"hi \" + name + \"\"; };\nvar result = value !== null && value !== void 0 ? value : fallback;\n"
        );
    }

    #[test]
    fn preserves_parsed_modern_syntax_for_esnext() {
        assert_eq!(
            emit(
                "async function* stream(source) { await source?.next?.(); yield* source?.[0]!; } class Box { #value = 1; static count = 0; *values() { yield this.#value; } async read() { return await this.#value; } static { this.count++; } } for await (const item of items) { item; } const { first, ...rest } = input; const [head, ...tail] = items; const copy = { first, ...rest, async run() { await task; }, *iter() { yield 1; } }; const values = [0, ...items]; const typed = (value as number)! satisfies number; const run = async (value) => await value; import data from 'pkg' with { type: 'json' }; export { data } from 'pkg' with { type: 'json' };"
            ),
            "async function* stream(source) {\n    await source?.next?.();\n    yield* source?.[0];\n}\nclass Box {\n    #value = 1;\n    static count = 0;\n    *values() {\n        yield this.#value;\n    }\n    async read() {\n        return await this.#value;\n    }\n    static {\n        this.count++;\n    }\n}\nfor await (const item of items) {\n    item;\n}\nconst { first, ...rest } = input;\nconst [head, ...tail] = items;\nconst copy = { first, ...rest, async run() {\n    await task;\n}, *iter() {\n    yield 1;\n} };\nconst values = [0, ...items];\nconst typed = (value);\nconst run = async (value) => await value;\nimport data from \"pkg\" with { type: \"json\" };\nexport { data } from \"pkg\" with { type: \"json\" };\n"
        );
    }

    #[test]
    fn downlevels_optional_element_and_spread_for_es5() {
        let result = emit_with(
            "const value = source?.[key]; const merged = { a: 1, ...extra, b: 2 }; const list = [0, ...items, 3];",
            ScriptTarget::Es5,
            ModuleKind::EsNext,
        );
        assert_eq!(
            result.code,
            "var value = source === null || source === void 0 ? void 0 : source[key];\nvar merged = Object.assign({}, { a: 1 }, extra, { b: 2 });\nvar list = [].concat([], [0], items, [3]);\n"
        );
    }

    #[test]
    fn downlevels_es5_classes_with_fields_methods_and_inheritance() {
        let result = emit_with(
            "class Point { x = 1; static origin = 0; constructor(y: number) { this.y = y; } move(d: number) { this.x = this.x + d; } static make() { return new Point(0); } } class ColoredPoint extends Point { color = 'red'; constructor(y: number) { super(y); this.color = 'blue'; } paint() { return this.color; } }",
            ScriptTarget::Es5,
            ModuleKind::EsNext,
        );
        assert_eq!(
            result.code,
            "var __extends = (this && this.__extends) || (function () {\n    var extendStatics = function (d, b) {\n        extendStatics = Object.setPrototypeOf ||\n            ({ __proto__: [] } instanceof Array && function (d, b) { d.__proto__ = b; }) ||\n            function (d, b) { for (var p in b) if (Object.prototype.hasOwnProperty.call(b, p)) d[p] = b[p]; };\n        return extendStatics(d, b);\n    };\n    return function (d, b) {\n        if (typeof b !== \"function\" && b !== null)\n            throw new TypeError(\"Class extends value \" + String(b) + \" is not a constructor or null\");\n        extendStatics(d, b);\n        function __() { this.constructor = d; }\n        d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());\n    };\n})();\nvar Point = /** @class */ (function () {\n    function Point(y) {\n        this.x = 1;\n        this.y = y;\n    }\n    Point.prototype.move = function (d) {\n        this.x = this.x + d;\n    };\n    Point.make = function () {\n        return new Point(0);\n    };\n    Point.origin = 0;\n    return Point;\n}());\nvar ColoredPoint = /** @class */ (function (_super) {\n    __extends(ColoredPoint, _super);\n    function ColoredPoint(y) {\n        var _this = _super.call(this, y) || this;\n        _this.color = 'red';\n        _this.color = 'blue';\n        return _this;\n    }\n    ColoredPoint.prototype.paint = function () {\n        return this.color;\n    };\n    return ColoredPoint;\n}(Point));\n"
        );
    }

    #[test]
    fn lowers_fields_but_preserves_class_syntax_before_es2022() {
        let result = emit_with(
            "class Box { value = 1; read() { return this.value; } }",
            ScriptTarget::Es2015,
            ModuleKind::EsNext,
        );
        assert_eq!(
            result.code,
            "class Box {\n    constructor() {\n        this.value = 1;\n    }\n    read() {\n        return this.value;\n    }\n}\n"
        );
    }

    #[test]
    fn lowers_derived_and_static_fields_before_es2022() {
        let result = emit_with(
            "class Box extends Base { value = 1; static count = 2; constructor(name: string) { super(name); this.ready = true; } }",
            ScriptTarget::Es2021,
            ModuleKind::EsNext,
        );
        assert_eq!(
            result.code,
            "class Box extends Base {\n    constructor(name) {\n        super(name);\n        this.value = 1;\n        this.ready = true;\n    }\n}\nBox.count = 2;\n"
        );
    }

    #[test]
    fn preserves_native_fields_for_es2022_and_newer() {
        let result = emit_with(
            "class Box { value = 1; static count = 2; }",
            ScriptTarget::Es2022,
            ModuleKind::EsNext,
        );
        assert_eq!(
            result.code,
            "class Box {\n    value = 1;\n    static count = 2;\n}\n"
        );
    }

    #[test]
    fn matches_2d_arrays_strict_and_class_field_shape() {
        let source = r"class Cell {}
class Ship {
    isSunk: boolean = false;
}
class Board {
    ships: Ship[] = [];
    cells: Cell[] = [];
}";
        let parsed = parse_source_file(source);
        let result = emit_source_file_with_settings(
            &parsed.arena,
            parsed.source_file,
            "input.ts",
            source,
            PrinterSettings {
                always_strict: true,
                target: ScriptTarget::Es2015,
                module: ModuleKind::EsNext,
                jsx: JsxEmit::Preserve,
                emit_javascript: true,
                emit_declarations: false,
                source_map: false,
                inline_source_map: false,
            },
        )
        .unwrap();
        assert_eq!(
            result.code,
            "\"use strict\";\nclass Cell {\n}\nclass Ship {\n    constructor() {\n        this.isSunk = false;\n    }\n}\nclass Board {\n    constructor() {\n        this.ships = [];\n        this.cells = [];\n    }\n}\n"
        );
    }

    #[test]
    fn matches_class_declaration_overload_erasure_baseline() {
        let source = "class C { constructor(); foo(); }";
        let parsed = parse_source_file(source);
        let result = emit_source_file_with_settings(
            &parsed.arena,
            parsed.source_file,
            "input.ts",
            source,
            PrinterSettings {
                always_strict: true,
                target: ScriptTarget::Es2015,
                module: ModuleKind::EsNext,
                jsx: JsxEmit::Preserve,
                emit_javascript: true,
                emit_declarations: false,
                source_map: false,
                inline_source_map: false,
            },
        )
        .unwrap();
        assert_eq!(result.code, "\"use strict\";\nclass C {\n}\n");
    }

    #[test]
    fn preserves_only_the_implemented_constructor_trailing_comment() {
        let result = emit_with(
            concat!(
                "class C1 {\n",
                " constructor(public p1: string); // ERROR\n",
                " constructor(private p2: number); // ERROR\n",
                " constructor(public p3: any) {} // OK\n",
                "}",
            ),
            ScriptTarget::Es2015,
            ModuleKind::EsNext,
        );
        assert_eq!(
            result.code,
            concat!(
                "class C1 {\n",
                "    constructor(p3) {\n",
                "        this.p3 = p3;\n",
                "    } // OK\n",
                "}\n",
            )
        );
    }

    #[test]
    fn keeps_leading_comments_after_erased_overloads() {
        let result = emit_with(
            concat!(
                "class C {\n",
                " method(value: string): void; // erased overload\n",
                " // implementation comment\n",
                " method(value: string) {}\n",
                "}\n",
            ),
            ScriptTarget::Es2015,
            ModuleKind::EsNext,
        );
        assert_eq!(
            result.code,
            concat!(
                "class C {\n",
                "    // implementation comment\n",
                "    method(value) { }\n",
                "}\n",
            )
        );
    }

    #[test]
    fn preserves_immediate_trailing_statement_comments() {
        let result = emit_with(
            concat!(
                "import moduleA = require(\"./aliasAssignments_moduleA\");\n",
                "var x = moduleA;\n",
                "x = 1; // Should be error\n",
                "var y = 1;\n",
                "y = moduleA; // should be error\n",
            ),
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert_eq!(
            result.code,
            concat!(
                "\"use strict\";\n",
                "Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "const moduleA = require(\"./aliasAssignments_moduleA\");\n",
                "var x = moduleA;\n",
                "x = 1; // Should be error\n",
                "var y = 1;\n",
                "y = moduleA; // should be error\n",
            )
        );
    }

    #[test]
    fn preserves_constructor_body_comments_around_lowered_fields() {
        let source = concat!(
            "abstract class A {\n",
            " other = this.prop;\n",
            " constructor() {\n",
            "  this.cb(); // OK\n",
            "  const inner = () => this.prop; // nested reference\n",
            " }\n",
            " abstract prop: string;\n",
            " abstract cb(): void;\n",
            "}\n",
        );
        let result = emit_with(source, ScriptTarget::Es2015, ModuleKind::EsNext);
        assert_eq!(
            result.code,
            concat!(
                "class A {\n",
                "    constructor() {\n",
                "        this.other = this.prop;\n",
                "        this.cb(); // OK\n",
                "        const inner = () => this.prop; // nested reference\n",
                "    }\n",
                "}\n",
            )
        );
        let downlevel = emit_with(source, ScriptTarget::Es5, ModuleKind::EsNext).code;
        assert!(downlevel.contains("this.cb(); // OK"), "{downlevel}");
        assert!(downlevel.contains("// nested reference"), "{downlevel}");
    }

    #[test]
    fn preserves_trailing_comments_across_erased_abstract_type_statements() {
        let source = concat!(
            "class ConcreteA {}\n",
            "class ConcreteB {}\n",
            "abstract class AbstractA { a: string; }\n",
            "abstract class AbstractB { b: string; }\n",
            "type Abstracts = typeof AbstractA | typeof AbstractB;\n",
            "declare const cls1: Abstracts;\n",
            "new cls1(); // should error\n",
            "[ConcreteA, AbstractA].map(cls => new cls()); // should error\n",
            "[ConcreteA, ConcreteB].map(cls => new cls()); // should work\n",
        );
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::EsNext).code,
            concat!(
                "class ConcreteA {\n",
                "}\n",
                "class ConcreteB {\n",
                "}\n",
                "class AbstractA {\n",
                "}\n",
                "class AbstractB {\n",
                "}\n",
                "new cls1(); // should error\n",
                "[ConcreteA, AbstractA].map(cls => new cls()); // should error\n",
                "[ConcreteA, ConcreteB].map(cls => new cls()); // should work\n",
            )
        );
    }

    #[test]
    fn does_not_duplicate_an_existing_use_strict_directive() {
        let source = "\"use strict\"; const value = 1;";
        let parsed = parse_source_file(source);
        let result = emit_source_file_with_settings(
            &parsed.arena,
            parsed.source_file,
            "input.ts",
            source,
            PrinterSettings {
                always_strict: true,
                target: ScriptTarget::Es2015,
                module: ModuleKind::EsNext,
                jsx: JsxEmit::Preserve,
                emit_javascript: true,
                emit_declarations: false,
                source_map: false,
                inline_source_map: false,
            },
        )
        .unwrap();
        assert_eq!(result.code, "\"use strict\";\nconst value = 1;\n");
    }

    #[test]
    fn preserves_export_modifiers_for_es_modules() {
        let result = emit_with(
            "export const value: number = 1; export default function read() { return value; }",
            ScriptTarget::EsNext,
            ModuleKind::EsNext,
        );
        assert_eq!(
            result.code,
            "export const value = 1;\nexport default function read() {\n    return value;\n}\n"
        );
    }

    #[test]
    fn transforms_es_modules_to_commonjs() {
        let result = emit_with(
            "import main, { read as load, write } from 'pkg'; import 'side'; export { load as result }; export * from 'other'; export default main;",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert_eq!(
            result.code,
            "\"use strict\";\nvar __importDefault = (this && this.__importDefault) || function (mod) {\n    return (mod && mod.__esModule) ? mod : { \"default\": mod };\n};\nObject.defineProperty(exports, \"__esModule\", { value: true });\nconst pkg_1 = __importDefault(require('pkg'));\nconst { read: load, write } = require('pkg');\nrequire('side');\nexports.result = load;\nObject.assign(exports, require('other'));\nexports.default = pkg_1.default;\n"
        );
    }

    #[test]
    fn wraps_commonjs_default_imports_with_import_default() {
        let result = emit_with(
            "import Foo from \"./b\"; new Foo();",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert_eq!(
            result.code,
            "\"use strict\";\nvar __importDefault = (this && this.__importDefault) || function (mod) {\n    return (mod && mod.__esModule) ? mod : { \"default\": mod };\n};\nObject.defineProperty(exports, \"__esModule\", { value: true });\nconst b_1 = __importDefault(require(\"./b\"));\nnew b_1.default();\n"
        );
    }

    #[test]
    fn emits_default_import_initializers_directly_to_commonjs_exports() {
        let result = emit_with(
            "import Namespace from \"./b\"; export var x = new Namespace.Foo();",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert_eq!(
            result.code,
            "\"use strict\";\nvar __importDefault = (this && this.__importDefault) || function (mod) {\n    return (mod && mod.__esModule) ? mod : { \"default\": mod };\n};\nObject.defineProperty(exports, \"__esModule\", { value: true });\nexports.x = void 0;\nconst b_1 = __importDefault(require(\"./b\"));\nexports.x = new b_1.default.Foo();\n"
        );
    }

    #[test]
    fn treats_named_default_imports_as_commonjs_default_imports() {
        let result = emit_with(
            "import { default as Foo } from \"./b\"; Foo.bar(); Foo.foo();",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert_eq!(
            result.code,
            "\"use strict\";\nvar __importDefault = (this && this.__importDefault) || function (mod) {\n    return (mod && mod.__esModule) ? mod : { \"default\": mod };\n};\nObject.defineProperty(exports, \"__esModule\", { value: true });\nconst b_1 = __importDefault(require(\"./b\"));\nb_1.default.bar();\nb_1.default.foo();\n"
        );
    }

    #[test]
    fn does_not_emit_import_default_for_type_only_default_usage() {
        let result = emit_with(
            "import Foo from \"./b\"; let value: Foo;",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert_eq!(
            result.code,
            "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nlet value;\n"
        );
    }

    #[test]
    fn emits_runtime_import_equals_for_commonjs() {
        let commonjs = emit_with(
            "import ts = require('typescript'); ts.version;",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert_eq!(
            commonjs.code,
            "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nconst ts = require('typescript');\nts.version;\n"
        );

        let es_module = emit_with(
            "import ts = require('typescript'); ts.version;",
            ScriptTarget::Es2015,
            ModuleKind::EsNext,
        );
        assert_eq!(
            es_module.code,
            "const ts = require('typescript');\nts.version;\n"
        );
    }

    #[test]
    fn internal_import_equals_aliases_do_not_make_scripts_external_modules() {
        let result = emit_with(
            "namespace Models { export class Model {} } import Model = Models.Model; new Model();",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert!(!result.code.contains("__esModule"), "{}", result.code);
        assert!(!result.code.starts_with("\"use strict\";"));
        assert!(result.code.contains("const Model = Models.Model;"));
    }

    #[test]
    fn elides_imports_used_only_in_type_positions() {
        let source = "import Types = require('types'); import Runtime = require('runtime'); import 'side'; interface Box { value: Types.Value; } class Derived extends Runtime.Base {}";
        let result = emit_with(source, ScriptTarget::Es2015, ModuleKind::CommonJs);
        assert!(!result.code.contains("require('types')"), "{}", result.code);
        assert!(result.code.contains("const Runtime = require('runtime');"));
        assert!(result.code.contains("require('side');"));
        assert!(result.code.contains("class Derived extends Runtime.Base"));

        let namespace_source = "import * as Types from 'types'; import * as Runtime from 'runtime'; type Value = Types.Value; Runtime.run();";
        let namespace = emit_with(namespace_source, ScriptTarget::Es2015, ModuleKind::CommonJs);
        assert!(!namespace.code.contains("require('types')"));
        assert!(
            namespace
                .code
                .contains("const Runtime = __importStar(require('runtime'));")
        );

        let type_only_namespace = emit_with(
            "import * as Types from 'types'; type Value = Types.Value;",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert!(!type_only_namespace.code.contains("__importStar"));
        assert!(!type_only_namespace.code.contains("require('types')"));
    }

    #[test]
    fn emits_namespace_imports_for_es_modules_and_commonjs() {
        let es_module = emit_with(
            "import * as ts from 'typescript'; ts.version;",
            ScriptTarget::Es2015,
            ModuleKind::EsNext,
        );
        assert_eq!(
            es_module.code,
            "import * as ts from 'typescript';\nts.version;\n"
        );

        let commonjs = emit_with(
            "import * as ts from 'typescript'; ts.version;",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert!(commonjs.code.contains("var __createBinding ="));
        assert!(commonjs.code.contains("var __setModuleDefault ="));
        assert!(commonjs.code.contains("var __importStar ="));
        assert!(
            commonjs
                .code
                .ends_with("const ts = __importStar(require('typescript'));\nts.version;\n")
        );
    }

    #[test]
    fn emits_import_star_helpers_once_for_commonjs_namespace_imports() {
        let result = emit_with(
            "import * as first from 'first'; import * as second from 'second'; first.read(second);",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert_eq!(result.code.matches("var __importStar =").count(), 1);
        assert!(
            result
                .code
                .contains("const first = __importStar(require('first'));")
        );
        assert!(
            result
                .code
                .contains("const second = __importStar(require('second'));")
        );
    }

    #[test]
    fn emits_numeric_and_string_named_class_method_overloads() {
        let result = emit_with(
            "class Numeric { 0(); 1() { } } class StringNamed { 'foo'(); 'bar'() { } }",
            ScriptTarget::Es2015,
            ModuleKind::EsNext,
        );
        assert_eq!(
            result.code,
            "class Numeric {\n    1() { }\n}\nclass StringNamed {\n    'bar'() { }\n}\n"
        );
    }

    #[test]
    fn emits_commonjs_strict_prologue_only_for_modules() {
        let module = emit_with(
            "export const value = 1;",
            ScriptTarget::Es5,
            ModuleKind::CommonJs,
        );
        assert!(module.code.starts_with("\"use strict\";\n"));
        let script = emit_with("const value = 1;", ScriptTarget::Es5, ModuleKind::CommonJs);
        assert_eq!(script.code, "var value = 1;\n");
    }

    #[test]
    fn transforms_exported_declarations_to_commonjs() {
        let result = emit_with(
            "export const value = 1; export function read() { return value; } export class Box {} export enum Color { Red }",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        for assignment in [
            "exports.value = value;",
            "exports.read = read;",
            "exports.Box = Box;",
            "exports.Color = Color;",
        ] {
            assert!(result.code.contains(assignment), "{}", result.code);
        }
    }

    #[test]
    fn emits_commonjs_export_equals_after_runtime_declarations() {
        let source = "export = B;\nexport class C {\n}\n";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::CommonJs).code,
            "\"use strict\";\nexports.C = void 0;\nclass C {\n}\nmodule.exports = B;\n"
        );

        let type_only = emit_with(
            "interface Shape { value: number; } export = Shape;",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert_eq!(
            type_only.code,
            "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\n"
        );
    }

    #[test]
    fn emits_extends_helper_before_commonjs_module_prologue() {
        let result = emit_with(
            "export class Derived extends Base {}",
            ScriptTarget::Es5,
            ModuleKind::CommonJs,
        );
        let helper = result.code.find("var __extends").unwrap();
        let module = result.code.find("Object.defineProperty(exports").unwrap();
        assert!(helper < module, "{}", result.code);
    }

    #[test]
    fn preinitializes_commonjs_value_exports_once_in_source_order() {
        let result = emit_with(
            "export class First {} export const value = 1; export enum State { Ready } export default class Last {}",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert!(
            result.code.contains(
                "exports.default = exports.State = exports.value = exports.First = void 0;"
            ),
            "{}",
            result.code
        );
        assert_eq!(result.code.matches(" = void 0;").count(), 1);
        for assignment in [
            "exports.First = First;",
            "exports.value = value;",
            "exports.State = State;",
            "exports.default = Last;",
        ] {
            assert!(result.code.contains(assignment), "{}", result.code);
        }
    }

    #[test]
    fn preinitialization_is_the_only_emit_for_uninitialized_exported_variables() {
        let result = emit_with(
            "export var id: number;",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert_eq!(
            result.code,
            "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nexports.id = void 0;\n"
        );
    }

    #[test]
    fn produces_monotonic_source_map_mappings() {
        let result = emit_with(
            "const first = 1;\nconst second = first + 1;",
            ScriptTarget::EsNext,
            ModuleKind::EsNext,
        );
        let map = result.source_map.unwrap();
        assert_eq!(map.version, 3);
        assert_eq!(map.sources, ["input.ts"]);
        assert_eq!(map.mappings, "AAAA;AACA");
    }

    #[test]
    fn source_map_columns_use_utf16_code_units() {
        assert_eq!(original_position("😀 value", &[0], 5), (0, 3));
    }

    #[test]
    fn emits_ambient_declarations_for_exported_api() {
        let source = r#"
            import { Input } from "./types";
            const hidden = 0;
            export const version: number = 1;
            export function identity<T>(value: T): T { return value; }
            export function parse(value: string): string;
            export function parse(value: any): any { return value; }
            export class Store<T> { value: T; read(input: T): T { return input; } }
            export interface Box<T> { value: T; }
            export type Maybe<T> = T | undefined;
            export enum Color { Red, Blue = 2 }
            export namespace Helpers { export function read(value: string): string { return value; } }
            export { Input };
        "#;
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let result =
            emit_declaration_file(&parsed.arena, parsed.source_file, "input.ts", source, true)
                .unwrap();
        assert_eq!(
            result.code,
            "import { Input } from \"./types\";\nexport declare const version: number;\nexport declare function identity<T>(value: T): T;\nexport declare function parse(value: string): string;\nexport declare class Store<T> {\n    value: T;\n    read(input: T): T;\n}\nexport interface Box<T> {\n    value: T;\n}\nexport type Maybe<T> = T | undefined;\nexport declare enum Color {\n    Red,\n    Blue = 2,\n}\nexport declare namespace Helpers {\n    export function read(value: string): string;\n}\nexport { Input };\n"
        );
        assert!(result.source_map.is_some());
    }

    #[test]
    fn emits_only_reachable_private_declarations_and_a_scope_seal() {
        let source = concat!(
            "type T = { x: number };\n",
            "type Unused = { hidden: string };\n",
            "export interface I { f: T; }\n",
        );
        let parsed = parse_source_file(source);
        let NodeData::SourceFile(file) = &parsed.arena.get(parsed.source_file).unwrap().data else {
            panic!("expected source file");
        };
        let retained = BTreeSet::from([file.statements.nodes[0], file.statements.nodes[2]]);
        let reachability = BTreeMap::from([(parsed.source_file, retained)]);
        let result = emit_declaration_file_with_reachability(
            &parsed.arena,
            parsed.source_file,
            "input.ts",
            source,
            false,
            Some(&reachability),
            None,
        )
        .unwrap();
        assert_eq!(
            result.code,
            concat!(
                "type T = {\n",
                "    x: number;\n",
                "};\n",
                "export interface I {\n",
                "    f: T;\n",
                "}\n",
                "export {};\n",
            )
        );
    }
}
