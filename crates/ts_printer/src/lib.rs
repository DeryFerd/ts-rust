//! Deterministic modern-JavaScript emission from the generated TypeScript AST.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::error::Error;
use std::fmt;

use ts_ast::{Node, NodeArena, NodeData, NodeId, NodeList, SymbolId, SyntaxKind};
use ts_binder::{BindResult, bind_source_file};
use ts_checker::{FunctionType, ImportTypeReference, ObjectType, TypeArena, TypeId, TypeKind};
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
    pub amd_bundle: bool,
    pub amd_dependencies: &'a [AmdDependency<'a>],
    pub enum_member_values: &'a BTreeMap<NodeId, EmitConstantValue>,
    pub enum_access_values: &'a BTreeMap<NodeId, EmitConstantValue>,
    pub import_runtime_meanings: &'a BTreeMap<NodeId, bool>,
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
            no_emit_helpers: false,
            remove_comments: false,
            use_define_for_class_fields: None,
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
    let empty_import_meanings = BTreeMap::new();
    emit_source_file_with_context(
        arena,
        source_file,
        source_name,
        source_text,
        settings,
        &EmitContext {
            bindings,
            amd_module_name: None,
            amd_bundle: false,
            amd_dependencies: &[],
            enum_member_values: &empty_enum_values,
            enum_access_values: &empty_enum_values,
            import_runtime_meanings: &empty_import_meanings,
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
        generated_names: GeneratedNames::new(arena),
        runtime_identifier_uses: HashSet::new(),
        commonjs_default_imports: HashMap::new(),
        commonjs_named_import_temps: HashMap::new(),
        has_runtime_export_equals: false,
        bindings: context.bindings,
        identifier_rewrites: HashMap::new(),
        system_predeclared_names: HashSet::new(),
        system_export_function: None,
        system_exported_bindings: HashMap::new(),
        commonjs_module_transform: settings.module == ModuleKind::CommonJs,
        enum_member_values: context.enum_member_values,
        enum_access_values: context.enum_access_values,
        import_runtime_meanings: context.import_runtime_meanings,
        const_enum_emit_mode: ConstEnumEmitMode::new(
            context.preserve_const_enums,
            context.inline_const_enums,
        ),
        enum_access_fallbacks,
        emitted_source_comments: HashSet::new(),
        class_expression_temps: HashMap::new(),
        async_expression_transform: AsyncExpressionTransform::None,
        async_loop_counter: 0,
        async_control_counter: 0,
        commonjs_empty_binding_temps: HashMap::new(),
        commonjs_empty_binding_hoists: Vec::new(),
    };
    let node = printer.node(source_file)?.clone();
    let NodeData::SourceFile(data) = &node.data else {
        return Err(Printer::unsupported(source_file, node.kind));
    };
    let source_end = node.range.end.get();
    printer.runtime_identifier_uses = runtime_identifier_uses(arena, source_file);
    // The classic JSX transform synthesizes `React.createElement` calls, so a default
    // `React` import is a runtime dependency even when every source-level reference is
    // confined to type positions.
    if settings.jsx == JsxEmit::React && source_has_jsx(arena) {
        printer.runtime_identifier_uses.insert("React".to_owned());
    }
    if settings.module == ModuleKind::CommonJs {
        printer.commonjs_default_imports = commonjs_default_imports(
            arena,
            &data.statements,
            &printer.runtime_identifier_uses,
            context.import_runtime_meanings,
        );
        let (temps, rewrites) = commonjs_named_imports(
            arena,
            &data.statements,
            context.bindings,
            &printer.runtime_identifier_uses,
            context.import_runtime_meanings,
            &printer.commonjs_default_imports,
        );
        printer.commonjs_named_import_temps = temps;
        printer.identifier_rewrites.extend(rewrites);
    }
    let is_external_module = data.statements.nodes.iter().any(|statement| {
        arena
            .get(*statement)
            .is_some_and(|statement| declaration_is_module_indicator(arena, statement))
    });
    let has_runtime_module_indicator = data.statements.nodes.iter().any(|statement| {
        arena.get(*statement).is_some_and(|node| {
            declaration_is_module_indicator(arena, node)
                && printer.statement_emits_runtime(*statement, node)
        })
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
    let preserves_external_module_syntax = is_external_module
        && matches!(
            settings.module,
            ModuleKind::None
                | ModuleKind::Es2015
                | ModuleKind::Es2020
                | ModuleKind::Es2022
                | ModuleKind::EsNext
                | ModuleKind::Preserve
        );
    let has_empty_export = data.statements.nodes.iter().any(|statement| {
        arena
            .get(*statement)
            .is_some_and(|statement| export_declaration_is_empty(arena, statement))
    });
    let has_recovered_module_clause = data.statements.nodes.iter().any(|statement| {
        matches!(
            arena.get(*statement).map(|node| &node.data),
            Some(NodeData::NotEmittedStatement(_))
        )
    });
    let needs_async_generator_helper =
        settings.target < ScriptTarget::Es2018 && source_needs_async_generator_helper(arena);
    let needs_dynamic_import_helpers =
        settings.module == ModuleKind::CommonJs && source_has_dynamic_import(arena);
    if !has_use_strict
        && !preserves_external_module_syntax
        && (settings.always_strict
            || (settings.module == ModuleKind::CommonJs && is_external_module)
            || needs_async_generator_helper)
    {
        printer.writer.write("\"use strict\";");
        printer.writer.newline();
    }
    if settings.module == ModuleKind::CommonJs && is_external_module {
        printer.prepare_commonjs_empty_binding_temps(&data.statements);
        let temps = printer.commonjs_empty_binding_hoists.clone();
        if !temps.is_empty() {
            printer.writer.write("var ");
            printer.writer.write(&temps.join(", "));
            printer.writer.write(";");
            printer.writer.newline();
        }
    }
    let first_statement_start = data
        .statements
        .nodes
        .first()
        .and_then(|statement| arena.get(*statement))
        .map(|node| node.range.start.get());
    if let Some(start) = first_statement_start {
        printer.emit_leading_detached_source_comments(start);
        if settings.module == ModuleKind::CommonJs && is_external_module {
            printer.emit_leading_pinned_source_comments(start);
        } else if data.statements.nodes.first().is_some_and(|statement| {
            arena
                .get(*statement)
                .is_some_and(|node| printer.statement_emits_runtime(*statement, node))
        }) {
            printer.emit_leading_source_comments(start);
        } else {
            printer.emit_leading_pinned_source_comments(start);
        }
    }
    if needs_dynamic_import_helpers && !settings.no_emit_helpers {
        printer.emit_create_binding_helper();
        printer.emit_import_star_helper();
    }
    if settings.target < ScriptTarget::Es2017
        && source_needs_awaiter_helper(arena)
        && !settings.no_emit_helpers
    {
        printer.emit_awaiter_helper();
    }
    if settings.target < ScriptTarget::Es2015
        && (source_needs_awaiter_helper(arena)
            || source_needs_downlevel_generator_helper(arena)
            || needs_async_generator_helper)
        && !settings.no_emit_helpers
    {
        printer.emit_generator_helper();
    }
    if settings.target < ScriptTarget::Es2022
        && source_needs_set_function_name_helper(arena)
        && !settings.no_emit_helpers
    {
        printer.emit_set_function_name_helper();
    }
    if needs_async_generator_helper && !settings.no_emit_helpers {
        printer.emit_await_helper();
        printer.emit_async_generator_helper();
    }
    if settings.target < ScriptTarget::Es2015
        && source_needs_downlevel_values_helper(arena)
        && !settings.no_emit_helpers
    {
        printer.emit_values_helper();
    }
    if settings.target < ScriptTarget::Es2018
        && source_needs_object_rest_helper(arena)
        && !settings.no_emit_helpers
    {
        printer.emit_object_rest_helper();
    }
    if settings.target < ScriptTarget::Es2015 && source_needs_extends_helper(arena) {
        printer.emit_extends_helper();
    }
    let auto_accessor_storages = runtime_auto_accessor_storage_names(arena);
    if !auto_accessor_storages.is_empty() {
        printer.emit_auto_accessor_helpers();
        for storage in &auto_accessor_storages {
            printer.writer.write("var ");
            printer.writer.write(storage);
            printer.writer.write(";");
            printer.writer.newline();
        }
    }
    let export_equals_expression = runtime_export_equals_expression(arena, &data.statements);
    printer.has_runtime_export_equals = export_equals_expression.is_some();
    if settings.module == ModuleKind::CommonJs && is_external_module {
        let needs_import_star_helper = source_needs_import_star_helper(
            arena,
            &data.statements,
            &printer.runtime_identifier_uses,
            context.import_runtime_meanings,
        );
        let needs_export_star_helper = source_needs_export_star_helper(arena, &data.statements);
        if (needs_import_star_helper || needs_export_star_helper) && !needs_dynamic_import_helpers {
            printer.emit_create_binding_helper();
        }
        if needs_import_star_helper && !needs_dynamic_import_helpers {
            printer.emit_import_star_helper();
        }
        if needs_export_star_helper {
            printer.emit_export_star_helper();
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
        let preinitialized_exports = printer.commonjs_preinitialized_export_names(&data.statements);
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
                if function.body.is_none() {
                    continue;
                }
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
            printer.emit_commonjs_hoisted_function_exports(&data.statements)?;
        }
        if let Some(start) = first_statement_start {
            printer.emit_leading_source_comments(start);
        }
    }
    printer.emit_automatic_jsx_prelude();
    if (ScriptTarget::Es2015..ScriptTarget::Es2017).contains(&settings.target)
        && source_needs_async_static_field_class_temp(arena)
    {
        printer.writer.write("var _a;");
        printer.writer.newline();
    }
    let mut previous_end = data
        .statements
        .nodes
        .first()
        .and_then(|statement| arena.get(*statement))
        .map_or(0, |node| node.range.start.get());
    let mut reference_owner_start = 0;
    let mut previous_emitted = false;
    let mut emitted_runtime_statement = false;
    let mut pending_commonjs_imports = Vec::new();
    for statement in &data.statements.nodes {
        let statement_node = arena.get(*statement);
        let current_emitted =
            statement_node.is_some_and(|node| printer.statement_emits_runtime(*statement, node));
        let current_owns_source_comments =
            statement_node.is_some_and(|node| printer.statement_emits_in_place(*statement, node));
        emitted_runtime_statement |= current_emitted;
        let current_is_import = matches!(
            arena.get(*statement).map(|node| &node.data),
            Some(NodeData::ImportDeclaration(_))
        );
        if settings.module == ModuleKind::CommonJs && current_emitted && !current_is_import {
            for import in pending_commonjs_imports.drain(..) {
                printer.emit_commonjs_import_binding_exports(import, &data.statements)?;
            }
        }
        if let Some(node) = arena.get(*statement) {
            if current_emitted {
                printer.emit_reference_directives_between(
                    reference_owner_start,
                    node.range.start.get(),
                );
            } else if settings.module != ModuleKind::None {
                printer.emit_detached_reference_directives_between(
                    reference_owner_start,
                    node.range.start.get(),
                );
            }
            printer.emit_source_comments_between_with_ownership(
                previous_end,
                node.range.start.get(),
                previous_emitted,
                current_owns_source_comments,
            );
            previous_emitted = current_owns_source_comments;
            previous_end = node.range.end.get();
            if current_emitted || settings.module != ModuleKind::None {
                reference_owner_start = node.range.end.get();
            }
        }
        printer.emit_statement(*statement)?;
        if settings.module == ModuleKind::CommonJs && current_emitted && current_is_import {
            pending_commonjs_imports.push(*statement);
        }
    }
    for import in pending_commonjs_imports {
        printer.emit_commonjs_import_binding_exports(import, &data.statements)?;
    }
    if !emitted_runtime_statement {
        if data.statements.nodes.is_empty() {
            printer.emit_reference_directives_between(0, source_end);
        } else if settings.module == ModuleKind::None {
            let mut reference_owner_start = 0;
            for statement in &data.statements.nodes {
                let Some(node) = arena.get(*statement) else {
                    continue;
                };
                printer.emit_detached_reference_directives_between(
                    reference_owner_start,
                    node.range.start.get(),
                );
                reference_owner_start = node.range.end.get();
            }
            printer.emit_detached_reference_directives_between(reference_owner_start, source_end);
        }
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
    if preserves_external_module_syntax
        && (!has_runtime_module_indicator || has_empty_export || has_recovered_module_clause)
    {
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

fn source_needs_awaiter_helper(arena: &NodeArena) -> bool {
    arena.iter().any(|(_, node)| match &node.data {
        NodeData::FunctionDeclaration(function) => {
            function.body.is_some()
                && function.asterisk_token.is_none()
                && declaration_has_modifier(arena, node, SyntaxKind::AsyncKeyword)
        }
        NodeData::FunctionExpression(function) => {
            function.asterisk_token.is_none()
                && declaration_has_modifier(arena, node, SyntaxKind::AsyncKeyword)
        }
        NodeData::ArrowFunction(function) => function.modifiers.as_ref().is_some_and(|modifiers| {
            modifiers.list.nodes.iter().any(|modifier| {
                arena
                    .get(*modifier)
                    .is_some_and(|modifier| modifier.kind == SyntaxKind::AsyncKeyword)
            })
        }),
        NodeData::MethodDeclaration(method) => {
            method.body.is_some()
                && method.asterisk_token.is_none()
                && declaration_has_modifier(arena, node, SyntaxKind::AsyncKeyword)
        }
        _ => false,
    })
}

fn source_needs_downlevel_generator_helper(arena: &NodeArena) -> bool {
    arena.iter().any(|(_, node)| match &node.data {
        NodeData::FunctionDeclaration(function) => {
            function.body.is_some()
                && function.asterisk_token.is_some()
                && !declaration_has_modifier(arena, node, SyntaxKind::AsyncKeyword)
        }
        NodeData::FunctionExpression(function) => {
            function.asterisk_token.is_some()
                && !declaration_has_modifier_in_list(
                    arena,
                    function.modifiers.as_ref(),
                    SyntaxKind::AsyncKeyword,
                )
        }
        _ => false,
    })
}

fn source_needs_downlevel_values_helper(arena: &NodeArena) -> bool {
    arena.iter().any(|(_, node)| {
        if matches!(&node.data, NodeData::YieldExpression(yielded) if yielded.asterisk_token.is_some())
        {
            return true;
        }
        let NodeData::FunctionDeclaration(function) = &node.data else {
            return false;
        };
        function.asterisk_token.is_some()
            && !declaration_has_modifier(arena, node, SyntaxKind::AsyncKeyword)
            && function
                .body
                .is_some_and(|body| is_downlevel_generator_for_of_body(arena, body))
    })
}

fn is_downlevel_generator_for_of_body(arena: &NodeArena, body: NodeId) -> bool {
    let Some(NodeData::Block(block)) = arena.get(body).map(|node| &node.data) else {
        return false;
    };
    let [loop_id] = block.statements.nodes.as_slice() else {
        return false;
    };
    let Some(loop_node) = arena.get(*loop_id) else {
        return false;
    };
    let NodeData::ForInOrOfStatement(for_of) = &loop_node.data else {
        return false;
    };
    if loop_node.kind != SyntaxKind::ForOfStatement || for_of.await_modifier.is_some() {
        return false;
    }
    let Some(NodeData::Block(loop_body)) = arena.get(for_of.statement).map(|node| &node.data)
    else {
        return false;
    };
    loop_body.statements.nodes.last().is_some_and(|statement| {
        let Some(NodeData::ExpressionStatement(statement)) =
            arena.get(*statement).map(|node| &node.data)
        else {
            return false;
        };
        matches!(
            arena.get(statement.expression).map(|node| &node.data),
            Some(NodeData::YieldExpression(yielded)) if yielded.expression.is_some()
        )
    })
}

fn source_needs_async_generator_helper(arena: &NodeArena) -> bool {
    arena.iter().any(|(_, node)| match &node.data {
        NodeData::FunctionDeclaration(function) => {
            function.body.is_some()
                && function.asterisk_token.is_some()
                && declaration_has_modifier(arena, node, SyntaxKind::AsyncKeyword)
        }
        NodeData::FunctionExpression(function) => {
            function.asterisk_token.is_some()
                && declaration_has_modifier_in_list(
                    arena,
                    function.modifiers.as_ref(),
                    SyntaxKind::AsyncKeyword,
                )
        }
        NodeData::MethodDeclaration(method) => {
            method.body.is_some()
                && method.asterisk_token.is_some()
                && declaration_has_modifier_in_list(
                    arena,
                    method.modifiers.as_ref(),
                    SyntaxKind::AsyncKeyword,
                )
        }
        _ => false,
    })
}

fn source_has_dynamic_import(arena: &NodeArena) -> bool {
    arena.iter().any(|(_, node)| {
        let NodeData::CallExpression(call) = &node.data else {
            return false;
        };
        matches!(
            arena.get(call.expression).map(|node| &node.data),
            Some(NodeData::Identifier(identifier)) if identifier.text == "import"
        )
    })
}

fn source_needs_object_rest_helper(arena: &NodeArena) -> bool {
    arena.iter().any(|(_, node)| {
        let NodeData::ArrowFunction(function) = &node.data else {
            return false;
        };
        if !function.modifiers.as_ref().is_some_and(|modifiers| {
            modifiers.list.nodes.iter().any(|modifier| {
                arena
                    .get(*modifier)
                    .is_some_and(|modifier| modifier.kind == SyntaxKind::AsyncKeyword)
            })
        }) {
            return false;
        }
        function.parameters.nodes.iter().any(|parameter| {
            let Some(NodeData::ParameterDeclaration(parameter)) =
                arena.get(*parameter).map(|node| &node.data)
            else {
                return false;
            };
            let Some(NodeData::BindingPattern(pattern)) =
                arena.get(parameter.name).map(|node| &node.data)
            else {
                return false;
            };
            arena.get(parameter.name).is_some_and(|node| {
                node.kind == SyntaxKind::ObjectBindingPattern
                    && pattern.elements.nodes.iter().any(|element| {
                        matches!(
                            arena.get(*element).map(|node| &node.data),
                            Some(NodeData::BindingElement(element))
                                if element.dot_dot_dot_token.is_some()
                        )
                    })
            })
        })
    })
}

fn source_needs_async_static_field_class_temp(arena: &NodeArena) -> bool {
    arena.iter().any(|(_, node)| {
        let NodeData::ClassDeclaration(class) = &node.data else {
            return false;
        };
        class_has_async_static_field(arena, class)
    })
}

fn class_has_async_static_field(arena: &NodeArena, class: &ts_ast::ClassDeclarationData) -> bool {
    class.members.nodes.iter().any(|member| {
        let Some(member_node) = arena.get(*member) else {
            return false;
        };
        let NodeData::PropertyDeclaration(property) = &member_node.data else {
            return false;
        };
        property.modifiers.as_ref().is_some_and(|modifiers| {
            modifiers.list.nodes.iter().any(|modifier| {
                arena
                    .get(*modifier)
                    .is_some_and(|modifier| modifier.kind == SyntaxKind::StaticKeyword)
            })
        }) && property.initializer.is_some_and(|initializer| {
            let Some(NodeData::ArrowFunction(arrow)) =
                arena.get(initializer).map(|node| &node.data)
            else {
                return false;
            };
            arrow.modifiers.as_ref().is_some_and(|modifiers| {
                modifiers.list.nodes.iter().any(|modifier| {
                    arena
                        .get(*modifier)
                        .is_some_and(|modifier| modifier.kind == SyntaxKind::AsyncKeyword)
                })
            })
        })
    })
}

fn source_needs_extends_helper(arena: &NodeArena) -> bool {
    arena.iter().any(|(_, node)| {
        let heritage_clauses = match &node.data {
            NodeData::ClassDeclaration(class) => class.heritage_clauses.as_ref(),
            NodeData::ClassExpression(class) => class.heritage_clauses.as_ref(),
            _ => None,
        };
        heritage_clauses.is_some_and(|clauses| {
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

fn source_needs_set_function_name_helper(arena: &NodeArena) -> bool {
    arena.iter().any(|(id, node)| {
        let NodeData::ClassExpression(class) = &node.data else {
            return false;
        };
        if class.name.is_some() {
            return false;
        }
        let Some(parent) = node.parent.and_then(|parent| arena.get(parent)) else {
            return false;
        };
        let NodeData::VariableDeclaration(declaration) = &parent.data else {
            return false;
        };
        declaration.initializer == Some(id)
            && class.members.nodes.iter().any(|member| {
                let Some(NodeData::PropertyDeclaration(property)) =
                    arena.get(*member).map(|node| &node.data)
                else {
                    return false;
                };
                property.initializer.is_some()
                    && declaration_has_modifier_in_list(
                        arena,
                        property.modifiers.as_ref(),
                        SyntaxKind::StaticKeyword,
                    )
            })
    })
}

fn runtime_auto_accessor_storage_names(arena: &NodeArena) -> Vec<String> {
    let mut names = Vec::new();
    for (id, node) in arena.iter() {
        let NodeData::ClassDeclaration(class) = &node.data else {
            continue;
        };
        if node_is_in_ambient_context(arena, id) {
            continue;
        }
        let Some(class_name) = class
            .name
            .and_then(|name| declaration_name_text(arena, name))
        else {
            continue;
        };
        for member in &class.members.nodes {
            let Some(NodeData::PropertyDeclaration(property)) =
                arena.get(*member).map(|node| &node.data)
            else {
                continue;
            };
            if !declaration_has_modifier_in_list(
                arena,
                property.modifiers.as_ref(),
                SyntaxKind::AccessorKeyword,
            ) || declaration_has_modifier_in_list(
                arena,
                property.modifiers.as_ref(),
                SyntaxKind::StaticKeyword,
            ) {
                continue;
            }
            let Some(property_name) = declaration_name_text(arena, property.name) else {
                continue;
            };
            names.push(format!("_{class_name}_{property_name}_accessor_storage"));
        }
    }
    names
}

fn node_is_in_ambient_context(arena: &NodeArena, mut id: NodeId) -> bool {
    loop {
        let Some(node) = arena.get(id) else {
            return false;
        };
        if declaration_has_modifier(arena, node, SyntaxKind::DeclareKeyword) {
            return true;
        }
        let Some(parent) = node.parent else {
            return false;
        };
        id = parent;
    }
}

fn declaration_has_modifier_in_list(
    arena: &NodeArena,
    modifiers: Option<&ts_ast::ModifierList>,
    kind: SyntaxKind,
) -> bool {
    modifiers.is_some_and(|modifiers| {
        modifiers
            .list
            .nodes
            .iter()
            .any(|modifier| arena.get(*modifier).is_some_and(|node| node.kind == kind))
    })
}

fn source_needs_import_star_helper(
    arena: &NodeArena,
    statements: &NodeList,
    runtime_identifier_uses: &HashSet<String>,
    import_runtime_meanings: &BTreeMap<NodeId, bool>,
) -> bool {
    statements.nodes.iter().any(|statement| {
        if import_runtime_meanings.get(statement) == Some(&false) {
            return false;
        }
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

fn source_needs_export_star_helper(arena: &NodeArena, statements: &NodeList) -> bool {
    statements.nodes.iter().any(|statement| {
        matches!(
            arena.get(*statement).map(|node| &node.data),
            Some(NodeData::ExportDeclaration(export))
                if !export.is_type_only
                    && export.export_clause.is_none()
                    && export.module_specifier.is_some()
        )
    })
}

fn commonjs_default_imports(
    arena: &NodeArena,
    statements: &NodeList,
    runtime_identifier_uses: &HashSet<String>,
    import_runtime_meanings: &BTreeMap<NodeId, bool>,
) -> HashMap<String, String> {
    let mut imports = HashMap::new();
    let mut module_name_counts = HashMap::<String, usize>::new();
    for statement in &statements.nodes {
        if import_runtime_meanings.get(statement) == Some(&false) {
            continue;
        }
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

fn amd_import_dependency_path(path: &str, bundle: bool) -> String {
    if bundle {
        path.strip_prefix("./").unwrap_or(path).to_owned()
    } else {
        path.to_owned()
    }
}

fn commonjs_named_imports(
    arena: &NodeArena,
    statements: &NodeList,
    bindings: &BindResult,
    runtime_identifier_uses: &HashSet<String>,
    import_runtime_meanings: &BTreeMap<NodeId, bool>,
    default_imports: &HashMap<String, String>,
) -> (HashMap<NodeId, String>, HashMap<SymbolId, String>) {
    let mut temps = HashMap::new();
    let mut rewrites = HashMap::new();
    let mut generated_names = GeneratedNames::new(arena);
    generated_names
        .used
        .extend(default_imports.values().cloned());
    for statement in &statements.nodes {
        if import_runtime_meanings.get(statement) == Some(&false) {
            continue;
        }
        let Some(NodeData::ImportDeclaration(import)) =
            arena.get(*statement).map(|node| &node.data)
        else {
            continue;
        };
        if import.attributes.is_some() {
            continue;
        }
        let Some(clause_id) = import.import_clause else {
            continue;
        };
        let Some(NodeData::ImportClause(clause)) = arena.get(clause_id).map(|node| &node.data)
        else {
            continue;
        };
        if clause.name.is_some() || clause.phase_modifier == Some(SyntaxKind::TypeKeyword) {
            continue;
        }
        let Some(NodeData::NamedImports(imports)) = clause
            .named_bindings
            .and_then(|named| arena.get(named))
            .map(|node| &node.data)
        else {
            continue;
        };
        let mut imported_bindings = Vec::new();
        for specifier_id in &imports.elements.nodes {
            let Some(NodeData::ImportSpecifier(specifier)) =
                arena.get(*specifier_id).map(|node| &node.data)
            else {
                continue;
            };
            if specifier.is_type_only
                || specifier
                    .property_name
                    .is_some_and(|name| declaration_name_text(arena, name) == Some("default"))
            {
                continue;
            }
            let Some(local) = declaration_name_text(arena, specifier.name) else {
                continue;
            };
            if !runtime_identifier_uses.contains(local) {
                continue;
            }
            let imported = specifier
                .property_name
                .and_then(|name| declaration_name_text(arena, name))
                .unwrap_or(local);
            let Some(symbol) = bindings.node_symbols.get(&specifier.name).copied() else {
                continue;
            };
            imported_bindings.push((symbol, imported));
        }
        if imported_bindings.is_empty() {
            continue;
        }
        let base = commonjs_module_temp_base(arena, import.module_specifier);
        let temp = generated_names.generate(&base);
        temps.insert(clause_id, temp.clone());
        for (symbol, imported) in imported_bindings {
            rewrites.insert(symbol, commonjs_import_access(&temp, imported));
        }
    }
    (temps, rewrites)
}

fn commonjs_import_access(temp: &str, imported: &str) -> String {
    if is_identifier_text(imported) {
        return format!("{temp}.{imported}");
    }
    let mut writer = Writer::default();
    writer.write(temp);
    writer.write("[");
    write_quoted(&mut writer, imported);
    writer.write("]");
    writer.output
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
        NodeData::ExportDeclaration(_) if export_declaration_is_empty(arena, node) => false,
        NodeData::FunctionDeclaration(function) => function.body.is_some(),
        _ => true,
    }
}

fn export_declaration_is_empty(arena: &NodeArena, node: &Node) -> bool {
    let NodeData::ExportDeclaration(export) = &node.data else {
        return false;
    };
    if export.module_specifier.is_some() {
        return false;
    }
    matches!(
        export.export_clause.and_then(|clause| arena.get(clause)),
        Some(Node {
            data: NodeData::NamedExports(exports),
            ..
        }) if exports.elements.nodes.is_empty()
    )
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

fn source_has_jsx(arena: &NodeArena) -> bool {
    arena.iter().any(|(_, node)| {
        matches!(
            node.data,
            NodeData::JsxElement(_) | NodeData::JsxSelfClosingElement(_) | NodeData::JsxFragment(_)
        )
    })
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
        NodeData::ClassExpression(declaration) => declaration.name == Some(child),
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
    emit_declaration_file_with_semantics(
        arena,
        source_file,
        source_name,
        source_text,
        declaration_map,
        declaration_reachability,
        enum_member_values,
        None,
        None,
        None,
    )
}

/// Emits declarations with checker-owned inferred type metadata.
///
/// # Errors
///
/// Returns an error when a declaration contains an unsupported or missing node.
#[allow(clippy::too_many_arguments)]
pub fn emit_declaration_file_with_semantics(
    arena: &NodeArena,
    source_file: NodeId,
    source_name: &str,
    source_text: &str,
    declaration_map: bool,
    declaration_reachability: Option<&BTreeMap<NodeId, BTreeSet<NodeId>>>,
    enum_member_values: Option<&BTreeMap<NodeId, EmitConstantValue>>,
    semantic_types: Option<&TypeArena>,
    node_types: Option<&BTreeMap<NodeId, TypeId>>,
    import_type_references: Option<&BTreeMap<TypeId, ImportTypeReference>>,
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
        semantic_types,
        node_types,
        import_type_references,
        javascript_source: [".js", ".jsx", ".mjs", ".cjs"]
            .iter()
            .any(|extension| source_name.to_ascii_lowercase().ends_with(extension)),
        generated_names: HashSet::new(),
        emitted_javascript_class_properties: HashSet::new(),
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
    if let Some((name, type_id)) = printer.amd_like_factory_export(data) {
        printer.writer.write("export = ");
        printer.writer.write(&name);
        printer.writer.write(";");
        printer.writer.newline();
        printer.writer.write("declare const ");
        printer.writer.write(&name);
        printer.writer.write(": ");
        printer.emit_amd_like_factory_export_type(type_id)?;
        printer.writer.write(";");
        printer.writer.newline();
    }
    let mut deferred_javascript_namespaces = Vec::new();
    for statement in &data.statements.nodes {
        if printer.javascript_object_namespace_requires_deferral(*statement) {
            deferred_javascript_namespaces.push(*statement);
        } else {
            printer.emit_statement(*statement, false, source_file)?;
        }
    }
    for statement in deferred_javascript_namespaces {
        printer.emit_statement(statement, false, source_file)?;
    }
    if printer.scope_needs_seal(source_file) || (printer.module_file && printer.writer.is_empty()) {
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
    semantic_types: Option<&'a TypeArena>,
    node_types: Option<&'a BTreeMap<NodeId, TypeId>>,
    import_type_references: Option<&'a BTreeMap<TypeId, ImportTypeReference>>,
    javascript_source: bool,
    generated_names: HashSet<String>,
    emitted_javascript_class_properties: HashSet<(NodeId, String)>,
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

    fn amd_like_factory_export(&self, source: &ts_ast::SourceFileData) -> Option<(String, TypeId)> {
        if !self.javascript_source {
            return None;
        }
        source.statements.nodes.iter().find_map(|statement| {
            let NodeData::ExpressionStatement(statement) = &self.arena.get(*statement)?.data else {
                return None;
            };
            let NodeData::CallExpression(call) = &self
                .arena
                .get(self.unwrap_parenthesized(statement.expression))?
                .data
            else {
                return None;
            };
            if declaration_name_text(self.arena, call.expression) != Some("define") {
                return None;
            }
            call.arguments.nodes.iter().rev().find_map(|factory| {
                let block = self.factory_function_block(*factory)?;
                self.amd_like_block_export(block)
            })
        })
    }

    fn factory_function_block(&self, expression: NodeId) -> Option<&ts_ast::BlockData> {
        let expression = self.unwrap_parenthesized(expression);
        let body = match &self.arena.get(expression)?.data {
            NodeData::ArrowFunction(function) => function.body,
            NodeData::FunctionExpression(function) => function.body,
            _ => return None,
        };
        let NodeData::Block(block) = &self.arena.get(body)?.data else {
            return None;
        };
        Some(block)
    }

    fn amd_like_block_export(&self, block: &ts_ast::BlockData) -> Option<(String, TypeId)> {
        let returned_module = block.statements.nodes.iter().rev().find_map(|statement| {
            let NodeData::ReturnStatement(return_) = &self.arena.get(*statement)?.data else {
                return None;
            };
            self.module_exports_receiver(return_.expression?)
                .map(str::to_owned)
        })?;
        if !block
            .statements
            .nodes
            .iter()
            .any(|statement| self.variable_statement_declares(*statement, &returned_module))
        {
            return None;
        }
        let exported_name = block.statements.nodes.iter().find_map(|statement| {
            let NodeData::ExpressionStatement(statement) = &self.arena.get(*statement)?.data else {
                return None;
            };
            let NodeData::BinaryExpression(assignment) = &self
                .arena
                .get(self.unwrap_parenthesized(statement.expression))?
                .data
            else {
                return None;
            };
            if self.arena.get(assignment.operator_token)?.kind != SyntaxKind::EqualsToken
                || self.module_exports_receiver(assignment.left) != Some(returned_module.as_str())
            {
                return None;
            }
            declaration_name_text(self.arena, assignment.right).map(str::to_owned)
        })?;
        block.statements.nodes.iter().find_map(|statement| {
            let NodeData::VariableStatement(statement) = &self.arena.get(*statement)?.data else {
                return None;
            };
            let NodeData::VariableDeclarationList(list) =
                &self.arena.get(statement.declaration_list)?.data
            else {
                return None;
            };
            list.declarations.nodes.iter().find_map(|declaration_id| {
                let NodeData::VariableDeclaration(declaration) =
                    &self.arena.get(*declaration_id)?.data
                else {
                    return None;
                };
                (declaration_name_text(self.arena, declaration.name)
                    == Some(exported_name.as_str()))
                .then(|| {
                    let types = self.node_types?;
                    [
                        Some(*declaration_id),
                        Some(declaration.name),
                        declaration.initializer,
                    ]
                    .into_iter()
                    .flatten()
                    .filter_map(|node| types.get(&node).copied())
                    .find(|type_id| {
                        matches!(
                            self.semantic_types
                                .and_then(|types| types.get(*type_id))
                                .map(|type_| &type_.kind),
                            Some(TypeKind::Constructor(_))
                        )
                    })
                })
                .flatten()
                .map(|type_id| (exported_name.clone(), type_id))
            })
        })
    }

    fn variable_statement_declares(&self, statement: NodeId, name: &str) -> bool {
        let Some(NodeData::VariableStatement(statement)) =
            self.arena.get(statement).map(|node| &node.data)
        else {
            return false;
        };
        let Some(NodeData::VariableDeclarationList(list)) = self
            .arena
            .get(statement.declaration_list)
            .map(|node| &node.data)
        else {
            return false;
        };
        list.declarations.nodes.iter().any(|declaration| {
            let Some(NodeData::VariableDeclaration(declaration)) =
                self.arena.get(*declaration).map(|node| &node.data)
            else {
                return false;
            };
            declaration_name_text(self.arena, declaration.name) == Some(name)
        })
    }

    fn module_exports_receiver(&self, expression: NodeId) -> Option<&str> {
        let NodeData::PropertyAccessExpression(access) =
            &self.arena.get(self.unwrap_parenthesized(expression))?.data
        else {
            return None;
        };
        (declaration_name_text(self.arena, access.name) == Some("exports"))
            .then(|| declaration_name_text(self.arena, access.expression))
            .flatten()
    }

    fn unwrap_parenthesized(&self, mut expression: NodeId) -> NodeId {
        while let Some(NodeData::ParenthesizedExpression(parenthesized)) =
            self.arena.get(expression).map(|node| &node.data)
        {
            expression = parenthesized.expression;
        }
        expression
    }

    fn emit_amd_like_factory_export_type(&mut self, type_id: TypeId) -> Result<(), EmitError> {
        let constructor = self
            .semantic_types
            .and_then(|types| types.get(type_id))
            .and_then(|type_| match &type_.kind {
                TypeKind::Constructor(signature) => Some(signature.clone()),
                _ => None,
            });
        let Some(constructor) = constructor else {
            return self.emit_semantic_type(type_id);
        };
        self.writer.write("new (");
        self.emit_semantic_parameters(&constructor, None)?;
        self.writer.write(") => ");
        self.emit_semantic_type(constructor.return_type)
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
                if !self.variable_list_has_bound_names(data.declaration_list) {
                    return Ok(());
                }
                if !self.emit_javascript_object_namespaces(&node, data.declaration_list)? {
                    self.emit_declaration_prefix(&node, !in_namespace);
                    self.emit_variable_declarations(data.declaration_list)?;
                    self.writer.write(";");
                }
            }
            NodeData::FunctionDeclaration(data) => {
                self.emit_declaration_prefix(&node, !in_namespace);
                self.writer.write("function ");
                if let Some(name) = data.name {
                    self.emit_name(name)?;
                }
                self.emit_type_parameters(data.type_parameters.as_ref())?;
                let semantic_signature = self.semantic_function_signature(id);
                if let Some(signature) = &semantic_signature {
                    self.emit_declaration_parameters(&data.parameters, signature, id)?;
                } else {
                    self.emit_parameters(&data.parameters)?;
                }
                if data.type_.is_none()
                    && let Some(signature) = semantic_signature
                {
                    self.writer.write(": ");
                    self.emit_function_semantic_return_type(data, signature.return_type)?;
                } else {
                    self.emit_return_type(data.type_)?;
                }
                self.writer.write(";");
            }
            NodeData::ClassDeclaration(data) => {
                let synthetic_base = self.synthetic_class_base(data);
                if let Some((name, type_id, _, argument)) = &synthetic_base {
                    self.writer.write("declare const ");
                    self.writer.write(name);
                    self.writer.write(": ");
                    self.emit_synthetic_base_type(*type_id, argument.as_deref())?;
                    self.writer.write(";");
                    self.writer.newline();
                }
                if !in_namespace {
                    self.emit_declaration_prefix(&node, true);
                }
                self.writer.write("class");
                if let Some(name) = data.name {
                    self.writer.write(" ");
                    self.emit_name(name)?;
                }
                self.emit_type_parameters(data.type_parameters.as_ref())?;
                if let Some((name, _, _, _)) = &synthetic_base {
                    self.writer.write(" extends ");
                    self.writer.write(name);
                } else {
                    self.emit_heritage(data.heritage_clauses.as_ref())?;
                }
                self.writer.write(" {");
                self.writer.newline();
                self.writer.indent += 1;
                self.emit_constructor_parameter_properties(&data.members)?;
                for member in &data.members.nodes {
                    self.emit_member(*member)?;
                    self.emit_javascript_instance_properties(id, *member)?;
                }
                if self.class_has_recovered_constructor(data) {
                    self.writer.write("constructor();");
                    self.writer.newline();
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
                    if let Some(value) = self
                        .enum_member_values
                        .and_then(|values| values.get(&member_id))
                    {
                        self.writer.write(" = ");
                        write_enum_constant(&mut self.writer, value);
                    } else if let Some(initializer) = member.initializer {
                        self.writer.write(" = ");
                        self.emit_literal_expression(initializer)?;
                    }
                    if index + 1 != data.members.nodes.len() {
                        self.writer.write(",");
                    }
                    self.writer.newline();
                }
                self.writer.indent -= 1;
                self.writer.write("}");
            }
            NodeData::ModuleDeclaration(data) => {
                self.emit_declaration_prefix(&node, !in_namespace);
                self.writer.write(
                    if matches!(
                        self.arena.get(data.name).map(|node| &node.data),
                        Some(NodeData::StringLiteral(_))
                    ) {
                        "module "
                    } else {
                        "namespace "
                    },
                );
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
            NodeData::ImportDeclaration(data) => {
                if self.import_is_only_used_by_synthesized_declarations(id, data) {
                    return Ok(());
                }
                self.emit_import(data)?;
            }
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
                    self.emit_name(data.expression)?;
                    self.writer.write(";");
                } else if let Some(type_id) = self.synthesized_expression_type(data.expression) {
                    let name = self.generate_declaration_name("_default");
                    self.writer.write("declare const ");
                    self.writer.write(&name);
                    self.writer.write(": ");
                    self.emit_semantic_type(type_id)?;
                    self.writer.write(";");
                    self.writer.newline();
                    self.writer.write("export default ");
                    self.writer.write(&name);
                    self.writer.write(";");
                } else {
                    self.writer.write("export default ");
                    self.emit_name(data.expression)?;
                    self.writer.write(";");
                }
            }
            _ => return Ok(()),
        }
        self.writer.newline();
        Ok(())
    }

    fn synthesized_expression_type(&self, expression: NodeId) -> Option<TypeId> {
        if matches!(
            self.arena.get(expression).map(|node| &node.data),
            Some(NodeData::Identifier(_))
        ) {
            return None;
        }
        let type_id = self.node_types?.get(&expression).copied()?;
        matches!(
            self.semantic_types?.get(type_id)?.kind,
            TypeKind::Constructor(_) | TypeKind::Intersection(_) | TypeKind::Object(_)
        )
        .then_some(type_id)
    }

    fn synthetic_class_base(
        &mut self,
        class: &ts_ast::ClassDeclarationData,
    ) -> Option<(String, TypeId, NodeId, Option<String>)> {
        let class_name = class
            .name
            .and_then(|name| declaration_name_text(self.arena, name))?;
        let expression = class
            .heritage_clauses
            .as_ref()?
            .nodes
            .iter()
            .find_map(|clause| {
                let NodeData::HeritageClause(clause) = &self.arena.get(*clause)?.data else {
                    return None;
                };
                if clause.token != SyntaxKind::ExtendsKeyword {
                    return None;
                }
                let heritage = clause.types.nodes.first()?;
                let NodeData::ExpressionWithTypeArguments(heritage) =
                    &self.arena.get(*heritage)?.data
                else {
                    return None;
                };
                Some(heritage.expression)
            })?;
        let (type_id, argument) = match self.arena.get(expression).map(|node| &node.data) {
            Some(NodeData::CallExpression(call)) => self.parsed_heritage_call(call)?,
            Some(NodeData::Identifier(_) | NodeData::PropertyAccessExpression(_)) => {
                self.recovered_heritage_call(expression)?
            }
            _ => (self.node_types?.get(&expression).copied()?, None),
        };
        let name = self.generate_declaration_name(&format!("{class_name}_base"));
        Some((name, type_id, expression, argument))
    }

    fn parsed_heritage_call(
        &self,
        call: &ts_ast::CallExpressionData,
    ) -> Option<(TypeId, Option<String>)> {
        let function_type = self.node_types?.get(&call.expression).copied()?;
        let TypeKind::Function(signature) = &self.semantic_types?.get(function_type)?.kind else {
            return None;
        };
        let argument = match call.arguments.nodes.as_slice() {
            [argument] => declaration_name_text(self.arena, *argument).map(str::to_owned),
            _ => None,
        };
        Some((signature.return_type, argument))
    }

    fn recovered_heritage_call(&self, expression: NodeId) -> Option<(TypeId, Option<String>)> {
        let argument = self.raw_heritage_argument(expression)?;
        let function_type = self.node_types?.get(&expression).copied()?;
        let TypeKind::Function(signature) = &self.semantic_types?.get(function_type)?.kind else {
            return None;
        };
        Some((signature.return_type, Some(argument)))
    }

    fn raw_heritage_argument(&self, expression: NodeId) -> Option<String> {
        let end = usize::try_from(self.arena.get(expression)?.range.end.get()).ok()?;
        let argument = self
            .source_text
            .get(end..)?
            .trim_start()
            .strip_prefix('(')?
            .split_once(')')?
            .0
            .trim();
        (!argument.is_empty() && is_identifier_text(argument)).then(|| argument.to_owned())
    }

    fn emit_synthetic_base_type(
        &mut self,
        type_id: TypeId,
        argument: Option<&str>,
    ) -> Result<(), EmitError> {
        let Some(kind) = self
            .semantic_types
            .and_then(|types| types.get(type_id))
            .map(|type_| type_.kind.clone())
        else {
            return self.emit_semantic_type(type_id);
        };
        match kind {
            TypeKind::Intersection(members) => {
                let mut members = members;
                if argument.is_some() {
                    members.sort_by_key(|member| {
                        matches!(
                            self.semantic_types
                                .and_then(|types| types.get(*member))
                                .map(|type_| &type_.kind),
                            Some(TypeKind::TypeParameter { .. })
                        )
                    });
                }
                for (index, member) in members.iter().enumerate() {
                    if index != 0 {
                        self.writer.write(" & ");
                    }
                    self.emit_synthetic_base_type(*member, argument)?;
                }
                Ok(())
            }
            TypeKind::TypeParameter { .. } if argument.is_some() => {
                self.writer.write("typeof ");
                self.writer.write(argument.unwrap());
                Ok(())
            }
            _ => self.emit_semantic_type(type_id),
        }
    }

    fn class_has_recovered_constructor(&self, class: &ts_ast::ClassDeclarationData) -> bool {
        if !class.members.nodes.is_empty() {
            return false;
        }
        let Some(expression) = class.heritage_clauses.as_ref().and_then(|clauses| {
            clauses.nodes.iter().find_map(|clause| {
                let NodeData::HeritageClause(clause) = &self.arena.get(*clause)?.data else {
                    return None;
                };
                let heritage = clause.types.nodes.first()?;
                let NodeData::ExpressionWithTypeArguments(heritage) =
                    &self.arena.get(*heritage)?.data
                else {
                    return None;
                };
                Some(heritage.expression)
            })
        }) else {
            return false;
        };
        let Some(end) = self
            .arena
            .get(expression)
            .and_then(|node| usize::try_from(node.range.end.get()).ok())
        else {
            return false;
        };
        self.recovered_heritage_call(expression).is_some()
            && self
                .source_text
                .get(end..)
                .is_some_and(|tail| tail.contains("constructor("))
    }

    fn import_is_only_used_by_synthesized_declarations(
        &self,
        import_id: NodeId,
        import: &ts_ast::ImportDeclarationData,
    ) -> bool {
        let Some(NodeData::ImportClause(clause)) = import
            .import_clause
            .and_then(|clause| self.arena.get(clause))
            .map(|node| &node.data)
        else {
            return false;
        };
        let mut names = Vec::new();
        if let Some(name) = clause
            .name
            .and_then(|name| declaration_name_text(self.arena, name))
        {
            names.push(name.to_owned());
        }
        if let Some(bindings) = clause.named_bindings {
            match self.arena.get(bindings).map(|node| &node.data) {
                Some(NodeData::NamedImports(imports)) => {
                    names.extend(imports.elements.nodes.iter().filter_map(|specifier| {
                        let NodeData::ImportSpecifier(specifier) =
                            &self.arena.get(*specifier)?.data
                        else {
                            return None;
                        };
                        declaration_name_text(self.arena, specifier.name).map(str::to_owned)
                    }));
                }
                Some(NodeData::NamespaceImport(namespace)) => {
                    if let Some(name) = declaration_name_text(self.arena, namespace.name) {
                        names.push(name.to_owned());
                    }
                }
                _ => {}
            }
        }
        !names.is_empty()
            && names.iter().all(|name| {
                let uses = self
                    .arena
                    .iter()
                    .filter(|(_, node)| {
                        matches!(&node.data, NodeData::Identifier(identifier) if identifier.text == *name)
                    })
                    .map(|(id, _)| id)
                    .filter(|id| !self.node_is_within(*id, import_id))
                    .collect::<Vec<_>>();
                !uses.is_empty()
                    && uses
                        .iter()
                        .all(|use_| self.identifier_use_is_synthesized(*use_))
            })
    }

    fn identifier_use_is_synthesized(&self, identifier: NodeId) -> bool {
        if self.arena.iter().any(|(_, node)| {
            let NodeData::ClassDeclaration(class) = &node.data else {
                return false;
            };
            self.identifier_is_recovered_heritage_call(identifier, class)
        }) {
            return true;
        }
        if self.arena.iter().any(|(_, node)| {
            let NodeData::ClassDeclaration(class) = &node.data else {
                return false;
            };
            self.identifier_is_in_complex_heritage(identifier, class)
        }) {
            return true;
        }
        let mut current = identifier;
        while let Some(parent) = self.arena.get(current).and_then(|node| node.parent) {
            match &self.arena.get(parent).map(|node| &node.data) {
                Some(NodeData::ExportAssignment(export))
                    if !export.is_export_equals
                        && self
                            .synthesized_expression_type(export.expression)
                            .is_some() =>
                {
                    return true;
                }
                Some(NodeData::ExpressionWithTypeArguments(heritage))
                    if !matches!(
                        self.arena.get(heritage.expression).map(|node| &node.data),
                        Some(NodeData::Identifier(_) | NodeData::PropertyAccessExpression(_))
                    ) =>
                {
                    return true;
                }
                Some(NodeData::ClassDeclaration(class))
                    if self.identifier_is_in_complex_heritage(identifier, class) =>
                {
                    return true;
                }
                Some(NodeData::SourceFile(_)) => return false,
                _ => current = parent,
            }
        }
        false
    }

    fn identifier_is_recovered_heritage_call(
        &self,
        identifier: NodeId,
        class: &ts_ast::ClassDeclarationData,
    ) -> bool {
        class.heritage_clauses.as_ref().is_some_and(|clauses| {
            clauses.nodes.iter().any(|clause| {
                let Some(NodeData::HeritageClause(clause)) =
                    self.arena.get(*clause).map(|node| &node.data)
                else {
                    return false;
                };
                clause.types.nodes.iter().any(|heritage| {
                    let Some(NodeData::ExpressionWithTypeArguments(heritage)) =
                        self.arena.get(*heritage).map(|node| &node.data)
                    else {
                        return false;
                    };
                    heritage.expression == identifier
                        && self.raw_heritage_argument(heritage.expression).is_some()
                })
            })
        })
    }

    fn identifier_is_in_complex_heritage(
        &self,
        identifier: NodeId,
        class: &ts_ast::ClassDeclarationData,
    ) -> bool {
        class.heritage_clauses.as_ref().is_some_and(|clauses| {
            clauses.nodes.iter().any(|clause| {
                let Some(NodeData::HeritageClause(clause)) =
                    self.arena.get(*clause).map(|node| &node.data)
                else {
                    return false;
                };
                clause.types.nodes.iter().any(|heritage| {
                    let Some(NodeData::ExpressionWithTypeArguments(heritage)) =
                        self.arena.get(*heritage).map(|node| &node.data)
                    else {
                        return false;
                    };
                    !matches!(
                        self.arena.get(heritage.expression).map(|node| &node.data),
                        Some(NodeData::Identifier(_) | NodeData::PropertyAccessExpression(_))
                    ) && self.node_range_contains(heritage.expression, identifier)
                })
            })
        })
    }

    fn node_is_within(&self, node: NodeId, ancestor: NodeId) -> bool {
        let mut current = Some(node);
        while let Some(id) = current {
            if id == ancestor {
                return true;
            }
            current = self.arena.get(id).and_then(|node| node.parent);
        }
        false
    }

    fn node_range_contains(&self, ancestor: NodeId, node: NodeId) -> bool {
        let Some(ancestor) = self.arena.get(ancestor) else {
            return false;
        };
        let Some(node) = self.arena.get(node) else {
            return false;
        };
        ancestor.range.start <= node.range.start && node.range.end <= ancestor.range.end
    }

    fn emit_function_semantic_return_type(
        &mut self,
        function: &ts_ast::FunctionDeclarationData,
        return_type: TypeId,
    ) -> Result<(), EmitError> {
        let kind = self
            .semantic_types
            .and_then(|types| types.get(return_type))
            .map(|type_| type_.kind.clone());
        if let Some(TypeKind::Intersection(mut members)) = kind.clone()
            && function
                .body
                .and_then(|body| self.returned_class_expression(body))
                .is_some()
        {
            members.sort_by_key(|member| {
                matches!(
                    self.semantic_types
                        .and_then(|types| types.get(*member))
                        .map(|type_| &type_.kind),
                    Some(TypeKind::TypeParameter { .. })
                )
            });
            return self.emit_semantic_type_list(&members, " & ");
        }
        let Some(TypeKind::Constructor(signature)) = kind else {
            return self.emit_semantic_type(return_type);
        };
        let parameter_names = function
            .body
            .and_then(|body| self.returned_class_expression(body))
            .and_then(|class| self.class_expression_constructor_parameter_names(class));
        self.emit_semantic_constructor_type(&signature, parameter_names.as_deref())
    }

    fn returned_class_expression(&self, body: NodeId) -> Option<&ts_ast::ClassExpressionData> {
        let NodeData::Block(block) = &self.arena.get(body)?.data else {
            return None;
        };
        block.statements.nodes.iter().find_map(|statement| {
            let NodeData::ReturnStatement(return_) = &self.arena.get(*statement)?.data else {
                return None;
            };
            let expression = return_.expression?;
            let NodeData::ClassExpression(class) = &self.arena.get(expression)?.data else {
                return None;
            };
            Some(class.as_ref())
        })
    }

    fn class_expression_constructor_parameter_names(
        &self,
        class: &ts_ast::ClassExpressionData,
    ) -> Option<Vec<String>> {
        if let Some(parameters) =
            class
                .members
                .nodes
                .iter()
                .find_map(|member| match &self.arena.get(*member)?.data {
                    NodeData::ConstructorDeclaration(constructor) => Some(&constructor.parameters),
                    NodeData::MethodDeclaration(method)
                        if declaration_name_text(self.arena, method.name)
                            == Some("constructor") =>
                    {
                        Some(&method.parameters)
                    }
                    _ => None,
                })
        {
            return Some(self.parameter_names(parameters));
        }
        let base_name = class
            .heritage_clauses
            .as_ref()?
            .nodes
            .iter()
            .find_map(|clause| {
                let NodeData::HeritageClause(clause) = &self.arena.get(*clause)?.data else {
                    return None;
                };
                let heritage = clause.types.nodes.first()?;
                let NodeData::ExpressionWithTypeArguments(heritage) =
                    &self.arena.get(*heritage)?.data
                else {
                    return None;
                };
                declaration_name_text(self.arena, heritage.expression)
            })?;
        self.arena.iter().find_map(|(_, node)| {
            let NodeData::ClassDeclaration(class) = &node.data else {
                return None;
            };
            if class
                .name
                .and_then(|name| declaration_name_text(self.arena, name))
                != Some(base_name)
            {
                return None;
            }
            class.members.nodes.iter().find_map(|member| {
                let parameters = match &self.arena.get(*member)?.data {
                    NodeData::ConstructorDeclaration(constructor) => &constructor.parameters,
                    NodeData::MethodDeclaration(method)
                        if declaration_name_text(self.arena, method.name)
                            == Some("constructor") =>
                    {
                        &method.parameters
                    }
                    _ => return None,
                };
                Some(self.parameter_names(parameters))
            })
        })
    }

    fn parameter_names(&self, parameters: &NodeList) -> Vec<String> {
        parameters
            .nodes
            .iter()
            .enumerate()
            .map(|(index, parameter)| {
                let Some(NodeData::ParameterDeclaration(parameter)) =
                    self.arena.get(*parameter).map(|node| &node.data)
                else {
                    return format!("arg{index}");
                };
                declaration_name_text(self.arena, parameter.name)
                    .map_or_else(|| format!("arg{index}"), str::to_owned)
            })
            .collect()
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
        let declarations = data
            .declarations
            .nodes
            .iter()
            .copied()
            .filter(|declaration| {
                let Some(NodeData::VariableDeclaration(declaration)) =
                    self.arena.get(*declaration).map(|node| &node.data)
                else {
                    return true;
                };
                self.binding_name_has_identifier(declaration.name)
            })
            .collect::<Vec<_>>();
        for (index, declaration) in declarations.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            let declaration_id = *declaration;
            let declaration_node = self.node(declaration_id)?.clone();
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
            } else if let Some(type_name) = declaration
                .initializer
                .and_then(|initializer| self.known_new_expression_type(initializer))
            {
                self.writer.write(": ");
                self.writer.write(&type_name);
            } else if let Some(type_id) = self
                .node_types
                .and_then(|types| types.get(&declaration_id).copied())
            {
                if keyword != "const"
                    || !self.emit_semantic_const_initializer(type_id, declaration.initializer)?
                {
                    self.writer.write(": ");
                    self.emit_semantic_type(type_id)?;
                }
            } else {
                self.writer.write(": any");
            }
        }
        Ok(())
    }

    fn variable_list_has_bound_names(&self, list: NodeId) -> bool {
        let Some(NodeData::VariableDeclarationList(list)) =
            self.arena.get(list).map(|node| &node.data)
        else {
            return true;
        };
        list.declarations.nodes.iter().any(|declaration| {
            let Some(NodeData::VariableDeclaration(declaration)) =
                self.arena.get(*declaration).map(|node| &node.data)
            else {
                return true;
            };
            self.binding_name_has_identifier(declaration.name)
        })
    }

    fn binding_name_has_identifier(&self, name: NodeId) -> bool {
        match self.arena.get(name).map(|node| &node.data) {
            Some(NodeData::Identifier(_)) => true,
            Some(NodeData::BindingPattern(pattern)) => {
                pattern.elements.nodes.iter().any(|element| {
                    let Some(NodeData::BindingElement(element)) =
                        self.arena.get(*element).map(|node| &node.data)
                    else {
                        return false;
                    };
                    element
                        .name
                        .is_some_and(|name| self.binding_name_has_identifier(name))
                })
            }
            _ => false,
        }
    }

    fn known_new_expression_type(&self, initializer: NodeId) -> Option<String> {
        let Some(NodeData::NewExpression(new_expression)) =
            self.arena.get(initializer).map(|node| &node.data)
        else {
            return None;
        };
        if declaration_name_text(self.arena, new_expression.expression) != Some("DataView") {
            return None;
        }
        let buffer_type = new_expression
            .arguments
            .as_ref()
            .and_then(|arguments| arguments.nodes.first())
            .and_then(|argument| self.arena.get(*argument))
            .and_then(|argument| match &argument.data {
                NodeData::NewExpression(buffer) => {
                    declaration_name_text(self.arena, buffer.expression)
                }
                _ => None,
            })
            .unwrap_or("ArrayBufferLike");
        Some(format!("DataView<{buffer_type}>"))
    }

    fn emit_semantic_const_initializer(
        &mut self,
        type_id: TypeId,
        initializer: Option<NodeId>,
    ) -> Result<bool, EmitError> {
        let Some(kind) = self
            .semantic_types
            .and_then(|types| types.get(type_id))
            .map(|type_| type_.kind.clone())
        else {
            return Ok(false);
        };
        if !matches!(
            kind,
            TypeKind::BooleanLiteral(_)
                | TypeKind::NumberLiteral(_)
                | TypeKind::StringLiteral(_)
                | TypeKind::BigIntLiteral(_)
        ) {
            return Ok(false);
        }
        self.writer.write(" = ");
        if let Some(initializer) = initializer
            && self.is_enum_member_initializer(initializer)
        {
            self.emit_enum_member_initializer(initializer)?;
        } else {
            match kind {
                TypeKind::BooleanLiteral(value) => {
                    self.writer.write(if value { "true" } else { "false" });
                }
                TypeKind::NumberLiteral(value) | TypeKind::BigIntLiteral(value) => {
                    self.writer.write(&value);
                }
                TypeKind::StringLiteral(value) => write_quoted(&mut self.writer, &value),
                _ => unreachable!("literal kind checked above"),
            }
        }
        Ok(true)
    }

    fn is_enum_member_initializer(&self, id: NodeId) -> bool {
        let receiver = match self.arena.get(id).map(|node| &node.data) {
            Some(NodeData::PropertyAccessExpression(access)) => access.expression,
            Some(NodeData::ElementAccessExpression(access)) => access.expression,
            _ => return false,
        };
        let Some(name) = declaration_name_text(self.arena, receiver) else {
            return false;
        };
        self.arena.iter().any(|(_, node)| {
            let NodeData::EnumDeclaration(enumeration) = &node.data else {
                return false;
            };
            declaration_name_text(self.arena, enumeration.name) == Some(name)
        })
    }

    fn emit_enum_member_initializer(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        match &node.data {
            NodeData::PropertyAccessExpression(access) => {
                self.emit_name(access.expression)?;
                self.writer.write(".");
                self.emit_name(access.name)?;
            }
            NodeData::ElementAccessExpression(access) => {
                self.emit_name(access.expression)?;
                self.writer.write("[");
                self.emit_literal_expression(access.argument_expression)?;
                self.writer.write("]");
            }
            _ => return Err(Self::unsupported(id, node.kind)),
        }
        Ok(())
    }

    fn emit_javascript_object_namespaces(
        &mut self,
        statement: &Node,
        list: NodeId,
    ) -> Result<bool, EmitError> {
        if !self.javascript_source {
            return Ok(false);
        }
        let Some(NodeData::VariableDeclarationList(list)) =
            self.arena.get(list).map(|node| &node.data)
        else {
            return Ok(false);
        };
        let declarations = list.declarations.nodes.clone();
        if declarations.is_empty()
            || declarations.iter().any(|declaration| {
                !matches!(
                    self.arena.get(*declaration).map(|node| &node.data),
                    Some(NodeData::VariableDeclaration(declaration))
                        if matches!(
                            declaration
                                .initializer
                                .and_then(|initializer| self.arena.get(initializer))
                                .map(|node| &node.data),
                            Some(NodeData::ObjectLiteralExpression(_))
                        )
                )
            })
        {
            return Ok(false);
        }
        for (index, declaration_id) in declarations.iter().enumerate() {
            if index != 0 {
                self.writer.newline();
            }
            self.emit_javascript_object_namespace(
                *declaration_id,
                declaration_has_modifier(self.arena, statement, SyntaxKind::ExportKeyword),
            )?;
        }
        Ok(true)
    }

    fn is_javascript_object_namespace_statement(&self, statement: NodeId) -> bool {
        if !self.javascript_source {
            return false;
        }
        let Some(NodeData::VariableStatement(statement)) =
            self.arena.get(statement).map(|node| &node.data)
        else {
            return false;
        };
        let Some(NodeData::VariableDeclarationList(list)) = self
            .arena
            .get(statement.declaration_list)
            .map(|node| &node.data)
        else {
            return false;
        };
        !list.declarations.nodes.is_empty()
            && list.declarations.nodes.iter().all(|declaration| {
                matches!(
                    self.arena.get(*declaration).map(|node| &node.data),
                    Some(NodeData::VariableDeclaration(declaration))
                        if matches!(
                            declaration
                                .initializer
                                .and_then(|initializer| self.arena.get(initializer))
                                .map(|node| &node.data),
                            Some(NodeData::ObjectLiteralExpression(_))
                        )
                )
            })
    }

    fn javascript_object_namespace_requires_deferral(&self, statement: NodeId) -> bool {
        if !self.is_javascript_object_namespace_statement(statement) {
            return false;
        }
        let Some(NodeData::VariableStatement(statement)) =
            self.arena.get(statement).map(|node| &node.data)
        else {
            return false;
        };
        let Some(NodeData::VariableDeclarationList(list)) = self
            .arena
            .get(statement.declaration_list)
            .map(|node| &node.data)
        else {
            return false;
        };
        list.declarations.nodes.iter().any(|declaration| {
            let Some(NodeData::VariableDeclaration(declaration)) =
                self.arena.get(*declaration).map(|node| &node.data)
            else {
                return false;
            };
            let Some(NodeData::ObjectLiteralExpression(object)) = declaration
                .initializer
                .and_then(|initializer| self.arena.get(initializer))
                .map(|node| &node.data)
            else {
                return false;
            };
            object.properties.nodes.iter().any(|property| {
                let Some(NodeData::PropertyAssignment(property)) =
                    self.arena.get(*property).map(|node| &node.data)
                else {
                    return false;
                };
                matches!(
                    self.arena.get(property.initializer).map(|node| &node.data),
                    Some(NodeData::ArrowFunction(_) | NodeData::FunctionExpression(_))
                )
            })
        })
    }

    #[allow(clippy::too_many_lines)]
    fn emit_javascript_object_namespace(
        &mut self,
        declaration_id: NodeId,
        exported: bool,
    ) -> Result<(), EmitError> {
        let declaration_node = self.node(declaration_id)?.clone();
        let NodeData::VariableDeclaration(declaration) = &declaration_node.data else {
            return Err(Self::unsupported(declaration_id, declaration_node.kind));
        };
        let initializer = declaration
            .initializer
            .expect("object namespace declarations have initializers");
        let object_node = self.node(initializer)?.clone();
        let NodeData::ObjectLiteralExpression(object) = &object_node.data else {
            return Err(Self::unsupported(initializer, object_node.kind));
        };
        let semantic_object = self
            .node_types
            .and_then(|types| types.get(&declaration_id).copied())
            .and_then(|type_id| self.semantic_types?.get(type_id))
            .and_then(|type_| match &type_.kind {
                TypeKind::Object(object) => Some(object.clone()),
                _ => None,
            })
            .unwrap_or_default();
        self.writer.write(if exported {
            "export namespace "
        } else {
            "declare namespace "
        });
        self.emit_name(declaration.name)?;
        self.writer.write(" {");
        self.writer.newline();
        self.writer.indent += 1;

        let mut accessor_halves = HashMap::<String, (bool, bool)>::new();
        for property in &object.properties.nodes {
            let Some(node) = self.arena.get(*property) else {
                continue;
            };
            let (name, getter, setter) = match &node.data {
                NodeData::GetAccessorDeclaration(accessor) => (accessor.name, true, false),
                NodeData::SetAccessorDeclaration(accessor) => (accessor.name, false, true),
                _ => continue,
            };
            let Some(name) = declaration_name_text(self.arena, name) else {
                continue;
            };
            let entry = accessor_halves.entry(name.to_owned()).or_default();
            entry.0 |= getter;
            entry.1 |= setter;
        }

        let mut emitted = HashSet::new();
        for property in &object.properties.nodes {
            let Some(node) = self.arena.get(*property) else {
                continue;
            };
            let (name_node, getter_only, function_initializer) = match &node.data {
                NodeData::PropertyAssignment(property) => {
                    let function_initializer = matches!(
                        self.arena.get(property.initializer).map(|node| &node.data),
                        Some(NodeData::ArrowFunction(_) | NodeData::FunctionExpression(_))
                    )
                    .then_some(property.initializer);
                    (property.name, false, function_initializer)
                }
                NodeData::ShorthandPropertyAssignment(property) => (property.name, false, None),
                NodeData::GetAccessorDeclaration(accessor) => {
                    let Some(name) = declaration_name_text(self.arena, accessor.name) else {
                        continue;
                    };
                    let halves = accessor_halves.get(name).copied().unwrap_or_default();
                    (accessor.name, halves.0 && !halves.1, None)
                }
                NodeData::SetAccessorDeclaration(accessor) => (accessor.name, false, None),
                _ => continue,
            };
            let Some(exported_name) = declaration_name_text(self.arena, name_node) else {
                continue;
            };
            if !emitted.insert(exported_name.to_owned()) {
                continue;
            }
            let local_name = self.generate_declaration_name(exported_name);
            let renamed = local_name != exported_name;
            let semantic_type = semantic_object
                .properties
                .get(exported_name)
                .copied()
                .and_then(|type_id| self.semantic_types?.get(type_id))
                .map(|type_| type_.kind.clone());
            if let (Some(initializer), Some(TypeKind::Function(signature))) =
                (function_initializer, semantic_type.as_ref())
            {
                self.emit_javascript_namespace_function(&local_name, initializer, signature)?;
                if renamed {
                    self.writer.write("export { ");
                    self.writer.write(&local_name);
                    self.writer.write(" as ");
                    self.emit_semantic_property_name(exported_name);
                    self.writer.write(" };");
                    self.writer.newline();
                }
                continue;
            }
            let paired_accessor = accessor_halves
                .get(exported_name)
                .is_some_and(|(getter, setter)| *getter && *setter);
            if paired_accessor && !renamed {
                self.writer.write("export ");
            }
            self.writer
                .write(if getter_only { "const " } else { "let " });
            self.writer.write(&local_name);
            self.writer.write(": ");
            if let Some(type_id) = semantic_object.properties.get(exported_name) {
                self.emit_semantic_type(*type_id)?;
            } else {
                self.writer.write("any");
            }
            self.writer.write(";");
            self.writer.newline();
            if renamed {
                self.writer.write("export { ");
                self.writer.write(&local_name);
                self.writer.write(" as ");
                self.emit_semantic_property_name(exported_name);
                self.writer.write(" };");
                self.writer.newline();
            }
        }
        self.writer.indent -= 1;
        self.writer.write("}");
        Ok(())
    }

    fn emit_javascript_namespace_function(
        &mut self,
        name: &str,
        initializer: NodeId,
        signature: &FunctionType,
    ) -> Result<(), EmitError> {
        let initializer_node = self.node(initializer)?.clone();
        let parameters = match &initializer_node.data {
            NodeData::ArrowFunction(function) => function.parameters.clone(),
            NodeData::FunctionExpression(function) => function.parameters.clone(),
            _ => return Err(Self::unsupported(initializer, initializer_node.kind)),
        };
        self.writer.write("function ");
        self.writer.write(name);
        self.writer.write("(");
        for (index, parameter) in parameters.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            let node = self.node(*parameter)?.clone();
            let NodeData::ParameterDeclaration(parameter) = &node.data else {
                return Err(Self::unsupported(*parameter, node.kind));
            };
            self.emit_name(parameter.name)?;
            self.writer.write(": ");
            if let Some(type_id) = signature.parameters.get(index) {
                self.emit_semantic_type(*type_id)?;
            } else {
                self.writer.write("any");
            }
        }
        self.writer.write("): ");
        self.emit_semantic_type(signature.return_type)?;
        self.writer.write(";");
        self.writer.newline();
        Ok(())
    }

    fn generate_declaration_name(&mut self, preferred: &str) -> String {
        if self.generated_names.insert(preferred.to_owned()) {
            return preferred.to_owned();
        }
        let mut index = 1_u32;
        loop {
            let candidate = format!("{preferred}_{index}");
            if self.generated_names.insert(candidate.clone()) {
                return candidate;
            }
            index += 1;
        }
    }

    fn semantic_function_signature(&self, declaration: NodeId) -> Option<FunctionType> {
        let type_id = self.node_types?.get(&declaration)?;
        match &self.semantic_types?.get(*type_id)?.kind {
            TypeKind::Function(signature) => Some(signature.clone()),
            TypeKind::Overload(signatures) => signatures.first().cloned(),
            _ => None,
        }
    }

    fn emit_declaration_parameters(
        &mut self,
        parameters: &NodeList,
        signature: &FunctionType,
        declaration: NodeId,
    ) -> Result<(), EmitError> {
        self.writer.write("(");
        for (index, parameter_id) in parameters.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            let node = self.node(*parameter_id)?.clone();
            let NodeData::ParameterDeclaration(parameter) = &node.data else {
                return Err(Self::unsupported(*parameter_id, node.kind));
            };
            if parameter.dot_dot_dot_token.is_some() {
                self.writer.write("...");
            }
            self.emit_name(parameter.name)?;
            let type_id = signature.parameters.get(index).copied();
            let optional = parameter.question_token.is_some()
                || parameter.initializer.is_some()
                || type_id.is_some_and(|type_id| self.semantic_type_includes_undefined(type_id));
            if optional && parameter.dot_dot_dot_token.is_none() {
                self.writer.write("?");
            }
            self.writer.write(": ");
            if let Some(hint) = self.jsdoc_parameter_type_hint(declaration, parameter.name) {
                self.writer.write(&hint);
            } else if let Some(type_id) = type_id {
                self.emit_semantic_parameter_type(type_id, optional)?;
            } else if let Some(type_) = parameter.type_ {
                self.emit_type(type_)?;
            } else {
                self.writer.write("any");
            }
        }
        if let Some(rest) = signature.rest_parameter
            && !parameters.nodes.iter().any(|parameter| {
                matches!(
                    self.arena.get(*parameter).map(|node| &node.data),
                    Some(NodeData::ParameterDeclaration(parameter))
                        if parameter.dot_dot_dot_token.is_some()
                )
            })
        {
            if !parameters.nodes.is_empty() {
                self.writer.write(", ");
            }
            self.writer.write("...args: ");
            self.emit_semantic_type(rest)?;
        }
        self.writer.write(")");
        Ok(())
    }

    fn emit_semantic_parameter_type(
        &mut self,
        type_id: TypeId,
        omit_undefined: bool,
    ) -> Result<(), EmitError> {
        let members = self
            .semantic_types
            .and_then(|types| types.get(type_id))
            .and_then(|type_| match &type_.kind {
                TypeKind::Union(members) if omit_undefined => Some(members.clone()),
                _ => None,
            });
        let Some(members) = members else {
            return self.emit_semantic_type(type_id);
        };
        let members = members
            .into_iter()
            .filter(|member| !self.semantic_type_is_undefined(*member))
            .collect::<Vec<_>>();
        if members.is_empty() {
            self.writer.write("undefined");
            Ok(())
        } else {
            self.emit_semantic_type_list(&members, " | ")
        }
    }

    fn semantic_type_includes_undefined(&self, type_id: TypeId) -> bool {
        self.semantic_type_is_undefined(type_id)
            || matches!(
                self.semantic_types
                    .and_then(|types| types.get(type_id))
                    .map(|type_| &type_.kind),
                Some(TypeKind::Union(members))
                    if members.iter().any(|member| self.semantic_type_is_undefined(*member))
            )
    }

    fn semantic_type_is_undefined(&self, type_id: TypeId) -> bool {
        matches!(
            self.semantic_types
                .and_then(|types| types.get(type_id))
                .map(|type_| &type_.kind),
            Some(TypeKind::Undefined)
        )
    }

    fn leading_jsdoc_comment(&self, node: NodeId) -> Option<&str> {
        if !self.javascript_source {
            return None;
        }
        let start = usize::try_from(self.arena.get(node)?.range.start.get()).ok()?;
        let prefix = self.source_text.get(..start)?.trim_end();
        if !prefix.ends_with("*/") {
            return None;
        }
        let start = prefix.rfind("/**")?;
        Some(&prefix[start..])
    }

    fn emit_leading_jsdoc(&mut self, node: NodeId) {
        let Some(comment) = self.leading_jsdoc_comment(node).map(str::to_owned) else {
            return;
        };
        for (index, line) in comment.lines().enumerate() {
            if index != 0 {
                self.writer.write(" ");
            }
            self.writer.write(line.trim_start());
            self.writer.newline();
        }
    }

    fn jsdoc_parameter_type_hint(&self, declaration: NodeId, name: NodeId) -> Option<String> {
        let name = declaration_name_text(self.arena, name)?;
        let comment = self.leading_jsdoc_comment(declaration)?;
        comment.lines().find_map(|line| {
            let tag = line
                .trim()
                .trim_start_matches("/**")
                .trim_start_matches('*')
                .trim()
                .trim_end_matches("*/")
                .trim()
                .strip_prefix("@param")?
                .trim_start();
            let tag = tag.strip_prefix('{')?;
            let end = tag.find('}')?;
            let type_name = tag[..end].trim();
            let raw_name = tag[end + 1..].split_whitespace().next()?;
            let parameter_name = raw_name
                .trim_matches(['[', ']'])
                .split_once('=')
                .map_or_else(|| raw_name.trim_matches(['[', ']']), |(name, _)| name);
            (parameter_name == name).then(|| type_name.to_owned())
        })
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
        self.emit_leading_jsdoc(id);
        match &node.data {
            NodeData::PropertyDeclaration(data) => {
                self.emit_declaration_member_modifiers(data.modifiers.as_ref());
                self.emit_name(data.name)?;
                if data.postfix_token.is_some() {
                    self.writer.write("?");
                }
                if !self.member_has_modifier(data.modifiers.as_ref(), SyntaxKind::PrivateKeyword) {
                    self.writer.write(": ");
                    if let Some(type_) = data.type_ {
                        self.emit_type(type_)?;
                    } else if let Some(type_id) = data
                        .initializer
                        .and_then(|initializer| self.node_types?.get(&initializer).copied())
                    {
                        self.emit_widened_semantic_type(type_id)?;
                    } else {
                        self.writer.write("any");
                    }
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
                if declaration_name_text(self.arena, data.name) == Some("constructor") {
                    self.writer.write("constructor");
                    if let Some(signature) = self.semantic_function_signature(id) {
                        self.emit_declaration_parameters(&data.parameters, &signature, id)?;
                    } else {
                        self.emit_parameters(&data.parameters)?;
                    }
                    self.writer.write(";");
                    self.writer.newline();
                    return Ok(());
                }
                self.emit_name(data.name)?;
                if data.postfix_token.is_some() {
                    self.writer.write("?");
                }
                self.emit_type_parameters(data.type_parameters.as_ref())?;
                if let Some(signature) = self.semantic_function_signature(id) {
                    self.emit_declaration_parameters(&data.parameters, &signature, id)?;
                    self.writer.write(": ");
                    self.emit_semantic_type(signature.return_type)?;
                } else {
                    self.emit_parameters(&data.parameters)?;
                    self.emit_return_type(data.type_)?;
                }
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
                if let Some(signature) = self.semantic_function_signature(id) {
                    self.emit_declaration_parameters(&data.parameters, &signature, id)?;
                } else {
                    self.emit_parameters(&data.parameters)?;
                }
                self.writer.write(";");
            }
            NodeData::GetAccessorDeclaration(data) => {
                self.writer.write("get ");
                self.emit_name(data.name)?;
                self.emit_parameters(&data.parameters)?;
                if data.type_.is_none()
                    && let Some(type_id) = self.node_types.and_then(|types| types.get(&id).copied())
                {
                    self.writer.write(": ");
                    self.emit_semantic_type(type_id)?;
                } else {
                    self.emit_return_type(data.type_)?;
                }
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

    fn emit_javascript_instance_properties(
        &mut self,
        class_id: NodeId,
        member_id: NodeId,
    ) -> Result<(), EmitError> {
        if !self.javascript_source {
            return Ok(());
        }
        let class_type = self
            .node_types
            .and_then(|types| types.get(&class_id).copied())
            .and_then(|type_id| self.semantic_types?.get(type_id))
            .and_then(|type_| match &type_.kind {
                TypeKind::Object(object) => Some(object.clone()),
                _ => None,
            });
        let Some(class_type) = class_type else {
            return Ok(());
        };
        let body = match self.arena.get(member_id).map(|node| &node.data) {
            Some(NodeData::ConstructorDeclaration(constructor)) => constructor.body,
            Some(NodeData::MethodDeclaration(method)) => method.body,
            _ => None,
        };
        let Some(body) = body else {
            return Ok(());
        };
        let mut assignments = self
            .arena
            .iter()
            .filter_map(|(id, node)| {
                self.node_is_within(id, body)
                    .then_some((id, node.range.start.get(), &node.data))
            })
            .filter_map(|(id, start, data)| {
                let NodeData::BinaryExpression(assignment) = data else {
                    return None;
                };
                (self.arena.get(assignment.operator_token)?.kind == SyntaxKind::EqualsToken)
                    .then(|| self.javascript_this_property_name(assignment.left))
                    .flatten()
                    .map(|name| (id, start, name))
            })
            .collect::<Vec<_>>();
        assignments.sort_by_key(|(_, start, _)| *start);
        for (assignment, _, name) in assignments {
            if !self
                .emitted_javascript_class_properties
                .insert((class_id, name.clone()))
            {
                continue;
            }
            let Some(type_id) = class_type.properties.get(&name).copied() else {
                continue;
            };
            self.emit_leading_jsdoc(assignment);
            self.emit_semantic_property_name(&name);
            self.writer.write(": ");
            if let Some(hint) = self.jsdoc_type_hint(assignment) {
                self.writer.write(&hint);
            } else {
                self.emit_semantic_type(type_id)?;
            }
            if class_type.optional_properties.contains(&name) {
                self.writer.write(" | undefined");
            }
            self.writer.write(";");
            self.writer.newline();
        }
        Ok(())
    }

    fn javascript_this_property_name(&self, expression: NodeId) -> Option<String> {
        match &self.arena.get(expression)?.data {
            NodeData::PropertyAccessExpression(access)
                if self
                    .arena
                    .get(access.expression)
                    .is_some_and(|node| node.kind == SyntaxKind::ThisKeyword) =>
            {
                declaration_name_text(self.arena, access.name).map(str::to_owned)
            }
            NodeData::ElementAccessExpression(access)
                if self
                    .arena
                    .get(access.expression)
                    .is_some_and(|node| node.kind == SyntaxKind::ThisKeyword) =>
            {
                declaration_name_text(self.arena, access.argument_expression).map(str::to_owned)
            }
            _ => None,
        }
    }

    fn jsdoc_type_hint(&self, node: NodeId) -> Option<String> {
        self.leading_jsdoc_comment(node)?.lines().find_map(|line| {
            let tag = line
                .trim()
                .trim_start_matches("/**")
                .trim_start_matches('*')
                .trim()
                .trim_end_matches("*/")
                .trim()
                .strip_prefix("@type")?
                .trim();
            Some(
                tag.strip_prefix('{')
                    .and_then(|tag| tag.strip_suffix('}'))
                    .unwrap_or(tag)
                    .trim()
                    .to_owned(),
            )
        })
    }

    fn emit_constructor_parameter_properties(
        &mut self,
        members: &NodeList,
    ) -> Result<(), EmitError> {
        let parameters =
            members
                .nodes
                .iter()
                .find_map(|member| match &self.arena.get(*member)?.data {
                    NodeData::ConstructorDeclaration(constructor) => {
                        Some(constructor.parameters.clone())
                    }
                    NodeData::MethodDeclaration(method)
                        if declaration_name_text(self.arena, method.name)
                            == Some("constructor") =>
                    {
                        Some(method.parameters.clone())
                    }
                    _ => None,
                });
        let Some(parameters) = parameters else {
            return Ok(());
        };
        for parameter_id in &parameters.nodes {
            let parameter_node = self.node(*parameter_id)?.clone();
            let NodeData::ParameterDeclaration(parameter) = &parameter_node.data else {
                continue;
            };
            let is_parameter_property = parameter.modifiers.as_ref().is_some_and(|modifiers| {
                modifiers.list.nodes.iter().any(|modifier| {
                    self.arena.get(*modifier).is_some_and(|modifier| {
                        matches!(
                            modifier.kind,
                            SyntaxKind::PublicKeyword
                                | SyntaxKind::ProtectedKeyword
                                | SyntaxKind::PrivateKeyword
                                | SyntaxKind::ReadonlyKeyword
                        )
                    })
                })
            });
            if !is_parameter_property {
                continue;
            }
            let private =
                self.member_has_modifier(parameter.modifiers.as_ref(), SyntaxKind::PrivateKeyword);
            for (kind, text) in [
                (SyntaxKind::ProtectedKeyword, "protected "),
                (SyntaxKind::PrivateKeyword, "private "),
                (SyntaxKind::ReadonlyKeyword, "readonly "),
            ] {
                if self.member_has_modifier(parameter.modifiers.as_ref(), kind) {
                    self.writer.write(text);
                }
            }
            self.emit_name(parameter.name)?;
            if parameter.question_token.is_some() {
                self.writer.write("?");
            }
            if !private {
                self.writer.write(": ");
                if let Some(type_) = parameter.type_ {
                    self.emit_type(type_)?;
                } else {
                    self.writer.write("any");
                }
            }
            self.writer.write(";");
            self.writer.newline();
        }
        Ok(())
    }

    fn emit_widened_semantic_type(&mut self, type_id: TypeId) -> Result<(), EmitError> {
        match self
            .semantic_types
            .and_then(|types| types.get(type_id))
            .map(|type_| &type_.kind)
        {
            Some(TypeKind::BooleanLiteral(_)) => self.writer.write("boolean"),
            Some(TypeKind::NumberLiteral(_)) => self.writer.write("number"),
            Some(TypeKind::StringLiteral(_)) => self.writer.write("string"),
            Some(TypeKind::BigIntLiteral(_)) => self.writer.write("bigint"),
            _ => self.emit_semantic_type(type_id)?,
        }
        Ok(())
    }

    fn emit_declaration_member_modifiers(&mut self, modifiers: Option<&ts_ast::ModifierList>) {
        let Some(modifiers) = modifiers else {
            return;
        };
        for modifier in &modifiers.list.nodes {
            let Some(kind) = self.arena.get(*modifier).map(|node| node.kind) else {
                continue;
            };
            let text = match kind {
                SyntaxKind::PublicKeyword => "public ",
                SyntaxKind::ProtectedKeyword => "protected ",
                SyntaxKind::PrivateKeyword => "private ",
                SyntaxKind::StaticKeyword => "static ",
                SyntaxKind::AbstractKeyword => "abstract ",
                SyntaxKind::ReadonlyKeyword => "readonly ",
                SyntaxKind::OverrideKeyword => "override ",
                SyntaxKind::AccessorKeyword => "accessor ",
                _ => continue,
            };
            self.writer.write(text);
        }
    }

    fn member_has_modifier(
        &self,
        modifiers: Option<&ts_ast::ModifierList>,
        kind: SyntaxKind,
    ) -> bool {
        modifiers.is_some_and(|modifiers| {
            modifiers.list.nodes.iter().any(|modifier| {
                self.arena
                    .get(*modifier)
                    .is_some_and(|node| node.kind == kind)
            })
        })
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

    fn emit_semantic_type(&mut self, id: TypeId) -> Result<(), EmitError> {
        if let Some(reference) = self
            .import_type_references
            .and_then(|references| references.get(&id))
        {
            self.writer.write("import(");
            write_quoted(&mut self.writer, &reference.module_specifier);
            self.writer.write(")");
            if reference.qualifier != "export=" && !reference.qualifier.is_empty() {
                self.writer.write(".");
                self.writer.write(&reference.qualifier);
            }
            return Ok(());
        }
        let Some(kind) = self
            .semantic_types
            .and_then(|types| types.get(id))
            .map(|type_| type_.kind.clone())
        else {
            self.writer.write("any");
            return Ok(());
        };
        match kind {
            TypeKind::Any => self.writer.write("any"),
            TypeKind::Unknown => self.writer.write("unknown"),
            TypeKind::Never => self.writer.write("never"),
            TypeKind::Void => self.writer.write("void"),
            TypeKind::Undefined => self.writer.write("undefined"),
            TypeKind::Null => self.writer.write("null"),
            TypeKind::Boolean => self.writer.write("boolean"),
            TypeKind::Number => self.writer.write("number"),
            TypeKind::String => self.writer.write("string"),
            TypeKind::BigInt => self.writer.write("bigint"),
            TypeKind::BooleanLiteral(value) => {
                self.writer.write(if value { "true" } else { "false" });
            }
            TypeKind::NumberLiteral(value) | TypeKind::BigIntLiteral(value) => {
                self.writer.write(&value);
            }
            TypeKind::StringLiteral(value) => write_quoted(&mut self.writer, &value),
            TypeKind::Object(object) => self.emit_semantic_object_type(&object)?,
            TypeKind::TypeParameter { name, .. } => self.writer.write(&name),
            TypeKind::Array(element) => {
                self.emit_semantic_type(element)?;
                self.writer.write("[]");
            }
            TypeKind::Tuple(elements) => {
                self.writer.write("[");
                self.emit_semantic_type_list(&elements, ", ")?;
                self.writer.write("]");
            }
            TypeKind::Union(members) => self.emit_semantic_type_list(&members, " | ")?,
            TypeKind::Intersection(members) => self.emit_semantic_type_list(&members, " & ")?,
            TypeKind::Function(signature) => self.emit_semantic_function_type(&signature)?,
            TypeKind::Constructor(signature) => {
                self.emit_semantic_constructor_type(&signature, None)?;
            }
            TypeKind::Overload(signatures) => {
                for (index, signature) in signatures.iter().enumerate() {
                    if index != 0 {
                        self.writer.write(" | ");
                    }
                    self.emit_semantic_function_type(signature)?;
                }
            }
        }
        Ok(())
    }

    fn emit_semantic_type_list(
        &mut self,
        types: &[TypeId],
        separator: &str,
    ) -> Result<(), EmitError> {
        for (index, type_id) in types.iter().enumerate() {
            if index != 0 {
                self.writer.write(separator);
            }
            self.emit_semantic_type(*type_id)?;
        }
        Ok(())
    }

    fn emit_semantic_function_type(&mut self, signature: &FunctionType) -> Result<(), EmitError> {
        self.writer.write("(");
        self.emit_semantic_parameters(signature, None)?;
        self.writer.write(") => ");
        self.emit_semantic_type(signature.return_type)
    }

    fn emit_semantic_constructor_type(
        &mut self,
        signature: &FunctionType,
        parameter_names: Option<&[String]>,
    ) -> Result<(), EmitError> {
        self.writer.write("{");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("new (");
        self.emit_semantic_parameters(signature, parameter_names)?;
        self.writer.write("): ");
        if let Some(TypeKind::Object(object)) = self
            .semantic_types
            .and_then(|types| types.get(signature.return_type))
            .map(|type_| type_.kind.clone())
        {
            self.emit_semantic_object_type_with_methods(&object, true)?;
        } else {
            self.emit_semantic_type(signature.return_type)?;
        }
        self.writer.write(";");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("}");
        Ok(())
    }

    fn emit_semantic_parameters(
        &mut self,
        signature: &FunctionType,
        parameter_names: Option<&[String]>,
    ) -> Result<(), EmitError> {
        for (index, parameter) in signature.parameters.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            let rest = signature.parameters.len() == 1
                && matches!(
                    self.semantic_types
                        .and_then(|types| types.get(*parameter))
                        .map(|type_| &type_.kind),
                    Some(TypeKind::Array(_))
                );
            if rest {
                self.writer.write("...");
            }
            if let Some(name) = parameter_names.and_then(|names| names.get(index)) {
                self.writer.write(name);
            } else if rest {
                self.writer.write("args");
            } else {
                self.writer.write("arg");
                self.writer.write(&index.to_string());
            }
            self.writer.write(": ");
            self.emit_semantic_type(*parameter)?;
        }
        Ok(())
    }

    fn emit_semantic_object_type(&mut self, object: &ObjectType) -> Result<(), EmitError> {
        self.emit_semantic_object_type_with_methods(object, false)
    }

    fn emit_semantic_object_type_with_methods(
        &mut self,
        object: &ObjectType,
        methods: bool,
    ) -> Result<(), EmitError> {
        self.writer.write("{");
        if !object.properties.is_empty() {
            self.writer.newline();
            self.writer.indent += 1;
            for (name, type_id) in &object.properties {
                if object.readonly_properties.contains(name) {
                    self.writer.write("readonly ");
                }
                self.emit_semantic_property_name(name);
                if object.optional_properties.contains(name) {
                    self.writer.write("?");
                }
                let function = self
                    .semantic_types
                    .and_then(|types| types.get(*type_id))
                    .and_then(|type_| match &type_.kind {
                        TypeKind::Function(signature) if methods => Some(signature.clone()),
                        _ => None,
                    });
                if let Some(signature) = function {
                    self.writer.write("(");
                    self.emit_semantic_parameters(&signature, None)?;
                    self.writer.write("): ");
                    self.emit_semantic_type(signature.return_type)?;
                } else {
                    self.writer.write(": ");
                    self.emit_semantic_type(*type_id)?;
                }
                self.writer.write(";");
                self.writer.newline();
            }
            self.writer.indent -= 1;
        }
        self.writer.write("}");
        Ok(())
    }

    fn emit_semantic_property_name(&mut self, name: &str) {
        if is_identifier_text(name) {
            self.writer.write(name);
        } else {
            write_quoted(&mut self.writer, name);
        }
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
            NodeData::BigIntLiteral(data) => self.writer.write(&data.text.to_ascii_lowercase()),
            NodeData::ComputedPropertyName(data) => {
                self.writer.write("[");
                self.emit_literal_expression(data.expression)?;
                self.writer.write("]");
            }
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
            NodeData::BigIntLiteral(data) => self.writer.write(&data.text.to_ascii_lowercase()),
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
        if retained.iter().any(|statement| {
            matches!(
                self.arena.get(*statement).map(|node| &node.data),
                Some(NodeData::ExportAssignment(_))
            )
        }) {
            return false;
        }
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
        | NodeData::ExportAssignment(_)
        | NodeData::NotEmittedStatement(_) => true,
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
            .and_then(|symbol| bindings.symbols.get(symbol));
        let resolved_name = match resolved_name {
            Some(symbol) if symbol.flags.contains(ts_binder::SymbolFlags::CONST_ENUM) => {
                symbol.name.as_str()
            }
            Some(_) => continue,
            None => receiver_name,
        };
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
        NodeData::StringLiteral(literal) => Some(&literal.text),
        NodeData::NumericLiteral(literal) => Some(&literal.text),
        NodeData::ComputedPropertyName(computed) => {
            declaration_name_text(arena, computed.expression)
        }
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

fn is_identifier_text(text: &str) -> bool {
    let mut characters = text.chars();
    characters
        .next()
        .is_some_and(|character| character == '_' || character == '$' || character.is_alphabetic())
        && characters
            .all(|character| character == '_' || character == '$' || character.is_alphanumeric())
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
    fn is_empty(&self) -> bool {
        self.output.is_empty()
    }

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
        self.newline_preserving_trailing_spaces();
    }

    fn newline_preserving_trailing_spaces(&mut self) {
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

    fn ends_with_tight_comment_delimiter(&self) -> bool {
        matches!(self.output.as_bytes().last(), Some(b'(' | b'['))
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

struct AmdImportInitializer {
    parameter: String,
    helper: &'static str,
}

struct SystemModulePlan {
    export_function: String,
    context_object: String,
    dependencies: Vec<SystemDependency>,
    hoisted_names: Vec<String>,
    identifier_rewrites: HashMap<ts_ast::SymbolId, String>,
    exported_bindings: HashMap<ts_ast::SymbolId, String>,
    hoisted_functions: Vec<NodeId>,
}

#[derive(Clone)]
struct Es5AsyncCapturedLoop {
    prelude: Vec<NodeId>,
    loop_variable: String,
    initializer: NodeId,
    condition: NodeId,
    incrementor: NodeId,
    awaited: NodeId,
    after_await: Vec<NodeId>,
    control: Es5AsyncLoopControl,
}

#[derive(Clone)]
struct Es5GeneratorForOf {
    loop_variable: String,
    iterable: NodeId,
    before_yield: Vec<NodeId>,
    yielded: NodeId,
}

#[derive(Clone, Copy)]
enum Es5AsyncLoopControl {
    None,
    Break,
    Continue,
    Return(NodeId),
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

    fn claim(&mut self, preferred: &str) -> Option<String> {
        self.used
            .insert(preferred.to_owned())
            .then(|| preferred.to_owned())
    }

    fn generate_temp(&mut self) -> String {
        let mut suffix = 0_u32;
        loop {
            for letter in b'a'..=b'z' {
                let base = format!("_{}", char::from(letter));
                let candidate = if suffix == 0 {
                    base
                } else {
                    format!("{base}_{suffix}")
                };
                if self.used.insert(candidate.clone()) {
                    return candidate;
                }
            }
            suffix += 1;
        }
    }

    fn generate_loop_variable(&mut self) -> String {
        self.claim("_i").unwrap_or_else(|| self.generate_temp())
    }
}

#[derive(Clone)]
enum DownlevelBindingValue {
    Node(NodeId),
    Name(String),
    Element(Box<Self>, DownlevelBindingIndex),
    Slice(Box<Self>, usize),
    VoidZero,
}

#[derive(Clone)]
enum DownlevelBindingIndex {
    Number(usize),
    Name(String),
}

impl SystemModulePlan {
    #[allow(clippy::too_many_lines)]
    fn analyze(
        arena: &NodeArena,
        bindings: &BindResult,
        data: &ts_ast::SourceFileData,
        import_runtime_meanings: &BTreeMap<NodeId, bool>,
    ) -> Self {
        let mut names = GeneratedNames::new(arena);
        let export_function = names.generate("exports");
        let context_object = names.generate("context");
        let mut dependencies = Vec::new();
        let mut hoisted_names = Vec::new();
        let mut identifier_rewrites = HashMap::new();
        let mut exported_bindings = HashMap::new();
        let mut hoisted_functions = Vec::new();
        for statement in &data.statements.nodes {
            if import_runtime_meanings.get(statement) == Some(&false) {
                continue;
            }
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
                    if declaration_has_modifier(arena, node, SyntaxKind::ExportKeyword)
                        && let Some(NodeData::VariableDeclarationList(list)) =
                            arena.get(statement.declaration_list).map(|node| &node.data)
                    {
                        for declaration in &list.declarations.nodes {
                            let declaration_id = *declaration;
                            let Some(NodeData::VariableDeclaration(declaration)) =
                                arena.get(declaration_id).map(|node| &node.data)
                            else {
                                continue;
                            };
                            let Some(name) = declaration_name_text(arena, declaration.name) else {
                                continue;
                            };
                            if let Some(symbol) = bindings.node_symbols.get(&declaration_id) {
                                exported_bindings.insert(*symbol, name.to_owned());
                            }
                        }
                    }
                }
                NodeData::FunctionDeclaration(function) if function.body.is_some() => {
                    hoisted_functions.push(*statement);
                }
                NodeData::ClassDeclaration(class)
                    if !declaration_has_modifier(arena, node, SyntaxKind::DeclareKeyword) =>
                {
                    if let Some(name_id) = class.name
                        && let Some(name) = declaration_name_text(arena, name_id)
                    {
                        push_unique(&mut hoisted_names, name);
                        if declaration_has_modifier(arena, node, SyntaxKind::ExportKeyword)
                            && let Some(symbol) = bindings.node_symbols.get(&name_id)
                        {
                            exported_bindings.insert(*symbol, name.to_owned());
                        }
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
        let mut nested_var_names = arena
            .iter()
            .filter_map(|(id, node)| {
                let NodeData::VariableStatement(statement) = &node.data else {
                    return None;
                };
                let list = arena.get(statement.declaration_list)?;
                if list.flags.0 & 3 != 0 || !is_source_file_var_declaration(arena, id) {
                    return None;
                }
                Some((
                    node.range.start,
                    simple_variable_names(arena, statement.declaration_list),
                ))
            })
            .collect::<Vec<_>>();
        nested_var_names.sort_by_key(|(start, _)| *start);
        for (_, names) in nested_var_names {
            for name in names {
                push_unique(&mut hoisted_names, &name);
            }
        }
        Self {
            export_function,
            context_object,
            dependencies,
            hoisted_names,
            identifier_rewrites,
            exported_bindings,
            hoisted_functions,
        }
    }
}

fn is_source_file_var_declaration(arena: &NodeArena, mut node: NodeId) -> bool {
    while let Some(parent) = arena.get(node).and_then(|node| node.parent) {
        let Some(parent_node) = arena.get(parent) else {
            return false;
        };
        if matches!(
            parent_node.data,
            NodeData::FunctionDeclaration(_)
                | NodeData::FunctionExpression(_)
                | NodeData::ArrowFunction(_)
                | NodeData::MethodDeclaration(_)
                | NodeData::ConstructorDeclaration(_)
                | NodeData::GetAccessorDeclaration(_)
                | NodeData::SetAccessorDeclaration(_)
        ) {
            return false;
        }
        if matches!(parent_node.data, NodeData::SourceFile(_)) {
            return true;
        }
        node = parent;
    }
    false
}

fn node_is_in_nested_function(arena: &NodeArena, mut node: NodeId, body: NodeId) -> bool {
    let mut nested_function = false;
    while let Some(parent) = arena.get(node).and_then(|node| node.parent) {
        if parent == body {
            return nested_function;
        }
        let Some(parent_node) = arena.get(parent) else {
            return false;
        };
        nested_function |= matches!(
            parent_node.data,
            NodeData::FunctionDeclaration(_)
                | NodeData::FunctionExpression(_)
                | NodeData::ArrowFunction(_)
                | NodeData::MethodDeclaration(_)
                | NodeData::ConstructorDeclaration(_)
                | NodeData::GetAccessorDeclaration(_)
                | NodeData::SetAccessorDeclaration(_)
        );
        node = parent;
    }
    false
}

const fn variable_list_is_block_scoped(node: &Node) -> bool {
    node.flags.0 & 3 != 0
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
        if !declaration_has_modifier(arena, node, SyntaxKind::ExportKeyword) {
            continue;
        }
        match &node.data {
            NodeData::ImportEqualsDeclaration(import) => {
                let Some(name) = declaration_name_text(arena, import.name) else {
                    continue;
                };
                if let Some(symbol) = bindings.node_symbols.get(statement) {
                    rewrites.insert(*symbol, format!("{container}.{name}"));
                }
            }
            NodeData::VariableStatement(variable) => {
                let Some(NodeData::VariableDeclarationList(list)) =
                    arena.get(variable.declaration_list).map(|node| &node.data)
                else {
                    continue;
                };
                for declaration_id in &list.declarations.nodes {
                    let Some(NodeData::VariableDeclaration(declaration)) =
                        arena.get(*declaration_id).map(|node| &node.data)
                    else {
                        continue;
                    };
                    let Some(name) = declaration_name_text(arena, declaration.name) else {
                        continue;
                    };
                    if let Some(symbol) = bindings.node_symbols.get(&declaration.name) {
                        rewrites.insert(*symbol, format!("{container}.{name}"));
                    }
                }
            }
            _ => {}
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum AsyncExpressionTransform {
    None,
    AwaitAsYield,
    AsyncGenerator,
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
    generated_names: GeneratedNames,
    runtime_identifier_uses: HashSet<String>,
    commonjs_default_imports: HashMap<String, String>,
    commonjs_named_import_temps: HashMap<NodeId, String>,
    has_runtime_export_equals: bool,
    bindings: &'a BindResult,
    identifier_rewrites: HashMap<ts_ast::SymbolId, String>,
    system_predeclared_names: HashSet<String>,
    system_export_function: Option<String>,
    system_exported_bindings: HashMap<ts_ast::SymbolId, String>,
    commonjs_module_transform: bool,
    enum_member_values: &'a BTreeMap<NodeId, EmitConstantValue>,
    enum_access_values: &'a BTreeMap<NodeId, EmitConstantValue>,
    import_runtime_meanings: &'a BTreeMap<NodeId, bool>,
    const_enum_emit_mode: ConstEnumEmitMode,
    enum_access_fallbacks: HashMap<NodeId, EmitConstantValue>,
    emitted_source_comments: HashSet<(usize, usize)>,
    class_expression_temps: HashMap<NodeId, String>,
    async_expression_transform: AsyncExpressionTransform,
    async_loop_counter: u32,
    async_control_counter: u32,
    commonjs_empty_binding_temps: HashMap<NodeId, Vec<String>>,
    commonjs_empty_binding_hoists: Vec<String>,
}

impl Printer<'_> {
    #[allow(clippy::too_many_lines)]
    fn emit_amd_source_file(
        &mut self,
        data: &ts_ast::SourceFileData,
        context: &EmitContext<'_>,
    ) -> Result<EmitResult, EmitError> {
        self.commonjs_module_transform = true;
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
        let mut side_effect_dependencies = Vec::new();
        let mut import_initializers = Vec::new();
        let mut generated_names = GeneratedNames::new(self.arena);
        for statement in &data.statements.nodes {
            match self.arena.get(*statement).map(|node| &node.data) {
                Some(NodeData::ImportEqualsDeclaration(import)) => {
                    if !self.import_semantically_has_runtime_value(*statement)
                        || import.is_type_only
                        || (!self
                            .has_modifier(import.modifiers.as_ref(), SyntaxKind::ExportKeyword)
                            && !self.import_binding_is_used(import.name))
                    {
                        continue;
                    }
                    let Some(path) =
                        external_module_reference_text(self.arena, import.module_reference)
                    else {
                        continue;
                    };
                    dependencies.push(AmdRuntimeDependency {
                        path: amd_import_dependency_path(path, context.amd_bundle),
                        parameter: Some(self.identifier_text(import.name)?.to_owned()),
                    });
                }
                Some(NodeData::ImportDeclaration(import)) => {
                    if !self.import_semantically_has_runtime_value(*statement) {
                        continue;
                    }
                    let Some(path) = string_literal_text(self.arena, import.module_specifier)
                    else {
                        continue;
                    };
                    let Some(clause_id) = import.import_clause else {
                        side_effect_dependencies.push(AmdRuntimeDependency {
                            path: amd_import_dependency_path(path, context.amd_bundle),
                            parameter: None,
                        });
                        continue;
                    };
                    if !self.import_has_runtime_use(*statement, import) {
                        continue;
                    }
                    let Some(NodeData::ImportClause(clause)) =
                        self.arena.get(clause_id).map(|node| &node.data)
                    else {
                        continue;
                    };
                    let namespace = clause.named_bindings.and_then(|bindings| {
                        let NodeData::NamespaceImport(namespace) = &self.arena.get(bindings)?.data
                        else {
                            return None;
                        };
                        self.import_binding_is_used(namespace.name)
                            .then_some(namespace.name)
                    });
                    let parameter = if let Some(namespace) = namespace {
                        self.identifier_text(namespace)?.to_owned()
                    } else {
                        generated_names.generate(&commonjs_module_temp_base(
                            self.arena,
                            import.module_specifier,
                        ))
                    };
                    if let Some(default) = clause.name
                        && self.import_binding_is_used(default)
                    {
                        let local = self.identifier_text(default)?.to_owned();
                        self.commonjs_default_imports
                            .insert(local, parameter.clone());
                        import_initializers.push(AmdImportInitializer {
                            parameter: parameter.clone(),
                            helper: "__importDefault",
                        });
                    }
                    if let Some(bindings) = clause.named_bindings {
                        match self.arena.get(bindings).map(|node| &node.data) {
                            Some(NodeData::NamespaceImport(_)) if namespace.is_some() => {
                                import_initializers.push(AmdImportInitializer {
                                    parameter: parameter.clone(),
                                    helper: "__importStar",
                                });
                            }
                            Some(NodeData::NamedImports(imports)) => {
                                for specifier_id in &imports.elements.nodes {
                                    let Some(NodeData::ImportSpecifier(specifier)) =
                                        self.arena.get(*specifier_id).map(|node| &node.data)
                                    else {
                                        continue;
                                    };
                                    if specifier.is_type_only
                                        || !self.import_binding_is_used(specifier.name)
                                    {
                                        continue;
                                    }
                                    let imported = specifier
                                        .property_name
                                        .and_then(|name| declaration_name_text(self.arena, name))
                                        .or_else(|| {
                                            declaration_name_text(self.arena, specifier.name)
                                        });
                                    let Some(imported) = imported else {
                                        continue;
                                    };
                                    if imported == "default" {
                                        let Some(local) =
                                            declaration_name_text(self.arena, specifier.name)
                                        else {
                                            continue;
                                        };
                                        self.commonjs_default_imports
                                            .insert(local.to_owned(), parameter.clone());
                                        import_initializers.push(AmdImportInitializer {
                                            parameter: parameter.clone(),
                                            helper: "__importDefault",
                                        });
                                    } else if let Some(symbol) =
                                        self.bindings.node_symbols.get(&specifier.name)
                                    {
                                        self.identifier_rewrites
                                            .insert(*symbol, format!("{parameter}.{imported}"));
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                    dependencies.push(AmdRuntimeDependency {
                        path: amd_import_dependency_path(path, context.amd_bundle),
                        parameter: Some(parameter),
                    });
                }
                _ => {}
            }
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
        dependencies.extend(side_effect_dependencies);

        if data.statements.nodes.iter().all(|statement| {
            self.arena
                .get(*statement)
                .is_none_or(|node| !self.statement_emits_runtime(*statement, node))
        }) && let Some(first_statement) = data.statements.nodes.first()
            && let Some(node) = self.arena.get(*first_statement)
        {
            self.emit_detached_reference_directives_between(0, node.range.start.get());
        }

        for dependency in context.amd_dependencies {
            let start = usize::try_from(dependency.comment_start).unwrap_or(usize::MAX);
            let end = usize::try_from(dependency.comment_end).unwrap_or(usize::MAX);
            if let Some(comment) = self.source_text.get(start..end) {
                self.writer.write(comment);
                self.writer.newline();
            }
        }
        if source_needs_import_star_helper(
            self.arena,
            &data.statements,
            &self.runtime_identifier_uses,
            context.import_runtime_meanings,
        ) {
            self.emit_create_binding_helper();
            self.emit_import_star_helper();
        }
        if !self.commonjs_default_imports.is_empty() {
            self.emit_import_default_helper();
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
        if self.settings.target < ScriptTarget::Es2015 && source_needs_extends_helper(self.arena) {
            self.emit_extends_helper();
        }
        let export_equals_expression =
            runtime_export_equals_expression(self.arena, &data.statements);
        self.has_runtime_export_equals = export_equals_expression.is_some();
        if export_equals_expression.is_none() {
            self.writer
                .write("Object.defineProperty(exports, \"__esModule\", { value: true });");
            self.writer.newline();
        }
        let preinitialized_exports = self.commonjs_preinitialized_export_names(&data.statements);
        if !preinitialized_exports.is_empty() {
            for name in preinitialized_exports.iter().rev() {
                self.writer.write("exports.");
                self.writer.write(name);
                self.writer.write(" = ");
            }
            self.writer.write("void 0;");
            self.writer.newline();
        }
        if export_equals_expression.is_none() {
            for statement in &data.statements.nodes {
                let Some(node) = self.arena.get(*statement) else {
                    continue;
                };
                let NodeData::FunctionDeclaration(function) = &node.data else {
                    continue;
                };
                if function.body.is_none()
                    || !declaration_has_modifier(self.arena, node, SyntaxKind::ExportKeyword)
                {
                    continue;
                }
                let Some(name) = function
                    .name
                    .and_then(|name| declaration_name_text(self.arena, name))
                else {
                    continue;
                };
                self.writer.write("exports.");
                self.writer.write(name);
                self.writer.write(" = ");
                self.writer.write(name);
                self.writer.write(";");
                self.writer.newline();
            }
        }
        for initializer in &import_initializers {
            self.writer.write(&initializer.parameter);
            self.writer.write(" = ");
            self.writer.write(initializer.helper);
            self.writer.write("(");
            self.writer.write(&initializer.parameter);
            self.writer.write(");");
            self.writer.newline();
        }
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
        self.emit_automatic_jsx_prelude();
        let mut previous_end = data
            .statements
            .nodes
            .first()
            .and_then(|statement| self.arena.get(*statement))
            .map_or(0, |node| node.range.start.get());
        let mut reference_owner_start = 0;
        let mut previous_emitted = false;
        for statement in &data.statements.nodes {
            if let Some(node) = self.arena.get(*statement) {
                let current_owns_source_comments = self.statement_emits_in_place(*statement, node);
                if current_owns_source_comments {
                    self.emit_source_comments_between(previous_end, node.range.start.get());
                }
                if self.statement_emits_runtime(*statement, node)
                    && !self.import_runtime_meanings.contains_key(statement)
                {
                    self.emit_reference_directives_between(
                        reference_owner_start,
                        node.range.start.get(),
                    );
                }
                previous_end = node.range.end.get();
                reference_owner_start = node.range.end.get();
                previous_emitted = current_owns_source_comments;
            }
            let skip_import = match self.arena.get(*statement).map(|node| &node.data) {
                Some(NodeData::ImportDeclaration(_)) => true,
                Some(NodeData::ImportEqualsDeclaration(import)) => {
                    external_module_reference_text(self.arena, import.module_reference).is_some()
                }
                _ => false,
            };
            if skip_import {
                continue;
            }
            self.emit_statement(*statement)?;
        }
        self.emit_source_comments_between_with_ownership(
            previous_end,
            u32::try_from(self.source_text.len()).unwrap_or(u32::MAX),
            previous_emitted,
            false,
        );
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

    #[allow(clippy::too_many_lines)]
    fn emit_system_source_file(
        &mut self,
        data: &ts_ast::SourceFileData,
    ) -> Result<EmitResult, EmitError> {
        let plan = SystemModulePlan::analyze(
            self.arena,
            self.bindings,
            data,
            self.import_runtime_meanings,
        );
        self.identifier_rewrites = plan.identifier_rewrites;
        self.system_export_function = Some(plan.export_function.clone());
        self.system_exported_bindings = plan.exported_bindings.clone();
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
        let mut previous_function_end = 0;
        for function_id in &plan.hoisted_functions {
            let function_node = self.node(*function_id)?.clone();
            self.emit_source_comments_between_with_trailing(
                previous_function_end,
                function_node.range.start.get(),
                previous_function_end != 0,
            );
            self.emit_statement(*function_id)?;
            if let NodeData::FunctionDeclaration(function) = &function_node.data
                && self.has_modifier(function.modifiers.as_ref(), SyntaxKind::ExportKeyword)
                && let Some(name) = function
                    .name
                    .and_then(|name| declaration_name_text(self.arena, name))
            {
                self.writer.write(&plan.export_function);
                self.writer.write("(");
                write_quoted(&mut self.writer, name);
                self.writer.write(", ");
                self.writer.write(name);
                self.writer.write(");");
                self.writer.newline();
            }
            previous_function_end = function_node.range.end.get();
        }
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
            | NodeData::ExportAssignment(_)
            | NodeData::FunctionDeclaration(_) => Ok(()),
            NodeData::ImportEqualsDeclaration(import) => {
                if !self.import_semantically_has_runtime_value(statement) {
                    return Ok(());
                }
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
                let exported =
                    self.has_modifier(variable.modifiers.as_ref(), SyntaxKind::ExportKeyword);
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
                    let name = declaration_name_text(self.arena, declaration.name);
                    if exported && let Some(name) = name {
                        self.writer.write(export_function);
                        self.writer.write("(");
                        write_quoted(&mut self.writer, name);
                        self.writer.write(", ");
                    }
                    self.emit_expression(declaration.name, 1)?;
                    self.writer.write(" = ");
                    self.emit_expression(initializer, 1)?;
                    if exported && name.is_some() {
                        self.writer.write(")");
                    }
                    self.writer.write(";");
                    self.writer.newline();
                }
                Ok(())
            }
            NodeData::ClassDeclaration(class) => {
                let Some(name_id) = class.name else {
                    return self.emit_statement(statement);
                };
                let name = self.identifier_text(name_id)?.to_owned();
                self.writer.write(&name);
                self.writer.write(" = ");
                self.emit_class(class)?;
                self.writer.write(";");
                self.emit_auto_accessor_storage_initializers(class);
                self.writer.newline();
                if self.has_modifier(class.modifiers.as_ref(), SyntaxKind::ExportKeyword) {
                    let exported_name = if self
                        .has_modifier(class.modifiers.as_ref(), SyntaxKind::DefaultKeyword)
                    {
                        "default"
                    } else {
                        &name
                    };
                    self.writer.write(export_function);
                    self.writer.write("(");
                    write_quoted(&mut self.writer, exported_name);
                    self.writer.write(", ");
                    self.writer.write(&name);
                    self.writer.write(");");
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

    fn emit_reference_directives_between(&mut self, start: u32, end: u32) {
        self.emit_reference_directives_between_with_ownership(start, end, true);
    }

    fn emit_detached_reference_directives_between(&mut self, start: u32, end: u32) {
        self.emit_reference_directives_between_with_ownership(start, end, false);
    }

    fn emit_reference_directives_between_with_ownership(
        &mut self,
        start: u32,
        end: u32,
        include_owned: bool,
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
                let comment = &trivia[index..comment_end];
                if is_reference_directive(comment)
                    && (include_owned || contains_blank_line(&trivia[comment_end..]))
                {
                    self.writer.write(comment);
                    self.writer.newline_preserving_trailing_spaces();
                }
                index = comment_end;
            } else if bytes[index..].starts_with(b"/*") {
                index = bytes[index + 2..]
                    .windows(2)
                    .position(|window| window == b"*/")
                    .map_or(bytes.len(), |offset| index + 2 + offset + 2);
            } else {
                index += 1;
            }
        }
    }

    fn emit_source_comments_between_with_trailing(
        &mut self,
        start: u32,
        end: u32,
        preserve_immediate_trailing: bool,
    ) {
        self.emit_source_comments_between_with_ownership(
            start,
            end,
            preserve_immediate_trailing,
            true,
        );
    }

    fn emit_inline_block_comments_between(
        &mut self,
        start: u32,
        end: u32,
        space_before_first: bool,
    ) {
        if self.settings.remove_comments {
            return;
        }
        let start = usize::try_from(start).unwrap_or(usize::MAX);
        let end = usize::try_from(end).unwrap_or(usize::MAX);
        let Some(trivia) = self.source_text.get(start..end) else {
            return;
        };
        let mut index = 0;
        let mut first = true;
        while let Some(comment_start) = trivia[index..].find("/*") {
            let comment_start = index + comment_start;
            let Some(comment_end) = trivia[comment_start + 2..].find("*/") else {
                break;
            };
            let comment_end = comment_start + 2 + comment_end + 2;
            if self
                .emitted_source_comments
                .insert((start + comment_start, start + comment_end))
            {
                if first && space_before_first {
                    self.writer.write(" ");
                }
                self.writer.write(&trivia[comment_start..comment_end]);
                self.writer.write(" ");
                first = false;
            }
            index = comment_end;
        }
    }

    fn inline_await_leading_comment_start(&self, start: u32, end: u32) -> Option<u32> {
        let start = usize::try_from(start).ok()?;
        let end = usize::try_from(end).ok()?;
        let trivia = self.source_text.get(start..end)?;
        let line_start = trivia
            .rfind(['\n', '\r'])
            .map_or(0, |line_break| line_break + 1);
        let line = &trivia[line_start..];
        let comment_start = line.find("/*")?;
        line[..comment_start]
            .trim()
            .is_empty()
            .then(|| u32::try_from(start + line_start + comment_start).ok())?
    }

    fn emit_source_comments_between_with_ownership(
        &mut self,
        start: u32,
        end: u32,
        preserve_immediate_trailing: bool,
        preserve_leading: bool,
    ) {
        if self.settings.remove_comments {
            return;
        }
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
                let comment = &trivia[index..comment_end];
                if is_reference_directive(comment) {
                    index = comment_end;
                    continue;
                }
                let comment_range = (start + index, start + comment_end);
                let immediate_trailing = !trivia[..index].contains(['\n', '\r']);
                if ((immediate_trailing && preserve_immediate_trailing)
                    || (!immediate_trailing && preserve_leading))
                    && self.emitted_source_comments.insert(comment_range)
                {
                    if immediate_trailing {
                        self.writer.remove_trailing_newline();
                        if !self.writer.ends_with_tight_comment_delimiter() {
                            self.writer.write(" ");
                        }
                    }
                    self.writer.write(&trivia[index..comment_end]);
                    self.writer.newline_preserving_trailing_spaces();
                }
                index = comment_end;
            } else if bytes[index..].starts_with(b"/*") {
                let comment_end = bytes[index + 2..]
                    .windows(2)
                    .position(|window| window == b"*/")
                    .map_or(bytes.len(), |offset| index + 2 + offset + 2);
                let comment_range = (start + index, start + comment_end);
                let immediate_trailing = !trivia[..index].contains(['\n', '\r']);
                if ((immediate_trailing && preserve_immediate_trailing)
                    || (!immediate_trailing && preserve_leading))
                    && self.emitted_source_comments.insert(comment_range)
                {
                    if immediate_trailing {
                        self.writer.remove_trailing_newline();
                        self.writer.write(" ");
                    }
                    let normalized = trivia[index..comment_end]
                        .replace("\r\n", "\n")
                        .replace('\r', "\n");
                    let mut lines = normalized.split('\n').peekable();
                    while let Some(line) = lines.next() {
                        self.writer.write(line);
                        if lines.peek().is_none() && comment_range.1 == self.source_text.len() {
                            self.writer.write(" ");
                        }
                        self.writer.newline_preserving_trailing_spaces();
                    }
                }
                index = comment_end;
            } else {
                index += 1;
            }
        }
    }

    fn emit_leading_source_comments(&mut self, end: u32) {
        self.emit_leading_source_comments_excluding_with_mode(end, &[], false);
    }

    fn emit_leading_detached_source_comments(&mut self, end: u32) {
        let end = usize::try_from(end).unwrap_or(usize::MAX);
        let Some(prefix) = self.source_text.get(..end) else {
            return;
        };
        let bytes = prefix.as_bytes();
        let mut index = 0;
        let mut comment_end = None;
        while index < bytes.len() {
            if bytes[index..].starts_with(b"//") {
                if let Some(last_comment_end) = comment_end
                    && contains_blank_line(&prefix[last_comment_end..index])
                {
                    self.emit_leading_source_comments_excluding_with_mode(
                        u32::try_from(last_comment_end).unwrap_or(u32::MAX),
                        &[],
                        false,
                    );
                    return;
                }
                let end = bytes[index..]
                    .iter()
                    .position(|byte| *byte == b'\n' || *byte == b'\r')
                    .map_or(bytes.len(), |offset| index + offset);
                comment_end = Some(end);
                index = end;
            } else if bytes[index..].starts_with(b"/*") {
                if let Some(last_comment_end) = comment_end
                    && contains_blank_line(&prefix[last_comment_end..index])
                {
                    self.emit_leading_source_comments_excluding_with_mode(
                        u32::try_from(last_comment_end).unwrap_or(u32::MAX),
                        &[],
                        false,
                    );
                    return;
                }
                let end = bytes[index + 2..]
                    .windows(2)
                    .position(|window| window == b"*/")
                    .map_or(bytes.len(), |offset| index + 2 + offset + 2);
                comment_end = Some(end);
                index = end;
            } else {
                index += 1;
            }
        }
        if let Some(last_comment_end) = comment_end
            && contains_blank_line(&prefix[last_comment_end..])
        {
            self.emit_leading_source_comments_excluding_with_mode(
                u32::try_from(last_comment_end).unwrap_or(u32::MAX),
                &[],
                false,
            );
        }
    }

    fn emit_leading_pinned_source_comments(&mut self, end: u32) {
        self.emit_leading_source_comments_excluding_with_mode(end, &[], true);
    }

    fn emit_leading_source_comments_excluding(&mut self, end: u32, excluded: &[(u32, u32)]) {
        self.emit_leading_source_comments_excluding_with_mode(end, excluded, false);
    }

    fn emit_leading_source_comments_excluding_with_mode(
        &mut self,
        end: u32,
        excluded: &[(u32, u32)],
        pinned_only: bool,
    ) {
        if self.settings.remove_comments {
            return;
        }
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
                let comment = &prefix[index..comment_end];
                let comment_range = (index, comment_end);
                let pinned = comment.starts_with("//!")
                    || comment.contains("@license")
                    || is_amd_dependency_directive(comment);
                if (!pinned_only || pinned)
                    && !is_reference_directive(comment)
                    && !excluded.iter().any(|(start, end)| {
                        usize::try_from(*start) == Ok(index)
                            && usize::try_from(*end) == Ok(comment_end)
                    })
                    && self.emitted_source_comments.insert(comment_range)
                {
                    self.writer.write(comment);
                    self.writer.newline_preserving_trailing_spaces();
                }
                index = comment_end;
            } else if bytes[index..].starts_with(b"/*") {
                let comment_end = bytes[index + 2..]
                    .windows(2)
                    .position(|window| window == b"*/")
                    .map_or(bytes.len(), |offset| index + 2 + offset + 2);
                let comment = &prefix[index..comment_end];
                let comment_range = (index, comment_end);
                let pinned = comment.starts_with("/*!") || comment.contains("@license");
                if (!pinned_only || pinned) && self.emitted_source_comments.insert(comment_range) {
                    for line in comment
                        .replace("\r\n", "\n")
                        .replace('\r', "\n")
                        .split('\n')
                    {
                        self.writer.write(line);
                        self.writer.newline_preserving_trailing_spaces();
                    }
                }
                index = comment_end;
            } else {
                index += 1;
            }
        }
    }

    fn emit_create_binding_helper(&mut self) {
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
        ] {
            self.writer.write(line);
            self.writer.newline();
        }
    }

    fn emit_import_star_helper(&mut self) {
        for line in [
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

    fn emit_export_star_helper(&mut self) {
        for line in [
            "var __exportStar = (this && this.__exportStar) || function(m, exports) {",
            "    for (var p in m) if (p !== \"default\" && !Object.prototype.hasOwnProperty.call(exports, p)) __createBinding(exports, m, p);",
            "};",
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

    fn emit_awaiter_helper(&mut self) {
        for line in [
            "var __awaiter = (this && this.__awaiter) || function (thisArg, _arguments, P, generator) {",
            "    function adopt(value) { return value instanceof P ? value : new P(function (resolve) { resolve(value); }); }",
            "    return new (P || (P = Promise))(function (resolve, reject) {",
            "        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }",
            "        function rejected(value) { try { step(generator[\"throw\"](value)); } catch (e) { reject(e); } }",
            "        function step(result) { result.done ? resolve(result.value) : adopt(result.value).then(fulfilled, rejected); }",
            "        step((generator = generator.apply(thisArg, _arguments || [])).next());",
            "    });",
            "};",
        ] {
            self.writer.write(line);
            self.writer.newline();
        }
    }

    fn emit_await_helper(&mut self) {
        self.writer.write(
            "var __await = (this && this.__await) || function (v) { return this instanceof __await ? (this.v = v, this) : new __await(v); }",
        );
        self.writer.newline();
    }

    fn emit_async_generator_helper(&mut self) {
        for line in [
            "var __asyncGenerator = (this && this.__asyncGenerator) || function (thisArg, _arguments, generator) {",
            "    if (!Symbol.asyncIterator) throw new TypeError(\"Symbol.asyncIterator is not defined.\");",
            "    var g = generator.apply(thisArg, _arguments || []), i, q = [];",
            "    return i = Object.create((typeof AsyncIterator === \"function\" ? AsyncIterator : Object).prototype), verb(\"next\"), verb(\"throw\"), verb(\"return\", awaitReturn), i[Symbol.asyncIterator] = function () { return this; }, i;",
            "    function awaitReturn(f) { return function (v) { return Promise.resolve(v).then(f, reject); }; }",
            "    function verb(n, f) { if (g[n]) { i[n] = function (v) { return new Promise(function (a, b) { q.push([n, v, a, b]) > 1 || resume(n, v); }); }; if (f) i[n] = f(i[n]); } }",
            "    function resume(n, v) { try { step(g[n](v)); } catch (e) { settle(q[0][3], e); } }",
            "    function step(r) { r.value instanceof __await ? Promise.resolve(r.value.v).then(fulfill, reject) : settle(q[0][2], r); }",
            "    function fulfill(value) { resume(\"next\", value); }",
            "    function reject(value) { resume(\"throw\", value); }",
            "    function settle(f, v) { if (f(v), q.shift(), q.length) resume(q[0][0], q[0][1]); }",
            "};",
        ] {
            self.writer.write(line);
            self.writer.newline();
        }
    }

    fn emit_generator_helper(&mut self) {
        for line in [
            "var __generator = (this && this.__generator) || function (thisArg, body) {",
            "    var _ = { label: 0, sent: function() { if (t[0] & 1) throw t[1]; return t[1]; }, trys: [], ops: [] }, f, y, t, g = Object.create((typeof Iterator === \"function\" ? Iterator : Object).prototype);",
            "    return g.next = verb(0), g[\"throw\"] = verb(1), g[\"return\"] = verb(2), typeof Symbol === \"function\" && (g[Symbol.iterator] = function() { return this; }), g;",
            "    function verb(n) { return function (v) { return step([n, v]); }; }",
            "    function step(op) {",
            "        if (f) throw new TypeError(\"Generator is already executing.\");",
            "        while (g && (g = 0, op[0] && (_ = 0)), _) try {",
            "            if (f = 1, y && (t = op[0] & 2 ? y[\"return\"] : op[0] ? y[\"throw\"] || ((t = y[\"return\"]) && t.call(y), 0) : y.next) && !(t = t.call(y, op[1])).done) return t;",
            "            if (y = 0, t) op = [op[0] & 2, t.value];",
            "            switch (op[0]) {",
            "                case 0: case 1: t = op; break;",
            "                case 4: _.label++; return { value: op[1], done: false };",
            "                case 5: _.label++; y = op[1]; op = [0]; continue;",
            "                case 7: op = _.ops.pop(); _.trys.pop(); continue;",
            "                default:",
            "                    if (!(t = _.trys, t = t.length > 0 && t[t.length - 1]) && (op[0] === 6 || op[0] === 2)) { _ = 0; continue; }",
            "                    if (op[0] === 3 && (!t || (op[1] > t[0] && op[1] < t[3]))) { _.label = op[1]; break; }",
            "                    if (op[0] === 6 && _.label < t[1]) { _.label = t[1]; t = op; break; }",
            "                    if (t && _.label < t[2]) { _.label = t[2]; _.ops.push(op); break; }",
            "                    if (t[2]) _.ops.pop();",
            "                    _.trys.pop(); continue;",
            "            }",
            "            op = body.call(thisArg, _);",
            "        } catch (e) { op = [6, e]; y = 0; } finally { f = t = 0; }",
            "        if (op[0] & 5) throw op[1]; return { value: op[0] ? op[1] : void 0, done: true };",
            "    }",
            "};",
        ] {
            self.writer.write(line);
            self.writer.newline();
        }
    }

    fn emit_set_function_name_helper(&mut self) {
        for line in [
            "var __setFunctionName = (this && this.__setFunctionName) || function (f, name, prefix) {",
            "    if (typeof name === \"symbol\") name = name.description ? \"[\".concat(name.description, \"]\") : \"\";",
            "    return Object.defineProperty(f, \"name\", { configurable: true, value: prefix ? \"\".concat(prefix, \" \", name) : name });",
            "};",
        ] {
            self.writer.write(line);
            self.writer.newline();
        }
    }

    fn emit_values_helper(&mut self) {
        for line in [
            "var __values = (this && this.__values) || function(o) {",
            "    var s = typeof Symbol === \"function\" && Symbol.iterator, m = s && o[s], i = 0;",
            "    if (m) return m.call(o);",
            "    if (o && typeof o.length === \"number\") return {",
            "        next: function () {",
            "            if (o && i >= o.length) o = void 0;",
            "            return { value: o && o[i++], done: !o };",
            "        }",
            "    };",
            "    throw new TypeError(s ? \"Object is not iterable.\" : \"Symbol.iterator is not defined.\");",
            "};",
        ] {
            self.writer.write(line);
            self.writer.newline();
        }
    }

    fn emit_object_rest_helper(&mut self) {
        for line in [
            "var __rest = (this && this.__rest) || function (s, e) {",
            "    var t = {};",
            "    for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p) && e.indexOf(p) < 0)",
            "        t[p] = s[p];",
            "    if (s != null && typeof Object.getOwnPropertySymbols === \"function\")",
            "        for (var i = 0, p = Object.getOwnPropertySymbols(s); i < p.length; i++) {",
            "            if (e.indexOf(p[i]) < 0 && Object.prototype.propertyIsEnumerable.call(s, p[i]))",
            "                t[p[i]] = s[p[i]];",
            "        }",
            "    return t;",
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

    fn emit_auto_accessor_helpers(&mut self) {
        for line in [
            "var __classPrivateFieldGet = (this && this.__classPrivateFieldGet) || function (receiver, state, kind, f) {",
            "    if (kind === \"a\" && !f) throw new TypeError(\"Private accessor was defined without a getter\");",
            "    if (typeof state === \"function\" ? receiver !== state || !f : !state.has(receiver)) throw new TypeError(\"Cannot read private member from an object whose class did not declare it\");",
            "    return kind === \"m\" ? f : kind === \"a\" ? f.call(receiver) : f ? f.value : state.get(receiver);",
            "};",
            "var __classPrivateFieldSet = (this && this.__classPrivateFieldSet) || function (receiver, state, value, kind, f) {",
            "    if (kind === \"m\") throw new TypeError(\"Private method is not writable\");",
            "    if (kind === \"a\" && !f) throw new TypeError(\"Private accessor was defined without a setter\");",
            "    if (typeof state === \"function\" ? receiver !== state || !f : !state.has(receiver)) throw new TypeError(\"Cannot write private member to an object whose class did not declare it\");",
            "    return (kind === \"a\" ? f.call(receiver, value) : f ? f.value = value : state.set(receiver, value)), value;",
            "};",
        ] {
            self.writer.write(line);
            self.writer.newline();
        }
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

    fn commonjs_preinitialized_export_names(&self, statements: &NodeList) -> Vec<String> {
        let mut names = Vec::new();
        let mut seen = HashSet::new();
        for statement in &statements.nodes {
            let Some(node) = self.arena.get(*statement) else {
                continue;
            };
            if declaration_has_modifier(self.arena, node, SyntaxKind::DeclareKeyword) {
                continue;
            }
            if is_const_enum_declaration(self.arena, node)
                && !self.const_enum_emit_mode.preserves_declarations()
            {
                continue;
            }
            let exported = declaration_has_modifier(self.arena, node, SyntaxKind::ExportKeyword);
            let default_export =
                declaration_has_modifier(self.arena, node, SyntaxKind::DefaultKeyword);
            match &node.data {
                NodeData::ClassDeclaration(class) if exported => {
                    let name = if default_export {
                        Some("default")
                    } else {
                        class
                            .name
                            .and_then(|name| declaration_name_text(self.arena, name))
                    };
                    if let Some(name) = name
                        && seen.insert(name.to_owned())
                    {
                        names.push(name.to_owned());
                    }
                }
                NodeData::EnumDeclaration(enumeration) if exported => {
                    if let Some(name) = declaration_name_text(self.arena, enumeration.name)
                        && seen.insert(name.to_owned())
                    {
                        names.push(name.to_owned());
                    }
                }
                NodeData::VariableStatement(statement) if exported => {
                    let Some(NodeData::VariableDeclarationList(list)) = self
                        .arena
                        .get(statement.declaration_list)
                        .map(|node| &node.data)
                    else {
                        continue;
                    };
                    for declaration in &list.declarations.nodes {
                        let Some(NodeData::VariableDeclaration(declaration)) =
                            self.arena.get(*declaration).map(|node| &node.data)
                        else {
                            continue;
                        };
                        let Some(name) = declaration_name_text(self.arena, declaration.name) else {
                            continue;
                        };
                        if seen.insert(name.to_owned()) {
                            names.push(name.to_owned());
                        }
                    }
                }
                NodeData::ExportDeclaration(export) if export.module_specifier.is_none() => {
                    let Some(NodeData::NamedExports(exports)) = export
                        .export_clause
                        .and_then(|clause| self.arena.get(clause))
                        .map(|node| &node.data)
                    else {
                        continue;
                    };
                    for element in &exports.elements.nodes {
                        let Some(NodeData::ExportSpecifier(specifier)) =
                            self.arena.get(*element).map(|node| &node.data)
                        else {
                            continue;
                        };
                        if specifier.is_type_only
                            || !self.export_specifier_target_has_runtime_value(specifier)
                            || self
                                .commonjs_export_function_declaration(*element)
                                .is_some()
                        {
                            continue;
                        }
                        let Some(name) = declaration_name_text(self.arena, specifier.name) else {
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

    fn export_specifier_target_has_runtime_value(
        &self,
        specifier: &ts_ast::ExportSpecifierData,
    ) -> bool {
        let local = specifier.property_name.unwrap_or(specifier.name);
        let Some(name) = declaration_name_text(self.arena, local) else {
            return false;
        };
        let Some(symbol) = self.bindings.resolve_name_at(local, name) else {
            return false;
        };
        self.symbol_has_runtime_value(symbol, &mut HashSet::new())
    }

    fn statement_emits_runtime(&self, id: NodeId, node: &Node) -> bool {
        if declaration_has_modifier(self.arena, node, SyntaxKind::DeclareKeyword)
            || (is_const_enum_declaration(self.arena, node)
                && !self.const_enum_emit_mode.preserves_declarations())
        {
            return false;
        }
        match &node.data {
            NodeData::ImportDeclaration(import) => self.import_has_runtime_use(id, import),
            NodeData::ImportEqualsDeclaration(import) => {
                if self.is_external_import_equals(import) {
                    self.import_semantically_has_runtime_value(id)
                        && !import.is_type_only
                        && (self.has_modifier(import.modifiers.as_ref(), SyntaxKind::ExportKeyword)
                            || self.import_binding_is_used(import.name))
                } else {
                    !import.is_type_only && self.internal_import_equals_has_runtime_value(import)
                }
            }
            NodeData::NotEmittedStatement(_)
            | NodeData::InterfaceDeclaration(_)
            | NodeData::TypeAliasDeclaration(_) => false,
            NodeData::ExportDeclaration(_) if export_declaration_is_empty(self.arena, node) => {
                false
            }
            NodeData::ExportAssignment(assignment) => {
                self.entity_has_runtime_value(assignment.expression, &mut HashSet::new())
            }
            NodeData::FunctionDeclaration(function) => function.body.is_some(),
            NodeData::ModuleDeclaration(module) => {
                self.namespace_has_runtime_contents(module, &mut HashSet::new())
            }
            NodeData::VariableStatement(statement)
                if self.commonjs_module_transform
                    && declaration_has_modifier(self.arena, node, SyntaxKind::ExportKeyword)
                    && self.variable_list_is_uninitialized(statement.declaration_list) =>
            {
                false
            }
            _ => true,
        }
    }

    fn statement_emits_in_place(&self, id: NodeId, node: &Node) -> bool {
        self.statement_emits_runtime(id, node)
            && !matches!(
                &node.data,
                NodeData::ExportAssignment(assignment) if assignment.is_export_equals
            )
    }

    fn is_external_import_equals(&self, import: &ts_ast::ImportEqualsDeclarationData) -> bool {
        matches!(
            self.arena
                .get(import.module_reference)
                .map(|node| &node.data),
            Some(NodeData::ExternalModuleReference(_))
        )
    }

    fn internal_import_equals_has_runtime_value(
        &self,
        import: &ts_ast::ImportEqualsDeclarationData,
    ) -> bool {
        self.internal_import_equals_has_runtime_value_with_visited(import, &mut HashSet::new())
    }

    fn internal_import_equals_has_runtime_value_with_visited(
        &self,
        import: &ts_ast::ImportEqualsDeclarationData,
        visited: &mut HashSet<SymbolId>,
    ) -> bool {
        if matches!(
            self.arena
                .get(import.module_reference)
                .map(|node| &node.data),
            Some(NodeData::Identifier(identifier)) if identifier.text.is_empty()
        ) {
            return false;
        }
        self.entity_has_runtime_value(import.module_reference, visited)
    }

    fn entity_has_runtime_value(&self, entity: NodeId, visited: &mut HashSet<SymbolId>) -> bool {
        let Some(symbol) = self.resolve_entity_symbol(entity, &mut HashSet::new()) else {
            // Preserve the syntactic fallback for unresolved aliases.
            return true;
        };
        self.symbol_has_runtime_value(symbol, visited)
    }

    fn resolve_entity_symbol(
        &self,
        entity: NodeId,
        visited: &mut HashSet<SymbolId>,
    ) -> Option<SymbolId> {
        match &self.arena.get(entity)?.data {
            NodeData::Identifier(identifier) => {
                self.bindings.resolve_name_at(entity, &identifier.text)
            }
            NodeData::QualifiedName(name) => {
                let left = self.resolve_entity_symbol(name.left, visited)?;
                let left = self.alias_target_symbol(left, visited).unwrap_or(left);
                let right = declaration_name_text(self.arena, name.right)?;
                self.bindings.symbols.get(left)?.members.get(right)
            }
            _ => None,
        }
    }

    fn alias_target_symbol(
        &self,
        symbol: SymbolId,
        visited: &mut HashSet<SymbolId>,
    ) -> Option<SymbolId> {
        if !visited.insert(symbol) {
            return None;
        }
        let symbol = self.bindings.symbols.get(symbol)?;
        if let Some(target) = symbol.target {
            return Some(target);
        }
        symbol.declarations.iter().find_map(|declaration| {
            let NodeData::ImportEqualsDeclaration(import) = &self.arena.get(*declaration)?.data
            else {
                return None;
            };
            self.resolve_entity_symbol(import.module_reference, visited)
        })
    }

    fn symbol_has_runtime_value(&self, symbol: SymbolId, visited: &mut HashSet<SymbolId>) -> bool {
        if !visited.insert(symbol) {
            return false;
        }
        let Some(symbol) = self.bindings.symbols.get(symbol) else {
            return true;
        };
        if let Some(target) = symbol.target {
            return self.symbol_has_runtime_value(target, visited);
        }
        for declaration in &symbol.declarations {
            let Some(node) = self.arena.get(*declaration) else {
                continue;
            };
            match &node.data {
                NodeData::ImportEqualsDeclaration(import) => {
                    if self.entity_has_runtime_value(import.module_reference, visited) {
                        return true;
                    }
                }
                NodeData::ModuleDeclaration(module) => {
                    if self.namespace_has_runtime_contents(module, visited) {
                        return true;
                    }
                }
                NodeData::ImportClause(_)
                | NodeData::ImportSpecifier(_)
                | NodeData::NamespaceImport(_)
                | NodeData::NamedImports(_) => {
                    if self.import_binding_has_runtime_value(*declaration) {
                        return true;
                    }
                }
                NodeData::InterfaceDeclaration(_) | NodeData::TypeAliasDeclaration(_) => {}
                NodeData::FunctionDeclaration(function) if function.body.is_none() => {}
                NodeData::EnumDeclaration(_)
                    if is_const_enum_declaration(self.arena, node)
                        && !self.const_enum_emit_mode.preserves_declarations() => {}
                _ if !declaration_has_modifier(self.arena, node, SyntaxKind::DeclareKeyword) => {
                    return true;
                }
                _ => {}
            }
        }
        false
    }

    fn import_binding_has_runtime_value(&self, declaration: NodeId) -> bool {
        let mut current = declaration;
        loop {
            let Some(node) = self.arena.get(current) else {
                return true;
            };
            match &node.data {
                NodeData::ImportDeclaration(_) => {
                    return self.import_semantically_has_runtime_value(current);
                }
                NodeData::ImportClause(clause)
                    if clause.phase_modifier == Some(SyntaxKind::TypeKeyword) =>
                {
                    return false;
                }
                NodeData::ImportSpecifier(specifier) if specifier.is_type_only => return false,
                _ => {}
            }
            let Some(parent) = node.parent else {
                return true;
            };
            current = parent;
        }
    }

    fn namespace_has_runtime_contents(
        &self,
        module: &ts_ast::ModuleDeclarationData,
        visited: &mut HashSet<SymbolId>,
    ) -> bool {
        let Some(body) = module.body else {
            return false;
        };
        let Some(body) = self.arena.get(body) else {
            return false;
        };
        match &body.data {
            NodeData::ModuleBlock(block) => {
                block.statements.nodes.iter().any(|statement| {
                    self.namespace_statement_has_runtime_value(*statement, visited)
                })
            }
            NodeData::ModuleDeclaration(module) => {
                self.namespace_has_runtime_contents(module, visited)
            }
            _ => false,
        }
    }

    fn namespace_statement_has_runtime_value(
        &self,
        statement: NodeId,
        visited: &mut HashSet<SymbolId>,
    ) -> bool {
        let Some(node) = self.arena.get(statement) else {
            return false;
        };
        if declaration_has_modifier(self.arena, node, SyntaxKind::DeclareKeyword) {
            return false;
        }
        match &node.data {
            NodeData::InterfaceDeclaration(_) | NodeData::TypeAliasDeclaration(_) => false,
            NodeData::ModuleDeclaration(module) => {
                self.namespace_has_runtime_contents(module, visited)
            }
            // Exported aliases instantiate a module even when their target is type-only and the
            // alias is consequently erased. Non-exported imports do not instantiate a module.
            NodeData::ImportEqualsDeclaration(import) => {
                self.has_modifier(import.modifiers.as_ref(), SyntaxKind::ExportKeyword)
            }
            NodeData::EnumDeclaration(_)
                if is_const_enum_declaration(self.arena, node)
                    && !self.const_enum_emit_mode.preserves_declarations() =>
            {
                false
            }
            _ => true,
        }
    }

    fn namespace_has_prior_merged_value_declaration(&self, name: NodeId) -> bool {
        let Some(current) = self.arena.get(name).and_then(|node| node.parent) else {
            return false;
        };
        let Some(current_start) = self.arena.get(current).map(|node| node.range.start) else {
            return false;
        };
        self.bindings
            .node_symbols
            .get(&name)
            .and_then(|symbol| self.bindings.symbols.get(*symbol))
            .is_some_and(|symbol| {
                symbol.declarations.iter().any(|declaration| {
                    if *declaration == current {
                        return false;
                    }
                    let Some(node) = self.arena.get(*declaration) else {
                        return false;
                    };
                    if node.range.start >= current_start
                        || node_is_in_ambient_context(self.arena, *declaration)
                    {
                        return false;
                    }
                    match &node.data {
                        NodeData::ClassDeclaration(_) | NodeData::EnumDeclaration(_) => true,
                        NodeData::ModuleDeclaration(module) => {
                            self.namespace_has_runtime_contents(module, &mut HashSet::new())
                        }
                        NodeData::FunctionDeclaration(function) => function.body.is_some(),
                        _ => false,
                    }
                })
            })
    }

    fn namespace_needs_local_declaration(&self, name: NodeId, text: &str) -> bool {
        !self.namespace_has_prior_merged_value_declaration(name)
            && !self.system_predeclared_names.contains(text)
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
        if let NodeData::ExportAssignment(assignment) = &node.data
            && !self.entity_has_runtime_value(assignment.expression, &mut HashSet::new())
        {
            return Ok(());
        }
        match &node.data {
            NodeData::NotEmittedStatement(_) => return Ok(()),
            NodeData::ImportDeclaration(import) if !self.import_has_runtime_use(id, import) => {
                return Ok(());
            }
            NodeData::ImportEqualsDeclaration(import)
                if import.is_type_only
                    || if self.is_external_import_equals(import) {
                        !self.import_semantically_has_runtime_value(id)
                            || (!self
                                .has_modifier(import.modifiers.as_ref(), SyntaxKind::ExportKeyword)
                                && !self.import_binding_is_used(import.name))
                    } else {
                        !self.internal_import_equals_has_runtime_value(import)
                    } =>
            {
                return Ok(());
            }
            NodeData::ModuleDeclaration(module)
                if !self.namespace_has_runtime_contents(module, &mut HashSet::new()) =>
            {
                return Ok(());
            }
            NodeData::ExportDeclaration(export)
                if self.commonjs_module_transform
                    && self.commonjs_export_is_fully_hoisted(export) =>
            {
                return Ok(());
            }
            _ => {}
        }
        if let Some(container) = self.namespace_containers.last().cloned()
            && let NodeData::ImportEqualsDeclaration(import) = &node.data
            && !self.is_external_import_equals(import)
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
        if (self.commonjs_module_transform || !self.namespace_containers.is_empty())
            && declaration_has_modifier(self.arena, &node, SyntaxKind::ExportKeyword)
            && let NodeData::VariableStatement(statement) = &node.data
            && self.variable_list_is_uninitialized(statement.declaration_list)
        {
            return Ok(());
        }
        match &node.data {
            NodeData::InterfaceDeclaration(_) | NodeData::TypeAliasDeclaration(_) => return Ok(()),
            NodeData::FunctionDeclaration(data) if data.body.is_none() => return Ok(()),
            NodeData::ExportDeclaration(_) if export_declaration_is_empty(self.arena, &node) => {
                return Ok(());
            }
            _ => {}
        }
        self.record_mapping(&node);
        match &node.data {
            NodeData::Block(_) => self.emit_block(id)?,
            NodeData::EmptyStatement(_) => self.writer.write(";"),
            NodeData::VariableStatement(data) => {
                if self.commonjs_empty_binding_temps.contains_key(&id) {
                    self.emit_commonjs_empty_binding_initializer(id, data)?;
                } else if self.emit_system_predeclared_variable_assignment(data)? {
                } else if !self.emit_namespace_export_variable_initializers(data)?
                    && !self.emit_commonjs_export_variable_initializer(data)?
                {
                    self.emit_runtime_declaration_modifiers(data.modifiers.as_ref());
                    self.emit_variable_list(data.declaration_list)?;
                    self.writer.write(";");
                    let names = self.variable_declaration_names(data.declaration_list)?;
                    self.emit_commonjs_declaration_exports(data.modifiers.as_ref(), &names);
                }
            }
            NodeData::FunctionDeclaration(data) => {
                self.emit_runtime_declaration_modifiers(data.modifiers.as_ref());
                let is_async = self.has_modifier(data.modifiers.as_ref(), SyntaxKind::AsyncKeyword);
                let downlevel_async_generator = self.settings.target < ScriptTarget::Es2018
                    && data.asterisk_token.is_some()
                    && is_async;
                let downlevel_async = self.settings.target < ScriptTarget::Es2017
                    && data.asterisk_token.is_none()
                    && is_async;
                let downlevel_generator = self.settings.target < ScriptTarget::Es2015
                    && data.asterisk_token.is_some()
                    && !is_async;
                if !downlevel_async && !downlevel_async_generator && is_async {
                    self.writer.write("async ");
                }
                self.writer.write("function");
                if data.asterisk_token.is_some()
                    && !downlevel_async_generator
                    && !downlevel_generator
                {
                    self.writer.write("*");
                }
                self.writer.write(" ");
                let function_name = data
                    .name
                    .and_then(|name| declaration_name_text(self.arena, name))
                    .map(str::to_owned);
                if let Some(name) = data.name {
                    self.emit_expression(name, 0)?;
                }
                self.emit_parameters(&data.parameters)?;
                self.writer.write(" ");
                if downlevel_async {
                    self.emit_downlevel_async_function_body(
                        data.body.expect("body checked above"),
                        "this",
                    )?;
                } else if downlevel_async_generator {
                    let inner_name = self
                        .generated_names
                        .generate(function_name.as_deref().unwrap_or("_default"));
                    if self.settings.target < ScriptTarget::Es2015 {
                        self.emit_es5_downlevel_async_generator_body(
                            data.body.expect("body checked above"),
                            &inner_name,
                        )?;
                    } else {
                        self.emit_downlevel_async_generator_body(
                            data.body.expect("body checked above"),
                            &inner_name,
                        )?;
                    }
                } else if downlevel_generator {
                    self.emit_es5_generator_body(data.body.expect("body checked above"))?;
                } else if self.settings.target < ScriptTarget::Es2015
                    && self.body_has_downlevel_async_arrow(data.body.expect("body checked above"))
                {
                    self.emit_function_body_with_this_capture(
                        data.body.expect("body checked above"),
                    )?;
                } else {
                    self.emit_function_body(data.body.expect("body checked above"))?;
                }
                if let Some(container) = self.namespace_containers.last().cloned()
                    && self.has_modifier(data.modifiers.as_ref(), SyntaxKind::ExportKeyword)
                    && let Some(name) = data
                        .name
                        .and_then(|name| declaration_name_text(self.arena, name))
                        .map(str::to_owned)
                {
                    self.writer.newline();
                    self.writer.write(&container);
                    self.writer.write(".");
                    self.writer.write(&name);
                    self.writer.write(" = ");
                    self.writer.write(&name);
                    self.writer.write(";");
                }
            }
            NodeData::ClassDeclaration(data) => {
                self.emit_runtime_declaration_modifiers(data.modifiers.as_ref());
                self.emit_class(data)?;
                self.emit_auto_accessor_storage_initializers(data);
                if let Some(name) = data.name {
                    let names = self.declaration_names(&[name]);
                    if let Some(container) = self.namespace_containers.last().cloned() {
                        if self.has_modifier(data.modifiers.as_ref(), SyntaxKind::ExportKeyword)
                            && let Some(name) = names.first()
                        {
                            self.emit_source_comments_between_with_ownership(
                                node.range.end.get(),
                                u32::try_from(self.source_text.len()).unwrap_or(u32::MAX),
                                true,
                                false,
                            );
                            if !self.writer.line_start {
                                self.writer.newline();
                            }
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
                if !self.commonjs_module_transform || !self.namespace_containers.is_empty() {
                    let names = self.declaration_names(&[data.name]);
                    self.emit_commonjs_declaration_exports(data.modifiers.as_ref(), &names);
                }
            }
            NodeData::ModuleDeclaration(data) => self.emit_namespace(data)?,
            NodeData::ReturnStatement(data) => {
                self.writer.write("return");
                if self.async_expression_transform == AsyncExpressionTransform::AsyncGenerator {
                    self.writer.write(" yield __await(");
                    if let Some(expression) = data.expression {
                        self.emit_expression(expression, 0)?;
                    } else {
                        self.writer.write("void 0");
                    }
                    self.writer.write(")");
                } else if let Some(expression) = data.expression {
                    self.writer.write(" ");
                    self.emit_expression(expression, 0)?;
                }
                self.writer.write(";");
            }
            NodeData::IfStatement(data) => {
                self.emit_if_statement(data)?;
            }
            NodeData::WhileStatement(data) => {
                self.writer.write("while (");
                self.emit_expression(data.expression, 0)?;
                self.writer.write(") ");
                self.emit_embedded(data.statement)?;
            }
            NodeData::DoStatement(data) => {
                if !self.emit_es5_captured_do_loop(data)? {
                    self.writer.write("do ");
                    self.emit_embedded(data.statement)?;
                    self.writer.write(" while (");
                    self.emit_expression(data.expression, 0)?;
                    self.writer.write(");");
                }
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
                if node.kind == SyntaxKind::ForOfStatement
                    && data.await_modifier.is_none()
                    && self.settings.target < ScriptTarget::Es2015
                {
                    self.emit_downlevel_for_of(data)?;
                    self.writer.newline();
                    return Ok(());
                }
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
                let precedence = if self.settings.target < ScriptTarget::Es2015
                    && matches!(self.node(data.expression)?.data, NodeData::ArrowFunction(_))
                {
                    3
                } else {
                    0
                };
                self.emit_expression(data.expression, precedence)?;
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
            if let [statement] = clause.statements.nodes.as_slice()
                && matches!(
                    self.node(*statement)?.data,
                    NodeData::Block(_) | NodeData::ReturnStatement(_)
                )
                && self.switch_clause_statement_is_inline(*clause_id, *statement)
            {
                self.writer.write(" ");
                self.emit_statement(*statement)?;
                self.writer.remove_trailing_newline();
                self.writer.newline();
            } else {
                self.writer.newline();
                self.writer.indent += 1;
                for statement in &clause.statements.nodes {
                    self.emit_statement(*statement)?;
                }
                self.writer.indent -= 1;
            }
        }
        self.writer.indent -= 1;
        self.writer.write("}");
        Ok(())
    }

    fn switch_clause_statement_is_inline(&self, clause: NodeId, statement: NodeId) -> bool {
        if self.source_text.is_empty() {
            return true;
        }
        let Some(clause) = self.arena.get(clause) else {
            return false;
        };
        let Some(statement) = self.arena.get(statement) else {
            return false;
        };
        let start = usize::try_from(clause.range.start.get()).unwrap_or(usize::MAX);
        let end = usize::try_from(statement.range.start.get()).unwrap_or(usize::MAX);
        self.source_text
            .get(start..end)
            .is_some_and(|text| !text.contains(['\n', '\r']))
    }

    fn emit_if_statement(&mut self, data: &ts_ast::IfStatementData) -> Result<(), EmitError> {
        self.writer.write("if (");
        self.emit_expression(data.expression, 0)?;
        self.writer.write(") ");
        self.emit_embedded(data.then_statement)?;
        if let Some(otherwise) = data.else_statement {
            self.writer.newline();
            self.writer.write("else ");
            let otherwise_node = self.node(otherwise)?.clone();
            if let NodeData::IfStatement(otherwise) = &otherwise_node.data {
                self.emit_if_statement(otherwise)?;
            } else {
                self.emit_embedded(otherwise)?;
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    fn emit_es5_captured_do_loop(
        &mut self,
        data: &ts_ast::DoStatementData,
    ) -> Result<bool, EmitError> {
        if self.settings.target >= ScriptTarget::Es2015 {
            return Ok(false);
        }
        let body_node = self.node(data.statement)?.clone();
        let NodeData::Block(block) = &body_node.data else {
            return Ok(false);
        };
        let mut captured = None;
        for statement_id in &block.statements.nodes {
            let Some(NodeData::VariableStatement(statement)) =
                self.arena.get(*statement_id).map(|node| &node.data)
            else {
                continue;
            };
            let Some(list_node) = self.arena.get(statement.declaration_list) else {
                continue;
            };
            let NodeData::VariableDeclarationList(list) = &list_node.data else {
                continue;
            };
            if !variable_list_is_block_scoped(list_node) {
                continue;
            }
            for declaration_id in &list.declarations.nodes {
                let Some(NodeData::VariableDeclaration(declaration)) =
                    self.arena.get(*declaration_id).map(|node| &node.data)
                else {
                    continue;
                };
                let Some(name) = declaration_name_text(self.arena, declaration.name) else {
                    continue;
                };
                let rewrite_symbols = self
                    .arena
                    .iter()
                    .filter_map(|(id, node)| {
                        let NodeData::Identifier(identifier) = &node.data else {
                            return None;
                        };
                        (id != declaration.name
                            && identifier.text == name
                            && node_is_in_nested_function(self.arena, id, data.statement))
                        .then(|| self.bindings.resolve_name_at(id, name))
                        .flatten()
                    })
                    .collect::<HashSet<_>>();
                if !rewrite_symbols.is_empty() {
                    captured = Some((
                        *statement_id,
                        declaration.initializer,
                        rewrite_symbols,
                        name.to_owned(),
                    ));
                    break;
                }
            }
            if captured.is_some() {
                break;
            }
        }
        let Some((captured_statement, captured_initializer, rewrite_symbols, captured_name)) =
            captured
        else {
            return Ok(false);
        };
        let renamed = self.generated_names.generate(&captured_name);
        let loop_name = self.generated_names.generate("_loop");
        let mut hoisted = Vec::new();
        for statement_id in &block.statements.nodes {
            let Some(NodeData::VariableStatement(statement)) =
                self.arena.get(*statement_id).map(|node| &node.data)
            else {
                continue;
            };
            let Some(list_node) = self.arena.get(statement.declaration_list) else {
                continue;
            };
            if list_node.flags.0 & 3 != 0 {
                continue;
            }
            hoisted.extend(simple_variable_names(
                self.arena,
                statement.declaration_list,
            ));
        }

        self.writer.write("var ");
        self.writer.write(&loop_name);
        self.writer.write(" = function () {");
        self.writer.newline();
        self.writer.indent += 1;
        let previous_rewrites = rewrite_symbols
            .iter()
            .map(|symbol| {
                (
                    *symbol,
                    self.identifier_rewrites.insert(*symbol, renamed.clone()),
                )
            })
            .collect::<Vec<_>>();
        for statement_id in &block.statements.nodes {
            if *statement_id == captured_statement {
                self.writer.write("var ");
                self.writer.write(&renamed);
                if let Some(initializer) = captured_initializer {
                    self.writer.write(" = ");
                    self.emit_expression(initializer, 1)?;
                }
                self.writer.write(";");
                self.writer.newline();
                continue;
            }
            if let Some(NodeData::VariableStatement(statement)) =
                self.arena.get(*statement_id).map(|node| &node.data)
                && let Some(list_node) = self.arena.get(statement.declaration_list)
                && !variable_list_is_block_scoped(list_node)
                && let NodeData::VariableDeclarationList(list) = &list_node.data
            {
                for declaration_id in &list.declarations.nodes {
                    let Some(NodeData::VariableDeclaration(declaration)) =
                        self.arena.get(*declaration_id).map(|node| &node.data)
                    else {
                        continue;
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
                continue;
            }
            self.emit_statement(*statement_id)?;
        }
        for (symbol, rewrite) in previous_rewrites {
            if let Some(rewrite) = rewrite {
                self.identifier_rewrites.insert(symbol, rewrite);
            } else {
                self.identifier_rewrites.remove(&symbol);
            }
        }
        self.writer.indent -= 1;
        self.writer.write("};");
        self.writer.newline();
        if !hoisted.is_empty() {
            self.writer.write("var ");
            self.writer.write(&hoisted.join(", "));
            self.writer.write(";");
            self.writer.newline();
        }
        self.writer.write("do {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write(&loop_name);
        self.writer.write("();");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("} while (");
        self.emit_expression(data.expression, 0)?;
        self.writer.write(");");
        Ok(true)
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

    fn emit_downlevel_for_of(
        &mut self,
        data: &ts_ast::ForInOrOfStatementData,
    ) -> Result<(), EmitError> {
        let counter = self.generated_names.generate_loop_variable();
        let rhs = match self.node(data.expression)?.data.clone() {
            NodeData::Identifier(identifier) => self.generated_names.generate(&identifier.text),
            _ => self.generated_names.generate_temp(),
        };
        self.writer.write("for (var ");
        self.writer.write(&counter);
        self.writer.write(" = 0, ");
        self.writer.write(&rhs);
        self.writer.write(" = ");
        self.emit_expression(data.expression, 1)?;
        self.writer.write("; ");
        self.writer.write(&counter);
        self.writer.write(" < ");
        self.writer.write(&rhs);
        self.writer.write(".length; ");
        self.writer.write(&counter);
        self.writer.write("++) ");
        let value = DownlevelBindingValue::Element(
            Box::new(DownlevelBindingValue::Name(rhs)),
            DownlevelBindingIndex::Name(counter),
        );
        self.emit_downlevel_for_of_body(data.statement, data.initializer, &value)
    }

    fn emit_downlevel_for_of_body(
        &mut self,
        body: NodeId,
        initializer: NodeId,
        value: &DownlevelBindingValue,
    ) -> Result<(), EmitError> {
        self.writer.write("{");
        self.writer.newline();
        self.writer.indent += 1;
        self.emit_downlevel_for_of_binding(initializer, value)?;

        let body_node = self.node(body)?.clone();
        if let NodeData::Block(block) = &body_node.data {
            let mut previous_end = body_node.range.start.get().saturating_add(1);
            let mut previous_emitted = true;
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
        } else {
            self.emit_statement(body)?;
        }
        self.writer.indent -= 1;
        self.writer.write("}");
        Ok(())
    }

    fn emit_downlevel_for_of_binding(
        &mut self,
        initializer: NodeId,
        value: &DownlevelBindingValue,
    ) -> Result<(), EmitError> {
        let initializer_node = self.node(initializer)?.clone();
        if let NodeData::VariableDeclarationList(list) = &initializer_node.data {
            self.writer.write("var ");
            let mut emitted = false;
            if let Some(declaration_id) = list.declarations.nodes.first() {
                let declaration_node = self.node(*declaration_id)?.clone();
                let NodeData::VariableDeclaration(declaration) = &declaration_node.data else {
                    return Err(Self::unsupported(*declaration_id, declaration_node.kind));
                };
                let binding_value =
                    if self.node(declaration.name)?.kind == SyntaxKind::ArrayBindingPattern {
                        let temp = self.generated_names.generate_temp();
                        self.emit_downlevel_declarator_start(&mut emitted);
                        self.writer.write(&temp);
                        self.writer.write(" = ");
                        self.emit_downlevel_binding_value(value)?;
                        DownlevelBindingValue::Name(temp)
                    } else {
                        (*value).clone()
                    };
                self.emit_downlevel_binding_declarators(
                    declaration.name,
                    binding_value,
                    None,
                    &mut emitted,
                )?;
            }
            if !emitted {
                let temp = self.generated_names.generate_temp();
                self.emit_downlevel_declarator_start(&mut emitted);
                self.writer.write(&temp);
                self.writer.write(" = ");
                self.emit_downlevel_binding_value(value)?;
            }
            self.writer.write(";");
        } else {
            self.emit_expression(initializer, 1)?;
            self.writer.write(" = ");
            self.emit_downlevel_binding_value(value)?;
            self.writer.write(";");
        }
        self.writer.newline();
        Ok(())
    }

    fn emit_downlevel_binding_declarators(
        &mut self,
        name: NodeId,
        value: DownlevelBindingValue,
        initializer: Option<NodeId>,
        emitted: &mut bool,
    ) -> Result<(), EmitError> {
        let value = if let Some(initializer) = initializer {
            let temp = self.generated_names.generate_temp();
            self.emit_downlevel_declarator_start(emitted);
            self.writer.write(&temp);
            self.writer.write(" = ");
            self.emit_downlevel_binding_value(&value)?;
            let defaulted = self.generated_names.generate_temp();
            self.emit_downlevel_declarator_start(emitted);
            self.writer.write(&defaulted);
            self.writer.write(" = ");
            self.writer.write(&temp);
            self.writer.write(" === void 0 ? ");
            self.emit_expression(initializer, 2)?;
            self.writer.write(" : ");
            self.writer.write(&temp);
            DownlevelBindingValue::Name(defaulted)
        } else {
            value
        };

        let name_node = self.node(name)?.clone();
        match &name_node.data {
            NodeData::Identifier(_) => {
                self.emit_downlevel_declarator_start(emitted);
                self.emit_expression(name, 0)?;
                self.writer.write(" = ");
                self.emit_downlevel_binding_value(&value)?;
            }
            NodeData::BindingPattern(pattern)
                if name_node.kind == SyntaxKind::ArrayBindingPattern =>
            {
                let mut index = 0_usize;
                let mut previous_end = name_node.range.start.get().saturating_add(1);
                for element_id in &pattern.elements.nodes {
                    let element_node = self.node(*element_id)?.clone();
                    index += self
                        .array_binding_comma_count(previous_end, element_node.range.start.get());
                    if matches!(element_node.data, NodeData::OmittedExpression(_)) {
                        previous_end = element_node.range.end.get();
                        continue;
                    }
                    let NodeData::BindingElement(element) = &element_node.data else {
                        return Err(Self::unsupported(*element_id, element_node.kind));
                    };
                    let Some(element_name) = element.name else {
                        continue;
                    };
                    let mut element_value = if element.dot_dot_dot_token.is_some() {
                        DownlevelBindingValue::Slice(Box::new(value.clone()), index)
                    } else {
                        DownlevelBindingValue::Element(
                            Box::new(value.clone()),
                            DownlevelBindingIndex::Number(index),
                        )
                    };
                    if element.initializer.is_none()
                        && self.node(element_name)?.kind == SyntaxKind::ArrayBindingPattern
                    {
                        let temp = self.generated_names.generate_temp();
                        self.emit_downlevel_declarator_start(emitted);
                        self.writer.write(&temp);
                        self.writer.write(" = ");
                        self.emit_downlevel_binding_value(&element_value)?;
                        element_value = DownlevelBindingValue::Name(temp);
                    }
                    self.emit_downlevel_binding_declarators(
                        element_name,
                        element_value,
                        element.initializer,
                        emitted,
                    )?;
                    previous_end = element_node.range.end.get();
                }
            }
            _ => return Err(Self::unsupported(name, name_node.kind)),
        }
        Ok(())
    }

    fn array_binding_comma_count(&self, start: u32, end: u32) -> usize {
        let start = usize::try_from(start).unwrap_or(usize::MAX);
        let end = usize::try_from(end).unwrap_or(usize::MAX);
        let Some(text) = self.source_text.get(start..end) else {
            return 0;
        };
        let bytes = text.as_bytes();
        let mut index = 0;
        let mut commas = 0;
        while index < bytes.len() {
            if bytes[index..].starts_with(b"//") {
                index += 2;
                while index < bytes.len() && !matches!(bytes[index], b'\n' | b'\r') {
                    index += 1;
                }
            } else if bytes[index..].starts_with(b"/*") {
                index += 2;
                while index + 1 < bytes.len() && !bytes[index..].starts_with(b"*/") {
                    index += 1;
                }
                index = (index + 2).min(bytes.len());
            } else {
                commas += usize::from(bytes[index] == b',');
                index += 1;
            }
        }
        commas
    }

    fn emit_downlevel_declarator_start(&mut self, emitted: &mut bool) {
        if *emitted {
            self.writer.write(", ");
        }
        *emitted = true;
    }

    fn emit_downlevel_binding_value(
        &mut self,
        value: &DownlevelBindingValue,
    ) -> Result<(), EmitError> {
        match value {
            DownlevelBindingValue::Node(node) => self.emit_expression(*node, 18)?,
            DownlevelBindingValue::Name(name) => self.writer.write(name),
            DownlevelBindingValue::Element(value, index) => {
                self.emit_downlevel_binding_value(value)?;
                self.writer.write("[");
                match index {
                    DownlevelBindingIndex::Number(index) => {
                        self.writer.write(&index.to_string());
                    }
                    DownlevelBindingIndex::Name(name) => self.writer.write(name),
                }
                self.writer.write("]");
            }
            DownlevelBindingValue::Slice(value, index) => {
                self.emit_downlevel_binding_value(value)?;
                self.writer.write(".slice(");
                self.writer.write(&index.to_string());
                self.writer.write(")");
            }
            DownlevelBindingValue::VoidZero => self.writer.write("void 0"),
        }
        Ok(())
    }

    fn prepare_commonjs_empty_binding_temps(&mut self, statements: &NodeList) {
        for statement in &statements.nodes {
            let Some(node) = self.arena.get(*statement) else {
                continue;
            };
            let NodeData::VariableStatement(variable) = &node.data else {
                continue;
            };
            if !self.has_modifier(variable.modifiers.as_ref(), SyntaxKind::ExportKeyword) {
                continue;
            }
            let Some(NodeData::VariableDeclarationList(list)) = self
                .arena
                .get(variable.declaration_list)
                .map(|node| &node.data)
            else {
                continue;
            };
            let [declaration_id] = list.declarations.nodes.as_slice() else {
                continue;
            };
            let Some(NodeData::VariableDeclaration(declaration)) =
                self.arena.get(*declaration_id).map(|node| &node.data)
            else {
                continue;
            };
            if self
                .arena
                .get(declaration.name)
                .is_none_or(|node| node.kind != SyntaxKind::ArrayBindingPattern)
                || declaration.initializer.is_none()
                || !self.binding_pattern_has_no_identifiers(declaration.name)
            {
                continue;
            }
            let mut pattern_count = 0;
            self.count_array_binding_patterns(declaration.name, &mut pattern_count);
            if pattern_count == 0 {
                continue;
            }
            let temps = (0..pattern_count)
                .map(|_| self.generated_names.generate_temp())
                .collect::<Vec<_>>();
            self.commonjs_empty_binding_hoists
                .extend(temps.iter().cloned());
            self.commonjs_empty_binding_temps.insert(*statement, temps);
        }
    }

    fn binding_pattern_has_no_identifiers(&self, name: NodeId) -> bool {
        let Some(node) = self.arena.get(name) else {
            return false;
        };
        let NodeData::BindingPattern(pattern) = &node.data else {
            return false;
        };
        pattern.elements.nodes.iter().all(|element| {
            let Some(element) = self.arena.get(*element) else {
                return false;
            };
            match &element.data {
                NodeData::OmittedExpression(_) => true,
                NodeData::BindingElement(element) => element
                    .name
                    .is_some_and(|name| self.binding_pattern_has_no_identifiers(name)),
                _ => false,
            }
        })
    }

    fn count_array_binding_patterns(&self, name: NodeId, count: &mut usize) {
        let Some(node) = self.arena.get(name) else {
            return;
        };
        let NodeData::BindingPattern(pattern) = &node.data else {
            return;
        };
        if node.kind == SyntaxKind::ArrayBindingPattern {
            *count += 1;
        }
        for element in &pattern.elements.nodes {
            if let Some(NodeData::BindingElement(element)) =
                self.arena.get(*element).map(|node| &node.data)
                && let Some(name) = element.name
            {
                self.count_array_binding_patterns(name, count);
            }
        }
    }

    fn emit_commonjs_empty_binding_initializer(
        &mut self,
        statement: NodeId,
        variable: &ts_ast::VariableStatementData,
    ) -> Result<(), EmitError> {
        let temps = self
            .commonjs_empty_binding_temps
            .get(&statement)
            .cloned()
            .unwrap_or_default();
        let list = self.node(variable.declaration_list)?.clone();
        let NodeData::VariableDeclarationList(list) = &list.data else {
            return Err(Self::unsupported(variable.declaration_list, list.kind));
        };
        let declaration_id = list.declarations.nodes[0];
        let declaration = self.node(declaration_id)?.clone();
        let NodeData::VariableDeclaration(declaration) = &declaration.data else {
            return Err(Self::unsupported(declaration_id, declaration.kind));
        };
        let mut temps = temps.iter();
        let root = temps.next().expect("prepared empty binding root");
        self.writer.write(root);
        self.writer.write(" = ");
        self.emit_expression(declaration.initializer.expect("initializer checked"), 1)?;
        self.emit_empty_binding_children(declaration.name, root, &mut temps)?;
        self.writer.write(";");
        Ok(())
    }

    fn emit_empty_binding_children<'a>(
        &mut self,
        pattern_id: NodeId,
        parent_temp: &str,
        temps: &mut impl Iterator<Item = &'a String>,
    ) -> Result<(), EmitError> {
        let pattern_node = self.node(pattern_id)?.clone();
        let NodeData::BindingPattern(pattern) = &pattern_node.data else {
            return Ok(());
        };
        let mut index = 0_usize;
        let mut previous_end = pattern_node.range.start.get().saturating_add(1);
        for element_id in &pattern.elements.nodes {
            let element_node = self.node(*element_id)?.clone();
            index += self.array_binding_comma_count(previous_end, element_node.range.start.get());
            let NodeData::BindingElement(element) = &element_node.data else {
                previous_end = element_node.range.end.get();
                continue;
            };
            let Some(name) = element.name else {
                previous_end = element_node.range.end.get();
                continue;
            };
            if self.node(name)?.kind == SyntaxKind::ArrayBindingPattern {
                let temp = temps.next().expect("prepared nested empty binding temp");
                self.writer.write(", ");
                self.writer.write(temp);
                self.writer.write(" = ");
                self.writer.write(parent_temp);
                self.writer.write("[");
                self.writer.write(&index.to_string());
                self.writer.write("]");
                self.emit_empty_binding_children(name, temp, temps)?;
            }
            previous_end = element_node.range.end.get();
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
        self.namespace_declarations.push(HashSet::new());
        self.prepare_class_expression_temps(id, data);
        let mut previous_end = node.range.start.get().saturating_add(1);
        let mut previous_emitted = false;
        for statement in &data.statements.nodes {
            let statement_node = self.node(*statement)?.clone();
            if !previous_emitted
                && previous_end == node.range.start.get().saturating_add(1)
                && self.body_opening_line_comment_is_unowned(id)
            {
                previous_end = self.position_after_immediate_line_comment(
                    previous_end,
                    statement_node.range.start.get(),
                );
            }
            let direct_await = matches!(
                &statement_node.data,
                NodeData::ExpressionStatement(expression)
                    if matches!(
                        self.arena.get(expression.expression).map(|node| &node.data),
                        Some(NodeData::AwaitExpression(_))
                    )
            );
            let inline_comment_start = direct_await
                .then(|| {
                    self.inline_await_leading_comment_start(
                        previous_end,
                        statement_node.range.start.get(),
                    )
                })
                .flatten();
            let comment_end = inline_comment_start.unwrap_or(statement_node.range.start.get());
            self.emit_source_comments_between_with_trailing(
                previous_end,
                comment_end,
                previous_emitted || previous_end == node.range.start.get().saturating_add(1),
            );
            if let Some(comment_start) = inline_comment_start {
                self.emit_inline_block_comments_between(
                    comment_start,
                    statement_node.range.start.get(),
                    false,
                );
            }
            self.emit_statement(*statement)?;
            previous_end = statement_node.range.end.get();
            previous_emitted = statement_emits_javascript(self.arena, &statement_node);
        }
        self.emit_source_comments_between_with_trailing(
            previous_end,
            node.range.end.get().saturating_sub(1),
            previous_emitted,
        );
        self.namespace_declarations.pop();
        self.writer.indent -= 1;
        self.writer.write("}");
        Ok(())
    }

    fn prepare_class_expression_temps(&mut self, block_id: NodeId, block: &ts_ast::BlockData) {
        if self.settings.target >= ScriptTarget::Es2022 {
            return;
        }
        let class_expressions = block
            .statements
            .nodes
            .iter()
            .flat_map(|statement| {
                let Some(statement) = self.arena.get(*statement) else {
                    return Vec::new();
                };
                let expressions = match &statement.data {
                    NodeData::ReturnStatement(return_) => {
                        return_.expression.into_iter().collect::<Vec<_>>()
                    }
                    NodeData::VariableStatement(variable) => {
                        let Some(NodeData::VariableDeclarationList(list)) = self
                            .arena
                            .get(variable.declaration_list)
                            .map(|node| &node.data)
                        else {
                            return Vec::new();
                        };
                        list.declarations
                            .nodes
                            .iter()
                            .filter_map(|declaration| {
                                let NodeData::VariableDeclaration(declaration) =
                                    &self.arena.get(*declaration)?.data
                                else {
                                    return None;
                                };
                                declaration.initializer
                            })
                            .collect()
                    }
                    _ => Vec::new(),
                };
                expressions
                    .into_iter()
                    .filter(|expression| {
                        let Some(NodeData::ClassExpression(class)) =
                            self.arena.get(*expression).map(|node| &node.data)
                        else {
                            return false;
                        };
                        let declaration = Self::class_expression_as_declaration(class);
                        self.class_expression_requires_post_class_lowering(&declaration)
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let mut claimed = HashSet::new();
        for class_expression in class_expressions {
            let temp = self.generate_block_temp(block_id, &claimed);
            claimed.insert(temp.clone());
            self.class_expression_temps
                .insert(class_expression, temp.clone());
            self.writer.write("var ");
            self.writer.write(&temp);
            self.writer.write(";");
            self.writer.newline();
        }
    }

    fn generate_block_temp(&self, block: NodeId, claimed: &HashSet<String>) -> String {
        let mut suffix = 0_u32;
        loop {
            for letter in b'a'..=b'z' {
                let base = format!("_{}", char::from(letter));
                let candidate = if suffix == 0 {
                    base
                } else {
                    format!("{base}_{suffix}")
                };
                let block_range = self.arena.get(block).map(|block| block.range);
                let used_in_block = self.arena.iter().any(|(_, node)| {
                    matches!(&node.data, NodeData::Identifier(identifier) if identifier.text == candidate)
                        && block_range.is_some_and(|range| {
                            range.start <= node.range.start && node.range.end <= range.end
                        })
                });
                if !used_in_block && !claimed.contains(&candidate) {
                    return candidate;
                }
            }
            suffix += 1;
        }
    }

    fn body_opening_line_comment_is_unowned(&self, block: NodeId) -> bool {
        let Some(arrow) = self.arena.get(block).and_then(|block| block.parent) else {
            return false;
        };
        if matches!(
            self.arena.get(arrow).map(|node| &node.data),
            Some(NodeData::FunctionExpression(_))
        ) {
            return true;
        }
        if !matches!(
            self.arena.get(arrow).map(|node| &node.data),
            Some(NodeData::ArrowFunction(_))
        ) {
            return false;
        }
        self.arena
            .get(arrow)
            .and_then(|arrow| arrow.parent)
            .and_then(|parent| self.arena.get(parent))
            .is_some_and(|parent| matches!(parent.data, NodeData::PropertyAssignment(_)))
    }

    fn position_after_immediate_line_comment(&self, start: u32, end: u32) -> u32 {
        let start_index = usize::try_from(start).unwrap_or(usize::MAX);
        let end_index = usize::try_from(end).unwrap_or(usize::MAX);
        let Some(trivia) = self.source_text.get(start_index..end_index) else {
            return start;
        };
        let comment = trivia.trim_start_matches([' ', '\t']);
        if !comment.starts_with("//") {
            return start;
        }
        let leading = trivia.len() - comment.len();
        let comment_end = comment.find(['\n', '\r']).map_or(comment.len(), |end| end);
        u32::try_from(start_index + leading + comment_end).unwrap_or(end)
    }

    fn emit_function_body(&mut self, body: NodeId) -> Result<(), EmitError> {
        if let Some(statement) = self.single_line_body_statement(body)? {
            self.writer.write("{ ");
            self.emit_statement(statement)?;
            self.writer.remove_trailing_newline();
            self.writer.write(" }");
            Ok(())
        } else {
            self.emit_block(body)
        }
    }

    fn body_has_downlevel_async_arrow(&self, body: NodeId) -> bool {
        self.arena.iter().any(|(id, node)| {
            let NodeData::ArrowFunction(arrow) = &node.data else {
                return false;
            };
            if !declaration_has_modifier_in_list(
                self.arena,
                arrow.modifiers.as_ref(),
                SyntaxKind::AsyncKeyword,
            ) {
                return false;
            }
            let mut current = id;
            while let Some(parent) = self.arena.get(current).and_then(|node| node.parent) {
                if parent == body {
                    return true;
                }
                if matches!(
                    self.arena.get(parent).map(|node| &node.data),
                    Some(
                        NodeData::FunctionDeclaration(_)
                            | NodeData::FunctionExpression(_)
                            | NodeData::MethodDeclaration(_)
                            | NodeData::GetAccessorDeclaration(_)
                            | NodeData::SetAccessorDeclaration(_)
                    )
                ) {
                    return false;
                }
                current = parent;
            }
            false
        })
    }

    fn emit_function_body_with_this_capture(&mut self, body: NodeId) -> Result<(), EmitError> {
        self.writer.write("{");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("var _this = this;");
        self.writer.newline();
        let previous = self.this_alias;
        self.this_alias = Some("_this");
        let result = self.emit_block_statements(body);
        self.this_alias = previous;
        result?;
        self.writer.indent -= 1;
        self.writer.write("}");
        Ok(())
    }

    fn emit_downlevel_async_function_body(
        &mut self,
        body: NodeId,
        this_argument: &str,
    ) -> Result<(), EmitError> {
        if self.settings.target < ScriptTarget::Es2015 {
            return self.emit_es5_async_function_body(
                body,
                None,
                this_argument,
                "this",
                "_a",
                None,
                false,
            );
        }
        self.writer.write("{");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("return ");
        self.emit_awaiter_call(body, None, this_argument)?;
        self.writer.write(";");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("}");
        Ok(())
    }

    fn es5_generator_for_of(&self, body: NodeId) -> Result<Option<Es5GeneratorForOf>, EmitError> {
        let body_node = self.node(body)?;
        let NodeData::Block(block) = &body_node.data else {
            return Ok(None);
        };
        let [loop_id] = block.statements.nodes.as_slice() else {
            return Ok(None);
        };
        let loop_node = self.node(*loop_id)?;
        let NodeData::ForInOrOfStatement(for_of) = &loop_node.data else {
            return Ok(None);
        };
        if loop_node.kind != SyntaxKind::ForOfStatement || for_of.await_modifier.is_some() {
            return Ok(None);
        }
        let initializer = self.node(for_of.initializer)?;
        let NodeData::VariableDeclarationList(declarations) = &initializer.data else {
            return Ok(None);
        };
        let [declaration_id] = declarations.declarations.nodes.as_slice() else {
            return Ok(None);
        };
        let declaration = self.node(*declaration_id)?;
        let NodeData::VariableDeclaration(declaration) = &declaration.data else {
            return Ok(None);
        };
        let Ok(loop_variable) = self.identifier_text(declaration.name) else {
            return Ok(None);
        };
        let loop_variable = loop_variable.to_owned();
        let loop_body = self.node(for_of.statement)?;
        let NodeData::Block(loop_body) = &loop_body.data else {
            return Ok(None);
        };
        let Some((last, before_yield)) = loop_body.statements.nodes.split_last() else {
            return Ok(None);
        };
        let last = self.node(*last)?;
        let NodeData::ExpressionStatement(last) = &last.data else {
            return Ok(None);
        };
        let yielded = self.node(last.expression)?;
        let NodeData::YieldExpression(yielded) = &yielded.data else {
            return Ok(None);
        };
        let Some(yielded) = yielded.expression else {
            return Ok(None);
        };
        Ok(Some(Es5GeneratorForOf {
            loop_variable,
            iterable: for_of.expression,
            before_yield: before_yield.to_vec(),
            yielded,
        }))
    }

    fn emit_es5_generator_body(&mut self, body: NodeId) -> Result<(), EmitError> {
        if self.es5_generator_for_of(body)?.is_some() {
            return self.emit_es5_generator_for_of_body(body);
        }
        let node = self.node(body)?.clone();
        let NodeData::Block(block) = &node.data else {
            return Err(Self::unsupported(body, node.kind));
        };
        self.writer.write("{");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer
            .write("return __generator(this, function (_a) {");
        self.writer.newline();
        self.writer.indent += 1;
        self.emit_es5_generator_state_machine(&block.statements.nodes, "_a")?;
        self.writer.indent -= 1;
        self.writer.write("});");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("}");
        Ok(())
    }

    fn emit_es5_generator_state_machine(
        &mut self,
        statements: &[NodeId],
        state: &str,
    ) -> Result<(), EmitError> {
        let yields = statements
            .iter()
            .filter(|statement| self.direct_yield_expression(**statement).is_some())
            .count();
        if yields == 0 {
            for statement in statements {
                if let Some(NodeData::ReturnStatement(return_statement)) =
                    self.arena.get(*statement).map(|node| &node.data)
                {
                    self.emit_es5_generator_return(return_statement.expression)?;
                } else {
                    self.emit_statement(*statement)?;
                }
            }
            if !statements.last().is_some_and(|statement| {
                matches!(
                    self.arena.get(*statement).map(|node| &node.data),
                    Some(NodeData::ReturnStatement(_))
                )
            }) {
                self.writer.write("return [2 /*return*/];");
                self.writer.newline();
            }
            return Ok(());
        }

        self.writer.write("switch (");
        self.writer.write(state);
        self.writer.write(".label) {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("case 0:");
        self.writer.newline();
        self.writer.indent += 1;
        let mut case = 0;
        for statement in statements {
            if let Some(yielded) = self.direct_yield_expression(*statement).cloned() {
                let expression = yielded.expression;
                self.writer.write(if yielded.asterisk_token.is_some() {
                    "return [5 /*yield**/, __values("
                } else {
                    "return [4 /*yield*/, "
                });
                if let Some(expression) = expression {
                    self.emit_expression(expression, 0)?;
                } else {
                    self.writer.write("void 0");
                }
                if yielded.asterisk_token.is_some() {
                    self.writer.write(")");
                }
                self.writer.write("];");
                self.writer.newline();
                self.writer.indent -= 1;
                case += 1;
                self.writer.write("case ");
                self.writer.write(&case.to_string());
                self.writer.write(":");
                self.writer.newline();
                self.writer.indent += 1;
                self.writer.write(state);
                self.writer.write(".sent();");
                self.writer.newline();
            } else if let Some(NodeData::ReturnStatement(return_statement)) =
                self.arena.get(*statement).map(|node| &node.data)
            {
                self.emit_es5_generator_return(return_statement.expression)?;
            } else {
                self.emit_statement(*statement)?;
            }
        }
        if !statements.last().is_some_and(|statement| {
            matches!(
                self.arena.get(*statement).map(|node| &node.data),
                Some(NodeData::ReturnStatement(_))
            )
        }) {
            self.writer.write("return [2 /*return*/];");
            self.writer.newline();
        }
        self.writer.indent -= 2;
        self.writer.write("}");
        self.writer.newline();
        Ok(())
    }

    fn direct_yield_expression(&self, statement: NodeId) -> Option<&ts_ast::YieldExpressionData> {
        let NodeData::ExpressionStatement(expression) = &self.arena.get(statement)?.data else {
            return None;
        };
        let NodeData::YieldExpression(yielded) = &self.arena.get(expression.expression)?.data
        else {
            return None;
        };
        Some(yielded)
    }

    fn emit_es5_generator_return(&mut self, expression: Option<NodeId>) -> Result<(), EmitError> {
        self.writer.write("return [2 /*return*/");
        if let Some(expression) = expression {
            self.writer.write(", ");
            self.emit_expression(expression, 0)?;
        }
        self.writer.write("];");
        self.writer.newline();
        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    fn emit_es5_generator_for_of_body(&mut self, body: NodeId) -> Result<(), EmitError> {
        let info = self
            .es5_generator_for_of(body)?
            .expect("downlevel generator shape checked");
        self.writer.write("{");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("var _loop_1, _a, _b, ");
        self.writer.write(&info.loop_variable);
        self.writer.write(", e_1_1;");
        self.writer.newline();
        self.writer.write("var e_1, _c;");
        self.writer.newline();
        self.writer
            .write("return __generator(this, function (_d) {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("switch (_d.label) {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("case 0:");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("_loop_1 = function (");
        self.writer.write(&info.loop_variable);
        self.writer.write(") {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer
            .write("return __generator(this, function (_e) {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("switch (_e.label) {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("case 0:");
        self.writer.newline();
        self.writer.indent += 1;
        for statement in &info.before_yield {
            self.emit_statement(*statement)?;
        }
        self.writer.write("return [4 /*yield*/, ");
        self.emit_expression(info.yielded, 0)?;
        self.writer.write("];");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("case 1:");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("_e.sent();");
        self.writer.newline();
        self.writer.write("return [2 /*return*/];");
        self.writer.newline();
        self.writer.indent -= 2;
        self.writer.write("}");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("});");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("};");
        self.writer.newline();
        self.writer.write("_d.label = 1;");
        self.writer.newline();
        self.writer.indent -= 1;
        for line in ["case 1:", "    _d.trys.push([1, 6, 7, 8]);"] {
            self.writer.write(line);
            self.writer.newline();
        }
        self.writer.indent += 1;
        self.writer.write("_a = __values(");
        self.emit_expression(info.iterable, 0)?;
        self.writer.write("), _b = _a.next();");
        self.writer.newline();
        self.writer.write("_d.label = 2;");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("case 2:");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("if (!!_b.done) return [3 /*break*/, 5];");
        self.writer.newline();
        self.writer.write(&info.loop_variable);
        self.writer.write(" = _b.value;");
        self.writer.newline();
        self.writer.write("return [5 /*yield**/, _loop_1(");
        self.writer.write(&info.loop_variable);
        self.writer.write(")];");
        self.writer.newline();
        self.writer.indent -= 1;
        for line in [
            "case 3:",
            "    _d.sent();",
            "    _d.label = 4;",
            "case 4:",
            "    _b = _a.next();",
            "    return [3 /*break*/, 2];",
            "case 5: return [3 /*break*/, 8];",
            "case 6:",
            "    e_1_1 = _d.sent();",
            "    e_1 = { error: e_1_1 };",
            "    return [3 /*break*/, 8];",
            "case 7:",
            "    try {",
            "        if (_b && !_b.done && (_c = _a.return)) _c.call(_a);",
            "    }",
            "    finally { if (e_1) throw e_1.error; }",
            "    return [7 /*endfinally*/];",
            "case 8: return [2 /*return*/];",
        ] {
            self.writer.write(line);
            self.writer.newline();
        }
        self.writer.indent -= 1;
        self.writer.write("}");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("});");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("}");
        Ok(())
    }

    fn emit_downlevel_async_generator_body(
        &mut self,
        body: NodeId,
        inner_name: &str,
    ) -> Result<(), EmitError> {
        self.writer.write("{");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer
            .write("return __asyncGenerator(this, arguments, function* ");
        self.writer.write(inner_name);
        self.writer.write("() {");
        self.writer.newline();
        self.writer.indent += 1;
        let previous = self.async_expression_transform;
        self.async_expression_transform = AsyncExpressionTransform::AsyncGenerator;
        let result = self.emit_block_statements(body);
        self.async_expression_transform = previous;
        result?;
        self.writer.indent -= 1;
        self.writer.write("});");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("}");
        Ok(())
    }

    fn emit_es5_downlevel_async_generator_body(
        &mut self,
        body: NodeId,
        inner_name: &str,
    ) -> Result<(), EmitError> {
        let node = self.node(body)?.clone();
        let NodeData::Block(block) = &node.data else {
            return Err(Self::unsupported(body, node.kind));
        };
        self.writer.write("{");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer
            .write("return __asyncGenerator(this, arguments, function ");
        self.writer.write(inner_name);
        self.writer.write("() {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer
            .write("return __generator(this, function (_a) {");
        self.writer.newline();
        self.writer.indent += 1;
        self.emit_es5_async_generator_state_machine(&block.statements.nodes, "_a")?;
        self.writer.indent -= 1;
        self.writer.write("});");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("});");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("}");
        Ok(())
    }

    fn emit_es5_async_generator_state_machine(
        &mut self,
        statements: &[NodeId],
        state: &str,
    ) -> Result<(), EmitError> {
        let has_suspension = statements.iter().any(|statement| {
            self.direct_yield_expression(*statement).is_some()
                || self.direct_await_expression(*statement).is_some()
        });
        if !has_suspension {
            for statement in statements {
                if let Some(NodeData::ReturnStatement(return_statement)) =
                    self.arena.get(*statement).map(|node| &node.data)
                {
                    self.emit_es5_generator_return(return_statement.expression)?;
                } else {
                    self.emit_statement(*statement)?;
                }
            }
            if !self.statements_end_in_return(statements) {
                self.writer.write("return [2 /*return*/];");
                self.writer.newline();
            }
            return Ok(());
        }

        self.writer.write("switch (");
        self.writer.write(state);
        self.writer.write(".label) {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("case 0:");
        self.writer.newline();
        self.writer.indent += 1;
        let mut case = 0;
        for statement in statements {
            if let Some(yielded) = self.direct_yield_expression(*statement).cloned() {
                self.writer.write("return [4 /*yield*/, __await(");
                if let Some(expression) = yielded.expression {
                    self.emit_expression(expression, 0)?;
                } else {
                    self.writer.write("void 0");
                }
                self.writer.write(")];");
                self.writer.newline();
                self.writer.indent -= 1;
                case += 1;
                self.writer.write("case ");
                self.writer.write(&case.to_string());
                self.writer.write(": return [4 /*yield*/, ");
                self.writer.write(state);
                self.writer.write(".sent()];");
                self.writer.newline();
                self.writer.indent += 1;
                self.emit_es5_state_case(&mut case);
                self.writer.write(state);
                self.writer.write(".sent();");
                self.writer.newline();
            } else if let Some(awaited) = self.direct_await_expression(*statement) {
                self.writer.write("return [4 /*yield*/, __await(");
                self.emit_expression(awaited, 0)?;
                self.writer.write(")];");
                self.writer.newline();
                self.emit_es5_state_case(&mut case);
                self.writer.write(state);
                self.writer.write(".sent();");
                self.writer.newline();
            } else if let Some(NodeData::ReturnStatement(return_statement)) =
                self.arena.get(*statement).map(|node| &node.data)
            {
                self.emit_es5_generator_return(return_statement.expression)?;
            } else {
                self.emit_statement(*statement)?;
            }
        }
        if !self.statements_end_in_return(statements) {
            self.writer.write("return [2 /*return*/];");
            self.writer.newline();
        }
        self.writer.indent -= 2;
        self.writer.write("}");
        self.writer.newline();
        Ok(())
    }

    fn emit_es5_state_case(&mut self, case: &mut usize) {
        self.writer.indent -= 1;
        *case += 1;
        self.writer.write("case ");
        self.writer.write(&case.to_string());
        self.writer.write(":");
        self.writer.newline();
        self.writer.indent += 1;
    }

    fn direct_await_expression(&self, statement: NodeId) -> Option<NodeId> {
        let NodeData::ExpressionStatement(expression) = &self.arena.get(statement)?.data else {
            return None;
        };
        let NodeData::AwaitExpression(awaited) = &self.arena.get(expression.expression)?.data
        else {
            return None;
        };
        Some(awaited.expression)
    }

    fn statements_end_in_return(&self, statements: &[NodeId]) -> bool {
        statements.last().is_some_and(|statement| {
            matches!(
                self.arena.get(*statement).map(|node| &node.data),
                Some(NodeData::ReturnStatement(_))
            )
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_es5_async_function_body(
        &mut self,
        body: NodeId,
        expression_body: Option<NodeId>,
        this_argument: &str,
        generator_this: &str,
        state_parameter: &str,
        object_rest: Option<(NodeId, &str, Option<&str>)>,
        compact_outer: bool,
    ) -> Result<(), EmitError> {
        self.writer.write("{");
        if compact_outer {
            self.writer.write(" return ");
        } else {
            self.writer.newline();
        }
        if !compact_outer {
            self.writer.indent += 1;
        }
        if !compact_outer {
            self.writer.write("return ");
        }
        self.writer.write("__awaiter(");
        self.writer.write(this_argument);
        self.writer.write(", void 0, void 0, function () {");
        let callback_is_indented = !compact_outer
            || object_rest.is_some()
            || (expression_body.is_none() && self.this_alias != Some("_a"));
        if callback_is_indented {
            self.writer.newline();
        } else {
            self.writer.write(" ");
        }
        if callback_is_indented {
            self.writer.indent += 1;
        }

        if let Some((pattern, parameter, expression_temp)) = object_rest {
            if let Some(temp) = expression_temp {
                self.writer.write("var ");
                self.writer.write(temp);
                self.writer.write(";");
                self.writer.newline();
            }
            self.emit_object_rest_parameter_prologue(pattern, parameter)?;
        } else if expression_body.is_none()
            && let Some(loop_info) = self.es5_async_captured_for_loop(body)?
        {
            self.emit_es5_async_captured_loop_hoists(&loop_info)?;
        }

        self.writer.write("return __generator(");
        self.writer.write(generator_this);
        self.writer.write(", function (");
        self.writer.write(state_parameter);
        self.writer.write(") {");
        self.writer.newline();
        self.writer.indent += 1;

        if let Some(expression) = expression_body {
            self.emit_es5_async_expression_state_machine(
                expression,
                state_parameter,
                object_rest.and_then(|(_, _, temp)| temp),
            )?;
        } else if let Some(loop_info) = self.es5_async_captured_for_loop(body)? {
            self.emit_es5_async_captured_loop_state_machine(&loop_info, state_parameter)?;
        } else {
            self.emit_es5_async_block_state_machine(body, state_parameter)?;
        }

        self.writer.indent -= 1;
        self.writer.write("});");
        if compact_outer && !callback_is_indented {
            self.writer.write(" });");
        } else {
            self.writer.newline();
        }
        if callback_is_indented {
            self.writer.indent -= 1;
        }
        if !compact_outer {
            self.writer.write("});");
            self.writer.newline();
            self.writer.indent -= 1;
            self.writer.write("}");
        } else if callback_is_indented {
            self.writer.write("}); }");
        } else {
            self.writer.write(" }");
        }
        Ok(())
    }

    fn emit_es5_async_expression_state_machine(
        &mut self,
        expression: NodeId,
        state: &str,
        call_temp: Option<&str>,
    ) -> Result<(), EmitError> {
        let node = self.node(expression)?.clone();
        if let NodeData::CallExpression(call) = &node.data
            && call.arguments.nodes.len() == 1
            && let Some(NodeData::AwaitExpression(awaited)) = self
                .arena
                .get(call.arguments.nodes[0])
                .map(|node| &node.data)
            && let Some(temp) = call_temp
        {
            self.writer.write("switch (");
            self.writer.write(state);
            self.writer.write(".label) {");
            self.writer.newline();
            self.writer.indent += 1;
            self.writer.write("case 0:");
            self.writer.newline();
            self.writer.indent += 1;
            self.writer.write(temp);
            self.writer.write(" = ");
            self.emit_expression(call.expression, 0)?;
            self.writer.write(";");
            self.writer.newline();
            self.writer.write("return [4 /*yield*/, ");
            self.emit_expression(awaited.expression, 0)?;
            self.writer.write("];");
            self.writer.newline();
            self.writer.indent -= 1;
            self.writer.write("case 1: return [2 /*return*/, ");
            self.writer.write(temp);
            self.writer.write(".apply(void 0, [");
            self.writer.write(state);
            self.writer.write(".sent()])];");
            self.writer.newline();
            self.writer.indent -= 1;
            self.writer.write("}");
            self.writer.newline();
            return Ok(());
        }
        self.writer.write("return [2 /*return*/, ");
        self.emit_expression(expression, 0)?;
        self.writer.write("];");
        self.writer.newline();
        Ok(())
    }

    fn emit_es5_async_block_state_machine(
        &mut self,
        body: NodeId,
        state: &str,
    ) -> Result<(), EmitError> {
        let node = self.node(body)?.clone();
        let NodeData::Block(block) = &node.data else {
            return Err(Self::unsupported(body, node.kind));
        };
        if block.statements.nodes.is_empty() {
            self.writer.write("return [2 /*return*/];");
            self.writer.newline();
            return Ok(());
        }
        // The general sequential form covers ordinary statements and direct awaits.
        let await_index = block.statements.nodes.iter().position(|statement| {
            matches!(
                self.arena.get(*statement).map(|node| &node.data),
                Some(NodeData::ExpressionStatement(expression))
                    if matches!(self.arena.get(expression.expression).map(|node| &node.data), Some(NodeData::AwaitExpression(_)))
            )
        });
        let Some(await_index) = await_index else {
            for statement in &block.statements.nodes {
                if let Some(NodeData::ReturnStatement(return_statement)) =
                    self.arena.get(*statement).map(|node| &node.data)
                {
                    self.writer.write("return [2 /*return*/");
                    if let Some(expression) = return_statement.expression {
                        self.writer.write(", ");
                        self.emit_expression(expression, 0)?;
                    }
                    self.writer.write("];");
                    self.writer.newline();
                } else {
                    self.emit_statement(*statement)?;
                }
            }
            self.writer.write("return [2 /*return*/];");
            self.writer.newline();
            return Ok(());
        };
        self.writer.write("switch (");
        self.writer.write(state);
        self.writer.write(".label) {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("case 0:");
        self.writer.newline();
        self.writer.indent += 1;
        for statement in &block.statements.nodes[..await_index] {
            self.emit_statement(*statement)?;
        }
        let statement = self.node(block.statements.nodes[await_index])?.clone();
        let NodeData::ExpressionStatement(expression) = &statement.data else {
            unreachable!()
        };
        let awaited = self.node(expression.expression)?.clone();
        let NodeData::AwaitExpression(awaited) = &awaited.data else {
            unreachable!()
        };
        self.writer.write("return [4 /*yield*/, ");
        self.emit_expression(awaited.expression, 0)?;
        self.writer.write("];");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("case 1:");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write(state);
        self.writer.write(".sent();");
        self.writer.newline();
        for statement in &block.statements.nodes[await_index + 1..] {
            self.emit_statement(*statement)?;
        }
        self.writer.write("return [2 /*return*/];");
        self.writer.newline();
        self.writer.indent -= 2;
        self.writer.write("}");
        self.writer.newline();
        Ok(())
    }

    fn es5_async_captured_for_loop(
        &self,
        body: NodeId,
    ) -> Result<Option<Es5AsyncCapturedLoop>, EmitError> {
        let body_node = self.node(body)?.clone();
        let NodeData::Block(block) = &body_node.data else {
            return Ok(None);
        };
        let Some((for_index, for_id)) =
            block
                .statements
                .nodes
                .iter()
                .enumerate()
                .find(|(_, statement)| {
                    matches!(
                        self.arena.get(**statement).map(|node| &node.data),
                        Some(NodeData::ForStatement(_))
                    )
                })
        else {
            return Ok(None);
        };
        let for_node = self.node(*for_id)?.clone();
        let NodeData::ForStatement(for_statement) = &for_node.data else {
            return Ok(None);
        };
        let (Some(initializer), Some(condition), Some(incrementor)) = (
            for_statement.initializer,
            for_statement.condition,
            for_statement.incrementor,
        ) else {
            return Ok(None);
        };
        let initializer_node = self.node(initializer)?.clone();
        let NodeData::VariableDeclarationList(declarations) = &initializer_node.data else {
            return Ok(None);
        };
        let Some(declaration_id) = declarations.declarations.nodes.first().copied() else {
            return Ok(None);
        };
        let declaration_node = self.node(declaration_id)?.clone();
        let NodeData::VariableDeclaration(declaration) = &declaration_node.data else {
            return Ok(None);
        };
        let Some(initial_value) = declaration.initializer else {
            return Ok(None);
        };
        let loop_variable = self.identifier_text(declaration.name)?.to_owned();
        let loop_body_node = self.node(for_statement.statement)?.clone();
        let NodeData::Block(loop_body) = &loop_body_node.data else {
            return Ok(None);
        };
        let Some((await_index, awaited)) =
            loop_body
                .statements
                .nodes
                .iter()
                .enumerate()
                .find_map(|(index, statement)| {
                    let NodeData::ExpressionStatement(expression) =
                        self.arena.get(*statement).map(|node| &node.data)?
                    else {
                        return None;
                    };
                    let NodeData::AwaitExpression(awaited) = self
                        .arena
                        .get(expression.expression)
                        .map(|node| &node.data)?
                    else {
                        return None;
                    };
                    Some((index, awaited.expression))
                })
        else {
            return Ok(None);
        };
        let mut after_await = loop_body.statements.nodes[await_index + 1..].to_vec();
        let control = after_await
            .last()
            .and_then(|statement| self.arena.get(*statement))
            .map_or(Es5AsyncLoopControl::None, |node| match &node.data {
                NodeData::BreakStatement(_) => Es5AsyncLoopControl::Break,
                NodeData::ContinueStatement(_) => Es5AsyncLoopControl::Continue,
                NodeData::ReturnStatement(statement) => statement
                    .expression
                    .map_or(Es5AsyncLoopControl::None, Es5AsyncLoopControl::Return),
                _ => Es5AsyncLoopControl::None,
            });
        if !matches!(control, Es5AsyncLoopControl::None) {
            after_await.pop();
        }
        Ok(Some(Es5AsyncCapturedLoop {
            prelude: block.statements.nodes[..for_index].to_vec(),
            loop_variable,
            initializer: initial_value,
            condition,
            incrementor,
            awaited,
            after_await,
            control,
        }))
    }

    fn emit_es5_async_captured_loop_hoists(
        &mut self,
        info: &Es5AsyncCapturedLoop,
    ) -> Result<(), EmitError> {
        let loop_number = self.async_loop_counter + 1;
        self.writer.write("var ");
        let mut names = Vec::new();
        for statement in &info.prelude {
            let Some(NodeData::VariableStatement(variable)) =
                self.arena.get(*statement).map(|node| &node.data)
            else {
                continue;
            };
            let list_node = self.node(variable.declaration_list)?.clone();
            let NodeData::VariableDeclarationList(list) = &list_node.data else {
                continue;
            };
            for declaration in &list.declarations.nodes {
                let declaration_node = self.node(*declaration)?.clone();
                let NodeData::VariableDeclaration(declaration) = &declaration_node.data else {
                    continue;
                };
                names.push(self.identifier_text(declaration.name)?.to_owned());
            }
        }
        names.push(format!("_loop_{loop_number}"));
        names.push(info.loop_variable.clone());
        if matches!(
            info.control,
            Es5AsyncLoopControl::Break | Es5AsyncLoopControl::Return(_)
        ) {
            names.push(format!("state_{}", self.async_control_counter + 1));
        }
        self.writer.write(&names.join(", "));
        self.writer.write(";");
        self.writer.newline();
        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    fn emit_es5_async_captured_loop_state_machine(
        &mut self,
        info: &Es5AsyncCapturedLoop,
        state: &str,
    ) -> Result<(), EmitError> {
        let loop_number = self.async_loop_counter + 1;
        let loop_name = format!("_loop_{loop_number}");
        let control_name = matches!(
            info.control,
            Es5AsyncLoopControl::Break | Es5AsyncLoopControl::Return(_)
        )
        .then(|| format!("state_{}", self.async_control_counter + 1));
        self.writer.write("switch (");
        self.writer.write(state);
        self.writer.write(".label) {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("case 0:");
        self.writer.newline();
        self.writer.indent += 1;
        for statement in &info.prelude {
            let Some(NodeData::VariableStatement(variable)) =
                self.arena.get(*statement).map(|node| &node.data)
            else {
                continue;
            };
            let list_node = self.node(variable.declaration_list)?.clone();
            let NodeData::VariableDeclarationList(list) = &list_node.data else {
                continue;
            };
            for declaration in &list.declarations.nodes {
                let declaration_node = self.node(*declaration)?.clone();
                let NodeData::VariableDeclaration(declaration) = &declaration_node.data else {
                    continue;
                };
                self.emit_expression(declaration.name, 0)?;
                if let Some(initializer) = declaration.initializer {
                    self.writer.write(" = ");
                    self.emit_expression(initializer, 0)?;
                }
                self.writer.write(";");
                self.writer.newline();
            }
        }
        self.writer.write(&loop_name);
        self.writer.write(" = function (");
        self.writer.write(&info.loop_variable);
        self.writer.write(") {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer
            .write("return __generator(this, function (_b) {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("switch (_b.label) {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("case 0: return [4 /*yield*/, ");
        self.emit_expression(info.awaited, 0)?;
        self.writer.write("];");
        self.writer.newline();
        self.writer.write("case 1:");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("_b.sent();");
        self.writer.newline();
        for statement in &info.after_await {
            self.emit_statement(*statement)?;
        }
        self.writer.write("return [2 /*return*/");
        match info.control {
            Es5AsyncLoopControl::None => {}
            Es5AsyncLoopControl::Break => self.writer.write(", \"break\""),
            Es5AsyncLoopControl::Continue => self.writer.write(", \"continue\""),
            Es5AsyncLoopControl::Return(expression) => {
                self.writer.write(", { value: ");
                self.emit_expression(expression, 0)?;
                self.writer.write(" }");
            }
        }
        self.writer.write("];");
        self.writer.newline();
        self.writer.indent -= 2;
        self.writer.write("}");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("});");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("};");
        self.writer.newline();
        self.writer.write(&info.loop_variable);
        self.writer.write(" = ");
        self.emit_expression(info.initializer, 0)?;
        self.writer.write(";");
        self.writer.newline();
        self.writer.write(state);
        self.writer.write(".label = 1;");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("case 1:");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer.write("if (!(");
        self.emit_expression(info.condition, 0)?;
        self.writer.write(")) return [3 /*break*/, 4];");
        self.writer.newline();
        self.writer.write("return [5 /*yield**/, ");
        self.writer.write(&loop_name);
        self.writer.write("(");
        self.writer.write(&info.loop_variable);
        self.writer.write(")];");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("case 2:");
        self.writer.newline();
        self.writer.indent += 1;
        if let Some(control_name) = &control_name {
            self.writer.write(control_name);
            self.writer.write(" = ");
        }
        self.writer.write(state);
        self.writer.write(".sent();");
        self.writer.newline();
        if let Some(control_name) = &control_name {
            match info.control {
                Es5AsyncLoopControl::Break => {
                    self.writer.write("if (");
                    self.writer.write(control_name);
                    self.writer.write(" === \"break\")");
                    self.writer.newline();
                    self.writer.indent += 1;
                    self.writer.write("return [3 /*break*/, 4];");
                    self.writer.newline();
                    self.writer.indent -= 1;
                }
                Es5AsyncLoopControl::Return(_) => {
                    self.writer.write("if (typeof ");
                    self.writer.write(control_name);
                    self.writer.write(" === \"object\")");
                    self.writer.newline();
                    self.writer.indent += 1;
                    self.writer.write("return [2 /*return*/, ");
                    self.writer.write(control_name);
                    self.writer.write(".value];");
                    self.writer.newline();
                    self.writer.indent -= 1;
                }
                _ => {}
            }
        }
        self.writer.write(state);
        self.writer.write(".label = 3;");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("case 3:");
        self.writer.newline();
        self.writer.indent += 1;
        self.emit_expression(info.incrementor, 0)?;
        self.writer.write(";");
        self.writer.newline();
        self.writer.write("return [3 /*break*/, 1];");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("case 4: return [2 /*return*/];");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("}");
        self.writer.newline();
        self.async_loop_counter += 1;
        if control_name.is_some() {
            self.async_control_counter += 1;
        }
        Ok(())
    }

    fn emit_awaiter_call(
        &mut self,
        body: NodeId,
        expression_body: Option<NodeId>,
        this_argument: &str,
    ) -> Result<(), EmitError> {
        self.writer.write("__awaiter(");
        self.writer.write(this_argument);
        self.writer.write(", void 0, void 0, function* () ");
        let previous = self.async_expression_transform;
        self.async_expression_transform = AsyncExpressionTransform::AwaitAsYield;
        let result = if let Some(expression) = expression_body {
            self.writer.write("{ return ");
            self.emit_expression(expression, 0)?;
            self.writer.write("; }");
            Ok(())
        } else {
            self.emit_function_body(body)
        };
        self.async_expression_transform = previous;
        result?;
        self.writer.write(")");
        Ok(())
    }

    fn async_arrow_object_rest_parameter(
        &self,
        data: &ts_ast::ArrowFunctionData,
    ) -> Option<NodeId> {
        if data.parameters.nodes.len() != 1 {
            return None;
        }
        let parameter = self.arena.get(data.parameters.nodes[0])?;
        let NodeData::ParameterDeclaration(parameter) = &parameter.data else {
            return None;
        };
        let pattern_node = self.arena.get(parameter.name)?;
        let NodeData::BindingPattern(pattern) = &pattern_node.data else {
            return None;
        };
        (pattern_node.kind == SyntaxKind::ObjectBindingPattern
            && pattern.elements.nodes.iter().any(|element| {
                matches!(
                    self.arena.get(*element).map(|node| &node.data),
                    Some(NodeData::BindingElement(element)) if element.dot_dot_dot_token.is_some()
                )
            }))
        .then_some(parameter.name)
    }

    fn emit_awaiter_call_with_object_rest_parameter(
        &mut self,
        body: NodeId,
        pattern: NodeId,
        parameter_temp: &str,
        this_argument: &str,
    ) -> Result<(), EmitError> {
        self.writer.write("__awaiter(");
        self.writer.write(this_argument);
        self.writer.write(", void 0, void 0, function* () {");
        self.writer.newline();
        self.writer.indent += 1;
        self.emit_object_rest_parameter_prologue(pattern, parameter_temp)?;
        if matches!(&self.node(body)?.data, NodeData::Block(_)) {
            let previous = self.async_expression_transform;
            self.async_expression_transform = AsyncExpressionTransform::AwaitAsYield;
            let result = self.emit_block_statements(body);
            self.async_expression_transform = previous;
            result?;
        } else {
            self.writer.write("return ");
            let previous = self.async_expression_transform;
            self.async_expression_transform = AsyncExpressionTransform::AwaitAsYield;
            let result = self.emit_expression(body, 0);
            self.async_expression_transform = previous;
            result?;
            self.writer.write(";");
            self.writer.newline();
        }
        self.writer.indent -= 1;
        self.writer.write("})");
        Ok(())
    }

    fn emit_object_rest_parameter_prologue(
        &mut self,
        pattern: NodeId,
        parameter_temp: &str,
    ) -> Result<(), EmitError> {
        let pattern_node = self.node(pattern)?.clone();
        let NodeData::BindingPattern(pattern) = &pattern_node.data else {
            return Err(Self::unsupported(pattern, pattern_node.kind));
        };
        let mut ordinary = Vec::new();
        let mut rest = None;
        for element_id in &pattern.elements.nodes {
            let element_node = self.node(*element_id)?.clone();
            let NodeData::BindingElement(element) = &element_node.data else {
                return Err(Self::unsupported(*element_id, element_node.kind));
            };
            if element.dot_dot_dot_token.is_some() {
                rest = element.name;
            } else {
                ordinary.push(*element_id);
            }
        }
        self.writer.write("var ");
        if self.settings.target < ScriptTarget::Es2015 {
            for (index, element_id) in ordinary.iter().enumerate() {
                if index != 0 {
                    self.writer.write(", ");
                }
                let element_node = self.node(*element_id)?.clone();
                let NodeData::BindingElement(element) = &element_node.data else {
                    return Err(Self::unsupported(*element_id, element_node.kind));
                };
                let name = element
                    .name
                    .ok_or_else(|| Self::unsupported(*element_id, SyntaxKind::BindingElement))?;
                self.emit_expression(name, 0)?;
                self.writer.write(" = ");
                self.writer.write(parameter_temp);
                self.emit_downlevel_member_access(element.property_name.unwrap_or(name))?;
            }
        } else {
            self.writer.write("{ ");
            for (index, element) in ordinary.iter().enumerate() {
                if index != 0 {
                    self.writer.write(", ");
                }
                self.emit_expression(*element, 0)?;
            }
            self.writer.write(" } = ");
            self.writer.write(parameter_temp);
        }
        if let Some(rest) = rest {
            self.writer.write(", ");
            self.emit_expression(rest, 0)?;
            self.writer.write(" = __rest(");
            self.writer.write(parameter_temp);
            self.writer.write(", [");
            for (index, element_id) in ordinary.iter().enumerate() {
                if index != 0 {
                    self.writer.write(", ");
                }
                let element_node = self.node(*element_id)?.clone();
                let NodeData::BindingElement(element) = &element_node.data else {
                    return Err(Self::unsupported(*element_id, element_node.kind));
                };
                let property = element
                    .property_name
                    .or(element.name)
                    .ok_or_else(|| Self::unsupported(*element_id, SyntaxKind::BindingElement))?;
                let property_text =
                    declaration_name_text(self.arena, property).ok_or_else(|| {
                        Self::unsupported(property, self.node(property).unwrap().kind)
                    })?;
                write_quoted(&mut self.writer, property_text);
            }
            self.writer.write("])");
        }
        self.writer.write(";");
        self.writer.newline();
        Ok(())
    }

    fn emit_block_statements(&mut self, body: NodeId) -> Result<(), EmitError> {
        let body_node = self.node(body)?.clone();
        let NodeData::Block(block) = &body_node.data else {
            return Err(Self::unsupported(body, body_node.kind));
        };
        for statement in &block.statements.nodes {
            self.emit_statement(*statement)?;
        }
        Ok(())
    }

    fn arrow_is_nested_in_function(&self, arrow: NodeId) -> bool {
        let mut parent = self.arena.get(arrow).and_then(|node| node.parent);
        while let Some(id) = parent {
            let Some(node) = self.arena.get(id) else {
                break;
            };
            if matches!(
                node.data,
                NodeData::FunctionDeclaration(_)
                    | NodeData::FunctionExpression(_)
                    | NodeData::MethodDeclaration(_)
                    | NodeData::GetAccessorDeclaration(_)
                    | NodeData::SetAccessorDeclaration(_)
            ) {
                return true;
            }
            parent = node.parent;
        }
        false
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
        let mut emitted = false;
        for declaration in &data.declarations.nodes {
            let declaration_node = self.node(*declaration)?.clone();
            let NodeData::VariableDeclaration(declaration) = &declaration_node.data else {
                return Err(Self::unsupported(*declaration, declaration_node.kind));
            };
            if self.settings.target < ScriptTarget::Es2015
                && self.node(declaration.name)?.kind == SyntaxKind::ArrayBindingPattern
            {
                let value = if let Some(initializer) = declaration.initializer {
                    if self.array_binding_can_inline_initializer(declaration.name)
                        || matches!(
                            &self.node(initializer)?.data,
                            NodeData::Identifier(identifier)
                                if !self
                                    .binding_name_contains_identifier(
                                        declaration.name,
                                        &identifier.text,
                                    )?
                        )
                    {
                        DownlevelBindingValue::Node(initializer)
                    } else {
                        let temp = self.generated_names.generate_temp();
                        self.emit_downlevel_declarator_start(&mut emitted);
                        self.writer.write(&temp);
                        self.writer.write(" = ");
                        self.emit_expression(initializer, 1)?;
                        DownlevelBindingValue::Name(temp)
                    }
                } else {
                    DownlevelBindingValue::VoidZero
                };
                self.emit_downlevel_binding_declarators(
                    declaration.name,
                    value,
                    None,
                    &mut emitted,
                )?;
                continue;
            }
            self.emit_downlevel_declarator_start(&mut emitted);
            self.emit_expression(declaration.name, 0)?;
            if let Some(initializer) = declaration.initializer {
                self.writer.write(" = ");
                self.emit_expression(initializer, 1)?;
            }
        }
        Ok(())
    }

    fn array_binding_can_inline_initializer(&self, name: NodeId) -> bool {
        let Some(NodeData::BindingPattern(pattern)) = self.arena.get(name).map(|node| &node.data)
        else {
            return false;
        };
        let [element] = pattern.elements.nodes.as_slice() else {
            return false;
        };
        matches!(
            self.arena.get(*element).map(|node| &node.data),
            Some(NodeData::BindingElement(element))
                if element.dot_dot_dot_token.is_none()
                    && element.initializer.is_none()
                    && element.name.is_some_and(|name| {
                        matches!(
                            self.arena.get(name).map(|node| &node.data),
                            Some(NodeData::Identifier(_))
                        )
                    })
        )
    }

    fn binding_name_contains_identifier(
        &self,
        name: NodeId,
        identifier: &str,
    ) -> Result<bool, EmitError> {
        let node = self.node(name)?;
        match &node.data {
            NodeData::Identifier(data) => Ok(data.text == identifier),
            NodeData::BindingPattern(pattern) => {
                for element in &pattern.elements.nodes {
                    let element_node = self.node(*element)?;
                    if let NodeData::BindingElement(element) = &element_node.data
                        && let Some(name) = element.name
                        && self.binding_name_contains_identifier(name, identifier)?
                    {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Ok(false),
        }
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
        let lower_fields = self.settings.target < ScriptTarget::Es2022
            || self.settings.use_define_for_class_fields == Some(false);
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
        for (member_index, member) in data.members.nodes.iter().enumerate() {
            let node = self.node(*member)?.clone();
            let current_emitted = !self.class_member_is_abstract(&node)
                && match &node.data {
                    NodeData::MethodDeclaration(method) => method.body.is_some(),
                    NodeData::PropertyDeclaration(property) => {
                        self.property_is_auto_accessor(property) || !lower_fields
                    }
                    NodeData::GetAccessorDeclaration(accessor) => accessor.body.is_some(),
                    NodeData::SetAccessorDeclaration(accessor) => accessor.body.is_some(),
                    NodeData::ClassStaticBlockDeclaration(_) => true,
                    _ => false,
                };
            self.emit_source_comments_between_with_ownership(
                previous_end,
                node.range.start.get(),
                previous_emitted,
                current_emitted,
            );
            if previous_emitted {
                self.emit_class_empty_elements_between(previous_end, node.range.start.get());
            }
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
                    self.emit_function_body(method.body.expect("body checked above"))?;
                    self.writer.newline();
                }
                NodeData::MethodDeclaration(_) => {}
                NodeData::PropertyDeclaration(property)
                    if self.property_is_auto_accessor(property) =>
                {
                    let comment_end = data
                        .members
                        .nodes
                        .get(member_index + 1)
                        .and_then(|next| self.arena.get(*next).map(|node| node.range.start.get()))
                        .unwrap_or(data.members.range.end.get());
                    self.emit_native_auto_accessor(
                        data,
                        property,
                        node.range.end.get(),
                        comment_end,
                    )?;
                }
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
        self.emit_source_comments_between_with_ownership(
            previous_end,
            data.members.range.end.get(),
            previous_emitted,
            false,
        );
        if previous_emitted {
            self.emit_class_empty_elements_between(previous_end, data.members.range.end.get());
        }
        self.writer.indent -= 1;
        self.writer.write("}");
        if lower_fields {
            if (ScriptTarget::Es2015..ScriptTarget::Es2017).contains(&self.settings.target)
                && class_has_async_static_field(self.arena, data)
                && let Some(name) = data.name
            {
                self.writer.newline();
                self.writer.write("_a = ");
                self.emit_expression(name, 0)?;
                self.writer.write(";");
            }
            self.emit_native_static_fields(data)?;
        }
        Ok(())
    }

    fn emit_class_expression(
        &mut self,
        id: NodeId,
        data: &ts_ast::ClassExpressionData,
        parent_precedence: u8,
    ) -> Result<(), EmitError> {
        let declaration = Self::class_expression_as_declaration(data);
        let needs_post_class_lowering = self.settings.target < ScriptTarget::Es2022
            && self.class_expression_requires_post_class_lowering(&declaration);
        if needs_post_class_lowering {
            let Some(temp) = self.class_expression_temps.get(&id).cloned() else {
                return Err(Self::unsupported(id, SyntaxKind::ClassExpression));
            };
            let downlevel_name = (self.settings.target < ScriptTarget::Es2015)
                .then(|| self.class_expression_downlevel_name(id, &declaration));
            return self.emit_lowered_class_expression(
                id,
                &declaration,
                &temp,
                downlevel_name.as_deref(),
                parent_precedence > 0,
            );
        }
        if self.settings.target < ScriptTarget::Es2015 {
            let name = self.class_expression_downlevel_name(id, &declaration);
            return self.emit_downlevel_class_value(&declaration, &name);
        }
        self.emit_class(&declaration)
    }

    fn class_expression_downlevel_name(
        &mut self,
        id: NodeId,
        data: &ts_ast::ClassDeclarationData,
    ) -> String {
        if let Some(name) = data.name.and_then(|name| self.identifier_text(name).ok()) {
            return name.to_owned();
        }
        if data.members.nodes.iter().any(|member| {
            matches!(
                self.arena.get(*member).map(|node| &node.data),
                Some(NodeData::PropertyDeclaration(_))
            )
        }) {
            return self.generated_names.generate("class");
        }
        self.class_expression_inferred_name(id)
            .unwrap_or_else(|| "_class".to_owned())
    }

    fn class_expression_inferred_name(&self, id: NodeId) -> Option<String> {
        let parent = self.arena.get(id)?.parent?;
        let NodeData::VariableDeclaration(declaration) = &self.arena.get(parent)?.data else {
            return None;
        };
        (declaration.initializer == Some(id))
            .then(|| declaration_name_text(self.arena, declaration.name).map(str::to_owned))
            .flatten()
    }

    fn class_expression_as_declaration(
        data: &ts_ast::ClassExpressionData,
    ) -> ts_ast::ClassDeclarationData {
        ts_ast::ClassDeclarationData {
            flow_node: None,
            heritage_clauses: data.heritage_clauses.clone(),
            local_symbol: data.local_symbol,
            locals: data.locals.clone(),
            members: data.members.clone(),
            next_container: data.next_container,
            symbol: data.symbol,
            type_parameters: data.type_parameters.clone(),
            facts: data.facts,
            modifiers: data.modifiers.clone(),
            name: data.name,
        }
    }

    fn emit_lowered_class_expression(
        &mut self,
        id: NodeId,
        data: &ts_ast::ClassDeclarationData,
        temp: &str,
        downlevel_name: Option<&str>,
        wrap: bool,
    ) -> Result<(), EmitError> {
        if wrap {
            self.writer.write("(");
        }
        let mut core = data.clone();
        core.members.nodes.retain(|member| {
            let Some(node) = self.arena.get(*member) else {
                return true;
            };
            match &node.data {
                NodeData::ClassStaticBlockDeclaration(_) => false,
                NodeData::PropertyDeclaration(property) => {
                    !(property.initializer.is_some()
                        && self
                            .has_modifier(property.modifiers.as_ref(), SyntaxKind::StaticKeyword))
                }
                _ => true,
            }
        });
        self.writer.write(temp);
        self.writer.write(" = ");
        self.writer.indent += 1;
        if let Some(name) = downlevel_name {
            self.emit_downlevel_class_value(&core, name)?;
        } else {
            self.emit_class(&core)?;
        }
        self.writer.write(",");
        if data.name.is_none()
            && let Some(name) = self.class_expression_inferred_name(id)
        {
            self.writer.newline();
            self.writer.write("__setFunctionName(");
            self.writer.write(temp);
            self.writer.write(", ");
            write_quoted(&mut self.writer, &name);
            self.writer.write("),");
        }
        for member in &data.members.nodes {
            let node = self.node(*member)?.clone();
            match &node.data {
                NodeData::ClassStaticBlockDeclaration(block) => {
                    self.writer.newline();
                    self.writer.write("(() => ");
                    self.emit_block(block.body)?;
                    self.writer.write(")(),");
                }
                NodeData::PropertyDeclaration(property)
                    if property.initializer.is_some()
                        && self.has_modifier(
                            property.modifiers.as_ref(),
                            SyntaxKind::StaticKeyword,
                        ) =>
                {
                    self.writer.newline();
                    self.writer.write(temp);
                    self.emit_downlevel_member_access(property.name)?;
                    self.writer.write(" = ");
                    self.emit_expression(property.initializer.expect("initializer checked"), 1)?;
                    self.writer.write(",");
                }
                _ => {}
            }
        }
        self.writer.newline();
        self.writer.write(temp);
        self.writer.indent -= 1;
        if wrap {
            self.writer.write(")");
        }
        Ok(())
    }

    fn emit_native_auto_accessor(
        &mut self,
        class: &ts_ast::ClassDeclarationData,
        property: &ts_ast::PropertyDeclarationData,
        comment_start: u32,
        comment_end: u32,
    ) -> Result<(), EmitError> {
        let Some(storage) = self.auto_accessor_storage_name(class, property) else {
            return Ok(());
        };
        self.writer.write("get ");
        self.emit_expression(property.name, 0)?;
        self.writer
            .write("() { return __classPrivateFieldGet(this, ");
        self.writer.write(&storage);
        self.writer.write(", \"f\"); }");
        let comment_count = self.emitted_source_comments.len();
        self.emit_source_comments_between_with_trailing(comment_start, comment_end, true);
        if self.emitted_source_comments.len() == comment_count {
            self.writer.newline();
        }
        self.writer.write("set ");
        self.emit_expression(property.name, 0)?;
        self.writer.write("(value) { __classPrivateFieldSet(this, ");
        self.writer.write(&storage);
        self.writer.write(", value, \"f\"); }");
        self.writer.newline();
        Ok(())
    }

    fn class_expression_requires_post_class_lowering(
        &self,
        data: &ts_ast::ClassDeclarationData,
    ) -> bool {
        data.members.nodes.iter().any(|member| {
            let Some(node) = self.arena.get(*member) else {
                return false;
            };
            match &node.data {
                NodeData::PropertyDeclaration(property) => {
                    property.initializer.is_some()
                        && self.has_modifier(property.modifiers.as_ref(), SyntaxKind::StaticKeyword)
                }
                NodeData::ClassStaticBlockDeclaration(_) => true,
                _ => false,
            }
        })
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
        if !self.has_instance_field_initializers(data)
            && !self.has_parameter_properties(&method.parameters)
            && self.single_line_body_statement(body_id)?.is_some()
        {
            self.writer.write(" ");
            self.emit_function_body(body_id)?;
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
        self.writer.write("var ");
        self.writer.write(&name);
        self.writer.write(" = ");
        self.emit_downlevel_class_value(data, &name)?;
        self.writer.write(";");
        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    fn emit_downlevel_class_value(
        &mut self,
        data: &ts_ast::ClassDeclarationData,
        name: &str,
    ) -> Result<(), EmitError> {
        let base = self.class_base_expression(data)?;
        self.writer.write("/** @class */ (function (");
        if base.is_some() {
            self.writer.write("_super");
        }
        self.writer.write(") {");
        self.writer.newline();
        self.writer.indent += 1;
        if base.is_some() {
            self.writer.write("__extends(");
            self.writer.write(name);
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
        self.writer.write(name);
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
                ) || matches!(
                    &node.data,
                    NodeData::PropertyDeclaration(property) if self.property_is_auto_accessor(property)
                ));
            self.emit_source_comments_between_with_ownership(
                previous_end,
                node.range.start.get(),
                previous_emitted,
                current_emitted,
            );
            if previous_emitted {
                self.emit_class_empty_elements_between(previous_end, node.range.start.get());
            }
            previous_end = node.range.end.get();
            previous_emitted = current_emitted;
            if self.class_member_is_abstract(&node) {
                // Abstract members have no runtime representation.
            } else {
                match &node.data {
                    NodeData::MethodDeclaration(method)
                        if method.body.is_some() && !self.is_constructor_name(method.name) =>
                    {
                        self.writer.write(name);
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
                        self.emit_function_body(method.body.expect("body checked"))?;
                        self.writer.write(";");
                        self.writer.newline();
                    }
                    NodeData::GetAccessorDeclaration(_) | NodeData::SetAccessorDeclaration(_) => {
                        self.emit_downlevel_accessor(data, name, index)?;
                    }
                    NodeData::PropertyDeclaration(property)
                        if self.property_is_auto_accessor(property) =>
                    {
                        let comment_end = data
                            .members
                            .nodes
                            .get(index + 1)
                            .and_then(|next| {
                                self.arena.get(*next).map(|node| node.range.start.get())
                            })
                            .unwrap_or(data.members.range.end.get());
                        self.emit_downlevel_auto_accessor(
                            data,
                            name,
                            property,
                            node.range.end.get(),
                            comment_end,
                        )?;
                    }
                    _ => {}
                }
            }
        }
        self.emit_source_comments_between_with_ownership(
            previous_end,
            data.members.range.end.get(),
            previous_emitted,
            false,
        );
        if previous_emitted {
            self.emit_class_empty_elements_between(previous_end, data.members.range.end.get());
        }
        let captures_static_this = class_has_async_static_field(self.arena, data);
        if captures_static_this {
            self.writer.write("var _a;");
            self.writer.newline();
            self.writer.write("_a = ");
            self.writer.write(name);
            self.writer.write(";");
            self.writer.newline();
        }
        let previous_this_alias = self.this_alias;
        if captures_static_this {
            self.this_alias = Some("_a");
        }
        self.emit_static_fields(data, name)?;
        self.this_alias = previous_this_alias;
        self.writer.write("return ");
        self.writer.write(name);
        self.writer.write(";");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("}(");
        if let Some(base) = base {
            self.emit_expression(base, 0)?;
        }
        self.writer.write("))");
        Ok(())
    }

    fn emit_downlevel_auto_accessor(
        &mut self,
        class: &ts_ast::ClassDeclarationData,
        class_name: &str,
        property: &ts_ast::PropertyDeclarationData,
        comment_start: u32,
        comment_end: u32,
    ) -> Result<(), EmitError> {
        let Some(storage) = self.auto_accessor_storage_name(class, property) else {
            return Ok(());
        };
        self.writer.write("Object.defineProperty(");
        self.writer.write(class_name);
        self.writer.write(".prototype, ");
        self.emit_downlevel_property_name(property.name)?;
        self.writer.write(", {");
        self.writer.newline();
        self.writer.indent += 1;
        self.writer
            .write("get: function () { return __classPrivateFieldGet(this, ");
        self.writer.write(&storage);
        self.writer.write(", \"f\"); }");
        self.emit_source_comments_between_with_trailing(comment_start, comment_end, true);
        self.writer.write(",");
        self.writer.newline();
        self.writer
            .write("set: function (value) { __classPrivateFieldSet(this, ");
        self.writer.write(&storage);
        self.writer.write(", value, \"f\"); },");
        self.writer.newline();
        self.writer.write("enumerable: false,");
        self.writer.newline();
        self.writer.write("configurable: true");
        self.writer.newline();
        self.writer.indent -= 1;
        self.writer.write("});");
        self.writer.newline();
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
        let mut emitted = false;
        for parameter in &parameters.nodes {
            let node = self.node(*parameter)?.clone();
            let NodeData::ParameterDeclaration(parameter) = &node.data else {
                return Err(Self::unsupported(*parameter, node.kind));
            };
            if parameter.dot_dot_dot_token.is_some() {
                continue;
            }
            if emitted {
                self.writer.write(", ");
            }
            self.emit_expression(parameter.name, 0)?;
            emitted = true;
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
        let has_rest = parameters.nodes.iter().any(|parameter| {
            matches!(
                self.arena.get(*parameter).map(|node| &node.data),
                Some(NodeData::ParameterDeclaration(parameter)) if parameter.dot_dot_dot_token.is_some()
            )
        });
        if !has_defaults && !has_rest {
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
        for parameter in &parameters.nodes {
            let node = self.node(*parameter)?.clone();
            let NodeData::ParameterDeclaration(parameter) = &node.data else {
                return Err(Self::unsupported(*parameter, node.kind));
            };
            if parameter.dot_dot_dot_token.is_none() {
                continue;
            }
            self.writer.write("var ");
            self.emit_expression(parameter.name, 0)?;
            self.writer.write(" = [];");
            self.writer.newline();
            self.writer
                .write("for (var _i = 0; _i < arguments.length; _i++) {");
            self.writer.newline();
            self.writer.indent += 1;
            self.emit_expression(parameter.name, 0)?;
            self.writer.write("[_i] = arguments[_i];");
            self.writer.newline();
            self.writer.indent -= 1;
            self.writer.write("}");
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
                        if (property.initializer.is_some() || self.property_is_auto_accessor(property))
                            && !self.has_modifier(property.modifiers.as_ref(), SyntaxKind::StaticKeyword)
                )
        })
    }

    fn emit_instance_fields(
        &mut self,
        data: &ts_ast::ClassDeclarationData,
        receiver: &str,
    ) -> Result<(), EmitError> {
        for (index, member) in data.members.nodes.iter().enumerate() {
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
            if self.property_is_auto_accessor(property) {
                let Some(storage) = self.auto_accessor_storage_name(data, property) else {
                    continue;
                };
                self.writer.write(&storage);
                self.writer.write(".set(");
                self.writer.write(receiver);
                self.writer.write(", ");
                if let Some(initializer) = property.initializer {
                    self.emit_expression(initializer, 1)?;
                } else {
                    self.writer.write("void 0");
                }
                self.writer.write(");");
                self.writer.newline();
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
            let comment_end = data
                .members
                .nodes
                .get(index + 1)
                .and_then(|next| self.arena.get(*next).map(|node| node.range.start.get()))
                .unwrap_or(data.members.range.end.get());
            let comment_count = self.emitted_source_comments.len();
            self.emit_source_comments_between_with_ownership(
                node.range.end.get(),
                comment_end,
                true,
                false,
            );
            if self.emitted_source_comments.len() == comment_count {
                self.writer.newline();
            }
        }
        Ok(())
    }

    fn property_is_auto_accessor(&self, property: &ts_ast::PropertyDeclarationData) -> bool {
        self.has_modifier(property.modifiers.as_ref(), SyntaxKind::AccessorKeyword)
    }

    fn auto_accessor_storage_name(
        &self,
        class: &ts_ast::ClassDeclarationData,
        property: &ts_ast::PropertyDeclarationData,
    ) -> Option<String> {
        let class_name = class
            .name
            .and_then(|name| declaration_name_text(self.arena, name))?;
        let property_name = declaration_name_text(self.arena, property.name)?;
        Some(format!("_{class_name}_{property_name}_accessor_storage"))
    }

    fn emit_auto_accessor_storage_initializers(&mut self, class: &ts_ast::ClassDeclarationData) {
        for member in &class.members.nodes {
            let Some(NodeData::PropertyDeclaration(property)) =
                self.arena.get(*member).map(|node| &node.data)
            else {
                continue;
            };
            if !self.property_is_auto_accessor(property)
                || self.has_modifier(property.modifiers.as_ref(), SyntaxKind::StaticKeyword)
            {
                continue;
            }
            let Some(storage) = self.auto_accessor_storage_name(class, property) else {
                continue;
            };
            self.writer.newline();
            self.writer.write(&storage);
            self.writer.write(" = new WeakMap();");
        }
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
        let saved_identifier_rewrites = self.identifier_rewrites.clone();
        collect_namespace_alias_rewrites(
            self.arena,
            self.bindings,
            data,
            &name,
            &mut self.identifier_rewrites,
        );
        let exported = self.has_modifier(data.modifiers.as_ref(), SyntaxKind::ExportKeyword);
        let parent_container = self.namespace_containers.last().cloned();
        let first_declaration = self
            .namespace_declarations
            .last_mut()
            .expect("every namespace has a lexical declaration scope")
            .insert(name.clone());

        if first_declaration && self.namespace_needs_local_declaration(data.name, &name) {
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
                        let current_emitted =
                            self.statement_emits_runtime(*statement, &statement_node);
                        self.emit_source_comments_between_with_trailing(
                            previous_end,
                            statement_node.range.start.get(),
                            previous_emitted,
                        );
                        self.emit_statement(*statement)?;
                        previous_end = statement_node.range.end.get();
                        previous_emitted = current_emitted;
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
        self.identifier_rewrites = saved_identifier_rewrites;
        Ok(())
    }

    #[allow(clippy::too_many_lines)]
    fn emit_enum(&mut self, data: &ts_ast::EnumDeclarationData) -> Result<(), EmitError> {
        let name = self.identifier_text(data.name)?.to_owned();
        let first_declaration = self
            .namespace_declarations
            .last_mut()
            .expect("every enum has a lexical declaration scope")
            .insert(name.clone());
        if first_declaration && !self.namespace_has_prior_merged_value_declaration(data.name) {
            let block_scoped = self.settings.target >= ScriptTarget::Es2015
                && self
                    .arena
                    .get(data.name)
                    .and_then(|name| name.parent)
                    .and_then(|declaration| self.arena.get(declaration))
                    .and_then(|declaration| declaration.parent)
                    .and_then(|parent| self.arena.get(parent))
                    .is_some_and(|parent| matches!(parent.data, NodeData::Block(_)));
            self.writer
                .write(if block_scoped { "let " } else { "var " });
            self.writer.write(&name);
            self.writer.write(";");
            self.writer.newline();
        }
        self.writer.write("(function (");
        self.writer.write(&name);
        self.writer.write(") {");
        self.writer.newline();
        self.writer.indent += 1;
        let mut next_number = 0_i64;
        for (index, member) in data.members.nodes.iter().enumerate() {
            let member_id = *member;
            let node = self.node(*member)?.clone();
            let NodeData::EnumMember(member) = &node.data else {
                return Err(Self::unsupported(*member, node.kind));
            };
            let (member_name, numeric_name) = self.enum_member_name_text(member.name)?;
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
                if numeric_name {
                    self.writer.write(&member_name);
                } else {
                    write_quoted(&mut self.writer, &member_name);
                }
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
                if numeric_name {
                    self.writer.write(&member_name);
                } else {
                    write_quoted(&mut self.writer, &member_name);
                }
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
                if numeric_name {
                    self.writer.write(&member_name);
                } else {
                    write_quoted(&mut self.writer, &member_name);
                }
            }
            self.writer.write(";");
            self.writer.newline();
            let comment_end = data
                .members
                .nodes
                .get(index + 1)
                .and_then(|next| self.arena.get(*next))
                .map_or_else(
                    || {
                        self.arena
                            .get(data.name)
                            .and_then(|name| name.parent)
                            .and_then(|declaration| self.arena.get(declaration))
                            .map_or(node.range.end, |declaration| declaration.range.end)
                    },
                    |next| next.range.start,
                );
            self.emit_source_comments_between_with_trailing(
                node.range.end.get(),
                comment_end.get(),
                true,
            );
        }
        self.writer.indent -= 1;
        self.writer.write("})(");
        self.writer.write(&name);
        self.writer.write(" || (");
        if self.commonjs_module_transform
            && self.namespace_containers.is_empty()
            && self.has_modifier(data.modifiers.as_ref(), SyntaxKind::ExportKeyword)
        {
            self.writer.write("exports.");
            self.writer.write(&name);
            self.writer.write(" = ");
        }
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
        self.writer.write(if self.is_external_import_equals(data) {
            self.variable_keyword()
        } else {
            "var"
        });
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
        let named_temp = self.commonjs_named_import_temps.get(&clause_id).cloned();
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
        if let Some(temp) = named_temp {
            self.writer.write(self.variable_keyword());
            self.writer.write(" ");
            self.writer.write(&temp);
            self.writer.write(" = require(");
            if let Some(module) = string_literal_text(self.arena, data.module_specifier) {
                write_quoted(&mut self.writer, module);
            } else {
                self.emit_expression(data.module_specifier, 0)?;
            }
            self.writer.write(");");
            return Ok(());
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
            self.writer.write("__exportStar(require(");
            if let Some(module) = data.module_specifier {
                self.emit_expression(module, 0)?;
            } else {
                write_quoted(&mut self.writer, "");
            }
            self.writer.write("), exports);");
            return Ok(());
        };
        let node = self.node(clause)?.clone();
        let NodeData::NamedExports(exports) = &node.data else {
            return Err(Self::unsupported(clause, node.kind));
        };
        let mut emitted = false;
        for specifier_id in &exports.elements.nodes {
            if data.module_specifier.is_none()
                && (self
                    .commonjs_export_import_declaration(*specifier_id)
                    .is_some()
                    || self
                        .commonjs_export_function_declaration(*specifier_id)
                        .is_some())
            {
                continue;
            }
            if emitted {
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
            emitted = true;
        }
        Ok(())
    }

    fn emit_commonjs_import_binding_exports(
        &mut self,
        import_declaration: NodeId,
        statements: &NodeList,
    ) -> Result<(), EmitError> {
        for statement in &statements.nodes {
            let Some(NodeData::ExportDeclaration(export)) =
                self.arena.get(*statement).map(|node| &node.data)
            else {
                continue;
            };
            if export.is_type_only || export.module_specifier.is_some() {
                continue;
            }
            let Some(NodeData::NamedExports(exports)) = export
                .export_clause
                .and_then(|clause| self.arena.get(clause))
                .map(|node| &node.data)
            else {
                continue;
            };
            for specifier_id in &exports.elements.nodes {
                if self.commonjs_export_import_declaration(*specifier_id)
                    != Some(import_declaration)
                {
                    continue;
                }
                let node = self.node(*specifier_id)?.clone();
                let NodeData::ExportSpecifier(specifier) = &node.data else {
                    return Err(Self::unsupported(*specifier_id, node.kind));
                };
                self.writer.write("exports.");
                if let Some(name) = declaration_name_text(self.arena, specifier.name) {
                    self.writer.write(name);
                } else {
                    self.emit_expression(specifier.name, 0)?;
                }
                self.writer.write(" = ");
                self.emit_expression(specifier.property_name.unwrap_or(specifier.name), 0)?;
                self.writer.write(";");
                self.writer.newline();
            }
        }
        Ok(())
    }

    fn commonjs_export_is_fully_hoisted(&self, export: &ts_ast::ExportDeclarationData) -> bool {
        if export.is_type_only || export.module_specifier.is_some() {
            return false;
        }
        let Some(NodeData::NamedExports(exports)) = export
            .export_clause
            .and_then(|clause| self.arena.get(clause))
            .map(|node| &node.data)
        else {
            return false;
        };
        !exports.elements.nodes.is_empty()
            && exports.elements.nodes.iter().all(|specifier| {
                self.commonjs_export_import_declaration(*specifier)
                    .is_some()
                    || self
                        .commonjs_export_function_declaration(*specifier)
                        .is_some()
            })
    }

    fn emit_commonjs_hoisted_function_exports(
        &mut self,
        statements: &NodeList,
    ) -> Result<(), EmitError> {
        for statement in &statements.nodes {
            let Some(NodeData::ExportDeclaration(export)) =
                self.arena.get(*statement).map(|node| &node.data)
            else {
                continue;
            };
            if export.is_type_only || export.module_specifier.is_some() {
                continue;
            }
            let Some(NodeData::NamedExports(exports)) = export
                .export_clause
                .and_then(|clause| self.arena.get(clause))
                .map(|node| &node.data)
            else {
                continue;
            };
            for specifier_id in &exports.elements.nodes {
                if self
                    .commonjs_export_function_declaration(*specifier_id)
                    .is_none()
                {
                    continue;
                }
                let node = self.node(*specifier_id)?.clone();
                let NodeData::ExportSpecifier(specifier) = &node.data else {
                    continue;
                };
                self.writer.write("exports.");
                self.emit_expression(specifier.name, 0)?;
                self.writer.write(" = ");
                self.emit_expression(specifier.property_name.unwrap_or(specifier.name), 0)?;
                self.writer.write(";");
                self.writer.newline();
            }
        }
        Ok(())
    }

    fn commonjs_export_function_declaration(&self, specifier: NodeId) -> Option<NodeId> {
        let NodeData::ExportSpecifier(specifier) = &self.arena.get(specifier)?.data else {
            return None;
        };
        if specifier.is_type_only {
            return None;
        }
        let local = specifier.property_name.unwrap_or(specifier.name);
        let name = declaration_name_text(self.arena, local)?;
        self.arena.iter().find_map(|(declaration, node)| {
            let NodeData::FunctionDeclaration(function) = &node.data else {
                return None;
            };
            (function.body.is_some()
                && function
                    .name
                    .and_then(|name| declaration_name_text(self.arena, name))
                    == Some(name)
                && node.parent.is_some_and(|parent| {
                    matches!(
                        self.arena.get(parent).map(|parent| &parent.data),
                        Some(NodeData::SourceFile(_))
                    )
                }))
            .then_some(declaration)
        })
    }

    fn commonjs_export_import_declaration(&self, specifier: NodeId) -> Option<NodeId> {
        let NodeData::ExportSpecifier(specifier) = &self.arena.get(specifier)?.data else {
            return None;
        };
        if specifier.is_type_only {
            return None;
        }
        let local = specifier.property_name.unwrap_or(specifier.name);
        let name = declaration_name_text(self.arena, local)?;
        let symbol = self.bindings.resolve_name_at(local, name)?;
        self.bindings
            .symbols
            .get(symbol)?
            .declarations
            .iter()
            .find_map(|declaration| {
                if !matches!(
                    self.arena.get(*declaration).map(|node| &node.data),
                    Some(
                        NodeData::ImportClause(_)
                            | NodeData::ImportSpecifier(_)
                            | NodeData::NamespaceImport(_)
                    )
                ) || !self.import_binding_has_runtime_value(*declaration)
                {
                    return None;
                }
                let mut current = *declaration;
                loop {
                    let node = self.arena.get(current)?;
                    if matches!(node.data, NodeData::ImportDeclaration(_)) {
                        return Some(current);
                    }
                    current = node.parent?;
                }
            })
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
        if self.commonjs_module_transform
            || self.system_export_function.is_some()
            || !self.namespace_containers.is_empty()
        {
            return;
        }
        if self.has_modifier(modifiers, SyntaxKind::ExportKeyword) {
            self.writer.write("export ");
        }
        if self.has_modifier(modifiers, SyntaxKind::DefaultKeyword) {
            self.writer.write("default ");
        }
    }

    fn emit_system_predeclared_variable_assignment(
        &mut self,
        statement: &ts_ast::VariableStatementData,
    ) -> Result<bool, EmitError> {
        if self.system_export_function.is_none() {
            return Ok(false);
        }
        let list_node = self.node(statement.declaration_list)?.clone();
        let NodeData::VariableDeclarationList(list) = &list_node.data else {
            return Ok(false);
        };
        if list_node.flags.0 & 3 != 0 {
            return Ok(false);
        }
        let declarations = list
            .declarations
            .nodes
            .iter()
            .filter_map(|declaration_id| {
                let NodeData::VariableDeclaration(declaration) =
                    &self.arena.get(*declaration_id)?.data
                else {
                    return None;
                };
                let name = declaration_name_text(self.arena, declaration.name)?;
                self.system_predeclared_names
                    .contains(name)
                    .then_some((declaration.name, declaration.initializer))
            })
            .collect::<Vec<_>>();
        if declarations.len() != list.declarations.nodes.len() {
            return Ok(false);
        }
        let mut emitted = false;
        for (name, initializer) in declarations {
            let Some(initializer) = initializer else {
                continue;
            };
            if emitted {
                self.writer.write(", ");
            }
            self.emit_expression(name, 1)?;
            self.writer.write(" = ");
            self.emit_expression(initializer, 1)?;
            emitted = true;
        }
        if emitted {
            self.writer.write(";");
        }
        Ok(true)
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

    fn emit_commonjs_export_variable_initializer(
        &mut self,
        statement: &ts_ast::VariableStatementData,
    ) -> Result<bool, EmitError> {
        if !self.commonjs_module_transform
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
        let symbol = self.bindings.node_symbols.get(&declaration.name).copied();
        if !self.commonjs_export_initializer_can_be_direct(initializer) {
            return Ok(false);
        }
        if let Some(symbol) = symbol {
            self.identifier_rewrites
                .insert(symbol, format!("exports.{name}"));
        }
        self.writer.write("exports.");
        self.writer.write(name);
        self.writer.write(" = ");
        self.emit_expression(initializer, 1)?;
        self.writer.write(";");
        Ok(true)
    }

    fn emit_namespace_export_variable_initializers(
        &mut self,
        statement: &ts_ast::VariableStatementData,
    ) -> Result<bool, EmitError> {
        let Some(container) = self.namespace_containers.last().cloned() else {
            return Ok(false);
        };
        if !self.has_modifier(statement.modifiers.as_ref(), SyntaxKind::ExportKeyword) {
            return Ok(false);
        }
        let list_node = self.node(statement.declaration_list)?.clone();
        let NodeData::VariableDeclarationList(list) = &list_node.data else {
            return Ok(false);
        };
        let mut declarations = Vec::with_capacity(list.declarations.nodes.len());
        for declaration_id in &list.declarations.nodes {
            let declaration_node = self.node(*declaration_id)?.clone();
            let NodeData::VariableDeclaration(declaration) = &declaration_node.data else {
                return Ok(false);
            };
            let Some(name) = declaration_name_text(self.arena, declaration.name) else {
                return Ok(false);
            };
            declarations.push((name.to_owned(), declaration.name, declaration.initializer));
        }
        let mut emitted = false;
        for (name, name_id, initializer) in declarations {
            if let Some(symbol) = self.bindings.node_symbols.get(&name_id).copied() {
                self.identifier_rewrites
                    .insert(symbol, format!("{container}.{name}"));
            }
            let Some(initializer) = initializer else {
                continue;
            };
            if emitted {
                self.writer.newline();
            }
            self.writer.write(&container);
            self.writer.write(".");
            self.writer.write(&name);
            self.writer.write(" = ");
            self.emit_expression(initializer, 1)?;
            self.writer.write(";");
            emitted = true;
        }
        Ok(true)
    }

    fn commonjs_export_initializer_can_be_direct(&self, initializer: NodeId) -> bool {
        self.expression_uses_commonjs_default_import(initializer)
            || matches!(
                self.arena.get(initializer).map(|node| &node.data),
                Some(
                    NodeData::Identifier(_)
                        | NodeData::CallExpression(_)
                        | NodeData::ObjectLiteralExpression(_)
                        | NodeData::NumericLiteral(_)
                        | NodeData::BigIntLiteral(_)
                        | NodeData::StringLiteral(_)
                        | NodeData::NoSubstitutionTemplateLiteral(_)
                        | NodeData::KeywordExpression(_)
                )
            )
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

    fn commonjs_call_requires_unbound_receiver(&self, expression: NodeId) -> bool {
        let Some(NodeData::Identifier(identifier)) =
            self.arena.get(expression).map(|node| &node.data)
        else {
            return false;
        };
        let Some(symbol) = self.bindings.resolve_name_at(expression, &identifier.text) else {
            return false;
        };
        self.identifier_rewrites.contains_key(&symbol)
            && self.bindings.symbols.get(symbol).is_some_and(|symbol| {
                symbol.declarations.iter().any(|declaration| {
                    matches!(
                        self.arena.get(*declaration).map(|node| &node.data),
                        Some(NodeData::ImportSpecifier(specifier))
                            if !specifier.is_type_only
                                && !self.commonjs_import_specifier_is_default(*declaration)
                    )
                })
            })
    }

    fn is_dynamic_import_call(&self, call: &ts_ast::CallExpressionData) -> bool {
        matches!(
            self.arena.get(call.expression).map(|node| &node.data),
            Some(NodeData::Identifier(identifier)) if identifier.text == "import"
        )
    }

    fn emit_commonjs_dynamic_import(
        &mut self,
        call: &ts_ast::CallExpressionData,
    ) -> Result<(), EmitError> {
        let argument = call.arguments.nodes.first().copied();
        let inlineable = argument.is_none_or(|argument| {
            matches!(
                self.arena.get(argument).map(|node| &node.data),
                Some(NodeData::StringLiteral(_) | NodeData::NoSubstitutionTemplateLiteral(_))
            )
        });
        self.writer.write("Promise.resolve(");
        if !inlineable {
            self.writer.write("`${");
            self.emit_expression(argument.expect("non-inlineable import has an argument"), 0)?;
            self.writer.write("}`");
        }
        self.writer.write(").then(");
        if inlineable {
            self.writer.write("() => __importStar(require(");
            if let Some(argument) = argument {
                self.emit_expression(argument, 0)?;
            }
        } else {
            self.writer.write("s => __importStar(require(s");
        }
        self.writer.write(")))");
        Ok(())
    }

    fn emit_shorthand_property(&mut self, name: NodeId) -> Result<(), EmitError> {
        let rewrite = self
            .identifier_text(name)
            .ok()
            .and_then(|text| self.bindings.resolve_name_at(name, text))
            .and_then(|symbol| self.identifier_rewrites.get(&symbol))
            .cloned();
        if let Some(rewrite) = rewrite {
            let name = self.identifier_text(name)?.to_owned();
            self.writer.write(&name);
            self.writer.write(": ");
            self.writer.write(&rewrite);
        } else {
            self.emit_expression(name, 0)?;
        }
        Ok(())
    }

    fn import_binding_is_used(&self, name: NodeId) -> bool {
        self.identifier_text(name)
            .is_ok_and(|name| self.runtime_identifier_uses.contains(name))
    }

    fn system_exported_name(&self, expression: NodeId) -> Option<String> {
        let NodeData::Identifier(identifier) = &self.arena.get(expression)?.data else {
            return None;
        };
        let symbol = self
            .bindings
            .resolve_name_at(expression, &identifier.text)?;
        self.system_exported_bindings.get(&symbol).cloned()
    }

    fn emit_system_export_call_start(&mut self, name: &str) {
        let Some(export_function) = self.system_export_function.as_deref() else {
            return;
        };
        self.writer.write(export_function);
        self.writer.write("(");
        write_quoted(&mut self.writer, name);
        self.writer.write(", ");
    }

    fn import_semantically_has_runtime_value(&self, declaration: NodeId) -> bool {
        self.import_runtime_meanings
            .get(&declaration)
            .copied()
            .unwrap_or(true)
    }

    fn import_has_runtime_use(
        &self,
        _declaration: NodeId,
        import: &ts_ast::ImportDeclarationData,
    ) -> bool {
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
            NodeData::BigIntLiteral(data) => self.writer.write(&data.text.to_ascii_lowercase()),
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
                if !object && data.elements.has_trailing_comma {
                    self.writer.write(",");
                }
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
            NodeData::OmittedExpression(_) => {}
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
            NodeData::BinaryExpression(_) => {
                self.emit_binary_expression(id, parent_precedence)?;
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
                    let name = self.node(data.name)?.clone();
                    match &name.data {
                        NodeData::Identifier(name) => self.writer.write(&name.text),
                        NodeData::PrivateIdentifier(name) => self.writer.write(&name.text),
                        _ => self.emit_expression(data.name, 18)?,
                    }
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
                if self.commonjs_module_transform && self.is_dynamic_import_call(data) {
                    self.emit_commonjs_dynamic_import(data)?;
                } else if data.question_dot_token.is_some()
                    && self.settings.target < ScriptTarget::Es2020
                {
                    self.emit_downlevel_optional_call(
                        data.expression,
                        &data.arguments,
                        parent_precedence,
                    )?;
                } else {
                    let unbound_receiver = self.commonjs_module_transform
                        && self.commonjs_call_requires_unbound_receiver(data.expression);
                    if unbound_receiver {
                        self.writer.write("(0, ");
                    }
                    self.emit_expression(data.expression, 18)?;
                    if unbound_receiver {
                        self.writer.write(")");
                    }
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
                self.emit_array_literal(id, data)?;
            }
            NodeData::SpreadElement(data) => {
                self.writer.write("...");
                self.emit_expression(data.expression, 1)?;
            }
            NodeData::AwaitExpression(data) => {
                if self.async_expression_transform == AsyncExpressionTransform::AsyncGenerator {
                    self.writer.write("yield __await(");
                    self.emit_expression(data.expression, 0)?;
                    self.writer.write(")");
                } else if self.async_expression_transform == AsyncExpressionTransform::AwaitAsYield
                    || self.settings.target < ScriptTarget::Es2017
                {
                    self.writer.write("yield ");
                    self.emit_expression(data.expression, 2)?;
                } else {
                    self.writer.write("await");
                    let comment_count = self.emitted_source_comments.len();
                    self.emit_inline_block_comments_between(
                        node.range.start.get().saturating_add(5),
                        self.node(data.expression)?.range.start.get(),
                        true,
                    );
                    if self.emitted_source_comments.len() == comment_count {
                        let keyword_end = usize::try_from(node.range.start.get().saturating_add(5))
                            .unwrap_or(usize::MAX);
                        let expression_start =
                            usize::try_from(self.node(data.expression)?.range.start.get())
                                .unwrap_or(usize::MAX);
                        if self
                            .source_text
                            .get(keyword_end..expression_start)
                            .is_none_or(|trivia| !trivia.is_empty())
                        {
                            self.writer.write(" ");
                        }
                    }
                    self.emit_expression(data.expression, 2)?;
                }
            }
            NodeData::TypeOfExpression(data) => {
                self.writer.write("typeof ");
                self.emit_expression(data.expression, 16)?;
            }
            NodeData::YieldExpression(data) => {
                if self.async_expression_transform == AsyncExpressionTransform::AsyncGenerator
                    && data.asterisk_token.is_none()
                {
                    self.writer.write("yield yield __await(");
                    if let Some(expression) = data.expression {
                        self.emit_expression(expression, 0)?;
                    } else {
                        self.writer.write("void 0");
                    }
                    self.writer.write(")");
                } else {
                    self.writer.write("yield");
                    if data.asterisk_token.is_some() {
                        self.writer.write("*");
                    }
                    if let Some(expression) = data.expression {
                        self.writer.write(" ");
                        self.emit_expression(expression, 2)?;
                    }
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
                let system_export = matches!(
                    data.operator,
                    SyntaxKind::PlusPlusToken | SyntaxKind::MinusMinusToken
                )
                .then(|| self.system_exported_name(data.operand))
                .flatten();
                if let Some(name) = &system_export {
                    self.emit_system_export_call_start(name);
                }
                self.writer.write(
                    operator_text(data.operator).ok_or_else(|| Self::unsupported(id, node.kind))?,
                );
                if matches!(
                    data.operator,
                    SyntaxKind::PlusToken | SyntaxKind::MinusToken
                ) && self.node(data.operand).is_ok_and(|operand| {
                    matches!(
                        &operand.data,
                        NodeData::PrefixUnaryExpression(operand)
                            if matches!(
                                (data.operator, operand.operator),
                                (
                                    SyntaxKind::PlusToken,
                                    SyntaxKind::PlusToken | SyntaxKind::PlusPlusToken
                                ) | (
                                    SyntaxKind::MinusToken,
                                    SyntaxKind::MinusToken | SyntaxKind::MinusMinusToken
                                )
                            )
                    )
                }) {
                    self.writer.write(" ");
                }
                self.emit_expression(data.operand, 16)?;
                if system_export.is_some() {
                    self.writer.write(")");
                }
            }
            NodeData::PostfixUnaryExpression(data) => {
                let system_export = matches!(
                    data.operator,
                    SyntaxKind::PlusPlusToken | SyntaxKind::MinusMinusToken
                )
                .then(|| self.system_exported_name(data.operand))
                .flatten();
                if let Some(name) = &system_export {
                    self.emit_system_export_call_start(name);
                    self.writer.write("(");
                }
                self.emit_expression(data.operand, 17)?;
                self.writer.write(
                    operator_text(data.operator).ok_or_else(|| Self::unsupported(id, node.kind))?,
                );
                if system_export.is_some() {
                    self.writer.write(", ");
                    self.emit_expression(data.operand, 0)?;
                    self.writer.write("))");
                }
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
                let mut previous_end = node.range.start.get().saturating_add(1);
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
                    if multiline {
                        self.emit_source_comments_between_with_trailing(
                            previous_end,
                            node.range.start.get(),
                            index != 0,
                        );
                    }
                    match &node.data {
                        NodeData::PropertyAssignment(property) => {
                            self.emit_expression(property.name, 0)?;
                            self.writer.write(": ");
                            self.emit_expression(property.initializer, 1)?;
                        }
                        NodeData::ShorthandPropertyAssignment(property) => {
                            self.emit_shorthand_property(property.name)?;
                        }
                        NodeData::SpreadAssignment(property) => {
                            self.writer.write("...");
                            self.emit_expression(property.expression, 1)?;
                        }
                        NodeData::MethodDeclaration(method) if method.body.is_some() => {
                            let downlevel_async = method.asterisk_token.is_none()
                                && self.has_modifier(
                                    method.modifiers.as_ref(),
                                    SyntaxKind::AsyncKeyword,
                                )
                                && (ScriptTarget::Es2015..ScriptTarget::Es2017)
                                    .contains(&self.settings.target);
                            if !downlevel_async
                                && self.has_modifier(
                                    method.modifiers.as_ref(),
                                    SyntaxKind::AsyncKeyword,
                                )
                            {
                                self.writer.write("async ");
                            }
                            if method.asterisk_token.is_some() {
                                self.writer.write("*");
                            }
                            self.emit_expression(method.name, 0)?;
                            self.emit_parameters(&method.parameters)?;
                            self.writer.write(" ");
                            if downlevel_async {
                                self.emit_downlevel_async_function_body(
                                    method.body.expect("body checked above"),
                                    "this",
                                )?;
                            } else {
                                self.emit_function_body(method.body.expect("body checked above"))?;
                            }
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
                    previous_end = node.range.end.get();
                }
                if multiline {
                    self.emit_source_comments_between_with_trailing(
                        previous_end,
                        self.node(id)?.range.end.get().saturating_sub(1),
                        true,
                    );
                    if !self.writer.line_start {
                        self.writer.newline();
                    }
                    self.writer.indent -= 1;
                    self.writer.write("}");
                } else {
                    self.writer.write(" }");
                }
            }
            NodeData::ArrowFunction(data) => {
                let is_async = self.has_modifier(data.modifiers.as_ref(), SyntaxKind::AsyncKeyword);
                let downlevel_async = is_async && self.settings.target < ScriptTarget::Es2017;
                if self.settings.target < ScriptTarget::Es2015 && !is_async {
                    let wrap = parent_precedence > 2;
                    if wrap {
                        self.writer.write("(");
                    }
                    self.writer.write("function ");
                    self.emit_parameters(&data.parameters)?;
                    self.writer.write(" ");
                    if matches!(&self.node(data.body)?.data, NodeData::Block(_)) {
                        self.emit_function_body(data.body)?;
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
                let wrap =
                    parent_precedence > 2
                        || (downlevel_async
                            && self.settings.target < ScriptTarget::Es2015
                            && self.arena.get(id).and_then(|node| node.parent).is_some_and(
                                |parent| {
                                    matches!(
                                        self.arena.get(parent).map(|node| &node.data),
                                        Some(NodeData::ExpressionStatement(_))
                                    )
                                },
                            ));
                if wrap {
                    self.writer.write("(");
                }
                if is_async && !downlevel_async {
                    self.writer.write("async ");
                }
                let object_rest_parameter = downlevel_async
                    .then(|| self.async_arrow_object_rest_parameter(data))
                    .flatten();
                if self.settings.target < ScriptTarget::Es2015 && downlevel_async {
                    self.writer.write("function ");
                }
                if object_rest_parameter.is_some() {
                    self.writer.write("(_a)");
                } else if !downlevel_async && self.arrow_uses_bare_parameter(id, data) {
                    let parameter_id = data.parameters.nodes[0];
                    let parameter_node = self.node(parameter_id)?.clone();
                    let NodeData::ParameterDeclaration(parameter) = &parameter_node.data else {
                        return Err(Self::unsupported(parameter_id, parameter_node.kind));
                    };
                    self.emit_expression(parameter.name, 0)?;
                } else {
                    self.emit_parameters(&data.parameters)?;
                }
                if self.settings.target < ScriptTarget::Es2015 && downlevel_async {
                    self.writer.write(" ");
                } else {
                    self.writer.write(" => ");
                }
                if downlevel_async {
                    let this_argument = if self.settings.target < ScriptTarget::Es2015
                        && self.this_alias == Some("_a")
                    {
                        // A lowered static field uses `_a` as the class-value capture for
                        // the generator callback. It is not the receiver of the async arrow.
                        "void 0"
                    } else if let Some(alias) = self.this_alias {
                        alias
                    } else if self.arrow_is_nested_in_function(id) {
                        "this"
                    } else {
                        "void 0"
                    };
                    if self.settings.target < ScriptTarget::Es2015 {
                        let expression_body =
                            (!matches!(&self.node(data.body)?.data, NodeData::Block(_)))
                                .then_some(data.body);
                        let object_rest = object_rest_parameter.map(|pattern| {
                            let temp = expression_body.map(|_| "_b");
                            (pattern, "_a", temp)
                        });
                        let state = if object_rest.is_some() || self.this_alias == Some("_a") {
                            if object_rest.is_some() { "_c" } else { "_b" }
                        } else {
                            "_a"
                        };
                        let generator_this = if self.this_alias == Some("_a") {
                            "_a"
                        } else {
                            "this"
                        };
                        self.emit_es5_async_function_body(
                            data.body,
                            expression_body,
                            this_argument,
                            generator_this,
                            state,
                            object_rest,
                            true,
                        )?;
                    } else if let Some(pattern) = object_rest_parameter {
                        self.emit_awaiter_call_with_object_rest_parameter(
                            data.body,
                            pattern,
                            "_a",
                            this_argument,
                        )?;
                    } else {
                        let expression_body =
                            (!matches!(&self.node(data.body)?.data, NodeData::Block(_)))
                                .then_some(data.body);
                        self.emit_awaiter_call(data.body, expression_body, this_argument)?;
                    }
                } else if matches!(&self.node(data.body)?.data, NodeData::Block(_)) {
                    self.emit_function_body(data.body)?;
                } else {
                    self.emit_expression(data.body, 1)?;
                }
                if wrap {
                    self.writer.write(")");
                }
            }
            NodeData::FunctionExpression(data) => {
                let wrap = parent_precedence >= 18;
                if wrap {
                    self.writer.write("(");
                }
                let is_async = self.has_modifier(data.modifiers.as_ref(), SyntaxKind::AsyncKeyword);
                let downlevel_async_generator = self.settings.target < ScriptTarget::Es2018
                    && data.asterisk_token.is_some()
                    && is_async;
                let downlevel_async = data.asterisk_token.is_none()
                    && is_async
                    && self.settings.target < ScriptTarget::Es2017;
                let downlevel_generator = self.settings.target < ScriptTarget::Es2015
                    && data.asterisk_token.is_some()
                    && !is_async;
                if !downlevel_async && !downlevel_async_generator && is_async {
                    self.writer.write("async ");
                }
                self.writer.write("function");
                if data.asterisk_token.is_some()
                    && !downlevel_async_generator
                    && !downlevel_generator
                {
                    self.writer.write("*");
                }
                let function_name = data
                    .name
                    .and_then(|name| declaration_name_text(self.arena, name))
                    .map(str::to_owned);
                if let Some(name) = data.name {
                    self.writer.write(" ");
                    self.emit_expression(name, 0)?;
                } else {
                    self.writer.write(" ");
                }
                self.emit_parameters(&data.parameters)?;
                self.writer.write(" ");
                if downlevel_async {
                    self.emit_downlevel_async_function_body(data.body, "this")?;
                } else if downlevel_async_generator {
                    let inner_name = self
                        .generated_names
                        .generate(function_name.as_deref().unwrap_or("_default"));
                    if self.settings.target < ScriptTarget::Es2015 {
                        self.emit_es5_downlevel_async_generator_body(data.body, &inner_name)?;
                    } else {
                        self.emit_downlevel_async_generator_body(data.body, &inner_name)?;
                    }
                } else if downlevel_generator {
                    self.emit_es5_generator_body(data.body)?;
                } else if self.source_text.is_empty()
                    && let Some(expression) = self.single_line_return_expression(data.body)?
                {
                    self.writer.write("{ return ");
                    self.emit_expression(expression, 0)?;
                    self.writer.write("; }");
                } else {
                    self.emit_function_body(data.body)?;
                }
                if wrap {
                    self.writer.write(")");
                }
            }
            NodeData::ClassExpression(data) => {
                self.emit_class_expression(id, data, parent_precedence)?;
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
            self.writer.write("/>");
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
        self.writer.write("{ ");
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
        self.writer.write(" }");
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

    #[allow(clippy::too_many_lines)]
    fn emit_binary_expression(
        &mut self,
        expression: NodeId,
        parent_precedence: u8,
    ) -> Result<(), EmitError> {
        enum Action {
            Binary(NodeId, u8),
            Expression(NodeId, u8),
            Write(&'static str),
            SystemExportStart(String),
            BeforeOperator { comma: bool, line_break: bool },
            AfterOperator { line_break: bool },
            Dedent,
        }

        let mut actions = vec![Action::Binary(expression, parent_precedence)];
        while let Some(action) = actions.pop() {
            match action {
                Action::Expression(id, precedence) => {
                    let is_binary = matches!(
                        self.arena.get(id).map(|node| &node.data),
                        Some(NodeData::BinaryExpression(_))
                    );
                    let is_inlined_constant = self.const_enum_emit_mode.inlines_accesses()
                        && (self.enum_access_values.contains_key(&id)
                            || self.enum_access_fallbacks.contains_key(&id));
                    if is_binary && !is_inlined_constant {
                        actions.push(Action::Binary(id, precedence));
                    } else {
                        self.emit_expression(id, precedence)?;
                    }
                }
                Action::Write(text) => self.writer.write(text),
                Action::SystemExportStart(name) => self.emit_system_export_call_start(&name),
                Action::BeforeOperator { comma, line_break } => {
                    if line_break {
                        self.writer.indent += 1;
                        self.writer.newline();
                    } else if !comma {
                        self.writer.write(" ");
                    }
                }
                Action::AfterOperator { line_break } => {
                    if line_break {
                        self.writer.indent += 1;
                        self.writer.newline();
                    } else {
                        self.writer.write(" ");
                    }
                }
                Action::Dedent => self.writer.indent -= 1,
                Action::Binary(id, precedence) => {
                    let node = self.node(id)?.clone();
                    let NodeData::BinaryExpression(binary) = &node.data else {
                        return Err(Self::unsupported(id, node.kind));
                    };
                    let operator = self.node(binary.operator_token)?.kind;

                    if operator == SyntaxKind::QuestionQuestionToken
                        && self.settings.target < ScriptTarget::Es2020
                    {
                        let wrap = precedence > 2;
                        if wrap {
                            actions.push(Action::Write(")"));
                        }
                        actions.push(Action::Expression(binary.right, 2));
                        actions.push(Action::Write(" : "));
                        actions.push(Action::Expression(binary.left, 2));
                        actions.push(Action::Write(" !== void 0 ? "));
                        actions.push(Action::Expression(binary.left, 10));
                        actions.push(Action::Write(" !== null && "));
                        actions.push(Action::Expression(binary.left, 10));
                        if wrap {
                            actions.push(Action::Write("("));
                        }
                        continue;
                    }

                    if self.settings.target < ScriptTarget::Es2016
                        && matches!(
                            operator,
                            SyntaxKind::AsteriskAsteriskToken
                                | SyntaxKind::AsteriskAsteriskEqualsToken
                        )
                    {
                        let compound = operator == SyntaxKind::AsteriskAsteriskEqualsToken;
                        let wrap = compound && precedence > 1;
                        if wrap {
                            actions.push(Action::Write(")"));
                        }
                        actions.push(Action::Write(")"));
                        actions.push(Action::Expression(binary.right, 0));
                        actions.push(Action::Write(", "));
                        actions.push(Action::Expression(binary.left, 0));
                        actions.push(Action::Write("Math.pow("));
                        if compound {
                            actions.push(Action::Write(" = "));
                            actions.push(Action::Expression(binary.left, 2));
                        }
                        if wrap {
                            actions.push(Action::Write("("));
                        }
                        continue;
                    }

                    let (operator_precedence, right_associative) = binary_precedence(operator)
                        .ok_or_else(|| Self::unsupported(binary.operator_token, operator))?;
                    let operator_text = operator_text(operator)
                        .ok_or_else(|| Self::unsupported(binary.operator_token, operator))?;
                    let system_export = operator
                        .is_assignment_operator()
                        .then(|| self.system_exported_name(binary.left))
                        .flatten();
                    let wrap = system_export.is_none() && operator_precedence < precedence;
                    let line_break_before_operator = operator != SyntaxKind::CommaToken
                        && self.source_has_known_line_break_between(
                            binary.left,
                            binary.operator_token,
                        );
                    let line_break_after_operator = self
                        .source_has_known_line_break_between(binary.operator_token, binary.right);

                    if system_export.is_some() {
                        actions.push(Action::Write(")"));
                    }
                    if wrap {
                        actions.push(Action::Write(")"));
                    }
                    if line_break_before_operator {
                        actions.push(Action::Dedent);
                    }
                    if line_break_after_operator {
                        actions.push(Action::Dedent);
                    }
                    actions.push(Action::Expression(
                        binary.right,
                        if right_associative {
                            operator_precedence
                        } else {
                            operator_precedence + 1
                        },
                    ));
                    actions.push(Action::AfterOperator {
                        line_break: line_break_after_operator,
                    });
                    actions.push(Action::Write(operator_text));
                    actions.push(Action::BeforeOperator {
                        comma: operator == SyntaxKind::CommaToken,
                        line_break: line_break_before_operator,
                    });
                    actions.push(Action::Expression(binary.left, operator_precedence));
                    if wrap {
                        actions.push(Action::Write("("));
                    }
                    if let Some(name) = system_export {
                        actions.push(Action::SystemExportStart(name));
                    }
                }
            }
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
        self.writer.write("Object.assign(");
        let mut emitted_argument = false;
        let mut object_open = false;
        let mut properties_in_object = 0_usize;
        for property in &data.properties.nodes {
            let node = self.node(*property)?.clone();
            if let NodeData::SpreadAssignment(spread) = &node.data {
                if object_open {
                    self.writer.write(" }");
                    object_open = false;
                }
                if !emitted_argument {
                    self.writer.write("{}");
                    emitted_argument = true;
                }
                self.writer.write(", ");
                self.emit_expression(spread.expression, 1)?;
                continue;
            }
            if !object_open {
                if emitted_argument {
                    self.writer.write(", ");
                }
                self.writer.write("{ ");
                object_open = true;
                emitted_argument = true;
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
                self.emit_shorthand_property(property.name)?;
            }
            NodeData::MethodDeclaration(method) if method.body.is_some() => {
                let downlevel_async = method.asterisk_token.is_none()
                    && self.has_modifier(method.modifiers.as_ref(), SyntaxKind::AsyncKeyword)
                    && (ScriptTarget::Es2015..ScriptTarget::Es2017).contains(&self.settings.target);
                if !downlevel_async
                    && self.has_modifier(method.modifiers.as_ref(), SyntaxKind::AsyncKeyword)
                {
                    self.writer.write("async ");
                }
                if method.asterisk_token.is_some() {
                    self.writer.write("*");
                }
                self.emit_expression(method.name, 0)?;
                self.emit_parameters(&method.parameters)?;
                self.writer.write(" ");
                if downlevel_async {
                    self.emit_downlevel_async_function_body(
                        method.body.expect("body checked above"),
                        "this",
                    )?;
                } else {
                    self.emit_function_body(method.body.expect("body checked above"))?;
                }
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

    fn emit_array_literal(
        &mut self,
        id: NodeId,
        data: &ts_ast::ArrayLiteralExpressionData,
    ) -> Result<(), EmitError> {
        let multiline = !data.elements.nodes.is_empty() && self.node_source_is_multiline(id);
        self.writer.write("[");
        if !multiline {
            self.emit_expression_list(&data.elements)?;
            self.writer.write("]");
            return Ok(());
        }

        self.writer.indent += 1;
        self.writer.newline();
        let mut previous_end = data.elements.range.start.get();
        for (index, element) in data.elements.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(",");
                self.writer.newline();
            }
            let node = self.node(*element)?.clone();
            self.emit_source_comments_between_with_trailing(
                previous_end,
                node.range.start.get(),
                index != 0,
            );
            self.emit_expression(*element, 1)?;
            previous_end = node.range.end.get();
        }
        if data.elements.has_trailing_comma {
            self.writer.write(",");
        }
        self.emit_source_comments_between_with_trailing(
            previous_end,
            self.node(id)?.range.end.get().saturating_sub(1),
            true,
        );
        if !self.writer.line_start {
            self.writer.newline();
        }
        self.writer.indent -= 1;
        self.writer.write("]");
        Ok(())
    }

    fn emit_expression_list(&mut self, list: &NodeList) -> Result<(), EmitError> {
        let mut previous_end = list.range.start.get();
        for (index, expression) in list.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(",");
            }
            let expression_start = self.node(*expression)?.range.start.get();
            if self.source_range_contains_line_comment(previous_end, expression_start) {
                self.emit_expression_list_line_comments(previous_end, expression_start);
            } else {
                if index != 0 {
                    self.writer.write(" ");
                }
                self.emit_inline_block_comments(previous_end, expression_start);
            }
            self.emit_expression(*expression, 1)?;
            previous_end = self.node(*expression)?.range.end.get();
        }
        if self.source_range_contains_line_comment(previous_end, list.range.end.get()) {
            self.emit_expression_list_line_comments(previous_end, list.range.end.get());
        }
        Ok(())
    }

    fn source_range_contains_line_comment(&self, start: u32, end: u32) -> bool {
        let start = usize::try_from(start).unwrap_or(usize::MAX);
        let end = usize::try_from(end).unwrap_or(usize::MAX);
        let Some(trivia) = self.source_text.get(start..end) else {
            return false;
        };
        let bytes = trivia.as_bytes();
        let mut index = 0;
        while index + 1 < bytes.len() {
            if bytes[index..].starts_with(b"//") {
                return true;
            }
            if bytes[index..].starts_with(b"/*") {
                index = bytes[index + 2..]
                    .windows(2)
                    .position(|window| window == b"*/")
                    .map_or(bytes.len(), |offset| index + 2 + offset + 2);
            } else {
                index += 1;
            }
        }
        false
    }

    fn emit_expression_list_line_comments(&mut self, start: u32, end: u32) {
        if self.settings.remove_comments {
            return;
        }
        let starts_on_new_line = usize::try_from(start)
            .ok()
            .zip(usize::try_from(end).ok())
            .and_then(|(start, end)| self.source_text.get(start..end))
            .and_then(|trivia| trivia.find("//").map(|comment| &trivia[..comment]))
            .is_some_and(|leading| leading.contains(['\n', '\r']));
        if starts_on_new_line && !self.writer.line_start {
            self.writer.newline();
        }
        self.emit_source_comments_between_with_trailing(start, end, true);
    }

    fn emit_inline_block_comments(&mut self, start: u32, end: u32) {
        if self.settings.remove_comments {
            return;
        }
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
        let start = usize::try_from(node.range.start.get()).unwrap_or(usize::MAX);
        let end = usize::try_from(node.range.end.get()).unwrap_or(usize::MAX);
        let source_has_braces = self.source_text.get(start..end).is_some_and(|text| {
            let text = text.trim();
            text.starts_with('{') && text.ends_with('}')
        });
        if source_has_braces && self.node_source_is_multiline(block) {
            return Ok(None);
        }
        let statement_node = self.node(*statement)?;
        if self.statement_contains_class_expression(*statement)? {
            return Ok(None);
        }
        if source_has_braces
            && (self.source_range_contains_comment(
                node.range.start.get().saturating_add(1),
                statement_node.range.start.get(),
            ) || self.source_range_contains_comment(
                statement_node.range.end.get(),
                node.range.end.get().saturating_sub(1),
            ))
        {
            return Ok(None);
        }
        let compact = match &self.node(*statement)?.data {
            NodeData::ExpressionStatement(_)
            | NodeData::ReturnStatement(_)
            | NodeData::ThrowStatement(_) => true,
            NodeData::VariableStatement(_) => !source_has_braces,
            _ => false,
        };
        Ok(compact.then_some(*statement))
    }

    fn source_range_contains_comment(&self, start: u32, end: u32) -> bool {
        let start = usize::try_from(start).unwrap_or(usize::MAX);
        let end = usize::try_from(end).unwrap_or(usize::MAX);
        self.source_text
            .get(start..end)
            .is_some_and(|text| text.contains("//") || text.contains("/*"))
    }

    fn statement_contains_class_expression(&self, statement: NodeId) -> Result<bool, EmitError> {
        let expression = match &self.node(statement)?.data {
            NodeData::ExpressionStatement(data) => Some(data.expression),
            NodeData::ReturnStatement(data) => data.expression,
            NodeData::ThrowStatement(data) => Some(data.expression),
            _ => None,
        };
        Ok(expression
            .is_some_and(|expression| self.expression_contains_class_expression(expression)))
    }

    fn expression_contains_class_expression(&self, expression: NodeId) -> bool {
        match self.arena.get(expression).map(|node| &node.data) {
            Some(NodeData::ClassExpression(_)) => true,
            Some(NodeData::ParenthesizedExpression(data)) => {
                self.expression_contains_class_expression(data.expression)
            }
            Some(NodeData::AsExpression(data)) => {
                self.expression_contains_class_expression(data.expression)
            }
            Some(NodeData::SatisfiesExpression(data)) => {
                self.expression_contains_class_expression(data.expression)
            }
            Some(NodeData::TypeAssertion(data)) => {
                self.expression_contains_class_expression(data.expression)
            }
            Some(NodeData::BinaryExpression(data)) => {
                self.expression_contains_class_expression(data.left)
                    || self.expression_contains_class_expression(data.right)
            }
            Some(NodeData::TypeOfExpression(data)) => {
                self.expression_contains_class_expression(data.expression)
            }
            _ => false,
        }
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

    fn enum_member_name_text(&self, id: NodeId) -> Result<(String, bool), EmitError> {
        let node = self.node(id)?;
        match &node.data {
            NodeData::Identifier(data) => Ok((data.text.clone(), false)),
            NodeData::StringLiteral(data) => Ok((data.text.clone(), false)),
            NodeData::NumericLiteral(data) => Ok((data.text.clone(), true)),
            NodeData::ComputedPropertyName(data) => self.enum_member_name_text(data.expression),
            _ => Err(Self::unsupported(id, node.kind)),
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

fn is_reference_directive(comment: &str) -> bool {
    let Some(directive) = comment.strip_prefix("///") else {
        return false;
    };
    let Some(rest) = directive.trim_start().strip_prefix("<reference") else {
        return false;
    };
    rest.chars()
        .next()
        .is_some_and(|character| character.is_whitespace() || matches!(character, '/' | '>'))
}

fn contains_blank_line(text: &str) -> bool {
    let bytes = text.as_bytes();
    let mut index = 0;
    let mut line_breaks = 0;
    while index < bytes.len() {
        match bytes[index] {
            b'\n' => {
                line_breaks += 1;
                index += 1;
            }
            b'\r' => {
                line_breaks += 1;
                index += 1;
                if bytes.get(index) == Some(&b'\n') {
                    index += 1;
                }
            }
            b' ' | b'\t' => index += 1,
            _ => {
                line_breaks = 0;
                index += 1;
            }
        }
        if line_breaks >= 2 {
            return true;
        }
    }
    false
}

fn is_amd_dependency_directive(comment: &str) -> bool {
    let Some(directive) = comment.strip_prefix("///") else {
        return false;
    };
    let Some(rest) = directive.trim_start().strip_prefix("<amd-dependency") else {
        return false;
    };
    rest.chars()
        .next()
        .is_some_and(|character| character.is_whitespace() || matches!(character, '/' | '>'))
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

    use ts_ast::{NodeData, SyntaxKind};
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
                no_emit_helpers: false,
                remove_comments: false,
                use_define_for_class_fields: None,
            },
        )
        .unwrap()
    }

    fn emit_always_strict(
        source: &str,
        target: ScriptTarget,
        module: ModuleKind,
    ) -> super::EmitResult {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        emit_source_file_with_settings(
            &parsed.arena,
            parsed.source_file,
            "input.ts",
            source,
            PrinterSettings {
                always_strict: true,
                target,
                module,
                jsx: JsxEmit::Preserve,
                emit_javascript: true,
                emit_declarations: false,
                source_map: false,
                inline_source_map: false,
                no_emit_helpers: false,
                remove_comments: false,
                use_define_for_class_fields: None,
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
        let import_meanings = BTreeMap::new();
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
                no_emit_helpers: false,
                remove_comments: false,
                use_define_for_class_fields: None,
            },
            &EmitContext {
                bindings: &bindings,
                amd_module_name: parsed.amd_module_name.as_deref(),
                amd_bundle: false,
                amd_dependencies: &dependencies,
                enum_member_values: &enum_values,
                enum_access_values: &enum_values,
                import_runtime_meanings: &import_meanings,
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
                no_emit_helpers: false,
                remove_comments: false,
                use_define_for_class_fields: None,
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
    fn downlevels_regular_generator_functions_for_es5() {
        let source = "function* declared() { before(); yield 1; return 2; } const value = (function* named() { yield item; })();";
        let es5 = emit_with(source, ScriptTarget::Es5, ModuleKind::EsNext).code;
        assert!(es5.contains("var __generator ="), "{es5}");
        assert!(!es5.contains("var __values ="), "{es5}");
        assert!(
            es5.contains(concat!(
                "function declared() {\n",
                "    return __generator(this, function (_a) {\n",
                "        switch (_a.label) {\n",
                "            case 0:\n",
                "                before();\n",
                "                return [4 /*yield*/, 1];\n",
                "            case 1:\n",
                "                _a.sent();\n",
                "                return [2 /*return*/, 2];\n",
            )),
            "{es5}"
        );
        assert!(
            es5.contains(
                "var value = (function named() {\n    return __generator(this, function (_a) {"
            ),
            "{es5}"
        );

        let es2015 = emit_with(source, ScriptTarget::Es2015, ModuleKind::EsNext).code;
        assert!(es2015.contains("function* declared()"), "{es2015}");
        assert!(es2015.contains("function* named()"), "{es2015}");
        assert!(!es2015.contains("__generator"), "{es2015}");
    }

    #[test]
    fn downlevels_async_generator_functions_for_es5() {
        let source =
            "const value = (async function* named() { await ready; yield item; return done; })();";
        let es5 = emit_with(source, ScriptTarget::Es5, ModuleKind::EsNext).code;
        assert!(es5.contains("var __generator ="), "{es5}");
        assert!(es5.contains("var __await ="), "{es5}");
        assert!(es5.contains("var __asyncGenerator ="), "{es5}");
        assert!(
            es5.contains(concat!(
                "var value = (function named() {\n",
                "    return __asyncGenerator(this, arguments, function named_1() {\n",
                "        return __generator(this, function (_a) {\n",
                "            switch (_a.label) {\n",
                "                case 0:\n",
                "                    return [4 /*yield*/, __await(ready)];\n",
                "                case 1:\n",
                "                    _a.sent();\n",
                "                    return [4 /*yield*/, __await(item)];\n",
                "                case 2: return [4 /*yield*/, _a.sent()];\n",
                "                case 3:\n",
                "                    _a.sent();\n",
                "                    return [2 /*return*/, done];\n",
            )),
            "{es5}"
        );

        let es2015 = emit_with(source, ScriptTarget::Es2015, ModuleKind::EsNext).code;
        assert!(es2015.contains("function named()"), "{es2015}");
        assert!(es2015.contains("function* named_1()"), "{es2015}");
        assert!(!es2015.contains("var __generator ="), "{es2015}");
    }

    #[test]
    fn keeps_single_switch_returns_on_the_case_line() {
        assert_eq!(
            emit("switch (value) { case 0: return () => value; }"),
            "switch (value) {\n    case 0: return () => value;\n}\n"
        );
    }

    #[test]
    fn preserves_multiline_switch_returns() {
        assert_eq!(
            emit_with(
                "switch (value) {\ncase 0:\nreturn value;\n}",
                ScriptTarget::EsNext,
                ModuleKind::EsNext,
            )
            .code,
            "switch (value) {\n    case 0:\n        return value;\n}\n"
        );
    }

    #[test]
    fn captures_block_scoped_do_loop_bindings_when_downleveling() {
        assert_eq!(
            emit_with(
                "function f() { var v = 1; do { let x = v; var v; var v = 2; () => x + v; } while (false); use(v); }",
                ScriptTarget::Es5,
                ModuleKind::EsNext,
            )
            .code,
            concat!(
                "function f() {\n",
                "    var v = 1;\n",
                "    var _loop_1 = function () {\n",
                "        var x_1 = v;\n",
                "        v = 2;\n",
                "        (function () { return x_1 + v; });\n",
                "    };\n",
                "    var v, v;\n",
                "    do {\n",
                "        _loop_1();\n",
                "    } while (false);\n",
                "    use(v);\n",
                "}\n",
            )
        );
    }

    #[test]
    fn lowers_for_of_and_array_bindings_for_es5() {
        assert_eq!(
            emit_with(
                "function doubleAndReturnAsArray(x: number, y: number, z: number) { let result = []; for (let arg of arguments) { result.push(arg + arg); } return result; }",
                ScriptTarget::Es5,
                ModuleKind::EsNext,
            )
            .code,
            "function doubleAndReturnAsArray(x, y, z) {\n    var result = [];\n    for (var _i = 0, arguments_1 = arguments; _i < arguments_1.length; _i++) {\n        var arg = arguments_1[_i];\n        result.push(arg + arg);\n    }\n    return result;\n}\n"
        );
        assert_eq!(
            emit_with(
                "function doubleAndReturnAsArray(x: number, y: number, z: number) { let blah = arguments[Symbol.iterator]; let result = []; for (let arg of blah()) { result.push(arg + arg); } return result; }",
                ScriptTarget::Es5,
                ModuleKind::EsNext,
            )
            .code,
            "function doubleAndReturnAsArray(x, y, z) {\n    var blah = arguments[Symbol.iterator];\n    var result = [];\n    for (var _i = 0, _a = blah(); _i < _a.length; _i++) {\n        var arg = _a[_i];\n        result.push(arg + arg);\n    }\n    return result;\n}\n"
        );
        assert_eq!(
            emit_with(
                "function asReversedTuple(a: number, b: string, c: boolean) { let [x, y, z] = arguments; return [z, y, x]; }",
                ScriptTarget::Es5,
                ModuleKind::EsNext,
            )
            .code,
            "function asReversedTuple(a, b, c) {\n    var x = arguments[0], y = arguments[1], z = arguments[2];\n    return [z, y, x];\n}\n"
        );
    }

    #[test]
    fn downlevel_for_of_temps_avoid_source_names_and_evaluate_rhs_once() {
        let output = emit_with(
            "function iterate(_i: number, _a: number, arguments_1: unknown) { for (let value of make()) { // keep\n use(value); } }",
            ScriptTarget::Es5,
            ModuleKind::EsNext,
        )
        .code;
        assert_eq!(output.matches("make()").count(), 1, "{output}");
        assert_eq!(
            output,
            "function iterate(_i, _a, arguments_1) {\n    for (var _b = 0, _c = make(); _b < _c.length; _b++) {\n        var value = _c[_b]; // keep\n        use(value);\n    }\n}\n"
        );
    }

    #[test]
    fn downlevel_array_bindings_handle_defaults_omissions_rest_and_nested_patterns() {
        let output = emit_with(
            "let [head = fallback(), , [nested], ...tail] = make();",
            ScriptTarget::Es5,
            ModuleKind::EsNext,
        )
        .code;
        assert_eq!(output.matches("make()").count(), 1, "{output}");
        assert_eq!(output.matches("fallback()").count(), 1, "{output}");
        assert_eq!(
            output,
            "var _a = make(), _b = _a[0], _c = _b === void 0 ? fallback() : _b, head = _c, _d = _a[2], nested = _d[0], tail = _a.slice(3);\n"
        );
        assert_eq!(
            emit_with(
                "for (let [x, y] of rows()) { use(x, y); }",
                ScriptTarget::Es5,
                ModuleKind::EsNext,
            )
            .code,
            "for (var _i = 0, _a = rows(); _i < _a.length; _i++) {\n    var _b = _a[_i], x = _b[0], y = _b[1];\n    use(x, y);\n}\n"
        );
    }

    #[test]
    fn preserves_for_of_and_array_bindings_at_es2015() {
        assert_eq!(
            emit_with(
                "let [x, y] = arguments; for (let value of values) { use(value); }",
                ScriptTarget::Es2015,
                ModuleKind::EsNext,
            )
            .code,
            "let [x, y] = arguments;\nfor (let value of values) {\n    use(value);\n}\n"
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
            "const view = <Panel enabled {...props} title=\"hello\"><span>{value}</span><Icon/></Panel>;\n"
        );
        assert_eq!(
            emit_jsx(source, JsxEmit::React),
            "const view = React.createElement(Panel, { enabled: true, ...props, title: \"hello\" }, React.createElement(\"span\", null, value), React.createElement(Icon, null));\n"
        );
        let fragment = "const view = <><span />{value}</>;";
        assert_eq!(
            emit_jsx(fragment, JsxEmit::Preserve),
            "const view = <><span/>{value}</>;\n"
        );
        assert_eq!(
            emit_jsx(fragment, JsxEmit::React),
            "const view = React.createElement(React.Fragment, null, React.createElement(\"span\", null), value);\n"
        );
    }

    #[test]
    fn classic_jsx_retains_the_react_import_used_by_the_transform() {
        let source =
            "import React from 'react'; type ReactNode = React.ReactNode; const view = <Panel />;";
        assert_eq!(
            emit_jsx(source, JsxEmit::React),
            "import React from 'react';\nconst view = React.createElement(Panel, null);\n"
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
    fn avoids_redundant_parentheses_around_assigned_function_expressions() {
        assert_eq!(
            emit_with(
                "let callback: unknown; callback = function () { return null; };",
                ScriptTarget::Es2015,
                ModuleKind::None,
            )
            .code,
            "let callback;\ncallback = function () { return null; };\n"
        );
    }

    #[test]
    fn preserves_multiline_array_layout_and_element_comments() {
        assert_eq!(
            emit_with(
                "const values = [\n    // object\n    { value: 1 },\n    // number\n    2\n];",
                ScriptTarget::Es2015,
                ModuleKind::None,
            )
            .code,
            "const values = [\n    // object\n    { value: 1 },\n    // number\n    2\n];\n"
        );
    }

    #[test]
    fn preserves_line_comments_inside_call_argument_lists() {
        assert_eq!(
            emit_with(
                "f(  // first\n    // second\n    () => {\n        // body\n    }\n    // trailing\n);",
                ScriptTarget::Es2015,
                ModuleKind::None,
            )
            .code,
            "f(// first\n// second\n() => {\n    // body\n}\n// trailing\n);\n"
        );
    }

    #[test]
    fn keeps_single_line_arrow_bodies_compact_in_constructor_arguments() {
        assert_eq!(
            emit_with(
                "const value = new Box(() => { return result; }); // trailing",
                ScriptTarget::Es2015,
                ModuleKind::None,
            )
            .code,
            "const value = new Box(() => { return result; }); // trailing\n"
        );
    }

    #[test]
    fn downlevels_async_functions_to_awaiter_for_es2015() {
        let output = emit_with(
            "async function run() { await task(); } const next = async value => await value;",
            ScriptTarget::Es2015,
            ModuleKind::None,
        )
        .code;
        assert!(output.starts_with("var __awaiter = "), "{output}");
        assert!(
            output.contains(
                "return __awaiter(this, void 0, void 0, function* () { yield task(); });"
            ),
            "{output}"
        );
        assert!(
            output.contains(
                "const next = (value) => __awaiter(void 0, void 0, void 0, function* () { return yield value; });"
            ),
            "{output}"
        );
    }

    #[test]
    fn lowers_es2015_async_object_rest_parameters_and_static_fields() {
        let object_rest = emit_with(
            "async ({ foo, bar, ...rest }) => bar(await foo);",
            ScriptTarget::Es2015,
            ModuleKind::None,
        )
        .code;
        assert!(object_rest.contains("var __rest = "), "{object_rest}");
        assert!(
            object_rest.contains("(_a) => __awaiter(void 0, void 0, void 0, function* () {\n    var { foo, bar } = _a, rest = __rest(_a, [\"foo\", \"bar\"]);\n    return bar(yield foo);\n})"),
            "{object_rest}"
        );

        let static_field = emit_with(
            "class Test { static member = async (x: string) => {}; }",
            ScriptTarget::Es2015,
            ModuleKind::None,
        )
        .code;
        assert!(
            static_field.contains("var _a;\nclass Test"),
            "{static_field}"
        );
        assert!(
            static_field.contains("}\n_a = Test;\nTest.member = (x) => __awaiter("),
            "{static_field}"
        );
    }

    #[test]
    fn lowers_es5_async_static_field_with_separate_awaiter_and_generator_receivers() {
        let output = emit_with(
            "class Test { static member = async (x: string) => {}; }",
            ScriptTarget::Es5,
            ModuleKind::None,
        )
        .code;
        assert!(
            output.contains(
                "Test.member = function (x) { return __awaiter(void 0, void 0, void 0, function () { return __generator(_a, function (_b) {"
            ),
            "{output}"
        );
    }

    #[test]
    fn preserves_trailing_spaces_in_source_comments() {
        assert_eq!(
            emit_with(
                "// trailing space \nclass Value {}",
                ScriptTarget::Es2015,
                ModuleKind::None,
            )
            .code,
            "// trailing space \nclass Value {\n}\n"
        );
    }

    #[test]
    fn separates_a_final_block_comment_from_the_synthesized_newline() {
        assert_eq!(
            emit_with(
                "let value = 1;\n/* retained\n*/",
                ScriptTarget::Es2015,
                ModuleKind::None,
            )
            .code,
            "let value = 1;\n/* retained\n*/ \n"
        );
    }

    #[test]
    fn preserves_omitted_array_binding_slots() {
        assert_eq!(
            emit_with(
                "let [, b, , a] = results;",
                ScriptTarget::Es2015,
                ModuleKind::None,
            )
            .code,
            "let [, b, , a] = results;\n"
        );
    }

    #[test]
    fn preserves_lexical_blocks_inside_switch_clauses() {
        assert_eq!(
            emit_with(
                "switch (kind) { case \"x\": { const [value] = items; use(value); } }",
                ScriptTarget::Es2015,
                ModuleKind::None,
            )
            .code,
            "switch (kind) {\n    case \"x\": {\n        const [value] = items;\n        use(value);\n    }\n}\n"
        );
    }

    #[test]
    fn keeps_else_if_on_one_line() {
        assert_eq!(
            emit_with(
                "if (first) { a(); } else if (second) { b(); } else { c(); }",
                ScriptTarget::Es2015,
                ModuleKind::None,
            )
            .code,
            "if (first) {\n    a();\n}\nelse if (second) {\n    b();\n}\nelse {\n    c();\n}\n"
        );
    }

    #[test]
    fn preserves_object_property_leading_comments_without_reassigning_arrow_comments() {
        assert_eq!(
            emit_with(
                "const value = () => ({\n    // property\n    item: true,\n    run: () => { // arrow\n        // body\n        return 1;\n    }\n});",
                ScriptTarget::Es2015,
                ModuleKind::None,
            )
            .code,
            "const value = () => ({\n    // property\n    item: true,\n    run: () => {\n        // body\n        return 1;\n    }\n});\n"
        );
    }

    #[test]
    fn compacts_recovered_single_statement_arrow_blocks() {
        let source = "namespace M { namespace N { var value = () => var result = 1;}; } }";
        let parsed = parse_source_file(source);
        assert!(!parsed.diagnostics.is_empty());
        let result = emit_source_file_with_settings(
            &parsed.arena,
            parsed.source_file,
            "input.ts",
            source,
            PrinterSettings {
                always_strict: false,
                target: ScriptTarget::Es2015,
                module: ModuleKind::None,
                jsx: JsxEmit::Preserve,
                emit_javascript: true,
                emit_declarations: false,
                source_map: false,
                inline_source_map: false,
                no_emit_helpers: false,
                remove_comments: false,
                use_define_for_class_fields: None,
            },
        )
        .unwrap();
        assert_eq!(
            result.code,
            "var M;\n(function (M) {\n    let N;\n    (function (N) {\n        var value = () => { var result = 1; };\n    })(N || (N = {}));\n})(M || (M = {}));\n"
        );
    }

    #[test]
    fn preserves_asi_sensitive_binary_operator_line_breaks() {
        assert_eq!(
            emit_with(
                "var value =\n\nleft\n\n+\n\n+\n\n+\n\nright;",
                ScriptTarget::Es2015,
                ModuleKind::None,
            )
            .code,
            "var value = left\n    +\n        + +right;\n"
        );
    }

    #[test]
    fn lowers_returned_class_expression_static_blocks_with_a_function_scoped_temp() {
        let source = "function outer() { return class Named { static { use(arguments); } } }";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::None).code,
            "function outer() {\n    var _a;\n    return _a = class Named {\n        },\n        (() => {\n            use(arguments);\n        })(),\n        _a;\n}\n"
        );
        assert_eq!(
            emit_with(source, ScriptTarget::Es2022, ModuleKind::None).code,
            "function outer() {\n    return class Named {\n        static {\n            use(arguments);\n        }\n    };\n}\n"
        );
    }

    #[test]
    fn hoists_commonjs_named_exports_of_function_declarations() {
        assert_eq!(
            emit_with(
                "function check(value: unknown) { return value; } export { check };",
                ScriptTarget::Es2015,
                ModuleKind::CommonJs,
            )
            .code,
            "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nexports.check = check;\nfunction check(value) { return value; }\n"
        );
    }

    #[test]
    fn moves_empty_es_module_marker_after_async_generator_runtime_declarations() {
        assert_eq!(
            emit_with(
                "export {}; async function* values() { yield 1; }",
                ScriptTarget::EsNext,
                ModuleKind::EsNext,
            )
            .code,
            "async function* values() { yield 1; }\nexport {};\n"
        );
    }

    #[test]
    fn lowers_nested_commonjs_dynamic_imports_in_async_generators() {
        let output = emit_with(
            concat!(
                "async function* foo() {\n",
                "    import((await import(yield \"foo\")).default);\n",
                "}",
            ),
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        )
        .code;
        let create_binding = output.find("var __createBinding").unwrap();
        let import_star = output.find("var __importStar").unwrap();
        let await_helper = output.find("var __await").unwrap();
        let async_generator = output.find("var __asyncGenerator").unwrap();
        let function = output.find("function foo()").unwrap();
        assert!(
            create_binding < import_star
                && import_star < await_helper
                && await_helper < async_generator
                && async_generator < function,
            "{output}"
        );
        assert!(!output.contains("Object.defineProperty(exports, \"__esModule\""));
        assert!(output.ends_with(concat!(
            "function foo() {\n",
            "    return __asyncGenerator(this, arguments, function* foo_1() {\n",
            "        Promise.resolve(`${(yield __await(Promise.resolve(`${yield yield __await(\"foo\")}`).then(s => __importStar(require(s))))).default}`).then(s => __importStar(require(s)));\n",
            "    });\n",
            "}\n",
        )));
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
    fn emits_source_compact_function_and_method_bodies_for_es_modules() {
        let source = "function declared(value: number) { return value; }\nconst expression = function () { value; };\nclass Box { method(value: number) { return value; } }\nconst object = { method() { value; } };";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::EsNext).code,
            "function declared(value) { return value; }\nconst expression = function () { value; };\nclass Box {\n    method(value) { return value; }\n}\nconst object = { method() { value; } };\n"
        );
    }

    #[test]
    fn keeps_comment_bearing_and_source_multiline_function_bodies_expanded() {
        let source = "function commented() { /* keep */ return 1; }\nfunction multiline() {\n    return 2;\n}";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::EsNext).code,
            "function commented() { /* keep */\n    return 1;\n}\nfunction multiline() {\n    return 2;\n}\n"
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
    fn lowers_auto_accessors_and_keeps_trailing_comments_on_the_getter() {
        let source = "class Box { accessor value: string; // trailing\n}";
        for target in [ScriptTarget::Es5, ScriptTarget::Es2015] {
            let output = emit_with(source, target, ModuleKind::None).code;
            assert!(output.contains("var __classPrivateFieldGet"), "{output}");
            assert!(
                output.contains("_Box_value_accessor_storage.set(this, void 0);"),
                "{output}"
            );
            assert!(output.contains("\"f\"); } // trailing\n"), "{output}");
            assert!(
                output.contains("_Box_value_accessor_storage = new WeakMap();"),
                "{output}"
            );
        }
    }

    #[test]
    fn downlevels_rest_setter_parameters_into_the_accessor_body() {
        let source = "class C { set X(...v) { } static set X(...v2) { } }";
        assert_eq!(
            emit_with(source, ScriptTarget::Es5, ModuleKind::EsNext).code,
            concat!(
                "var C = /** @class */ (function () {\n",
                "    function C() {\n",
                "    }\n",
                "    Object.defineProperty(C.prototype, \"X\", {\n",
                "        set: function () {\n",
                "            var v = [];\n",
                "            for (var _i = 0; _i < arguments.length; _i++) {\n",
                "                v[_i] = arguments[_i];\n",
                "            }\n",
                "        },\n",
                "        enumerable: false,\n",
                "        configurable: true\n",
                "    });\n",
                "    Object.defineProperty(C, \"X\", {\n",
                "        set: function () {\n",
                "            var v2 = [];\n",
                "            for (var _i = 0; _i < arguments.length; _i++) {\n",
                "                v2[_i] = arguments[_i];\n",
                "            }\n",
                "        },\n",
                "        enumerable: false,\n",
                "        configurable: true\n",
                "    });\n",
                "    return C;\n",
                "}());\n",
            )
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
    fn emits_literal_and_computed_literal_enum_member_names() {
        let source = "enum Keys { \"string\", 1, [\"computed\"], [3] }";
        assert_eq!(
            emit(source),
            "var Keys;\n(function (Keys) {\n    Keys[Keys[\"string\"] = 0] = \"string\";\n    Keys[Keys[1] = 1] = 1;\n    Keys[Keys[\"computed\"] = 2] = \"computed\";\n    Keys[Keys[3] = 3] = 3;\n})(Keys || (Keys = {}));\n"
        );

        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        assert_eq!(
            emit_declaration_file(&parsed.arena, parsed.source_file, "input.ts", source, false)
                .unwrap()
                .code,
            "declare enum Keys {\n    \"string\",\n    1,\n    [\"computed\"],\n    [3]\n}\n"
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
        let import_meanings = BTreeMap::new();
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
                no_emit_helpers: false,
                remove_comments: false,
                use_define_for_class_fields: None,
            },
            &EmitContext {
                bindings: &bindings,
                amd_module_name: None,
                amd_bundle: false,
                amd_dependencies: &[],
                enum_member_values: &member_values,
                enum_access_values: &accesses,
                import_runtime_meanings: &import_meanings,
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
            concat!("var M;\n", "(function (M) {\n", "})(M || (M = {}));\n",)
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
    fn omits_redundant_variable_for_function_namespace_merges() {
        assert_eq!(
            emit_with(
                "function f() {} namespace f { export const value = 1; }",
                ScriptTarget::Es2015,
                ModuleKind::EsNext,
            )
            .code,
            concat!(
                "function f() { }\n",
                "(function (f) {\n",
                "    f.value = 1;\n",
                "})(f || (f = {}));\n",
            )
        );
    }

    #[test]
    fn emits_namespace_variable_for_erased_ambient_value_merges() {
        assert_eq!(
            emit_with(
                "declare class C {} namespace C { var value; }",
                ScriptTarget::Es2015,
                ModuleKind::EsNext,
            )
            .code,
            concat!(
                "var C;\n",
                "(function (C) {\n",
                "    var value;\n",
                "})(C || (C = {}));\n",
            )
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
    fn keeps_reference_directives_inside_amd_after_generated_prologues() {
        let source = concat!(
            "///<reference path='types.d.ts' />\n",
            "import runtime = require(\"runtime\");\n",
            "runtime.run();\n",
        );
        assert_eq!(
            emit_amd(source).code,
            concat!(
                "define([\"require\", \"exports\", \"runtime\"], function (require, exports, runtime) {\n",
                "    \"use strict\";\n",
                "    Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "    ///<reference path='types.d.ts' />\n",
                "    runtime.run();\n",
                "});\n",
            )
        );
    }

    #[test]
    fn drops_compiler_resolved_reference_directives_from_amd_output() {
        let source =
            "///<reference path='ambient.ts' />\nimport A = require('M');\nvar c = new A();";
        let parsed = parse_source_file(source);
        let bindings = bind_source_file(&parsed.arena, parsed.source_file);
        let NodeData::SourceFile(file) = &parsed.arena.get(parsed.source_file).unwrap().data else {
            panic!("expected source file");
        };
        let import_meanings = BTreeMap::from([(file.statements.nodes[0], true)]);
        let enum_values = BTreeMap::new();
        assert_eq!(
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
                    source_map: false,
                    inline_source_map: false,
                    no_emit_helpers: false,
                    remove_comments: false,
                    use_define_for_class_fields: None,
                },
                &EmitContext {
                    bindings: &bindings,
                    amd_module_name: None,
                    amd_bundle: false,
                    amd_dependencies: &[],
                    enum_member_values: &enum_values,
                    enum_access_values: &enum_values,
                    import_runtime_meanings: &import_meanings,
                    preserve_const_enums: false,
                    inline_const_enums: false,
                },
            )
            .unwrap()
            .code,
            "define([\"require\", \"exports\", \"M\"], function (require, exports, A) {\n    \"use strict\";\n    Object.defineProperty(exports, \"__esModule\", { value: true });\n    var c = new A();\n});\n"
        );
    }

    #[test]
    fn orders_amd_es_imports_between_dependency_pragmas() {
        let source = concat!(
            "///<amd-dependency path='namedPragma' name='pragma'/>",
            "\n///<amd-dependency path='unnamedPragma'/>",
            "\nimport { value } from \"bound\";",
            "\nvalue;",
            "\nimport \"sideEffect\";",
        );
        assert_eq!(
            emit_amd(source).code,
            concat!(
                "///<amd-dependency path='namedPragma' name='pragma'/>\n",
                "///<amd-dependency path='unnamedPragma'/>\n",
                "define([\"require\", \"exports\", \"namedPragma\", \"bound\", \"unnamedPragma\", \"sideEffect\"], function (require, exports, pragma, bound_1) {\n",
                "    \"use strict\";\n",
                "    Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "    bound_1.value;\n",
                "});\n",
            )
        );
    }

    #[test]
    fn emits_amd_import_helpers_before_define() {
        let source = concat!(
            "import value from \"defaultModule\";\n",
            "import * as ns from \"namespaceModule\";\n",
            "value; ns;",
        );
        let output = emit_amd(source).code;
        let star_helper = output.find("var __createBinding").unwrap();
        let default_helper = output.find("var __importDefault").unwrap();
        let define = output.find("define([").unwrap();
        assert!(
            star_helper < default_helper && default_helper < define,
            "{output}"
        );
        assert!(
            output.contains(
                "define([\"require\", \"exports\", \"defaultModule\", \"namespaceModule\"], function (require, exports, defaultModule_1, ns) {"
            ),
            "{output}"
        );
        assert!(
            output.contains(
                "defaultModule_1 = __importDefault(defaultModule_1);\n    ns = __importStar(ns);"
            ),
            "{output}"
        );
        assert!(
            output.contains("defaultModule_1.default;\n    ns;"),
            "{output}"
        );
    }

    #[test]
    fn emits_amd_exported_enums_through_exports_mutation() {
        let source = "export enum CharCode { A, B }";
        assert_eq!(
            emit_amd(source).code,
            concat!(
                "define([\"require\", \"exports\"], function (require, exports) {\n",
                "    \"use strict\";\n",
                "    Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "    exports.CharCode = void 0;\n",
                "    var CharCode;\n",
                "    (function (CharCode) {\n",
                "        CharCode[CharCode[\"A\"] = 0] = \"A\";\n",
                "        CharCode[CharCode[\"B\"] = 1] = \"B\";\n",
                "    })(CharCode || (exports.CharCode = CharCode = {}));\n",
                "});\n",
            )
        );
    }

    #[test]
    fn routes_commonjs_amd_dependency_before_the_generated_prologue() {
        let source =
            "///<amd-dependency path='bar' name='b'/>\nimport m1 = require(\"m2\");\nm1.f();";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::CommonJs).code,
            "\"use strict\";\n///<amd-dependency path='bar' name='b'/>\nObject.defineProperty(exports, \"__esModule\", { value: true });\nconst m1 = require(\"m2\");\nm1.f();\n"
        );
    }

    #[test]
    fn drops_an_ordinary_leading_comment_owned_by_an_erased_statement() {
        let source = "// target: es5\ntype Hidden = { value: string };\nfunction visible() { }";
        assert_eq!(
            emit_always_strict(source, ScriptTarget::Es2015, ModuleKind::None).code,
            "\"use strict\";\nfunction visible() { }\n"
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
    fn system_modules_hoist_exported_functions_and_nested_var_bindings() {
        let source = "export function read() { return value; } for (let item of []) { var value = item; () => item; }";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::System).code,
            concat!(
                "System.register([], function (exports_1, context_1) {\n",
                "    \"use strict\";\n",
                "    var value;\n",
                "    var __moduleName = context_1 && context_1.id;\n",
                "    function read() { return value; }\n",
                "    exports_1(\"read\", read);\n",
                "    return {\n",
                "        setters: [],\n",
                "        execute: function () {\n",
                "            for (let item of []) {\n",
                "                value = item;\n",
                "                () => item;\n",
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
    fn emits_system_default_import_storage_and_exported_initializer() {
        let source = r#"
            import Namespace from "./b";
            export var x = new Namespace.Foo();
        "#;
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::System).code,
            concat!(
                "System.register([\"./b\"], function (exports_1, context_1) {\n",
                "    \"use strict\";\n",
                "    var b_1, x;\n",
                "    var __moduleName = context_1 && context_1.id;\n",
                "    return {\n",
                "        setters: [\n",
                "            function (b_1_1) {\n",
                "                b_1 = b_1_1;\n",
                "            }\n",
                "        ],\n",
                "        execute: function () {\n",
                "            exports_1(\"x\", x = new b_1.default.Foo());\n",
                "        }\n",
                "    };\n",
                "});\n",
            )
        );
    }

    #[test]
    fn emits_system_export_updates() {
        let source = "export let x = 1; x = 2; ++x; x++;";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::System).code,
            concat!(
                "System.register([], function (exports_1, context_1) {\n",
                "    \"use strict\";\n",
                "    var x;\n",
                "    var __moduleName = context_1 && context_1.id;\n",
                "    return {\n",
                "        setters: [],\n",
                "        execute: function () {\n",
                "            exports_1(\"x\", x = 1);\n",
                "            exports_1(\"x\", x = 2);\n",
                "            exports_1(\"x\", ++x);\n",
                "            exports_1(\"x\", (x++, x));\n",
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
            "var value = source === null || source === void 0 ? void 0 : source[key];\nvar merged = Object.assign({ a: 1 }, extra, { b: 2 });\nvar list = [].concat([], [0], items, [3]);\n"
        );
    }

    #[test]
    fn downlevel_object_spread_groups_properties_in_source_order() {
        let source = concat!(
            "const leading = { before: one(), [computed()]: two(), ...spread(), after: three() };",
            "const spreadFirst = { ...first, [key()]: value(), plain: after(), ...second(), tail: end() };",
        );
        let output = emit_with(source, ScriptTarget::Es2015, ModuleKind::EsNext).code;
        assert_eq!(
            output,
            concat!(
                "const leading = Object.assign({ before: one(), [computed()]: two() }, spread(), { after: three() });\n",
                "const spreadFirst = Object.assign({}, first, { [key()]: value(), plain: after() }, second(), { tail: end() });\n",
            )
        );
        for call in [
            "one()",
            "computed()",
            "two()",
            "spread()",
            "three()",
            "key()",
            "value()",
            "after()",
            "second()",
            "end()",
        ] {
            assert_eq!(output.matches(call).count(), 1, "{call}: {output}");
        }
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
            "var __extends = (this && this.__extends) || (function () {\n    var extendStatics = function (d, b) {\n        extendStatics = Object.setPrototypeOf ||\n            ({ __proto__: [] } instanceof Array && function (d, b) { d.__proto__ = b; }) ||\n            function (d, b) { for (var p in b) if (Object.prototype.hasOwnProperty.call(b, p)) d[p] = b[p]; };\n        return extendStatics(d, b);\n    };\n    return function (d, b) {\n        if (typeof b !== \"function\" && b !== null)\n            throw new TypeError(\"Class extends value \" + String(b) + \" is not a constructor or null\");\n        extendStatics(d, b);\n        function __() { this.constructor = d; }\n        d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());\n    };\n})();\nvar Point = /** @class */ (function () {\n    function Point(y) {\n        this.x = 1;\n        this.y = y;\n    }\n    Point.prototype.move = function (d) { this.x = this.x + d; };\n    Point.make = function () { return new Point(0); };\n    Point.origin = 0;\n    return Point;\n}());\nvar ColoredPoint = /** @class */ (function (_super) {\n    __extends(ColoredPoint, _super);\n    function ColoredPoint(y) {\n        var _this = _super.call(this, y) || this;\n        _this.color = 'red';\n        _this.color = 'blue';\n        return _this;\n    }\n    ColoredPoint.prototype.paint = function () { return this.color; };\n    return ColoredPoint;\n}(Point));\n"
        );
    }

    #[test]
    fn emits_anonymous_class_expression_under_typeof_for_es2015_and_es5() {
        let source = "function f() { return typeof class {} === \"function\"; }";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::EsNext).code,
            concat!(
                "function f() {\n",
                "    return typeof class {\n",
                "    } === \"function\";\n",
                "}\n",
            )
        );
        assert_eq!(
            emit_with(source, ScriptTarget::Es5, ModuleKind::EsNext).code,
            concat!(
                "function f() {\n",
                "    return typeof /** @class */ (function () {\n",
                "        function _class() {\n",
                "        }\n",
                "        return _class;\n",
                "    }()) === \"function\";\n",
                "}\n",
            )
        );
    }

    #[test]
    fn emits_named_and_inherited_class_expression_values() {
        let named = "const Value = class Inner { method() { return 1; } };";
        assert_eq!(
            emit_with(named, ScriptTarget::Es2015, ModuleKind::EsNext).code,
            concat!(
                "const Value = class Inner {\n",
                "    method() { return 1; }\n",
                "};\n",
            )
        );
        assert_eq!(
            emit_with(named, ScriptTarget::Es5, ModuleKind::EsNext).code,
            concat!(
                "var Value = /** @class */ (function () {\n",
                "    function Inner() {\n",
                "    }\n",
                "    Inner.prototype.method = function () { return 1; };\n",
                "    return Inner;\n",
                "}());\n",
            )
        );

        let inherited = emit_with(
            "function make() { return class extends Base { method() { return 1; } }; }",
            ScriptTarget::Es5,
            ModuleKind::EsNext,
        )
        .code;
        assert!(inherited.starts_with("var __extends = "), "{inherited}");
        assert!(
            inherited.contains("return /** @class */ (function (_super) {"),
            "{inherited}"
        );
        assert!(
            inherited.contains("__extends(_class, _super);"),
            "{inherited}"
        );
        assert!(inherited.ends_with("}(Base));\n}\n"), "{inherited}");
        assert!(!inherited.contains("return var"), "{inherited}");
    }

    #[test]
    fn rejects_native_class_expression_static_lowering_without_a_scoped_temp() {
        let source = "const Value = class Inner { static value = 1; };";
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let error = emit_source_file_with_settings(
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
                no_emit_helpers: false,
                remove_comments: false,
                use_define_for_class_fields: None,
            },
        )
        .unwrap_err();
        assert_eq!(error.kind, SyntaxKind::ClassExpression);

        assert_eq!(
            emit_with(source, ScriptTarget::Es2022, ModuleKind::EsNext).code,
            "const Value = class Inner {\n    static value = 1;\n};\n"
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
            "class Box {\n    constructor() {\n        this.value = 1;\n    }\n    read() { return this.value; }\n}\n"
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
                no_emit_helpers: false,
                remove_comments: false,
                use_define_for_class_fields: None,
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
                no_emit_helpers: false,
                remove_comments: false,
                use_define_for_class_fields: None,
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
    fn drops_comments_without_an_emitted_class_member_owner() {
        let source = concat!(
            "class VisualizationModel extends Base {\n",
            "    // interesting stuff here\n",
            "}\n",
        );
        for target in [ScriptTarget::Es2015, ScriptTarget::Es5] {
            let output = emit_with(source, target, ModuleKind::EsNext).code;
            assert!(!output.contains("interesting stuff"), "{output}");
        }
    }

    #[test]
    fn assigns_comments_to_emitted_previous_or_next_nodes() {
        let source = concat!(
            "function before() {} // keep trailing\n",
            "// erased interface comment\n",
            "interface Hidden {}\n",
            "// keep leading\n",
            "function after() {}\n",
        );
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::EsNext).code,
            concat!(
                "function before() { } // keep trailing\n",
                "// keep leading\n",
                "function after() { }\n",
            )
        );
    }

    #[test]
    fn does_not_synthesize_blank_lines_for_erased_trailing_statements() {
        let source = "type T = number; export interface I { value: T; }\n";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::CommonJs).code,
            concat!(
                "\"use strict\";\n",
                "Object.defineProperty(exports, \"__esModule\", { value: true });\n",
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
    fn preserves_trailing_comments_on_namespaced_class_declarations() {
        let source = concat!(
            "namespace M {\n",
            "    export class C implements I {} // unresolved I\n",
            "}\n",
        );
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::None).code,
            concat!(
                "var M;\n",
                "(function (M) {\n",
                "    class C {\n",
                "    } // unresolved I\n",
                "    M.C = C;\n",
                "})(M || (M = {}));\n",
            )
        );
    }

    #[test]
    fn preserves_final_immediate_trailing_statement_comment_in_amd() {
        let result = emit_with(
            "import \"file2\"; let a: number; // should not work",
            ScriptTarget::Es2015,
            ModuleKind::Amd,
        );
        assert!(
            result.code.contains("    let a; // should not work\n"),
            "{}",
            result.code
        );
    }

    #[test]
    fn drops_unowned_function_expression_body_opening_comment() {
        let result = emit_with(
            "const f = function () { // diagnostic context\n return 1;\n};",
            ScriptTarget::Es2015,
            ModuleKind::EsNext,
        );
        assert_eq!(result.code, "const f = function () {\n    return 1;\n};\n");
    }

    #[test]
    fn defers_reference_directives_until_their_runtime_import_owner() {
        let source = concat!(
            "/*! license */\n",
            "///<reference path='types.d.ts' />\n",
            "import mod = require(\"./mod\");\n",
            "export const value = mod.value;\n",
        );
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::CommonJs).code,
            concat!(
                "\"use strict\";\n",
                "/*! license */\n",
                "Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "exports.value = void 0;\n",
                "///<reference path='types.d.ts' />\n",
                "const mod = require(\"./mod\");\n",
                "const value = mod.value;\n",
                "exports.value = value;\n",
            )
        );
    }

    #[test]
    fn drops_reference_directives_owned_by_erased_statements() {
        let source = concat!(
            "///<reference path='types.d.ts' />\n",
            "interface Shape { value: number; }\n",
            "export const value: Shape | number = 1;\n",
        );
        let output = emit_with(source, ScriptTarget::Es2015, ModuleKind::CommonJs).code;
        assert_eq!(
            output,
            concat!(
                "\"use strict\";\n",
                "Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "exports.value = void 0;\n",
                "exports.value = 1;\n",
            )
        );
        assert!(!output.contains("<reference"));
    }

    #[test]
    fn preserves_detached_lib_reference_in_type_only_script() {
        let source = concat!(
            "/// <reference lib=\"dom\" />\n",
            "\n",
            "interface Thenable<T> extends PromiseLike<T> {}\n",
            "type Value = Awaited<Thenable<string>>;\n",
        );
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::None).code,
            "/// <reference lib=\"dom\" />\n",
        );
    }

    #[test]
    fn drops_script_reference_directive_owned_by_erased_statement() {
        let source = concat!(
            "/// <reference path=\"types.d.ts\" />\n",
            "interface Shape { value: number; }\n",
            "\n",
            "interface Other { name: string; }\n",
        );
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::None).code,
            "",
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
                no_emit_helpers: false,
                remove_comments: false,
                use_define_for_class_fields: None,
            },
        )
        .unwrap();
        assert_eq!(result.code, "\"use strict\";\nconst value = 1;\n");
    }

    #[test]
    fn does_not_synthesize_use_strict_for_preserved_external_modules() {
        let source = "export const value: number = 1;";
        for module in [
            ModuleKind::None,
            ModuleKind::Es2015,
            ModuleKind::Es2020,
            ModuleKind::Es2022,
            ModuleKind::EsNext,
            ModuleKind::Preserve,
        ] {
            let parsed = parse_source_file(source);
            let result = emit_source_file_with_settings(
                &parsed.arena,
                parsed.source_file,
                "input.ts",
                source,
                PrinterSettings {
                    always_strict: true,
                    target: ScriptTarget::Es2015,
                    module,
                    jsx: JsxEmit::Preserve,
                    emit_javascript: true,
                    emit_declarations: false,
                    source_map: false,
                    inline_source_map: false,
                    no_emit_helpers: false,
                    remove_comments: false,
                    use_define_for_class_fields: None,
                },
            )
            .unwrap();
            assert_eq!(result.code, "export const value = 1;\n", "{module:?}");
        }

        let script = "const value: number = 1;";
        let parsed = parse_source_file(script);
        let result = emit_source_file_with_settings(
            &parsed.arena,
            parsed.source_file,
            "input.ts",
            script,
            PrinterSettings {
                always_strict: true,
                target: ScriptTarget::Es2015,
                module: ModuleKind::None,
                jsx: JsxEmit::Preserve,
                emit_javascript: true,
                emit_declarations: false,
                source_map: false,
                inline_source_map: false,
                no_emit_helpers: false,
                remove_comments: false,
                use_define_for_class_fields: None,
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
            "export const value = 1;\nexport default function read() { return value; }\n"
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
            concat!(
                "\"use strict\";\n",
                "var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {\n",
                "    if (k2 === undefined) k2 = k;\n",
                "    var desc = Object.getOwnPropertyDescriptor(m, k);\n",
                "    if (!desc || (\"get\" in desc ? !m.__esModule : desc.writable || desc.configurable)) {\n",
                "      desc = { enumerable: true, get: function() { return m[k]; } };\n",
                "    }\n",
                "    Object.defineProperty(o, k2, desc);\n",
                "}) : (function(o, m, k, k2) {\n",
                "    if (k2 === undefined) k2 = k;\n",
                "    o[k2] = m[k];\n",
                "}));\n",
                "var __exportStar = (this && this.__exportStar) || function(m, exports) {\n",
                "    for (var p in m) if (p !== \"default\" && !Object.prototype.hasOwnProperty.call(exports, p)) __createBinding(exports, m, p);\n",
                "};\n",
                "var __importDefault = (this && this.__importDefault) || function (mod) {\n",
                "    return (mod && mod.__esModule) ? mod : { \"default\": mod };\n",
                "};\n",
                "Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "exports.result = void 0;\n",
                "const pkg_1 = __importDefault(require('pkg'));\n",
                "const { read: load, write } = require('pkg');\n",
                "require('side');\n",
                "exports.result = load;\n",
                "__exportStar(require('other'), exports);\n",
                "exports.default = pkg_1.default;\n",
            )
        );
    }

    #[test]
    fn emits_commonjs_export_star_with_binding_helpers() {
        let result = emit_with(
            "export * from './dep';",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert_eq!(
            result.code,
            concat!(
                "\"use strict\";\n",
                "var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {\n",
                "    if (k2 === undefined) k2 = k;\n",
                "    var desc = Object.getOwnPropertyDescriptor(m, k);\n",
                "    if (!desc || (\"get\" in desc ? !m.__esModule : desc.writable || desc.configurable)) {\n",
                "      desc = { enumerable: true, get: function() { return m[k]; } };\n",
                "    }\n",
                "    Object.defineProperty(o, k2, desc);\n",
                "}) : (function(o, m, k, k2) {\n",
                "    if (k2 === undefined) k2 = k;\n",
                "    o[k2] = m[k];\n",
                "}));\n",
                "var __exportStar = (this && this.__exportStar) || function(m, exports) {\n",
                "    for (var p in m) if (p !== \"default\" && !Object.prototype.hasOwnProperty.call(exports, p)) __createBinding(exports, m, p);\n",
                "};\n",
                "Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "__exportStar(require('./dep'), exports);\n",
            )
        );
    }

    #[test]
    fn emits_single_commonjs_named_imports_through_a_module_temp() {
        let source = concat!(
            "import { f } from 'demoModule';\n",
            "// keep comment\n",
            "let x1: string = demoNS.f;\n",
            "let x2: string = f;\n",
        );
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::CommonJs).code,
            concat!(
                "\"use strict\";\n",
                "Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "const demoModule_1 = require(\"demoModule\");\n",
                "// keep comment\n",
                "let x1 = demoNS.f;\n",
                "let x2 = demoModule_1.f;\n",
            )
        );
    }

    #[test]
    fn emits_multiple_commonjs_named_imports_through_one_collision_safe_temp() {
        let source = concat!(
            "import { first, second as alias } from './mod';\n",
            "const mod_1 = 1;\n",
            "const record = { first, alias };\n",
            "first();\n",
            "alias;\n",
        );
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::CommonJs).code,
            concat!(
                "\"use strict\";\n",
                "Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "const mod_2 = require(\"./mod\");\n",
                "const mod_1 = 1;\n",
                "const record = { first: mod_2.first, alias: mod_2.second };\n",
                "(0, mod_2.first)();\n",
                "mod_2.second;\n",
            )
        );
    }

    #[test]
    fn preserves_named_default_helpers_alongside_named_module_temps() {
        let source = "import { default as Foo, read } from './b'; Foo; read();";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::CommonJs).code,
            concat!(
                "\"use strict\";\n",
                "var __importDefault = (this && this.__importDefault) || function (mod) {\n",
                "    return (mod && mod.__esModule) ? mod : { \"default\": mod };\n",
                "};\n",
                "Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "const b_1 = __importDefault(require('./b'));\n",
                "const b_2 = require(\"./b\");\n",
                "b_1.default;\n",
                "(0, b_2.read)();\n",
            )
        );
    }

    #[test]
    fn emits_unbound_named_import_calls_directly_to_commonjs_exports() {
        let source = "import { vextend } from './func';\nexport var a = vextend({ watch: {} });";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::CommonJs).code,
            "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nexports.a = void 0;\nconst func_1 = require(\"./func\");\nexports.a = (0, func_1.vextend)({ watch: {} });\n"
        );
    }

    #[test]
    fn preserves_an_erased_external_module_with_an_empty_export() {
        let source = "export declare namespace Foo { export var static: any; }";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::None).code,
            "export {};\n"
        );
    }

    #[test]
    fn preinitializes_local_named_exports_by_their_exported_runtime_name() {
        let runtime = emit_with(
            "import value from './dep'; export { value as result };",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert!(
            runtime
                .code
                .contains("exports.result = void 0;\nconst dep_1 = __importDefault"),
            "{}",
            runtime.code
        );
        assert!(!runtime.code.contains("exports.value = void 0;"));

        let type_only = emit_with(
            "interface Shape {} export { Shape };",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert!(!type_only.code.contains("void 0;"), "{}", type_only.code);
    }

    #[test]
    fn emits_merged_type_and_import_binding_as_a_commonjs_default_export() {
        let source = concat!(
            "export default interface zzz { x: string; }\n",
            "import zzz from \"./b\";\n",
            "const x: zzz = { x: \"\" };\n",
            "zzz;\n",
            "export { zzz as default };\n",
        );
        let result = emit_with(source, ScriptTarget::Es2015, ModuleKind::CommonJs);
        assert_eq!(
            result.code,
            concat!(
                "\"use strict\";\n",
                "var __importDefault = (this && this.__importDefault) || function (mod) {\n",
                "    return (mod && mod.__esModule) ? mod : { \"default\": mod };\n",
                "};\n",
                "Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "exports.default = void 0;\n",
                "const b_1 = __importDefault(require(\"./b\"));\n",
                "exports.default = b_1.default;\n",
                "const x = { x: \"\" };\n",
                "b_1.default;\n",
            )
        );
    }

    #[test]
    fn lowers_simple_commonjs_export_initializers_and_rewrites_local_uses() {
        let result = emit_with(
            "export const zzz = 123; zzz; export default zzz;",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert_eq!(
            result.code,
            concat!(
                "\"use strict\";\n",
                "Object.defineProperty(exports, \"__esModule\", { value: true });\n",
                "exports.zzz = void 0;\n",
                "exports.zzz = 123;\n",
                "exports.zzz;\n",
                "exports.default = exports.zzz;\n",
            )
        );
    }

    #[test]
    fn lowers_commonjs_exported_object_initializers_directly() {
        let result = emit_with(
            "export var item = { get value() { return 1; } }; item.value;",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert!(result.code.contains("exports.item = {"), "{}", result.code);
        assert!(!result.code.contains("var item ="), "{}", result.code);
        assert!(
            result.code.contains("exports.item.value;"),
            "{}",
            result.code
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
        assert!(result.code.contains("var Model = Models.Model;"));
    }

    #[test]
    fn erases_empty_namespace_aliases_and_preserves_runtime_alias_chains() {
        let empty = emit_with(
            "namespace M { export namespace N {} export import X = N; } import r = M.X;",
            ScriptTarget::Es2015,
            ModuleKind::EsNext,
        );
        assert_eq!(
            empty.code,
            concat!("var M;\n", "(function (M) {\n", "})(M || (M = {}));\n",)
        );
        let cyclic = emit_with(
            "namespace M { namespace N { import X = N; } export import Y = N; }",
            ScriptTarget::Es2015,
            ModuleKind::EsNext,
        );
        assert_eq!(cyclic.code, empty.code);

        let instantiated = emit_with(
            "namespace M { namespace N { class C {} } import R = N; export import X = R; }",
            ScriptTarget::Es2015,
            ModuleKind::EsNext,
        );
        assert_eq!(
            instantiated.code,
            concat!(
                "var M;\n",
                "(function (M) {\n",
                "    let N;\n",
                "    (function (N) {\n",
                "        class C {\n",
                "        }\n",
                "    })(N || (N = {}));\n",
                "    var R = N;\n",
                "    M.X = R;\n",
                "})(M || (M = {}));\n",
            )
        );
    }

    #[test]
    fn emits_unused_internal_aliases_when_their_targets_have_runtime_values() {
        let result = emit_with(
            "namespace foo { export class Provide {} export namespace bar { export namespace baz { export class boo {} } } } import provide = foo; import booz = foo.bar.baz;",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert!(
            result.code.contains("var provide = foo;"),
            "{}",
            result.code
        );
        assert!(
            result.code.contains("var booz = foo.bar.baz;"),
            "{}",
            result.code
        );
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
    fn always_strict_exports_namespace_functions_on_the_namespace_object() {
        let source =
            "namespace M {\n    export function f() {\n        var arguments = [];\n    }\n}";
        assert_eq!(
            emit_always_strict(source, ScriptTarget::Es2015, ModuleKind::CommonJs).code,
            "\"use strict\";\nvar M;\n(function (M) {\n    function f() {\n        var arguments = [];\n    }\n    M.f = f;\n})(M || (M = {}));\n"
        );
    }

    #[test]
    fn commonjs_prologue_precedes_an_exported_initializer_leading_comment() {
        let source = "// Module commonjs\nexport const a = 1;";
        assert_eq!(
            emit_always_strict(source, ScriptTarget::Es2015, ModuleKind::CommonJs).code,
            "\"use strict\";\nObject.defineProperty(exports, \"__esModule\", { value: true });\nexports.a = void 0;\n// Module commonjs\nexports.a = 1;\n"
        );
    }

    #[test]
    fn detached_file_header_precedes_commonjs_generated_prologue() {
        let source = "/* file header */\n\nexport const value = 1;";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::CommonJs).code,
            "\"use strict\";\n/* file header */\nObject.defineProperty(exports, \"__esModule\", { value: true });\nexports.value = void 0;\nexports.value = 1;\n"
        );
    }

    #[test]
    fn remove_comments_suppresses_detached_inline_and_trailing_source_comments() {
        let source = "// header\n\nconst value = 1 /* inline */; // trailing";
        let parsed = parse_source_file(source);
        let mut settings = ts_options::CompilerOptions::default().printer_settings();
        settings.always_strict = false;
        settings.target = ScriptTarget::EsNext;
        settings.module = ModuleKind::EsNext;
        settings.remove_comments = true;
        let result = emit_source_file_with_settings(
            &parsed.arena,
            parsed.source_file,
            "source.ts",
            source,
            settings,
        )
        .unwrap();
        assert_eq!(result.code, "const value = 1;\n");
    }

    #[test]
    fn keeps_first_statement_comment_after_commonjs_generated_prologue() {
        let source = "// file header\n\n// statement comment\nexport const value = 1;";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::CommonJs).code,
            "\"use strict\";\n// file header\nObject.defineProperty(exports, \"__esModule\", { value: true });\nexports.value = void 0;\n// statement comment\nexports.value = 1;\n"
        );
    }

    #[test]
    fn detached_file_header_precedes_runtime_after_erased_declarations() {
        let source = "// file header\n\ntype Alias = string;\nlet value: Alias = \"x\";";
        assert_eq!(
            emit_with(source, ScriptTarget::Es2015, ModuleKind::None).code,
            "// file header\nlet value = \"x\";\n"
        );
    }

    #[test]
    fn transforms_exported_declarations_to_commonjs() {
        let result = emit_with(
            "export const value = 1; export function read() { return value; } export class Box {} export enum Color { Red }",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        for assignment in [
            "exports.value = 1;",
            "exports.read = read;",
            "exports.Box = Box;",
            "exports.Color = Color = {}",
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
            "exports.value = 1;",
            "exports.State = State = {}",
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
            "import { Input } from \"./types\";\nexport declare const version: number;\nexport declare function identity<T>(value: T): T;\nexport declare function parse(value: string): string;\nexport declare class Store<T> {\n    value: T;\n    read(input: T): T;\n}\nexport interface Box<T> {\n    value: T;\n}\nexport type Maybe<T> = T | undefined;\nexport declare enum Color {\n    Red,\n    Blue = 2\n}\nexport declare namespace Helpers {\n    export function read(value: string): string;\n}\nexport { Input };\n"
        );
        assert!(result.source_map.is_some());
    }

    #[test]
    fn declaration_emit_erases_empty_binding_patterns_and_preserves_module_scope() {
        let source = "export let [,,[,[],,[],]] = undefined as any;";
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        assert_eq!(
            emit_declaration_file(&parsed.arena, parsed.source_file, "input.ts", source, false)
                .unwrap()
                .code,
            "export {};\n"
        );
    }

    #[test]
    fn declaration_emit_keeps_named_declarators_beside_empty_patterns() {
        let source = "export let [] = [] as any, value = 1;";
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        assert_eq!(
            emit_declaration_file(&parsed.arena, parsed.source_file, "input.ts", source, false)
                .unwrap()
                .code,
            "export declare let value: any;\n"
        );
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

    #[test]
    fn export_assignment_prevents_a_redundant_declaration_scope_seal() {
        let source = "interface Color { c: string; }\nexport default Color;";
        let parsed = parse_source_file(source);
        let NodeData::SourceFile(file) = &parsed.arena.get(parsed.source_file).unwrap().data else {
            panic!("expected source file");
        };
        let reachability = BTreeMap::from([(
            parsed.source_file,
            file.statements
                .nodes
                .iter()
                .copied()
                .collect::<BTreeSet<_>>(),
        )]);
        assert_eq!(
            emit_declaration_file_with_reachability(
                &parsed.arena,
                parsed.source_file,
                "input.ts",
                source,
                false,
                Some(&reachability),
                None,
            )
            .unwrap()
            .code,
            "interface Color {\n    c: string;\n}\nexport default Color;\n"
        );
    }
}
