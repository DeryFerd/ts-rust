//! Deterministic modern-JavaScript emission from the generated TypeScript AST.

use std::error::Error;
use std::fmt;

use ts_ast::{Node, NodeArena, NodeData, NodeId, NodeList, SyntaxKind};
use ts_options::{ModuleKind, PrinterSettings, ScriptTarget};
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
pub fn emit_source_file_with_settings(
    arena: &NodeArena,
    source_file: NodeId,
    source_name: &str,
    source_text: &str,
    settings: PrinterSettings,
) -> Result<EmitResult, EmitError> {
    if !settings.emit_javascript {
        return Ok(EmitResult::default());
    }
    let mut printer = Printer {
        arena,
        writer: Writer::default(),
        settings,
        source_map: settings.source_map.then(SourceMapBuilder::new),
        source_text,
        source_line_starts: settings.source_map.then(|| line_starts(source_text)),
    };
    let node = printer.node(source_file)?.clone();
    let NodeData::SourceFile(data) = &node.data else {
        return Err(Printer::unsupported(source_file, node.kind));
    };
    for statement in &data.statements.nodes {
        printer.emit_statement(*statement)?;
    }
    let source_map = printer
        .source_map
        .map(|builder| builder.finish(None, vec![source_name.to_owned()]));
    Ok(EmitResult {
        code: printer.writer.finish(),
        source_map,
    })
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
                self.output.push_str("  ");
                self.column += 2;
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
                .saturating_mul(2)
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

struct Printer<'a> {
    arena: &'a NodeArena,
    writer: Writer,
    settings: PrinterSettings,
    source_map: Option<SourceMapBuilder>,
    source_text: &'a str,
    source_line_starts: Option<Vec<usize>>,
}

impl Printer<'_> {
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

    fn emit_statement(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
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
                self.emit_variable_list(data.declaration_list)?;
                self.writer.write(";");
            }
            NodeData::FunctionDeclaration(data) => {
                self.writer.write("function ");
                if let Some(name) = data.name {
                    self.emit_expression(name, 0)?;
                }
                self.emit_parameters(&data.parameters)?;
                self.writer.write(" ");
                self.emit_block(data.body.expect("body checked above"))?;
            }
            NodeData::ClassDeclaration(data) => self.emit_class(data)?,
            NodeData::EnumDeclaration(data) => self.emit_enum(data)?,
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
                    self.writer.write(" else ");
                    self.emit_embedded(otherwise)?;
                }
            }
            NodeData::WhileStatement(data) => {
                self.writer.write("while (");
                self.emit_expression(data.expression, 0)?;
                self.writer.write(") ");
                self.emit_embedded(data.statement)?;
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
                self.writer.write("; ");
                if let Some(condition) = data.condition {
                    self.emit_expression(condition, 0)?;
                }
                self.writer.write("; ");
                if let Some(incrementor) = data.incrementor {
                    self.emit_expression(incrementor, 0)?;
                }
                self.writer.write(") ");
                self.emit_embedded(data.statement)?;
            }
            NodeData::ImportDeclaration(data) => self.emit_import(data)?,
            NodeData::ExportAssignment(data) => {
                if self.settings.module == ModuleKind::CommonJs {
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

    fn emit_block(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        let NodeData::Block(data) = &node.data else {
            return Err(Self::unsupported(id, node.kind));
        };
        self.writer.write("{");
        self.writer.newline();
        self.writer.indent += 1;
        for statement in &data.statements.nodes {
            self.emit_statement(*statement)?;
        }
        self.writer.indent -= 1;
        self.writer.write("}");
        Ok(())
    }

    fn emit_embedded(&mut self, id: NodeId) -> Result<(), EmitError> {
        if matches!(&self.node(id)?.data, NodeData::Block(_)) {
            return self.emit_block(id);
        }
        self.writer.write("{");
        self.writer.newline();
        self.writer.indent += 1;
        self.emit_statement(id)?;
        self.writer.indent -= 1;
        self.writer.write("}");
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
            self.emit_expression(data.name, 0)?;
            if let Some(initializer) = data.initializer {
                self.writer.write(" = ");
                self.emit_expression(initializer, 1)?;
            }
        }
        self.writer.write(")");
        Ok(())
    }

    fn emit_class(&mut self, data: &ts_ast::ClassDeclarationData) -> Result<(), EmitError> {
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
        for member in &data.members.nodes {
            let node = self.node(*member)?.clone();
            match &node.data {
                NodeData::MethodDeclaration(method) if method.body.is_some() => {
                    self.emit_expression(method.name, 0)?;
                    self.emit_parameters(&method.parameters)?;
                    self.writer.write(" ");
                    self.emit_block(method.body.expect("body checked above"))?;
                    self.writer.newline();
                }
                NodeData::MethodDeclaration(_) => {}
                NodeData::PropertyDeclaration(property) => {
                    self.emit_expression(property.name, 0)?;
                    if let Some(initializer) = property.initializer {
                        self.writer.write(" = ");
                        self.emit_expression(initializer, 1)?;
                    }
                    self.writer.write(";");
                    self.writer.newline();
                }
                _ => return Err(Self::unsupported(*member, node.kind)),
            }
        }
        self.writer.indent -= 1;
        self.writer.write("}");
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
            let node = self.node(*member)?.clone();
            let NodeData::EnumMember(member) = &node.data else {
                return Err(Self::unsupported(*member, node.kind));
            };
            let member_name = self.identifier_text(member.name)?.to_owned();
            self.writer.write(&name);
            self.writer.write("[");
            let is_string_member = if let Some(initializer) = member.initializer {
                matches!(
                    &self.node(initializer)?.data,
                    NodeData::StringLiteral(_) | NodeData::NoSubstitutionTemplateLiteral(_)
                )
            } else {
                false
            };
            if is_string_member {
                write_quoted(&mut self.writer, &member_name);
                self.writer.write("] = ");
                self.emit_expression(member.initializer.expect("initializer checked above"), 1)?;
            } else {
                self.writer.write(&name);
                self.writer.write("[");
                write_quoted(&mut self.writer, &member_name);
                self.writer.write("] = ");
                if let Some(initializer) = member.initializer {
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
        if self.settings.module == ModuleKind::CommonJs {
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
        self.writer.write(";");
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
        if let Some(name) = clause.name {
            self.writer.write(self.variable_keyword());
            self.writer.write(" ");
            self.emit_expression(name, 0)?;
            self.writer.write(" = require(");
            self.emit_expression(data.module_specifier, 0)?;
            self.writer.write(").default;");
            if clause.named_bindings.is_some() {
                self.writer.newline();
            }
        }
        if let Some(bindings) = clause.named_bindings {
            self.writer.write(self.variable_keyword());
            self.writer.write(" { ");
            self.emit_commonjs_named_imports(bindings)?;
            self.writer.write(" } = require(");
            self.emit_expression(data.module_specifier, 0)?;
            self.writer.write(");");
        }
        Ok(())
    }

    fn emit_commonjs_named_imports(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        let NodeData::NamedImports(data) = &node.data else {
            return Err(Self::unsupported(id, node.kind));
        };
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
                self.writer.write(": ");
            }
            self.emit_expression(specifier.name, 0)?;
        }
        Ok(())
    }

    fn emit_named_imports(&mut self, id: NodeId) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
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
        if self.settings.module == ModuleKind::CommonJs {
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

    #[allow(clippy::too_many_lines)]
    fn emit_expression(&mut self, id: NodeId, parent_precedence: u8) -> Result<(), EmitError> {
        let node = self.node(id)?.clone();
        match &node.data {
            NodeData::Identifier(data) => self.writer.write(&data.text),
            NodeData::NumericLiteral(data) => self.writer.write(&data.text),
            NodeData::BigIntLiteral(data) => self.writer.write(&data.text),
            NodeData::StringLiteral(data) => write_quoted(&mut self.writer, &data.text),
            NodeData::KeywordExpression(_) => self.writer.write(match node.kind {
                SyntaxKind::NullKeyword => "null",
                SyntaxKind::TrueKeyword => "true",
                SyntaxKind::FalseKeyword => "false",
                _ => return Err(Self::unsupported(id, node.kind)),
            }),
            NodeData::ParenthesizedExpression(data) => {
                self.writer.write("(");
                self.emit_expression(data.expression, 0)?;
                self.writer.write(")");
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
                self.writer.write(" ");
                self.emit_expression(
                    data.right,
                    if right_associative {
                        precedence
                    } else {
                        precedence + 1
                    },
                )?;
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
                    self.writer.write(if data.question_dot_token.is_some() {
                        "?."
                    } else {
                        "."
                    });
                    self.emit_expression(data.name, 18)?;
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
                self.writer.write("[");
                self.emit_expression_list(&data.elements)?;
                self.writer.write("]");
            }
            NodeData::ObjectLiteralExpression(data) => {
                self.writer.write("{ ");
                for (index, property) in data.properties.nodes.iter().enumerate() {
                    if index != 0 {
                        self.writer.write(", ");
                    }
                    let node = self.node(*property)?.clone();
                    let NodeData::PropertyAssignment(property) = &node.data else {
                        return Err(Self::unsupported(*property, node.kind));
                    };
                    self.emit_expression(property.name, 0)?;
                    self.writer.write(": ");
                    self.emit_expression(property.initializer, 1)?;
                }
                self.writer.write(" }");
            }
            NodeData::ArrowFunction(data) => {
                if self.settings.target < ScriptTarget::Es2015 {
                    let wrap = parent_precedence > 1;
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
                let wrap = parent_precedence > 1;
                if wrap {
                    self.writer.write("(");
                }
                self.emit_parameters(&data.parameters)?;
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
        for (index, expression) in list.nodes.iter().enumerate() {
            if index != 0 {
                self.writer.write(", ");
            }
            self.emit_expression(*expression, 1)?;
        }
        if list.has_trailing_comma && !list.nodes.is_empty() {
            self.writer.write(",");
        }
        Ok(())
    }

    fn identifier_text(&self, id: NodeId) -> Result<&str, EmitError> {
        let node = self.node(id)?;
        if let NodeData::Identifier(data) = &node.data {
            Ok(&data.text)
        } else {
            Err(Self::unsupported(id, node.kind))
        }
    }
}

fn write_quoted(writer: &mut Writer, text: &str) {
    writer.write("\"");
    for ch in text.chars() {
        match ch {
            '\\' => writer.write("\\\\"),
            '"' => writer.write("\\\""),
            '\n' => writer.write("\\n"),
            '\r' => writer.write("\\r"),
            '\t' => writer.write("\\t"),
            ch if ch.is_control() => writer.write(&format!("\\u{:04x}", u32::from(ch))),
            ch => writer.write(&ch.to_string()),
        }
    }
    writer.write("\"");
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
    use ts_options::{JsxEmit, ModuleKind, PrinterSettings, ScriptTarget};
    use ts_parser::parse_source_file;

    use super::{emit_source_file, emit_source_file_with_settings, original_position};

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

    #[test]
    fn erases_types_and_prints_declarations() {
        assert_eq!(
            emit(
                "interface Shape { area(): number; } type Id<T> = T; const answer: number = 42; function add<T>(a: number, b?: number): number { return a + b; }"
            ),
            "const answer = 42;\nfunction add(a, b) {\n  return a + b;\n}\n"
        );
    }

    #[test]
    fn prints_classes_and_control_flow() {
        assert_eq!(
            emit(
                "class Counter extends Base implements Shape { value: number = 0; inc(step: number) { value = value + step; } } let i: number = 0; while (i < 2) { i = i + 1; } for (let j: number = 0; j < 2; j = j + 1) { i = i + j; }"
            ),
            "class Counter extends Base {\n  value = 0;\n  inc(step) {\n    value = value + step;\n  }\n}\nlet i = 0;\nwhile (i < 2) {\n  i = i + 1;\n}\nfor (let j = 0; j < 2; j = j + 1) {\n  i = i + j;\n}\n"
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
    fn emits_enums_deterministically() {
        assert_eq!(
            emit("enum Color { Red, Green = 4, Blue, Label = 'blue' }"),
            "var Color;\n(function (Color) {\n  Color[Color[\"Red\"] = 0] = \"Red\";\n  Color[Color[\"Green\"] = 4] = \"Green\";\n  Color[Color[\"Blue\"] = 5] = \"Blue\";\n  Color[\"Label\"] = \"blue\";\n})(Color || (Color = {}));\n"
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
    fn transforms_es_modules_to_commonjs() {
        let result = emit_with(
            "import main, { read as load, write } from 'pkg'; import 'side'; export { load as result }; export * from 'other'; export default main;",
            ScriptTarget::Es2015,
            ModuleKind::CommonJs,
        );
        assert_eq!(
            result.code,
            "const main = require(\"pkg\").default;\nconst { read: load, write } = require(\"pkg\");\nrequire(\"side\");\nexports.result = load;\nObject.assign(exports, require(\"other\"));\nexports.default = main;\n"
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
}
