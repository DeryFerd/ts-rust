//! Ordered AST walks for the pinned type and symbol baseline generator.

use std::{error::Error, fmt, fmt::Write as _};

use ts_ast::{Node, NodeArena, NodeData, NodeFlags, NodeId, NodeRef, SyntaxKind};
use ts_compiler::{
    CanonicalArtifactQueryError, CanonicalProgramCheckError, CanonicalProgramCheckFailureClass,
    CanonicalProgramQueries, CanonicalSymbolId, CanonicalTypeFormatFlags, CanonicalTypeId, Program,
    SourceFile,
};

use crate::{
    Case, Unit, baseline_unit_name, is_default_library_file, pinned_project_config,
    project_config_unit, project_root_unit_indices, remove_test_path_prefixes,
    unit_uses_implicit_references, virtual_unit_path,
};

pub(crate) mod project;
pub(crate) mod symbols;
pub(crate) mod types;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SemanticArtifactKind {
    Types,
    Symbols,
}

impl SemanticArtifactKind {
    pub(crate) const fn extension(self) -> &'static str {
        match self {
            Self::Types => types::EXTENSION,
            Self::Symbols => symbols::EXTENSION,
        }
    }

    pub(crate) fn baseline_base(self, file_name: &str) -> Option<&str> {
        match self {
            Self::Types => types::baseline_base(file_name),
            Self::Symbols => symbols::baseline_base(file_name),
        }
    }
}

/// Nodes visited by each pinned baseline walk, grouped in harness input order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct SemanticArtifactWalk {
    pub(crate) types: Vec<NodeRef>,
    pub(crate) symbols: Vec<NodeRef>,
}

/// Owned baselines produced while the original canonical checker remains alive.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct GeneratedSemanticArtifacts {
    pub(crate) walk: SemanticArtifactWalk,
    pub(crate) types: Result<String, String>,
    pub(crate) symbols: Result<String, String>,
}

impl GeneratedSemanticArtifacts {
    pub(crate) fn unavailable(walk: SemanticArtifactWalk, detail: &str) -> Self {
        Self {
            walk,
            types: Err(detail.to_owned()),
            symbols: Err(detail.to_owned()),
        }
    }

    pub(crate) fn result(&self, kind: SemanticArtifactKind) -> &Result<String, String> {
        match kind {
            SemanticArtifactKind::Types => &self.types,
            SemanticArtifactKind::Symbols => &self.symbols,
        }
    }

    pub(crate) fn visited_nodes(&self, kind: SemanticArtifactKind) -> usize {
        match kind {
            SemanticArtifactKind::Types => self.walk.types.len(),
            SemanticArtifactKind::Symbols => self.walk.symbols.len(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ArtifactLine {
    line: usize,
    source_text: String,
    value: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ArtifactIdentity {
    Type(CanonicalTypeId),
    Symbol(Option<CanonicalSymbolId>),
}

struct QueriedArtifactLine {
    line: Option<ArtifactLine>,
    identity: ArtifactIdentity,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ArtifactRenderError {
    pub(crate) class: CanonicalProgramCheckFailureClass,
    pub(crate) detail: String,
}

impl ArtifactRenderError {
    fn invariant(code: &'static str, detail: String) -> Self {
        Self {
            class: CanonicalProgramCheckFailureClass::Fatal {
                invariant_code: code,
            },
            detail,
        }
    }

    fn query(operation: &str, file_name: &str, error: CanonicalArtifactQueryError) -> Self {
        let class = match error {
            CanonicalArtifactQueryError::UnsupportedNode { .. } => {
                CanonicalProgramCheckFailureClass::Unsupported {
                    capability_code: "ARTIFACT.UNSUPPORTED_NODE",
                }
            }
            CanonicalArtifactQueryError::MissingType { .. } => {
                CanonicalProgramCheckFailureClass::Unsupported {
                    capability_code: "ARTIFACT.MISSING_TYPE",
                }
            }
            CanonicalArtifactQueryError::SourceCheck(error) => {
                CanonicalProgramCheckError::SourceCheck {
                    file_name: file_name.to_owned(),
                    error,
                }
                .failure_class()
            }
            CanonicalArtifactQueryError::DeclaredType(error) => {
                CanonicalProgramCheckError::SourceCheck {
                    file_name: file_name.to_owned(),
                    error: error.into(),
                }
                .failure_class()
            }
            // Alias failures include provenance checks. Until the compiler
            // exposes a typed alias classifier, keep them fatal.
            CanonicalArtifactQueryError::Alias(_) => CanonicalProgramCheckFailureClass::Fatal {
                invariant_code: "INV.ARTIFACT.UNCLASSIFIED_ALIAS",
            },
            CanonicalArtifactQueryError::MissingFile(_)
            | CanonicalArtifactQueryError::ForeignNode(_)
            | CanonicalArtifactQueryError::StaleFile { .. }
            | CanonicalArtifactQueryError::InvalidType { .. }
            | CanonicalArtifactQueryError::InvalidSymbol { .. }
            | CanonicalArtifactQueryError::ForeignSymbol(_)
            | CanonicalArtifactQueryError::ForeignDeclaration { .. } => {
                CanonicalProgramCheckFailureClass::Fatal {
                    invariant_code: "INV.ARTIFACT.QUERY",
                }
            }
        };
        Self {
            class,
            detail: format!("{operation}: {error}"),
        }
    }
}

impl fmt::Display for ArtifactRenderError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.detail)
    }
}

impl Error for ArtifactRenderError {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ArtifactWalkError {
    MissingNode {
        file_name: String,
        node: NodeId,
    },
    MissingParent {
        file_name: String,
        node: NodeId,
        parent: NodeId,
    },
    ForeignNode {
        file_name: String,
        node: NodeId,
    },
}

impl fmt::Display for ArtifactWalkError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingNode { file_name, node } => {
                write!(
                    formatter,
                    "semantic artifact walk cannot resolve {node:?} in '{file_name}'"
                )
            }
            Self::MissingParent {
                file_name,
                node,
                parent,
            } => write!(
                formatter,
                "semantic artifact node {node:?} in '{file_name}' has invalid parent {parent:?}"
            ),
            Self::ForeignNode { file_name, node } => write!(
                formatter,
                "semantic artifact node {node:?} does not belong to Program source '{file_name}'"
            ),
        }
    }
}

impl Error for ArtifactWalkError {}

fn source_files<'a>(
    case: &'a Case,
    program: &'a Program,
) -> impl Iterator<Item = (usize, &'a Unit, &'a SourceFile)> + 'a {
    let mut order = (0..case.units.len()).collect::<Vec<_>>();
    let config_path = project_config_unit(case).map(|(path, _)| path);
    // The pinned compiler runner writes toBeCompiled, then otherFiles. Both
    // groups retain fixture order, independent of the Program's load order.
    if let Some(config) = pinned_project_config(case) {
        let roots = project_root_unit_indices(case, &config);
        order.sort_by_key(|index| !roots.contains(index));
    } else if config_path.is_none()
        && (case
            .directive_values("noImplicitReferences")
            .last()
            .is_some_and(|value| !value.is_empty())
            || case.units.last().is_some_and(unit_uses_implicit_references))
        && !order.is_empty()
    {
        order.rotate_right(1);
    }

    order.into_iter().filter_map(move |index| {
        let unit = &case.units[index];
        let file_name = virtual_unit_path(case, unit, index);
        if config_path.as_deref() == Some(file_name.as_str()) {
            return None;
        }
        // Only loaded fixture files have sections. Libraries loaded from the
        // compiler or harness filesystem do not belong to this list.
        program
            .source_file(&file_name)
            .map(|source| (index, unit, source))
    })
}

pub(crate) fn walk_program(
    case: &Case,
    program: &Program,
) -> Result<SemanticArtifactWalk, ArtifactWalkError> {
    let mut result = SemanticArtifactWalk::default();
    for (_, _, source) in source_files(case, program) {
        walk_source(source, SemanticArtifactKind::Types, &mut result.types)?;
        walk_source(source, SemanticArtifactKind::Symbols, &mut result.symbols)?;
    }
    Ok(result)
}

pub(crate) fn render_program(
    case: &Case,
    program: &Program,
    queries: &mut CanonicalProgramQueries<'_>,
    has_fixture_diagnostics: bool,
) -> Result<GeneratedSemanticArtifacts, ArtifactWalkError> {
    let walk = walk_program(case, program)?;
    let has_diagnostics = has_fixture_diagnostics || queries.has_diagnostics();
    let types = render_baseline(
        case,
        program,
        queries,
        SemanticArtifactKind::Types,
        &walk.types,
        has_diagnostics,
    );
    let symbols = render_baseline(
        case,
        program,
        queries,
        SemanticArtifactKind::Symbols,
        &walk.symbols,
        has_diagnostics,
    );
    Ok(GeneratedSemanticArtifacts {
        walk,
        types,
        symbols,
    })
}

fn render_baseline(
    case: &Case,
    program: &Program,
    queries: &mut CanonicalProgramQueries<'_>,
    kind: SemanticArtifactKind,
    nodes: &[NodeRef],
    has_diagnostics: bool,
) -> Result<String, String> {
    let mut sections = String::new();
    for (index, unit, source) in source_files(case, program) {
        let lines = nodes
            .iter()
            .copied()
            .filter(|node| node.file == source.id)
            .map(|node| artifact_line(program, queries, source, node, kind, has_diagnostics))
            .map(|result| result.map(|result| result.line))
            .filter_map(Result::transpose)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| error.to_string())?;
        render_source_section(
            &mut sections,
            &baseline_unit_name(case, unit, index),
            unit.source_text.as_scannable_str(),
            &lines,
        );
    }

    if sections.is_empty() {
        return Ok("<no content>".to_owned());
    }

    Ok(format!(
        "//// [{}] ////\r\n\r\n{}",
        baseline_header(case),
        remove_test_path_prefixes(&sections),
    ))
}

fn artifact_line(
    program: &Program,
    queries: &mut CanonicalProgramQueries<'_>,
    source: &SourceFile,
    reference: NodeRef,
    kind: SemanticArtifactKind,
    has_diagnostics: bool,
) -> Result<QueriedArtifactLine, ArtifactRenderError> {
    let node = program.node(reference).ok_or_else(|| {
        ArtifactRenderError::invariant(
            "INV.ARTIFACT.NODE",
            format!("semantic baseline references foreign node {reference:?}"),
        )
    })?;
    let start = usize::try_from(node.range.start.get()).map_err(|_| {
        ArtifactRenderError::invariant(
            "INV.ARTIFACT.RANGE",
            format!("semantic baseline position exceeds usize at {reference:?}"),
        )
    })?;
    let end = usize::try_from(node.range.end.get()).map_err(|_| {
        ArtifactRenderError::invariant(
            "INV.ARTIFACT.RANGE",
            format!("semantic baseline position exceeds usize at {reference:?}"),
        )
    })?;
    let source_text = source
        .source_text
        .get(start..end)
        .ok_or_else(|| {
            ArtifactRenderError::invariant(
                "INV.ARTIFACT.RANGE",
                format!("semantic baseline node {reference:?} has an invalid source range"),
            )
        })?
        .replace("\r\n", "")
        .replace('\n', "");

    let (value, identity) = match kind {
        SemanticArtifactKind::Types => {
            let type_id = queries.get_type_at_location(reference).map_err(|error| {
                ArtifactRenderError::query("semantic .types query failed", &source.file_name, error)
            })?;
            let intrinsic_name = if !has_diagnostics
                && uses_intrinsic_any_name(source, reference.node, node, &source_text)
            {
                queries
                    .intrinsic_any_name(type_id)
                    .map_err(|error| ArtifactRenderError {
                        class: CanonicalProgramCheckError::SourceCheck {
                            file_name: source.file_name.clone(),
                            error: error.into(),
                        }
                        .failure_class(),
                        detail: format!("semantic intrinsic type query failed: {error}"),
                    })?
            } else {
                None
            };
            let value = if let Some(name) = intrinsic_name {
                name.to_owned()
            } else {
                queries
                    .type_to_string_at_location_with_flags(
                        type_id,
                        node.parent.map_or(reference, |parent| {
                            NodeRef::new(reference.arena, reference.file, parent)
                        }),
                        CanonicalTypeFormatFlags::NO_TRUNCATION
                            | CanonicalTypeFormatFlags::ALLOW_UNIQUE_ES_SYMBOL_TYPE,
                    )
                    .map_err(|error| ArtifactRenderError {
                        class: CanonicalProgramCheckError::SourceCheck {
                            file_name: source.file_name.clone(),
                            error: error.into(),
                        }
                        .failure_class(),
                        detail: format!("semantic .types formatting failed: {error}"),
                    })?
            };
            (value, ArtifactIdentity::Type(type_id))
        }
        SemanticArtifactKind::Symbols => {
            let Some(symbol) = queries.get_symbol_at_location(reference).map_err(|error| {
                ArtifactRenderError::query(
                    "semantic .symbols query failed",
                    &source.file_name,
                    error,
                )
            })?
            else {
                return Ok(QueriedArtifactLine {
                    line: None,
                    identity: ArtifactIdentity::Symbol(None),
                });
            };
            (
                render_symbol(
                    program,
                    queries,
                    &source.file_name,
                    symbol,
                    node.parent.map_or(reference, |parent| {
                        NodeRef::new(reference.arena, reference.file, parent)
                    }),
                )?,
                ArtifactIdentity::Symbol(Some(symbol)),
            )
        }
    };

    Ok(QueriedArtifactLine {
        line: Some(ArtifactLine {
            line: ecma_line_and_utf16_column(&source.source_text, start).0,
            source_text,
            value,
        }),
        identity,
    })
}

fn uses_intrinsic_any_name(
    source: &SourceFile,
    node_id: NodeId,
    node: &Node,
    source_text: &str,
) -> bool {
    let Some(parent) = node
        .parent
        .and_then(|parent| source.parse.arena.get(parent))
    else {
        return true;
    };
    if is_jsx_tag(node_id, Some(parent))
        && (source_text
            .as_bytes()
            .first()
            .is_some_and(u8::is_ascii_lowercase)
            || source_text.contains('-'))
    {
        return false;
    }
    match &parent.data {
        NodeData::BindingElement(_)
        | NodeData::PropertyAccessExpression(_)
        | NodeData::QualifiedName(_)
        | NodeData::MetaProperty(_) => false,
        NodeData::ModuleDeclaration(module) if module.keyword == SyntaxKind::GlobalKeyword => false,
        NodeData::LabeledStatement(statement) => statement.label != node_id,
        NodeData::BreakStatement(statement) => statement.label != Some(node_id),
        NodeData::ContinueStatement(statement) => statement.label != Some(node_id),
        NodeData::ImportSpecifier(specifier) => {
            specifier.name != node_id && specifier.property_name != Some(node_id)
        }
        NodeData::ExportSpecifier(specifier) => {
            specifier.name != node_id && specifier.property_name != Some(node_id)
        }
        NodeData::ImportClause(clause) => clause.name != Some(node_id),
        NodeData::ImportEqualsDeclaration(declaration) => declaration.name != node_id,
        NodeData::ExportAssignment(assignment) => assignment.expression != node_id,
        _ => true,
    }
}

fn render_symbol(
    program: &Program,
    queries: &mut CanonicalProgramQueries<'_>,
    file_name: &str,
    symbol: ts_compiler::CanonicalSymbolId,
    enclosing: NodeRef,
) -> Result<String, ArtifactRenderError> {
    let name = queries
        .symbol_to_string_at_location(symbol, enclosing)
        .map_err(|error| {
            ArtifactRenderError::query("semantic .symbols formatting failed", file_name, error)
        })?;
    let declarations = queries.get_symbol_declarations(symbol).map_err(|error| {
        ArtifactRenderError::query("semantic .symbols declarations failed", file_name, error)
    })?;
    let mut result = format!("Symbol({name}");
    for (index, declaration) in declarations.iter().enumerate() {
        if index == 5 {
            write!(result, " ... and {} more", declarations.len() - index)
                .expect("writing to a String cannot fail");
            break;
        }
        let source = program.source_file_by_id(declaration.file).ok_or_else(|| {
            ArtifactRenderError::invariant(
                "INV.ARTIFACT.DECLARATION",
                format!("semantic .symbols declaration has no source file: {declaration:?}"),
            )
        })?;
        let record = program.node(*declaration).ok_or_else(|| {
            ArtifactRenderError::invariant(
                "INV.ARTIFACT.DECLARATION",
                format!("semantic .symbols declaration is foreign to its Program: {declaration:?}"),
            )
        })?;
        let file_name = source
            .file_name
            .rsplit(['/', '\\'])
            .next()
            .unwrap_or(&source.file_name);
        if source.is_default_library || is_default_library_file(file_name) {
            write!(result, ", Decl({file_name}, --, --)").expect("writing to a String cannot fail");
            continue;
        }

        let position = declaration_full_start(
            &source.source_text,
            usize::try_from(record.range.start.get()).map_err(|_| {
                ArtifactRenderError::invariant(
                    "INV.ARTIFACT.RANGE",
                    format!(
                        "semantic .symbols declaration position exceeds usize: {declaration:?}"
                    ),
                )
            })?,
        );
        let (line, column) = ecma_line_and_utf16_column(&source.source_text, position);
        write!(result, ", Decl({file_name}, {line}, {column})")
            .expect("writing to a String cannot fail");
    }
    result.push(')');
    Ok(result)
}

fn declaration_full_start(source: &str, position: usize) -> usize {
    let mut start = position.min(source.len());
    loop {
        start = source[..start]
            .trim_end_matches(|character: char| {
                character.is_whitespace() || character == '\u{feff}'
            })
            .len();

        if source[..start].ends_with("*/")
            && let Some(comment_start) = source[..start - 2].rfind("/*")
        {
            start = comment_start;
            continue;
        }

        let line_start = source[..start]
            .rfind(['\r', '\n', '\u{2028}', '\u{2029}'])
            .map_or(0, |line_break| {
                line_break
                    + source[line_break..]
                        .chars()
                        .next()
                        .map_or(0, char::len_utf8)
            });
        if let Some(comment_start) = line_comment_start(&source[line_start..start]) {
            start = line_start + comment_start;
            continue;
        }

        return start;
    }
}

fn line_comment_start(line: &str) -> Option<usize> {
    let bytes = line.as_bytes();
    let mut index = 0;
    let mut quote = None;
    while index < bytes.len() {
        let byte = bytes[index];
        if let Some(delimiter) = quote {
            if byte == b'\\' {
                index += usize::from(index + 1 < bytes.len());
            } else if byte == delimiter {
                quote = None;
            }
        } else if matches!(byte, b'\'' | b'"' | b'`') {
            quote = Some(byte);
        } else if byte == b'/' && bytes.get(index + 1) == Some(&b'/') {
            return Some(index);
        } else if byte == b'/'
            && bytes.get(index + 1) == Some(&b'*')
            && let Some(end) = line[index + 2..].find("*/")
        {
            index += end + 3;
        }
        index += 1;
    }
    None
}

fn ecma_line_and_utf16_column(source: &str, position: usize) -> (usize, usize) {
    let prefix = &source[..position.min(source.len())];
    let mut line = 0;
    let mut column = 0;
    let mut previous_carriage_return = false;
    for character in prefix.chars() {
        match character {
            '\r' => {
                line += 1;
                column = 0;
                previous_carriage_return = true;
            }
            '\n' if previous_carriage_return => previous_carriage_return = false,
            '\n' | '\u{2028}' | '\u{2029}' => {
                line += 1;
                column = 0;
                previous_carriage_return = false;
            }
            _ => {
                column += character.len_utf16();
                previous_carriage_return = false;
            }
        }
    }
    (line, column)
}

fn render_source_section(output: &mut String, name: &str, source: &str, results: &[ArtifactLine]) {
    write!(output, "=== {name} ===\r\n").expect("writing to a String cannot fail");
    let code_lines = source
        .split(['\n', '\r', '\u{2028}', '\u{2029}'])
        .collect::<Vec<_>>();
    let mut last_written = None;
    for result in results {
        let line = result.line.min(code_lines.len().saturating_sub(1));
        match last_written {
            None => append_code_lines(output, &code_lines[..=line]),
            Some(previous) if previous != line => {
                if !suppresses_blank_separator(code_lines.get(previous + 1).copied()) {
                    output.push_str("\r\n");
                }
                append_code_lines(output, &code_lines[previous + 1..=line]);
            }
            Some(_) => {}
        }
        last_written = Some(line);
        write!(output, ">{} : {}\r\n", result.source_text, result.value)
            .expect("writing to a String cannot fail");
    }

    let next = last_written.map_or(0, |line| line + 1);
    if next < code_lines.len() {
        if !suppresses_blank_separator(code_lines.get(next).copied()) {
            output.push_str("\r\n");
        }
        output.push_str(&code_lines[next..].join("\r\n"));
    }
    output.push_str("\r\n");
}

fn append_code_lines(output: &mut String, lines: &[&str]) {
    output.push_str(&lines.join("\r\n"));
    output.push_str("\r\n");
}

fn suppresses_blank_separator(line: Option<&str>) -> bool {
    line.is_some_and(|line| {
        let trimmed = line.trim();
        trimmed.is_empty() || matches!(trimmed, "{" | "|" | "}")
    })
}

fn baseline_header(case: &Case) -> String {
    let path = case.path.to_string_lossy().replace('\\', "/");
    if let Some((_, relative)) = path.rsplit_once("/_submodules/TypeScript/") {
        return relative.to_owned();
    }
    if let Some((_, relative)) = path.rsplit_once("/testdata/") {
        return relative.to_owned();
    }
    path.strip_prefix("_submodules/TypeScript/")
        .or_else(|| path.strip_prefix("testdata/"))
        .unwrap_or(&path)
        .to_owned()
}

fn walk_source(
    source: &SourceFile,
    artifact: SemanticArtifactKind,
    results: &mut Vec<NodeRef>,
) -> Result<(), ArtifactWalkError> {
    let arena = &source.parse.arena;
    let mut pending = vec![source.parse.source_file];
    let mut children = Vec::new();

    while let Some(node_id) = pending.pop() {
        let node = node(source, node_id)?;
        let parent = node
            .parent
            .map(|parent| parent_node(source, node_id, parent))
            .transpose()?;
        if !should_traverse_reparsed(node_id, node, parent) {
            continue;
        }

        if should_include_reparsed(node, parent)
            && is_artifact_candidate(arena, node_id, node, parent)
            && match artifact {
                SemanticArtifactKind::Types => types::includes(arena, node_id, node, parent),
                SemanticArtifactKind::Symbols => symbols::includes(node),
            }
        {
            let reference =
                source
                    .node_ref(node_id)
                    .ok_or_else(|| ArtifactWalkError::ForeignNode {
                        file_name: source.file_name.clone(),
                        node: node_id,
                    })?;
            results.push(reference);
        }

        children.clear();
        node.for_each_child(|child| children.push(child));
        pending.extend(children.iter().rev().copied());
    }

    Ok(())
}

fn node(source: &SourceFile, node_id: NodeId) -> Result<&Node, ArtifactWalkError> {
    source
        .parse
        .arena
        .get(node_id)
        .ok_or_else(|| ArtifactWalkError::MissingNode {
            file_name: source.file_name.clone(),
            node: node_id,
        })
}

fn parent_node(
    source: &SourceFile,
    node_id: NodeId,
    parent: NodeId,
) -> Result<&Node, ArtifactWalkError> {
    source
        .parse
        .arena
        .get(parent)
        .ok_or_else(|| ArtifactWalkError::MissingParent {
            file_name: source.file_name.clone(),
            node: node_id,
            parent,
        })
}

fn should_traverse_reparsed(node_id: NodeId, node: &Node, parent: Option<&Node>) -> bool {
    if node.flags.0 & NodeFlags::REPARSED.0 == 0
        || matches!(
            node.kind,
            SyntaxKind::AsExpression | SyntaxKind::SatisfiesExpression
        )
    {
        return true;
    }

    parent.is_some_and(|parent| match &parent.data {
        NodeData::AsExpression(expression) => expression.expression == node_id,
        NodeData::SatisfiesExpression(expression) => expression.expression == node_id,
        _ => false,
    })
}

fn should_include_reparsed(node: &Node, parent: Option<&Node>) -> bool {
    node.flags.0 & NodeFlags::REPARSED.0 == 0
        || parent.is_some_and(|parent| {
            matches!(
                parent.kind,
                SyntaxKind::AsExpression | SyntaxKind::SatisfiesExpression
            )
        })
}

pub(super) fn is_artifact_candidate(
    arena: &NodeArena,
    node_id: NodeId,
    node: &Node,
    parent: Option<&Node>,
) -> bool {
    node.kind == SyntaxKind::Identifier
        || is_expression_node(arena, node_id, node, parent)
        || (!matches!(
            node.kind,
            SyntaxKind::ObjectBindingPattern | SyntaxKind::ArrayBindingPattern
        ) && parent.is_some_and(|parent| declaration_name(parent) == Some(node_id)))
}

fn is_expression_node(
    arena: &NodeArena,
    node_id: NodeId,
    node: &Node,
    parent: Option<&Node>,
) -> bool {
    match node.kind {
        SyntaxKind::SuperKeyword
        | SyntaxKind::NullKeyword
        | SyntaxKind::TrueKeyword
        | SyntaxKind::FalseKeyword
        | SyntaxKind::RegularExpressionLiteral
        | SyntaxKind::ArrayLiteralExpression
        | SyntaxKind::ObjectLiteralExpression
        | SyntaxKind::PropertyAccessExpression
        | SyntaxKind::ElementAccessExpression
        | SyntaxKind::CallExpression
        | SyntaxKind::NewExpression
        | SyntaxKind::TaggedTemplateExpression
        | SyntaxKind::AsExpression
        | SyntaxKind::TypeAssertionExpression
        | SyntaxKind::SatisfiesExpression
        | SyntaxKind::NonNullExpression
        | SyntaxKind::ParenthesizedExpression
        | SyntaxKind::FunctionExpression
        | SyntaxKind::ClassExpression
        | SyntaxKind::ArrowFunction
        | SyntaxKind::VoidExpression
        | SyntaxKind::DeleteExpression
        | SyntaxKind::TypeOfExpression
        | SyntaxKind::PrefixUnaryExpression
        | SyntaxKind::PostfixUnaryExpression
        | SyntaxKind::BinaryExpression
        | SyntaxKind::ConditionalExpression
        | SyntaxKind::SpreadElement
        | SyntaxKind::TemplateExpression
        | SyntaxKind::OmittedExpression
        | SyntaxKind::JsxElement
        | SyntaxKind::JsxSelfClosingElement
        | SyntaxKind::JsxFragment
        | SyntaxKind::YieldExpression
        | SyntaxKind::AwaitExpression => true,
        SyntaxKind::ExpressionWithTypeArguments => {
            parent.is_none_or(|parent| parent.kind != SyntaxKind::HeritageClause)
        }
        SyntaxKind::MetaProperty => parent.is_none_or(|parent| {
            !matches!(&parent.data, NodeData::CallExpression(call) if call.expression == node_id)
        }),
        SyntaxKind::PrivateIdentifier => parent.is_some_and(|parent| {
            matches!(
                &parent.data,
                NodeData::BinaryExpression(binary)
                    if binary.left == node_id
                        && arena
                            .get(binary.operator_token)
                            .is_some_and(|operator| operator.kind == SyntaxKind::InKeyword)
            )
        }),
        SyntaxKind::QualifiedName => is_qualified_expression(arena, node_id, parent),
        SyntaxKind::Identifier => {
            parent.is_some_and(|parent| parent.kind == SyntaxKind::TypeQuery)
                || is_jsx_tag(node_id, parent)
                || parent.is_some_and(|parent| in_expression_context(arena, node_id, parent))
        }
        SyntaxKind::NumericLiteral
        | SyntaxKind::BigIntLiteral
        | SyntaxKind::StringLiteral
        | SyntaxKind::NoSubstitutionTemplateLiteral
        | SyntaxKind::ThisKeyword => {
            parent.is_some_and(|parent| in_expression_context(arena, node_id, parent))
        }
        _ => false,
    }
}

fn is_qualified_expression<'arena>(
    arena: &'arena NodeArena,
    mut node_id: NodeId,
    mut parent: Option<&'arena Node>,
) -> bool {
    while let Some(current_parent) = parent {
        if current_parent.kind != SyntaxKind::QualifiedName {
            return current_parent.kind == SyntaxKind::TypeQuery
                || is_jsx_tag(node_id, Some(current_parent));
        }
        let Some(parent_id) = current_parent.parent else {
            return false;
        };
        node_id = parent_id;
        parent = arena.get(parent_id);
    }
    false
}

fn is_jsx_tag(node_id: NodeId, parent: Option<&Node>) -> bool {
    parent.is_some_and(|parent| match &parent.data {
        NodeData::JsxOpeningElement(element) => element.tag_name == node_id,
        NodeData::JsxClosingElement(element) => element.tag_name == node_id,
        NodeData::JsxSelfClosingElement(element) => element.tag_name == node_id,
        _ => false,
    })
}

fn in_expression_context(arena: &NodeArena, node_id: NodeId, parent: &Node) -> bool {
    match &parent.data {
        NodeData::VariableDeclaration(data) => data.initializer == Some(node_id),
        NodeData::ParameterDeclaration(data) => data.initializer == Some(node_id),
        NodeData::PropertyDeclaration(data) => data.initializer == Some(node_id),
        NodeData::PropertySignatureDeclaration(data) => data.initializer == node_id,
        NodeData::EnumMember(data) => data.initializer == Some(node_id),
        NodeData::PropertyAssignment(data) => data.initializer == node_id,
        NodeData::BindingElement(data) => data.initializer == Some(node_id),
        NodeData::ExpressionStatement(data) => data.expression == node_id,
        NodeData::IfStatement(data) => data.expression == node_id,
        NodeData::DoStatement(data) => data.expression == node_id,
        NodeData::WhileStatement(data) => data.expression == node_id,
        NodeData::ReturnStatement(data) => data.expression == Some(node_id),
        NodeData::WithStatement(data) => data.expression == node_id,
        NodeData::SwitchStatement(data) => data.expression == node_id,
        NodeData::CaseOrDefaultClause(data) => data.expression == node_id,
        NodeData::ThrowStatement(data) => data.expression == node_id,
        NodeData::TypeAssertion(data) => data.expression == node_id,
        NodeData::AsExpression(data) => data.expression == node_id,
        NodeData::SatisfiesExpression(data) => data.expression == node_id,
        NodeData::TemplateSpan(data) => data.expression == node_id,
        NodeData::ComputedPropertyName(data) => data.expression == node_id,
        NodeData::ForStatement(data) => {
            data.condition == Some(node_id)
                || data.incrementor == Some(node_id)
                || (data.initializer == Some(node_id)
                    && arena
                        .get(node_id)
                        .is_some_and(|node| node.kind != SyntaxKind::VariableDeclarationList))
        }
        NodeData::ForInOrOfStatement(data) => {
            data.expression == node_id
                || (data.initializer == node_id
                    && arena
                        .get(node_id)
                        .is_some_and(|node| node.kind != SyntaxKind::VariableDeclarationList))
        }
        NodeData::Decorator(_)
        | NodeData::JsxExpression(_)
        | NodeData::JsxSpreadAttribute(_)
        | NodeData::SpreadAssignment(_) => true,
        NodeData::ExpressionWithTypeArguments(data) => {
            data.expression == node_id && !types::is_part_of_type_node(arena, node_id, parent)
        }
        NodeData::ShorthandPropertyAssignment(data) => {
            data.object_assignment_initializer == Some(node_id)
        }
        _ => parent
            .parent
            .and_then(|parent_id| arena.get(parent_id))
            .is_some_and(|grandparent| {
                is_expression_node(arena, node_id, parent, Some(grandparent))
            }),
    }
}

pub(super) fn declaration_name(parent: &Node) -> Option<NodeId> {
    match &parent.data {
        NodeData::BindingElement(data) => data.name,
        NodeData::ClassDeclaration(data) => data.name,
        NodeData::ClassExpression(data) => data.name,
        NodeData::EnumDeclaration(data) => Some(data.name),
        NodeData::EnumMember(data) => Some(data.name),
        NodeData::ExportSpecifier(data) => Some(data.name),
        NodeData::FunctionDeclaration(data) => data.name,
        NodeData::FunctionExpression(data) => data.name,
        NodeData::GetAccessorDeclaration(data) => Some(data.name),
        NodeData::ImportClause(data) => data.name,
        NodeData::ImportEqualsDeclaration(data) => Some(data.name),
        NodeData::ImportSpecifier(data) => Some(data.name),
        NodeData::InterfaceDeclaration(data) => Some(data.name),
        NodeData::JsxAttribute(data) => Some(data.name),
        NodeData::MethodDeclaration(data) => Some(data.name),
        NodeData::MethodSignatureDeclaration(data) => Some(data.name),
        NodeData::ModuleDeclaration(data) => Some(data.name),
        NodeData::NamedTupleMember(data) => Some(data.name),
        NodeData::NamespaceExport(data) => Some(data.name),
        NodeData::NamespaceExportDeclaration(data) => Some(data.name),
        NodeData::NamespaceImport(data) => Some(data.name),
        NodeData::ParameterDeclaration(data) => Some(data.name),
        NodeData::PropertyAssignment(data) => Some(data.name),
        NodeData::PropertyDeclaration(data) => Some(data.name),
        NodeData::PropertySignatureDeclaration(data) => Some(data.name),
        NodeData::SetAccessorDeclaration(data) => Some(data.name),
        NodeData::ShorthandPropertyAssignment(data) => Some(data.name),
        NodeData::TypeAliasDeclaration(data) => Some(data.name),
        NodeData::TypeParameterDeclaration(data) => Some(data.name),
        NodeData::VariableDeclaration(data) => Some(data.name),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use ts_ast::{NodeData, SyntaxKind};
    use ts_compiler::Program;
    use ts_options::CompilerOptions;
    use ts_vfs::{FileSystem, MemoryFileSystem};

    use crate::{Case, fixture_case_sensitive, virtual_harness_path, virtual_unit_path};

    use super::{
        SemanticArtifactWalk, declaration_full_start, ecma_line_and_utf16_column, render_program,
        source_files, walk_program,
    };

    fn fixture_filesystem(case: &Case) -> MemoryFileSystem {
        let filesystem = MemoryFileSystem::new(fixture_case_sensitive(case));
        for (index, unit) in case.units.iter().enumerate() {
            filesystem
                .write_file(
                    &virtual_unit_path(case, unit, index),
                    unit.source_text.as_scannable_str(),
                )
                .unwrap();
        }
        filesystem
    }

    fn assert_walk_file_order(program: &Program, walk: &SemanticArtifactWalk, paths: &[String]) {
        let expected = paths
            .iter()
            .map(|path| program.source_file(path).unwrap().id)
            .collect::<Vec<_>>();
        for nodes in [&walk.types, &walk.symbols] {
            let mut actual = nodes.iter().map(|node| node.file).collect::<Vec<_>>();
            actual.dedup();
            assert_eq!(actual, expected);
        }
    }

    fn assert_rendered_file_order(case: &Case, roots: &[&str], expected: &[&str]) {
        let filesystem = fixture_filesystem(case);
        let roots = roots
            .iter()
            .map(|path| virtual_harness_path(case, path))
            .collect::<Vec<_>>();
        let expected_paths = expected
            .iter()
            .map(|path| virtual_harness_path(case, path))
            .collect::<Vec<_>>();
        let (_, artifacts) = Program::try_new_with_canonical_checker_and_queries(
            &filesystem,
            "/.src",
            &roots,
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
            |program, queries| {
                render_program(case, program, queries, false).inspect(|artifacts| {
                    assert_walk_file_order(program, &artifacts.walk, &expected_paths);
                })
            },
        )
        .unwrap();
        let artifacts = artifacts.unwrap().unwrap();
        let expected = expected
            .iter()
            .map(|name| format!("=== {name} ==="))
            .collect::<Vec<_>>();
        for baseline in [artifacts.types, artifacts.symbols] {
            let baseline = baseline.unwrap();
            let sections = baseline
                .lines()
                .filter(|line| line.starts_with("=== "))
                .collect::<Vec<_>>();
            assert_eq!(sections, expected);
        }
    }

    #[test]
    fn semantic_artifacts_keep_fixture_order_for_unreferenced_roots() {
        let case = Case::parse(
            "roots.ts",
            concat!(
                "// @filename: second.ts\n",
                "const second = 2;\n",
                "// @filename: first.ts\n",
                "const first = 1;\n",
            ),
        )
        .unwrap();
        assert_rendered_file_order(
            &case,
            &["second.ts", "first.ts"],
            &["second.ts", "first.ts"],
        );
    }

    #[test]
    fn semantic_artifacts_put_implicit_reference_root_before_dependencies() {
        let case = Case::parse(
            "references.ts",
            concat!(
                "// @filename: first.ts\n",
                "const first = 1;\n",
                "// @filename: ignored.ts\n",
                "const ignored = 0;\n",
                "// @filename: second.ts\n",
                "const second = 2;\n",
                "// @filename: entry.ts\n",
                "/// <reference path=\"./second.ts\" />\n",
                "/// <reference path=\"./first.ts\" />\n",
                "const entry = 3;\n",
            ),
        )
        .unwrap();
        assert_rendered_file_order(&case, &["entry.ts"], &["entry.ts", "first.ts", "second.ts"]);
    }

    #[test]
    fn semantic_artifacts_partition_project_roots_in_fixture_order() {
        let case = Case::parse(
            "project.ts",
            concat!(
                "// @noImplicitReferences: true\n",
                "// @filename: /app/dep-a.ts\n",
                "const dependencyA = 1;\n",
                "// @filename: /app/src/second.ts\n",
                "/// <reference path=\"../dep-b.ts\" />\n",
                "const second = 2;\n",
                "// @filename: /app/tsconfig.json\n",
                "{ \"files\": [\"src/first.ts\", \"src/second.ts\"] }\n",
                "// @filename: /app/dep-b.ts\n",
                "const dependencyB = 2;\n",
                "// @filename: /app/src/first.ts\n",
                "/// <reference path=\"../dep-a.ts\" />\n",
                "const first = 1;\n",
            ),
        )
        .unwrap();
        assert_rendered_file_order(
            &case,
            &["/app/src/second.ts", "/app/src/first.ts"],
            &[
                "/app/src/second.ts",
                "/app/src/first.ts",
                "/app/dep-a.ts",
                "/app/dep-b.ts",
            ],
        );
    }

    #[test]
    fn semantic_artifacts_keep_project_membership_before_harness_overrides() {
        let case = Case::parse(
            "projectOverride.ts",
            concat!(
                "// @allowJs: true\n",
                "// @filename: dependency.js\n",
                "export const dependency = 1;\n",
                "// @filename: tsconfig.json\n",
                "{}\n",
                "// @filename: entry.ts\n",
                "import './dependency.js';\n",
                "export const entry = 1;\n",
            ),
        )
        .unwrap();
        let filesystem = fixture_filesystem(&case);
        let program = Program::new_with_options(
            &filesystem,
            "/.src",
            &["/.src/entry.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                allow_js: true,
                allow_js_specified: true,
                ..CompilerOptions::default()
            },
        );
        let paths = [
            "/.src/entry.ts".to_owned(),
            "/.src/dependency.js".to_owned(),
        ];
        assert_eq!(
            source_files(&case, &program)
                .map(|(_, _, source)| &source.file_name)
                .collect::<Vec<_>>(),
            paths.iter().collect::<Vec<_>>(),
        );
        assert_walk_file_order(&program, &walk_program(&case, &program).unwrap(), &paths);
    }

    #[test]
    fn semantic_artifacts_skip_non_fixture_libraries_but_keep_fixture_declarations() {
        let case = Case::parse(
            "libraries.ts",
            concat!(
                "// @filename: lib.fixture.d.ts\n",
                "declare const fixtureValue: number;\n",
                "// @filename: lib.unloaded.d.ts\n",
                "declare const unloaded: number;\n",
                "// @filename: entry.ts\n",
                "/// <reference path=\"./lib.fixture.d.ts\" />\n",
                "/// <reference path=\"/.lib/harness.d.ts\" />\n",
                "const entry = 1;\n",
            ),
        )
        .unwrap();
        let filesystem = fixture_filesystem(&case);
        filesystem
            .write_file(
                "/.lib/harness.d.ts",
                "declare const harnessValue: number;\n",
            )
            .unwrap();
        let program = Program::new_with_options(
            &filesystem,
            "/.src",
            &["/.src/entry.ts".to_owned()],
            CompilerOptions {
                skip_lib_check: true,
                skip_default_lib_check: true,
                ..CompilerOptions::default()
            },
        );
        assert!(
            program
                .source_files()
                .iter()
                .any(|source| source.is_default_library)
        );
        assert!(program.source_file("/.lib/harness.d.ts").is_some());
        assert!(program.source_file("/.src/lib.unloaded.d.ts").is_none());
        assert_eq!(
            source_files(&case, &program)
                .map(|(_, _, source)| source.file_name.as_str())
                .collect::<Vec<_>>(),
            ["/.src/entry.ts", "/.src/lib.fixture.d.ts"],
        );
        assert_walk_file_order(
            &program,
            &walk_program(&case, &program).unwrap(),
            &[
                "/.src/entry.ts".to_owned(),
                "/.src/lib.fixture.d.ts".to_owned(),
            ],
        );
    }

    #[test]
    fn semantic_artifact_walks_exclude_binding_patterns_but_visit_their_children() {
        let case = Case::parse(
            "bindings.ts",
            concat!(
                "const { value, nested: { inner } } = { value: 1, nested: { inner: 2 } };\n",
                "const [first, , ...rest] = [1, 2, 3];\n",
            ),
        )
        .unwrap();
        let filesystem = fixture_filesystem(&case);
        let program = Program::new_with_options(
            &filesystem,
            "/.src",
            &["/.src/bindings.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let walk = walk_program(&case, &program).unwrap();
        for nodes in [&walk.types, &walk.symbols] {
            assert!(nodes.iter().all(|node| {
                !matches!(
                    program.node(*node).unwrap().kind,
                    SyntaxKind::ObjectBindingPattern | SyntaxKind::ArrayBindingPattern
                )
            }));
            for name in ["value", "inner", "first", "rest"] {
                assert!(nodes.iter().any(|node| {
                    matches!(
                        &program.node(*node).unwrap().data,
                        NodeData::Identifier(identifier) if identifier.text == name
                    )
                }));
            }
            assert!(nodes.iter().any(|node| {
                program.node(*node).unwrap().kind == SyntaxKind::ObjectLiteralExpression
            }));
            assert!(nodes.iter().any(|node| {
                program.node(*node).unwrap().kind == SyntaxKind::ArrayLiteralExpression
            }));
        }
    }

    #[test]
    fn semantic_artifact_walks_include_switch_case_literals() {
        let source = concat!(
            "declare const value: 'type';\n",
            "switch (value) {\n",
            "  case 'text': break;\n",
            "  case 1: break;\n",
            "  case 2n: break;\n",
            "  case `template`: break;\n",
            "  default: break;\n",
            "}\n",
        );
        let case = Case::parse("switch.ts", source).unwrap();
        let filesystem = fixture_filesystem(&case);
        let program = Program::new_with_options(
            &filesystem,
            "/.src",
            &["/.src/switch.ts".to_owned()],
            CompilerOptions {
                no_lib: true,
                ..CompilerOptions::default()
            },
        );
        let walk = walk_program(&case, &program).unwrap();
        for nodes in [&walk.types, &walk.symbols] {
            let literals = nodes
                .iter()
                .map(|node| program.node(*node).unwrap())
                .filter(|node| {
                    matches!(
                        node.kind,
                        SyntaxKind::StringLiteral
                            | SyntaxKind::NumericLiteral
                            | SyntaxKind::BigIntLiteral
                            | SyntaxKind::NoSubstitutionTemplateLiteral
                    )
                })
                .map(|node| {
                    &source[usize::try_from(node.range.start.get()).unwrap()
                        ..usize::try_from(node.range.end.get()).unwrap()]
                })
                .collect::<Vec<_>>();
            assert_eq!(literals, ["'text'", "1", "2n", "`template`"]);
        }
    }

    #[test]
    fn declaration_positions_include_leading_line_and_jsdoc_comments() {
        let first = "// upstream issue\n\ntype Thing = string;";
        assert_eq!(
            declaration_full_start(first, first.find("type Thing").unwrap()),
            0
        );

        let previous =
            "const value = 1; // trailing detail\n\n/**\n * docs\n */\nfunction next() {}";
        assert_eq!(
            declaration_full_start(previous, previous.find("function next").unwrap()),
            previous.find(';').unwrap() + 1
        );

        let url = "const address = \"https://example.test\"; // trailing\ninterface Shape {}";
        assert_eq!(
            declaration_full_start(url, url.find("interface Shape").unwrap()),
            url.find(';').unwrap() + 1
        );
    }

    #[test]
    fn declaration_positions_count_supplementary_characters_in_utf16() {
        let source = "const icon = \"😀\"; // comment\n\n/** docs */\nfunction next() {}";
        let start = declaration_full_start(source, source.find("function next").unwrap());
        assert_eq!(start, source.find(';').unwrap() + 1);
        assert_eq!(ecma_line_and_utf16_column(source, start), (0, 18));

        let after_separator = "first\u{2028}😀next";
        let next = after_separator.find("next").unwrap();
        assert_eq!(ecma_line_and_utf16_column(after_separator, next), (1, 2));
    }

    #[test]
    fn clean_jsx_elements_print_their_error_intrinsic_without_changing_tag_any() {
        let source = "const view = <div />;\n";
        let case = Case::parse("view.tsx", source).unwrap();
        let filesystem = MemoryFileSystem::new(true);
        filesystem.write_file("/.src/view.tsx", source).unwrap();
        let options = CompilerOptions {
            no_lib: false,
            no_implicit_any: false,
            no_implicit_any_specified: true,
            strict: false,
            jsx: ts_options::JsxEmit::Preserve,
            ..CompilerOptions::default()
        };
        let (_, artifacts) = Program::try_new_with_canonical_checker_and_queries(
            &filesystem,
            "/.src",
            &["/.src/view.tsx".to_owned()],
            options,
            |program, queries| render_program(&case, program, queries, false),
        )
        .unwrap();
        let artifacts = artifacts.unwrap().unwrap();
        let types = artifacts.types.unwrap();

        assert!(types.contains(">view : error\r\n"), "{types}");
        assert!(types.contains("><div /> : error\r\n"), "{types}");
        assert!(types.contains(">div : any\r\n"), "{types}");
    }

    #[test]
    fn intrinsic_error_display_uses_diagnostics_after_comment_suppression() {
        for (source, no_implicit_any, has_diagnostics, expected) in [
            ("const view = <div />;\n", false, false, "error"),
            ("const view = <div />;\n", true, true, "any"),
            (
                "// @ts-ignore\nconst view = <div />;\n",
                true,
                false,
                "error",
            ),
            (
                "const invalid: number = 'text';\nconst view = <div />;\n",
                false,
                true,
                "any",
            ),
            (
                "declare namespace JSX { interface IntrinsicElements { div: {} } }\nconst view = <div />;\n",
                true,
                false,
                "error",
            ),
        ] {
            let case = Case::parse("view.tsx", source).unwrap();
            let filesystem = fixture_filesystem(&case);
            let (program, result) = Program::try_new_with_canonical_checker_and_queries(
                &filesystem,
                "/.src",
                &["/.src/view.tsx".to_owned()],
                CompilerOptions {
                    no_lib: false,
                    no_implicit_any,
                    no_implicit_any_specified: true,
                    jsx: ts_options::JsxEmit::Preserve,
                    ..CompilerOptions::default()
                },
                |program, queries| {
                    (
                        queries.has_diagnostics(),
                        render_program(&case, program, queries, false),
                    )
                },
            )
            .unwrap();
            let (snapshot, artifacts) = result.unwrap();
            assert_eq!(
                snapshot,
                has_diagnostics,
                "{source}: {:?}",
                program.diagnostics()
            );
            assert_eq!(snapshot, !program.diagnostics().is_empty(), "{source}");
            let types = artifacts.unwrap().types.unwrap();
            assert!(
                types.contains(&format!(">view : {expected}\r\n")),
                "{types}"
            );
            assert!(
                types.contains(&format!("><div /> : {expected}\r\n")),
                "{types}"
            );
        }
    }

    #[test]
    fn evolving_array_targets_keep_their_intrinsic_any_display() {
        let source = "let values = []; values[0] = { foo: 'hi' }; const observed = values;\n";
        let case = Case::parse("array.ts", source).unwrap();
        let filesystem = fixture_filesystem(&case);
        let (program, artifacts) = Program::try_new_with_canonical_checker_and_queries(
            &filesystem,
            "/.src",
            &["/.src/array.ts".to_owned()],
            CompilerOptions {
                no_lib: false,
                strict_null_checks: true,
                strict_null_checks_specified: true,
                no_implicit_any: true,
                no_implicit_any_specified: true,
                ..CompilerOptions::default()
            },
            |program, queries| render_program(&case, program, queries, false),
        )
        .unwrap();
        assert!(
            program.diagnostics().is_empty(),
            "{:?}",
            program.diagnostics()
        );
        let types = artifacts.unwrap().unwrap().types.unwrap();
        assert!(types.contains(">values[0] : any\r\n"), "{types}");
    }

    #[test]
    fn walks_type_and_symbol_candidates_in_source_child_order() {
        let source = "type Alias = string;\nconst value: Alias = 'ok';\n";
        let case = Case::parse("input.ts", source).unwrap();
        let filesystem = MemoryFileSystem::new(true);
        filesystem.write_file("/.src/input.ts", source).unwrap();
        let options = CompilerOptions {
            no_lib: true,
            ..CompilerOptions::default()
        };
        let program = Program::new_with_options(
            &filesystem,
            "/.src",
            &["/.src/input.ts".to_owned()],
            options,
        );

        let walk = walk_program(&case, &program).unwrap();
        let source_file = program.source_file("/.src/input.ts").unwrap();
        let descriptions = |nodes: &[ts_ast::NodeRef]| {
            nodes
                .iter()
                .map(|reference| {
                    let node = source_file.parse.arena.get(reference.node).unwrap();
                    match &node.data {
                        NodeData::Identifier(identifier) => identifier.text.clone(),
                        NodeData::StringLiteral(literal) => format!("'{}'", literal.text),
                        _ => node.kind.as_str().to_owned(),
                    }
                })
                .collect::<Vec<_>>()
        };

        assert_eq!(descriptions(&walk.types), ["Alias", "value", "'ok'"]);
        assert_eq!(
            descriptions(&walk.symbols),
            ["Alias", "value", "Alias", "'ok'"]
        );
        assert!(walk.types.iter().all(|reference| {
            source_file
                .parse
                .arena
                .get(reference.node)
                .is_some_and(|node| node.kind != SyntaxKind::StringKeyword)
        }));
    }
}
