#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fmt::Write as _;
use std::path::Path;

use crate::{
    FieldDef, ListKind, MemberDef, NodeAlias, NodeDef, Schema, StringOrList, rust_type_name,
    snake_case,
};

#[derive(Clone, Debug)]
struct ResolvedField {
    schema_name: String,
    ty: StringOrList,
    optional: bool,
    list: Option<ListKind>,
    no_go: bool,
}

struct AstGenerator<'a> {
    schema: &'a Schema,
    node_names: HashSet<&'a str>,
    base_names: HashSet<&'a str>,
    node_alias_names: HashSet<&'a str>,
    list_alias_names: HashSet<&'a str>,
    instantiation_alias_names: HashSet<&'a str>,
    syntax_node_names: HashSet<&'a str>,
    syntax_kind_names: HashSet<&'a str>,
    kind_alias_names: HashSet<&'a str>,
}

/// Generate arena-oriented Rust AST foundations for every schema node.
///
/// # Errors
///
/// Returns an error when the input is invalid or contains unresolved base,
/// member, alias, or type references.
pub fn generate_ast(json: &str) -> Result<String, String> {
    let schema: Schema = serde_json::from_str(json).map_err(|error| error.to_string())?;
    AstGenerator::new(&schema)?.generate()
}

/// Read an `ast.json` file and generate arena-oriented Rust AST foundations.
///
/// # Errors
///
/// Returns an error when the file cannot be read or generated.
pub fn generate_ast_file(path: &Path) -> Result<String, String> {
    let json = std::fs::read_to_string(path)
        .map_err(|error| format!("failed to read {}: {error}", path.display()))?;
    generate_ast(&json)
}

impl<'a> AstGenerator<'a> {
    fn new(schema: &'a Schema) -> Result<Self, String> {
        let generator = Self {
            schema,
            node_names: schema
                .nodes
                .definitions
                .keys()
                .map(String::as_str)
                .collect(),
            base_names: schema.bases.keys().map(String::as_str).collect(),
            node_alias_names: schema.nodes.aliases.keys().map(String::as_str).collect(),
            list_alias_names: schema
                .nodes
                .list_aliases
                .keys()
                .map(String::as_str)
                .collect(),
            instantiation_alias_names: schema
                .nodes
                .definitions
                .values()
                .flat_map(|node| node.instantiation_aliases.keys())
                .map(String::as_str)
                .collect(),
            syntax_node_names: schema
                .nodes
                .definitions
                .iter()
                .flat_map(|(name, node)| syntax_node_names(name, node))
                .collect(),
            syntax_kind_names: schema
                .kinds
                .elements
                .iter()
                .filter_map(|element| match element {
                    crate::KindElement::Name(name) => Some(name.as_str()),
                    crate::KindElement::Detailed { name, .. } => name.as_deref(),
                })
                .collect(),
            kind_alias_names: schema.kinds.aliases.keys().map(String::as_str).collect(),
        };
        generator.validate()?;
        Ok(generator)
    }

    fn validate(&self) -> Result<(), String> {
        for (name, base) in &self.schema.bases {
            self.validate_extends(name, &base.extends)?;
            self.collect_base_fields(name, &mut Vec::new())?;
            for (field_name, field) in &base.fields {
                self.rust_type(&field.r#type, field.list, field.optional)
                    .map_err(|error| format!("{name}.{field_name}: {error}"))?;
            }
        }
        for (name, node) in &self.schema.nodes.definitions {
            self.validate_extends(name, &node.extends)?;
            self.validate_node_kinds(name, node)?;
            let fields = self.node_fields(name, node)?;
            let mut rust_fields = HashSet::new();
            for field in &fields {
                let rust_name = rust_field_name(&field.schema_name);
                if !rust_fields.insert(rust_name.clone()) {
                    return Err(format!("{name} has duplicate Rust field {rust_name}"));
                }
                self.rust_type(&field.ty, field.list, field.optional)
                    .map_err(|error| format!("{name}.{}: {error}", field.schema_name))?;
            }
            if node.hand_written && name != "SourceFile" {
                return Err(format!("unsupported handwritten node {name}"));
            }
        }
        for (name, alias) in &self.schema.nodes.aliases {
            match alias {
                NodeAlias::Base { base } if !self.base_names.contains(base.as_str()) => {
                    return Err(format!("node alias {name} has unknown base {base}"));
                }
                NodeAlias::Members(members) => {
                    for member in members {
                        if !self.is_node_type(member)
                            && !self.kind_alias_names.contains(member.as_str())
                        {
                            return Err(format!("node alias {name} has unknown member {member}"));
                        }
                    }
                }
                NodeAlias::Base { .. } => {}
            }
        }
        for (name, element) in &self.schema.nodes.list_aliases {
            if !self.is_node_type(element) {
                return Err(format!("list alias {name} has unknown element {element}"));
            }
        }
        Ok(())
    }

    fn validate_node_kinds(&self, name: &str, node: &NodeDef) -> Result<(), String> {
        let kind_member = node
            .members
            .iter()
            .find(|member| matches!(member.name.as_str(), "Kind" | "kind"));
        if let Some(kind) = &node.kind {
            for kind_name in type_names(kind) {
                self.validate_kind_reference(name, kind_name)?;
            }
        } else if node.type_parameters.is_empty()
            && kind_member.is_none()
            && !self.syntax_kind_names.contains(name)
        {
            return Err(format!("node {name} has no matching SyntaxKind"));
        }
        for parameter in &node.type_parameters {
            self.validate_kind_reference(name, &parameter.constraint)?;
        }
        for kind in node.instantiation_aliases.values() {
            self.validate_kind_reference(name, kind)?;
        }
        if let Some(member) = kind_member
            && let Some(kind) = &member.r#type
        {
            for kind_name in type_names(kind) {
                if !node
                    .type_parameters
                    .iter()
                    .any(|parameter| parameter.name == kind_name)
                {
                    self.validate_kind_reference(name, kind_name)?;
                }
            }
        }
        Ok(())
    }

    fn validate_kind_reference(&self, owner: &str, name: &str) -> Result<(), String> {
        let name = strip_syntax_kind(name);
        if self.syntax_kind_names.contains(name) || self.kind_alias_names.contains(name) {
            Ok(())
        } else {
            Err(format!("{owner} references unknown SyntaxKind {name}"))
        }
    }

    fn validate_extends(&self, name: &str, extends: &[String]) -> Result<(), String> {
        for base in extends {
            if !self.base_names.contains(base.as_str()) {
                return Err(format!("{name} extends unknown base {base}"));
            }
        }
        Ok(())
    }

    fn collect_base_fields(
        &self,
        name: &str,
        stack: &mut Vec<String>,
    ) -> Result<BTreeMap<String, ResolvedField>, String> {
        if stack.iter().any(|item| item == name) {
            return Err(format!("cyclic base inheritance involving {name}"));
        }
        let base = self
            .schema
            .bases
            .get(name)
            .ok_or_else(|| format!("unknown base {name}"))?;
        stack.push(name.to_owned());
        let mut fields = BTreeMap::new();
        for parent in &base.extends {
            for (field_name, field) in self.collect_base_fields(parent, stack)? {
                Self::merge_field(name, &mut fields, field_name, field)?;
            }
        }
        stack.pop();
        for (field_name, field) in &base.fields {
            // `noGo` fields describe TypeScript-only overrides. They do not
            // replace an inherited runtime field with the same name.
            if field.no_go {
                continue;
            }
            let resolved = resolved_base_field(field_name, field);
            fields.insert(field_name.clone(), resolved);
        }
        Ok(fields)
    }

    fn merge_field(
        owner: &str,
        fields: &mut BTreeMap<String, ResolvedField>,
        name: String,
        field: ResolvedField,
    ) -> Result<(), String> {
        if let Some(previous) = fields.get(&name) {
            if format!("{:?}", previous.ty) != format!("{:?}", field.ty)
                || previous.list.map(|kind| kind as u8) != field.list.map(|kind| kind as u8)
            {
                return Err(format!("conflicting inherited field {owner}.{name}"));
            }
            return Ok(());
        }
        fields.insert(name, field);
        Ok(())
    }

    fn node_fields(&self, name: &str, node: &NodeDef) -> Result<Vec<ResolvedField>, String> {
        let mut fields = BTreeMap::new();
        for base in &node.extends {
            for (field_name, field) in self.collect_base_fields(base, &mut Vec::new())? {
                Self::merge_field(name, &mut fields, field_name, field)?;
            }
        }
        for member in &node.members {
            if is_header_field(&member.name) {
                continue;
            }
            if member.inherited {
                Self::apply_inherited_member(name, &mut fields, member)?;
            } else {
                let ty = member
                    .r#type
                    .clone()
                    .ok_or_else(|| format!("{name}.{} has no type", member.name))?;
                fields.insert(
                    member.name.clone(),
                    ResolvedField {
                        schema_name: member.name.clone(),
                        ty,
                        optional: member.optional.unwrap_or(false),
                        list: member.list,
                        no_go: member.no_go,
                    },
                );
            }
        }
        fields.remove("Flags");
        Ok(fields.into_values().filter(|field| !field.no_go).collect())
    }

    fn apply_inherited_member(
        node_name: &str,
        fields: &mut BTreeMap<String, ResolvedField>,
        member: &MemberDef,
    ) -> Result<(), String> {
        let Some(field) = fields.get_mut(&member.name) else {
            return Err(format!(
                "{node_name}.{} does not resolve to an inherited base field",
                member.name
            ));
        };
        if let Some(ty) = &member.r#type {
            field.ty.clone_from(ty);
        }
        if let Some(optional) = member.optional {
            field.optional = optional;
        }
        if let Some(list) = member.list {
            field.list = Some(list);
        }
        field.no_go |= member.no_go;
        Ok(())
    }

    fn rust_type(
        &self,
        ty: &StringOrList,
        list: Option<ListKind>,
        optional: bool,
    ) -> Result<String, String> {
        let base = if let Some(list) = list {
            match list {
                ListKind::NodeList => "NodeList".to_owned(),
                ListKind::ModifierList => "ModifierList".to_owned(),
                ListKind::Raw => format!("Vec<{}>", self.scalar_rust_type(ty)?),
            }
        } else {
            self.scalar_rust_type(ty)?
        };
        if optional && !base.starts_with("Option<") {
            Ok(format!("Option<{base}>"))
        } else {
            Ok(base)
        }
    }

    fn scalar_rust_type(&self, ty: &StringOrList) -> Result<String, String> {
        match ty {
            StringOrList::One(name) => self.named_rust_type(name),
            StringOrList::Many(names) => {
                let mapped: BTreeSet<_> = names
                    .iter()
                    .map(|name| self.named_rust_type(name))
                    .collect::<Result<_, _>>()?;
                if mapped.len() == 1 {
                    Ok(mapped.into_iter().next().unwrap())
                } else {
                    Err(format!("union has incompatible Rust types: {mapped:?}"))
                }
            }
        }
    }

    fn named_rust_type(&self, name: &str) -> Result<String, String> {
        let ty = match name {
            "bool" | "boolean" => "bool",
            "int" => "i32",
            "string" => "String",
            "NodeFlags" => "NodeFlags",
            "TokenFlags" => "TokenFlags",
            "ModifierFlags" => "ModifierFlags",
            "SymbolTable" => "SymbolTable",
            "atomic.Uint32" => "u32",
            "any" => "OpaqueValue",
            "*Node" => "Option<NodeId>",
            "*Symbol" => "Option<SymbolId>",
            "*FlowNode" => "Option<FlowNodeId>",
            "Kind" => "SyntaxKind",
            _ if name.starts_with("SyntaxKind.") => "SyntaxKind",
            _ if self.kind_alias_names.contains(name) => "SyntaxKind",
            _ if self.list_alias_names.contains(name) => "NodeList",
            _ if self.is_node_type(name) => "NodeId",
            _ => return Err(format!("unresolved schema type {name}")),
        };
        Ok(ty.to_owned())
    }

    fn is_node_type(&self, name: &str) -> bool {
        name == "Node"
            || self.node_names.contains(name)
            || self.base_names.contains(name)
            || self.node_alias_names.contains(name)
            || self.instantiation_alias_names.contains(name)
            || self.syntax_node_names.contains(name)
    }

    #[allow(clippy::too_many_lines)]
    fn generate(&self) -> Result<String, String> {
        let mut output = String::new();
        writeln!(
            output,
            "// Code generated by tools/ts_ast_codegen. DO NOT EDIT."
        )
        .unwrap();
        writeln!(output).unwrap();
        writeln!(output, "use crate::SyntaxKind;").unwrap();
        writeln!(output, "use ts_core::TextRange;").unwrap();
        writeln!(output).unwrap();
        write_foundations(&mut output);

        for (name, node) in &self.schema.nodes.definitions {
            let rust_name = rust_type_name(name);
            let fields = self.node_fields(name, node)?;
            writeln!(output, "#[derive(Clone, Debug)]").unwrap();
            if fields.is_empty() {
                writeln!(output, "pub struct {rust_name}Data;").unwrap();
            } else {
                writeln!(output, "pub struct {rust_name}Data {{").unwrap();
                for field in fields {
                    writeln!(
                        output,
                        "    pub {}: {},",
                        rust_field_name(&field.schema_name),
                        self.rust_type(&field.ty, field.list, field.optional)?
                    )
                    .unwrap();
                }
                writeln!(output, "}}").unwrap();
            }
            writeln!(output).unwrap();
        }

        writeln!(output, "#[derive(Clone, Debug)]").unwrap();
        writeln!(output, "pub enum NodeData {{").unwrap();
        for name in self.schema.nodes.definitions.keys() {
            let rust_name = rust_type_name(name);
            writeln!(output, "    {rust_name}(Box<{rust_name}Data>),").unwrap();
        }
        writeln!(output, "}}").unwrap();
        writeln!(output).unwrap();
        writeln!(output, "impl NodeData {{").unwrap();
        writeln!(
            output,
            "    pub const SCHEMA_NODE_COUNT: usize = {};",
            self.schema.nodes.definitions.len()
        )
        .unwrap();
        writeln!(
            output,
            "    pub const SCHEMA_BASE_COUNT: usize = {};",
            self.schema.bases.len()
        )
        .unwrap();
        writeln!(
            output,
            "    pub const SCHEMA_NODE_ALIAS_COUNT: usize = {};",
            self.schema.nodes.aliases.len()
        )
        .unwrap();
        writeln!(
            output,
            "    pub const SCHEMA_LIST_ALIAS_COUNT: usize = {};",
            self.schema.nodes.list_aliases.len()
        )
        .unwrap();
        writeln!(output).unwrap();
        writeln!(output, "    #[must_use]").unwrap();
        writeln!(output, "    #[allow(clippy::too_many_lines)]").unwrap();
        writeln!(
            output,
            "    pub const fn schema_name(&self) -> &'static str {{"
        )
        .unwrap();
        writeln!(output, "        match self {{").unwrap();
        for name in self.schema.nodes.definitions.keys() {
            let rust_name = rust_type_name(name);
            writeln!(output, "            Self::{rust_name}(..) => \"{name}\",").unwrap();
        }
        writeln!(output, "        }}").unwrap();
        writeln!(output, "    }}").unwrap();
        writeln!(output, "}}").unwrap();
        writeln!(output).unwrap();

        for name in self.schema.nodes.definitions.keys() {
            writeln!(output, "pub type {}Node = NodeId;", rust_type_name(name)).unwrap();
        }
        for name in self.schema.nodes.aliases.keys() {
            writeln!(output, "pub type {} = NodeId;", rust_type_name(name)).unwrap();
        }
        for name in self.schema.nodes.list_aliases.keys() {
            writeln!(output, "pub type {} = NodeList;", rust_type_name(name)).unwrap();
        }
        Ok(output)
    }
}

fn syntax_node_names<'a>(node_name: &'a str, node: &'a NodeDef) -> Vec<&'a str> {
    let mut names = Vec::new();
    if let Some(kind) = &node.kind {
        names.extend(type_names(kind).map(strip_syntax_kind));
    } else {
        names.push(node_name);
    }
    if let Some(kind_member) = node
        .members
        .iter()
        .find(|member| matches!(member.name.as_str(), "Kind" | "kind"))
        && let Some(kind) = &kind_member.r#type
    {
        names.extend(type_names(kind).map(strip_syntax_kind));
    }
    names
}

fn type_names(ty: &StringOrList) -> impl Iterator<Item = &str> {
    match ty {
        StringOrList::One(name) => std::slice::from_ref(name).iter(),
        StringOrList::Many(names) => names.iter(),
    }
    .map(String::as_str)
}

fn strip_syntax_kind(name: &str) -> &str {
    name.strip_prefix("SyntaxKind.").unwrap_or(name)
}

fn resolved_base_field(name: &str, field: &FieldDef) -> ResolvedField {
    ResolvedField {
        schema_name: name.to_owned(),
        ty: field.r#type.clone(),
        optional: field.optional,
        list: field.list,
        no_go: field.no_go,
    }
}

fn is_header_field(name: &str) -> bool {
    matches!(name, "Kind" | "kind" | "Flags")
}

fn rust_field_name(name: &str) -> String {
    let name = snake_case(name);
    if matches!(
        name.as_str(),
        "as" | "async"
            | "await"
            | "break"
            | "const"
            | "continue"
            | "crate"
            | "dyn"
            | "else"
            | "enum"
            | "extern"
            | "false"
            | "fn"
            | "for"
            | "if"
            | "impl"
            | "in"
            | "let"
            | "loop"
            | "match"
            | "mod"
            | "move"
            | "mut"
            | "pub"
            | "ref"
            | "return"
            | "self"
            | "static"
            | "struct"
            | "super"
            | "trait"
            | "true"
            | "type"
            | "union"
            | "unsafe"
            | "use"
            | "where"
            | "while"
            | "yield"
    ) {
        format!("{name}_")
    } else {
        name
    }
}

#[allow(clippy::too_many_lines)] // One generated foundation block.
fn write_foundations(output: &mut String) {
    output.push_str(
        r#"#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeId(u32);

impl NodeId {
    #[must_use]
    pub const fn new(index: u32) -> Self { Self(index) }

    #[must_use]
    pub const fn index(self) -> usize { self.0 as usize }
}

/// Opaque identity for one node arena allocation.
///
/// Moving an arena preserves its identity. Cloning creates an independent
/// arena with a fresh identity so binding provenance cannot cross clones.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeArenaId(std::num::NonZeroU64);

impl std::fmt::Debug for NodeArenaId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("NodeArenaId")
    }
}

static LAST_NODE_ARENA_ID: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

pub(crate) fn allocate_node_arena_id_from(
    counter: &std::sync::atomic::AtomicU64,
) -> NodeArenaId {
    let previous = counter
        .fetch_update(
            std::sync::atomic::Ordering::Relaxed,
            std::sync::atomic::Ordering::Relaxed,
            |current| current.checked_add(1),
        )
        .unwrap_or_else(|_| panic!("AST node arena identity space exhausted"));
    NodeArenaId(
        std::num::NonZeroU64::new(previous + 1)
            .expect("allocated AST node arena identities are nonzero"),
    )
}

fn allocate_node_arena_id() -> NodeArenaId {
    allocate_node_arena_id_from(&LAST_NODE_ARENA_ID)
}

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct SymbolId(pub u32);

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct FlowNodeId(pub u32);

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct NodeFlags(pub u32);

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct TokenFlags(pub u32);

#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct ModifierFlags(pub u32);

#[derive(Clone, Debug, Default)]
pub struct SymbolTable;

#[derive(Clone, Debug, Default)]
pub struct OpaqueValue;

#[derive(Clone, Debug, Default)]
pub struct NodeList {
    pub range: TextRange,
    pub nodes: Vec<NodeId>,
    pub has_trailing_comma: bool,
}

#[derive(Clone, Debug, Default)]
pub struct ModifierList {
    pub list: NodeList,
    pub flags: ModifierFlags,
}

#[derive(Clone, Debug)]
pub struct Node {
    pub kind: SyntaxKind,
    pub flags: NodeFlags,
    pub range: TextRange,
    pub parent: Option<NodeId>,
    pub data: NodeData,
}

#[derive(Debug)]
pub struct NodeArena {
    id: NodeArenaId,
    nodes: Vec<Node>,
    source_text: Option<String>,
}

impl Clone for NodeArena {
    fn clone(&self) -> Self {
        Self {
            id: allocate_node_arena_id(),
            nodes: self.nodes.clone(),
            source_text: self.source_text.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        self.id = allocate_node_arena_id();
        self.nodes.clone_from(&source.nodes);
        self.source_text.clone_from(&source.source_text);
    }
}

impl Default for NodeArena {
    fn default() -> Self { Self::new() }
}

impl NodeArena {
    /// Creates an empty arena with a fresh, process-local identity.
    ///
    /// # Panics
    ///
    /// Panics if the process has exhausted the arena identity space.
    #[must_use]
    pub fn new() -> Self {
        Self {
            id: allocate_node_arena_id(),
            nodes: Vec::new(),
            source_text: None,
        }
    }

    #[must_use]
    pub const fn id(&self) -> NodeArenaId { self.id }

    pub fn set_source_text(&mut self, source_text: impl Into<String>) {
        self.source_text = Some(source_text.into());
    }

    #[must_use]
    pub fn source_text(&self) -> Option<&str> { self.source_text.as_deref() }

    /// Allocate a node and return its stable arena identifier.
    ///
    /// # Panics
    ///
    /// Panics if the arena contains more than `u32::MAX` nodes.
    pub fn alloc(&mut self, node: Node) -> NodeId {
        let index = u32::try_from(self.nodes.len()).expect("AST node arena exceeds u32::MAX nodes");
        self.nodes.push(node);
        NodeId::new(index)
    }

    #[must_use]
    pub fn get(&self, id: NodeId) -> Option<&Node> { self.nodes.get(id.index()) }

    #[must_use]
    pub fn get_mut(&mut self, id: NodeId) -> Option<&mut Node> { self.nodes.get_mut(id.index()) }

    #[must_use]
    pub fn len(&self) -> usize { self.nodes.len() }

    #[must_use]
    pub fn is_empty(&self) -> bool { self.nodes.is_empty() }

    /// Iterate over nodes in allocation order with their identifiers.
    ///
    /// # Panics
    ///
    /// Panics if the arena invariant limiting it to `u32::MAX` nodes is broken.
    #[must_use]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (NodeId, &Node)> {
        self.nodes.iter().enumerate().map(|(index, node)| {
            let index = u32::try_from(index).expect("AST node arena exceeds u32::MAX nodes");
            (NodeId::new(index), node)
        })
    }
}

"#,
    );
}

#[cfg(test)]
mod tests {
    use super::generate_ast;

    const UPSTREAM_AST: &str = include_str!("../spec/ast.json");

    #[test]
    fn current_schema_emits_every_node_definition() {
        let output = generate_ast(UPSTREAM_AST).unwrap();
        assert!(output.contains("pub struct NodeArenaId(std::num::NonZeroU64);"));
        assert!(output.contains("static LAST_NODE_ARENA_ID:"));
        assert!(output.contains("pub(crate) fn allocate_node_arena_id_from("));
        assert!(output.contains("impl Clone for NodeArena"));
        assert!(output.contains("fn clone_from(&mut self, source: &Self)"));
        assert!(output.contains("id: allocate_node_arena_id(),"));
        assert!(output.contains("pub const SCHEMA_NODE_COUNT: usize = 192;"));
        assert!(output.contains("pub const SCHEMA_BASE_COUNT: usize = 35;"));
        assert!(output.contains("pub const SCHEMA_NODE_ALIAS_COUNT: usize = 72;"));
        assert!(output.contains("pub const SCHEMA_LIST_ALIAS_COUNT: usize = 23;"));
        assert_eq!(output.matches("(Box<").count(), 192);
        assert!(output.contains("pub struct SourceFileData"));
        assert!(output.contains("pub struct JsDocParameterOrPropertyTagData"));
    }

    #[test]
    fn hard_schema_cases_have_resolved_rust_fields() {
        let output = generate_ast(UPSTREAM_AST).unwrap();
        let for_in_or_of = output
            .split("pub struct ForInOrOfStatementData")
            .nth(1)
            .unwrap()
            .split('}')
            .next()
            .unwrap();
        assert!(!for_in_or_of.contains("pub kind:"));
        assert!(output.contains("pub else_statement: Option<NodeId>"));
        assert!(output.contains("pub statements: NodeList"));
        assert!(output.contains("pub modifiers: Option<ModifierList>"));
        assert!(output.contains("pub flow_node: Option<FlowNodeId>"));
        assert!(output.contains("pub type Expression = NodeId;"));
        assert!(output.contains("pub type StatementList = NodeList;"));
    }
}
