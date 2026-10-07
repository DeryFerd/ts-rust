//! Port of Effect-TS/tsgo `internal/layergraph` (`types.go`, `extract.go`,
//! `outline.go`). It models how Effect Layers are composed in source code.
//! It builds directed graphs where nodes represent Layer expressions and
//! edges represent composition relationships (pipe, call, array literal,
//! symbol).
//!
//! PORT: `format.go`, `magic.go`, `mermaidurl.go` and `providers.go` are not
//! ported: only hover and refactors use them.

use crate::effect::graph::{Direction, Graph, NodeIndex};
use crate::effect::typeparser::*;
use crate::gostd::slices::sort_slice;
use crate::prelude::*;

// ---------------------------------------------------------------------------
// types.go
// ---------------------------------------------------------------------------

/// Go `LayerGraphNodeInfo`: holds data for each node in the layer graph.
#[derive(Clone, Debug, Default)]
pub struct LayerGraphNodeInfo {
    /// The AST expression node
    pub node: Node,
    /// The node used for display (e.g. variable name instead of initializer)
    pub display_node: Node,
    /// Parsed Layer type (ROut, E, RIn) or nil
    pub layer_type: Option<Rc<Layer>>,
    /// Individual service types from ROut (unrolled intersection, Never filtered)
    pub provides: Vec<TypeId>,
    /// Provides minus pass-through (types also in Requires)
    pub actual_provides: Vec<TypeId>,
    /// Individual service types from RIn (unrolled intersection, Never filtered)
    pub requires: Vec<TypeId>,
}

/// Go `EdgeRelationship`: the type of relationship between two nodes in the
/// layer graph.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum EdgeRelationship {
    /// Go `EdgeRelationshipCall`
    #[default]
    Call,
    /// Go `EdgeRelationshipPipe`
    Pipe,
    /// Go `EdgeRelationshipArrayLiteral`
    ArrayLiteral,
    /// Go `EdgeRelationshipSymbol`
    Symbol,
}

impl EdgeRelationship {
    /// The Go string value.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            EdgeRelationship::Call => "call",
            EdgeRelationship::Pipe => "pipe",
            EdgeRelationship::ArrayLiteral => "arrayLiteral",
            EdgeRelationship::Symbol => "symbol",
        }
    }
}

/// Go `LayerGraphEdgeInfo`: describes the relationship between two nodes in
/// the layer graph. It is a discriminated union keyed on Relationship.
// PORT: Go's zero `Relationship` is "", which no Go code creates; the port
// has no empty variant.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LayerGraphEdgeInfo {
    /// One of: "call", "pipe", "arrayLiteral", "symbol"
    pub relationship: EdgeRelationship,
    /// Only meaningful for "call" edges (0-based argument position)
    pub argument_index: i32,
    /// Only meaningful for "arrayLiteral" edges (0-based element position)
    pub index: i32,
}

impl LayerGraphEdgeInfo {
    // Go: LayerGraphEdgeInfo.MarshalJSON
    /// Produces JSON matching the reference format, only including fields
    /// relevant to each relationship type:
    ///
    /// ```text
    /// {"relationship":"call","argumentIndex":0}
    /// {"relationship":"pipe"}
    /// {"relationship":"arrayLiteral","index":0}
    /// {"relationship":"symbol"}
    /// ```
    // PORT: the relationship strings need no JSON escaping, so the port
    // writes the text that Go's `json.Marshal` gives.
    #[must_use]
    pub fn marshal_json(&self) -> String {
        match self.relationship {
            EdgeRelationship::Call => format!(
                "{{\"relationship\":\"{}\",\"argumentIndex\":{}}}",
                self.relationship.as_str(),
                self.argument_index
            ),
            EdgeRelationship::ArrayLiteral => format!(
                "{{\"relationship\":\"{}\",\"index\":{}}}",
                self.relationship.as_str(),
                self.index
            ),
            _ => format!("{{\"relationship\":\"{}\"}}", self.relationship.as_str()),
        }
    }
}

/// Go `LayerOutlineGraphNodeInfo`: holds data for nodes in the simplified
/// outline graph.
#[derive(Clone, Debug, Default)]
pub struct LayerOutlineGraphNodeInfo {
    /// The AST node
    pub node: Node,
    /// The node used for display
    pub display_node: Node,
    /// Service types provided
    pub provides: Vec<TypeId>,
    /// Actual (non-pass-through) provides
    pub actual_provides: Vec<TypeId>,
    /// Service types required
    pub requires: Vec<TypeId>,
}

/// Go `LayerMagicNode`: represents a single node in the layer magic result,
/// annotated with flags that determine which Layer.* combinator to use.
#[derive(Clone, Debug, Default)]
pub struct LayerMagicNode {
    /// Whether this node should be merged (provides a target output type)
    pub merges: bool,
    /// Whether this node provides services
    pub provides: bool,
    /// The layer expression AST node
    pub node: Node,
    /// Service types provided
    pub provided_types: Vec<TypeId>,
    /// Actual (non-pass-through) provides
    pub actual_provided_types: Vec<TypeId>,
    /// Service types required
    pub required_types: Vec<TypeId>,
}

/// Go `LayerMagicResult`: holds the output of ConvertOutlineGraphToLayerMagic.
#[derive(Clone, Debug, Default)]
pub struct LayerMagicResult {
    /// Ordered list of layer nodes with merge/provide flags
    pub nodes: Vec<LayerMagicNode>,
    /// Target output types not satisfied by any node
    pub missing_output_types: Vec<TypeId>,
}

/// Go `ProviderRequirerKind`: distinguishes between providers and requirers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ProviderRequirerKind {
    /// Go `ProviderRequirerKindProvided`
    Provided,
    /// Go `ProviderRequirerKindRequired`
    Required,
}

impl ProviderRequirerKind {
    /// The Go string value.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            ProviderRequirerKind::Provided => "provided",
            ProviderRequirerKind::Required => "required",
        }
    }
}

/// Go `ProviderRequirerInfo`: summarizes which leaf layers provide or
/// require a service type.
#[derive(Clone, Debug)]
pub struct ProviderRequirerInfo {
    /// "provided" or "required"
    pub kind: ProviderRequirerKind,
    /// The service type
    pub type_: TypeId,
    /// The leaf nodes that provide/require this type
    pub nodes: Vec<Node>,
    /// Display nodes for those leaves
    pub display_nodes: Vec<Node>,
}

/// Go `ExtractLayerGraphOptions`: controls the behavior of ExtractLayerGraph.
#[derive(Clone, Copy, Debug, Default)]
pub struct ExtractLayerGraphOptions {
    /// Treat array literals [l1, l2] as implicit Layer.mergeAll (default: false)
    pub array_literal_as_merge: bool,
    /// Only explode calls to Layer module APIs (default: false)
    pub explode_only_layer_calls: bool,
    /// How many levels deep to follow identifier references (default: 0)
    pub follow_symbols_depth: i32,
    /// Do not decompose pipe/call/array expressions (default: false)
    pub skip_explode: bool,
}

// ---------------------------------------------------------------------------
// extract.go
// ---------------------------------------------------------------------------

/// Go `workItem`: represents a node to visit in the DFS work queue.
#[derive(Clone, Copy, Debug)]
pub struct WorkItem {
    pub node: Node,
    pub depth: i32,
}

// Go: ExtractLayerGraph
/// Builds a directed graph of Layer composition from the given AST nodes.
/// It performs a DFS with a two-pass approach using an explicit work stack:
///   - First pass: push children for processing
///   - Second pass: link processed children into the graph
pub fn extract_layer_graph(
    tp: &mut TypeParser<'_>,
    nodes: &[Node],
    sf: Node,
    opts: ExtractLayerGraphOptions,
) -> Graph<LayerGraphNodeInfo, LayerGraphEdgeInfo> {
    let mut g: Graph<LayerGraphNodeInfo, LayerGraphEdgeInfo> = Graph::new();
    let mut node_to_graph_index: FxHashMap<Node, NodeIndex> = FxHashMap::default();
    let mut visited_nodes: FxHashMap<Node, bool> = FxHashMap::default();
    let mut node_in_pipe_context: FxHashMap<Node, bool> = FxHashMap::default();
    let mut depth_budget: FxHashMap<Node, i32> = FxHashMap::default();

    // Resolve the Layer module import name for ExplodeOnlyLayerCalls checks.
    let mut layer_module_name = String::new();
    if !opts.skip_explode {
        layer_module_name = find_layer_module_name(sf);
    }

    // Initialize the work stack with the root nodes.
    let mut stack: Vec<WorkItem> = Vec::new();

    fn append_node_to_visit(
        depth_budget: &mut FxHashMap<Node, i32>,
        stack: &mut Vec<WorkItem>,
        n: Node,
        depth: i32,
    ) {
        depth_budget.insert(n, depth);
        stack.push(WorkItem { node: n, depth });
    }
    for &node in nodes {
        append_node_to_visit(
            &mut depth_budget,
            &mut stack,
            node,
            opts.follow_symbols_depth,
        );
    }

    fn add_node(
        g: &mut Graph<LayerGraphNodeInfo, LayerGraphEdgeInfo>,
        node_to_graph_index: &mut FxHashMap<Node, NodeIndex>,
        n: Node,
        info: LayerGraphNodeInfo,
    ) -> NodeIndex {
        let idx = g.add_node(info);
        node_to_graph_index.insert(n, idx);
        idx
    }

    while let Some(item) = stack.pop() {
        // Pop from the stack (LIFO).
        let current = item.node;
        let current_depth = depth_budget.get(&current).copied().unwrap_or(0);
        let in_pipe = |m: &FxHashMap<Node, bool>| m.get(&current).copied().unwrap_or(false);
        let visited = visited_nodes.get(&current).copied().unwrap_or(false);

        // Case 1: Pipe detection
        if !opts.skip_explode {
            if let Some(pipe_result) = tp.parse_pipe_call(current) {
                if !visited {
                    // First pass: push self back, then subject and args.
                    append_node_to_visit(&mut depth_budget, &mut stack, current, current_depth);
                    append_node_to_visit(
                        &mut depth_budget,
                        &mut stack,
                        pipe_result.subject,
                        current_depth,
                    );
                    for &arg in &pipe_result.args {
                        append_node_to_visit(&mut depth_budget, &mut stack, arg, current_depth);
                        node_in_pipe_context.insert(arg, true);
                    }
                    visited_nodes.insert(current, true);
                } else {
                    // Second pass: collect child graph indices.
                    let mut all_children: Vec<Node> =
                        Vec::with_capacity(1 + pipe_result.args.len());
                    all_children.push(pipe_result.subject);
                    all_children.extend(pipe_result.args.iter().copied());

                    let child_indices =
                        collect_child_indices(&all_children, &node_to_graph_index, &g);

                    if child_indices.len() == all_children.len() {
                        // All members are graph nodes — link them sequentially.
                        let mut last_idx: NodeIndex = 0;
                        for (i, &child_idx) in child_indices.iter().enumerate() {
                            if i > 0 {
                                g.add_edge(
                                    child_idx,
                                    last_idx,
                                    LayerGraphEdgeInfo {
                                        relationship: EdgeRelationship::Pipe,
                                        ..Default::default()
                                    },
                                );
                            }
                            last_idx = child_idx;
                        }
                        // Add a node for the pipe call itself, linking to the last child.
                        let info =
                            extract_node_info(tp, current, sf, in_pipe(&node_in_pipe_context));
                        let pipe_idx = add_node(&mut g, &mut node_to_graph_index, current, info);
                        g.add_edge(
                            pipe_idx,
                            last_idx,
                            LayerGraphEdgeInfo {
                                relationship: EdgeRelationship::Pipe,
                                ..Default::default()
                            },
                        );
                    } else {
                        // Not all children are graph nodes — remove partial children and try as leaf.
                        remove_partial_children(&all_children, &mut node_to_graph_index, &mut g);
                        let info =
                            extract_node_info(tp, current, sf, in_pipe(&node_in_pipe_context));
                        if info.layer_type.is_some() {
                            add_node(&mut g, &mut node_to_graph_index, current, info);
                        }
                    }
                }
                continue;
            }
        }

        // Case 2: Call expression
        if !opts.skip_explode && current.kind() == SyntaxKind::CallExpression {
            let call_expr = current;
            let mut should_explode = !opts.explode_only_layer_calls;
            if opts.explode_only_layer_calls {
                if is_layer_module_call(call_expr, &layer_module_name) {
                    should_explode = true;
                }
            }
            if should_explode {
                let args: Vec<Node> = call_expr.arguments().to_vec();
                if !visited {
                    // First pass: push self back, then all arguments.
                    append_node_to_visit(&mut depth_budget, &mut stack, current, current_depth);
                    for &arg in &args {
                        append_node_to_visit(&mut depth_budget, &mut stack, arg, current_depth);
                    }
                    visited_nodes.insert(current, true);
                } else {
                    // Second pass: collect child graph indices.
                    let child_indices = collect_child_indices(&args, &node_to_graph_index, &g);

                    if child_indices.len() == args.len() {
                        // All arguments are graph nodes.
                        let info =
                            extract_node_info(tp, current, sf, in_pipe(&node_in_pipe_context));
                        let call_idx = add_node(&mut g, &mut node_to_graph_index, current, info);
                        for (i, &child_idx) in child_indices.iter().enumerate() {
                            g.add_edge(
                                call_idx,
                                child_idx,
                                LayerGraphEdgeInfo {
                                    relationship: EdgeRelationship::Call,
                                    argument_index: i as i32,
                                    ..Default::default()
                                },
                            );
                        }
                    } else {
                        // Not all arguments are graph nodes.
                        remove_partial_children(&args, &mut node_to_graph_index, &mut g);
                        let info =
                            extract_node_info(tp, current, sf, in_pipe(&node_in_pipe_context));
                        if info.layer_type.is_some() {
                            add_node(&mut g, &mut node_to_graph_index, current, info);
                        }
                    }
                }
                continue;
            }
        }

        // Case 3: Array literal (when ArrayLiteralAsMerge is enabled)
        if !opts.skip_explode
            && opts.array_literal_as_merge
            && current.kind() == SyntaxKind::ArrayLiteralExpression
        {
            let array_expr = current;
            let elements: Vec<Node> = array_expr.elements().to_vec();
            if !visited {
                // First pass: push self back, then all elements.
                append_node_to_visit(&mut depth_budget, &mut stack, current, current_depth);
                for &elem in &elements {
                    append_node_to_visit(&mut depth_budget, &mut stack, elem, current_depth);
                }
                visited_nodes.insert(current, true);
            } else {
                // Second pass: collect child graph indices (doesn't require ALL).
                let child_indices = collect_child_indices(&elements, &node_to_graph_index, &g);
                if !child_indices.is_empty() {
                    let info = extract_node_info(tp, current, sf, in_pipe(&node_in_pipe_context));
                    let array_idx = add_node(&mut g, &mut node_to_graph_index, current, info);
                    for (i, &child_idx) in child_indices.iter().enumerate() {
                        g.add_edge(
                            array_idx,
                            child_idx,
                            LayerGraphEdgeInfo {
                                relationship: EdgeRelationship::ArrayLiteral,
                                index: i as i32,
                                ..Default::default()
                            },
                        );
                    }
                }
            }
            continue;
        }

        // Case 4: Symbol following
        if current_depth > 0 && is_simple_identifier(current) {
            let mut sym = tp.get_symbol_at_location(current);
            if sym.is_some() {
                if tp.checker.sym(sym).flags.intersects(SymbolFlags::ALIAS) {
                    let resolved = tp.checker.skip_alias(sym);
                    if resolved.is_some() {
                        sym = resolved;
                    }
                }
                if tp.checker.sym(sym).declarations.len() == 1 {
                    let decl = tp.checker.sym(sym).declarations[0];
                    let decl_node = get_adjusted_node(decl);
                    if decl_node.is_some() {
                        if !visited {
                            // First pass: push self back, push declaration with decremented depth.
                            append_node_to_visit(
                                &mut depth_budget,
                                &mut stack,
                                current,
                                current_depth,
                            );
                            append_node_to_visit(
                                &mut depth_budget,
                                &mut stack,
                                decl_node,
                                current_depth - 1,
                            );
                            visited_nodes.insert(current, true);
                            continue;
                        }
                        // Second pass: link to declaration if it's in the graph.
                        if let Some(&child_idx) = node_to_graph_index.get(&decl_node) {
                            let info =
                                extract_node_info(tp, current, sf, in_pipe(&node_in_pipe_context));
                            let ident_idx =
                                add_node(&mut g, &mut node_to_graph_index, current, info);
                            g.add_edge(
                                ident_idx,
                                child_idx,
                                LayerGraphEdgeInfo {
                                    relationship: EdgeRelationship::Symbol,
                                    ..Default::default()
                                },
                            );
                            continue;
                        }
                    }
                }
            }
        }

        // Case 5: Leaf node (base case)
        if is_expression(current) {
            let info = extract_node_info(tp, current, sf, in_pipe(&node_in_pipe_context));
            if info.layer_type.is_some() {
                add_node(&mut g, &mut node_to_graph_index, current, info);
            }
        }
    }

    g
}

// Go: extractNodeInfo
/// Computes the LayerGraphNodeInfo for a given AST node.
fn extract_node_info(
    tp: &mut TypeParser<'_>,
    node: Node,
    _sf: Node,
    in_pipe_context: bool,
) -> LayerGraphNodeInfo {
    let mut info = LayerGraphNodeInfo {
        node,
        display_node: get_display_node(node),
        ..Default::default()
    };

    // Get the type of the node.
    // When in a pipe context, resolve the contextual type's return type
    // (the pipe argument is a function whose return type is the Layer).
    let mut t = TypeId::NIL;
    if in_pipe_context && is_expression(node) {
        let contextual_type = tp
            .checker
            .get_contextual_type_exported(node, ContextFlags::NONE);
        if contextual_type.is_some() {
            let call_signatures = tp
                .checker
                .get_signatures_of_type_exported(contextual_type, SignatureKind::CALL);
            if call_signatures.len() == 1 {
                t = tp
                    .checker
                    .get_return_type_of_signature_exported(call_signatures[0]);
            }
        }
    } else {
        t = tp.get_type_at_location(node);
    }
    if t.is_nil() {
        return info;
    }

    // Parse as Layer type.
    let Some(layer) = tp.layer_type(t) else {
        return info;
    };
    info.layer_type = Some(layer.clone());

    // Unroll provides and requires, filtering out Never types.
    for p in tp.unroll_union_members(layer.r_out) {
        if !tp.checker.ty(p).flags.intersects(TypeFlags::NEVER) {
            info.provides.push(p);
        }
    }
    for r in tp.unroll_union_members(layer.r_in) {
        if !tp.checker.ty(r).flags.intersects(TypeFlags::NEVER) {
            info.requires.push(r);
        }
    }

    // ActualProvides: provides that are NOT assignable to the RIn type.
    for &p in &info.provides {
        if !tp.checker.is_type_assignable_to(p, layer.r_in) {
            info.actual_provides.push(p);
        }
    }

    // Sort all type lists deterministically by their string representation.
    // NOTE: Intentional divergence from .repos reference. The TypeScript implementation
    // preserves union member order in output/nested formats (using deterministicTypeOrder
    // only for providers/requirers extraction and quickinfo). We sort alphabetically
    // everywhere for consistent determinism independent of compiler-internal union ordering.
    let c = &mut *tp.checker;
    let mut sort_types = |types: &mut Vec<TypeId>| {
        sort_slice(types, |a, b| c.type_to_string(*a) < c.type_to_string(*b));
    };
    sort_types(&mut info.provides);
    sort_types(&mut info.requires);
    sort_types(&mut info.actual_provides);

    info
}

// Go: getDisplayNode
/// Returns the node used for display purposes.
/// If the node's parent is a variable declaration and the node is the initializer,
/// use the variable's name node instead.
fn get_display_node(node: Node) -> Node {
    if node.parent().is_some() && node.parent().kind() == SyntaxKind::VariableDeclaration {
        let var_decl = node.parent();
        if var_decl.initializer().is_some() && var_decl.initializer() == node {
            return var_decl.name();
        }
    }
    if node.parent().is_some() && node.parent().kind() == SyntaxKind::PropertyDeclaration {
        let prop_decl = node.parent();
        if prop_decl.initializer().is_some() && prop_decl.initializer() == node {
            return prop_decl.name();
        }
    }
    node
}

// Go: getAdjustedNode
/// Extracts the initializer expression from a declaration node to follow
/// during symbol resolution.
fn get_adjusted_node(node: Node) -> Node {
    match node.kind() {
        SyntaxKind::VariableDeclaration => node.initializer(),
        SyntaxKind::PropertyDeclaration => node.initializer(),
        _ => {
            if is_expression(node) {
                return node;
            }
            Node::NIL
        }
    }
}

// Go: isSimpleIdentifier
/// Checks if a node is a simple identifier or a chain of property accesses
/// with simple identifiers (e.g., `a`, `a.b`, `a.b.c`).
fn is_simple_identifier(node: Node) -> bool {
    if node.kind() == SyntaxKind::Identifier {
        return true;
    }
    if node.kind() == SyntaxKind::PropertyAccessExpression {
        let prop = node;
        return prop.name().is_some()
            && prop.name().kind() == SyntaxKind::Identifier
            && is_simple_identifier(prop.expression());
    }
    false
}

// Go: isLayerModuleCall
/// Checks if a call expression's callee is a Layer module API call
/// (e.g., Layer.provide, Layer.merge, etc.).
fn is_layer_module_call(call_expr: Node, layer_module_name: &str) -> bool {
    let expr = call_expr.expression();
    if expr.kind() != SyntaxKind::PropertyAccessExpression {
        return false;
    }
    let prop_access = expr;
    if prop_access.expression().kind() != SyntaxKind::Identifier {
        return false;
    }
    get_text_of_node(prop_access.expression()) == layer_module_name
}

// Go: findLayerModuleName
/// Resolves the imported identifier name for the "Layer" export from the
/// "effect" package. Falls back to "Layer" if not found.
fn find_layer_module_name(sf: Node) -> String {
    if sf.is_nil() {
        return "Layer".to_string();
    }
    for stmt in sf.statements() {
        if stmt.kind() != SyntaxKind::ImportDeclaration {
            continue;
        }
        let import_decl = stmt;
        if import_decl.module_specifier().is_nil() {
            continue;
        }
        let mut module_name = get_text_of_node(import_decl.module_specifier());
        // Strip quotes from module specifier.
        let bytes = module_name.as_bytes();
        if bytes.len() >= 2 && (bytes[0] == b'"' || bytes[0] == b'\'') {
            // PORT: Go slices bytes; the result is only compared with "effect".
            module_name = String::from_utf8_lossy(&bytes[1..bytes.len() - 1]).into_owned();
        }
        if module_name != "effect" {
            continue;
        }
        // Look for named imports.
        if import_decl.import_clause().is_nil() {
            continue;
        }
        let clause = import_decl.import_clause();
        if clause.named_bindings().is_nil()
            || clause.named_bindings().kind() != SyntaxKind::NamedImports
        {
            continue;
        }
        let named_imports = clause.named_bindings();
        for elem in named_imports.elements() {
            let spec = elem;
            // The "real" name is PropertyName if set (import { Layer as X }),
            // otherwise Name.
            let imported_name = if spec.property_name().is_some() {
                get_text_of_node(spec.property_name())
            } else {
                get_text_of_node(spec.name())
            };
            if imported_name == "Layer" {
                return get_text_of_node(spec.name());
            }
        }
    }
    "Layer".to_string()
}

// Go: collectChildIndices
/// Gathers graph node indices for the given AST nodes, filtering out nodes
/// that aren't in the graph.
fn collect_child_indices(
    nodes: &[Node],
    node_to_graph_index: &FxHashMap<Node, NodeIndex>,
    g: &Graph<LayerGraphNodeInfo, LayerGraphEdgeInfo>,
) -> Vec<NodeIndex> {
    let mut indices = Vec::new();
    for n in nodes {
        if let Some(&idx) = node_to_graph_index.get(n) {
            if g.has_node(idx) {
                indices.push(idx);
            }
        }
    }
    indices
}

// Go: removePartialChildren
/// Removes graph nodes for the given AST nodes.
fn remove_partial_children(
    nodes: &[Node],
    node_to_graph_index: &mut FxHashMap<Node, NodeIndex>,
    g: &mut Graph<LayerGraphNodeInfo, LayerGraphEdgeInfo>,
) {
    for n in nodes {
        if let Some(&idx) = node_to_graph_index.get(n) {
            g.remove_node(idx);
            node_to_graph_index.remove(n);
        }
    }
}

// ---------------------------------------------------------------------------
// outline.go
// ---------------------------------------------------------------------------

// Go: ExtractOutlineGraph
/// Builds a simplified dependency graph from the full layer graph.
/// It keeps only leaf nodes (deduplicated by symbol) and connects them based on
/// type compatibility: if node A requires a service that node B provides, add an edge.
// PORT: Go returns a `*graph.Graph` that is never nil; the port returns the
// graph by value.
pub fn extract_outline_graph(
    tp: &mut TypeParser<'_>,
    layer_graph: &Graph<LayerGraphNodeInfo, LayerGraphEdgeInfo>,
) -> Graph<LayerOutlineGraphNodeInfo, ()> {
    let mut g: Graph<LayerOutlineGraphNodeInfo, ()> = Graph::new();

    // Track providers: providedType → list of outline node indices that provide it.
    // PORT: Go walks this map in random order before the sort below; the
    // port keeps insertion order, which is one of Go's orders.
    let mut providers: IndexMap<TypeId, Vec<NodeIndex>> = IndexMap::new();
    // Track seen symbols for deduplication.
    let mut known_symbols: FxHashSet<SymbolId> = FxHashSet::default();

    // Step 1: Get leaf nodes (nodes with no outgoing edges) and deduplicate by symbol.
    let leaf_nodes: Vec<LayerGraphNodeInfo> = layer_graph
        .externals(Direction::Outgoing)
        .map(|(_, n)| n.clone())
        .collect();
    let mut deduped_leaf_nodes: Vec<LayerGraphNodeInfo> = Vec::new();
    for leaf_node in leaf_nodes {
        let sym = tp.get_symbol_at_location(leaf_node.node);
        if sym.is_nil() {
            deduped_leaf_nodes.push(leaf_node);
        } else if !known_symbols.contains(&sym) {
            deduped_leaf_nodes.push(leaf_node);
            known_symbols.insert(sym);
        }
    }

    // Step 2: Create outline nodes and build the provider map.
    for leaf_node in &deduped_leaf_nodes {
        let node_index = g.add_node(LayerOutlineGraphNodeInfo {
            node: leaf_node.node,
            display_node: leaf_node.display_node,
            provides: leaf_node.provides.clone(),
            actual_provides: leaf_node.actual_provides.clone(),
            requires: leaf_node.requires.clone(),
        });
        for &provided_type in &leaf_node.actual_provides {
            providers.entry(provided_type).or_default().push(node_index);
        }
    }

    // Sort provider types alphabetically for deterministic edge ordering. This
    // intentionally diverges from the .repos reference implementation which uses
    // non-deterministic checker iteration order, to avoid flaky output from Go's
    // map iteration.
    let mut sorted_provider_types: Vec<TypeId> = providers.keys().copied().collect();
    {
        let c = &mut *tp.checker;
        sort_slice(&mut sorted_provider_types, |a, b| {
            c.type_to_string(*a) < c.type_to_string(*b)
        });
    }

    // Step 3: Connect requires to providers based on type assignability.
    let outline_nodes: Vec<(NodeIndex, Vec<TypeId>)> = g
        .nodes()
        .map(|(idx, info)| (idx, info.requires.clone()))
        .collect();
    for (node_index, requires) in outline_nodes {
        for &required_type in &requires {
            for &provided_type in &sorted_provider_types {
                let provider_node_indices =
                    providers.get(&provided_type).cloned().unwrap_or_default();
                if required_type == provided_type
                    || tp
                        .checker
                        .is_type_assignable_to(required_type, provided_type)
                {
                    for provider_node_index in provider_node_indices {
                        if !g.has_edge(node_index, provider_node_index) {
                            g.add_edge(node_index, provider_node_index, ());
                        }
                    }
                }
            }
        }
    }

    g
}
