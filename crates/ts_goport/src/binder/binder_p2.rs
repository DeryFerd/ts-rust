//! Go `binder/binder.go` lines 911-1816 (bindFunctionExpression .. bindIterativeStatement).
//!
//! PORT: Go writes binder results straight onto AST nodes and the `SourceFile`.
//! Our AST is read-only while binding, so this file assumes these `Binder`
//! fields (defined in binder_p1.rs) hold the per-file results until
//! `bind_source_file` stores them in the `GoFile` OnceCells:
//! - `node_bind: NodeBindBuilder` indexed by `NodeId::index()` of `self.file` nodes
//!   (Go `node.Symbol`, `node.Locals`, `FlowNodeData().FlowNode`, `EndFlowNode`, and
//!   the binder-added bits of `node.Flags` in `added_flags`).
//! - `flow_node_arena: Vec<FlowNode>` indexed by `FlowNodeId::local_index()`.
//! - `symbol_arena` (Go `symbolArena`): the `SymbolArena` (owned or `&mut`).
//! - `common_js_module_indicator: Node` (Go `file.CommonJSModuleIndicator`, set by the binder).
//! The small module-private helpers below read and write that state.

use crate::astdata::NodeData;
use crate::prelude::*;

// ---------------------------------------------------------------------------
// Module-private access helpers (not Go functions).
// ---------------------------------------------------------------------------

/// Binder data for a node of the file being bound (Go reads it from the node).
fn bound(b: &Binder, node: Node) -> &NodeBindData {
    debug_assert!(node.is_some(), "nil node dereference");
    debug_assert_eq!(node.file_index(), b.file.file_index());
    b.node_bind.get(node.node_id().index())
}

fn bound_mut(b: &mut Binder, node: Node) -> &mut NodeBindData {
    debug_assert!(node.is_some(), "nil node dereference");
    debug_assert_eq!(node.file_index(), b.file.file_index());
    b.node_bind.get_mut(node.node_id().index())
}

/// Go `node.Flags` during binding: parser flags plus the flags the binder added so far.
#[inline]
fn node_flags(b: &Binder, node: Node) -> NodeFlags {
    b.node_flags(node)
}

fn flow_data(b: &Binder, flow: FlowNodeId) -> &FlowNode {
    debug_assert!(flow.is_some(), "nil flow node dereference");
    &b.flow_nodes[flow.local_index()]
}

fn flow_data_mut(b: &mut Binder, flow: FlowNodeId) -> &mut FlowNode {
    debug_assert!(flow.is_some(), "nil flow node dereference");
    &mut b.flow_nodes[flow.local_index()]
}

/// Go `ast.GetExports(symbol)`: creates the table on first use.
fn binder_get_exports(b: &mut Binder, symbol: SymbolId) -> SymbolTable {
    let exports = b.symbols.sym(symbol).exports;
    if exports.is_some() {
        return exports;
    }
    let table = b.symbols.new_table();
    b.symbols.sym_mut(symbol).exports = table;
    table
}

/// Go `ast.GetMembers(symbol)`: creates the table on first use.
fn binder_get_members(b: &mut Binder, symbol: SymbolId) -> SymbolTable {
    let members = b.symbols.sym(symbol).members;
    if members.is_some() {
        return members;
    }
    let table = b.symbols.new_table();
    b.symbols.sym_mut(symbol).members = table;
    table
}

/// Go `ast.GetLocals(container)`: creates the table on first use.
// PERF: `Binder::get_locals` sizes a new table for the container.
fn binder_get_locals(b: &mut Binder, container: Node) -> SymbolTable {
    b.get_locals(container)
}

/// Go `ast.IsExternalOrCommonJSModule(b.file)` while binding: the CommonJS
/// indicator is binder state until binding ends.
fn binder_is_external_or_common_js_module(b: &Binder) -> bool {
    with_source_file_info(b.file, |info| info.external_module_indicator).is_some()
        || b.common_js_module_indicator.is_some()
}

impl Binder {
    // Go: ast/utilities.go:4226 IsImplicitlyExportedJSDocDeclaration
    // PORT: while binding, the CommonJS indicator of the file is binder
    // state, so the Go `ast.IsExternalOrCommonJSModule(node.Parent)` test
    // reads it from the binder. The parent is always the file being bound.
    pub(super) fn is_implicitly_exported_js_doc_declaration(&self, node: Node) -> bool {
        let parent = node.parent();
        if !is_source_file(parent) {
            return false;
        }
        debug_assert!(parent == self.file);
        if !binder_is_external_or_common_js_module(self) {
            return false;
        }
        if is_js_type_alias_declaration(node) {
            return true;
        }
        // A reparsed ModuleDeclaration synthesized from a JSDoc @typedef/@callback
        // dotted name should also be treated as implicitly exported in modules.
        is_module_declaration(node) && node.flags().intersects(NodeFlags::REPARSED)
    }
}

/// Go `node.BodyData() != nil`: kinds that embed `ast.BodyBase`.
fn has_body_data(node: Node) -> bool {
    matches!(
        node.kind(),
        SyntaxKind::FunctionDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::Constructor
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::FunctionExpression
            | SyntaxKind::ArrowFunction
            | SyntaxKind::ModuleDeclaration
    )
}

impl Binder {
    // Go: binder/binder.go:914 bindFunctionExpression
    pub fn bind_function_expression(&mut self, node: Node) {
        if !with_source_file_info(self.file, |info| info.is_declaration_file)
            && !node_flags(self, node).intersects(NodeFlags::AMBIENT)
            && is_async_function(node)
        {
            self.emit_flags |= NodeFlags::HAS_ASYNC_FUNCTIONS;
        }
        let current_flow = self.current_flow;
        self.set_flow_node(node, current_flow);
        let mut binding_name: String = INTERNAL_SYMBOL_NAME_FUNCTION.to_string();
        if is_function_expression(node) && node.name().is_some() {
            self.check_strict_mode_function_name(node);
            binding_name = node.name().text().to_string();
        }
        self.bind_anonymous_declaration(node, SymbolFlags::FUNCTION, &binding_name);
    }

    // Go: binder/binder.go:927 bindCallExpression
    pub fn bind_call_expression(&mut self, node: Node) {
        // We're only inspecting call expressions to detect CommonJS modules, so we can skip
        // this check if we've already seen the module indicator
        if self.common_js_module_indicator.is_nil()
            && is_require_call(node, false /*requireStringLiteralLikeArgument*/)
        {
            self.set_common_js_module_indicator(node);
        }
    }

    // Go: binder/binder.go:935 setCommonJSModuleIndicator
    pub fn set_common_js_module_indicator(&mut self, node: Node) -> bool {
        let external_module_indicator =
            with_source_file_info(self.file, |info| info.external_module_indicator);
        if external_module_indicator.is_some() && external_module_indicator != self.file {
            return false;
        }
        if self.common_js_module_indicator.is_nil() {
            self.common_js_module_indicator = node;
            if external_module_indicator.is_nil() {
                self.bind_source_file_as_external_module();
            }
        }
        true
    }

    // Go: binder/binder.go:948 bindClassLikeDeclaration
    pub fn bind_class_like_declaration(&mut self, node: Node) {
        let name = node.name();
        match node.kind() {
            SyntaxKind::ClassDeclaration => {
                self.bind_block_scoped_declaration(
                    node,
                    SymbolFlags::CLASS,
                    SymbolFlags::CLASS_EXCLUDES,
                );
            }
            SyntaxKind::ClassExpression => {
                let mut name_text: String = INTERNAL_SYMBOL_NAME_CLASS.to_string();
                if name.is_some() {
                    name_text = name.text().to_string();
                }
                self.bind_anonymous_declaration(node, SymbolFlags::CLASS, &name_text);
            }
            _ => {}
        }
        let symbol = bound(self, node).symbol;
        // TypeScript 1.0 spec (April 2014): 8.4
        // Every class automatically contains a static property member named 'prototype', the
        // type of which is an instantiation of the class type with type Any supplied as a type
        // argument for each type parameter. It is an error to explicitly declare a static
        // property member with the name 'prototype'.
        //
        // Note: we check for this here because this class may be merging into a module.  The
        // module might have an exported variable called 'prototype'.  We can't allow that as
        // that would clash with the built-in 'prototype' for the class.
        let prototype_symbol =
            self.new_symbol(SymbolFlags::PROPERTY | SymbolFlags::PROTOTYPE, "prototype");
        let prototype_name = self.symbols.sym(prototype_symbol).name.clone();
        let exports = binder_get_exports(self, symbol);
        let symbol_export = self.symbols.get_name(exports, &prototype_name);
        if symbol_export.is_some() {
            let decl = self.symbols.sym(symbol_export).declarations[0];
            let display = symbol_name(&self.symbols, prototype_symbol);
            self.error_on_node(decl, diag::Duplicate_identifier_0, args![display]);
        }
        let exports = binder_get_exports(self, symbol);
        self.symbols.set(exports, prototype_name, prototype_symbol);
        self.symbols.sym_mut(prototype_symbol).parent = symbol;
    }

    // Go: binder/binder.go:979 bindPropertyOrMethodOrAccessor
    // PERF: query Q7-3. `d` is the data of `node`, which the caller already
    // loaded with `parsed_node_data`.
    pub fn bind_property_or_method_or_accessor(
        &mut self,
        node: Node,
        d: LoadedData,
        symbol_flags: SymbolFlags,
        symbol_excludes: SymbolFlags,
    ) {
        if !with_source_file_info(self.file, |info| info.is_declaration_file)
            && !node_flags(self, node).intersects(NodeFlags::AMBIENT)
            && is_async_function(node)
        {
            self.emit_flags |= NodeFlags::HAS_ASYNC_FUNCTIONS;
        }
        if self.current_flow.is_some()
            && is_object_literal_or_class_expression_method_or_accessor(node)
        {
            let current_flow = self.current_flow;
            self.set_flow_node(node, current_flow);
        }
        if has_dynamic_name_in(node, d) {
            self.bind_anonymous_declaration(node, symbol_flags, INTERNAL_SYMBOL_NAME_COMPUTED);
        } else {
            self.declare_symbol_and_add_to_symbol_table(node, symbol_flags, symbol_excludes);
        }
    }

    // Go: binder/binder.go:993 bindFunctionOrConstructorType
    pub fn bind_function_or_constructor_type(&mut self, node: Node) {
        // For a given function symbol "<...>(...) => T" we want to generate a symbol identical
        // to the one we would get for: { <...>(...): T }
        //
        // We do that by making an anonymous type literal symbol, and then setting the function
        // symbol as its sole member. To the rest of the system, this symbol will be indistinguishable
        // from an actual type literal symbol you would have gotten had you used the long form.
        let declaration_name = self.get_declaration_name(node);
        let symbol = self.new_symbol(SymbolFlags::SIGNATURE, &declaration_name);
        self.add_declaration_to_symbol(symbol, node, SymbolFlags::SIGNATURE);
        let type_literal_symbol =
            self.new_symbol(SymbolFlags::TYPE_LITERAL, INTERNAL_SYMBOL_NAME_TYPE);
        self.add_declaration_to_symbol(type_literal_symbol, node, SymbolFlags::TYPE_LITERAL);
        let members = self.symbols.new_table();
        self.symbols.sym_mut(type_literal_symbol).members = members;
        let member_name = self.symbols.sym(symbol).name.clone();
        self.symbols.set(members, member_name, symbol);
    }

    // Go: binder/binder.go:1008 addLateBoundAssignmentDeclarationToSymbol
    pub fn add_late_bound_assignment_declaration_to_symbol(
        &mut self,
        node: Node,
        symbol: SymbolId,
    ) {
        let exports = binder_get_exports(self, symbol);
        let mut assignment_symbol = self
            .symbols
            .get(exports, INTERNAL_SYMBOL_NAME_ASSIGNMENT_DECLARATION);
        if assignment_symbol.is_nil() {
            assignment_symbol = self.new_symbol(
                SymbolFlags::NONE,
                INTERNAL_SYMBOL_NAME_ASSIGNMENT_DECLARATION,
            );
            self.symbols.set(
                exports,
                INTERNAL_SYMBOL_NAME_ASSIGNMENT_DECLARATION,
                assignment_symbol,
            );
        }
        self.symbols
            .sym_mut(assignment_symbol)
            .declarations
            .push(node);
    }

    // Go: binder/binder.go:1018 bindModuleExportsAssignment
    pub fn bind_module_exports_assignment(&mut self, node: Node) {
        if self.set_common_js_module_indicator(node) {
            let container = self.file;
            let flags = if expression_is_alias(node.right()) {
                SymbolFlags::ALIAS
            } else {
                SymbolFlags::PROPERTY
            };
            let container_symbol = bound(self, container).symbol;
            let exports = binder_get_exports(self, container_symbol);
            let symbol =
                self.declare_symbol(exports, container_symbol, node, flags, SymbolFlags::NONE);
            set_value_declaration(&mut self.symbols, symbol, node);
        }
    }

    // Go: binder/binder.go:1027 bindExpandoPropertyAssignment
    pub fn bind_expando_property_assignment(&mut self, node: Node) {
        self.expando_assignments.push(ExpandoAssignmentInfo {
            node,
            container: self.container,
            block_scope_container: self.block_scope_container,
        });
    }

    // Go: binder/binder.go:1035 bindDeferredExpandoAssignments
    pub fn bind_deferred_expando_assignments(&mut self) {
        let count = self.expando_assignments.len();
        for i in 0..count {
            let info = &self.expando_assignments[i];
            let (node, container, block_scope_container) =
                (info.node, info.container, info.block_scope_container);
            self.container = container;
            self.block_scope_container = block_scope_container;
            self.bind_deferred_expando_assignment(node);
        }
    }

    // Go: binder/binder.go:1046 bindCommonJSTypeExports
    // If the given module symbol has an export= symbol, promote exports with a type or namespace meaning
    // from the module symbol onto the export= symbol and, if any such exports exist, mark the export=
    // symbol as a namespace module.
    pub fn bind_common_js_type_exports(&mut self, module_symbol: SymbolId) {
        let module_exports = self.symbols.sym(module_symbol).exports;
        let export_equals = self
            .symbols
            .get(module_exports, INTERNAL_SYMBOL_NAME_EXPORT_EQUALS);
        if export_equals.is_some() {
            for symbol in self.symbols.values(module_exports) {
                let (name, flags) = {
                    let s = self.symbols.sym(symbol);
                    (s.name.clone(), s.flags)
                };
                if name != INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
                    && flags.intersects(SymbolFlags::TYPE | SymbolFlags::NAMESPACE)
                {
                    let exports = binder_get_exports(self, export_equals);
                    self.symbols.set(exports, name, symbol);
                    self.symbols.sym_mut(export_equals).flags |= SymbolFlags::NAMESPACE_MODULE;
                }
            }
        }
    }

    // Go: binder/binder.go:1058 bindDeferredExpandoAssignment
    pub fn bind_deferred_expando_assignment(&mut self, node: Node) {
        let parent = get_parent_of_property_assignment(node);
        let block_scope_container = self.block_scope_container;
        let mut symbol = self.lookup_entity(parent, block_scope_container);
        if symbol.is_nil() {
            let container = self.container;
            symbol = self.lookup_entity(parent, container);
        }
        symbol = get_initializer_symbol(self, symbol);
        if symbol.is_some() {
            // PERF: a superset of "gave `node` a symbol". The declaration
            // transformer walks for expando assignments only when it is set.
            self.file_bind.has_expando_assignments = true;
            if has_dynamic_name(node) {
                self.bind_anonymous_declaration(
                    node,
                    SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT,
                    INTERNAL_SYMBOL_NAME_COMPUTED,
                );
                self.add_late_bound_assignment_declaration_to_symbol(node, symbol);
            } else {
                // We declare expandos only when there are no non-expando declarations for that name.
                let exports = binder_get_exports(self, symbol);
                let declaration_name = self.get_declaration_name(node);
                let existing = self.symbols.get_name(exports, &declaration_name);
                if existing.is_nil()
                    || self
                        .symbols
                        .sym(existing)
                        .flags
                        .intersects(SymbolFlags::ASSIGNMENT)
                {
                    self.declare_symbol(
                        exports,
                        symbol,
                        node,
                        SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT,
                        SymbolFlags::PROPERTY_EXCLUDES,
                    );
                }
            }
        }
    }
}

// Go: binder/binder.go:1078 getParentOfPropertyAssignment
pub fn get_parent_of_property_assignment(node: Node) -> Node {
    match node.kind() {
        SyntaxKind::BinaryExpression => return node.left().expression(),
        SyntaxKind::CallExpression => return node.arguments().get(0),
        _ => {}
    }
    panic!("Unhandled case in getParentOfPropertyAssignment")
}

impl Binder {
    // Go: binder/binder.go:1088 bindExportsOrObjectDefineProperty
    pub fn bind_exports_or_object_define_property(&mut self, node: Node) {
        if self.set_common_js_module_indicator(node) {
            let container = self.file;
            let flags = if is_binary_expression(node) && expression_is_alias(node.right()) {
                SymbolFlags::ALIAS
            } else {
                SymbolFlags::FUNCTION_SCOPED_VARIABLE
            };
            let container_symbol = bound(self, container).symbol;
            let exports = binder_get_exports(self, container_symbol);
            self.declare_symbol(
                exports,
                container_symbol,
                node,
                flags,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES,
            );
        }
    }
}

// Go: binder/binder.go:1096 getInitializerSymbol
// PORT: Go reads `initializer.Symbol()` from the node; during binding that lives in
// the binder, so this takes the binder instead of only the symbol arena.
pub fn get_initializer_symbol(b: &Binder, symbol: SymbolId) -> SymbolId {
    if symbol.is_nil() || b.symbols.sym(symbol).value_declaration.is_nil() {
        return SymbolId::NIL;
    }
    let declaration = b.symbols.sym(symbol).value_declaration;
    // For an assignment 'fn.xxx = ...', where 'fn' is a previously declared function or a previously
    // declared const variable initialized with a function expression or arrow function, we add expando
    // property declarations to the function's symbol. This also applies to class expressions in JS files,
    // and empty object literals in JS files when the declaration doesn't have a type annotation.
    if is_function_declaration(declaration)
        || is_in_js_file(declaration) && is_class_declaration(declaration)
    {
        return symbol;
    } else if is_variable_declaration(declaration)
        && (node_flags(b, declaration.parent()).intersects(NodeFlags::CONST)
            || is_in_js_file(declaration))
    {
        let initializer = declaration.initializer();
        if is_expando_initializer(declaration, initializer) {
            return bound(b, initializer).symbol;
        }
    } else if is_binary_expression(declaration) && is_in_js_file(declaration) {
        let initializer = declaration.right();
        if is_expando_initializer(declaration, initializer) {
            return bound(b, initializer).symbol;
        }
    }
    SymbolId::NIL
}

impl Binder {
    // Go: binder/binder.go:1123 bindThisPropertyAssignment
    pub fn bind_this_property_assignment(&mut self, node: Node) {
        if !is_in_js_file(node) {
            return;
        }
        let left = node.left();
        if is_property_access_expression(left) && is_private_identifier(left.name())
            || self.this_container.is_nil()
        {
            return;
        }
        let (class_symbol, symbol_table) = self.get_this_class_and_symbol_table();
        if symbol_table.is_some() {
            if has_dynamic_name(node) {
                self.declare_symbol_ex(
                    symbol_table,
                    class_symbol,
                    node,
                    SymbolFlags::PROPERTY,
                    SymbolFlags::NONE,
                    true, /*isReplaceableByMethod*/
                    true, /*isComputedName*/
                );
                self.add_late_bound_assignment_declaration_to_symbol(node, class_symbol);
            } else {
                self.declare_symbol_ex(
                    symbol_table,
                    class_symbol,
                    node,
                    SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT,
                    SymbolFlags::NONE,
                    true,  /*isReplaceableByMethod*/
                    false, /*isComputedName*/
                );
            }
        } else if self.this_container.kind() != SyntaxKind::FunctionDeclaration
            && self.this_container.kind() != SyntaxKind::FunctionExpression
        {
            // !!! constructor functions
            panic!(
                "Unhandled case in bindThisPropertyAssignment: {:?}",
                self.this_container.kind()
            );
        }
    }

    // Go: binder/binder.go:1145 getThisClassAndSymbolTable
    pub fn get_this_class_and_symbol_table(&mut self) -> (SymbolId, SymbolTable) {
        let mut class_symbol = SymbolId::NIL;
        let mut symbol_table = SymbolTable::NIL;
        if self.this_container.is_nil() {
            return (SymbolId::NIL, SymbolTable::NIL);
        }
        match self.this_container.kind() {
            SyntaxKind::FunctionDeclaration | SyntaxKind::FunctionExpression => {
                // !!! constructor functions
            }
            SyntaxKind::Constructor
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::ClassStaticBlockDeclaration => {
                // this.property assignment in class member -- bind to the containing class
                let this_container = self.this_container;
                class_symbol = bound(self, this_container.parent()).symbol;
                if is_static(this_container) {
                    symbol_table = binder_get_exports(self, class_symbol);
                } else {
                    symbol_table = binder_get_members(self, class_symbol);
                }
            }
            _ => {}
        }
        (class_symbol, symbol_table)
    }

    // Go: binder/binder.go:1164 bindEnumDeclaration
    pub fn bind_enum_declaration(&mut self, node: Node) {
        if is_enum_const(node) {
            self.bind_block_scoped_declaration(
                node,
                SymbolFlags::CONST_ENUM,
                SymbolFlags::CONST_ENUM_EXCLUDES,
            );
        } else {
            self.bind_block_scoped_declaration(
                node,
                SymbolFlags::REGULAR_ENUM,
                SymbolFlags::REGULAR_ENUM_EXCLUDES,
            );
        }
    }

    // Go: binder/binder.go:1172 bindVariableDeclarationOrBindingElement
    pub fn bind_variable_declaration_or_binding_element(&mut self, node: Node) {
        self.check_strict_mode_eval_or_arguments(node, node.name());
        let name = node.name();
        if name.is_some() && !is_binding_pattern(name) {
            if is_variable_declaration_initialized_to_require(node) {
                self.declare_symbol_and_add_to_symbol_table(
                    node,
                    SymbolFlags::ALIAS,
                    SymbolFlags::ALIAS_EXCLUDES,
                );
            } else if is_block_or_catch_scoped(node) {
                self.bind_block_scoped_declaration(
                    node,
                    SymbolFlags::BLOCK_SCOPED_VARIABLE,
                    SymbolFlags::BLOCK_SCOPED_VARIABLE_EXCLUDES,
                );
            } else if is_part_of_parameter_declaration(node) {
                // It is safe to walk up parent chain to find whether the node is a destructuring parameter declaration
                // because its parent chain has already been set up, since parents are set before descending into children.
                //
                // If node is a binding element in parameter declaration, we need to use ParameterExcludes.
                // Using ParameterExcludes flag allows the compiler to report an error on duplicate identifiers in Parameter Declaration
                // For example:
                //      function foo([a,a]) {} // Duplicate Identifier error
                //      function bar(a,a) {}   // Duplicate Identifier error, parameter declaration in this case is handled in bindParameter
                //                             // which correctly set excluded symbols
                self.declare_symbol_and_add_to_symbol_table(
                    node,
                    SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                    SymbolFlags::PARAMETER_EXCLUDES,
                );
            } else {
                self.declare_symbol_and_add_to_symbol_table(
                    node,
                    SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                    SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES,
                );
            }
        }
    }

    // Go: binder/binder.go:1197 bindParameter
    pub fn bind_parameter(&mut self, node: Node) {
        // PERF: query Q7-3. The node data is looked up once, and the field
        // reads below (name, modifiers, question token) use it.
        let d = parsed_node_data(node);
        let decl_name = node.name_in(d);
        if !node_flags(self, node).intersects(NodeFlags::AMBIENT) {
            // It is a SyntaxError if the identifier eval or arguments appears within a FormalParameterList of a
            // strict mode FunctionLikeDeclaration or FunctionExpression(13.1)
            self.check_strict_mode_eval_or_arguments(node, decl_name);
        }
        if is_binding_pattern(decl_name) {
            let index: i32 = node
                .parent()
                .parameters()
                .iter()
                .position(|p| p == node)
                .map_or(-1, |i| i as i32);
            self.bind_anonymous_declaration(
                node,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                &format!("__{index}"),
            );
        } else {
            self.declare_symbol_and_add_to_symbol_table(
                node,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                SymbolFlags::PARAMETER_EXCLUDES,
            );
        }
        // If this is a property-parameter, then also declare the property symbol into the
        // containing class.
        // Go `ast.IsParameterPropertyDeclaration(node, node.Parent)` on the loaded data.
        let parent = node.parent();
        if is_parameter_declaration(node)
            && has_syntactic_modifier_in(node, d, ModifierFlags::PARAMETER_PROPERTY_MODIFIER)
            && parent.kind() == SyntaxKind::Constructor
        {
            let class_declaration = parent.parent();
            let flags = SymbolFlags::PROPERTY
                | if node.question_token_in(d).is_some() {
                    SymbolFlags::OPTIONAL
                } else {
                    SymbolFlags::NONE
                };
            let class_symbol = bound(self, class_declaration).symbol;
            let members = binder_get_members(self, class_symbol);
            self.declare_symbol(
                members,
                class_symbol,
                node,
                flags,
                SymbolFlags::PROPERTY_EXCLUDES,
            );
        }
    }

    // Go: binder/binder.go:1219 bindFunctionDeclaration
    pub fn bind_function_declaration(&mut self, node: Node) {
        if !with_source_file_info(self.file, |info| info.is_declaration_file)
            && !node_flags(self, node).intersects(NodeFlags::AMBIENT)
            && is_async_function(node)
        {
            self.emit_flags |= NodeFlags::HAS_ASYNC_FUNCTIONS;
        }
        self.check_strict_mode_function_name(node);
        self.bind_block_scoped_declaration(
            node,
            SymbolFlags::FUNCTION,
            SymbolFlags::FUNCTION_EXCLUDES,
        );
    }

    // Go: binder/binder.go:1227 getInferTypeContainer
    pub fn get_infer_type_container(&self, node: Node) -> Node {
        // PORT: Go `ast.FindAncestor(node, callback)` inlined (same walk up the parent chain).
        let mut extends_type = Node::NIL;
        let mut n = node;
        while n.is_some() {
            let parent = n.parent();
            if parent.is_some() && is_conditional_type_node(parent) && parent.extends_type() == n {
                extends_type = n;
                break;
            }
            n = n.parent();
        }
        if extends_type.is_some() {
            return extends_type.parent();
        }
        Node::NIL
    }

    // Go: binder/binder.go:1238 bindAnonymousDeclaration
    pub fn bind_anonymous_declaration(
        &mut self,
        node: Node,
        symbol_flags: SymbolFlags,
        name: &str,
    ) {
        let symbol = self.new_symbol(symbol_flags, name);
        if symbol_flags.intersects(SymbolFlags::ENUM_MEMBER | SymbolFlags::CLASS_MEMBER) {
            let container = self.container;
            let container_symbol = bound(self, container).symbol;
            self.symbols.sym_mut(symbol).parent = container_symbol;
        }
        self.add_declaration_to_symbol(symbol, node, symbol_flags);
    }

    // Go: binder/binder.go:1246 bindBlockScopedDeclaration
    pub fn bind_block_scoped_declaration(
        &mut self,
        node: Node,
        symbol_flags: SymbolFlags,
        symbol_excludes: SymbolFlags,
    ) {
        match self.block_scope_container.kind() {
            SyntaxKind::ModuleDeclaration => {
                self.declare_module_member(node, symbol_flags, symbol_excludes);
                return;
            }
            SyntaxKind::SourceFile => {
                // PORT: Go `ast.IsExternalOrCommonJSModule(b.container.AsSourceFile())`; the
                // container here is the file being bound, whose CommonJS indicator is binder state.
                debug_assert!(self.container == self.file);
                if binder_is_external_or_common_js_module(self) {
                    self.declare_module_member(node, symbol_flags, symbol_excludes);
                    return;
                }
                // fallthrough
            }
            _ => {}
        }
        let block_scope_container = self.block_scope_container;
        let locals = binder_get_locals(self, block_scope_container);
        self.declare_symbol(
            locals,
            SymbolId::NIL, /*parent*/
            node,
            symbol_flags,
            symbol_excludes,
        );
    }

    // Go: binder/binder.go:1261 bindTypeParameter
    pub fn bind_type_parameter(&mut self, node: Node) {
        if node.parent().kind() == SyntaxKind::InferType {
            let container = self.get_infer_type_container(node.parent());
            if container.is_some() {
                let locals = binder_get_locals(self, container);
                self.declare_symbol(
                    locals,
                    SymbolId::NIL, /*parent*/
                    node,
                    SymbolFlags::TYPE_PARAMETER,
                    SymbolFlags::TYPE_PARAMETER_EXCLUDES,
                );
            } else {
                let declaration_name = self.get_declaration_name(node);
                self.bind_anonymous_declaration(
                    node,
                    SymbolFlags::TYPE_PARAMETER,
                    &declaration_name,
                );
            }
        } else {
            self.declare_symbol_and_add_to_symbol_table(
                node,
                SymbolFlags::TYPE_PARAMETER,
                SymbolFlags::TYPE_PARAMETER_EXCLUDES,
            );
        }
    }

    // Go: binder/binder.go:1274 lookupEntity
    pub fn lookup_entity(&mut self, node: Node, container: Node) -> SymbolId {
        if is_identifier(node) {
            return self.lookup_name(node.text(), container);
        }
        if node.expression().kind() == SyntaxKind::ThisKeyword {
            let (_, symbol_table) = self.get_this_class_and_symbol_table();
            if symbol_table.is_some() {
                let name = get_element_or_property_access_name(node);
                if name.is_some() {
                    return self.symbols.get(symbol_table, name.text());
                }
            }
            return SymbolId::NIL;
        }
        let entity = self.lookup_entity(node.expression(), container);
        let symbol = get_initializer_symbol(self, entity);
        if symbol.is_some() && self.symbols.sym(symbol).exports.is_some() {
            let name = get_element_or_property_access_name(node);
            if name.is_some() {
                let exports = self.symbols.sym(symbol).exports;
                return self.symbols.get(exports, name.text());
            }
        }
        SymbolId::NIL
    }

    // Go: binder/binder.go:1294 lookupName
    pub fn lookup_name(&self, name: &str, container: Node) -> SymbolId {
        // PORT: Go checks `LocalsContainerData() != nil` and `DeclarationData() != nil`; every
        // node has a NodeBindData here, and nodes without that Go data keep nil locals/symbol.
        let locals = bound(self, container).locals;
        if locals.is_some() {
            let local = self.symbols.get(locals, name);
            if local.is_some() {
                let export_symbol = self.symbols.sym(local).export_symbol;
                return if export_symbol.is_some() {
                    export_symbol
                } else {
                    local
                };
            }
        }
        let declaration_symbol = bound(self, container).symbol;
        if declaration_symbol.is_some() {
            let exports = self.symbols.sym(declaration_symbol).exports;
            return self.symbols.get(exports, name);
        }
        SymbolId::NIL
    }

    // Go: binder/binder.go:1309 checkContextualIdentifier
    // The binder visits every node in the syntax tree so it is a convenient place to perform a single localized
    // check for reserved words used as identifiers in strict mode code, as well as `yield` or `await` in
    // [Yield] or [Await] contexts, respectively.
    pub fn check_contextual_identifier(&mut self, node: Node) {
        // Report error only if there are no parse errors in file
        let flags = node_flags(self, node);
        // PERF: U1 (a). Every test below is pure, and the code below does
        // nothing for an ambient or JSDoc node or for a text that is no
        // keyword (`original_keyword_kind == Identifier`). So these cases
        // return here: the flag tests first, then the keyword bit made at
        // parse (`Node::text_is_keyword`), without the diagnostics lookup,
        // `is_identifier_name` and the text load.
        if flags.intersects(NodeFlags::AMBIENT)
            || flags.intersects(NodeFlags::JS_DOC)
            || !node.text_is_keyword()
        {
            return;
        }
        if source_file_info(self.file).diagnostics.is_empty()
            && !flags.intersects(NodeFlags::AMBIENT)
            && !flags.intersects(NodeFlags::JS_DOC)
            && !is_identifier_name(node)
        {
            // strict mode identifiers
            let original_keyword_kind = get_identifier_token(node.text());
            if original_keyword_kind == SyntaxKind::Identifier {
                return;
            }
            if (original_keyword_kind as u16) >= (SyntaxKind::FIRST_FUTURE_RESERVED_WORD as u16)
                && (original_keyword_kind as u16) <= (SyntaxKind::LAST_FUTURE_RESERVED_WORD as u16)
            {
                let message = self.get_strict_mode_identifier_message(node);
                self.error_on_node(node, message, args![declaration_name_to_string(node)]);
            } else if original_keyword_kind == SyntaxKind::AwaitKeyword {
                if is_external_module(self.file) && is_in_top_level_context(node) {
                    self.error_on_node(
                        node,
                        diag::Identifier_expected_0_is_a_reserved_word_at_the_top_level_of_a_module,
                        args![declaration_name_to_string(node)],
                    );
                } else if flags.intersects(NodeFlags::AWAIT_CONTEXT) {
                    self.error_on_node(
                        node,
                        diag::Identifier_expected_0_is_a_reserved_word_that_cannot_be_used_here,
                        args![declaration_name_to_string(node)],
                    );
                }
            } else if original_keyword_kind == SyntaxKind::YieldKeyword
                && flags.intersects(NodeFlags::YIELD_CONTEXT)
            {
                self.error_on_node(
                    node,
                    diag::Identifier_expected_0_is_a_reserved_word_that_cannot_be_used_here,
                    args![declaration_name_to_string(node)],
                );
            }
        }
    }

    // Go: binder/binder.go:1331 checkPrivateIdentifier
    pub fn check_private_identifier(&mut self, node: Node) {
        if node.text() == "#constructor" {
            // Report error only if there are no parse errors in file
            if source_file_info(self.file).diagnostics.is_empty() {
                self.error_on_node(
                    node,
                    diag::X_constructor_is_a_reserved_word,
                    args![declaration_name_to_string(node)],
                );
            }
        }
    }

    // Go: binder/binder.go:1340 getStrictModeIdentifierMessage
    pub fn get_strict_mode_identifier_message(
        &self,
        node: Node,
    ) -> &'static crate::diagnostics::Message {
        // Provide specialized messages to help the user understand why we think they're in
        // strict mode.
        if get_containing_class(node).is_some() {
            return diag::Identifier_expected_0_is_a_reserved_word_in_strict_mode_Class_definitions_are_automatically_in_strict_mode;
        }
        if with_source_file_info(self.file, |info| info.external_module_indicator).is_some() {
            return diag::Identifier_expected_0_is_a_reserved_word_in_strict_mode_Modules_are_automatically_in_strict_mode;
        }
        diag::Identifier_expected_0_is_a_reserved_word_in_strict_mode
    }
}

// Go: binder/binder.go:1353 isUseStrictPrologueDirective
// Should be called only on prologue directives (ast.IsPrologueDirective(node) should be true)
pub fn is_use_strict_prologue_directive(source_file: Node, node: Node) -> bool {
    let node_text = get_source_text_of_node_from_source_file(
        source_file,
        node.expression(),
        false, /*includeTrivia*/
    );
    // Note: the node text must be exactly "use strict" or 'use strict'.  It is not ok for the
    // string to contain unicode escapes (as per ES5).
    node_text == "\"use strict\"" || node_text == "'use strict'"
}

// Go: binder/binder.go:1360 FindUseStrictPrologue
pub fn find_use_strict_prologue(source_file: Node, statements: &[Node]) -> Node {
    for &statement in statements {
        if is_prologue_directive(statement) {
            if is_use_strict_prologue_directive(source_file, statement) {
                return statement;
            }
        } else {
            return Node::NIL;
        }
    }
    Node::NIL
}

impl Binder {
    // Go: binder/binder.go:1374 checkStrictModeFunctionName
    pub fn check_strict_mode_function_name(&mut self, node: Node) {
        if !node_flags(self, node).intersects(NodeFlags::AMBIENT) {
            // It is a SyntaxError if the identifier eval or arguments appears within a FormalParameterList of a strict mode FunctionDeclaration or FunctionExpression (13.1))
            self.check_strict_mode_eval_or_arguments(node, node.name());
        }
    }

    // Go: binder/binder.go:1381 getStrictModeBlockScopeFunctionDeclarationMessage
    pub fn get_strict_mode_block_scope_function_declaration_message(
        &self,
        node: Node,
    ) -> &'static crate::diagnostics::Message {
        // Provide specialized messages to help the user understand why we think they're in strict mode.
        if get_containing_class(node).is_some() {
            return diag::Function_declarations_are_not_allowed_inside_blocks_in_strict_mode_when_targeting_ES5_Class_definitions_are_automatically_in_strict_mode;
        }
        if with_source_file_info(self.file, |info| info.external_module_indicator).is_some() {
            return diag::Function_declarations_are_not_allowed_inside_blocks_in_strict_mode_when_targeting_ES5_Modules_are_automatically_in_strict_mode;
        }
        diag::Function_declarations_are_not_allowed_inside_blocks_in_strict_mode_when_targeting_ES5
    }

    // Go: binder/binder.go:1392 checkStrictModeBinaryExpression
    pub fn check_strict_mode_binary_expression(&mut self, node: Node) {
        let left = node.left();
        if is_left_hand_side_expression(left)
            && is_assignment_operator(node.operator_token().kind())
        {
            // ECMA 262 (Annex C) The identifier eval or arguments may not appear as the LeftHandSideExpression of an
            // Assignment operator(11.13) or of a PostfixExpression(11.3)
            self.check_strict_mode_eval_or_arguments(node, left);
        }
    }

    // Go: binder/binder.go:1401 checkStrictModeCatchClause
    pub fn check_strict_mode_catch_clause(&mut self, node: Node) {
        // It is a SyntaxError if a TryStatement with a Catch occurs within strict code and the Identifier of the
        // Catch production is eval or arguments
        let variable_declaration = node.variable_declaration();
        if variable_declaration.is_some() {
            self.check_strict_mode_eval_or_arguments(node, variable_declaration.name());
        }
    }

    // Go: binder/binder.go:1410 checkStrictModeDeleteExpression
    pub fn check_strict_mode_delete_expression(&mut self, node: Node) {
        // Grammar checking
        let expression = node.expression();
        if expression.kind() == SyntaxKind::Identifier {
            // When a delete operator occurs within strict mode code, a SyntaxError is thrown if its
            // UnaryExpression is a direct reference to a variable, function argument, or function name
            self.error_on_node(
                expression,
                diag::X_delete_cannot_be_called_on_an_identifier_in_strict_mode,
                args![],
            );
        }
    }

    // Go: binder/binder.go:1420 checkStrictModePostfixUnaryExpression
    pub fn check_strict_mode_postfix_unary_expression(&mut self, node: Node) {
        // Grammar checking
        // The identifier eval or arguments may not appear as the LeftHandSideExpression of an
        // Assignment operator(11.13) or of a PostfixExpression(11.3) or as the UnaryExpression
        // operated upon by a Prefix Increment(11.4.4) or a Prefix Decrement(11.4.5) operator.
        self.check_strict_mode_eval_or_arguments(node, node.operand());
    }

    // Go: binder/binder.go:1428 checkStrictModePrefixUnaryExpression
    pub fn check_strict_mode_prefix_unary_expression(&mut self, node: Node) {
        // Grammar checking
        let operator = node.operator();
        if operator == SyntaxKind::PlusPlusToken || operator == SyntaxKind::MinusMinusToken {
            self.check_strict_mode_eval_or_arguments(node, node.operand());
        }
    }

    // Go: binder/binder.go:1436 checkStrictModeWithStatement
    pub fn check_strict_mode_with_statement(&mut self, node: Node) {
        // Grammar checking for withStatement
        self.error_on_first_token(
            node,
            diag::X_with_statements_are_not_allowed_in_strict_mode,
            args![],
        );
    }

    // Go: binder/binder.go:1441 checkStrictModeLabeledStatement
    pub fn check_strict_mode_labeled_statement(&mut self, node: Node) {
        // Grammar checking for labeledStatement
        let statement = node.statement();
        if is_declaration_statement(statement) || is_variable_statement(statement) {
            self.error_on_first_token(node.label(), diag::A_label_is_not_allowed_here, args![]);
        }
    }
}

/// `eval` and `arguments`, interned once for `is_eval_or_arguments_identifier`.
static EVAL_NAME: std::sync::LazyLock<Name> = std::sync::LazyLock::new(|| Name::from("eval"));
static ARGUMENTS_NAME: std::sync::LazyLock<Name> =
    std::sync::LazyLock::new(|| Name::from("arguments"));

// Go: binder/binder.go:1449 isEvalOrArgumentsIdentifier
// PERF: U1 (a). Compares name ids (`Node::text_is`), with no text load.
pub fn is_eval_or_arguments_identifier(node: Node) -> bool {
    if is_identifier(node) {
        return node.text_is(&EVAL_NAME) || node.text_is(&ARGUMENTS_NAME);
    }
    false
}

impl Binder {
    // Go: binder/binder.go:1457 checkStrictModeEvalOrArguments
    pub fn check_strict_mode_eval_or_arguments(&mut self, context_node: Node, name: Node) {
        if name.is_some() && is_eval_or_arguments_identifier(name) {
            // We check first if the name is inside class declaration or class expression; if so give explicit message
            // otherwise report generic error message.
            let message = self.get_strict_mode_eval_or_arguments_message(context_node);
            self.error_on_node(name, message, args![name.text()]);
        }
    }

    // Go: binder/binder.go:1465 getStrictModeEvalOrArgumentsMessage
    pub fn get_strict_mode_eval_or_arguments_message(
        &self,
        node: Node,
    ) -> &'static crate::diagnostics::Message {
        // Provide specialized messages to help the user understand why we think they're in strict mode
        if get_containing_class(node).is_some() {
            return diag::Code_contained_in_a_class_is_evaluated_in_JavaScript_s_strict_mode_which_does_not_allow_this_use_of_0_For_more_information_see_https_Colon_Slash_Slashdeveloper_mozilla_org_Slashen_US_Slashdocs_SlashWeb_SlashJavaScript_SlashReference_SlashStrict_mode;
        }
        if with_source_file_info(self.file, |info| info.external_module_indicator).is_some() {
            return diag::Invalid_use_of_0_Modules_are_automatically_in_strict_mode;
        }
        diag::Invalid_use_of_0_in_strict_mode
    }
}

impl Binder {
    // Go: binder/binder.go:1479 bindContainer
    // All container nodes are kept on a linked list in declaration order. This list is used by
    // the getLocalNameOfContainer function in the type checker to validate that the local name
    // used for a container is unique.
    pub fn bind_container(&mut self, node: Node, container_flags: ContainerFlags) {
        let kind = node.kind();
        // Before we recurse into a node's children, we first save the existing parent, container
        // and block-container.  Then after we pop out of processing the children, we restore
        // these saved values.
        let save_container = self.container;
        let save_this_container = self.this_container;
        let saved_block_scope_container = self.block_scope_container;
        // Depending on what kind of node this is, we may have to adjust the current container
        // and block-container.   If the current node is a container, then it is automatically
        // considered the current block-container as well.  Also, for containers that we know
        // may contain locals, we eagerly initialize the .locals field. We do this because
        // it's highly likely that the .locals will be needed to place some child in (for example,
        // a parameter, or variable declaration).
        //
        // However, we do not proactively create the .locals for block-containers because it's
        // totally normal and common for block-containers to never actually have a block-scoped
        // variable in them.  We don't want to end up allocating an object for every 'block' we
        // run into when most of them won't be necessary.
        //
        // Finally, if this is a block-container, then we clear out any existing .locals object
        // it may contain within it.  This happens in incremental scenarios.  Because we can be
        // reusing a node from a previous compilation, that node may have had 'locals' created
        // for it.  We must clear this so we don't accidentally move any stale data forward from
        // a previous compilation.
        if container_flags.intersects(ContainerFlags::IS_CONTAINER) {
            self.container = node;
            self.block_scope_container = node;
            if container_flags.intersects(ContainerFlags::HAS_LOCALS) {
                // localsContainer := node
                // localsContainer.LocalsContainerData().locals = make(SymbolTable)
                // U1 (d): `Node::next_container` reads nil for other kinds.
                debug_assert!(is_locals_container(node), "container chain on a {:?}", kind);
                self.add_to_container_chain(node);
            }
        } else if container_flags.intersects(ContainerFlags::IS_BLOCK_SCOPED_CONTAINER) {
            self.block_scope_container = node;
            // U1 (d): as above.
            debug_assert!(is_locals_container(node), "container chain on a {:?}", kind);
            self.add_to_container_chain(node);
        }
        if container_flags.intersects(ContainerFlags::IS_THIS_CONTAINER) {
            self.this_container = node;
        }
        if container_flags.intersects(ContainerFlags::IS_CONTROL_FLOW_CONTAINER) {
            let save_current_flow = self.current_flow;
            let save_break_target = self.current_break_target;
            let save_continue_target = self.current_continue_target;
            let save_return_target = self.current_return_target;
            let save_exception_target = self.current_exception_target;
            let save_active_label_list = self.active_label_list.clone();
            let save_has_explicit_return = self.has_explicit_return;
            let save_seen_this_keyword = self.seen_this_keyword;
            let is_immediately_invoked = (container_flags
                .intersects(ContainerFlags::IS_FUNCTION_EXPRESSION)
                && !has_syntactic_modifier(node, ModifierFlags::ASYNC)
                && !is_generator_function_expression(node)
                && get_immediately_invoked_function_expression(node).is_some())
                || kind == SyntaxKind::ClassStaticBlockDeclaration;
            // A non-async, non-generator IIFE is considered part of the containing control flow. Return statements behave
            // similarly to break statements that exit to a label just past the statement body.
            if !is_immediately_invoked {
                let flow_start = self.new_flow_node(FlowFlags::START);
                self.current_flow = flow_start;
                if container_flags.intersects(
                    ContainerFlags::IS_FUNCTION_EXPRESSION
                        | ContainerFlags::IS_OBJECT_LITERAL_OR_CLASS_EXPRESSION_METHOD_OR_ACCESSOR,
                ) {
                    flow_data_mut(self, flow_start).node = node;
                }
            }
            // We create a return control flow graph for IIFEs and constructors. For constructors
            // we use the return control flow graph in strict property initialization checks.
            if is_immediately_invoked || kind == SyntaxKind::Constructor {
                self.current_return_target = self.new_flow_node(FlowFlags::BRANCH_LABEL);
            } else {
                self.current_return_target = FlowNodeId::NIL;
            }
            self.current_exception_target = FlowNodeId::NIL;
            self.current_break_target = FlowNodeId::NIL;
            self.current_continue_target = FlowNodeId::NIL;
            self.active_label_list = None;
            self.has_explicit_return = false;
            self.seen_this_keyword = false;
            self.bind_children_of_kind(node, kind);
            // Reset flags (for incremental scenarios)
            {
                let data = bound_mut(self, node);
                data.added_flags = data
                    .added_flags
                    .without(NodeFlags::REACHABILITY_AND_EMIT_FLAGS | NodeFlags::CONTAINS_THIS);
            }
            if !flow_data(self, self.current_flow)
                .flags
                .intersects(FlowFlags::UNREACHABLE)
                && container_flags.intersects(ContainerFlags::IS_FUNCTION_LIKE)
            {
                if has_body_data(node) && node_is_present(node.body()) {
                    let has_explicit_return = self.has_explicit_return;
                    let current_flow = self.current_flow;
                    let data = bound_mut(self, node);
                    data.added_flags |= NodeFlags::HAS_IMPLICIT_RETURN;
                    if has_explicit_return {
                        data.added_flags |= NodeFlags::HAS_EXPLICIT_RETURN;
                    }
                    data.end_flow_node = current_flow;
                }
            }
            if self.seen_this_keyword {
                bound_mut(self, node).added_flags |= NodeFlags::CONTAINS_THIS;
            }
            if kind == SyntaxKind::SourceFile {
                let emit_flags = self.emit_flags;
                bound_mut(self, node).added_flags |= emit_flags;
            }
            if self.current_return_target.is_some() {
                let current_return_target = self.current_return_target;
                let current_flow = self.current_flow;
                self.add_antecedent(current_return_target, current_flow);
                self.current_flow = self.finish_flow_label(current_return_target);
                if kind == SyntaxKind::Constructor
                    || kind == SyntaxKind::ClassStaticBlockDeclaration
                {
                    let current_flow = self.current_flow;
                    self.set_return_flow_node(node, current_flow);
                }
            }
            if !is_immediately_invoked {
                self.current_flow = save_current_flow;
            }
            self.current_break_target = save_break_target;
            self.current_continue_target = save_continue_target;
            self.current_return_target = save_return_target;
            self.current_exception_target = save_exception_target;
            self.active_label_list = save_active_label_list;
            self.has_explicit_return = save_has_explicit_return;
            if container_flags.intersects(ContainerFlags::PROPAGATES_THIS_KEYWORD) {
                self.seen_this_keyword = save_seen_this_keyword || self.seen_this_keyword;
            } else {
                self.seen_this_keyword = save_seen_this_keyword;
            }
        } else if container_flags.intersects(ContainerFlags::IS_INTERFACE) {
            let save_seen_this_keyword = self.seen_this_keyword;
            self.seen_this_keyword = false;
            self.bind_children_of_kind(node, kind);
            // ContainsThis cannot overlap with HasExtendedUnicodeEscape on Identifier
            let seen_this_keyword = self.seen_this_keyword;
            let data = bound_mut(self, node);
            if seen_this_keyword {
                data.added_flags |= NodeFlags::CONTAINS_THIS;
            } else {
                data.added_flags = data.added_flags.without(NodeFlags::CONTAINS_THIS);
            }
            self.seen_this_keyword = save_seen_this_keyword;
        } else {
            self.bind_children_of_kind(node, kind);
        }
        if is_source_file(node) && is_in_js_file(node) {
            // Binding of top-level JSTypeAliasDeclaration nodes is deferred to ensure CommonJS module
            // indicators, if any, are processed first.
            for statement in node.statements().iter() {
                if is_js_type_alias_declaration(statement) {
                    self.bind_block_scoped_declaration(
                        statement,
                        SymbolFlags::TYPE_ALIAS,
                        SymbolFlags::TYPE_ALIAS_EXCLUDES,
                    );
                }
            }
            if self.common_js_module_indicator.is_some() {
                self.declare_common_js_variable("module");
                self.declare_common_js_variable("exports");
            }
        }
        // PORT: Go `ast.IsExternalOrCommonJSModule(node.AsSourceFile())`; a SourceFile node here
        // is always the file being bound.
        if is_source_file(node) && binder_is_external_or_common_js_module(self)
            || is_ambient_module(node)
        {
            let node_symbol = bound(self, node).symbol;
            self.bind_common_js_type_exports(node_symbol);
        }
        self.container = save_container;
        self.this_container = save_this_container;
        self.block_scope_container = saved_block_scope_container;
    }

    // Go: binder/binder.go:1628 declareCommonJSVariable
    pub fn declare_common_js_variable(&mut self, name: &str) {
        let file = self.file;
        let locals = binder_get_locals(self, file);
        if self.symbols.get(locals, name).is_nil() {
            let symbol = self.new_symbol(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::MODULE_EXPORTS,
                name,
            );
            let declarations = self.new_single_declaration(file);
            let value_declaration = declarations[0];
            {
                let s = self.symbols.sym_mut(symbol);
                s.declarations = declarations.clone();
                s.value_declaration = value_declaration;
            }
            if name == "module" {
                let exports_property = self.new_symbol(
                    SymbolFlags::MODULE_EXPORTS | SymbolFlags::PROPERTY,
                    "exports",
                );
                {
                    let p = self.symbols.sym_mut(exports_property);
                    p.declarations = declarations;
                    p.value_declaration = value_declaration;
                    p.parent = symbol;
                }
                let members = self.symbols.new_table();
                self.symbols.sym_mut(symbol).members = members;
                self.symbols.set(members, "exports", exports_property);
            }
            self.symbols.set(locals, name, symbol);
        }
    }

    // Go: binder/binder.go:1646 bindChildren
    pub fn bind_children(&mut self, node: Node) {
        self.bind_children_of_kind(node, node.kind());
    }

    /// `bind_children` for a caller that already read `node.kind()`.
    pub fn bind_children_of_kind(&mut self, node: Node, kind: SyntaxKind) {
        let save_in_assignment_pattern = self.in_assignment_pattern;
        // Most nodes aren't valid in an assignment pattern, so we clear the value here
        // and set it before we descend into nodes that could actually be part of an assignment pattern.
        self.in_assignment_pattern = false;

        if self.current_flow == self.unreachable_flow {
            // PORT: Go `if flowNodeData := node.FlowNodeData(); flowNodeData != nil { flowNodeData.FlowNode = nil }`
            // is exactly `setFlowNode(node, nil)`.
            self.set_flow_node(node, FlowNodeId::NIL);
            if is_potentially_executable_node(node) {
                bound_mut(self, node).added_flags |= NodeFlags::UNREACHABLE;
            }
            self.bind_each_child(node);
            self.in_assignment_pattern = save_in_assignment_pattern;
            return;
        }

        if (SyntaxKind::FIRST_STATEMENT as u16) <= (kind as u16)
            && (kind as u16) <= (SyntaxKind::LAST_STATEMENT as u16)
        {
            // PORT: Go sets `FlowNodeData().FlowNode` when the node has flow data, which is `setFlowNode`.
            let current_flow = self.current_flow;
            self.set_flow_node(node, current_flow);
        }

        match kind {
            SyntaxKind::WhileStatement => self.bind_while_statement(node),
            SyntaxKind::DoStatement => self.bind_do_statement(node),
            SyntaxKind::ForStatement => self.bind_for_statement(node),
            SyntaxKind::ForInStatement | SyntaxKind::ForOfStatement => {
                self.bind_for_in_or_for_of_statement(node)
            }
            SyntaxKind::IfStatement => self.bind_if_statement(node),
            SyntaxKind::ReturnStatement => self.bind_return_statement(node),
            SyntaxKind::ThrowStatement => self.bind_throw_statement(node),
            SyntaxKind::BreakStatement => self.bind_break_statement(node),
            SyntaxKind::ContinueStatement => self.bind_continue_statement(node),
            SyntaxKind::TryStatement => self.bind_try_statement(node),
            SyntaxKind::SwitchStatement => self.bind_switch_statement(node),
            SyntaxKind::CaseBlock => self.bind_case_block(node),
            SyntaxKind::CaseClause | SyntaxKind::DefaultClause => {
                self.bind_case_or_default_clause(node)
            }
            SyntaxKind::ExpressionStatement => self.bind_expression_statement(node),
            SyntaxKind::LabeledStatement => self.bind_labeled_statement(node),
            SyntaxKind::PrefixUnaryExpression => self.bind_prefix_unary_expression_flow(node),
            SyntaxKind::PostfixUnaryExpression => self.bind_postfix_unary_expression_flow(node),
            SyntaxKind::BinaryExpression => {
                if is_destructuring_assignment(node) {
                    // Carry over whether we are in an assignment pattern to
                    // binary expressions that could actually be an initializer
                    self.in_assignment_pattern = save_in_assignment_pattern;
                    self.bind_destructuring_assignment_flow(node);
                    return;
                }
                self.bind_binary_expression_flow(node);
            }
            SyntaxKind::DeleteExpression => self.bind_delete_expression_flow(node),
            SyntaxKind::ConditionalExpression => self.bind_conditional_expression_flow(node),
            SyntaxKind::VariableDeclaration => self.bind_variable_declaration_flow(node),
            SyntaxKind::PropertyAccessExpression | SyntaxKind::ElementAccessExpression => {
                self.bind_access_expression_flow(node);
            }
            SyntaxKind::CallExpression => self.bind_call_expression_flow(node),
            SyntaxKind::NonNullExpression => self.bind_non_null_expression_flow(node),
            SyntaxKind::SourceFile => {
                // PORT: Go `sourceFile.Statements` (the NodeList field) via `StatementList()`.
                self.bind_each_statement_functions_first(node.statement_list());
                self.bind(node.end_of_file_token());
            }
            SyntaxKind::Block | SyntaxKind::ModuleBlock => {
                self.bind_each_statement_functions_first(node.statement_list());
            }
            SyntaxKind::BindingElement => self.bind_binding_element_flow(node),
            SyntaxKind::Parameter => self.bind_parameter_flow(node),
            SyntaxKind::ObjectLiteralExpression
            | SyntaxKind::ArrayLiteralExpression
            | SyntaxKind::PropertyAssignment
            | SyntaxKind::SpreadElement => {
                self.in_assignment_pattern = save_in_assignment_pattern;
                self.bind_each_child(node);
            }
            _ => self.bind_each_child(node),
        }
        self.in_assignment_pattern = save_in_assignment_pattern;
    }

    // Go: binder/binder.go:1745 bindEachChild
    // PERF: R2-5. A published store node walks its child links
    // (`frozen_store_children`): the same children in the same order as
    // `for_each_child`, from the first child and next sibling of each slot,
    // so a node that the binder only passes through (type references,
    // unions) never loads its data.
    // bindfast1: a node of a freeable file version (an edited file) walks
    // the link column of its version (`version_links`), so its walk skips
    // the scoped node data reads too.
    // Debug builds compare the walk with `for_each_child`.
    pub fn bind_each_child(&mut self, node: Node) {
        // A clone of the guard (`None` for a static file), so the walk does
        // not borrow `self`.
        let version_links = self.version_links.clone();
        let children = frozen_store_children(node).or_else(|| {
            version_links
                .as_ref()
                .and_then(|links| links.children(node))
        });
        if let Some(children) = children {
            debug_assert!(
                children.eq(node.iter_children()),
                "R2-5 child links differ from for_each_child"
            );
            for child in children {
                // Go `ForEachChild` stops when the visitor returns true.
                if self.bind(child) {
                    break;
                }
            }
            return;
        }
        // PORT: Go passes the cached `b.bindFunc` closure; a fresh closure is equivalent.
        node.for_each_child(&mut |child: Node| self.bind(child));
    }

    // Go: binder/binder.go:1749 bindEach
    pub fn bind_each(&mut self, nodes: &[Node]) {
        for &node in nodes {
            self.bind(node);
        }
    }

    // Go: binder/binder.go:1755 bindNodeList
    pub fn bind_node_list(&mut self, node_list: NodeList) {
        if !node_list.is_nil() {
            for node in node_list.nodes() {
                self.bind(node);
            }
        }
    }

    // Go: binder/binder.go:1761 bindModifiers
    pub fn bind_modifiers(&mut self, modifiers: ModifierList) {
        if !modifiers.is_nil() {
            for node in modifiers.nodes() {
                self.bind(node);
            }
        }
    }

    // Go: binder/binder.go:1767 bindEachStatementFunctionsFirst
    pub fn bind_each_statement_functions_first(&mut self, statements: NodeList) {
        let nodes = statements.nodes();
        for node in nodes.iter() {
            if node.kind() == SyntaxKind::FunctionDeclaration {
                self.bind(node);
            }
        }
        for node in nodes.iter() {
            if node.kind() != SyntaxKind::FunctionDeclaration {
                self.bind(node);
            }
        }
    }

    // Go: binder/binder.go:1780 setContinueTarget
    pub fn set_continue_target(&mut self, node: Node, target: FlowNodeId) -> FlowNodeId {
        let mut label = self.active_label_list.clone();
        let mut node = node;
        while let Some(current) = label.clone() {
            if node.parent().kind() != SyntaxKind::LabeledStatement {
                break;
            }
            current.borrow_mut().continue_target = target;
            label = current.borrow().next.clone();
            node = node.parent();
        }
        target
    }

    // Go: binder/binder.go:1790 doWithConditionalBranches
    pub fn do_with_conditional_branches(
        &mut self,
        action: &mut dyn FnMut(&mut Binder, Node) -> bool,
        value: Node,
        true_target: FlowNodeId,
        false_target: FlowNodeId,
    ) {
        let saved_true_target = self.current_true_target;
        let saved_false_target = self.current_false_target;
        self.current_true_target = true_target;
        self.current_false_target = false_target;
        action(self, value);
        self.current_true_target = saved_true_target;
        self.current_false_target = saved_false_target;
    }

    // Go: binder/binder.go:1800 bindCondition
    pub fn bind_condition(
        &mut self,
        node: Node,
        true_target: FlowNodeId,
        false_target: FlowNodeId,
    ) {
        self.do_with_conditional_branches(
            &mut |b: &mut Binder, n: Node| b.bind(n),
            node,
            true_target,
            false_target,
        );
        if node.is_nil()
            || !is_logical_assignment_expression(node)
                && !is_logical_expression(node)
                && !(is_optional_chain(node) && is_outermost_optional_chain(node))
        {
            let current_flow = self.current_flow;
            let true_flow =
                self.create_flow_condition(FlowFlags::TRUE_CONDITION, current_flow, node);
            self.add_antecedent(true_target, true_flow);
            let current_flow = self.current_flow;
            let false_flow =
                self.create_flow_condition(FlowFlags::FALSE_CONDITION, current_flow, node);
            self.add_antecedent(false_target, false_flow);
        }
    }

    // Go: binder/binder.go:1808 bindIterativeStatement
    pub fn bind_iterative_statement(
        &mut self,
        node: Node,
        break_target: FlowNodeId,
        continue_target: FlowNodeId,
    ) {
        let save_break_target = self.current_break_target;
        let save_continue_target = self.current_continue_target;
        self.current_break_target = break_target;
        self.current_continue_target = continue_target;
        self.bind(node);
        self.current_break_target = save_break_target;
        self.current_continue_target = save_continue_target;
    }
}
