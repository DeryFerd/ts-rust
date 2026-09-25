//! Go `binder/referenceresolver.go`.
//!
//! PORT: Go `ReferenceResolver` is an interface with one implementation
//! (`referenceResolver`). Here it is the struct `ReferenceResolver`.
//! Go hook closures capture the checker. Here each hook is a plain function
//! that takes the checker as its first argument, and each resolver method
//! takes `c: &mut Checker` to pass to the hooks. The fallback name resolver
//! (`crate::checker::NameResolver`) also needs the checker.

use crate::prelude::*;

use std::cell::Cell;
use ts_diagnostics::Message;

/// Go `func(location *ast.Node, name string, meaning ast.SymbolFlags, nameNotFoundMessage *diagnostics.Message, isUse bool, excludeGlobals bool) *ast.Symbol`.
pub type ResolveNameHook =
    fn(&mut Checker, Node, &str, SymbolFlags, Option<&'static Message>, bool, bool) -> SymbolId;

// Go: binder/referenceresolver.go:18 ReferenceResolverHooks
#[derive(Clone, Copy, Default)]
pub struct ReferenceResolverHooks {
    pub resolve_name: Option<ResolveNameHook>,
    pub get_resolved_symbol: Option<fn(&mut Checker, Node) -> SymbolId>,
    pub get_merged_symbol: Option<fn(&mut Checker, SymbolId) -> SymbolId>,
    pub get_parent_of_symbol: Option<fn(&mut Checker, SymbolId) -> SymbolId>,
    pub get_symbol_of_declaration: Option<fn(&mut Checker, Node) -> SymbolId>,
    pub get_type_only_alias_declaration: Option<fn(&mut Checker, SymbolId, SymbolFlags) -> Node>,
    pub get_export_symbol_of_value_symbol_if_exported:
        Option<fn(&mut Checker, SymbolId) -> SymbolId>,
    pub get_element_access_expression_name: Option<fn(&mut Checker, Node) -> (String, bool)>,
}

// Go: binder/referenceresolver.go:31 referenceResolver
pub struct ReferenceResolver {
    // PORT: Go `*NameResolver`, created lazily. `None` is Go nil.
    pub resolver: Option<NameResolver>,
    pub options: &'static CompilerOptions,
    pub hooks: ReferenceResolverHooks,
}

// Go: binder/referenceresolver.go:37 NewReferenceResolver
pub fn new_reference_resolver(
    options: &'static CompilerOptions,
    hooks: ReferenceResolverHooks,
) -> ReferenceResolver {
    ReferenceResolver {
        resolver: None,
        options,
        hooks,
    }
}

impl ReferenceResolver {
    // Go: binder/referenceresolver.go:44 getResolvedSymbol
    fn get_resolved_symbol(&self, c: &mut Checker, node: Node) -> SymbolId {
        if node.is_some() {
            if let Some(get_resolved_symbol) = self.hooks.get_resolved_symbol {
                return get_resolved_symbol(c, node);
            }
        }
        SymbolId::NIL
    }

    // Go: binder/referenceresolver.go:53 getMergedSymbol
    fn get_merged_symbol(&self, c: &mut Checker, symbol: SymbolId) -> SymbolId {
        if symbol.is_some() {
            if let Some(get_merged_symbol) = self.hooks.get_merged_symbol {
                return get_merged_symbol(c, symbol);
            }
            return symbol;
        }
        SymbolId::NIL
    }

    // Go: binder/referenceresolver.go:63 getParentOfSymbol
    fn get_parent_of_symbol(&self, c: &mut Checker, symbol: SymbolId) -> SymbolId {
        if symbol.is_some() {
            if let Some(get_parent_of_symbol) = self.hooks.get_parent_of_symbol {
                return get_parent_of_symbol(c, symbol);
            }
            return c.sym(symbol).parent;
        }
        SymbolId::NIL
    }

    // Go: binder/referenceresolver.go:73 getSymbolOfDeclaration
    fn get_symbol_of_declaration(&self, c: &mut Checker, declaration: Node) -> SymbolId {
        if declaration.is_some() {
            if let Some(get_symbol_of_declaration) = self.hooks.get_symbol_of_declaration {
                return get_symbol_of_declaration(c, declaration);
            }
            return declaration.symbol();
        }
        SymbolId::NIL
    }

    // Go: binder/referenceresolver.go:83 getReferencedValueSymbol
    fn get_referenced_value_symbol(
        &mut self,
        c: &mut Checker,
        reference: Node,
        start_in_declaration_container: bool,
    ) -> SymbolId {
        let resolved_symbol = self.get_resolved_symbol(c, reference);
        if resolved_symbol.is_some() {
            return resolved_symbol;
        }

        let mut location = reference;
        if start_in_declaration_container
            && reference.parent().is_some()
            && is_declaration(reference.parent())
            && reference.parent().name() == reference
        {
            location = get_declaration_container(reference.parent());
        }

        let meaning = SymbolFlags::EXPORT_VALUE | SymbolFlags::VALUE | SymbolFlags::ALIAS;
        if let Some(resolve_name) = self.hooks.resolve_name {
            return resolve_name(
                c,
                location,
                reference.text(),
                meaning,
                None,  /*nameNotFoundMessage*/
                false, /*isUse*/
                false, /*excludeGlobals*/
            );
        }

        let options = self.options;
        let resolver = self.resolver.get_or_insert_with(|| NameResolver {
            compiler_options: options,
            get_symbol_of_declaration: None,
            error: None,
            globals: SymbolTable::NIL,
            arguments_symbol: Cell::new(SymbolId::NIL),
            require_symbol: SymbolId::NIL,
            lookup: None,
            symbol_referenced: None,
            set_requires_scope_change_cache: None,
            get_requires_scope_change_cache: None,
            on_property_with_invalid_initializer: None,
            on_failed_to_resolve_symbol: None,
            on_successfully_resolved_symbol: None,
        });

        resolver.resolve(
            c,
            location,
            reference.text(),
            meaning,
            None,  /*nameNotFoundMessage*/
            false, /*isUse*/
            false, /*excludeGlobals*/
        )
    }

    // Go: binder/referenceresolver.go:107 isTypeOnlyAliasDeclaration
    fn is_type_only_alias_declaration(&self, c: &mut Checker, symbol: SymbolId) -> bool {
        if symbol.is_some() {
            if let Some(get_type_only_alias_declaration) =
                self.hooks.get_type_only_alias_declaration
            {
                return get_type_only_alias_declaration(c, symbol, SymbolFlags::VALUE).is_some();
            }

            let mut node = self.get_declaration_of_alias_symbol(c, symbol);
            while node.is_some() {
                match node.kind() {
                    SyntaxKind::ImportEqualsDeclaration | SyntaxKind::ExportDeclaration => {
                        return node.is_type_only();
                    }
                    SyntaxKind::ImportClause
                    | SyntaxKind::ImportSpecifier
                    | SyntaxKind::ExportSpecifier => {
                        if node.is_type_only() {
                            return true;
                        }
                        node = node.parent();
                        continue;
                    }
                    SyntaxKind::NamedImports | SyntaxKind::NamedExports => {
                        node = node.parent();
                        continue;
                    }
                    _ => {}
                }
                break;
            }
        }
        false
    }

    // Go: binder/referenceresolver.go:134 getDeclarationOfAliasSymbol
    fn get_declaration_of_alias_symbol(&self, c: &Checker, symbol: SymbolId) -> Node {
        c.sym(symbol)
            .declarations
            .iter()
            .rev()
            .copied()
            .find(|&d| is_alias_symbol_declaration(d))
            .unwrap_or(Node::NIL)
    }

    // Go: binder/referenceresolver.go:138 getExportSymbolOfValueSymbolIfExported
    fn get_export_symbol_of_value_symbol_if_exported(
        &self,
        c: &mut Checker,
        mut symbol: SymbolId,
    ) -> SymbolId {
        if symbol.is_some() {
            if let Some(get_export_symbol_of_value_symbol_if_exported) =
                self.hooks.get_export_symbol_of_value_symbol_if_exported
            {
                return get_export_symbol_of_value_symbol_if_exported(c, symbol);
            }
            if c.sym(symbol).flags.intersects(SymbolFlags::EXPORT_VALUE)
                && c.sym(symbol).export_symbol.is_some()
            {
                symbol = c.sym(symbol).export_symbol;
            }
            return self.get_merged_symbol(c, symbol);
        }
        SymbolId::NIL
    }

    // Go: binder/referenceresolver.go:151 GetReferencedExportContainer
    pub fn get_referenced_export_container(
        &mut self,
        c: &mut Checker,
        node: Node,
        prefix_locals: bool,
    ) -> Node /*SourceFile|ModuleDeclaration|EnumDeclaration*/ {
        // When resolving the export for the name of a module or enum
        // declaration, we need to start resolution at the declaration's container.
        // Otherwise, we could incorrectly resolve the export as the
        // declaration if it contains an exported member with the same name.
        let start_in_declaration_container = node.parent().is_some()
            && (node.parent().kind() == SyntaxKind::ModuleDeclaration
                || node.parent().kind() == SyntaxKind::EnumDeclaration)
            && node == node.parent().name();
        let mut symbol = self.get_referenced_value_symbol(c, node, start_in_declaration_container);
        if symbol.is_some() {
            if c.sym(symbol).flags.intersects(SymbolFlags::EXPORT_VALUE) {
                // If we reference an exported entity within the same module declaration, then whether
                // we prefix depends on the kind of entity. SymbolFlags.ExportHasLocal encompasses all the
                // kinds that we do NOT prefix.
                let export_symbol = c.sym(symbol).export_symbol;
                let export_symbol = self.get_merged_symbol(c, export_symbol);
                let export_flags = c.sym(export_symbol).flags;
                if !prefix_locals
                    && export_flags.intersects(SymbolFlags::EXPORT_HAS_LOCAL)
                    && !export_flags.intersects(SymbolFlags::VARIABLE)
                {
                    return Node::NIL;
                }
                symbol = export_symbol;
            }
            let parent_symbol = self.get_parent_of_symbol(c, symbol);
            if parent_symbol.is_some() {
                let parent_value_declaration = c.sym(parent_symbol).value_declaration;
                if c.sym(parent_symbol)
                    .flags
                    .intersects(SymbolFlags::VALUE_MODULE)
                    && parent_value_declaration.is_some()
                    && parent_value_declaration.kind() == SyntaxKind::SourceFile
                {
                    let symbol_file = parent_value_declaration;
                    let reference_file = get_source_file_of_node(node);
                    // If `node` accesses an export and that export isn't in the same file, then symbol is a namespace export, so return nil.
                    let symbol_is_umd_export = symbol_file != reference_file;
                    if symbol_is_umd_export {
                        return Node::NIL;
                    }
                    return symbol_file;
                }
                let is_matching_container = |n: Node| -> bool {
                    (n.kind() == SyntaxKind::ModuleDeclaration
                        || n.kind() == SyntaxKind::EnumDeclaration)
                        && self.get_symbol_of_declaration(c, n) == parent_symbol
                };
                return find_ancestor(node.parent(), is_matching_container);
            }
        }

        Node::NIL
    }

    // Go: binder/referenceresolver.go:190 GetReferencedImportDeclaration
    pub fn get_referenced_import_declaration(&mut self, c: &mut Checker, node: Node) -> Node {
        let symbol =
            self.get_referenced_value_symbol(c, node, false /*startInDeclarationContainer*/);
        if symbol.is_some() {
            // We should only get the declaration of an alias if there isn't a local value
            // declaration for the symbol
            if is_non_local_alias(&c.symbols, symbol, SymbolFlags::VALUE /*excludes*/)
                && !self.is_type_only_alias_declaration(c, symbol)
            {
                return self.get_declaration_of_alias_symbol(c, symbol);
            }
        }

        Node::NIL
    }

    // Go: binder/referenceresolver.go:202 GetReferencedValueDeclaration
    pub fn get_referenced_value_declaration(&mut self, c: &mut Checker, node: Node) -> Node {
        let symbol =
            self.get_referenced_value_symbol(c, node, false /*startInDeclarationContainer*/);
        if symbol.is_some() {
            let symbol = self.get_export_symbol_of_value_symbol_if_exported(c, symbol);
            return c.sym(symbol).value_declaration;
        }
        Node::NIL
    }

    // Go: binder/referenceresolver.go:209 GetReferencedValueDeclarations
    pub fn get_referenced_value_declarations(&mut self, c: &mut Checker, node: Node) -> Vec<Node> {
        let mut declarations = Vec::new();
        let symbol =
            self.get_referenced_value_symbol(c, node, false /*startInDeclarationContainer*/);
        if symbol.is_some() {
            let symbol = self.get_export_symbol_of_value_symbol_if_exported(c, symbol);
            for &declaration in &c.sym(symbol).declarations {
                match declaration.kind() {
                    SyntaxKind::VariableDeclaration
                    | SyntaxKind::Parameter
                    | SyntaxKind::BindingElement
                    | SyntaxKind::PropertyDeclaration
                    | SyntaxKind::PropertyAssignment
                    | SyntaxKind::ShorthandPropertyAssignment
                    | SyntaxKind::EnumMember
                    | SyntaxKind::ObjectLiteralExpression
                    | SyntaxKind::FunctionDeclaration
                    | SyntaxKind::FunctionExpression
                    | SyntaxKind::ArrowFunction
                    | SyntaxKind::ClassDeclaration
                    | SyntaxKind::ClassExpression
                    | SyntaxKind::EnumDeclaration
                    | SyntaxKind::MethodDeclaration
                    | SyntaxKind::GetAccessor
                    | SyntaxKind::SetAccessor
                    | SyntaxKind::ModuleDeclaration => declarations.push(declaration),
                    _ => {}
                }
            }
        }
        declarations
    }

    // Go: binder/referenceresolver.go:240 GetElementAccessExpressionName
    pub fn get_element_access_expression_name(&self, c: &mut Checker, expression: Node) -> String {
        if expression.is_some() {
            if let Some(get_element_access_expression_name) =
                self.hooks.get_element_access_expression_name
            {
                let (name, ok) = get_element_access_expression_name(c, expression);
                if ok {
                    return name;
                }
            }
        }
        String::new()
    }

    // Go: binder/referenceresolver.go:251 GetReferencedMemberValueDeclaration
    pub fn get_referenced_member_value_declaration(&self, c: &mut Checker, node: Node) -> Node {
        // member references are `this.something` or `this[something]`, so should always simply have a resolved symbol
        let mut s = self.get_resolved_symbol(c, node);
        if s.is_nil() && node.symbol().is_some() {
            // might be a declaration instead of a ref, get the merged declaration symbol
            s = self.get_merged_symbol(c, node.symbol());
        }
        if s.is_nil() {
            return Node::NIL;
        }
        let s = self.get_export_symbol_of_value_symbol_if_exported(c, s);
        c.sym(s).value_declaration
    }
}
