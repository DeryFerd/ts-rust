//! Port of Go `transformers/moduletransforms/utilities.go`.

use crate::frontend::outputpaths::get_output_extension;
use crate::frontend::tspath;
use crate::prelude::*;

// Go: transformers/moduletransforms/utilities.go:12 isDeclarationNameOfEnumOrNamespace
pub(crate) fn is_declaration_name_of_enum_or_namespace(
    emit_context: &EmitContext,
    node: Node,
) -> bool {
    let original = emit_context.most_original(node);
    if original.is_some() && original.parent().is_some() {
        match original.parent().kind() {
            SyntaxKind::EnumDeclaration | SyntaxKind::ModuleDeclaration => {
                return original == original.parent().name();
            }
            _ => {}
        }
    }
    false
}

// Go: transformers/moduletransforms/utilities.go:22 rewriteModuleSpecifier
pub(crate) fn rewrite_module_specifier(
    emit_context: &EmitContext,
    node: Node,
    compiler_options: &CompilerOptions,
) -> Node {
    if node.is_nil()
        || !is_string_literal(node)
        || !should_rewrite_module_specifier(node.text(), compiler_options)
    {
        return node;
    }
    let updated_text = tspath::change_extension(
        node.text(),
        get_output_extension(node.text(), compiler_options.jsx),
    );
    if updated_text != node.text() {
        let updated = emit_context
            .factory()
            .new_string_literal(updated_text, node.token_flags());
        emit_context.set_original(updated, node);
        emit_context.assign_comment_and_source_map_ranges(updated, node);
        return updated;
    }
    node
}

// Go: core/core.go:687 ShouldRewriteModuleSpecifier
// PORT: the checker copy (`checker_p17::core_p17`) is private, so this unit
// keeps its own copy of the Go `core` helper.
pub(crate) fn should_rewrite_module_specifier(
    specifier: &str,
    compiler_options: &CompilerOptions,
) -> bool {
    compiler_options
        .rewrite_relative_import_extensions
        .is_true()
        && tspath::path_is_relative(specifier)
        && !tspath::is_declaration_file_name(specifier)
        && tspath::has_ts_file_extension(specifier)
}

// Go: transformers/moduletransforms/utilities.go:37 createEmptyImports
pub(crate) fn create_empty_imports(factory: &NodeFactory) -> Node {
    factory.new_export_declaration(
        ModifierList::NIL, /*modifiers*/
        false,             /*isTypeOnly*/
        factory.new_named_exports(factory.new_node_list(&[])),
        Node::NIL, /*moduleSpecifier*/
        Node::NIL, /*attributes*/
    )
}

// Go: transformers/moduletransforms/utilities.go:55 getExternalModuleNameLiteral
/// Get the name of a target module from an import/export declaration as should be written in the emitted output.
/// The emitted output name can be different from the input if:
///  1. The module has a /// <amd-module name="<new name>" />
///  2. --out or --outFile is used, making the name relative to the rootDir
///     3- The containing SourceFile has an entry in renamedDependencies for the import as requested by some module loaders (e.g. System).
///
/// Otherwise, a new StringLiteral node representing the module name will be returned.
// PORT: Go `host any` is always nil and unused, so it is dropped. Go `resolver`
// is a nilable interface, so it is an `Option`.
pub(crate) fn get_external_module_name_literal(
    factory: &NodeFactory,
    import_node: Node, /*ImportDeclaration | ExportDeclaration | ImportEqualsDeclaration | ImportCall*/
    source_file: Node,
    resolver: Option<&dyn EmitResolver>,
    compiler_options: &CompilerOptions,
) -> Node {
    let module_name = get_external_module_name(import_node);
    if module_name.is_some() && is_string_literal(module_name) {
        let mut name =
            try_get_module_name_from_declaration(import_node, factory, resolver, compiler_options);
        if name.is_nil() {
            name = try_rename_external_module(factory, module_name, source_file);
        }
        if name.is_nil() {
            // !!! propagate token flags (will produce new diffs)
            name = factory.new_string_literal(module_name.text(), TokenFlags::NONE);
        }
        return name;
    }
    Node::NIL
}

// Go: transformers/moduletransforms/utilities.go:77 tryGetModuleNameFromFile
/// Get the name of a module as should be written in the emitted output.
/// The emitted output name can be different from the input if:
///  1. The module has a /// <amd-module name="<new name>" />
///  2. --out or --outFile is used, making the name relative to the rootDir
///
/// Otherwise, a new StringLiteral node representing the module name will be returned.
pub(crate) fn try_get_module_name_from_file(
    _factory: &NodeFactory,
    file: Node,
    _options: &CompilerOptions,
) -> Node {
    if file.is_nil() {
        return Node::NIL;
    }
    // !!!
    // if file.moduleName {
    // 	return factory.createStringLiteral(file.moduleName)
    // }
    Node::NIL
}

// Go: transformers/moduletransforms/utilities.go:88 tryGetModuleNameFromDeclaration
pub(crate) fn try_get_module_name_from_declaration(
    declaration: Node, /*ImportEqualsDeclaration | ImportDeclaration | ExportDeclaration | ImportCall*/
    factory: &NodeFactory,
    resolver: Option<&dyn EmitResolver>,
    compiler_options: &CompilerOptions,
) -> Node {
    let Some(resolver) = resolver else {
        return Node::NIL;
    };
    try_get_module_name_from_file(
        factory,
        resolver.get_external_module_file_from_declaration(declaration),
        compiler_options,
    )
}

// Go: transformers/moduletransforms/utilities.go:96 getExternalModuleNameFromPath
/// Resolves a local path to a path which is absolute to the base of the emit
pub(crate) fn get_external_module_name_from_path(
    _file_name: &str,
    _reference_path: &str,
) -> String {
    // !!!
    String::new()
}

// Go: transformers/moduletransforms/utilities.go:103 tryRenameExternalModule
/// Some bundlers (SystemJS builder) sometimes want to rename dependencies.
/// Here we check if alternative name was provided for a given moduleName and return it if possible.
pub(crate) fn try_rename_external_module(
    _factory: &NodeFactory,
    _module_name: Node,
    _source_file: Node,
) -> Node {
    // !!!
    Node::NIL
}

// Go: transformers/moduletransforms/utilities.go:108 isFileLevelReservedGeneratedIdentifier
pub(crate) fn is_file_level_reserved_generated_identifier(
    emit_context: &EmitContext,
    name: Node,
) -> bool {
    match emit_context.get_auto_generate_info(name) {
        Some(info) => {
            info.flags.is_file_level()
                && info.flags.is_optimistic()
                && info.flags.is_reserved_in_nested_scopes()
        }
        None => false,
    }
}

// Go: transformers/moduletransforms/utilities.go:115 isSimpleInlineableExpression
/// A simple inlinable expression is an expression which can be copied into multiple locations
/// without risk of repeating any sideeffects and whose value could not possibly change between
/// any such locations
pub(crate) fn is_simple_inlineable_expression(expression: Node) -> bool {
    !is_identifier(expression)
        && crate::transformers::utilities::is_simple_copiable_expression(expression)
}

/// Go `ast.IsExternalModule(file)` for a parsed or factory-made SourceFile.
// PORT: `ast::is_external_module` reads `SourceFileInfo`, which only parsed
// files have. Earlier transforms hand this unit factory SourceFiles, so read
// the indicator through `source_file_parser_fields`.
pub(crate) fn is_external_module_file(file: Node) -> bool {
    external_module_indicator_of(file).is_some()
}

/// Go `file.ExternalModuleIndicator` for a parsed or factory-made SourceFile.
pub(crate) fn external_module_indicator_of(file: Node) -> Node {
    if is_synthetic_node(file) {
        return source_file_parser_fields(file).external_module_indicator;
    }
    source_file_info(file).external_module_indicator
}

/// Go `file.CommonJSModuleIndicator` for a parsed or factory-made SourceFile.
pub(crate) fn common_js_module_indicator_of(file: Node) -> Node {
    if is_synthetic_node(file) {
        return source_file_parser_fields(file).common_js_module_indicator;
    }
    source_file_info(file).common_js_module_indicator
}

/// Go `file.IsDeclarationFile` for a parsed or factory-made SourceFile.
pub(crate) fn is_declaration_file_of(file: Node) -> bool {
    if is_synthetic_node(file) {
        return source_file_parser_fields(file).is_declaration_file;
    }
    source_file_info(file).is_declaration_file
}

// Go: ast/utilities.go IsEffectiveExternalModule
/// Go `ast.IsEffectiveExternalModule` for a parsed or factory-made SourceFile.
// PORT: see `is_external_module_file`.
pub(crate) fn is_effective_external_module_file(
    node: Node,
    compiler_options: &CompilerOptions,
) -> bool {
    is_external_module_file(node)
        || (is_common_js_containing_module_kind(compiler_options.get_emit_module_kind())
            && common_js_module_indicator_of(node).is_some())
}
