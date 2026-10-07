// Go: internal/typeparser/module_identifier.go

use crate::effect::typeparser::*;
use crate::prelude::*;

/// FindEffectModuleIdentifier finds the local name for the Effect module from imports.
/// It checks both namespace imports (import * as X from "effect/Effect") and
/// named imports (import { Effect } from "effect"), falling back to "Effect".
pub fn find_effect_module_identifier(sf: Node) -> String {
    if sf.is_nil() {
        return "Effect".to_string();
    }
    for stmt in sf.statements().iter() {
        if stmt.kind() != SyntaxKind::ImportDeclaration {
            continue;
        }
        let import_decl = stmt;
        if import_decl.module_specifier().is_nil() || import_decl.import_clause().is_nil() {
            continue;
        }
        let mut module_name = get_text_of_node(import_decl.module_specifier());
        if module_name.len() >= 2
            && (module_name.as_bytes()[0] == b'"' || module_name.as_bytes()[0] == b'\'')
        {
            module_name = module_name[1..module_name.len() - 1].to_string();
        }

        let clause = import_decl.import_clause();
        let named_bindings = clause.named_bindings();
        if named_bindings.is_nil() {
            continue;
        }

        // Check namespace import: import * as X from "effect/Effect"
        if module_name == "effect/Effect" && named_bindings.kind() == SyntaxKind::NamespaceImport {
            let ns_import = named_bindings;
            if ns_import.name().is_some() {
                return get_text_of_node(ns_import.name());
            }
        }

        // Check named imports: import { Effect } from "effect"
        if module_name == "effect" && named_bindings.kind() == SyntaxKind::NamedImports {
            let named_imports = named_bindings;
            // PORT: Go skips a nil Elements list; a nil list has no elements here.
            for elem in named_imports.elements().iter() {
                let spec = elem;
                let imported_name = if spec.property_name().is_some() {
                    get_text_of_node(spec.property_name())
                } else {
                    get_text_of_node(spec.name())
                };
                if imported_name == "Effect" {
                    return get_text_of_node(spec.name());
                }
            }
        }
    }
    "Effect".to_string()
}

/// FindModuleIdentifier resolves the imported identifier name for the given export
/// from the "effect" package. Falls back to the provided exportName if not found.
/// It checks named imports: import { ExportName as Alias } from "effect".
pub fn find_module_identifier(sf: Node, export_name: &str) -> String {
    if sf.is_nil() {
        return export_name.to_string();
    }
    for stmt in sf.statements().iter() {
        if stmt.kind() != SyntaxKind::ImportDeclaration {
            continue;
        }
        let import_decl = stmt;
        if import_decl.module_specifier().is_nil() {
            continue;
        }
        let mut module_name = get_text_of_node(import_decl.module_specifier());
        if module_name.len() >= 2
            && (module_name.as_bytes()[0] == b'"' || module_name.as_bytes()[0] == b'\'')
        {
            module_name = module_name[1..module_name.len() - 1].to_string();
        }

        if import_decl.import_clause().is_nil() {
            continue;
        }
        let clause = import_decl.import_clause();
        let named_bindings = clause.named_bindings();
        if named_bindings.is_nil() {
            continue;
        }

        // Check namespace import: import * as X from "effect/<exportName>"
        if module_name == format!("effect/{export_name}")
            && named_bindings.kind() == SyntaxKind::NamespaceImport
        {
            let ns_import = named_bindings;
            if ns_import.name().is_some() {
                return get_text_of_node(ns_import.name());
            }
        }

        // Check named imports: import { ExportName as Alias } from "effect"
        if module_name == "effect" && named_bindings.kind() == SyntaxKind::NamedImports {
            let named_imports = named_bindings;
            for elem in named_imports.elements().iter() {
                let spec = elem;
                let imported_name = if spec.property_name().is_some() {
                    get_text_of_node(spec.property_name())
                } else {
                    get_text_of_node(spec.name())
                };
                if imported_name == export_name {
                    return get_text_of_node(spec.name());
                }
            }
        }
    }
    export_name.to_string()
}

/// FindModuleIdentifierForPackage resolves the imported identifier name for the given
/// module from an arbitrary package. It checks:
///   - Namespace imports: import * as X from "<packageName>/<moduleName>"
///   - Named imports: import { <moduleName> as X } from "<packageName>"
///
/// Falls back to moduleName if not found.
pub fn find_module_identifier_for_package(
    sf: Node,
    package_name: &str,
    module_name: &str,
) -> String {
    if sf.is_nil() {
        return module_name.to_string();
    }
    for stmt in sf.statements().iter() {
        if stmt.kind() != SyntaxKind::ImportDeclaration {
            continue;
        }
        let import_decl = stmt;
        if import_decl.module_specifier().is_nil() {
            continue;
        }
        let mut specifier = get_text_of_node(import_decl.module_specifier());
        if specifier.len() >= 2
            && (specifier.as_bytes()[0] == b'"' || specifier.as_bytes()[0] == b'\'')
        {
            specifier = specifier[1..specifier.len() - 1].to_string();
        }

        if import_decl.import_clause().is_nil() {
            continue;
        }
        let clause = import_decl.import_clause();
        let named_bindings = clause.named_bindings();
        if named_bindings.is_nil() {
            continue;
        }

        // Check namespace import: import * as X from "<packageName>/<moduleName>"
        if specifier == format!("{package_name}/{module_name}")
            && named_bindings.kind() == SyntaxKind::NamespaceImport
        {
            let ns_import = named_bindings;
            if ns_import.name().is_some() {
                return get_text_of_node(ns_import.name());
            }
        }

        // Check named imports: import { <moduleName> as X } from "<packageName>"
        if specifier == package_name && named_bindings.kind() == SyntaxKind::NamedImports {
            let named_imports = named_bindings;
            for elem in named_imports.elements().iter() {
                let spec = elem;
                let imported_name = if spec.property_name().is_some() {
                    get_text_of_node(spec.property_name())
                } else {
                    get_text_of_node(spec.name())
                };
                if imported_name == module_name {
                    return get_text_of_node(spec.name());
                }
            }
        }
    }
    module_name.to_string()
}
