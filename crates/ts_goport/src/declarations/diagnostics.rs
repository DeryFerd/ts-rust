//! Port of `transformers/declarations/diagnostics.go`.

use crate::checker::utilities_p1::new_diagnostic_for_node;
use crate::prelude::*;
use crate::printer::{EmitResolver, SymbolAccessibility, SymbolAccessibilityResult};
use ts_diagnostics::Message;

// Go: transformers/declarations/diagnostics.go:10 GetSymbolAccessibilityDiagnostic
// PORT: a Go func value is an `Rc<dyn Fn>` so the transformer can save and
// restore it. A nil Go func is `None` at the use sites.
pub type GetSymbolAccessibilityDiagnostic =
    Rc<dyn Fn(&SymbolAccessibilityResult) -> Option<SymbolAccessibilityDiagnostic>>;

// PORT: Go passes the selectors as func values; they are plain fns here.
type DiagnosticSelector = fn(Node, &SymbolAccessibilityResult) -> Option<&'static Message>;

// Go: transformers/declarations/diagnostics.go:12 SymbolAccessibilityDiagnostic
#[derive(Clone)]
pub struct SymbolAccessibilityDiagnostic {
    pub error_node: Node,
    pub diagnostic_message: &'static Message,
    pub type_name: Node,
}

// Go: transformers/declarations/diagnostics.go:18 wrapSimpleDiagnosticSelector
fn wrap_simple_diagnostic_selector(
    node: Node,
    selector: DiagnosticSelector,
) -> GetSymbolAccessibilityDiagnostic {
    Rc::new(move |symbol_accessibility_result| {
        let diagnostic_message = selector(node, symbol_accessibility_result)?;
        Some(SymbolAccessibilityDiagnostic {
            error_node: node,
            diagnostic_message,
            type_name: get_name_of_declaration(node),
        })
    })
}

// Go: transformers/declarations/diagnostics.go:32 wrapNamedDiagnosticSelector
fn wrap_named_diagnostic_selector(
    node: Node,
    selector: DiagnosticSelector,
) -> GetSymbolAccessibilityDiagnostic {
    Rc::new(move |symbol_accessibility_result| {
        let diagnostic_message = selector(node, symbol_accessibility_result)?;
        let name = get_name_of_declaration(node);
        Some(SymbolAccessibilityDiagnostic {
            error_node: name,
            diagnostic_message,
            type_name: name,
        })
    })
}

// Go: transformers/declarations/diagnostics.go:47 wrapFallbackErrorDiagnosticSelector
fn wrap_fallback_error_diagnostic_selector(
    node: Node,
    selector: DiagnosticSelector,
) -> GetSymbolAccessibilityDiagnostic {
    Rc::new(move |symbol_accessibility_result| {
        let diagnostic_message = selector(node, symbol_accessibility_result)?;
        let mut error_node = get_name_of_declaration(node);
        if error_node.is_nil() {
            error_node = node;
        }
        Some(SymbolAccessibilityDiagnostic {
            error_node,
            diagnostic_message,
            type_name: Node::NIL,
        })
    })
}

// Go: transformers/declarations/diagnostics.go:64 selectDiagnosticBasedOnModuleName
fn select_diagnostic_based_on_module_name(
    symbol_accessibility_result: &SymbolAccessibilityResult,
    module_not_nameable: &'static Message,
    private_module: &'static Message,
    non_module: &'static Message,
) -> Option<&'static Message> {
    if !symbol_accessibility_result.error_module_name.is_empty() {
        if symbol_accessibility_result.accessibility == SymbolAccessibility::CANNOT_BE_NAMED {
            return Some(module_not_nameable);
        }
        return Some(private_module);
    }
    Some(non_module)
}

// Go: transformers/declarations/diagnostics.go:74 selectDiagnosticBasedOnModuleNameNoNameCheck
fn select_diagnostic_based_on_module_name_no_name_check(
    symbol_accessibility_result: &SymbolAccessibilityResult,
    private_module: &'static Message,
    non_module: &'static Message,
) -> Option<&'static Message> {
    if !symbol_accessibility_result.error_module_name.is_empty() {
        return Some(private_module);
    }
    Some(non_module)
}

// Go: transformers/declarations/diagnostics.go:81 createGetSymbolAccessibilityDiagnosticForNodeName
// PERF: the Go `ast.Is*` tests are pure kind compares, so one match on the kind
// picks the same branch.
pub fn create_get_symbol_accessibility_diagnostic_for_node_name(
    node: Node,
) -> GetSymbolAccessibilityDiagnostic {
    match node.kind() {
        SyntaxKind::SetAccessor | SyntaxKind::GetAccessor => {
            wrap_simple_diagnostic_selector(node, get_accessor_name_visibility_diagnostic_message)
        }
        SyntaxKind::MethodDeclaration | SyntaxKind::MethodSignature => {
            wrap_simple_diagnostic_selector(node, get_method_name_visibility_diagnostic_message)
        }
        _ => create_get_symbol_accessibility_diagnostic_for_node(node),
    }
}

// Go: transformers/declarations/diagnostics.go:91 getAccessorNameVisibilityDiagnosticMessage
fn get_accessor_name_visibility_diagnostic_message(
    node: Node,
    r: &SymbolAccessibilityResult,
) -> Option<&'static Message> {
    if is_static(node) {
        select_diagnostic_based_on_module_name(
            r,
            diag::Public_static_property_0_of_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            diag::Public_static_property_0_of_exported_class_has_or_is_using_name_1_from_private_module_2,
            diag::Public_static_property_0_of_exported_class_has_or_is_using_private_name_1,
        )
    } else if node.parent().kind() == SyntaxKind::ClassDeclaration {
        select_diagnostic_based_on_module_name(
            r,
            diag::Public_property_0_of_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            diag::Public_property_0_of_exported_class_has_or_is_using_name_1_from_private_module_2,
            diag::Public_property_0_of_exported_class_has_or_is_using_private_name_1,
        )
    } else {
        select_diagnostic_based_on_module_name_no_name_check(
            r,
            diag::Property_0_of_exported_interface_has_or_is_using_name_1_from_private_module_2,
            diag::Property_0_of_exported_interface_has_or_is_using_private_name_1,
        )
    }
}

// Go: transformers/declarations/diagnostics.go:115 getMethodNameVisibilityDiagnosticMessage
fn get_method_name_visibility_diagnostic_message(
    node: Node,
    r: &SymbolAccessibilityResult,
) -> Option<&'static Message> {
    if is_static(node) {
        select_diagnostic_based_on_module_name(
            r,
            diag::Public_static_method_0_of_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            diag::Public_static_method_0_of_exported_class_has_or_is_using_name_1_from_private_module_2,
            diag::Public_static_method_0_of_exported_class_has_or_is_using_private_name_1,
        )
    } else if node.parent().kind() == SyntaxKind::ClassDeclaration {
        select_diagnostic_based_on_module_name(
            r,
            diag::Public_method_0_of_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            diag::Public_method_0_of_exported_class_has_or_is_using_name_1_from_private_module_2,
            diag::Public_method_0_of_exported_class_has_or_is_using_private_name_1,
        )
    } else {
        select_diagnostic_based_on_module_name_no_name_check(
            r,
            diag::Method_0_of_exported_interface_has_or_is_using_name_1_from_private_module_2,
            diag::Method_0_of_exported_interface_has_or_is_using_private_name_1,
        )
    }
}

// Go: transformers/declarations/diagnostics.go:139 createGetSymbolAccessibilityDiagnosticForNode
// PERF: Go chains up to 23 `ast.Is*` tests. Each one is a pure kind compare
// and the branches test disjoint kinds, so one match on the kind picks the same
// branch. The arms keep the Go order.
pub fn create_get_symbol_accessibility_diagnostic_for_node(
    node: Node,
) -> GetSymbolAccessibilityDiagnostic {
    match node.kind() {
        SyntaxKind::VariableDeclaration
        | SyntaxKind::PropertyDeclaration
        | SyntaxKind::PropertySignature
        | SyntaxKind::PropertyAccessExpression
        | SyntaxKind::ElementAccessExpression
        | SyntaxKind::BinaryExpression
        | SyntaxKind::BindingElement
        | SyntaxKind::Constructor => wrap_simple_diagnostic_selector(
            node,
            get_variable_declaration_type_visibility_diagnostic_message,
        ),
        SyntaxKind::SetAccessor | SyntaxKind::GetAccessor => wrap_named_diagnostic_selector(
            node,
            get_accessor_declaration_type_visibility_diagnostic_message,
        ),
        SyntaxKind::ConstructSignature
        | SyntaxKind::CallSignature
        | SyntaxKind::MethodDeclaration
        | SyntaxKind::MethodSignature
        | SyntaxKind::FunctionDeclaration
        | SyntaxKind::IndexSignature => wrap_fallback_error_diagnostic_selector(
            node,
            get_return_type_visibility_diagnostic_message,
        ),
        SyntaxKind::Parameter => {
            if is_parameter_property_declaration(node, node.parent())
                && has_syntactic_modifier(node.parent(), ModifierFlags::PRIVATE)
            {
                return wrap_simple_diagnostic_selector(
                    node,
                    get_variable_declaration_type_visibility_diagnostic_message,
                );
            }
            wrap_simple_diagnostic_selector(
                node,
                get_parameter_declaration_type_visibility_diagnostic_message,
            )
        }
        SyntaxKind::TypeParameter => wrap_simple_diagnostic_selector(
            node,
            get_type_parameter_constraint_visibility_diagnostic_message,
        ),
        SyntaxKind::ExpressionWithTypeArguments => {
            // unique node selection behavior, inline closure
            Rc::new(move |_symbol_accessibility_result| {
                let diagnostic_message;
                // Heritage clause is written by user so it can always be named
                if is_class_declaration(node.parent().parent()) {
                    // Class or Interface implemented/extended is inaccessible
                    if is_heritage_clause(node.parent())
                        && node.parent().token() == SyntaxKind::ImplementsKeyword
                    {
                        diagnostic_message =
                            diag::Implements_clause_of_exported_class_0_has_or_is_using_private_name_1;
                    } else if node.parent().parent().name().is_some() {
                        diagnostic_message =
                            diag::X_extends_clause_of_exported_class_0_has_or_is_using_private_name_1;
                    } else {
                        diagnostic_message =
                            diag::X_extends_clause_of_exported_class_has_or_is_using_private_name_0;
                    }
                } else {
                    // interface is inaccessible
                    diagnostic_message =
                        diag::X_extends_clause_of_exported_interface_0_has_or_is_using_private_name_1;
                }
                Some(SymbolAccessibilityDiagnostic {
                    diagnostic_message,
                    error_node: node,
                    type_name: get_name_of_declaration(node.parent().parent()),
                })
            })
        }
        SyntaxKind::ImportEqualsDeclaration => wrap_simple_diagnostic_selector(node, |_, _| {
            Some(diag::Import_declaration_0_is_using_private_name_1)
        }),
        SyntaxKind::TypeAliasDeclaration | SyntaxKind::JsTypeAliasDeclaration => {
            // unique node selection behavior, inline closure
            Rc::new(move |symbol_accessibility_result| {
                let diagnostic_message = select_diagnostic_based_on_module_name_no_name_check(
                    symbol_accessibility_result,
                    diag::Exported_type_alias_0_has_or_is_using_private_name_1_from_module_2,
                    diag::Exported_type_alias_0_has_or_is_using_private_name_1,
                )?;
                Some(SymbolAccessibilityDiagnostic {
                    error_node: node.type_(),
                    diagnostic_message,
                    type_name: node.name(),
                })
            })
        }
        SyntaxKind::CallExpression => {
            // JS object.defineProperty call
            // unique node selection behavior, inline closure
            Rc::new(move |symbol_accessibility_result| {
                let diagnostic_message = select_diagnostic_based_on_module_name(
                    symbol_accessibility_result,
                    diag::Exported_variable_0_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
                    diag::Exported_variable_0_has_or_is_using_name_1_from_private_module_2,
                    diag::Exported_variable_0_has_or_is_using_private_name_1,
                )?;
                let argument = node.arguments().get(1);
                Some(SymbolAccessibilityDiagnostic {
                    error_node: argument,
                    diagnostic_message,
                    type_name: argument,
                })
            })
        }
        kind => panic!(
            "Attempted to set a declaration diagnostic context for unhandled node kind: {kind:?}"
        ),
    }
}

// Go: transformers/declarations/diagnostics.go:223 getVariableDeclarationTypeVisibilityDiagnosticMessage
fn get_variable_declaration_type_visibility_diagnostic_message(
    node: Node,
    r: &SymbolAccessibilityResult,
) -> Option<&'static Message> {
    let kind = node.kind();
    if kind == SyntaxKind::VariableDeclaration || kind == SyntaxKind::BindingElement {
        return select_diagnostic_based_on_module_name(
            r,
            diag::Exported_variable_0_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            diag::Exported_variable_0_has_or_is_using_name_1_from_private_module_2,
            diag::Exported_variable_0_has_or_is_using_private_name_1,
        );
        // This check is to ensure we don't report error on constructor parameter property as that error would be reported during parameter emit
        // The only exception here is if the constructor was marked as private. we are not emitting the constructor parameters at all.
    } else if kind == SyntaxKind::PropertyDeclaration
        || kind == SyntaxKind::PropertyAccessExpression
        || kind == SyntaxKind::ElementAccessExpression
        || kind == SyntaxKind::BinaryExpression
        || kind == SyntaxKind::PropertySignature
        || (kind == SyntaxKind::Parameter
            && has_syntactic_modifier(node.parent(), ModifierFlags::PRIVATE))
    {
        if is_static(node) {
            return select_diagnostic_based_on_module_name(
                r,
                diag::Public_static_property_0_of_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
                diag::Public_static_property_0_of_exported_class_has_or_is_using_name_1_from_private_module_2,
                diag::Public_static_property_0_of_exported_class_has_or_is_using_private_name_1,
            );
        } else if node.parent().kind() == SyntaxKind::ClassDeclaration
            || kind == SyntaxKind::Parameter
        {
            return select_diagnostic_based_on_module_name(
                r,
                diag::Public_property_0_of_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
                diag::Public_property_0_of_exported_class_has_or_is_using_name_1_from_private_module_2,
                diag::Public_property_0_of_exported_class_has_or_is_using_private_name_1,
            );
        } else {
            // Interfaces cannot have types that cannot be named
            return select_diagnostic_based_on_module_name_no_name_check(
                r,
                diag::Property_0_of_exported_interface_has_or_is_using_name_1_from_private_module_2,
                diag::Property_0_of_exported_interface_has_or_is_using_private_name_1,
            );
        }
    }
    None
}

// Go: transformers/declarations/diagnostics.go:263 getAccessorDeclarationTypeVisibilityDiagnosticMessage
fn get_accessor_declaration_type_visibility_diagnostic_message(
    node: Node,
    r: &SymbolAccessibilityResult,
) -> Option<&'static Message> {
    if node.kind() == SyntaxKind::SetAccessor {
        // Getters can infer the return type from the returned expression, but setters cannot, so the
        // "_from_external_module_1_but_cannot_be_named" case cannot occur.
        if is_static(node) {
            select_diagnostic_based_on_module_name_no_name_check(
                r,
                diag::Parameter_type_of_public_static_setter_0_from_exported_class_has_or_is_using_name_1_from_private_module_2,
                diag::Parameter_type_of_public_static_setter_0_from_exported_class_has_or_is_using_private_name_1,
            )
        } else {
            select_diagnostic_based_on_module_name_no_name_check(
                r,
                diag::Parameter_type_of_public_setter_0_from_exported_class_has_or_is_using_name_1_from_private_module_2,
                diag::Parameter_type_of_public_setter_0_from_exported_class_has_or_is_using_private_name_1,
            )
        }
    } else if is_static(node) {
        select_diagnostic_based_on_module_name(
            r,
            diag::Return_type_of_public_static_getter_0_from_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            diag::Return_type_of_public_static_getter_0_from_exported_class_has_or_is_using_name_1_from_private_module_2,
            diag::Return_type_of_public_static_getter_0_from_exported_class_has_or_is_using_private_name_1,
        )
    } else {
        select_diagnostic_based_on_module_name(
            r,
            diag::Return_type_of_public_getter_0_from_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            diag::Return_type_of_public_getter_0_from_exported_class_has_or_is_using_name_1_from_private_module_2,
            diag::Return_type_of_public_getter_0_from_exported_class_has_or_is_using_private_name_1,
        )
    }
}

// Go: transformers/declarations/diagnostics.go:299 getReturnTypeVisibilityDiagnosticMessage
fn get_return_type_visibility_diagnostic_message(
    node: Node,
    r: &SymbolAccessibilityResult,
) -> Option<&'static Message> {
    match node.kind() {
        SyntaxKind::ConstructSignature => select_diagnostic_based_on_module_name_no_name_check(
            r,
            diag::Return_type_of_constructor_signature_from_exported_interface_has_or_is_using_name_0_from_private_module_1,
            diag::Return_type_of_constructor_signature_from_exported_interface_has_or_is_using_private_name_0,
        ),
        SyntaxKind::CallSignature => select_diagnostic_based_on_module_name_no_name_check(
            r,
            diag::Return_type_of_call_signature_from_exported_interface_has_or_is_using_name_0_from_private_module_1,
            diag::Return_type_of_call_signature_from_exported_interface_has_or_is_using_private_name_0,
        ),
        SyntaxKind::IndexSignature => select_diagnostic_based_on_module_name_no_name_check(
            r,
            diag::Return_type_of_index_signature_from_exported_interface_has_or_is_using_name_0_from_private_module_1,
            diag::Return_type_of_index_signature_from_exported_interface_has_or_is_using_private_name_0,
        ),
        SyntaxKind::MethodDeclaration | SyntaxKind::MethodSignature => {
            if is_static(node) {
                select_diagnostic_based_on_module_name(
                    r,
                    diag::Return_type_of_public_static_method_from_exported_class_has_or_is_using_name_0_from_external_module_1_but_cannot_be_named,
                    diag::Return_type_of_public_static_method_from_exported_class_has_or_is_using_name_0_from_private_module_1,
                    diag::Return_type_of_public_static_method_from_exported_class_has_or_is_using_private_name_0,
                )
            } else if node.parent().kind() == SyntaxKind::ClassDeclaration {
                select_diagnostic_based_on_module_name(
                    r,
                    diag::Return_type_of_public_method_from_exported_class_has_or_is_using_name_0_from_external_module_1_but_cannot_be_named,
                    diag::Return_type_of_public_method_from_exported_class_has_or_is_using_name_0_from_private_module_1,
                    diag::Return_type_of_public_method_from_exported_class_has_or_is_using_private_name_0,
                )
            } else {
                // Interfaces cannot have return types that cannot be named
                select_diagnostic_based_on_module_name_no_name_check(
                    r,
                    diag::Return_type_of_method_from_exported_interface_has_or_is_using_name_0_from_private_module_1,
                    diag::Return_type_of_method_from_exported_interface_has_or_is_using_private_name_0,
                )
            }
        }
        SyntaxKind::FunctionDeclaration => select_diagnostic_based_on_module_name(
            r,
            diag::Return_type_of_exported_function_has_or_is_using_name_0_from_external_module_1_but_cannot_be_named,
            diag::Return_type_of_exported_function_has_or_is_using_name_0_from_private_module_1,
            diag::Return_type_of_exported_function_has_or_is_using_private_name_0,
        ),
        kind => panic!("This is unknown kind for signature: {kind:?}"),
    }
}

// Go: transformers/declarations/diagnostics.go:358 getParameterDeclarationTypeVisibilityDiagnosticMessage
fn get_parameter_declaration_type_visibility_diagnostic_message(
    node: Node,
    r: &SymbolAccessibilityResult,
) -> Option<&'static Message> {
    match node.parent().kind() {
        SyntaxKind::Constructor => select_diagnostic_based_on_module_name(
            r,
            diag::Parameter_0_of_constructor_from_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            diag::Parameter_0_of_constructor_from_exported_class_has_or_is_using_name_1_from_private_module_2,
            diag::Parameter_0_of_constructor_from_exported_class_has_or_is_using_private_name_1,
        ),
        // Interfaces cannot have parameter types that cannot be named
        SyntaxKind::ConstructSignature | SyntaxKind::ConstructorType => select_diagnostic_based_on_module_name_no_name_check(
            r,
            diag::Parameter_0_of_constructor_signature_from_exported_interface_has_or_is_using_name_1_from_private_module_2,
            diag::Parameter_0_of_constructor_signature_from_exported_interface_has_or_is_using_private_name_1,
        ),
        SyntaxKind::CallSignature => select_diagnostic_based_on_module_name_no_name_check(
            r,
            diag::Parameter_0_of_call_signature_from_exported_interface_has_or_is_using_name_1_from_private_module_2,
            diag::Parameter_0_of_call_signature_from_exported_interface_has_or_is_using_private_name_1,
        ),
        SyntaxKind::IndexSignature => select_diagnostic_based_on_module_name_no_name_check(
            r,
            diag::Parameter_0_of_index_signature_from_exported_interface_has_or_is_using_name_1_from_private_module_2,
            diag::Parameter_0_of_index_signature_from_exported_interface_has_or_is_using_private_name_1,
        ),
        SyntaxKind::MethodDeclaration | SyntaxKind::MethodSignature => {
            if is_static(node.parent()) {
                select_diagnostic_based_on_module_name(
                    r,
                    diag::Parameter_0_of_public_static_method_from_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
                    diag::Parameter_0_of_public_static_method_from_exported_class_has_or_is_using_name_1_from_private_module_2,
                    diag::Parameter_0_of_public_static_method_from_exported_class_has_or_is_using_private_name_1,
                )
            } else if node.parent().parent().kind() == SyntaxKind::ClassDeclaration {
                select_diagnostic_based_on_module_name(
                    r,
                    diag::Parameter_0_of_public_method_from_exported_class_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
                    diag::Parameter_0_of_public_method_from_exported_class_has_or_is_using_name_1_from_private_module_2,
                    diag::Parameter_0_of_public_method_from_exported_class_has_or_is_using_private_name_1,
                )
            } else {
                select_diagnostic_based_on_module_name_no_name_check(
                    r,
                    diag::Parameter_0_of_method_from_exported_interface_has_or_is_using_name_1_from_private_module_2,
                    diag::Parameter_0_of_method_from_exported_interface_has_or_is_using_private_name_1,
                )
            }
        }
        SyntaxKind::FunctionDeclaration
        | SyntaxKind::FunctionType
        | SyntaxKind::ArrowFunction
        | SyntaxKind::FunctionExpression => select_diagnostic_based_on_module_name(
            r,
            diag::Parameter_0_of_exported_function_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            diag::Parameter_0_of_exported_function_has_or_is_using_name_1_from_private_module_2,
            diag::Parameter_0_of_exported_function_has_or_is_using_private_name_1,
        ),
        SyntaxKind::SetAccessor | SyntaxKind::GetAccessor => select_diagnostic_based_on_module_name(
            r,
            diag::Parameter_0_of_accessor_has_or_is_using_name_1_from_external_module_2_but_cannot_be_named,
            diag::Parameter_0_of_accessor_has_or_is_using_name_1_from_private_module_2,
            diag::Parameter_0_of_accessor_has_or_is_using_private_name_1,
        ),
        kind => panic!("Unknown parent for parameter: {kind:?}"),
    }
}

// Go: transformers/declarations/diagnostics.go:435 getTypeParameterConstraintVisibilityDiagnosticMessage
fn get_type_parameter_constraint_visibility_diagnostic_message(
    node: Node,
    _r: &SymbolAccessibilityResult,
) -> Option<&'static Message> {
    // Type parameter constraints are named by user so we should always be able to name it
    Some(match node.parent().kind() {
        SyntaxKind::ClassDeclaration => diag::Type_parameter_0_of_exported_class_has_or_is_using_private_name_1,
        SyntaxKind::InterfaceDeclaration => diag::Type_parameter_0_of_exported_interface_has_or_is_using_private_name_1,
        SyntaxKind::MappedType => diag::Type_parameter_0_of_exported_mapped_object_type_is_using_private_name_1,
        SyntaxKind::ConstructorType | SyntaxKind::ConstructSignature => {
            diag::Type_parameter_0_of_constructor_signature_from_exported_interface_has_or_is_using_private_name_1
        }
        SyntaxKind::CallSignature => {
            diag::Type_parameter_0_of_call_signature_from_exported_interface_has_or_is_using_private_name_1
        }
        SyntaxKind::MethodDeclaration | SyntaxKind::MethodSignature => {
            if is_static(node.parent()) {
                diag::Type_parameter_0_of_public_static_method_from_exported_class_has_or_is_using_private_name_1
            } else if node.parent().parent().kind() == SyntaxKind::ClassDeclaration {
                diag::Type_parameter_0_of_public_method_from_exported_class_has_or_is_using_private_name_1
            } else {
                diag::Type_parameter_0_of_method_from_exported_interface_has_or_is_using_private_name_1
            }
        }
        SyntaxKind::FunctionType | SyntaxKind::FunctionDeclaration => {
            diag::Type_parameter_0_of_exported_function_has_or_is_using_private_name_1
        }
        SyntaxKind::InferType => diag::Extends_clause_for_inferred_type_0_has_or_is_using_private_name_1,
        SyntaxKind::TypeAliasDeclaration | SyntaxKind::JsTypeAliasDeclaration => {
            diag::Type_parameter_0_of_exported_type_alias_has_or_is_using_private_name_1
        }
        kind => panic!("This is unknown parent for type parameter: {kind:?}"),
    })
}

// Go: transformers/declarations/diagnostics.go:470 getRelatedSuggestionByDeclarationKind
fn get_related_suggestion_by_declaration_kind(kind: SyntaxKind) -> Option<&'static Message> {
    Some(match kind {
        SyntaxKind::ArrowFunction => diag::Add_a_return_type_to_the_function_expression,
        SyntaxKind::FunctionExpression => diag::Add_a_return_type_to_the_function_expression,
        SyntaxKind::MethodDeclaration => diag::Add_a_return_type_to_the_method,
        SyntaxKind::GetAccessor => diag::Add_a_return_type_to_the_get_accessor_declaration,
        SyntaxKind::SetAccessor => diag::Add_a_type_to_parameter_of_the_set_accessor_declaration,
        SyntaxKind::FunctionDeclaration => diag::Add_a_return_type_to_the_function_declaration,
        SyntaxKind::ConstructSignature => diag::Add_a_return_type_to_the_function_declaration,
        SyntaxKind::Parameter => diag::Add_a_type_annotation_to_the_parameter_0,
        SyntaxKind::VariableDeclaration => diag::Add_a_type_annotation_to_the_variable_0,
        SyntaxKind::PropertyDeclaration => diag::Add_a_type_annotation_to_the_property_0,
        SyntaxKind::PropertySignature => diag::Add_a_type_annotation_to_the_property_0,
        SyntaxKind::ExportAssignment => {
            diag::Move_the_expression_in_default_export_to_a_variable_and_add_a_type_annotation_to_it
        }
        _ => return None,
    })
}

// Go: transformers/declarations/diagnostics.go:501 getErrorByDeclarationKind
fn get_error_by_declaration_kind(kind: SyntaxKind) -> Option<&'static Message> {
    Some(match kind {
        SyntaxKind::FunctionExpression | SyntaxKind::FunctionDeclaration | SyntaxKind::ArrowFunction => {
            diag::Function_must_have_an_explicit_return_type_annotation_with_isolatedDeclarations
        }
        SyntaxKind::MethodDeclaration | SyntaxKind::ConstructSignature => {
            diag::Method_must_have_an_explicit_return_type_annotation_with_isolatedDeclarations
        }
        SyntaxKind::GetAccessor | SyntaxKind::SetAccessor => {
            diag::At_least_one_accessor_must_have_an_explicit_type_annotation_with_isolatedDeclarations
        }
        SyntaxKind::Parameter => diag::Parameter_must_have_an_explicit_type_annotation_with_isolatedDeclarations,
        SyntaxKind::VariableDeclaration => diag::Variable_must_have_an_explicit_type_annotation_with_isolatedDeclarations,
        SyntaxKind::PropertyDeclaration | SyntaxKind::PropertySignature => {
            diag::Property_must_have_an_explicit_type_annotation_with_isolatedDeclarations
        }
        SyntaxKind::ComputedPropertyName => {
            diag::Computed_property_names_on_class_or_object_literals_cannot_be_inferred_with_isolatedDeclarations
        }
        SyntaxKind::SpreadAssignment => diag::Objects_that_contain_spread_assignments_can_t_be_inferred_with_isolatedDeclarations,
        SyntaxKind::ShorthandPropertyAssignment => {
            diag::Objects_that_contain_shorthand_properties_can_t_be_inferred_with_isolatedDeclarations
        }
        SyntaxKind::ArrayLiteralExpression => diag::Only_const_arrays_can_be_inferred_with_isolatedDeclarations,
        SyntaxKind::ExportAssignment => diag::Default_exports_can_t_be_inferred_with_isolatedDeclarations,
        SyntaxKind::SpreadElement => diag::Arrays_with_spread_elements_can_t_inferred_with_isolatedDeclarations,
        _ => return None,
    })
}

// Go: transformers/declarations/diagnostics.go:542 isDeclarationEnoughForErrors
fn is_declaration_enough_for_errors(node: Node) -> bool {
    is_export_assignment(node)
        || is_statement(node)
        || is_variable_declaration(node)
        || is_property_declaration(node)
        || is_parameter_declaration(node)
}

// Go: transformers/declarations/diagnostics.go:546 isFunctionLikeAndNotConstructor
fn is_function_like_and_not_constructor(node: Node) -> bool {
    is_function_like_declaration(node) && !is_constructor_declaration(node)
}

// Go: transformers/declarations/diagnostics.go:550 findNearestDeclaration
fn find_nearest_declaration(node: Node) -> Node {
    let result = find_ancestor(node, is_declaration_enough_for_errors);
    if result.is_nil() {
        return Node::NIL;
    }
    if is_export_assignment(result) {
        return result;
    }
    if is_return_statement(result) {
        return find_ancestor(result, is_function_like_and_not_constructor);
    }
    if is_statement(result) {
        return Node::NIL;
    }
    result
}

// PORT: Go `createDiagnosticForNode` (tracker.go:209) takes a
// `*diagnostics.Message` that can be nil when a kind lookup misses. Here the
// lookups return `Option`, and a nil message would crash in Go when the
// diagnostic is formatted, so `None` panics at creation.
fn message(message: Option<&'static Message>) -> &'static Message {
    message.expect("nil diagnostic message")
}

// Go: transformers/declarations/diagnostics.go:567 createEntityInTypeNodeError
fn create_entity_in_type_node_error(node: Node) -> Diagnostic {
    let mut diag = create_diagnostic_for_node(
        node,
        diag::Type_containing_private_name_0_can_t_be_used_with_isolatedDeclarations,
        args![get_text_of_node(node)],
    );
    add_parent_declaration_related_info(node, &mut diag);
    diag
}

// Go: transformers/declarations/diagnostics.go:573 addParentDeclarationRelatedInfo
fn add_parent_declaration_related_info(node: Node, diag: &mut Diagnostic) {
    let parent_declaration = find_nearest_declaration(node);
    if parent_declaration.is_nil() {
        return;
    }
    let mut target_str = String::new();
    if !is_export_assignment(parent_declaration) && parent_declaration.name().is_some() {
        target_str = get_text_of_node(parent_declaration.name());
    }
    diag.add_related_info(Some(create_diagnostic_for_node(
        parent_declaration,
        message(get_related_suggestion_by_declaration_kind(
            parent_declaration.kind(),
        )),
        args![target_str],
    )));
}

// Go: transformers/declarations/diagnostics.go:585 createAccessorTypeError
// PORT: Go reads `node.Symbol().Declarations`. The declarations module has no
// checker, so it reads the binder symbol from `prog().bound_symbols`.
fn create_accessor_type_error(node: Node) -> Diagnostic {
    let declarations = bound_symbol_declarations(node.symbol());
    let all_declarations = get_all_accessor_declarations_for_declaration(node, &declarations);
    let get_accessor = all_declarations.get_accessor;
    let set_accessor = all_declarations.set_accessor;
    let mut target_node = node;
    if is_set_accessor_declaration(node) && node.parameters().len() > 0 {
        target_node = node.parameters().get(0);
    }
    let mut diag = create_diagnostic_for_node(
        target_node,
        message(get_error_by_declaration_kind(node.kind())),
        args![],
    );
    if set_accessor.is_some() {
        diag.add_related_info(Some(create_diagnostic_for_node(
            set_accessor,
            message(get_related_suggestion_by_declaration_kind(
                set_accessor.kind(),
            )),
            args![],
        )));
    }
    if get_accessor.is_some() {
        diag.add_related_info(Some(create_diagnostic_for_node(
            get_accessor,
            message(get_related_suggestion_by_declaration_kind(
                get_accessor.kind(),
            )),
            args![],
        )));
    }
    diag
}

/// The declarations of a binder symbol. Go reads `symbol.Declarations`.
pub(crate) fn bound_symbol_declarations(symbol: SymbolId) -> Vec<Node> {
    prog()
        .bound_symbols
        .get()
        .expect("program not bound")
        .sym(symbol)
        .declarations
        .to_vec()
}

// Go: transformers/declarations/diagnostics.go:603 createObjectLiteralError
fn create_object_literal_error(node: Node) -> Diagnostic {
    let mut diag = create_diagnostic_for_node(
        node,
        message(get_error_by_declaration_kind(node.kind())),
        args![],
    );
    add_parent_declaration_related_info(node, &mut diag);
    diag
}

// Go: transformers/declarations/diagnostics.go:609 createArrayLiteralError
fn create_array_literal_error(node: Node) -> Diagnostic {
    let mut diag = create_diagnostic_for_node(
        node,
        message(get_error_by_declaration_kind(node.kind())),
        args![],
    );
    add_parent_declaration_related_info(node, &mut diag);
    diag
}

// Go: transformers/declarations/diagnostics.go:615 createReturnTypeError
fn create_return_type_error(node: Node) -> Diagnostic {
    let mut diag = create_diagnostic_for_node(
        node,
        message(get_error_by_declaration_kind(node.kind())),
        args![],
    );
    add_parent_declaration_related_info(node, &mut diag);
    diag.add_related_info(Some(create_diagnostic_for_node(
        node,
        message(get_related_suggestion_by_declaration_kind(node.kind())),
        args![],
    )));
    diag
}

// Go: transformers/declarations/diagnostics.go:622 createBindingElementError
fn create_binding_element_error(node: Node) -> Diagnostic {
    create_diagnostic_for_node(
        node,
        diag::Binding_elements_with_initializers_can_t_be_exported_directly_with_isolatedDeclarations,
        args![],
    )
}

// Go: transformers/declarations/diagnostics.go:626 createVariableOrPropertyError
fn create_variable_or_property_error(node: Node) -> Diagnostic {
    let mut diag = create_diagnostic_for_node(
        node,
        message(get_error_by_declaration_kind(node.kind())),
        args![],
    );
    diag.add_related_info(Some(create_diagnostic_for_node(
        node,
        message(get_related_suggestion_by_declaration_kind(node.kind())),
        args![get_text_of_node(node.name())],
    )));
    diag
}

// Go: transformers/declarations/diagnostics.go:632 createExpressionError
fn create_expression_error(node: Node) -> Diagnostic {
    create_expression_error_ex(node, None)
}

// Go: transformers/declarations/diagnostics.go:636 createClassExpressionError
fn create_class_expression_error(node: Node) -> Diagnostic {
    create_expression_error_ex(
        node,
        Some(diag::Inference_from_class_expressions_is_not_supported_with_isolatedDeclarations),
    )
}

// Go: transformers/declarations/diagnostics.go:640 isParentForIDDIagnostic
fn is_parent_for_idd_iagnostic(node: Node) -> FindAncestorResult {
    if is_export_assignment(node) {
        return FindAncestorResult::FIND_ANCESTOR_TRUE;
    }
    if is_statement(node) {
        return FindAncestorResult::FIND_ANCESTOR_QUIT;
    }
    to_find_ancestor_result(!is_parenthesized_expression(node) && !is_assertion_expression(node))
}

// Go: transformers/declarations/diagnostics.go:650 createExpressionErrorEx
fn create_expression_error_ex(
    node: Node,
    mut diagnostic_message: Option<&'static Message>,
) -> Diagnostic {
    let parent_declaration = find_nearest_declaration(node);
    if parent_declaration.is_nil() {
        let msg = diagnostic_message
            .unwrap_or(diag::Expression_type_can_t_be_inferred_with_isolatedDeclarations);
        return create_diagnostic_for_node(node, msg, args![]);
    }

    let mut target_str = String::new();
    if !is_export_assignment(parent_declaration) && parent_declaration.name().is_some() {
        target_str = get_text_of_node(parent_declaration.name());
    }
    let parent = find_ancestor_or_quit(node.parent(), is_parent_for_idd_iagnostic);

    if parent_declaration == parent {
        if diagnostic_message.is_none() {
            diagnostic_message = get_error_by_declaration_kind(parent_declaration.kind());
        }
        let mut diag = create_diagnostic_for_node(node, message(diagnostic_message), args![]);
        diag.add_related_info(Some(create_diagnostic_for_node(
            parent_declaration,
            message(get_related_suggestion_by_declaration_kind(
                parent_declaration.kind(),
            )),
            args![target_str],
        )));
        return diag;
    }
    let msg = diagnostic_message
        .unwrap_or(diag::Expression_type_can_t_be_inferred_with_isolatedDeclarations);
    let mut diag = create_diagnostic_for_node(node, msg, args![]);
    diag.add_related_info(Some(create_diagnostic_for_node(
        parent_declaration,
        message(get_related_suggestion_by_declaration_kind(
            parent_declaration.kind(),
        )),
        args![target_str],
    )));
    diag.add_related_info(Some(create_diagnostic_for_node(
        node,
        diag::Add_satisfies_and_a_type_assertion_to_this_expression_satisfies_T_as_T_to_make_the_type_explicit,
        args![],
    )));
    diag
}

/// Go `func(node *ast.Node) *ast.Diagnostic` returned by createGetIsolatedDeclarationErrors.
/// PORT: the first argument is the checker that the caller already holds
/// (inside a node builder call), or `None` when no checker is lent out.
pub type GetIsolatedDeclarationError = Box<dyn Fn(Option<&mut Checker>, Node) -> Diagnostic>;

// Go: transformers/declarations/diagnostics.go:682 createGetIsolatedDeclarationErrors
pub fn create_get_isolated_declaration_errors(
    resolver: Rc<dyn EmitResolver>,
) -> GetIsolatedDeclarationError {
    let create_parameter_error = move |c: Option<&mut Checker>, node: Node| -> Diagnostic {
        if is_set_accessor_declaration(node.parent()) {
            return create_accessor_type_error(node.parent());
        }
        // skip checker lock - node builder will already have one
        // PORT: Go always skips the lock. Here a caller inside the node
        // builder passes its checker, which is used directly. Without one,
        // the trait method borrows the resolver's checker, which is free.
        let add_undefined = match c {
            Some(c) => c
                .get_emit_resolver()
                .requires_adding_implicit_undefined_unsafe_worker(
                    c,
                    node,
                    SymbolId::NIL,
                    Node::NIL,
                ),
            None => {
                resolver.requires_adding_implicit_undefined_unsafe(node, SymbolId::NIL, Node::NIL)
            }
        };
        if !add_undefined && node.initializer().is_some() {
            return create_expression_error(node.initializer());
        }
        let mut msg = get_error_by_declaration_kind(node.kind());
        if add_undefined {
            msg = Some(diag::Declaration_emit_for_this_parameter_requires_implicitly_adding_undefined_to_its_type_This_is_not_supported_with_isolatedDeclarations);
        }
        let mut diag = create_diagnostic_for_node(node, message(msg), args![]);
        let target_str = get_text_of_node(node.name());
        diag.add_related_info(Some(create_diagnostic_for_node(
            node,
            message(get_related_suggestion_by_declaration_kind(node.kind())),
            args![target_str],
        )));
        diag
    };

    Box::new(move |c: Option<&mut Checker>, node: Node| -> Diagnostic {
        let heritage_clause = find_ancestor(node, is_heritage_clause);
        if heritage_clause.is_some() {
            return create_diagnostic_for_node(
                node,
                diag::Extends_clause_can_t_contain_an_expression_with_isolatedDeclarations,
                args![],
            );
        }
        if is_part_of_type_node(node) || is_type_query_node(node) {
            return create_entity_in_type_node_error(node);
        }
        if is_entity_name(node) || is_entity_name_expression(node) {
            return create_entity_in_type_node_error(node);
        }
        match node.kind() {
            SyntaxKind::GetAccessor | SyntaxKind::SetAccessor => create_accessor_type_error(node),
            SyntaxKind::ComputedPropertyName
            | SyntaxKind::ShorthandPropertyAssignment
            | SyntaxKind::SpreadAssignment => create_object_literal_error(node),
            SyntaxKind::ArrayLiteralExpression | SyntaxKind::SpreadElement => {
                create_array_literal_error(node)
            }
            SyntaxKind::MethodDeclaration
            | SyntaxKind::ConstructSignature
            | SyntaxKind::FunctionExpression
            | SyntaxKind::ArrowFunction
            | SyntaxKind::FunctionDeclaration => create_return_type_error(node),
            SyntaxKind::BindingElement => create_binding_element_error(node),
            SyntaxKind::PropertyDeclaration | SyntaxKind::VariableDeclaration => {
                create_variable_or_property_error(node)
            }
            SyntaxKind::Parameter => create_parameter_error(c, node),
            SyntaxKind::PropertyAssignment => create_expression_error(node.initializer()),
            SyntaxKind::ClassExpression => create_class_expression_error(node),
            _ => create_expression_error(node),
        }
    })
}

// Go: transformers/declarations/tracker.go:207 createDiagnosticForNode
pub(crate) fn create_diagnostic_for_node(
    node: Node,
    message: &'static Message,
    args: Vec<String>,
) -> Diagnostic {
    new_diagnostic_for_node(node, message, args)
}
