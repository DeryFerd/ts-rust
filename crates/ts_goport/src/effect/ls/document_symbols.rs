//! Port of Effect-TS/tsgo `etslshooks/document_symbols.go` (effect-tsgo
//! 0.51.1): the Effect document symbol tree. With the plugin, a synthetic
//! `Effect` symbol (Layers, Services, Errors, Schemas, and Flows with the
//! `debug` option) goes before the plain symbols of the file.
//!
//! PORT: Go passes the checker beside the type parser to each helper. The
//! port's type parser holds the checker (`tp.checker`), so the helpers take
//! only the type parser. Go `*lsproto.DocumentSymbol` is `DocSymbol`
//! (`ls/symbols.rs`).

use crate::effect::rulerunner::enabled_options;
use crate::effect::typeparser::{PipingFlowTransformation, TypeParser};
use crate::ls::prelude::*;

/// Go `detail func(*typeparser.TypeParser, *checker.Checker, *ast.Node) *string`.
type DetailFn = fn(&mut TypeParser<'_>, Node) -> Option<String>;

// Go: etslshooks/document_symbols.go:20 afterDocumentSymbols
/// Called by `ls/symbols.rs` after the document symbols of a file are
/// collected and their expandos merged (Effect-TS/tsgo patch 024). Returns
/// the symbols with the `Effect` symbol first, or the symbols unchanged when
/// the file has no Effect declaration.
// PORT: Go makes the type parser from `program`. Here it takes the checker's
// program (the same program), as the hover hook does.
pub(crate) fn after_document_symbols(
    ctx: &Context,
    sf: Node,
    symbols: Vec<DocSymbol>,
    program: &compiler::NewProgram,
    lang_service: &LanguageService,
) -> Vec<DocSymbol> {
    let Some(effect_config) = enabled_options(program.options()) else {
        return symbols;
    };

    // PORT: Go `defer done()`: `_done` releases the checker when the hook
    // returns, after the checker borrow ends.
    let (checker, _done) = ls_program::get_type_checker_for_file(program, ctx, sf);
    let c = &mut *checker.borrow_mut();
    let mut tp = TypeParser::new(c.program, c);

    let layer_children = collect_layer_document_symbols(&mut tp, sf, lang_service);
    let service_children = collect_service_document_symbols(&mut tp, sf, lang_service);
    let error_children = collect_error_document_symbols(&mut tp, sf, lang_service);
    let schema_children = collect_schema_document_symbols(&mut tp, sf, lang_service);
    let mut flow_children: Vec<DocSymbol> = Vec::new();
    if effect_config.get_debug_enabled() {
        flow_children = collect_flow_document_symbols(&mut tp, sf, lang_service);
    }
    if layer_children.is_empty()
        && service_children.is_empty()
        && error_children.is_empty()
        && schema_children.is_empty()
        && flow_children.is_empty()
    {
        return symbols;
    }

    let mut effect_children: Vec<DocSymbol> = Vec::with_capacity(5);
    for (name, children) in [
        ("Layers", layer_children),
        ("Services", service_children),
        ("Errors", error_children),
        ("Schemas", schema_children),
        ("Flows", flow_children),
    ] {
        if !children.is_empty() {
            let group = new_synthetic_namespace_symbol(name);
            group.borrow_mut().children = Some(children);
            effect_children.push(group);
        }
    }
    let effect = new_synthetic_namespace_symbol("Effect");
    effect.borrow_mut().children = Some(effect_children);

    let mut result = Vec::with_capacity(symbols.len() + 1);
    result.push(effect);
    result.extend(symbols);
    result
}

// Go: etslshooks/document_symbols.go:74 collectLayerDocumentSymbols
fn collect_layer_document_symbols(
    tp: &mut TypeParser<'_>,
    sf: Node,
    lang_service: &LanguageService,
) -> Vec<DocSymbol> {
    // PORT: the recursive Go closure `walk` is a nested fn that takes the
    // captured `symbols` and `seen`.
    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        lang_service: &LanguageService,
        seen: &mut FxHashSet<Node>,
        symbols: &mut Vec<DocSymbol>,
        current: Node,
    ) -> bool {
        if current.is_nil() {
            return false;
        }
        if is_effect_symbol_declaration(current) && is_layer_declaration(tp, current) {
            let display_node = resolve_layer_display_node(current);
            if seen.insert(display_node) {
                symbols.push(new_effect_document_symbol(
                    tp,
                    sf,
                    lang_service,
                    current,
                    display_node,
                    Some(layer_symbol_detail),
                ));
            }
            return false;
        }
        current.for_each_child(|child| walk(tp, sf, lang_service, seen, symbols, child));
        false
    }
    let mut symbols = Vec::new();
    let mut seen = FxHashSet::default();
    sf.for_each_child(|child| walk(tp, sf, lang_service, &mut seen, &mut symbols, child));
    symbols
}

// Go: etslshooks/document_symbols.go:99 collectServiceDocumentSymbols
fn collect_service_document_symbols(
    tp: &mut TypeParser<'_>,
    sf: Node,
    lang_service: &LanguageService,
) -> Vec<DocSymbol> {
    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        lang_service: &LanguageService,
        seen: &mut FxHashSet<Node>,
        symbols: &mut Vec<DocSymbol>,
        current: Node,
    ) -> bool {
        if current.is_nil() {
            return false;
        }
        if is_effect_symbol_declaration(current) {
            if is_service_declaration(tp, current) {
                let display_node = resolve_service_display_node(current);
                if seen.insert(display_node) {
                    symbols.push(new_effect_document_symbol(
                        tp,
                        sf,
                        lang_service,
                        current,
                        display_node,
                        None,
                    ));
                }
                return false;
            }
            let t = tp.get_type_at_location(current);
            if tp.is_layer_type(t) {
                return false;
            }
        }
        current.for_each_child(|child| walk(tp, sf, lang_service, seen, symbols, child));
        false
    }
    let mut symbols = Vec::new();
    let mut seen = FxHashSet::default();
    sf.for_each_child(|child| walk(tp, sf, lang_service, &mut seen, &mut symbols, child));
    symbols
}

// Go: etslshooks/document_symbols.go:128 collectErrorDocumentSymbols
fn collect_error_document_symbols(
    tp: &mut TypeParser<'_>,
    sf: Node,
    lang_service: &LanguageService,
) -> Vec<DocSymbol> {
    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        lang_service: &LanguageService,
        seen: &mut FxHashSet<Node>,
        symbols: &mut Vec<DocSymbol>,
        current: Node,
    ) -> bool {
        if current.is_nil() {
            return false;
        }
        if is_effect_symbol_declaration(current) && is_error_declaration(tp, current) {
            let display_node = resolve_service_display_node(current);
            if seen.insert(display_node) {
                symbols.push(new_effect_document_symbol(
                    tp,
                    sf,
                    lang_service,
                    current,
                    display_node,
                    None,
                ));
            }
            return false;
        }
        current.for_each_child(|child| walk(tp, sf, lang_service, seen, symbols, child));
        false
    }
    let mut symbols = Vec::new();
    let mut seen = FxHashSet::default();
    sf.for_each_child(|child| walk(tp, sf, lang_service, &mut seen, &mut symbols, child));
    symbols
}

// Go: etslshooks/document_symbols.go:153 collectSchemaDocumentSymbols
fn collect_schema_document_symbols(
    tp: &mut TypeParser<'_>,
    sf: Node,
    lang_service: &LanguageService,
) -> Vec<DocSymbol> {
    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        lang_service: &LanguageService,
        seen: &mut FxHashSet<Node>,
        symbols: &mut Vec<DocSymbol>,
        current: Node,
    ) -> bool {
        if current.is_nil() {
            return false;
        }
        if is_effect_symbol_declaration(current) && is_schema_declaration(tp, current) {
            let display_node = resolve_service_display_node(current);
            if seen.insert(display_node) {
                symbols.push(new_effect_document_symbol(
                    tp,
                    sf,
                    lang_service,
                    current,
                    display_node,
                    None,
                ));
            }
            return false;
        }
        current.for_each_child(|child| walk(tp, sf, lang_service, seen, symbols, child));
        false
    }
    let mut symbols = Vec::new();
    let mut seen = FxHashSet::default();
    sf.for_each_child(|child| walk(tp, sf, lang_service, &mut seen, &mut symbols, child));
    symbols
}

// Go: etslshooks/document_symbols.go:178 collectFlowDocumentSymbols
// PORT: Go skips a nil flow; a Rust flow is never nil, so only the nil
// `flow.Node` check is left.
fn collect_flow_document_symbols(
    tp: &mut TypeParser<'_>,
    sf: Node,
    lang_service: &LanguageService,
) -> Vec<DocSymbol> {
    let flows = tp.piping_flows(sf, true);
    if flows.is_empty() {
        return Vec::new();
    }

    let mut symbols = Vec::with_capacity(flows.len());
    for (i, flow) in flows.iter().enumerate() {
        if flow.node.is_nil() {
            continue;
        }

        let mut children = Vec::with_capacity(flow.transformations.len() + 1);
        if flow.subject.node.is_some() {
            let detail = type_to_detail(tp, flow.subject.out_type, flow.subject.node);
            children.push(new_named_document_symbol(
                sf,
                lang_service,
                flow.subject.node,
                debug_flow_node_text(sf, flow.subject.node),
                detail,
                layer_symbol_kind(flow.subject.node),
            ));
        }
        for (j, transformation) in flow.transformations.iter().enumerate() {
            if transformation.callee.is_nil() {
                continue;
            }
            let detail = type_to_detail(tp, transformation.out_type, transformation.callee);
            children.push(new_named_document_symbol(
                sf,
                lang_service,
                transformation.callee,
                j.to_string() + ": " + &debug_flow_transformation_text(sf, transformation),
                detail,
                lsproto::SymbolKind::FUNCTION,
            ));
        }

        let flow_symbol = new_named_document_symbol(
            sf,
            lang_service,
            flow.node,
            "Flow ".to_string() + &i.to_string(),
            None,
            lsproto::SymbolKind::VARIABLE,
        );
        flow_symbol.borrow_mut().children = Some(children);
        symbols.push(flow_symbol);
    }

    symbols
}

// Go: etslshooks/document_symbols.go:230 newSyntheticNamespaceSymbol
fn new_synthetic_namespace_symbol(name: &str) -> DocSymbol {
    let zero = lsproto::Position::default();
    Rc::new(RefCell::new(DocumentSymbolNode {
        name: name.to_string(),
        detail: None,
        kind: lsproto::SymbolKind::PACKAGE,
        tags: None,
        deprecated: None,
        range: lsproto::Range {
            start: zero,
            end: zero,
        },
        selection_range: lsproto::Range {
            start: zero,
            end: zero,
        },
        children: Some(Vec::new()),
    }))
}

// Go: etslshooks/document_symbols.go:248 newNamedDocumentSymbol
fn new_named_document_symbol(
    sf: Node,
    lang_service: &LanguageService,
    node: Node,
    name: String,
    detail: Option<String>,
    kind: lsproto::SymbolKind,
) -> DocSymbol {
    let range = if node.is_nil() {
        let zero = lsproto::Position::default();
        lsproto::Range {
            start: zero,
            end: zero,
        }
    } else {
        // PORT: the shim's `lsconv.ToLSPPosition` drops the fidelity.
        let converters = &lang_service.converters;
        let start_pos = skip_trivia(&source_file_text(sf), node.pos());
        let end_pos = i32::max(start_pos, node.end());
        let (start, _) = converters.to_lsp_position(&sf, start_pos);
        let (end, _) = converters.to_lsp_position(&sf, end_pos);
        lsproto::Range { start, end }
    };
    Rc::new(RefCell::new(DocumentSymbolNode {
        name,
        detail,
        kind,
        tags: None,
        deprecated: None,
        range,
        selection_range: range,
        children: Some(Vec::new()),
    }))
}

// Go: etslshooks/document_symbols.go:291 newEffectDocumentSymbol
fn new_effect_document_symbol(
    tp: &mut TypeParser<'_>,
    sf: Node,
    lang_service: &LanguageService,
    node: Node,
    display_node: Node,
    detail: Option<DetailFn>,
) -> DocSymbol {
    let symbol_detail = detail.and_then(|detail| detail(tp, node));
    new_named_document_symbol(
        sf,
        lang_service,
        node,
        layer_symbol_name(sf, display_node),
        symbol_detail,
        layer_symbol_kind(display_node),
    )
}

// Go: etslshooks/document_symbols.go:311 typeToDetail
// PORT: Go also returns nil for a nil checker; the type parser always has one.
fn type_to_detail(tp: &mut TypeParser<'_>, t: TypeId, node: Node) -> Option<String> {
    if t.is_nil() || node.is_nil() {
        return None;
    }
    Some(
        tp.checker
            .type_to_string_ex(t, node, TypeFormatFlags::NO_TRUNCATION, None),
    )
}

// Go: etslshooks/document_symbols.go:319 debugFlowNodeText
fn debug_flow_node_text(sf: Node, node: Node) -> String {
    if node.is_nil() {
        return "<unknown>".to_string();
    }
    let text = get_source_text_of_node_from_source_file(sf, node, false)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    if text.is_empty() {
        return "<unknown>".to_string();
    }
    if text.len() > 80 {
        return go_byte_prefix(&text, 77) + "...";
    }
    text
}

// Go: etslshooks/document_symbols.go:333 debugFlowTransformationText
fn debug_flow_transformation_text(sf: Node, transformation: &PipingFlowTransformation) -> String {
    if transformation.callee.is_nil() {
        return "<unknown>".to_string();
    }
    debug_flow_node_text(sf, transformation.callee)
}

// Go: etslshooks/document_symbols.go:340 layerSymbolDetail
fn layer_symbol_detail(tp: &mut TypeParser<'_>, node: Node) -> Option<String> {
    let (type_check_node, types) = classification_types(tp, node);
    for t in types {
        let Some(layer) = tp.layer_type(t) else {
            continue;
        };
        let flags = TypeFormatFlags::NO_TRUNCATION;
        let r_out = tp
            .checker
            .type_to_string_ex(layer.r_out, type_check_node, flags, None);
        let e = tp
            .checker
            .type_to_string_ex(layer.e, type_check_node, flags, None);
        let r_in = tp
            .checker
            .type_to_string_ex(layer.r_in, type_check_node, flags, None);
        return Some(format!("<{r_out}, {e}, {r_in}>"));
    }
    None
}

// Go: etslshooks/document_symbols.go:356 resolveLayerDisplayNode
fn resolve_layer_display_node(node: Node) -> Node {
    if node.is_nil() || node.parent().is_nil() {
        return node;
    }
    match node.parent().kind() {
        SyntaxKind::VariableDeclaration
        | SyntaxKind::PropertyDeclaration
        | SyntaxKind::PropertyAssignment
        | SyntaxKind::ShorthandPropertyAssignment
        | SyntaxKind::PropertySignature
        | SyntaxKind::BindingElement => node.parent(),
        _ => node,
    }
}

// Go: etslshooks/document_symbols.go:373 resolveServiceDisplayNode
fn resolve_service_display_node(node: Node) -> Node {
    let mut current = node;
    while current.is_some() {
        match current.kind() {
            SyntaxKind::ClassDeclaration
            | SyntaxKind::VariableDeclaration
            | SyntaxKind::PropertyDeclaration => return current,
            _ => {}
        }
        current = current.parent();
    }
    node
}

// Go: etslshooks/document_symbols.go:385 classificationTypes
fn classification_types(tp: &mut TypeParser<'_>, node: Node) -> (Node, Vec<TypeId>) {
    if node.is_nil() {
        return (Node::NIL, Vec::new());
    }
    let t = tp.get_type_at_location(node);
    if t.is_nil() {
        return (node, Vec::new());
    }
    let mut types = vec![t];
    if node.kind() == SyntaxKind::ClassDeclaration {
        let class_name = node.name();
        if class_name.is_some() {
            let class_symbol = tp.get_symbol_at_location(class_name);
            if class_symbol.is_some() {
                let class_type = tp
                    .checker
                    .get_type_of_symbol_at_location(class_symbol, node);
                if class_type.is_some() && class_type != t {
                    types.push(class_type);
                }
            }
        }
    }
    let construct_signatures = tp.checker.get_construct_signatures(t);
    if let Some(&signature) = construct_signatures.first() {
        let return_type = tp.checker.get_return_type_of_signature_exported(signature);
        if return_type.is_some() {
            types.push(return_type);
        }
    }
    let call_signatures = tp
        .checker
        .get_signatures_of_type_exported(t, SignatureKind::CALL);
    if let Some(&signature) = call_signatures.first() {
        let return_type = tp.checker.get_return_type_of_signature_exported(signature);
        if return_type.is_some() {
            types.push(return_type);
        }
    }
    (node, types)
}

// Go: etslshooks/document_symbols.go:416 isLayerDeclaration
fn is_layer_declaration(tp: &mut TypeParser<'_>, node: Node) -> bool {
    let (_, types) = classification_types(tp, node);
    types.into_iter().any(|t| tp.is_layer_type(t))
}

// Go: etslshooks/document_symbols.go:421 isServiceDeclaration
fn is_service_declaration(tp: &mut TypeParser<'_>, node: Node) -> bool {
    if node.is_nil() {
        return false;
    }
    let (_, types) = classification_types(tp, node);
    types
        .into_iter()
        .any(|t| tp.is_service_type(t) || tp.is_context_tag(t))
}

// Go: etslshooks/document_symbols.go:434 isErrorDeclaration
fn is_error_declaration(tp: &mut TypeParser<'_>, node: Node) -> bool {
    if node.is_nil() {
        return false;
    }
    match node.kind() {
        SyntaxKind::ClassDeclaration | SyntaxKind::VariableDeclaration => {}
        _ => return false,
    }
    let (_, types) = classification_types(tp, node);
    types.into_iter().any(|t| tp.is_yieldable_error_type(t))
}

// Go: etslshooks/document_symbols.go:447 isSchemaDeclaration
fn is_schema_declaration(tp: &mut TypeParser<'_>, node: Node) -> bool {
    if node.is_nil() {
        return false;
    }
    match node.kind() {
        SyntaxKind::ClassDeclaration
        | SyntaxKind::VariableDeclaration
        | SyntaxKind::PropertyDeclaration => {}
        _ => return false,
    }
    let (_, types) = classification_types(tp, node);
    types.into_iter().any(|t| tp.is_schema_type(t))
}

// Go: etslshooks/document_symbols.go:460 resolveErrorDisplayNode
// Go: etslshooks/document_symbols.go:472 resolveSchemaDisplayNode
// PORT: both have the body of resolveServiceDisplayNode; the port calls that
// one.

// Go: etslshooks/document_symbols.go:484 isEffectSymbolDeclaration
fn is_effect_symbol_declaration(node: Node) -> bool {
    if node.is_nil() {
        return false;
    }
    match node.kind() {
        SyntaxKind::ClassDeclaration
        | SyntaxKind::VariableDeclaration
        | SyntaxKind::PropertyDeclaration => {}
        _ => return false,
    }
    let mut current = node.parent();
    while current.is_some() {
        if matches!(
            current.kind(),
            SyntaxKind::ObjectLiteralExpression
                | SyntaxKind::ForOfStatement
                | SyntaxKind::ForInStatement
        ) {
            return false;
        }
        current = current.parent();
    }
    true
}

// Go: etslshooks/document_symbols.go:503 layerSymbolName
fn layer_symbol_name(sf: Node, node: Node) -> String {
    if node.kind() == SyntaxKind::PropertyDeclaration {
        let class_like = node.parent();
        if class_like.is_some() && is_class_like(class_like) {
            // PORT: a class with no name (`export default class`, a class
            // expression) panics in Go: `GetTextOfNode(nil)` reads
            // `(*SourceFile)(nil).Text()`. The server's `recover` makes it a
            // request error, here as in Go.
            if class_like.name().is_nil() {
                crate::core::go_nil_dereference();
            }
            let class_name = get_text_of_node(class_like.name());
            let property_name = get_text_of_node(node.name());
            let (class_name, property_name) = (class_name.trim(), property_name.trim());
            if !class_name.is_empty() && !property_name.is_empty() {
                return class_name.to_string() + "." + property_name;
            }
        }
    }
    if is_declaration(node) {
        let name = get_name_of_declaration(node);
        if name.is_some() {
            let text = get_text_of_node(name);
            let text = text.trim();
            if !text.is_empty() {
                return text.to_string();
            }
        }
    }
    let text = get_source_text_of_node_from_source_file(sf, node, false);
    let text = text.trim();
    if text.is_empty() {
        return "<layer>".to_string();
    }
    if text.len() > 80 {
        return go_byte_prefix(text, 77) + "...";
    }
    text.to_string()
}

// Go: etslshooks/document_symbols.go:531 layerSymbolKind
fn layer_symbol_kind(node: Node) -> lsproto::SymbolKind {
    match node.kind() {
        SyntaxKind::VariableDeclaration | SyntaxKind::BindingElement => {
            lsproto::SymbolKind::VARIABLE
        }
        SyntaxKind::PropertyDeclaration
        | SyntaxKind::PropertyAssignment
        | SyntaxKind::PropertySignature => lsproto::SymbolKind::PROPERTY,
        SyntaxKind::FunctionDeclaration
        | SyntaxKind::FunctionExpression
        | SyntaxKind::ArrowFunction
        | SyntaxKind::MethodDeclaration => lsproto::SymbolKind::FUNCTION,
        SyntaxKind::ClassDeclaration | SyntaxKind::ClassExpression => lsproto::SymbolKind::CLASS,
        _ => lsproto::SymbolKind::VARIABLE,
    }
}

// PORT: Go `text[:n]` cuts bytes, so it can split a UTF-8 char. Go's JSON
// writer (`AllowInvalidUTF8`) then sends each byte of the split char as
// U+FFFD. This keeps the whole chars before byte `n` and puts one U+FFFD for
// each byte of a split char, which gives the same JSON.
fn go_byte_prefix(text: &str, n: usize) -> String {
    let mut end = n;
    while !text.is_char_boundary(end) {
        end -= 1;
    }
    let mut prefix = text[..end].to_string();
    prefix.extend(std::iter::repeat_n(char::REPLACEMENT_CHARACTER, n - end));
    prefix
}
