use crate::ls::lsutil::prelude::*;

use crate::frontend::core_nodemodules::{
    EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES, node_core_modules,
};
use crate::gostd::unicode;

// Port of Go `ls/lsutil/utilities.go`.

// Go: ls/lsutil/utilities.go:15 ProbablyUsesSemicolons
// PORT: Go `visit` is a recursive closure over the counters. Here it is a
// nested fn that takes them by reference.
pub fn probably_uses_semicolons(file: Node) -> bool {
    let mut with_semicolon: i32 = 0;
    let mut without_semicolon: i32 = 0;
    let n_statements_to_observe: i32 = 5;

    fn visit(
        node: Node,
        file: Node,
        with_semicolon: &mut i32,
        without_semicolon: &mut i32,
        n_statements_to_observe: i32,
    ) -> bool {
        if node.flags().intersects(NodeFlags::REPARSED) {
            return false;
        }
        if syntax_requires_trailing_semicolon_or_asi(node.kind()) {
            let last_token = get_last_token(node, file);
            if last_token.is_some() && last_token.kind() == SyntaxKind::SemicolonToken {
                *with_semicolon += 1;
            } else {
                *without_semicolon += 1;
            }
        } else if syntax_requires_trailing_comma_or_semicolon_or_asi(node.kind()) {
            let last_token = get_last_token(node, file);
            if last_token.is_some() && last_token.kind() == SyntaxKind::SemicolonToken {
                *with_semicolon += 1;
            } else if last_token.is_some() && last_token.kind() != SyntaxKind::CommaToken {
                let last_token_line = get_ecma_line_of_position(
                    file,
                    crate::astnav::get_start_of_node(last_token, file, false /*includeJSDoc*/),
                );
                let next_token_line = get_ecma_line_of_position(
                    file,
                    skip_trivia(&source_file_text(file), last_token.end()),
                );
                // Avoid counting missing semicolon in single-line objects:
                // `function f(p: { x: string /*no semicolon here is insignificant*/ }) {`
                if last_token_line != next_token_line {
                    *without_semicolon += 1;
                }
            }
        }

        if *with_semicolon + *without_semicolon >= n_statements_to_observe {
            return true;
        }

        node.for_each_child(|child| {
            visit(
                child,
                file,
                &mut *with_semicolon,
                &mut *without_semicolon,
                n_statements_to_observe,
            )
        })
    }

    file.for_each_child(|child| {
        visit(
            child,
            file,
            &mut with_semicolon,
            &mut without_semicolon,
            n_statements_to_observe,
        )
    });

    // One statement missing a semicolon isn't sufficient evidence to say the user
    // doesn't want semicolons, because they may not even be done writing that statement.
    if with_semicolon == 0 && without_semicolon <= 1 {
        return true;
    }

    // When both kinds of observation exist, treat the file as using semicolons when the
    // ratio withSemicolon/withoutSemicolon exceeds 1/nStatementsToObserve (real arithmetic),
    // implemented as an integer inequality to avoid truncation.
    if without_semicolon == 0 {
        return true;
    }
    with_semicolon * n_statements_to_observe > without_semicolon
}

// Go: ls/lsutil/utilities.go:77 ShouldUseUriStyleNodeCoreModules
pub fn should_use_uri_style_node_core_modules(
    file: Node,
    program: &crate::frontend::compiler::NewProgram,
) -> Tristate {
    for node in source_file_imports(file).iter() {
        let text = node.text();
        if node_core_modules().get(text).copied().unwrap_or(false)
            && !EXCLUSIVELY_PREFIXED_NODE_CORE_MODULES
                .get(text)
                .copied()
                .unwrap_or(false)
        {
            if text.starts_with("node:") {
                return Tristate::True;
            } else {
                return Tristate::False;
            }
        }
    }

    program.uses_uri_style_node_core_modules()
}

// Go: ls/lsutil/utilities.go:91 QuotePreferenceFromString
pub fn quote_preference_from_string(str: Node) -> QuotePreference {
    if str.token_flags().intersects(TokenFlags::SINGLE_QUOTE) {
        return QuotePreference::SINGLE;
    }
    QuotePreference::DOUBLE
}

// Go: ls/lsutil/utilities.go:98 GetQuotePreference
pub fn get_quote_preference(source_file: Node, preferences: &UserPreferences) -> QuotePreference {
    if !preferences.quote_preference.0.is_empty() && preferences.quote_preference.0 != "auto" {
        if preferences.quote_preference.0 == "single" {
            return QuotePreference::SINGLE;
        }
        return QuotePreference::DOUBLE;
    }
    // ignore synthetic import added when importHelpers: true
    let first_module_specifier = source_file_imports(source_file)
        .iter()
        .find(|&n| is_string_literal(n) && !node_is_synthesized(n.parent()))
        .unwrap_or(Node::NIL);
    if first_module_specifier.is_some() {
        return quote_preference_from_string(first_module_specifier);
    }
    QuotePreference::DOUBLE
}

// Go: ls/lsutil/utilities.go:115 ModuleSymbolToValidIdentifier
// PORT: reading `moduleSymbol.Name` needs the symbol arena, so it is the
// first parameter (as for Go `ast` functions that take a symbol).
pub fn module_symbol_to_valid_identifier(
    symbols: &SymbolArena,
    module_symbol: SymbolId,
    force_capitalize: bool,
) -> String {
    let mut module_name = symbols.sym(module_symbol).name.as_str().to_string();
    if let Some(ambient_module_name) = try_get_ambient_module_name_from_symbol_name(&module_name) {
        module_name = ambient_module_name.to_string();
    }
    module_specifier_to_valid_identifier(&module_name, force_capitalize)
}

// Go: ls/lsutil/utilities.go:123 ModuleSpecifierToValidIdentifier
// PORT: Go `[]rune(s)` turns invalid UTF-8 into U+FFFD; a Rust `&str` is
// always valid, so `chars()` gives the same runes.
pub fn module_specifier_to_valid_identifier(
    module_specifier: &str,
    force_capitalize: bool,
) -> String {
    let without_extension = crate::frontend::tspath::remove_any_file_extension(module_specifier);
    let base_name = crate::frontend::tspath::get_base_file_name(
        without_extension
            .strip_suffix("/index")
            .unwrap_or(without_extension),
    );
    let mut res: Vec<char> = Vec::new();
    let mut last_char_was_valid = true;
    let base_name_runes: Vec<char> = base_name.chars().collect();
    if !base_name_runes.is_empty() && is_identifier_start(base_name_runes[0]) {
        if force_capitalize {
            res.push(unicode::to_upper(base_name_runes[0]));
        } else {
            res.push(base_name_runes[0]);
        }
    } else {
        last_char_was_valid = false;
    }

    for &rune in base_name_runes.iter().skip(1) {
        let is_valid = is_identifier_part(rune);
        if is_valid {
            if !last_char_was_valid {
                res.push(unicode::to_upper(rune));
            } else {
                res.push(rune);
            }
        }
        last_char_was_valid = is_valid;
    }

    // Need `"_"` to ensure result isn't empty.
    let res_string: String = res.into_iter().collect();
    if !res_string.is_empty() && !is_non_contextual_keyword(string_to_token(&res_string)) {
        return res_string;
    }
    format!("_{res_string}")
}

// Go: ls/lsutil/utilities.go:158 IsNonContextualKeyword
pub fn is_non_contextual_keyword(token: SyntaxKind) -> bool {
    is_keyword_kind(token) && !is_contextual_keyword(token)
}
