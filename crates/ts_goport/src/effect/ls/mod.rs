//! Port of Effect-TS/tsgo `etslshooks` at effect-tsgo 0.51.1 (`47cb1ed7`):
//! the Effect language service hooks.
//!
//! Go registers each hook in `init()` (`etslshooks/init.go:37-85`), and the
//! patched TypeScript code calls it. The port calls the hook functions here
//! directly from the `ls/*` sites, and each site names its patch:
//!
//! | Patch | Site | Hook |
//! |---|---|---|
//! | 011 | `ls/codeactions.rs` quick fix loop | [`EFFECT_FIX_PROVIDER`] |
//! | 011 | `ls/codeactions.rs` refactor loop | [`EFFECT_REFACTOR_PROVIDER`] |
//! | 012 | `ls/hover.rs` `provide_hover` | [`hover::after_quick_info`] |
//! | 015 | `ls/inlay_hints.rs` `provide_inlay_hint` | [`inlay_hints::after_inlay_hints`] |
//! | 022 | `ls/completions_p1.rs` `provide_completion` | [`after_completion`] |
//! | 024 | `ls/symbols.rs` `get_document_symbols_for_children` | [`after_document_symbols`] |
//!
//! Every hook returns its input at once when the program has no Effect
//! plugin, as in Go. A standalone API process (`tsgo --api`) has the hooks
//! off unless `TSGO_EFFECT_API=1` (`rulerunner::enabled_options`), as for
//! the rules.
//!
//! Not ported here: patch 017 (`refactor.rewrite` in the server's code
//! action kinds; root decision D1 keeps the plain list), and the auto-import
//! transformer of `init()` (lane E3). The lists that later lanes fill:
//! fixables (E4, E5), refactors (E9), completions (E6), document symbols
//! (E8) and the Layer hover (E7).

use std::sync::LazyLock;

use crate::effect::rulerunner::enabled_options;
use crate::ls::prelude::*;

pub mod hover;
pub mod inlay_hints;

// Go: etslshooks/init.go:89 effectFixProvider
/// The code fix provider for the Effect diagnostic codes.
/// `ls/codeactions.rs` runs it after the built-in providers.
// PORT: Go `ErrorCodes: fixables.AllErrorCodes()` and
// `FixIds: fixables.AllFixIDs()`. Lane E4 ports `internal/fixables`. Until
// then `fixables.All` is empty, so both lists are empty and the provider
// matches no diagnostic.
pub static EFFECT_FIX_PROVIDER: LazyLock<CodeFixProvider> = LazyLock::new(|| CodeFixProvider {
    error_codes: Vec::new(),
    get_code_actions: get_effect_code_actions,
    fix_ids: Vec::new(),
    get_all_code_actions: None,
});

// Go: etslshooks/init.go:96 getEffectCodeActions
// getEffectCodeActions finds applicable fixables and collects their code actions.
// PORT: lane E4 ports the body after the plugin check: the options for the
// file, the checker for the file, the type parser, `fixable.NewContext` and
// each fixable of `fixables.ByErrorCode`. Until then `fixables.All` is
// empty, so Go collects no action (and the provider has no error code, so
// it is not called).
fn get_effect_code_actions(
    _ctx: &Context,
    fix_ctx: &CodeFixContext<'_>,
) -> Result<Vec<CodeAction>, GoError> {
    if enabled_options(fix_ctx.program.options()).is_none() {
        return Ok(Vec::new());
    }
    Ok(Vec::new())
}

// Go: etslshooks/init.go:130 effectRefactorProvider
/// The refactor provider for the Effect refactors. `ls/codeactions.rs`
/// runs it in its refactor loop.
pub static EFFECT_REFACTOR_PROVIDER: RefactorProvider = RefactorProvider {
    get_refactor_actions: get_effect_refactor_actions,
};

// Go: etslshooks/init.go:135 getEffectRefactorActions
// getEffectRefactorActions iterates all registered refactors and collects their code actions.
// PORT: lane E9 ports `internal/refactor` and `internal/refactors`. Until
// then `refactors.All` is empty, so Go collects no action. The port does not
// take the checker for the file until then (Go takes it and gives it back).
fn get_effect_refactor_actions(
    _ctx: &Context,
    _file: Node,
    _span: TextRange,
    program: &compiler::NewProgram,
    _ls: &LanguageService,
) -> Result<Vec<CodeAction>, GoError> {
    let Some(effect_config) = enabled_options(program.options()) else {
        return Ok(Vec::new());
    };
    if !effect_config.get_refactors_enabled() {
        return Ok(Vec::new());
    }
    Ok(Vec::new())
}

// Go: etslshooks/init.go:157 afterCompletion
/// Called by `ls/completions_p1.rs` after the completion list is built
/// (Effect-TS/tsgo patch 022). Returns the items with the Effect completions
/// appended.
// PORT: Go returns the items when `completions.All` is empty. Lane E6 ports
// `internal/completion` and `internal/completions`; until then the list is
// empty, so the items come back unchanged.
pub fn after_completion(
    _ctx: &Context,
    _sf: Node,
    _position: i32,
    items: Vec<lsproto::CompletionItem>,
    program: &compiler::NewProgram,
    _lang_service: &LanguageService,
) -> Vec<lsproto::CompletionItem> {
    let Some(effect_config) = enabled_options(program.options()) else {
        return items;
    };
    if !effect_config.get_completions_enabled() {
        return items;
    }
    items
}

// Go: etslshooks/document_symbols.go:20 afterDocumentSymbols
/// Called by `ls/symbols.rs` after the document symbols of a file are
/// collected and their expandos merged (Effect-TS/tsgo patch 024).
// PORT: lane E8 ports this function (`etslshooks/document_symbols.go`): with
// the plugin it puts a synthetic `Effect` symbol (Layers, Services, Errors,
// Schemas) first. Until then the symbols come back unchanged, as Go returns
// them without the plugin.
pub(crate) fn after_document_symbols(
    _ctx: &Context,
    _sf: Node,
    symbols: Vec<DocSymbol>,
    program: &compiler::NewProgram,
    _lang_service: &LanguageService,
) -> Vec<DocSymbol> {
    if enabled_options(program.options()).is_none() {
        return symbols;
    }
    symbols
}
