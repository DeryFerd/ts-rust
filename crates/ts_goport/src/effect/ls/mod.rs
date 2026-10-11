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
//! fixables (E4 ported the disable actions and 12 fixes; E5 the other 43),
//! refactors (E9a ported the framework and 9 refactors; E9b to E9d the other
//! 12), completions (E6), document symbols (E8) and the Layer hover (E7).

use std::sync::LazyLock;

use crate::effect::pluginoptions::resolve_effect_plugin_options_for_source_file;
use crate::effect::rulerunner::enabled_options;
use crate::effect::typeparser::TypeParser;
use crate::ls::prelude::*;

pub mod fixable;
pub mod fixables;
pub mod hover;
pub mod inlay_hints;
pub mod refactor;
pub mod refactors;
pub mod rewriter;

// Go: etslshooks/init.go:87 effectFixProvider
/// The code fix provider for the Effect diagnostic codes.
/// `ls/codeactions.rs` runs it after the built-in providers. It delegates to
/// the fixables of [`fixables::ALL`].
// PORT: Go sets `FixIds`, but nothing reads them, and no Effect action has a
// fix ID, so there is no fix-all.
pub static EFFECT_FIX_PROVIDER: LazyLock<CodeFixProvider> = LazyLock::new(|| CodeFixProvider {
    error_codes: fixables::all_error_codes(),
    get_code_actions: get_effect_code_actions,
    fix_ids: fixables::all_fix_ids(),
    get_all_code_actions: None,
});

// Go: etslshooks/init.go:94 getEffectCodeActions
// getEffectCodeActions finds applicable fixables and collects their code actions.
// PORT: Go `fixCtx.Program == nil` cannot happen in Rust, and
// `GetTypeCheckerForFile` never gives a nil checker. The plugin check is
// `rulerunner::enabled_options`, so a standalone API process without
// `TSGO_EFFECT_API=1` gets no Effect action, as it gets no Effect
// diagnostic.
fn get_effect_code_actions(
    ctx: &Context,
    fix_ctx: &CodeFixContext<'_>,
) -> Result<Vec<CodeAction>, GoError> {
    let Some(parsed_effect_config) = enabled_options(fix_ctx.program.options()) else {
        return Ok(Vec::new());
    };
    let options = resolve_effect_plugin_options_for_source_file(
        parsed_effect_config,
        source_file_file_name(fix_ctx.source_file),
        &fix_ctx.program.options().config_file_path,
        use_case_sensitive_file_names(),
    );

    let (ch, done) =
        ls_program::get_type_checker_for_file(fix_ctx.program, ctx, fix_ctx.source_file);
    let mut actions = Vec::new();
    {
        let mut ch = ch.borrow_mut();
        let program = ch.program;
        let mut tp = TypeParser::new(program, &mut ch);
        let mut f_ctx = fixable::new_context(ctx, fix_ctx, &options, &mut tp);
        for provider in fixables::by_error_code(fix_ctx.error_code) {
            actions.extend((provider.run)(&mut f_ctx));
        }
    }
    done.call();
    Ok(actions)
}

// Go: etslshooks/init.go:128 effectRefactorProvider
/// The refactor provider for the Effect refactors. `ls/codeactions.rs`
/// runs it in its refactor loop.
pub static EFFECT_REFACTOR_PROVIDER: RefactorProvider = RefactorProvider {
    get_refactor_actions: get_effect_refactor_actions,
};

// Go: etslshooks/init.go:133 getEffectRefactorActions
// getEffectRefactorActions iterates all registered refactors and collects their code actions.
// PORT: the plugin check is `rulerunner::enabled_options`, as for the code
// fix provider. One context runs all refactors of [`refactors::ALL`], in
// Go order.
fn get_effect_refactor_actions(
    ctx: &Context,
    file: Node,
    span: TextRange,
    program: &compiler::NewProgram,
    lang_service: &LanguageService,
) -> Result<Vec<CodeAction>, GoError> {
    let Some(effect_config) = enabled_options(program.options()) else {
        return Ok(Vec::new());
    };
    if !effect_config.get_refactors_enabled() {
        return Ok(Vec::new());
    }

    let (ch, done) = ls_program::get_type_checker_for_file(program, ctx, file);
    let mut actions = Vec::new();
    {
        let mut ch = ch.borrow_mut();
        let go_program = ch.program;
        let mut tp = TypeParser::new(go_program, &mut ch);
        let mut r_ctx = refactor::new_context(ctx, file, span, program, lang_service, &mut tp);
        for r in refactors::ALL {
            actions.extend((r.run)(&mut r_ctx));
        }
    }
    done.call();
    Ok(actions)
}

// Go: etslshooks/init.go:155 afterCompletion
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
