use crate::format::prelude::*;

use crate::flags_macros::{go_enum, go_flags};
use std::sync::Arc;

// Go: format/rule.go:5 ruleImpl
pub struct RuleImpl {
    pub debug_name: String,
    pub context: Vec<ContextPredicate>,
    pub action: RuleAction,
    pub flags: RuleFlags,
}

impl RuleImpl {
    // Go: format/rule.go:12 Action
    #[must_use]
    pub fn action(&self) -> RuleAction {
        self.action
    }

    // Go: format/rule.go:16 Context
    #[must_use]
    pub fn context(&self) -> &[ContextPredicate] {
        &self.context
    }

    // Go: format/rule.go:20 Flags
    #[must_use]
    pub fn flags(&self) -> RuleFlags {
        self.flags
    }

    // Go: format/rule.go:24 String
    #[must_use]
    pub fn string(&self) -> String {
        self.debug_name.clone()
    }
}

impl std::fmt::Display for RuleImpl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.debug_name)
    }
}

// Go: format/rule.go:28 tokenRange
#[derive(Clone, Debug, Default)]
pub struct TokenRange {
    pub tokens: Vec<SyntaxKind>,
    pub is_specific: bool,
}

// Go: format/rule.go:33 ruleSpec
pub struct RuleSpec {
    pub left_token_range: TokenRange,
    pub right_token_range: TokenRange,
    pub rule: Arc<RuleImpl>,
}

/**
 * A rule takes a two tokens (left/right) and a particular context
 * for which you're meant to look at them. You then declare what should the
 * whitespace annotation be between these tokens via the action param.
 *
 * @param debugName Name to print
 * @param left The left side of the comparison
 * @param right The right side of the comparison
 * @param context A set of filters to narrow down the space in which this formatter rule applies
 * @param action a declaration of the expected whitespace
 * @param flags whether the rule deletes a line or not, defaults to no-op
 */
// Go: format/rule.go:51 rule
// PORT: Go `left any, right any` switch on the dynamic type in toTokenRange;
// here they are `impl Into<TokenRange>` (see the `From` impls below). Go
// `flags ...ruleFlags` is a slice; only the first element is read.
pub fn rule(
    debug_name: &str,
    left: impl Into<TokenRange>,
    right: impl Into<TokenRange>,
    context: Vec<ContextPredicate>,
    action: RuleAction,
    flags: &[RuleFlags],
) -> RuleSpec {
    let mut flag = RuleFlags::NONE;
    if !flags.is_empty() {
        flag = flags[0];
    }
    let left_range = to_token_range(left);
    let right_range = to_token_range(right);
    let rule = Arc::new(RuleImpl {
        debug_name: debug_name.to_string(),
        context,
        action,
        flags: flag,
    });
    RuleSpec {
        left_token_range: left_range,
        right_token_range: right_range,
        rule,
    }
}

// Go: format/rule.go:71 toTokenRange
// PORT: the Go type switch is the `From` impls below. Go panics for any other
// argument type ("Unknown argument type passed to toTokenRange - only
// ast.Kind, []ast.Kind, and tokenRange supported"); in Rust that case does
// not compile.
pub fn to_token_range(e: impl Into<TokenRange>) -> TokenRange {
    e.into()
}

// Go: format/rule.go:73 `case ast.Kind`
impl From<SyntaxKind> for TokenRange {
    fn from(t: SyntaxKind) -> Self {
        TokenRange {
            is_specific: true,
            tokens: vec![t],
        }
    }
}

// Go: format/rule.go:75 `case []ast.Kind`
impl From<Vec<SyntaxKind>> for TokenRange {
    fn from(t: Vec<SyntaxKind>) -> Self {
        TokenRange {
            is_specific: true,
            tokens: t,
        }
    }
}

// Go: format/rule.go:77 `case tokenRange` is the identity `From<T> for T`.

// Go: format/rule.go:83 contextPredicate
// PORT: Go `func(ctx *FormattingContext) bool`. The rules map is a
// process-wide static, so predicates are `Send + Sync`. `&mut` because the
// FormattingContext getters cache tristates (Go mutates through the pointer).
pub type ContextPredicate = Arc<dyn Fn(&mut FormattingContext) -> bool + Send + Sync>;

// Go: format/rule.go:85 anyContext
pub static ANY_CONTEXT: Vec<ContextPredicate> = Vec::new();

// Go: format/rule.go:87 ruleAction
go_flags!(RuleAction, i32 {
    NONE = 0; // ruleActionNone
    STOP_PROCESSING_SPACE_ACTIONS = 1 << 0; // ruleActionStopProcessingSpaceActions
    STOP_PROCESSING_TOKEN_ACTIONS = 1 << 1; // ruleActionStopProcessingTokenActions
    INSERT_SPACE = 1 << 2; // ruleActionInsertSpace
    INSERT_NEW_LINE = 1 << 3; // ruleActionInsertNewLine
    DELETE_SPACE = 1 << 4; // ruleActionDeleteSpace
    DELETE_TOKEN = 1 << 5; // ruleActionDeleteToken
    INSERT_TRAILING_SEMICOLON = 1 << 6; // ruleActionInsertTrailingSemicolon

    STOP_ACTION = (1 << 0) | (1 << 1); // ruleActionStopProcessingSpaceActions | ruleActionStopProcessingTokenActions
    MODIFY_SPACE_ACTION = (1 << 2) | (1 << 3) | (1 << 4); // ruleActionInsertSpace | ruleActionInsertNewLine | ruleActionDeleteSpace
    MODIFY_TOKEN_ACTION = (1 << 5) | (1 << 6); // ruleActionDeleteToken | ruleActionInsertTrailingSemicolon
});

// Go: format/rule.go:104 ruleFlags
go_enum!(RuleFlags, i32 {
    NONE = 0; // ruleFlagsNone
    CAN_DELETE_NEW_LINES = 1; // ruleFlagsCanDeleteNewLines
});
