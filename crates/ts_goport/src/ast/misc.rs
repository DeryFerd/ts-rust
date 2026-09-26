//! Go `ast/symbol.go`, `ast/diagnostic.go`, `ast/precedence.go`,
//! `ast/modifierflags.go`, `ast/flow.go`, `ast/checkflags.go`,
//! `ast/symbolflags.go`, `ast/functionflags.go`, `ast/positionmap.go` and
//! `ast/ids.go` (functions and non-flag types only; the flag consts live in
//! `crate::flags`).

use crate::prelude::*;

// ---------------------------------------------------------------------------
// symbol.go
// ---------------------------------------------------------------------------

impl Symbol {
    // Go: ast/symbol.go:23 IsExternalModule
    #[must_use]
    pub fn is_external_module(&self) -> bool {
        self.flags.intersects(SymbolFlags::MODULE)
            && !self.name.is_empty()
            && self.name.as_bytes()[0] == b'"'
    }

    // Go: ast/symbol.go:27 IsStatic
    #[must_use]
    pub fn is_static(&self) -> bool {
        if self.value_declaration.is_nil() {
            return false;
        }
        let modifier_flags = self.value_declaration.modifier_flags();
        modifier_flags.intersects(ModifierFlags::STATIC)
    }

    // Go: ast/symbol.go:36 CombinedLocalAndExportSymbolFlags
    // See comment on `declareModuleMember` in `binder.go`.
    // PORT: Go follows `s.ExportSymbol` directly; here the arena that owns the
    // export symbol is passed in.
    #[must_use]
    pub fn combined_local_and_export_symbol_flags(&self, symbols: &SymbolArena) -> SymbolFlags {
        if self.export_symbol.is_some() {
            return self.flags | symbols.sym(self.export_symbol).flags;
        }
        self.flags
    }
}

// PORT: Go uses the byte 0xFE, which is invalid UTF-8. A Rust `String` holds
// it in the port form of Go strings (see `scanner_util::GO_STRING_MARKER`):
// U+FDD0 + U+10F7FE, the invalid byte unit for 0xFE. Source text with the
// byte 0xFE has the same port form, so it names the same internal symbols as
// in Go, and a real U+FFFE char stays an ordinary char. Go byte checks such as
// `name[0] == '\xFE'` port to `name.starts_with(INTERNAL_SYMBOL_NAME_PREFIX)`.
pub const INTERNAL_SYMBOL_NAME_PREFIX: &str = "\u{FDD0}\u{10F7FE}"; // Invalid as IdentifierName

pub const INTERNAL_SYMBOL_NAME_CALL: &str = "\u{FDD0}\u{10F7FE}call"; // Call signatures
pub const INTERNAL_SYMBOL_NAME_CONSTRUCTOR: &str = "\u{FDD0}\u{10F7FE}constructor"; // Constructor implementations
pub const INTERNAL_SYMBOL_NAME_NEW: &str = "\u{FDD0}\u{10F7FE}new"; // Constructor signatures
pub const INTERNAL_SYMBOL_NAME_INDEX: &str = "\u{FDD0}\u{10F7FE}index"; // Index signatures
pub const INTERNAL_SYMBOL_NAME_EXPORT_STAR: &str = "\u{FDD0}\u{10F7FE}export"; // Module export * declarations
pub const INTERNAL_SYMBOL_NAME_GLOBAL: &str = "\u{FDD0}\u{10F7FE}global"; // Global self-reference
pub const INTERNAL_SYMBOL_NAME_MISSING: &str = "\u{FDD0}\u{10F7FE}missing"; // Indicates missing symbol
pub const INTERNAL_SYMBOL_NAME_TYPE: &str = "\u{FDD0}\u{10F7FE}type"; // Anonymous type literal symbol
pub const INTERNAL_SYMBOL_NAME_OBJECT: &str = "\u{FDD0}\u{10F7FE}object"; // Anonymous object literal declaration
pub const INTERNAL_SYMBOL_NAME_JSX_ATTRIBUTES: &str = "\u{FDD0}\u{10F7FE}jsxAttributes"; // Anonymous JSX attributes object literal declaration
pub const INTERNAL_SYMBOL_NAME_CLASS: &str = "\u{FDD0}\u{10F7FE}class"; // Unnamed class expression
pub const INTERNAL_SYMBOL_NAME_FUNCTION: &str = "\u{FDD0}\u{10F7FE}function"; // Unnamed function expression
pub const INTERNAL_SYMBOL_NAME_COMPUTED: &str = "\u{FDD0}\u{10F7FE}computed"; // Computed property name declaration with dynamic name
pub const INTERNAL_SYMBOL_NAME_ASSIGNMENT_DECLARATION: &str = "\u{FDD0}\u{10F7FE}assignment"; // Assignment declarations
pub const INTERNAL_SYMBOL_NAME_INSTANTIATION_EXPRESSION: &str =
    "\u{FDD0}\u{10F7FE}instantiationExpression"; // Instantiation expressions
pub const INTERNAL_SYMBOL_NAME_IMPORT_ATTRIBUTES: &str = "\u{FDD0}\u{10F7FE}importAttributes";
pub const INTERNAL_SYMBOL_NAME_EXPORT_EQUALS: &str = "export="; // Export assignment symbol
pub const INTERNAL_SYMBOL_NAME_DEFAULT: &str = "default"; // Default export symbol (technically not wholly internal, but included here for usability)
pub const INTERNAL_SYMBOL_NAME_THIS: &str = "this";
pub const INTERNAL_SYMBOL_NAME_MODULE_EXPORTS: &str = "module.exports";

// Go: ast/symbol.go:72 SymbolName
#[must_use]
pub fn symbol_name(symbols: &SymbolArena, symbol: SymbolId) -> String {
    let s = symbols.sym(symbol);
    if s.value_declaration.is_some()
        && is_private_identifier_class_element_declaration(s.value_declaration)
    {
        return s.value_declaration.name().text().to_string();
    }
    s.name.to_string()
}

// Go: ast/symbol.go:80 EscapeAllInternalSymbolNames
// EscapeAllInternalSymbolNames replaces internal symbol name markers ("\xFE") with "__".
// PORT: each byte 0xFE is the unit INTERNAL_SYMBOL_NAME_PREFIX in the port
// form. A plain text search could also match a U+FDD0 unit (U+FDD0 twice)
// followed by a real U+10F7FE char, so this reads the units.
#[must_use]
pub fn escape_all_internal_symbol_names(name: &str) -> String {
    if !contains_go_string_marker(name) {
        return name.to_string();
    }
    let mut out = String::with_capacity(name.len());
    let mut i = 0usize;
    while i < name.len() {
        let (unit, size) = go_unit_at(name, i);
        if unit == GoUnit::InvalidByte(0xFE) {
            out.push_str("__");
        } else {
            out.push_str(&name[i..i + size]);
        }
        i += size;
    }
    out
}

// ---------------------------------------------------------------------------
// diagnostic.go
// ---------------------------------------------------------------------------

/// Go `ast.RepopulateDiagnosticKind`: the kind of repopulation for a
/// diagnostic chain entry.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RepopulateDiagnosticKind(pub i32);

impl RepopulateDiagnosticKind {
    pub const MODE_MISMATCH: Self = Self(1); // RepopulateModeMismatch
    pub const MODULE_NOT_FOUND: Self = Self(2); // RepopulateModuleNotFound
}

/// Go `ast.RepopulateDiagnosticInfo`. It stores information needed to
/// recompute a diagnostic chain entry during incremental builds when the
/// program state may have changed.
/// PORT: Go `core.ResolutionMode` is an alias of `core.ModuleKind`.
#[derive(Clone, Debug, Default)]
pub struct RepopulateDiagnosticInfo {
    pub kind: RepopulateDiagnosticKind,
    pub module_reference: String,
    pub mode: ModuleKind,
    pub package_name: String,
}

// PORT: `core::Diagnostic` has no `messageKey` field. The message key is
// always `message.key()`.
impl Diagnostic {
    // Go: ast/diagnostic.go:50 File
    #[must_use]
    pub fn file(&self) -> Node {
        self.file
    }

    // Go: ast/diagnostic.go:51 Pos
    #[must_use]
    pub fn pos(&self) -> i32 {
        self.pos
    }

    // Go: ast/diagnostic.go:52 End
    #[must_use]
    pub fn end(&self) -> i32 {
        self.end
    }

    // Go: ast/diagnostic.go:53 Len
    #[must_use]
    pub fn len(&self) -> i32 {
        self.end - self.pos
    }

    // Go: ast/diagnostic.go:54 Loc
    #[must_use]
    pub fn loc(&self) -> TextRange {
        TextRange::new(self.pos, self.end)
    }

    // Go: ast/diagnostic.go:55 Code
    #[must_use]
    pub fn code(&self) -> i32 {
        self.code
    }

    // Go: ast/diagnostic.go:56 Category
    #[must_use]
    pub fn category(&self) -> ts_diagnostics::Category {
        self.category
    }

    // Go: ast/diagnostic.go:57 MessageKey
    #[must_use]
    pub fn message_key(&self) -> &'static str {
        self.message.key()
    }

    // Go: ast/diagnostic.go:58 MessageArgs
    #[must_use]
    pub fn message_args(&self) -> &[String] {
        &self.message_args
    }

    // Go: ast/diagnostic.go:59 MessageChain
    #[must_use]
    pub fn message_chain(&self) -> &[Diagnostic] {
        &self.message_chain
    }

    // Go: ast/diagnostic.go:60 RelatedInformation
    #[must_use]
    pub fn related_information(&self) -> &[Diagnostic] {
        &self.related_information
    }

    // Go: ast/diagnostic.go:61 ReportsUnnecessary
    #[must_use]
    pub fn reports_unnecessary(&self) -> bool {
        self.reports_unnecessary
    }

    // Go: ast/diagnostic.go:62 ReportsDeprecated
    #[must_use]
    pub fn reports_deprecated(&self) -> bool {
        self.reports_deprecated
    }

    // Go: ast/diagnostic.go:63 SkippedOnNoEmit
    #[must_use]
    pub fn skipped_on_no_emit(&self) -> bool {
        self.skipped_on_no_emit
    }

    // Go: ast/diagnostic.go:64 RepopulateInfo
    #[must_use]
    pub fn repopulate_info(&self) -> Option<std::sync::Arc<RepopulateDiagnosticInfo>> {
        self.repopulate_info.clone()
    }

    // Go: ast/diagnostic.go:66 SetFile
    pub fn set_file(&mut self, file: Node) {
        self.file = file;
    }

    // Go: ast/diagnostic.go:67 SetLocation
    pub fn set_location(&mut self, loc: TextRange) {
        self.pos = loc.pos();
        self.end = loc.end();
    }

    // Go: ast/diagnostic.go:68 SetCategory
    pub fn set_category(&mut self, category: ts_diagnostics::Category) {
        self.category = category;
    }

    // Go: ast/diagnostic.go:69 SetSkippedOnNoEmit
    pub fn set_skipped_on_no_emit(&mut self) {
        self.skipped_on_no_emit = true;
    }

    // Go: ast/diagnostic.go:70 SetRepopulateInfo
    pub fn set_repopulate_info(&mut self, info: Option<std::sync::Arc<RepopulateDiagnosticInfo>>) {
        self.repopulate_info = info;
    }

    // Go: ast/diagnostic.go:72 SetMessageChain
    // PORT: Go returns the receiver for chaining; this returns `&mut Self`.
    pub fn set_message_chain(&mut self, message_chain: Vec<Diagnostic>) -> &mut Self {
        self.message_chain = message_chain;
        self
    }

    // Go: ast/diagnostic.go:77 AddMessageChain
    pub fn add_message_chain(&mut self, message_chain: Option<Diagnostic>) -> &mut Self {
        if let Some(message_chain) = message_chain {
            self.message_chain.push(message_chain);
        }
        self
    }

    // Go: ast/diagnostic.go:84 SetRelatedInfo
    pub fn set_related_info(&mut self, related_information: Vec<Diagnostic>) -> &mut Self {
        self.related_information = related_information;
        self
    }

    // Go: ast/diagnostic.go:89 AddRelatedInfo
    pub fn add_related_info(&mut self, related_information: Option<Diagnostic>) -> &mut Self {
        if let Some(related_information) = related_information {
            self.related_information.push(related_information);
        }
        self
    }

    // Go: ast/diagnostic.go:96 Clone
    // PORT: Go `d.Clone()` is a shallow copy; use the derived `Clone::clone`.
    // Go shares the slices between the copies, but no Go caller mutates them
    // in place after cloning, so a deep clone behaves the same.

    // Go: ast/diagnostic.go:101 Localize
    // PORT: the port resolves the message when it makes the diagnostic (see
    // NewDiagnosticFromSerialized below), so the Go `d.messageKey` is never
    // read and the key is "".
    #[must_use]
    pub fn localize(&self, locale: &crate::locale::Locale) -> String {
        crate::diagnostics_loc::localize(locale, Some(self.message), "", &self.message_args)
    }

    // Go: ast/diagnostic.go:106 String
    // For debugging only.
    #[must_use]
    pub fn string(&self) -> String {
        format_message(self.message, &self.message_args)
    }
}

// Go: diagnostics/diagnostics.go:117 Format
// PORT: also Go `diagnostics.Localize` with the default locale; the port has
// only the English messages. `Message::format` replaces the placeholders,
// and Go panics on a bad placeholder.
pub fn format_message(message: &'static ts_diagnostics::Message, args: &[String]) -> String {
    // Replace invalid UTF-8 with Unicode replacement character
    // PORT: each arg is the port form of a Go string (see
    // `scanner_util::GO_STRING_MARKER`), so only an arg with a marker can
    // hold invalid bytes.
    let valid: Vec<String>;
    let args = if args.iter().any(|arg| contains_go_string_marker(arg)) {
        valid = args
            .iter()
            .map(|arg| go_to_valid_utf8(arg).into_owned())
            .collect();
        &valid[..]
    } else {
        args
    };
    match message.format(args) {
        Ok(text) => text,
        Err(_) => panic!("Invalid formatting placeholder"),
    }
}

// Go: ast/diagnostic.go:110 NewDiagnosticFromSerialized
// PORT: Go keeps `message` nil and resolves the key lazily in `Localize`
// (panicking on an unknown key). `core::Diagnostic` needs the message, so it
// is resolved here with the same panic.
#[allow(clippy::too_many_arguments)]
#[must_use]
pub fn new_diagnostic_from_serialized(
    file: Node,
    loc: TextRange,
    code: i32,
    category: ts_diagnostics::Category,
    message_key: &str,
    message_args: Vec<String>,
    message_chain: Vec<Diagnostic>,
    related_information: Vec<Diagnostic>,
    reports_unnecessary: bool,
    reports_deprecated: bool,
    skipped_on_no_emit: bool,
) -> Diagnostic {
    let message = match ts_diagnostics::message_by_key(message_key) {
        Some(message) => message,
        None => panic!("Unknown diagnostic message: {message_key}"),
    };
    Diagnostic {
        file,
        pos: loc.pos(),
        end: loc.end(),
        code,
        category,
        message,
        message_args,
        message_chain,
        related_information,
        reports_unnecessary,
        reports_deprecated,
        skipped_on_no_emit,
        repopulate_info: None,
    }
}

// Go: ast/diagnostic.go:138 NewDiagnostic
#[must_use]
pub fn new_diagnostic(
    file: Node,
    loc: TextRange,
    message: &'static ts_diagnostics::Message,
    args: Vec<String>,
) -> Diagnostic {
    Diagnostic {
        file,
        pos: loc.pos(),
        end: loc.end(),
        code: message.code() as i32,
        category: message.category(),
        message,
        message_args: args,
        message_chain: Vec::new(),
        related_information: Vec::new(),
        reports_unnecessary: message.reports_unnecessary(),
        reports_deprecated: message.reports_deprecated(),
        skipped_on_no_emit: false,
        repopulate_info: None,
    }
}

// Go: ast/diagnostic.go:152 NewDiagnosticChain
#[must_use]
pub fn new_diagnostic_chain(
    chain: Option<Diagnostic>,
    message: &'static ts_diagnostics::Message,
    args: Vec<String>,
) -> Diagnostic {
    if let Some(chain) = chain {
        let related_information = chain.related_information.clone();
        let mut result = new_diagnostic(chain.file, chain.loc(), message, args);
        result
            .add_message_chain(Some(chain))
            .set_related_info(related_information);
        return result;
    }
    new_diagnostic(Node::NIL, TextRange::new(0, 0), message, args)
}

// Go: ast/diagnostic.go:159 NewCompilerDiagnostic
// PORT: Go `core.UndefinedTextRange()` is `TextRange{-1, -1}`.
#[must_use]
pub fn new_compiler_diagnostic(
    message: &'static ts_diagnostics::Message,
    args: Vec<String>,
) -> Diagnostic {
    new_diagnostic(Node::NIL, TextRange::new(-1, -1), message, args)
}

/// Go `ast.DiagnosticsCollection`. The mutex is dropped (single thread).
/// PORT: `file_diagnostics` is an `IndexMap` so `get_diagnostics` sees a
/// deterministic order before its sort. Go map order is random there.
#[derive(Clone, Debug, Default)]
pub struct DiagnosticsCollection {
    pub count: i32,
    pub file_diagnostics: IndexMap<String, Vec<Diagnostic>>,
    pub file_diagnostics_sorted: FxHashSet<String>,
    pub non_file_diagnostics: Vec<Diagnostic>,
    pub non_file_diagnostics_sorted: bool,
}

impl DiagnosticsCollection {
    // Go: ast/diagnostic.go:172 Add
    pub fn add(&mut self, diagnostic: Diagnostic) {
        self.count += 1;

        if diagnostic.file().is_some() {
            let file_name = source_file_file_name(diagnostic.file()).to_string();
            self.file_diagnostics
                .entry(file_name.clone())
                .or_default()
                .push(diagnostic);
            self.file_diagnostics_sorted.remove(&file_name);
        } else {
            self.non_file_diagnostics.push(diagnostic);
            self.non_file_diagnostics_sorted = false;
        }
    }

    // Go: ast/diagnostic.go:191 Lookup
    // PORT: Go returns the stored pointer; this returns a clone of it.
    pub fn lookup(&mut self, diagnostic: &Diagnostic) -> Option<Diagnostic> {
        let diagnostics = if diagnostic.file().is_some() {
            self.get_diagnostics_for_file_locked(source_file_file_name(diagnostic.file()))
        } else {
            self.get_global_diagnostics_locked()
        };
        // Go slices.BinarySearchFunc: the first index where cmp >= 0.
        let i = diagnostics.partition_point(|d| compare_diagnostics(d, diagnostic) < 0);
        if i < diagnostics.len() && compare_diagnostics(&diagnostics[i], diagnostic) == 0 {
            return Some(diagnostics[i].clone());
        }
        None
    }

    // Go: ast/diagnostic.go:207 GetGlobalDiagnostics
    pub fn get_global_diagnostics(&mut self) -> Vec<Diagnostic> {
        self.get_global_diagnostics_locked()
    }

    // Go: ast/diagnostic.go:214 getGlobalDiagnosticsLocked
    fn get_global_diagnostics_locked(&mut self) -> Vec<Diagnostic> {
        if !self.non_file_diagnostics_sorted {
            self.non_file_diagnostics
                .sort_by(|a, b| compare_diagnostics(a, b).cmp(&0));
            self.non_file_diagnostics_sorted = true;
        }
        self.non_file_diagnostics.clone()
    }

    // Go: ast/diagnostic.go:222 GetDiagnosticsForFile
    pub fn get_diagnostics_for_file(&mut self, file_name: &str) -> Vec<Diagnostic> {
        self.get_diagnostics_for_file_locked(file_name)
    }

    // Go: ast/diagnostic.go:229 getDiagnosticsForFileLocked
    fn get_diagnostics_for_file_locked(&mut self, file_name: &str) -> Vec<Diagnostic> {
        if !self.file_diagnostics_sorted.contains(file_name) {
            if let Some(diagnostics) = self.file_diagnostics.get_mut(file_name) {
                diagnostics.sort_by(|a, b| compare_diagnostics(a, b).cmp(&0));
            }
            self.file_diagnostics_sorted.insert(file_name.to_string());
        }
        self.file_diagnostics
            .get(file_name)
            .cloned()
            .unwrap_or_default()
    }

    // Go: ast/diagnostic.go:237 GetDiagnostics
    #[must_use]
    pub fn get_diagnostics(&self) -> Vec<Diagnostic> {
        let mut diagnostics: Vec<Diagnostic> = Vec::with_capacity(self.count as usize);
        diagnostics.extend(self.non_file_diagnostics.iter().cloned());
        for diags in self.file_diagnostics.values() {
            diagnostics.extend(diags.iter().cloned());
        }
        // PORT: Go uses the unstable slices.SortFunc; any order of equal
        // elements is valid there, so a stable sort is used here.
        diagnostics.sort_by(|a, b| compare_diagnostics(a, b).cmp(&0));
        diagnostics
    }
}

// Go: ast/diagnostic.go:250 getDiagnosticPath
// PORT: returns `&'static str` (file names live for the program).
fn get_diagnostic_path(d: &Diagnostic) -> &'static str {
    if d.file().is_some() {
        return source_file_file_name(d.file());
    }
    ""
}

// Go: ast/diagnostic.go:257 EqualDiagnostics
#[must_use]
pub fn equal_diagnostics(d1: &Diagnostic, d2: &Diagnostic) -> bool {
    if std::ptr::eq(d1, d2) {
        return true;
    }
    equal_diagnostics_no_related_info(d1, d2)
        && d1.related_information().len() == d2.related_information().len()
        && d1
            .related_information()
            .iter()
            .zip(d2.related_information())
            .all(|(a, b)| equal_diagnostics(a, b))
}

// Go: ast/diagnostic.go:265 EqualDiagnosticsNoRelatedInfo
#[must_use]
pub fn equal_diagnostics_no_related_info(d1: &Diagnostic, d2: &Diagnostic) -> bool {
    if std::ptr::eq(d1, d2) {
        return true;
    }
    get_diagnostic_path(d1) == get_diagnostic_path(d2)
        && d1.pos() == d2.pos()
        && d1.end() == d2.end()
        && d1.code() == d2.code()
        && d1.message_args() == d2.message_args()
        && d1.message_chain().len() == d2.message_chain().len()
        && d1
            .message_chain()
            .iter()
            .zip(d2.message_chain())
            .all(|(a, b)| equal_message_chain(a, b))
}

// Go: ast/diagnostic.go:276 equalMessageChain
fn equal_message_chain(c1: &Diagnostic, c2: &Diagnostic) -> bool {
    if std::ptr::eq(c1, c2) {
        return true;
    }
    c1.code() == c2.code()
        && c1.message_args() == c2.message_args()
        && c1.message_chain().len() == c2.message_chain().len()
        && c1
            .message_chain()
            .iter()
            .zip(c2.message_chain())
            .all(|(a, b)| equal_message_chain(a, b))
}

// Go `slices.Compare` / `strings.Compare` as -1, 0, 1.
fn ordering_to_int(ordering: std::cmp::Ordering) -> i32 {
    match ordering {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

// Go: ast/diagnostic.go:285 compareMessageChainSize
fn compare_message_chain_size(c1: &[Diagnostic], c2: &[Diagnostic]) -> i32 {
    let mut c = c2.len() as i32 - c1.len() as i32;
    if c != 0 {
        return c;
    }
    for i in 0..c1.len() {
        c = compare_message_chain_size(c1[i].message_chain(), c2[i].message_chain());
        if c != 0 {
            return c;
        }
    }
    0
}

// Go: ast/diagnostic.go:299 compareMessageChainContent
fn compare_message_chain_content(c1: &[Diagnostic], c2: &[Diagnostic]) -> i32 {
    for i in 0..c1.len() {
        let mut c = ordering_to_int(compare_go_bytes_slices(
            c1[i].message_args(),
            c2[i].message_args(),
        ));
        if c != 0 {
            return c;
        }
        // PORT: Go checks `!= nil`; an empty chain recurses over nothing and
        // returns 0, so `!is_empty()` is equivalent.
        if !c1[i].message_chain().is_empty() {
            c = compare_message_chain_content(c1[i].message_chain(), c2[i].message_chain());
            if c != 0 {
                return c;
            }
        }
    }
    0
}

// Go: ast/diagnostic.go:315 compareRelatedInfo
fn compare_related_info(r1: &[Diagnostic], r2: &[Diagnostic]) -> i32 {
    let mut c = r2.len() as i32 - r1.len() as i32;
    if c != 0 {
        return c;
    }
    for i in 0..r1.len() {
        c = compare_diagnostics(&r1[i], &r2[i]);
        if c != 0 {
            return c;
        }
    }
    0
}

// Go: ast/diagnostic.go:329 CompareDiagnostics
#[must_use]
pub fn compare_diagnostics(d1: &Diagnostic, d2: &Diagnostic) -> i32 {
    if std::ptr::eq(d1, d2) {
        return 0;
    }
    // PORT: Go compares the bytes of the strings, which are port forms here
    // (see `scanner_util::compare_go_bytes`).
    let mut c = ordering_to_int(compare_go_bytes(
        get_diagnostic_path(d1),
        get_diagnostic_path(d2),
    ));
    if c != 0 {
        return c;
    }
    c = d1.pos() - d2.pos();
    if c != 0 {
        return c;
    }
    c = d1.end() - d2.end();
    if c != 0 {
        return c;
    }
    c = d1.code() - d2.code();
    if c != 0 {
        return c;
    }
    c = ordering_to_int(compare_go_bytes_slices(
        d1.message_args(),
        d2.message_args(),
    ));
    if c != 0 {
        return c;
    }
    c = compare_message_chain_size(d1.message_chain(), d2.message_chain());
    if c != 0 {
        return c;
    }
    c = compare_message_chain_content(d1.message_chain(), d2.message_chain());
    if c != 0 {
        return c;
    }
    compare_related_info(d1.related_information(), d2.related_information())
}

// ---------------------------------------------------------------------------
// precedence.go (OperatorPrecedence, OperatorPrecedenceFlags and
// TypePrecedence consts are in `crate::flags`)
// ---------------------------------------------------------------------------

// Go: ast/precedence.go:189 getOperator
fn get_operator(expression: Node) -> SyntaxKind {
    match expression.kind() {
        SyntaxKind::BinaryExpression => expression.operator_token().kind(),
        SyntaxKind::PrefixUnaryExpression => expression.operator(),
        SyntaxKind::PostfixUnaryExpression => expression.operator(),
        _ => expression.kind(),
    }
}

// Go: ast/precedence.go:203 GetExpressionPrecedence
// Gets the precedence of an expression
#[must_use]
pub fn get_expression_precedence(expression: Node) -> OperatorPrecedence {
    let operator = get_operator(expression);
    let mut flags = OperatorPrecedenceFlags::NONE;
    if expression.kind() == SyntaxKind::NewExpression && expression.argument_list().is_nil() {
        flags = OperatorPrecedenceFlags::NEW_WITHOUT_ARGUMENTS;
    } else if is_optional_chain(expression) {
        flags = OperatorPrecedenceFlags::OPTIONAL_CHAIN;
    }
    get_operator_precedence(expression.kind(), operator, flags)
}

// Go: ast/precedence.go:223 GetOperatorPrecedence
// Gets the precedence of an operator
#[must_use]
pub fn get_operator_precedence(
    node_kind: SyntaxKind,
    operator_kind: SyntaxKind,
    flags: OperatorPrecedenceFlags,
) -> OperatorPrecedence {
    match node_kind {
        SyntaxKind::SpreadElement => OperatorPrecedence::SPREAD,
        SyntaxKind::YieldExpression => OperatorPrecedence::YIELD,
        // !!! By necessity, this differs from the old compiler to better align with ParenthesizerRules. consider backporting
        SyntaxKind::ArrowFunction => OperatorPrecedence::ASSIGNMENT,
        SyntaxKind::ConditionalExpression => OperatorPrecedence::CONDITIONAL,
        SyntaxKind::BinaryExpression => match operator_kind {
            SyntaxKind::CommaToken => OperatorPrecedence::COMMA,

            SyntaxKind::EqualsToken
            | SyntaxKind::PlusEqualsToken
            | SyntaxKind::MinusEqualsToken
            | SyntaxKind::AsteriskAsteriskEqualsToken
            | SyntaxKind::AsteriskEqualsToken
            | SyntaxKind::SlashEqualsToken
            | SyntaxKind::PercentEqualsToken
            | SyntaxKind::LessThanLessThanEqualsToken
            | SyntaxKind::GreaterThanGreaterThanEqualsToken
            | SyntaxKind::GreaterThanGreaterThanGreaterThanEqualsToken
            | SyntaxKind::AmpersandEqualsToken
            | SyntaxKind::CaretEqualsToken
            | SyntaxKind::BarEqualsToken
            | SyntaxKind::BarBarEqualsToken
            | SyntaxKind::AmpersandAmpersandEqualsToken
            | SyntaxKind::QuestionQuestionEqualsToken => OperatorPrecedence::ASSIGNMENT,

            _ => get_binary_operator_precedence(operator_kind),
        },
        // TODO: Should prefix `++` and `--` be moved to the `Update` precedence?
        SyntaxKind::TypeAssertionExpression
        | SyntaxKind::NonNullExpression
        | SyntaxKind::PrefixUnaryExpression
        | SyntaxKind::TypeOfExpression
        | SyntaxKind::VoidExpression
        | SyntaxKind::DeleteExpression
        | SyntaxKind::AwaitExpression => OperatorPrecedence::UNARY,

        SyntaxKind::PostfixUnaryExpression => OperatorPrecedence::UPDATE,

        // !!! By necessity, this differs from the old compiler to better align with ParenthesizerRules. consider backporting
        SyntaxKind::PropertyAccessExpression | SyntaxKind::ElementAccessExpression => {
            if flags.intersects(OperatorPrecedenceFlags::OPTIONAL_CHAIN) {
                return OperatorPrecedence::OPTIONAL_CHAIN;
            }
            OperatorPrecedence::MEMBER
        }

        SyntaxKind::CallExpression => {
            if flags.intersects(OperatorPrecedenceFlags::OPTIONAL_CHAIN) {
                return OperatorPrecedence::OPTIONAL_CHAIN;
            }
            OperatorPrecedence::MEMBER
        }

        // !!! By necessity, this differs from the old compiler to better align with ParenthesizerRules. consider backporting
        SyntaxKind::NewExpression => {
            if flags.intersects(OperatorPrecedenceFlags::NEW_WITHOUT_ARGUMENTS) {
                return OperatorPrecedence::LEFT_HAND_SIDE;
            }
            OperatorPrecedence::MEMBER
        }

        // !!! By necessity, this differs from the old compiler to better align with ParenthesizerRules. consider backporting
        SyntaxKind::TaggedTemplateExpression
        | SyntaxKind::MetaProperty
        | SyntaxKind::ExpressionWithTypeArguments => OperatorPrecedence::MEMBER,

        SyntaxKind::AsExpression | SyntaxKind::SatisfiesExpression => {
            OperatorPrecedence::RELATIONAL
        }

        SyntaxKind::ThisKeyword
        | SyntaxKind::SuperKeyword
        | SyntaxKind::ImportKeyword
        | SyntaxKind::Identifier
        | SyntaxKind::PrivateIdentifier
        | SyntaxKind::NullKeyword
        | SyntaxKind::TrueKeyword
        | SyntaxKind::FalseKeyword
        | SyntaxKind::NumericLiteral
        | SyntaxKind::BigIntLiteral
        | SyntaxKind::StringLiteral
        | SyntaxKind::ArrayLiteralExpression
        | SyntaxKind::ObjectLiteralExpression
        | SyntaxKind::FunctionExpression
        | SyntaxKind::ClassExpression
        | SyntaxKind::RegularExpressionLiteral
        | SyntaxKind::NoSubstitutionTemplateLiteral
        | SyntaxKind::TemplateExpression
        | SyntaxKind::OmittedExpression
        | SyntaxKind::JsxElement
        | SyntaxKind::JsxSelfClosingElement
        | SyntaxKind::JsxFragment
        | SyntaxKind::MissingDeclaration => OperatorPrecedence::PRIMARY,

        // !!! By necessity, this differs from the old compiler to support emit. consider backporting
        SyntaxKind::ParenthesizedExpression => OperatorPrecedence::PARENTHESES,

        _ => OperatorPrecedence::INVALID,
    }
}

// Go: ast/precedence.go:336 GetBinaryOperatorPrecedence
// Gets the precedence of a binary operator
#[must_use]
pub fn get_binary_operator_precedence(operator_kind: SyntaxKind) -> OperatorPrecedence {
    match operator_kind {
        SyntaxKind::QuestionQuestionToken => return OperatorPrecedence::COALESCE,
        SyntaxKind::BarBarToken => return OperatorPrecedence::LOGICAL_OR,
        SyntaxKind::AmpersandAmpersandToken => return OperatorPrecedence::LOGICAL_AND,
        SyntaxKind::BarToken => return OperatorPrecedence::BITWISE_OR,
        SyntaxKind::CaretToken => return OperatorPrecedence::BITWISE_XOR,
        SyntaxKind::AmpersandToken => return OperatorPrecedence::BITWISE_AND,
        SyntaxKind::EqualsEqualsToken
        | SyntaxKind::ExclamationEqualsToken
        | SyntaxKind::EqualsEqualsEqualsToken
        | SyntaxKind::ExclamationEqualsEqualsToken => return OperatorPrecedence::EQUALITY,
        SyntaxKind::LessThanToken
        | SyntaxKind::GreaterThanToken
        | SyntaxKind::LessThanEqualsToken
        | SyntaxKind::GreaterThanEqualsToken
        | SyntaxKind::InstanceOfKeyword
        | SyntaxKind::InKeyword
        | SyntaxKind::AsKeyword
        | SyntaxKind::SatisfiesKeyword => return OperatorPrecedence::RELATIONAL,
        SyntaxKind::LessThanLessThanToken
        | SyntaxKind::GreaterThanGreaterThanToken
        | SyntaxKind::GreaterThanGreaterThanGreaterThanToken => return OperatorPrecedence::SHIFT,
        SyntaxKind::PlusToken | SyntaxKind::MinusToken => return OperatorPrecedence::ADDITIVE,
        SyntaxKind::AsteriskToken | SyntaxKind::SlashToken | SyntaxKind::PercentToken => {
            return OperatorPrecedence::MULTIPLICATIVE;
        }
        SyntaxKind::AsteriskAsteriskToken => return OperatorPrecedence::EXPONENTIATION,
        _ => {}
    }
    // -1 is lower than all other precedences.  Returning it will cause binary expression
    // parsing to stop.
    OperatorPrecedence::INVALID
}

// Go: ast/precedence.go:370 GetLeftmostExpression
// Gets the leftmost expression of an expression, e.g. `a` in `a.b`, `a[b]`, `a++`, `a+b`, `a?b:c`, `a as B`, etc.
#[must_use]
pub fn get_leftmost_expression(mut node: Node, stop_at_call_expressions: bool) -> Node {
    loop {
        match node.kind() {
            SyntaxKind::PostfixUnaryExpression => {
                node = node.operand();
                continue;
            }
            SyntaxKind::BinaryExpression => {
                node = node.left();
                continue;
            }
            SyntaxKind::ConditionalExpression => {
                node = node.condition();
                continue;
            }
            SyntaxKind::TaggedTemplateExpression => {
                node = node.tag();
                continue;
            }
            SyntaxKind::CallExpression
            | SyntaxKind::AsExpression
            | SyntaxKind::ElementAccessExpression
            | SyntaxKind::PropertyAccessExpression
            | SyntaxKind::NonNullExpression
            | SyntaxKind::PartiallyEmittedExpression
            | SyntaxKind::SatisfiesExpression => {
                // Go: `case KindCallExpression: if stopAtCallExpressions { return node }; fallthrough`
                if node.kind() == SyntaxKind::CallExpression && stop_at_call_expressions {
                    return node;
                }
                node = node.expression();
                continue;
            }
            _ => {}
        }
        return node;
    }
}

// Go: ast/precedence.go:655 GetTypeNodePrecedence
// Gets the precedence of a TypeNode
#[must_use]
pub fn get_type_node_precedence(n: Node) -> TypePrecedence {
    match n.kind() {
        SyntaxKind::ConditionalType => TypePrecedence::CONDITIONAL,
        SyntaxKind::JsDocOptionalType | SyntaxKind::JsDocVariadicType => TypePrecedence::JS_DOC,
        SyntaxKind::FunctionType | SyntaxKind::ConstructorType => TypePrecedence::FUNCTION,
        SyntaxKind::UnionType => TypePrecedence::UNION,
        SyntaxKind::IntersectionType => TypePrecedence::INTERSECTION,
        SyntaxKind::TypeOperator => TypePrecedence::TYPE_OPERATOR,
        SyntaxKind::InferType => {
            if n.type_parameter().constraint().is_some() {
                // `infer T extends U` must be treated as FunctionTypeNode precedence as the `extends` clause eagerly consumes
                // TypeNode
                return TypePrecedence::FUNCTION;
            }
            TypePrecedence::TYPE_OPERATOR
        }
        SyntaxKind::IndexedAccessType | SyntaxKind::ArrayType | SyntaxKind::OptionalType => TypePrecedence::POSTFIX,
        SyntaxKind::TypeQuery => {
            // TypeQueryNode is actually a NonArrayType, but we treat it as TypeOperatorNode
            // precedence so that it is parenthesized when used in a PostfixType
            // context (e.g., `(typeof C)[]` instead of `typeof C[]`)
            TypePrecedence::TYPE_OPERATOR
        }
        SyntaxKind::AnyKeyword
        | SyntaxKind::UnknownKeyword
        | SyntaxKind::StringKeyword
        | SyntaxKind::NumberKeyword
        | SyntaxKind::BigIntKeyword
        | SyntaxKind::SymbolKeyword
        | SyntaxKind::BooleanKeyword
        | SyntaxKind::UndefinedKeyword
        | SyntaxKind::NeverKeyword
        | SyntaxKind::ObjectKeyword
        | SyntaxKind::IntrinsicKeyword
        | SyntaxKind::VoidKeyword
        | SyntaxKind::JsDocAllType
        | SyntaxKind::JsDocNullableType
        | SyntaxKind::JsDocNonNullableType
        | SyntaxKind::LiteralType
        | SyntaxKind::TypePredicate
        | SyntaxKind::TypeReference
        | SyntaxKind::TypeLiteral
        | SyntaxKind::TupleType
        | SyntaxKind::RestType
        | SyntaxKind::ParenthesizedType
        | SyntaxKind::ThisType
        | SyntaxKind::MappedType
        | SyntaxKind::NamedTupleMember
        | SyntaxKind::TemplateLiteralType
        | SyntaxKind::ImportType
        // These occur in pseudo-types like `f<T>.C`, where `f` is a generic function and `C` is a local type
        | SyntaxKind::PropertyAccessExpression
        | SyntaxKind::ExpressionWithTypeArguments => TypePrecedence::NON_ARRAY,
        kind => panic!("unhandled TypeNode: {kind:?}"),
    }
}

// ---------------------------------------------------------------------------
// modifierflags.go, checkflags.go, symbolflags.go: consts only (in
// `crate::flags`).
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// flow.go (FlowFlags consts are in `crate::flags`; `FlowNode` is in
// `crate::core`, with `antecedents: Vec<FlowNodeId>` in place of Go `FlowList`)
// ---------------------------------------------------------------------------

/// Go `ast.FlowSwitchClauseData` (synthetic AST node for
/// `FlowFlags::SWITCH_CLAUSE`).
/// PORT: Go wraps this in a synthetic `*Node` of `KindUnknown` stored in
/// `FlowNode.Node`. `core::FlowNode.node` is a handle into parsed files and
/// cannot hold a synthetic node, so this is a plain value. The owner of the
/// flow node storage decides where it lives.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct FlowSwitchClauseData {
    pub switch_statement: Node,
    pub clause_start: i32, // Start index of case/default clause range
    pub clause_end: i32,   // End index of case/default clause range
}

// Go: ast/flow.go:52 NewFlowSwitchClauseData
// PORT: returns the data value instead of a synthetic `*Node` (see the struct).
#[must_use]
pub fn new_flow_switch_clause_data(
    switch_statement: Node,
    clause_start: i32,
    clause_end: i32,
) -> FlowSwitchClauseData {
    FlowSwitchClauseData {
        switch_statement,
        clause_start,
        clause_end,
    }
}

impl FlowSwitchClauseData {
    // Go: ast/flow.go:60 IsEmpty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.clause_start == self.clause_end
    }
}

/// Go `ast.FlowReduceLabelData` (synthetic AST node for
/// `FlowFlags::REDUCE_LABEL`).
/// PORT: plain value, like `FlowSwitchClauseData`. Go `*FlowList` becomes
/// `Vec<FlowNodeId>` in the same order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FlowReduceLabelData {
    pub target: FlowNodeId,           // Target label
    pub antecedents: Vec<FlowNodeId>, // Temporary antecedent list
}

// Go: ast/flow.go:72 NewFlowReduceLabelData
// PORT: returns the data value instead of a synthetic `*Node` (see the struct).
#[must_use]
pub fn new_flow_reduce_label_data(
    target: FlowNodeId,
    antecedents: Vec<FlowNodeId>,
) -> FlowReduceLabelData {
    FlowReduceLabelData {
        target,
        antecedents,
    }
}

// ---------------------------------------------------------------------------
// functionflags.go (FunctionFlags consts are in `crate::flags`)
// ---------------------------------------------------------------------------

// Go: ast/functionflags.go:13 GetFunctionFlags
#[must_use]
pub fn get_function_flags(node: Node) -> FunctionFlags {
    if node.is_nil() {
        return FunctionFlags::INVALID;
    }
    // PORT: Go `node.BodyData()` is non-nil exactly for the kinds that embed
    // `BodyBase` (FunctionDeclaration, MethodDeclaration, Constructor,
    // Get/SetAccessor, FunctionExpression, ArrowFunction, ModuleDeclaration).
    // `data.AsteriskToken` / `data.Body` are read with the field accessors.
    let has_body_data = matches!(
        node.kind(),
        SyntaxKind::FunctionDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::Constructor
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::FunctionExpression
            | SyntaxKind::ArrowFunction
            | SyntaxKind::ModuleDeclaration
    );
    if !has_body_data {
        return FunctionFlags::INVALID;
    }
    let mut flags = FunctionFlags::NORMAL;
    match node.kind() {
        SyntaxKind::FunctionDeclaration
        | SyntaxKind::FunctionExpression
        | SyntaxKind::MethodDeclaration
        | SyntaxKind::ArrowFunction => {
            // Go: generator check, then `fallthrough` to the ArrowFunction case.
            if node.kind() != SyntaxKind::ArrowFunction && node.asterisk_token().is_some() {
                flags |= FunctionFlags::GENERATOR;
            }
            if has_syntactic_modifier(node, ModifierFlags::ASYNC) {
                flags |= FunctionFlags::ASYNC;
            }
        }
        _ => {}
    }
    if node.body().is_nil() {
        flags |= FunctionFlags::INVALID;
    }
    flags
}

// ---------------------------------------------------------------------------
// positionmap.go
// ---------------------------------------------------------------------------

/// Go `ast.PositionMap`: bidirectional mapping between UTF-8 byte offsets
/// (used by Go) and UTF-16 code unit offsets (used by JavaScript/TypeScript).
///
/// For ASCII-only text, the two are identical. For text containing non-ASCII
/// characters, the offsets diverge because multi-byte UTF-8 sequences map to
/// different numbers of UTF-16 code units:
///   - U+0000..U+007F:   1 byte  in UTF-8, 1 code unit  in UTF-16
///   - U+0080..U+07FF:   2 bytes in UTF-8, 1 code unit  in UTF-16
///   - U+0800..U+FFFF:   3 bytes in UTF-8, 1 code unit  in UTF-16
///   - U+10000..U+10FFFF: 4 bytes in UTF-8, 2 code units in UTF-16 (surrogate pair)
#[derive(Clone, Debug, Default)]
pub struct PositionMap {
    /// True if the text contains only ASCII characters, meaning UTF-8 byte
    /// offsets and UTF-16 code unit offsets are identical.
    pub ascii_only: bool,
    /// For each multi-byte character: the UTF-8 byte offset after it and the
    /// cumulative delta (utf8Offset - utf16Offset) through it. This allows
    /// O(log n) conversion in either direction.
    pub entries: Vec<PositionMapEntry>,
}

/// Go `ast.positionMapEntry`.
#[derive(Clone, Copy, Debug, Default)]
pub struct PositionMapEntry {
    pub utf8_pos: i32, // UTF-8 byte offset AFTER this multi-byte character
    pub delta: i32,    // cumulative (utf8 - utf16) offset difference after this character
}

// Go: ast/positionmap.go:37 ComputePositionMap
// ComputePositionMap builds a PositionMap for the given text.
// PORT: Go decodes invalid UTF-8 as one-byte runes; a Rust `&str` is always
// valid UTF-8, so iterating chars is equivalent.
#[must_use]
pub fn compute_position_map(text: &str) -> PositionMap {
    let mut pm = PositionMap::default();
    let mut delta: i32 = 0;
    for (i, r) in text.char_indices() {
        let size = r.len_utf8() as i32;
        if size == 1 {
            continue;
        }
        let utf16_size: i32 = if (r as u32) >= 0x10000 { 2 } else { 1 };
        delta += size - utf16_size;
        pm.entries.push(PositionMapEntry {
            utf8_pos: i as i32 + size,
            delta,
        });
    }
    pm.ascii_only = pm.entries.is_empty();
    pm
}

impl PositionMap {
    // Go: ast/positionmap.go:61 IsAsciiOnly
    // IsAsciiOnly returns true if the text is ASCII-only,
    // meaning UTF-8 and UTF-16 offsets are identical.
    #[must_use]
    pub fn is_ascii_only(&self) -> bool {
        self.ascii_only
    }

    // Go: ast/positionmap.go:66 UTF8ToUTF16
    // UTF8ToUTF16 converts a UTF-8 byte offset to a UTF-16 code unit offset.
    #[must_use]
    pub fn utf8_to_utf16(&self, utf8_offset: i32) -> i32 {
        if self.ascii_only {
            return utf8_offset;
        }
        // Binary search: find the last entry where utf8Pos <= utf8Offset
        let (mut lo, mut hi) = (0usize, self.entries.len());
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if self.entries[mid].utf8_pos <= utf8_offset {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        if lo == 0 {
            // Before any multi-byte character
            return utf8_offset;
        }
        utf8_offset - self.entries[lo - 1].delta
    }

    // Go: ast/positionmap.go:88 UTF16ToUTF8
    // UTF16ToUTF8 converts a UTF-16 code unit offset to a UTF-8 byte offset.
    #[must_use]
    pub fn utf16_to_utf8(&self, utf16_offset: i32) -> i32 {
        if self.ascii_only {
            return utf16_offset;
        }
        // We need the last entry where (utf8Pos - delta) <= utf16Offset.
        // (utf8Pos - delta) is the UTF-16 offset of that entry's character.
        let (mut lo, mut hi) = (0usize, self.entries.len());
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let utf16_pos = self.entries[mid].utf8_pos - self.entries[mid].delta;
            if utf16_pos <= utf16_offset {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        if lo == 0 {
            return utf16_offset;
        }
        utf16_offset + self.entries[lo - 1].delta
    }
}

// ---------------------------------------------------------------------------
// ids.go
// ---------------------------------------------------------------------------

// PORT: Go `ast.NodeId` and `ast.SymbolId` are plain `uint64` ids. The port
// uses the `core::Node` and `core::SymbolId` handles instead, so there is
// nothing to define here.
