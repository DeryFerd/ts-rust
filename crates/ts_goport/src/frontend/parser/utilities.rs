//! Port of typescript-go `internal/parser/utilities.go`,
//! `internal/parser/types.go` and `internal/ast/parseoptions.go`.
//!
//! PORT: Go `parser.ParseFlags` (types.go) is already ported as
//! `crate::flags::ParseFlags` with the Go values, so types.go adds nothing
//! here.
//!
//! PORT: parseoptions.go is in package `ast`. The plan gives it to this unit
//! without a file, so it is here, next to the parser code that uses it.

use crate::frontend::prelude::*;

// ── parser/utilities.go ────────────────────────────────────────────────

// Go: parser/utilities.go:11 getLanguageVariant
pub fn get_language_variant(script_kind: ScriptKind) -> LanguageVariant {
    match script_kind {
        // .tsx and .jsx files are treated as jsx language variant.
        ScriptKind::TSX | ScriptKind::JSX | ScriptKind::JS | ScriptKind::JSON => {
            LanguageVariant::JSX
        }
        _ => LanguageVariant::STANDARD,
    }
}

// Go: parser/utilities.go:20 tokenIsIdentifierOrKeyword
// Go: parser/utilities.go:24 tokenIsIdentifierOrKeywordOrGreaterThan
// PORT: the same two functions from Go checker/utilities.go are already
// public in `checker/utilities_p1.rs` (`token_is_identifier_or_keyword`,
// `token_is_identifier_or_keyword_or_greater_than`) with the same bodies. A
// second public copy would make the prelude glob ambiguous, so the parser
// uses those.

// Go: parser/utilities.go:28 GetJSDocCommentRanges
// PORT: Go appends to the `commentRanges` slice and filters it in place
// (`slices.DeleteFunc`). Here the vector is taken by value and returned.
pub fn get_js_doc_comment_ranges(
    f: &NodeFactory,
    mut comment_ranges: Vec<CommentRange>,
    node: Node,
    text: &str,
) -> Vec<CommentRange> {
    match node.kind() {
        SyntaxKind::Parameter
        | SyntaxKind::TypeParameter
        | SyntaxKind::FunctionExpression
        | SyntaxKind::ArrowFunction
        | SyntaxKind::ParenthesizedExpression
        | SyntaxKind::VariableDeclaration
        | SyntaxKind::ExportSpecifier => {
            comment_ranges.extend(get_trailing_comment_ranges(f, text, node.pos()));
            comment_ranges.extend(get_leading_comment_ranges(f, text, node.pos()));
        }
        _ => {
            comment_ranges.extend(get_leading_comment_ranges(f, text, node.pos()));
        }
    }
    // Keep if the comment starts with '/**' but not if it is '/**/'
    let bytes = text.as_bytes();
    comment_ranges.retain(|comment| {
        let comment_start = comment.pos();
        let comment_len = comment.end() - comment_start;
        !(comment.end() > node.end()
            || comment_len < 4
            || bytes[(comment_start + 1) as usize] != b'*'
            || bytes[(comment_start + 2) as usize] != b'*'
            || bytes[(comment_start + 3) as usize] == b'/')
    });
    comment_ranges
}

// Go: parser/utilities.go:50 isKeywordOrPunctuation
pub fn is_keyword_or_punctuation(token: SyntaxKind) -> bool {
    is_keyword_kind(token) || is_punctuation_kind(token)
}

// Go: parser/utilities.go:54 isJSDocLikeText
// PORT: `pub(super)`, because `printer/utilities.rs` has a crate-visible
// `is_js_doc_like_text` (the Go printer function of the same name, with other
// parameters). Parser files call this one as `super::utilities::is_js_doc_like_text`.
pub(super) fn is_js_doc_like_text(text: &str) -> bool {
    let bytes = text.as_bytes();
    bytes.len() >= 4 && bytes[1] == b'*' && bytes[2] == b'*' && bytes[3] != b'/'
}

// ── ast/parseoptions.go ────────────────────────────────────────────────

/// Go `ast.SourceFileParseOptions`.
// Go: ast/parseoptions.go:8 SourceFileParseOptions
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SourceFileParseOptions {
    pub file_name: String,
    pub path: Path,
    pub external_module_indicator_options: ExternalModuleIndicatorOptions,
}

/// Go `ast.ExternalModuleIndicatorOptions`.
// Go: ast/parseoptions.go:14 ExternalModuleIndicatorOptions
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ExternalModuleIndicatorOptions {
    pub jsx: bool,
    pub force: bool,
}

// Go: ast/parseoptions.go:19 GetExternalModuleIndicatorOptions
pub fn get_external_module_indicator_options(
    file_name: &str,
    options: &CompilerOptions,
    metadata: &SourceFileMetaData,
) -> ExternalModuleIndicatorOptions {
    if is_declaration_file_name(file_name) {
        return ExternalModuleIndicatorOptions::default();
    }

    match options.get_emit_module_detection_kind() {
        // All non-declaration files are modules, declaration files still do the usual isFileProbablyExternalModule
        ModuleDetectionKind::FORCE => ExternalModuleIndicatorOptions {
            jsx: false,
            force: true,
        },
        // Files are modules if they have imports, exports, or import.meta
        ModuleDetectionKind::LEGACY => ExternalModuleIndicatorOptions::default(),
        // If module is nodenext or node16, all esm format files are modules
        // If jsx is react-jsx or react-jsxdev then jsx tags force module-ness
        // otherwise, the presence of import or export statments (or import.meta) implies module-ness
        ModuleDetectionKind::AUTO => ExternalModuleIndicatorOptions {
            jsx: options.jsx == JsxEmit::REACT_JSX || options.jsx == JsxEmit::REACT_JSX_DEV,
            force: is_file_forced_to_be_module_by_format(file_name, options, metadata),
        },
        _ => ExternalModuleIndicatorOptions::default(),
    }
}

// Go: ast/parseoptions.go:44 isFileForcedToBeModuleByFormatExtensions
const IS_FILE_FORCED_TO_BE_MODULE_BY_FORMAT_EXTENSIONS: [&str; 4] =
    [EXTENSION_CJS, EXTENSION_CTS, EXTENSION_MJS, EXTENSION_MTS];

// Go: ast/parseoptions.go:46 isFileForcedToBeModuleByFormat
fn is_file_forced_to_be_module_by_format(
    file_name: &str,
    options: &CompilerOptions,
    metadata: &SourceFileMetaData,
) -> bool {
    // Excludes declaration files - they still require an explicit `export {}` or the like
    // for back compat purposes. The only non-declaration files _not_ forced to be a module are `.js` files
    // that aren't esm-mode (meaning not in a `type: module` scope).
    get_implied_node_format_for_emit_worker(file_name, options.get_emit_module_kind(), metadata)
        == ModuleKind::ES_NEXT
        || file_extension_is_one_of(file_name, &IS_FILE_FORCED_TO_BE_MODULE_BY_FORMAT_EXTENSIONS)
}

// Go: ast/parseoptions.go:56 SetExternalModuleIndicator
// PORT: Go takes `*ast.SourceFile`. The SourceFile fields live in
// `ParsedSourceFile` (plan contract 6).
pub fn set_external_module_indicator(
    file: &mut ParsedSourceFile,
    opts: ExternalModuleIndicatorOptions,
) {
    file.external_module_indicator = get_external_module_indicator(file, opts);
}

thread_local! {
    /// Set when `get_external_module_indicator` reads its options. A
    /// detached parse reports it (`parse_source_file_detached`).
    static MODULE_INDICATOR_OPTIONS_READ: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(crate) fn reset_module_indicator_options_read() {
    MODULE_INDICATOR_OPTIONS_READ.with(|read| read.set(false));
}

pub(crate) fn module_indicator_options_read() -> bool {
    MODULE_INDICATOR_OPTIONS_READ.with(std::cell::Cell::get)
}

// Go: ast/parseoptions.go:60 getExternalModuleIndicator
fn get_external_module_indicator(
    file: &ParsedSourceFile,
    opts: ExternalModuleIndicatorOptions,
) -> Node {
    if file.script_kind == ScriptKind::JSON {
        return Node::NIL;
    }

    let node = is_file_probably_external_module(file.root);
    if node.is_some() {
        return node;
    }

    if file.is_declaration_file {
        return Node::NIL;
    }

    MODULE_INDICATOR_OPTIONS_READ.with(|read| read.set(true));
    if opts.jsx {
        let node = is_file_module_from_using_jsx_tag(file.root);
        if node.is_some() {
            return node;
        }
    }

    if opts.force {
        return file.root;
    }

    Node::NIL
}

/// PORT: not in Go (perf). `file` as a parse of its text with `opts` gives
/// it, so a watch build can keep a parse after a config change: `file`
/// itself for its own options, a copy with `opts` when the two differ only
/// in module indicator options that its parse did not read, else `None`.
/// Go parses the file again. A parse reads its module indicator options
/// only in `get_external_module_indicator`, and only when the file has no
/// import, export or `import.meta` and is not a declaration or JSON file:
/// the parse worker rule (`read_module_indicator_options`). The copy has
/// the same nodes and the new options, which a later `UpdateProgram` and
/// the watch fast path read (Go `oldFile.ParseOptions()`).
#[must_use]
pub fn parse_with_options(
    file: &Rc<ParsedSourceFile>,
    opts: &SourceFileParseOptions,
) -> Option<Rc<ParsedSourceFile>> {
    let own = file.parse_options();
    if own == opts {
        return Some(file.clone());
    }
    let reads_options = file.script_kind != ScriptKind::JSON
        && is_file_probably_external_module(file.root).is_nil()
        && !file.is_declaration_file;
    if own.file_name != opts.file_name
        || own.path != opts.path
        || reads_options
        || !file.content_mapper().is_empty()
    {
        return None;
    }
    Some(Rc::new(ParsedSourceFile {
        parse_options: opts.clone(),
        ..(**file).clone()
    }))
}

// Go: ast/parseoptions.go:86 isFileProbablyExternalModule
// PORT: takes the SourceFile node.
fn is_file_probably_external_module(source_file: Node) -> Node {
    for statement in source_file.statements().iter() {
        if is_an_external_module_indicator_node(statement) {
            return statement;
        }
    }
    get_import_meta_if_necessary(source_file)
}

// Go: ast/parseoptions.go:95 isAnExternalModuleIndicatorNode
fn is_an_external_module_indicator_node(node: Node) -> bool {
    has_syntactic_modifier(node, ModifierFlags::EXPORT)
        || is_import_equals_declaration(node)
            && is_external_module_reference(node.module_reference())
        || is_import_declaration(node)
        || is_export_assignment(node)
        || is_export_declaration(node)
}

// Go: ast/parseoptions.go:101 getImportMetaIfNecessary
fn get_import_meta_if_necessary(source_file: Node) -> Node {
    if source_file
        .flags()
        .intersects(NodeFlags::POSSIBLY_CONTAINS_IMPORT_META)
    {
        return find_child_node(source_file, is_import_meta);
    }
    Node::NIL
}

// Go: ast/parseoptions.go:108 findChildNode
fn find_child_node(root: Node, check: fn(Node) -> bool) -> Node {
    fn visit(node: Node, check: fn(Node) -> bool, result: &mut Node) -> bool {
        if check(node) {
            *result = node;
            return true;
        }
        node.for_each_child(|child| visit(child, check, result))
    }
    let mut result = Node::NIL;
    visit(root, check, &mut result);
    result
}

// Go: ast/parseoptions.go:122 isFileModuleFromUsingJSXTag
fn is_file_module_from_using_jsx_tag(file: Node) -> Node {
    walk_tree_for_jsx_tags(file)
}

// Go: ast/parseoptions.go:129 walkTreeForJSXTags
// This is a somewhat unavoidable full tree walk to locate a JSX tag - `import.meta` requires the same,
// but we avoid that walk (or parts of it) if at all possible using the `PossiblyContainsImportMeta` node flag.
// Unfortunately, there's no `NodeFlag` space to do the same for JSX.
fn walk_tree_for_jsx_tags(node: Node) -> Node {
    fn visitor(node: Node, found: &mut Node) -> bool {
        if found.is_some() {
            return true;
        }
        if !node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_JSX)
        {
            return false;
        }
        if is_jsx_opening_like_element(node) || is_jsx_fragment(node) {
            *found = node;
            return true;
        }
        node.for_each_child(|child| visitor(child, found))
    }
    let mut found = Node::NIL;
    visitor(node, &mut found);
    found
}
