//! Port of the parser fields of Go `ast.SourceFile` (`ast/ast.go:2467`).
//!
//! The Go parser returns a `*ast.SourceFile`, which is a node with extra
//! fields. Here the node lives in the node store of the file (`root`), and
//! the extra fields live in `ParsedSourceFile`. The parser (parser.go),
//! references.go and parseoptions.go set them.

use crate::frontend::prelude::*;

/// The Go `ast.SourceFile` fields that the parser sets.
// PORT: Go keeps these fields on the `SourceFile` node data. astdata cannot
// hold them, so the parser returns them next to the root node. The binder,
// ECMA line map and language service fields of Go `SourceFile` are not here:
// the parser does not set them. The Go mutexes are not needed (one thread).
// Go setters (`SetDiagnostics`, `SetJSDocCache`, ...) are field writes.
#[derive(Clone, Debug)]
pub struct ParsedSourceFile {
    /// Node store id of the file (`new_file_store`).
    pub store: usize,
    /// The `SourceFile` node.
    pub root: Node,

    // Fields set by NewSourceFile
    pub parse_options: SourceFileParseOptions,
    pub text: &'static str,
    pub end_of_file_token: Node,

    // Fields set by parser
    pub diagnostics: Vec<Diagnostic>,
    pub js_diagnostics: Vec<Diagnostic>,
    pub jsdoc_diagnostics: Vec<Diagnostic>,
    pub language_variant: LanguageVariant,
    pub script_kind: ScriptKind,
    pub is_declaration_file: bool,
    pub contains_non_ascii: bool,
    pub uses_uri_style_node_core_modules: Tristate,
    pub identifier_count: i32,
    pub imports: Vec<Node>,
    pub module_augmentations: Vec<Node>,
    pub ambient_module_names: Vec<String>,
    pub comment_directives: Vec<CommentDirective>,
    pub jsdoc_cache: FxHashMap<Node, Vec<Node>>,
    pub has_lazy_js_doc: bool,
    pub reparsed_clones: Vec<Node>,
    pub pragmas: Vec<Pragma>,
    pub referenced_files: Vec<FileReference>,
    pub type_reference_directives: Vec<FileReference>,
    pub lib_reference_directives: Vec<FileReference>,
    pub check_js_directive: Option<CheckJsDirective>,
    pub node_count: usize,
    pub text_count: usize,
    pub common_js_module_indicator: Node,
    /// If this is the SourceFile itself, then this module was "forced"
    /// to be an external module (previously "true").
    pub external_module_indicator: Node,
}

impl ParsedSourceFile {
    /// The fields that Go `NewSourceFile` sets. `root` is the node that
    /// `NodeFactory::new_source_file` made in store `store`.
    // PORT: Go `NewSourceFile` makes the node and these fields in one call.
    #[must_use]
    pub fn new(
        store: usize,
        root: Node,
        parse_options: SourceFileParseOptions,
        text: &'static str,
        end_of_file_token: Node,
    ) -> Self {
        Self {
            store,
            root,
            parse_options,
            text,
            end_of_file_token,
            diagnostics: Vec::new(),
            js_diagnostics: Vec::new(),
            jsdoc_diagnostics: Vec::new(),
            language_variant: LanguageVariant::default(),
            script_kind: ScriptKind::default(),
            is_declaration_file: false,
            // Go: NewSourceFile sets `ContainsNonASCII` from the text
            // (`stringutil.ContainsNonASCII`: a byte >= 0x80). A Go byte
            // >= 0x80 is not ASCII in the port form either.
            contains_non_ascii: !text.is_ascii(),
            uses_uri_style_node_core_modules: Tristate::Unknown,
            identifier_count: 0,
            imports: Vec::new(),
            module_augmentations: Vec::new(),
            ambient_module_names: Vec::new(),
            comment_directives: Vec::new(),
            jsdoc_cache: FxHashMap::default(),
            has_lazy_js_doc: false,
            reparsed_clones: Vec::new(),
            pragmas: Vec::new(),
            referenced_files: Vec::new(),
            type_reference_directives: Vec::new(),
            lib_reference_directives: Vec::new(),
            check_js_directive: None,
            node_count: 0,
            text_count: 0,
            common_js_module_indicator: Node::NIL,
            external_module_indicator: Node::NIL,
        }
    }

    /// Moves the node handles of a detached parse to the real store id
    /// (`adopt_detached_parse`).
    pub fn remap_store(&mut self, remap: StoreRemap) {
        let node = |n: &mut Node| *n = remap.node(*n);
        self.store = remap.store();
        node(&mut self.root);
        node(&mut self.end_of_file_token);
        node(&mut self.common_js_module_indicator);
        node(&mut self.external_module_indicator);
        self.imports.iter_mut().for_each(node);
        self.module_augmentations.iter_mut().for_each(node);
        self.reparsed_clones.iter_mut().for_each(node);
        for diagnostics in [
            &mut self.diagnostics,
            &mut self.js_diagnostics,
            &mut self.jsdoc_diagnostics,
        ] {
            for d in diagnostics {
                remap_diagnostic(d, remap);
            }
        }
        self.jsdoc_cache = std::mem::take(&mut self.jsdoc_cache)
            .into_iter()
            .map(|(key, mut jsdocs)| {
                jsdocs.iter_mut().for_each(node);
                (remap.node(key), jsdocs)
            })
            .collect();
    }

    // Go: ast/ast.go:2562 ParseOptions
    #[must_use]
    pub fn parse_options(&self) -> &SourceFileParseOptions {
        &self.parse_options
    }

    // Go: ast/ast.go:2566 Text
    #[must_use]
    pub fn text(&self) -> &'static str {
        self.text
    }

    // Go: ast/ast.go:2570 FileName
    #[must_use]
    pub fn file_name(&self) -> &str {
        &self.parse_options.file_name
    }

    // Go: ast/ast.go:2574 Path
    #[must_use]
    pub fn path(&self) -> &Path {
        &self.parse_options.path
    }

    /// Go `node.Statements`.
    #[must_use]
    pub fn statements(&self) -> NodeList {
        self.root.statement_list()
    }

    // Go: ast/ast.go:2657 IsJS
    #[must_use]
    pub fn is_js(&self) -> bool {
        // Go: IsSourceFileJS
        self.root.flags().intersects(NodeFlags::JAVA_SCRIPT_FILE)
    }
}

fn remap_diagnostic(d: &mut Diagnostic, remap: StoreRemap) {
    d.file = remap.node(d.file);
    for d in d
        .message_chain
        .iter_mut()
        .chain(d.related_information.iter_mut())
    {
        remap_diagnostic(d, remap);
    }
}

// PORT: Go `(*SourceFile).Diagnostics()` and `SetDiagnostics` read the
// node itself. Code that only holds the `SourceFile` node of a parsed store
// file (the tsconfig parser) reads the diagnostics from this table, keyed by
// store id. `parse_source_file` fills it.
thread_local! {
    static PARSED_FILE_DIAGNOSTICS: RefCell<FxHashMap<usize, &'static [Diagnostic]>> =
        RefCell::new(FxHashMap::default());
}

// Go: ast.go (*SourceFile).SetDiagnostics
pub fn set_source_file_diagnostics(file: Node, diagnostics: Vec<Diagnostic>) {
    let diagnostics: &'static [Diagnostic] = Box::leak(diagnostics.into_boxed_slice());
    PARSED_FILE_DIAGNOSTICS.with(|m| m.borrow_mut().insert(file.file_index(), diagnostics));
}

// Go: ast.go (*SourceFile).Diagnostics, for a parsed store file.
#[must_use]
pub fn parsed_source_file_diagnostics(file: Node) -> &'static [Diagnostic] {
    PARSED_FILE_DIAGNOSTICS.with(|m| m.borrow().get(&file.file_index()).copied().unwrap_or(&[]))
}
