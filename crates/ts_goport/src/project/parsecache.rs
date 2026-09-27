//! Go `internal/project/parsecache.go`.

use crate::project::prelude::*;

use crate::frontend::parser;
use xxhash_rust::xxh3::xxh3_128;

// Go: project/parsecache.go:10 ParseCacheKey
// PORT: Go embeds `ast.SourceFileParseOptions` (with its
// `ExternalModuleIndicatorOptions`). The parser structs do not derive `Hash`
// and the plan keeps the parser unchanged, so the key copies their fields:
// `file_name`, `path` and the `jsx` and `force` fields of
// `ExternalModuleIndicatorOptions`. `source_file_parse_options` rebuilds the
// Go embedded value. Go `xxh3.Uint128` is `u128`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ParseCacheKey {
    pub file_name: String,
    pub path: tspath::Path,
    pub jsx: bool,
    pub force: bool,
    pub script_kind: ScriptKind,
    pub hash: u128,
}

impl ParseCacheKey {
    /// Go `key.SourceFileParseOptions` (the embedded value).
    pub fn source_file_parse_options(&self) -> parser::SourceFileParseOptions {
        parser::SourceFileParseOptions {
            file_name: self.file_name.clone(),
            path: self.path.clone(),
            external_module_indicator_options: parser::ExternalModuleIndicatorOptions {
                jsx: self.jsx,
                force: self.force,
            },
        }
    }
}

// Go: project/parsecache.go:16 NewParseCacheKey
// PORT: Go passes the options by value; here by reference.
pub fn new_parse_cache_key(
    options: &parser::SourceFileParseOptions,
    hash: u128,
    script_kind: ScriptKind,
) -> ParseCacheKey {
    ParseCacheKey {
        file_name: options.file_name.clone(),
        path: options.path.clone(),
        jsx: options.external_module_indicator_options.jsx,
        force: options.external_module_indicator_options.force,
        hash,
        script_kind,
    }
}

/// The value the parse cache holds: Go `*ast.SourceFile` after
/// `file.Hash = fh.Hash()`.
// PORT: `ParsedSourceFile` has no `Hash` field and the plan does not edit
// it, so the cache entry keeps the hash next to the file. For a file that a
// program returns, Go `file.Hash` is `xxh3_128(file.text)`, the same value.
#[derive(Clone, Debug)]
pub struct HashedSourceFile {
    pub file: Rc<parser::ParsedSourceFile>,
    pub hash: u128,
}

// Go: project/parsecache.go:28 ParseCache
pub type ParseCache = RefCountCache<ParseCacheKey, HashedSourceFile, Rc<dyn FileHandle>>;

// Go: project/parsecache.go:30 NewParseCache
pub fn new_parse_cache(options: RefCountCacheOptions) -> Rc<ParseCache> {
    new_ref_count_cache(
        options,
        |key: &ParseCacheKey, fh: Rc<dyn FileHandle>| -> HashedSourceFile {
            let opts = key.source_file_parse_options();
            let content = fh.content();
            // PORT: during a program load a parse worker (`FilesParser`
            // prefetch) may have read and parsed this text already, as in
            // compiler/host.rs. A worker result is used only for the same
            // text, and its parse only when it equals the parse below.
            let prefetched =
                compiler::take_prefetched(&opts, key.script_kind, Some(content.as_str()));
            let file = match prefetched {
                compiler::Prefetched::Parse(file) => file,
                // The worker text has the same bytes and is already leaked.
                compiler::Prefetched::Text(text) => {
                    parser::parse_source_file(&opts, text, key.script_kind)
                }
                compiler::Prefetched::Nothing => {
                    // PORT: the parser takes `&'static str` (node data points
                    // into the text), so the text is leaked, as in
                    // compiler/host.rs.
                    let text: &'static str = Box::leak(content.into_boxed_str());
                    parser::parse_source_file(&opts, text, key.script_kind)
                }
            };
            let file = Rc::new(file);
            // PORT: the next program version publishes the file's store. A
            // version that does not include the file (a package duplicate, an
            // auto-import entrypoint) must still publish its parser fields,
            // so a later version can share the file.
            crate::program::note_parsed_source_file(&file);
            // Go: file.Hash = fh.Hash()
            let hash = fh.hash();
            TEXT_HASHES.with_borrow_mut(|hashes| {
                hashes.insert(text_id(file.text), hash);
            });
            HashedSourceFile { file, hash }
        },
    )
}

thread_local! {
    /// Go `file.Hash` of each text that the parse cache parsed on this
    /// thread, by `text_id`.
    // PORT: `ParsedSourceFile` has no `Hash` field. This map lets program
    // clones and snapshot disposal find the hash without hashing every file
    // text again. `deref_program_file` removes an entry with its cache
    // entry; other derefs (autoimport.rs) leave a few bytes for each parse.
    static TEXT_HASHES: RefCell<FxHashMap<(usize, usize), u128>> =
        RefCell::new(FxHashMap::default());
}

/// Address and length of a file text. A `&'static str` is never freed, so
/// two texts with the same id have the same bytes and the same hash.
fn text_id(text: &'static str) -> (usize, usize) {
    (text.as_ptr().addr(), text.len())
}

/// Go `NewParseCacheKey(file.ParseOptions(), file.Hash, file.ScriptKind)`.
// PORT: a text the parse cache did not parse on this thread is hashed
// again. It is the same value: Go `file.Hash` is `fh.Hash()`, the xxh3-128
// of the text.
fn program_file_key(
    options: &parser::SourceFileParseOptions,
    text: &'static str,
    script_kind: ScriptKind,
) -> ParseCacheKey {
    let hash = TEXT_HASHES
        .with_borrow(|hashes| hashes.get(&text_id(text)).copied())
        .unwrap_or_else(|| xxh3_128(text.as_bytes()));
    new_parse_cache_key(options, hash, script_kind)
}

/// Go `parseCache.Ref(NewParseCacheKey(file.ParseOptions(), file.Hash,
/// file.ScriptKind))` for a program file or a duplicate source file.
pub fn ref_program_file(
    cache: &ParseCache,
    options: &parser::SourceFileParseOptions,
    text: &'static str,
    script_kind: ScriptKind,
) {
    cache.ref_(&program_file_key(options, text, script_kind));
}

/// Go `parseCache.Deref(NewParseCacheKey(file.ParseOptions(), file.Hash,
/// file.ScriptKind))` for a program file or a duplicate source file.
/// When the entry is gone, its hash is forgotten too.
pub fn deref_program_file(
    cache: &ParseCache,
    options: &parser::SourceFileParseOptions,
    text: &'static str,
    script_kind: ScriptKind,
) {
    let key = program_file_key(options, text, script_kind);
    // PORT: called by path so `std::ops::Deref::deref` can not win.
    ParseCache::deref(cache, &key);
    if !cache.has(&key) {
        TEXT_HASHES.with_borrow_mut(|hashes| {
            hashes.remove(&text_id(text));
        });
    }
}
