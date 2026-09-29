//! Go `internal/project/parsecache.go`.

use crate::project::prelude::*;

use crate::contentmapper;
use crate::frontend::core_ext::ensure_script_kind_from_file_name;
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
    mut script_kind: ScriptKind,
) -> ParseCacheKey {
    if script_kind == ScriptKind::UNKNOWN {
        script_kind = ensure_script_kind_from_file_name(&options.file_name);
    }
    ParseCacheKey {
        file_name: options.file_name.clone(),
        path: options.path.clone(),
        jsx: options.external_module_indicator_options.jsx,
        force: options.external_module_indicator_options.force,
        hash,
        script_kind,
    }
}

// Go: project/parsecache.go:36 ContentMappedParseCacheKey (tsgo#4712)
// ContentMappedParseCacheKey identifies the complete output bundle for one mapped input. Hash folds the
// original content, mapper transform identity, and diagnostic locale together.
// PORT: the embedded `ast.SourceFileParseOptions` is copied field by field,
// as in `ParseCacheKey`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ContentMappedParseCacheKey {
    pub file_name: String,
    pub path: tspath::Path,
    pub jsx: bool,
    pub force: bool,
    pub hash: u128,
}

impl ContentMappedParseCacheKey {
    /// Go `ContentMappedParseCacheKey{SourceFileParseOptions: options, Hash: hash}`.
    pub fn new(options: &parser::SourceFileParseOptions, hash: u128) -> ContentMappedParseCacheKey {
        ContentMappedParseCacheKey {
            file_name: options.file_name.clone(),
            path: options.path.clone(),
            jsx: options.external_module_indicator_options.jsx,
            force: options.external_module_indicator_options.force,
            hash,
        }
    }

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

// Go: project/parsecache.go:43 contentMappedParseCacheKey (tsgo#4712)
// PORT: Go `xxh3.Uint128` `Hi` is the high 64 bits of the `u128`, `Lo` the
// low 64 bits.
pub fn content_mapped_parse_cache_key(
    options: &parser::SourceFileParseOptions,
    raw_hash: u128,
    transform_identity: u128,
    diagnostic_locale: &locale::Locale,
) -> ContentMappedParseCacheKey {
    let diagnostic_locale = diagnostic_locale.string();
    let mut buf = Vec::with_capacity(32 + diagnostic_locale.len());
    buf.extend_from_slice(&((raw_hash >> 64) as u64).to_le_bytes());
    buf.extend_from_slice(&(raw_hash as u64).to_le_bytes());
    buf.extend_from_slice(&((transform_identity >> 64) as u64).to_le_bytes());
    buf.extend_from_slice(&(transform_identity as u64).to_le_bytes());
    buf.extend_from_slice(diagnostic_locale.as_bytes());
    ContentMappedParseCacheKey::new(options, xxh3_128(&buf))
}

// Go: project/parsecache.go:54 parseCacheKeyForFile (tsgo#4712)
// parseCacheKeyForFile reconstructs the ordinary parse-cache key for a source file held by a program.
pub fn parse_cache_key_for_file(file: &parser::ParsedSourceFile) -> ParseCacheKey {
    program_file_key(file.parse_options(), file.text, file.script_kind)
}

// Go: project/parsecache.go:58 contentMappedParseCacheKeyForFile (tsgo#4712)
pub fn content_mapped_parse_cache_key_for_file(
    file: &parser::ParsedSourceFile,
) -> ContentMappedParseCacheKey {
    ContentMappedParseCacheKey::new(
        file.content_mapper_parse_options(),
        source_file_hash(file.text),
    )
}

// Go: project/parsecache.go:63 parseCacheKeyForDuplicate (tsgo#4712)
// parseCacheKeyForDuplicate reconstructs an ordinary parse-cache key for a deduplicated source file.
pub fn parse_cache_key_for_duplicate(file: &compiler::DuplicateSourceFile) -> ParseCacheKey {
    program_file_key(&file.parse_options, file.text, file.script_kind)
}

// Go: project/parsecache.go:67 contentMappedParseCacheKeyForDuplicate (tsgo#4712)
pub fn content_mapped_parse_cache_key_for_duplicate(
    file: &compiler::DuplicateSourceFile,
) -> ContentMappedParseCacheKey {
    ContentMappedParseCacheKey::new(
        &file.content_mapper_parse_options,
        source_file_hash(file.text),
    )
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
            // Program versions share the parse, so its nodes belong to the thread.
            let _base = crate::ast::enter_base_synthetic_owner();
            // Not in Go: a new version of a published path can be freed
            // (lsshells M3a). Its parse keeps its nodes in its store, not in
            // the leaked AST arena, so they are freed with it (M3c). A
            // prefetched parse keeps its leaked nodes.
            let freeable = crate::ast::freeable_path(&key.path.0);
            let _owned_nodes = freeable.then(crate::ast::enter_freeable_parse);
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
            // Not in Go: a new version of a published path can be freed. The
            // holders of the parse (programs, cache entries) keep it alive
            // (lsshells M3a, `ast/file_version.rs`).
            if freeable {
                assert!(
                    file.version
                        .set(crate::ast::FileVersion::new(file.store))
                        .is_ok()
                );
            }
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

// Go: project/parsecache.go:84 ContentMappedParseCache (tsgo#4712)
// PORT: Go embeds `*RefCountCache`; the type alias gives the same methods.
// One reference owns the canonical file and all supplemental files as a
// bundle (`contentmapper::SourceFiles`). Callers ref and deref the
// canonical file only.
pub type ContentMappedParseCache =
    RefCountCache<ContentMappedParseCacheKey, contentmapper::SourceFiles, ()>;

// Go: project/parsecache.go:90 NewContentMappedParseCache (tsgo#4712)
pub fn new_content_mapped_parse_cache(
    options: RefCountCacheOptions,
) -> Rc<ContentMappedParseCache> {
    new_ref_count_cache(
        options,
        |_: &ContentMappedParseCacheKey, (): ()| -> contentmapper::SourceFiles {
            panic!("content-mapped source files must be produced with AcquireOrError")
        },
    )
}

/// Go `file.Hash = hash` for a file that the content-mapped parse cache
/// holds (project/compilerhost.go GetContentMappedSourceFiles).
// PORT: see `TEXT_HASHES`. A content-mapped file's Go `Hash` is the hash of
// its cache key, not of its text.
pub fn set_source_file_hash(file: &parser::ParsedSourceFile, hash: u128) {
    TEXT_HASHES.with_borrow_mut(|hashes| {
        hashes.insert(text_id(file.text), hash);
    });
}

/// Go `file.Hash` of a file that the parse cache or the content-mapped
/// parse cache made on this thread. For any other text it is the xxh3-128
/// of the text (Go `fh.Hash()`).
// PORT: for the api encoder (Go `Hash` of a content-mapped file is its key
// hash) and the key helpers above.
pub fn source_file_hash(text: &'static str) -> u128 {
    TEXT_HASHES
        .with_borrow(|hashes| hashes.get(&text_id(text)).copied())
        .unwrap_or_else(|| xxh3_128(text.as_bytes()))
}

/// Go `contentMappedParseCache.Deref(key)` for a program file or a
/// duplicate source file. When the bundle entry is gone, the hashes of its
/// files are forgotten too.
// PORT: see `deref_program_file`.
pub fn deref_content_mapped_file(
    cache: &ContentMappedParseCache,
    key: &ContentMappedParseCacheKey,
) {
    let bundle = cache
        .entries
        .borrow()
        .get(key)
        .and_then(|entry| entry.value.borrow().clone());
    // PORT: called by path so `std::ops::Deref::deref` can not win.
    ContentMappedParseCache::deref(cache, key);
    if !cache.has(key)
        && let Some(bundle) = bundle
    {
        TEXT_HASHES.with_borrow_mut(|hashes| {
            if let Some(canonical) = &bundle.canonical {
                hashes.remove(&text_id(canonical.text));
            }
            for supplemental in &bundle.supplemental {
                hashes.remove(&text_id(supplemental.text));
            }
        });
    }
}

thread_local! {
    /// Go `file.Hash` of each text that the parse cache parsed on this
    /// thread, by `text_id`. It also holds the Go `Hash` of the files of the
    /// content-mapped parse cache (`set_source_file_hash`).
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
    new_parse_cache_key(options, source_file_hash(text), script_kind)
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
