//! Go `internal/project/parsecache.go`.

use crate::project::prelude::*;

use crate::frontend::parser;

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
            // PORT: the parser takes `&'static str` (node data points into the
            // text), so the text is leaked, as in compiler/host.rs.
            let text: &'static str = Box::leak(fh.content().into_boxed_str());
            let file = Rc::new(parser::parse_source_file(
                &key.source_file_parse_options(),
                text,
                key.script_kind,
            ));
            // PORT: the next program version publishes the file's store. A
            // version that does not include the file (a package duplicate, an
            // auto-import entrypoint) must still publish its parser fields,
            // so a later version can share the file.
            crate::program::note_parsed_source_file(&file);
            // Go: file.Hash = fh.Hash()
            HashedSourceFile {
                file,
                hash: fh.hash(),
            }
        },
    )
}
