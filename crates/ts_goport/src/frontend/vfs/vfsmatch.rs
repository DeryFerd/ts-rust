use crate::frontend::prelude::*;

// This file ports vfs/vfsmatch/vfsmatch.go and stringer_generated.go.
// It implements the glob matching algorithm specified in MATCHING_ALGORITHM.md.
// PORT: Go slices strings at byte offsets that can be inside a UTF-8
// sequence. Rust `str` cannot be sliced there, so the matcher compares byte
// slices and decodes runes like Go `utf8.DecodeRuneInString` (see
// `decode_rune`).

// Go: vfs/vfsmatch/vfsmatch.go:20 Usage
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Usage {
    Files,
    Directories,
    Exclude,
}

// Go: vfs/vfsmatch/stringer_generated.go:19 Usage.String
// PORT: a Rust enum has no out-of-range values, so the `Usage(%d)` branch
// is not needed.
impl std::fmt::Display for Usage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            Usage::Files => "Files",
            Usage::Directories => "Directories",
            Usage::Exclude => "Exclude",
        };
        f.write_str(name)
    }
}

// Go: vfs/vfsmatch/vfsmatch.go:29 UnlimitedDepth
// PORT: Go `math.MaxInt`. Go `int` is `i32` in this port.
/// Pass as the depth argument to indicate there is no depth limit.
pub const UNLIMITED_DEPTH: i32 = i32::MAX;

// Go: vfs/vfsmatch/vfsmatch.go:31 ReadDirectory
pub fn read_directory(
    host: &dyn Fs,
    current_dir: &str,
    path: &str,
    extensions: &[String],
    excludes: &[String],
    includes: &[String],
    depth: i32,
) -> Vec<String> {
    match_files(
        path,
        extensions,
        excludes,
        includes,
        host.use_case_sensitive_file_names(),
        current_dir,
        depth,
        host,
    )
}

// Go: vfs/vfsmatch/vfsmatch.go:38 IsImplicitGlob
/// Checks if a path component is implicitly a glob.
/// An "includes" path "foo" is implicitly a glob "foo/**/*" if its last component has no extension,
/// and does not contain any glob characters itself.
pub fn is_implicit_glob(last_path_component: &str) -> bool {
    !last_path_component.contains(['.', '*', '?'])
}

// Go: vfs/vfsmatch/vfsmatch.go:42 wildcardCharCodes
const WILDCARD_CHAR_CODES: [char; 2] = ['*', '?'];

// Go: vfs/vfsmatch/vfsmatch.go:44 getIncludeBasePath
fn get_include_base_path(absolute: &str) -> String {
    let Some(wildcard_offset) = absolute.find(WILDCARD_CHAR_CODES) else {
        // No "*" or "?" in the path
        if !has_extension(absolute) {
            return absolute.to_string();
        } else {
            return remove_trailing_directory_separator(&get_directory_path(absolute)).to_string();
        }
    };
    // PORT: Go `max(LastIndex(...), 0)`; a missing separator gives 0.
    let end = absolute[..wildcard_offset].rfind('/').unwrap_or(0);
    absolute[..end].to_string()
}

// Go: vfs/vfsmatch/vfsmatch.go:58 getBasePaths
/// Computes the unique non-wildcard base paths amongst the provided include patterns.
fn get_base_paths(
    path: &str,
    includes: &[String],
    use_case_sensitive_file_names: bool,
) -> Vec<String> {
    // Storage for our results in the form of literal paths (e.g. the paths as written by the user).
    let mut base_paths = vec![path.to_string()];

    if !includes.is_empty() {
        let compare_paths_options = ComparePathsOptions {
            current_directory: path.to_string(),
            use_case_sensitive_file_names,
        };
        let string_comparer = compare_paths_options.get_comparer();

        // Storage for literal base paths amongst the include patterns.
        let mut include_base_paths: Vec<String> = Vec::new();
        for include in includes {
            // We also need to check the relative paths by converting them to absolute and normalizing
            // in case they escape the base path (e.g "..\somedirectory")
            let absolute = if is_rooted_disk_path(include) {
                include.clone()
            } else {
                normalize_path(&combine_paths(path, &[include.as_str()]))
            };
            // Append the literal and canonical candidate base paths.
            include_base_paths.push(get_include_base_path(&absolute));
        }

        // Sort the offsets array using either the literal or canonical path representations.
        // PORT: Go `slices.SortStableFunc`; Rust `sort_by` is stable.
        include_base_paths.sort_by(|a, b| string_comparer(a, b).cmp(&0));

        // Iterate over each include base path and include unique base paths that are not a
        // subpath of an existing base path
        for include_base_path in include_base_paths {
            if base_paths.iter().all(|basepath| {
                !contains_path(basepath, &include_base_path, &compare_paths_options)
            }) {
                base_paths.push(include_base_path);
            }
        }
    }

    base_paths
}

// Go: vfs/vfsmatch/vfsmatch.go:99 globPattern
/// A compiled glob pattern for matching file paths without regex.
#[derive(Clone, Debug, Default)]
struct GlobPattern {
    /// path segments to match (e.g., ["src", "**", "*.ts"])
    components: Vec<Component>,
    /// exclude patterns have different matching rules
    is_exclude: bool,
    case_sensitive: bool,
    /// for "files" patterns, exclude .min.js by default
    exclude_min_js: bool,
}

// Go: vfs/vfsmatch/vfsmatch.go:108 component
/// A single path segment in a glob pattern.
/// Examples: "src" (literal), "*" (wildcard), "*.ts" (wildcard), "**" (recursive)
#[derive(Clone, Debug)]
struct Component {
    kind: ComponentKind,
    /// for Literal: the exact string to match
    literal: String,
    /// for Wildcard: parsed wildcard pattern
    segments: Vec<Segment>,
    /// Include patterns with wildcards skip common package folders (node_modules, etc.)
    skip_package_folders: bool,
}

// Go: vfs/vfsmatch/vfsmatch.go:116 componentKind
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ComponentKind {
    /// exact match (e.g., "src")
    Literal,
    /// contains * or ? (e.g., "*.ts")
    Wildcard,
    /// ** matches zero or more directories
    DoubleAsterisk,
}

// Go: vfs/vfsmatch/vfsmatch.go:126 segment
/// A piece of a wildcard component.
/// Example: "*.ts" becomes [Star, Literal(".ts")]
#[derive(Clone, Debug)]
struct Segment {
    kind: SegmentKind,
    /// only for Literal
    literal: String,
}

// Go: vfs/vfsmatch/vfsmatch.go:131 segmentKind
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SegmentKind {
    /// exact text
    Literal,
    /// * matches any chars except /
    Star,
    /// ? matches single char except /
    Question,
}

// Go: vfs/vfsmatch/vfsmatch.go:141 compileGlobPattern
/// Compiles a glob spec (e.g., "src/**/*.ts") into a pattern.
/// Returns `None` if the pattern would match nothing.
fn compile_glob_pattern(
    spec: &str,
    base_path: &str,
    usage: Usage,
    case_sensitive: bool,
) -> Option<GlobPattern> {
    let mut parts = get_normalized_path_components(spec, base_path);

    // "src/**" without a filename matches nothing (for include patterns)
    if usage != Usage::Exclude && parts.last().map(String::as_str).unwrap_or("") == "**" {
        return None;
    }

    // Normalize root: "/home/" -> "/home"
    parts[0] = remove_trailing_directory_separator(&parts[0]).to_string();

    // Directories implicitly match all files: "src" -> "src/**/*"
    if is_implicit_glob(parts.last().map(String::as_str).unwrap_or("")) {
        parts.push("**".to_string());
        parts.push("*".to_string());
    }

    let mut p = GlobPattern {
        is_exclude: usage == Usage::Exclude,
        case_sensitive,
        exclude_min_js: usage == Usage::Files,
        // Avoid slice growth during compilation.
        components: Vec::with_capacity(parts.len()),
    };

    for part in &parts {
        p.components
            .push(parse_component(part, usage != Usage::Exclude));
    }
    Some(p)
}

// Go: vfs/vfsmatch/vfsmatch.go:172 parseComponent
/// Converts a path segment string into a component.
fn parse_component(s: &str, is_include: bool) -> Component {
    if s == "**" {
        return Component {
            kind: ComponentKind::DoubleAsterisk,
            literal: String::new(),
            segments: Vec::new(),
            skip_package_folders: false,
        };
    }
    if !s.contains(['*', '?']) {
        return Component {
            kind: ComponentKind::Literal,
            literal: s.to_string(),
            segments: Vec::new(),
            skip_package_folders: false,
        };
    }
    Component {
        kind: ComponentKind::Wildcard,
        literal: String::new(),
        segments: parse_segments(s),
        skip_package_folders: is_include,
    }
}

// Go: vfs/vfsmatch/vfsmatch.go:187 parseSegments
/// Breaks "*.ts" into [Star, Literal(".ts")]
fn parse_segments(s: &str) -> Vec<Segment> {
    // Preallocate based on wildcard count: each wildcard contributes 1 segment,
    // and each wildcard can split literals into at most one extra literal segment.
    let b = s.as_bytes();
    let wildcards = b.iter().filter(|&&c| c == b'*' || c == b'?').count();
    let mut result: Vec<Segment> = Vec::with_capacity(2 * wildcards + 1);
    let mut start = 0;
    for i in 0..b.len() {
        if b[i] == b'*' || b[i] == b'?' {
            if i > start {
                result.push(Segment {
                    kind: SegmentKind::Literal,
                    literal: s[start..i].to_string(),
                });
            }
            if b[i] == b'*' {
                result.push(Segment {
                    kind: SegmentKind::Star,
                    literal: String::new(),
                });
            } else {
                result.push(Segment {
                    kind: SegmentKind::Question,
                    literal: String::new(),
                });
            }
            start = i + 1;
        }
    }
    if start < b.len() {
        result.push(Segment {
            kind: SegmentKind::Literal,
            literal: s[start..].to_string(),
        });
    }
    result
}

impl GlobPattern {
    // Go: vfs/vfsmatch/vfsmatch.go:219 (*globPattern).matches
    /// Returns true if path matches this pattern.
    fn matches(&self, path: &str) -> bool {
        self.match_path_parts(path, "", 0, 0, false)
    }

    // Go: vfs/vfsmatch/vfsmatch.go:225 (*globPattern).matchesParts
    /// Returns true if prefix+suffix matches this pattern.
    /// This avoids allocating a combined string for common call sites where prefix ends with '/'.
    fn matches_parts(&self, prefix: &str, suffix: &str) -> bool {
        self.match_path_parts(prefix, suffix, 0, 0, false)
    }

    // Go: vfs/vfsmatch/vfsmatch.go:230 (*globPattern).matchesPrefixParts
    /// Returns true if files under prefix+suffix could match.
    fn matches_prefix_parts(&self, prefix: &str, suffix: &str) -> bool {
        self.match_path_parts(prefix, suffix, 0, 0, true)
    }

    // Go: vfs/vfsmatch/vfsmatch.go:236 (*globPattern).matchPathParts
    /// Like matchPath, but operates on a virtual path formed by prefix+suffix.
    /// Offsets are in the combined string.
    fn match_path_parts(
        &self,
        prefix: &str,
        suffix: &str,
        mut path_offset: usize,
        mut comp_idx: usize,
        prefix_only: bool,
    ) -> bool {
        loop {
            let Some((path_part, next_offset)) = next_path_part_parts(prefix, suffix, path_offset)
            else {
                if prefix_only {
                    return true;
                }
                return self.pattern_satisfied(comp_idx);
            };

            if comp_idx >= self.components.len() {
                return self.is_exclude && !prefix_only;
            }

            let comp = &self.components[comp_idx];
            match comp.kind {
                ComponentKind::DoubleAsterisk => {
                    if self.match_path_parts(prefix, suffix, path_offset, comp_idx + 1, prefix_only)
                    {
                        return true;
                    }
                    if !self.is_exclude
                        && (is_hidden_path(path_part) || is_package_folder(path_part))
                    {
                        return false;
                    }
                    path_offset = next_offset;
                    continue;
                }
                ComponentKind::Literal => {
                    if comp.skip_package_folders && is_package_folder(path_part) {
                        panic!("unreachable: literal components never have skipPackageFolders");
                    }
                    if !self.strings_equal(comp.literal.as_bytes(), path_part.as_bytes()) {
                        return false;
                    }
                }
                ComponentKind::Wildcard => {
                    if comp.skip_package_folders && is_package_folder(path_part) {
                        return false;
                    }
                    if !self.match_wildcard(&comp.segments, path_part.as_bytes()) {
                        return false;
                    }
                }
            }

            path_offset = next_offset;
            comp_idx += 1;
        }
    }

    // Go: vfs/vfsmatch/vfsmatch.go:283 (*globPattern).patternSatisfied
    /// Checks if remaining pattern components can match empty input.
    fn pattern_satisfied(&self, comp_idx: usize) -> bool {
        // A pattern is satisfied when remaining components can match empty input.
        // For both include and exclude patterns, only trailing "**" components may match nothing.
        self.components[comp_idx..]
            .iter()
            .all(|c| c.kind == ComponentKind::DoubleAsterisk)
    }
}

// Go: vfs/vfsmatch/vfsmatch.go:295 nextPathPartSingle
/// Extracts the next path component from path starting at offset.
/// PORT: Go returns `(part, nextOffset, ok)`; `None` is `ok == false`.
fn next_path_part_single(s: &str, mut offset: usize) -> Option<(&str, usize)> {
    let b = s.as_bytes();
    if offset >= b.len() {
        return None;
    }
    if offset == 0 && !b.is_empty() && b[0] == b'/' {
        return Some(("", 1));
    }
    while offset < b.len() && b[offset] == b'/' {
        offset += 1;
    }
    if offset >= b.len() {
        return None;
    }
    let rest = &s[offset..];
    if let Some(idx) = rest.find('/') {
        return Some((&rest[..idx], offset + idx));
    }
    Some((rest, b.len()))
}

// Go: vfs/vfsmatch/vfsmatch.go:315 nextPathPartParts
/// PORT: Go returns `(part, nextOffset, ok)`; `None` is `ok == false`.
fn next_path_part_parts<'a>(
    prefix: &'a str,
    suffix: &'a str,
    mut offset: usize,
) -> Option<(&'a str, usize)> {
    // Fast paths: keep the hot single-string scan tight.
    if suffix.is_empty() {
        return next_path_part_single(prefix, offset);
    }
    if prefix.is_empty() {
        return next_path_part_single(suffix, offset);
    }

    // For matchFilesNoRegex call sites, prefix is a directory path ending in '/',
    // and suffix is a single entry name (no '/'). That makes this significantly
    // simpler than a general-purpose "virtual concatenation" scanner.

    let pb = prefix.as_bytes();
    let total_len = pb.len() + suffix.len();
    if offset >= total_len {
        return None;
    }

    // Handle leading slash (root of absolute path)
    if offset == 0 && pb[0] == b'/' {
        return Some(("", 1));
    }

    // Scan within prefix.
    if offset < pb.len() {
        while offset < pb.len() && pb[offset] == b'/' {
            offset += 1;
        }
        if offset < pb.len() {
            let rest = &prefix[offset..];
            // idx is guaranteed >= 0 for the call sites we care about because prefix ends in '/'.
            // PORT: Go slices with idx -1 and panics when there is no '/'; this panics too.
            let idx = rest.find('/').expect("slice bounds out of range");
            return Some((&rest[..idx], offset + idx));
        }
        // Fall through into suffix region.
    }

    // Scan suffix: it's a single component.
    let s_off = offset - pb.len();
    if s_off >= suffix.len() {
        return None;
    }
    Some((&suffix[s_off..], total_len))
}

impl GlobPattern {
    // Go: vfs/vfsmatch/vfsmatch.go:361 (*globPattern).matchWildcard
    /// Matches a path component against wildcard segments.
    fn match_wildcard(&self, segs: &[Segment], s: &[u8]) -> bool {
        // Include patterns: wildcards at start cannot match hidden files
        if !self.is_exclude
            && !segs.is_empty()
            && is_hidden_path_bytes(s)
            && (segs[0].kind == SegmentKind::Star || segs[0].kind == SegmentKind::Question)
        {
            return false;
        }

        // Fast path: single * followed by literal suffix (e.g., "*.ts")
        if segs.len() == 2
            && segs[0].kind == SegmentKind::Star
            && segs[1].kind == SegmentKind::Literal
        {
            let suffix = segs[1].literal.as_bytes();
            if s.len() < suffix.len() || !self.strings_equal(suffix, &s[s.len() - suffix.len()..]) {
                return false;
            }
            return self.should_include_min_js(s, segs);
        }

        self.match_segments(segs, s) && self.should_include_min_js(s, segs)
    }

    // Go: vfs/vfsmatch/vfsmatch.go:382 (*globPattern).matchSegments
    /// Matches segments against string s using an iterative algorithm.
    /// This avoids exponential backtracking by tracking only the last star position.
    /// The algorithm is O(n*m) where n is the string length and m is pattern length.
    fn match_segments(&self, segs: &[Segment], s: &[u8]) -> bool {
        let (mut seg_idx, mut s_idx) = (0usize, 0usize);
        // PORT: Go uses -1 for "no star"; that is `None`.
        let (mut star_seg_idx, mut star_s_idx): (Option<usize>, usize) = (None, 0);

        while s_idx < s.len() {
            if seg_idx < segs.len() {
                let seg = &segs[seg_idx];
                match seg.kind {
                    SegmentKind::Literal => {
                        let lit = seg.literal.as_bytes();
                        let end = s_idx + lit.len();
                        if end <= s.len() && self.strings_equal(lit, &s[s_idx..end]) {
                            s_idx = end;
                            seg_idx += 1;
                            continue;
                        }
                    }
                    SegmentKind::Question => {
                        if s[s_idx] != b'/' {
                            let (_, size) = decode_rune(&s[s_idx..]);
                            s_idx += size;
                            seg_idx += 1;
                            continue;
                        }
                    }
                    SegmentKind::Star => {
                        // Record star position for backtracking, then try matching zero chars.
                        star_seg_idx = Some(seg_idx);
                        star_s_idx = s_idx;
                        seg_idx += 1;
                        continue;
                    }
                }
            }

            // Current segment didn't match. Backtrack to last star if possible.
            if let Some(star) = star_seg_idx
                && star_s_idx < s.len()
                && s[star_s_idx] != b'/'
            {
                // Star consumes one more character (rune), retry from segment after star.
                let (_, size) = decode_rune(&s[star_s_idx..]);
                star_s_idx += size;
                s_idx = star_s_idx;
                seg_idx = star + 1;
                continue;
            }

            return false;
        }

        // Consume any trailing stars.
        while seg_idx < segs.len() && segs[seg_idx].kind == SegmentKind::Star {
            seg_idx += 1;
        }
        seg_idx >= segs.len()
    }

    // Go: vfs/vfsmatch/vfsmatch.go:433 (*globPattern).shouldIncludeMinJs
    fn should_include_min_js(&self, filename: &[u8], segs: &[Segment]) -> bool {
        if !self.exclude_min_js {
            return true;
        }

        // Preserve legacy behavior:
        // - When matching is case-sensitive, only the exact ".min.js" suffix is excluded by default.
        // - When matching is case-insensitive, any casing variant is excluded by default.
        if !self.has_min_js_suffix(filename) {
            return true;
        }
        // Allow when the user's pattern explicitly references the .min. suffix.
        if self.pattern_mentions_min_suffix(segs) {
            return true;
        }
        false
    }

    // Go: vfs/vfsmatch/vfsmatch.go:451 (*globPattern).hasMinJsSuffix
    fn has_min_js_suffix(&self, filename: &[u8]) -> bool {
        const MIN_JS: &[u8] = b".min.js";
        if self.case_sensitive {
            return filename.ends_with(MIN_JS);
        }
        if filename.len() < MIN_JS.len() {
            return false;
        }
        // Avoid allocating via strings.ToLower; compare suffix case-insensitively.
        equal_fold(&filename[filename.len() - MIN_JS.len()..], MIN_JS)
    }

    // Go: vfs/vfsmatch/vfsmatch.go:463 (*globPattern).patternMentionsMinSuffix
    fn pattern_mentions_min_suffix(&self, segs: &[Segment]) -> bool {
        for seg in segs {
            if seg.kind != SegmentKind::Literal {
                continue;
            }
            // PORT: Go `strings.ToLower` uses the simple (one rune) lowercase
            // mapping. The first rune of Rust `to_lowercase` is that mapping
            // (U+0130 is the only multi-rune case, and it starts with 'i').
            let lit: String = if !self.case_sensitive {
                seg.literal
                    .chars()
                    .map(|c| c.to_lowercase().next().unwrap_or(c))
                    .collect()
            } else {
                seg.literal.clone()
            };
            if lit.contains(".min.js") || lit.contains(".min.") {
                return true;
            }
        }
        false
    }

    // Go: vfs/vfsmatch/vfsmatch.go:480 (*globPattern).stringsEqual
    /// Compares strings with appropriate case sensitivity.
    fn strings_equal(&self, a: &[u8], b: &[u8]) -> bool {
        if self.case_sensitive {
            return a == b;
        }
        equal_fold(a, b)
    }
}

// Go: vfs/vfsmatch/vfsmatch.go:488 isHiddenPath
/// Checks if a path component is hidden (starts with dot).
fn is_hidden_path(name: &str) -> bool {
    is_hidden_path_bytes(name.as_bytes())
}

// PORT: byte form of `isHiddenPath` for `matchWildcard`, which works on bytes.
fn is_hidden_path_bytes(name: &[u8]) -> bool {
    !name.is_empty() && name[0] == b'.'
}

// Go: vfs/vfsmatch/vfsmatch.go:493 isPackageFolder
/// Checks if name is a common package folder (node_modules, etc.)
fn is_package_folder(name: &str) -> bool {
    let b = name.as_bytes();
    // PORT: Go switches on the byte length; "node_modules" (12),
    // "jspm_packages" (13) and "bower_components" (16) have distinct lengths.
    match b.len() {
        12 => equal_fold(b, b"node_modules"),
        13 => equal_fold(b, b"jspm_packages"),
        16 => equal_fold(b, b"bower_components"),
        _ => false,
    }
}

// Go: vfs/vfsmatch/vfsmatch.go:505 ensureTrailingSlash
fn ensure_trailing_slash(s: &str) -> String {
    if !s.is_empty() && !s.ends_with('/') {
        return format!("{s}/");
    }
    s.to_string()
}

// PORT: Go `utf8.DecodeRuneInString`. An invalid or truncated sequence
// gives U+FFFD with width 1. The input is never empty at the call sites.
fn decode_rune(s: &[u8]) -> (char, usize) {
    let head = &s[..s.len().min(4)];
    let valid = match std::str::from_utf8(head) {
        Ok(v) => v,
        // `valid_up_to` marks the valid UTF-8 prefix.
        Err(e) => std::str::from_utf8(&head[..e.valid_up_to()]).unwrap_or(""),
    };
    match valid.chars().next() {
        Some(c) => (c, c.len_utf8()),
        None => (char::REPLACEMENT_CHARACTER, 1),
    }
}

// PORT: Go `unicode.ToUpper` uses the simple mapping. A multi-rune full
// uppercase has no simple mapping, so the rune stays the same.
fn simple_to_upper(c: char) -> char {
    let mut u = c.to_uppercase();
    match (u.next(), u.next()) {
        (Some(single), None) => single,
        _ => c,
    }
}

// PORT: simple case fold key, the same approach as tspath's private helper.
// Two runes are in the same Go `unicode.SimpleFold` orbit when their keys
// are equal. U+0131 (dotless i) has only a Turkic fold entry, so its orbit
// is itself, like Go. Rust and Go can use different Unicode versions; this
// matters only for runes added between those versions.
fn simple_fold_key(c: char) -> char {
    if c == '\u{0131}' {
        return c;
    }
    let u = simple_to_upper(c);
    let mut l = u.to_lowercase();
    match (l.next(), l.next()) {
        (Some(single), None) => single,
        _ => u,
    }
}

// PORT: Go `strings.EqualFold` on byte strings. Runes are decoded like Go
// (see `decode_rune`). Each rune pair must be equal, ASCII case equal, or
// in the same simple fold orbit (see `simple_fold_key`).
fn equal_fold(a: &[u8], b: &[u8]) -> bool {
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        let (sr, sn) = decode_rune(&a[i..]);
        let (tr, tn) = decode_rune(&b[j..]);
        i += sn;
        j += tn;
        if sr == tr {
            continue;
        }
        let (sr, tr) = if tr < sr { (tr, sr) } else { (sr, tr) };
        if (tr as u32) < 0x80 {
            // ASCII only, sr/tr must be upper/lower case
            if sr.is_ascii_uppercase() && tr as u32 == sr as u32 + ('a' as u32 - 'A' as u32) {
                continue;
            }
            return false;
        }
        if simple_fold_key(sr) == simple_fold_key(tr) {
            continue;
        }
        return false;
    }
    i == a.len() && j == b.len()
}

// Go: vfs/vfsmatch/vfsmatch.go:513 globMatcher
/// Combines include and exclude patterns for file matching.
struct GlobMatcher {
    includes: Vec<GlobPattern>,
    excludes: Vec<GlobPattern>,
    /// true if include specs were provided (even if none compiled)
    had_includes: bool,
}

// Go: vfs/vfsmatch/vfsmatch.go:519 newGlobMatcher
fn new_glob_matcher(
    include_specs: &[String],
    exclude_specs: &[String],
    base_path: &str,
    case_sensitive: bool,
    usage: Usage,
) -> GlobMatcher {
    let mut m = GlobMatcher {
        had_includes: !include_specs.is_empty(),
        includes: Vec::with_capacity(include_specs.len()),
        excludes: Vec::with_capacity(exclude_specs.len()),
    };

    for spec in include_specs {
        if let Some(p) = compile_glob_pattern(spec, base_path, usage, case_sensitive) {
            m.includes.push(p);
        }
    }
    for spec in exclude_specs {
        if let Some(p) = compile_glob_pattern(spec, base_path, Usage::Exclude, case_sensitive) {
            m.excludes.push(p);
        }
    }
    m
}

impl GlobMatcher {
    // Go: vfs/vfsmatch/vfsmatch.go:541 (*globMatcher).matchesFileParts
    /// Checks if prefix+suffix matches against the glob patterns.
    /// Returns the index of the matching include pattern, or `None` if not matched.
    /// PORT: Go returns `(0, false)` for no match; that is `None`.
    fn matches_file_parts(&self, prefix: &str, suffix: &str) -> Option<usize> {
        for exclude in &self.excludes {
            if exclude.matches_parts(prefix, suffix) {
                return None;
            }
        }
        if self.includes.is_empty() {
            if self.had_includes {
                return None;
            }
            return Some(0);
        }
        for (i, include) in self.includes.iter().enumerate() {
            if include.matches_parts(prefix, suffix) {
                return Some(i);
            }
        }
        None
    }

    // Go: vfs/vfsmatch/vfsmatch.go:562 (*globMatcher).matchesDirectoryParts
    /// Checks if files under the directory prefix+suffix could match any pattern.
    fn matches_directory_parts(&self, prefix: &str, suffix: &str) -> bool {
        for exclude in &self.excludes {
            if exclude.matches_parts(prefix, suffix) {
                return false;
            }
        }
        if self.includes.is_empty() {
            return !self.had_includes;
        }
        for include in &self.includes {
            if include.matches_prefix_parts(prefix, suffix) {
                return true;
            }
        }
        false
    }
}

// Go: vfs/vfsmatch/vfsmatch.go:580 globVisitor
/// Traverses directories matching files against glob patterns.
/// PORT: Go `vfs.FS` is a borrowed `&dyn Fs` for the length of the walk.
struct GlobVisitor<'a> {
    host: &'a dyn Fs,
    file_matcher: GlobMatcher,
    directory_matcher: GlobMatcher,
    extensions: Vec<&'a str>,
    use_case_sensitive_file_names: bool,
    visited: FxHashSet<String>,
    results: Vec<Vec<String>>,
}

impl GlobVisitor<'_> {
    // Go: vfs/vfsmatch/vfsmatch.go:594 (*globVisitor).visit
    /// Walks a directory tree, collecting files that match the glob patterns.
    /// resolved_real_path, when non-empty, is the already-resolved real path for this
    /// directory (computed incrementally from the parent). When empty, Realpath is
    /// called to resolve symlinks.
    fn visit(
        &mut self,
        path: &str,
        absolute_path: &str,
        mut depth: i32,
        resolved_real_path: String,
    ) {
        // Detect symlink cycles
        let real_path = if !resolved_real_path.is_empty() {
            resolved_real_path
        } else {
            self.host.realpath(absolute_path)
        };
        let canonical_path =
            get_canonical_file_name(&real_path, self.use_case_sensitive_file_names);
        if self.visited.contains(&canonical_path) {
            return;
        }
        self.visited.insert(canonical_path);

        let entries = self.host.get_accessible_entries(absolute_path);

        let path_prefix = ensure_trailing_slash(path);
        let abs_prefix = ensure_trailing_slash(absolute_path);

        for file in &entries.files {
            if !self.extensions.is_empty() && !file_extension_is_one_of(file, &self.extensions) {
                continue;
            }
            if let Some(idx) = self.file_matcher.matches_file_parts(&abs_prefix, file) {
                self.results[idx].push(format!("{path_prefix}{file}"));
            }
        }

        if depth != UNLIMITED_DEPTH {
            depth -= 1;
            if depth == 0 {
                return;
            }
        }

        for dir in &entries.directories {
            if !self
                .directory_matcher
                .matches_directory_parts(&abs_prefix, dir)
            {
                continue;
            }
            let abs_dir = format!("{abs_prefix}{dir}");
            let mut child_real_path = String::new();
            if let Some(symlinks) = &entries.symlinks {
                if !symlinks.contains(dir) {
                    // Non-symlink directory: compute realpath incrementally.
                    child_real_path = combine_paths(&real_path, &[dir.as_str()]);
                }
                // else: symlink directory; leave child_real_path empty to force Realpath call.
            }
            // If Symlinks is nil, the FS doesn't track symlinks;
            // leave child_real_path empty to call Realpath (preserving old behavior).
            self.visit(
                &format!("{path_prefix}{dir}"),
                &abs_dir,
                depth,
                child_real_path,
            );
        }
    }
}

// Go: vfs/vfsmatch/vfsmatch.go:648 matchFiles
#[allow(clippy::too_many_arguments)]
fn match_files(
    path: &str,
    extensions: &[String],
    excludes: &[String],
    includes: &[String],
    use_case_sensitive_file_names: bool,
    current_directory: &str,
    depth: i32,
    host: &dyn Fs,
) -> Vec<String> {
    let path = normalize_path(path);
    let current_directory = normalize_path(current_directory);
    let absolute_path = combine_paths(&current_directory, &[path.as_str()]);

    let file_matcher = new_glob_matcher(
        includes,
        excludes,
        &absolute_path,
        use_case_sensitive_file_names,
        Usage::Files,
    );
    let directory_matcher = new_glob_matcher(
        includes,
        excludes,
        &absolute_path,
        use_case_sensitive_file_names,
        Usage::Directories,
    );

    let results_len = file_matcher.includes.len().max(1);
    let mut v = GlobVisitor {
        host,
        file_matcher,
        directory_matcher,
        extensions: extensions.iter().map(String::as_str).collect(),
        use_case_sensitive_file_names,
        visited: FxHashSet::default(),
        results: vec![Vec::new(); results_len],
    };

    for base_path in get_base_paths(&path, includes, use_case_sensitive_file_names) {
        let abs = combine_paths(&current_directory, &[base_path.as_str()]);
        v.visit(&base_path, &abs, depth, String::new());
    }

    // Fast path: a single include bucket (or no includes) doesn't need flattening.
    if v.results.len() == 1 {
        return v.results.pop().unwrap_or_default();
    }
    v.results.into_iter().flatten().collect()
}

// Go: vfs/vfsmatch/vfsmatch.go:677 SpecMatcher
/// Wraps multiple glob patterns for matching paths.
#[derive(Clone, Debug)]
pub struct SpecMatcher {
    patterns: Vec<GlobPattern>,
}

impl SpecMatcher {
    // Go: vfs/vfsmatch/vfsmatch.go:682 (*SpecMatcher).MatchString
    /// Returns true if any pattern matches the path.
    pub fn match_string(&self, path: &str) -> bool {
        self.patterns.iter().any(|p| p.matches(path))
    }

    // Go: vfs/vfsmatch/vfsmatch.go:692 (*SpecMatcher).MatchIndex
    /// Returns the index of the first matching pattern, or -1.
    pub fn match_index(&self, path: &str) -> i32 {
        for (i, p) in self.patterns.iter().enumerate() {
            if p.matches(path) {
                return i as i32;
            }
        }
        -1
    }
}

// Go: vfs/vfsmatch/vfsmatch.go:703 NewSpecMatcher
/// Creates a matcher for one or more glob specs.
/// It returns a matcher that can test if paths match any of the patterns.
/// PORT: Go returns a nil pointer for no patterns; that is `None`.
pub fn new_spec_matcher(
    specs: &[String],
    base_path: &str,
    usage: Usage,
    use_case_sensitive_file_names: bool,
) -> Option<SpecMatcher> {
    if specs.is_empty() {
        return None;
    }
    let mut patterns = Vec::with_capacity(specs.len());
    for spec in specs {
        if let Some(p) = compile_glob_pattern(spec, base_path, usage, use_case_sensitive_file_names)
        {
            patterns.push(p);
        }
    }
    if patterns.is_empty() {
        return None;
    }
    Some(SpecMatcher { patterns })
}
