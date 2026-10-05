use crate::prelude::*;

impl Checker {
    // Go: checker/jsdoc.go:9 checkUnmatchedJSDocParameters
    pub fn check_unmatched_js_doc_parameters(&mut self, node: Node) {
        // PERF: most JSDoc has no parameter tag. Skip the lazy JSDoc parse
        // when the source text shows that no tag can be one. With no
        // parameter tag, jsdoc_parameters is empty and Go returns below.
        if !may_have_js_doc_parameter_tag(node) {
            debug_assert!(
                get_all_js_doc_tags(node)
                    .iter()
                    .all(|tag| tag.kind() != SyntaxKind::JsDocParameterTag),
                "JSDoc parameter tag missed by the text precheck"
            );
            return;
        }
        let mut jsdoc_parameters: Vec<Node> = Vec::new();
        for tag in get_all_js_doc_tags(node) {
            if tag.kind() == SyntaxKind::JsDocParameterTag {
                let name = tag.name();
                if is_identifier(name) && name.text().is_empty() {
                    continue;
                }
                jsdoc_parameters.push(tag);
            }
        }

        if jsdoc_parameters.is_empty() {
            return;
        }

        let is_js = is_in_js_file(node);
        let mut parameters: FxHashSet<String> = FxHashSet::default();
        let mut excluded_parameters: FxHashSet<i32> = FxHashSet::default();

        for (i, param) in node.parameters().iter().enumerate() {
            let name = param.name();
            if is_identifier(name) {
                parameters.insert(name.text().to_string());
            }
            if is_binding_pattern(name) {
                excluded_parameters.insert(i as i32);
            }
        }
        if self.contains_arguments_reference(node) {
            if is_js {
                let last_js_doc_param_index = jsdoc_parameters.len() as i32 - 1;
                let last_js_doc_param = jsdoc_parameters[last_js_doc_param_index as usize];
                if last_js_doc_param.is_nil() || !is_identifier(last_js_doc_param.name()) {
                    return;
                }
                if excluded_parameters.contains(&last_js_doc_param_index)
                    || parameters.contains(last_js_doc_param.name().text())
                {
                    return;
                }
                let type_expression = last_js_doc_param.type_expression();
                if type_expression.is_nil() || type_expression.type_().is_nil() {
                    return;
                }
                let t = self.get_type_from_type_node(type_expression.type_());
                if self.is_array_type(t) {
                    return;
                }
                self.error(
                    last_js_doc_param.name(),
                    diag::JSDoc_param_tag_has_name_0_but_there_is_no_parameter_with_that_name_It_would_match_arguments_if_it_had_an_array_type,
                    args![last_js_doc_param.name().text()],
                );
            }
        } else {
            for (index, tag) in jsdoc_parameters.iter().copied().enumerate() {
                let name = tag.name();
                let is_name_first = tag.is_name_first();

                if excluded_parameters.contains(&(index as i32))
                    || (is_identifier(name) && parameters.contains(name.text()))
                {
                    continue;
                }

                if is_qualified_name(name) {
                    if is_js {
                        // PORT: the checker-package `entityNameToString(name)` is
                        // `ast.EntityNameToString(name, scanner.GetTextOfNode)`; it is
                        // called directly here to avoid the snake-name clash with the
                        // ast function (same approach as checker_p18.rs).
                        self.error(
                            name,
                            diag::Qualified_name_0_is_not_allowed_without_a_leading_param_object_1,
                            args![
                                entity_name_to_string(name, Some(&get_text_of_node)),
                                entity_name_to_string(name.left(), Some(&get_text_of_node))
                            ],
                        );
                    }
                } else if !is_name_first {
                    self.error_or_suggestion(
                        is_js,
                        name,
                        diag::JSDoc_param_tag_has_name_0_but_there_is_no_parameter_with_that_name,
                        args![name.text()],
                    );
                }
            }
        }
    }
}

// PERF: a text precheck for check_unmatched_js_doc_parameters. It walks the
// same hosts as get_all_js_doc_tags. The JSDoc of a host is parsed from the
// comment ranges at host.pos(), and those ranges all end before
// skip_trivia(host.pos()). A parameter tag starts at an `@` that
// `is_param_tag_mark` accepts. False means that no host can have a
// JsDocParameterTag. True is conservative.
//
// PERF: chkfacts1. The marks of a static text are found in one scan and kept
// for the last file of the thread (`PARAM_TAG_MARKS`). A host whose range
// has no mark from its pos to its end (the end of its first token or later)
// needs no `skip_trivia`, and a file with no mark returns at once.
fn may_have_js_doc_parameter_tag(node: Node) -> bool {
    let file = get_source_file_of_node(node);
    if file.is_nil() {
        return true;
    }
    let text = source_file_text(file);
    let Some(text) = text.as_static() else {
        // A freeable text (a language service edit): scan each range.
        return js_doc_hosts_any(node, |_, pos| {
            let end = skip_trivia(&text, pos as i32) as usize;
            let Some(range) = text.as_bytes().get(pos..end) else {
                return true;
            };
            memchr::memchr_iter(b'@', range).any(|i| is_param_tag_mark(text.as_bytes(), pos + i))
        });
    };
    PARAM_TAG_MARKS.with_borrow_mut(|(key, marks)| {
        // A static text is never freed, so its address names it.
        if *key != (text.as_ptr() as usize, text.len()) {
            *key = (text.as_ptr() as usize, text.len());
            marks.clear();
            marks.extend(
                memchr::memchr_iter(b'@', text.as_bytes())
                    .filter(|&i| is_param_tag_mark(text.as_bytes(), i))
                    .map(|i| i as u32),
            );
        }
        js_doc_hosts_any(node, |host, pos| {
            let first = marks.partition_point(|&m| (m as usize) < pos);
            marks.get(first).is_some_and(|&m| {
                (m as i32) < host.end() && (m as i32) < skip_trivia(text, pos as i32)
            })
        })
    })
}

thread_local! {
    /// The address and length of the last static text that
    /// `may_have_js_doc_parameter_tag` read, and the positions in it that
    /// `is_param_tag_mark` accepts, in order.
    static PARAM_TAG_MARKS: std::cell::RefCell<((usize, usize), Vec<u32>)> =
        const { std::cell::RefCell::new(((0, 0), Vec::new())) };
}

/// Whether `has_mark(host, pos)` holds for a JSDoc host of `node` (the hosts
/// that `get_all_js_doc_tags` reads), or a host has no position.
fn js_doc_hosts_any(node: Node, mut has_mark: impl FnMut(Node, usize) -> bool) -> bool {
    let mut current = node;
    while current.is_some() {
        if current.flags().intersects(NodeFlags::HAS_JS_DOC) {
            let Ok(pos) = usize::try_from(current.pos()) else {
                return true;
            };
            if has_mark(current, pos) {
                return true;
            }
        }
        current = get_next_js_doc_comment_location(current);
    }
    false
}

/// Whether the `@` at `at` in `text` can start a parameter tag: the tag
/// name `param`, `arg` or `argument`, or a name with a unicode escape (a
/// `\` after its first letters).
fn is_param_tag_mark(text: &[u8], at: usize) -> bool {
    let name = &text[at + 1..];
    if name.starts_with(b"param") || name.starts_with(b"arg") {
        return true;
    }
    let letters = name
        .iter()
        .take_while(|&&b| b.is_ascii_alphanumeric() || b == b'_' || b == b'$')
        .count();
    name.get(letters) == Some(&b'\\')
}

// Go: checker/jsdoc.go:86 getAllJSDocTags
pub fn get_all_js_doc_tags(node: Node) -> Vec<Node> {
    if !node.flags().intersects(NodeFlags::JS_DOC) {
        let mut current = node;
        while current.is_some() {
            let jsdocs = current.js_doc(Node::NIL);
            if !jsdocs.is_empty() {
                let last_js_doc = jsdocs.get(jsdocs.len() - 1);
                let tags = last_js_doc.tags();
                if !tags.is_nil() {
                    return tags.nodes().to_vec();
                }
            }
            current = get_next_js_doc_comment_location(current);
        }
    }
    Vec::new()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `is_param_tag_mark` at the first `@` of each text.
    #[test]
    fn param_tag_marks() {
        let cases = [
            ("@param x", true),
            ("@arg x", true),
            ("@argument x", true),
            (r"@param x", true),
            (r"@\u{70}aram x", true),
            ("@returns x", false),
            ("@type {number}", false),
            ("@ param x", false),
            ("a@b.c", false),
            ("@", false),
        ];
        for (text, want) in cases {
            let at = text.find('@').unwrap();
            assert_eq!(is_param_tag_mark(text.as_bytes(), at), want, "{text}");
        }
    }

    /// The precheck is true for each function whose JSDoc (Go
    /// `getAllJSDocTags`) has a parameter tag, also when the mark is in a
    /// host above the function, and false for the functions with no mark in
    /// their ranges, before and after the marks of the file.
    #[test]
    fn precheck_finds_every_parameter_tag() {
        let source = r"/** @returns {number} */
function before(a) { return 1; }
/** @param {number} a */
function documented(a) {}
/** @param {number} b
 */
function wrong(a) {}
/** @param {number} c */
function escaped(a) {}
/** @param {number} d */
const assigned = function (a) {};
/** no tag: a@b.c */
function mail(a) {}
/** @returns {number} */
function after(a) { return 1; }
function plain(a) {}
";
        let dir =
            std::env::temp_dir().join(format!("ts_goport_jsdoc_marks_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("a.js"), source).unwrap();
        std::fs::write(
            dir.join("tsconfig.json"),
            r#"{ "compilerOptions": { "allowJs": true, "checkJs": true, "noEmit": true, "types": [] }, "files": ["a.js"] }"#,
        )
        .unwrap();
        let config = dir.join("tsconfig.json");
        let program = crate::program::try_load_version(&config.to_string_lossy(), |_| {})
            .unwrap_or_else(|e| panic!("cannot load {}: {e}", config.display()));
        let _ = std::fs::remove_dir_all(&dir);
        let scope = crate::core::enter_program(Some(program));
        let file = program
            .source_files()
            .find(|file| file.info.file_name.ends_with("/a.js"))
            .expect("a.js is not in the program")
            .root;
        let mut got = Vec::new();
        for statement in file.statements().iter() {
            let function = match statement.kind() {
                SyntaxKind::FunctionDeclaration => statement,
                SyntaxKind::VariableStatement => statement
                    .declaration_list()
                    .declarations()
                    .nodes()
                    .first()
                    .map_or(Node::NIL, |d| d.initializer()),
                _ => continue,
            };
            let has_tag = get_all_js_doc_tags(function)
                .iter()
                .any(|tag| tag.kind() == SyntaxKind::JsDocParameterTag);
            let may_have = may_have_js_doc_parameter_tag(function);
            assert!(may_have || !has_tag, "statement {}", got.len());
            got.push(may_have);
        }
        drop(scope);
        crate::program::release_program(program);
        // before, documented, wrong, escaped, assigned, mail, after, plain.
        assert_eq!(got, [false, true, true, true, true, false, false, false]);
    }
}
