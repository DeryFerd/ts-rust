//! Checker-owned canonical diagnostics.
//!
//! TypeScript-Go diagnostics may have no source location (for example, a
//! missing global type) and may accumulate related information after their
//! primary occurrence has already been issued. This collection preserves raw
//! issuance order for checker algorithms. Final compiler aggregation owns the
//! pinned `CompareDiagnostics` sorting policy.

use ts_ast::NodeRef;
use ts_core::TextRange;
use ts_diagnostics::Diagnostic;

/// Related information attached to one checker diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalCheckerRelatedInformation {
    pub node: Option<NodeRef>,
    pub diagnostic: Diagnostic,
}

/// Exact source range for a checker diagnostic, tied to its owning syntax node.
///
/// Construction alone does not prove ownership because the AST is held by the
/// production checker and compiler boundaries. Both boundaries validate that
/// the anchor is the diagnostic's primary node and that the nonempty range is
/// contained by the anchor and its source file before publishing it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CanonicalCheckerDiagnosticRange {
    anchor: NodeRef,
    range: TextRange,
}

impl CanonicalCheckerDiagnosticRange {
    #[must_use]
    pub const fn new(anchor: NodeRef, range: TextRange) -> Self {
        Self { anchor, range }
    }

    #[must_use]
    pub const fn anchor(self) -> NodeRef {
        self.anchor
    }

    #[must_use]
    pub const fn range(self) -> TextRange {
        self.range
    }

    /// Validates this override against the retained diagnostic and source AST.
    #[must_use]
    pub fn is_valid_for(
        self,
        diagnostic_node: NodeRef,
        anchor_range: TextRange,
        source_range: TextRange,
    ) -> bool {
        self.anchor == diagnostic_node
            && self.range.start.get() < self.range.end.get()
            && source_range.start.get() <= self.range.start.get()
            && self.range.end.get() <= source_range.end.get()
            && anchor_range.start.get() <= self.range.start.get()
            && self.range.end.get() <= anchor_range.end.get()
    }
}

/// One canonical checker diagnostic with stable related-information order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalCheckerDiagnostic {
    pub node: Option<NodeRef>,
    pub range_override: Option<CanonicalCheckerDiagnosticRange>,
    pub diagnostic: Diagnostic,
    pub related_information: Vec<CanonicalCheckerRelatedInformation>,
}

impl CanonicalCheckerDiagnostic {
    /// Appends related information without applying duplicate or length policy.
    ///
    /// Callers such as duplicate-declaration reporting own those rules at the
    /// exact checker branch where the related diagnostic is constructed.
    pub fn append_related(&mut self, related: CanonicalCheckerRelatedInformation) {
        self.related_information.push(related);
    }
}

/// Deterministic owner for nonfatal checker diagnostics.
///
/// [`Self::add`] is unconditional, matching the checker's ordinary diagnostic
/// path. [`Self::lookup_or_issue`] matches the complete current diagnostic,
/// including related information, and is reserved for checker paths that
/// explicitly request lookup semantics. The collection retains raw issuance
/// order; it is not the compiler's final sorted diagnostic view.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CanonicalCheckerDiagnostics {
    diagnostics: Vec<CanonicalCheckerDiagnostic>,
}

impl CanonicalCheckerDiagnostics {
    /// Unconditionally appends one primary diagnostic.
    pub fn add(
        &mut self,
        node: Option<NodeRef>,
        diagnostic: Diagnostic,
    ) -> &mut CanonicalCheckerDiagnostic {
        self.append_entry(CanonicalCheckerDiagnostic {
            node,
            range_override: None,
            diagnostic,
            related_information: Vec::new(),
        })
    }

    /// Unconditionally appends one primary diagnostic at an exact subrange.
    pub fn add_at_range(
        &mut self,
        range_override: CanonicalCheckerDiagnosticRange,
        diagnostic: Diagnostic,
    ) -> &mut CanonicalCheckerDiagnostic {
        self.append_entry(CanonicalCheckerDiagnostic {
            node: Some(range_override.anchor()),
            range_override: Some(range_override),
            diagnostic,
            related_information: Vec::new(),
        })
    }

    /// Returns an equal current diagnostic or unconditionally issues one.
    ///
    /// Equality includes the complete related-information vector. In
    /// particular, a pristine candidate does not match an earlier occurrence
    /// after related information has been attached to that occurrence.
    pub fn lookup_or_issue(
        &mut self,
        node: Option<NodeRef>,
        diagnostic: Diagnostic,
    ) -> &mut CanonicalCheckerDiagnostic {
        let candidate = CanonicalCheckerDiagnostic {
            node,
            range_override: None,
            diagnostic,
            related_information: Vec::new(),
        };
        if let Some(index) = self
            .diagnostics
            .iter()
            .position(|current| current == &candidate)
        {
            return &mut self.diagnostics[index];
        }
        self.append_entry(candidate)
    }

    /// Returns an equal exact-range diagnostic or unconditionally issues one.
    pub fn lookup_or_issue_at_range(
        &mut self,
        range_override: CanonicalCheckerDiagnosticRange,
        diagnostic: Diagnostic,
    ) -> &mut CanonicalCheckerDiagnostic {
        let candidate = CanonicalCheckerDiagnostic {
            node: Some(range_override.anchor()),
            range_override: Some(range_override),
            diagnostic,
            related_information: Vec::new(),
        };
        if let Some(index) = self
            .diagnostics
            .iter()
            .position(|current| current == &candidate)
        {
            return &mut self.diagnostics[index];
        }
        self.append_entry(candidate)
    }

    /// Returns a diagnostic with the same primary node and payload, ignoring
    /// related information accumulated by an earlier retry, or issues it.
    ///
    /// This is intentionally checker-internal: only retry staging may collapse
    /// the same primary emission while unioning its related information.
    pub(super) fn lookup_primary_or_issue(
        &mut self,
        node: Option<NodeRef>,
        range_override: Option<CanonicalCheckerDiagnosticRange>,
        diagnostic: Diagnostic,
    ) -> &mut CanonicalCheckerDiagnostic {
        if let Some(index) = self.diagnostics.iter().position(|current| {
            current.node == node
                && current.range_override == range_override
                && current.diagnostic == diagnostic
        }) {
            return &mut self.diagnostics[index];
        }
        self.append_entry(CanonicalCheckerDiagnostic {
            node,
            range_override,
            diagnostic,
            related_information: Vec::new(),
        })
    }

    fn append_entry(
        &mut self,
        diagnostic: CanonicalCheckerDiagnostic,
    ) -> &mut CanonicalCheckerDiagnostic {
        self.diagnostics.push(diagnostic);
        self.diagnostics
            .last_mut()
            .expect("a diagnostic was just appended")
    }

    /// Diagnostics in raw issuance order before compiler aggregation sorting.
    #[must_use]
    pub fn as_slice(&self) -> &[CanonicalCheckerDiagnostic] {
        &self.diagnostics
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.diagnostics.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.diagnostics.is_empty()
    }

    #[must_use]
    pub fn into_vec(self) -> Vec<CanonicalCheckerDiagnostic> {
        self.diagnostics
    }
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
    use ts_core::{TextPos, TextRange};
    use ts_diagnostics::{Diagnostic, message_by_code};
    use ts_parser::parse_source_file;

    use super::{
        CanonicalCheckerDiagnosticRange, CanonicalCheckerDiagnostics,
        CanonicalCheckerRelatedInformation,
    };

    #[test]
    fn unconditional_add_preserves_raw_issuance_order() {
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let missing = Diagnostic::with_arguments(message_by_code(2318).unwrap(), ["Array"]);
        let duplicate = Diagnostic::with_arguments(message_by_code(2300).unwrap(), ["Item"]);

        diagnostics.add(None, missing.clone());
        diagnostics.add(None, missing);
        diagnostics.add(None, duplicate);

        assert_eq!(diagnostics.len(), 3);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2318);
        assert_eq!(diagnostics.as_slice()[1].diagnostic.code(), 2318);
        assert_eq!(diagnostics.as_slice()[2].diagnostic.code(), 2300);
        assert!(
            diagnostics
                .as_slice()
                .iter()
                .all(|entry| entry.node.is_none() && entry.range_override.is_none())
        );
    }

    #[test]
    fn lookup_equality_includes_current_related_information() {
        let parsed = parse_source_file("let first = 1; let second = 2;");
        let file = FileId::new(1);
        let mut identifiers = parsed.arena.iter().filter_map(|(node, record)| {
            (record.kind == ts_ast::SyntaxKind::Identifier).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        });
        let first_node = identifiers.next().unwrap();
        let second_node = identifiers.next().unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let primary = Diagnostic::with_arguments(message_by_code(2451).unwrap(), ["value"]);
        let first_related = CanonicalCheckerRelatedInformation {
            node: Some(second_node),
            diagnostic: Diagnostic::with_arguments(message_by_code(6203).unwrap(), ["value"]),
        };
        let second_related = CanonicalCheckerRelatedInformation {
            node: None,
            diagnostic: Diagnostic::new(message_by_code(6204).unwrap()),
        };

        diagnostics
            .lookup_or_issue(Some(first_node), primary.clone())
            .append_related(first_related.clone());
        diagnostics
            .lookup_or_issue(Some(first_node), primary.clone())
            .append_related(second_related.clone());
        diagnostics.lookup_or_issue(Some(first_node), primary.clone());
        diagnostics.lookup_or_issue(Some(first_node), primary);

        assert_eq!(diagnostics.len(), 3);
        assert_eq!(
            diagnostics.as_slice()[0].related_information,
            [first_related]
        );
        assert_eq!(
            diagnostics.as_slice()[1].related_information,
            [second_related]
        );
        assert!(diagnostics.as_slice()[2].related_information.is_empty());
    }

    #[test]
    fn related_append_is_unconditional() {
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let related = CanonicalCheckerRelatedInformation {
            node: None,
            diagnostic: Diagnostic::new(message_by_code(6204).unwrap()),
        };
        let diagnostic = diagnostics.add(
            None,
            Diagnostic::with_arguments(message_by_code(2300).unwrap(), ["item"]),
        );

        diagnostic.append_related(related.clone());
        diagnostic.append_related(related.clone());

        assert_eq!(diagnostic.related_information, [related.clone(), related]);
    }

    #[test]
    fn primary_lookup_ignores_related_information_for_retry_staging() {
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let primary = Diagnostic::with_arguments(message_by_code(2300).unwrap(), ["item"]);
        let related = CanonicalCheckerRelatedInformation {
            node: None,
            diagnostic: Diagnostic::new(message_by_code(6204).unwrap()),
        };
        diagnostics
            .lookup_primary_or_issue(None, None, primary.clone())
            .append_related(related.clone());
        let retry = diagnostics.lookup_primary_or_issue(None, None, primary);
        if !retry.related_information.contains(&related) {
            retry.append_related(related.clone());
        }

        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics.as_slice()[0].related_information, [related]);
    }

    #[test]
    fn exact_range_participates_in_lookup_order_and_retry_identity() {
        let parsed = parse_source_file("let target = 1;");
        let file = FileId::new(2);
        let (identifier, record) = parsed
            .arena
            .iter()
            .find(|(_, record)| record.kind == ts_ast::SyntaxKind::Identifier)
            .unwrap();
        let anchor = NodeRef::new(parsed.arena.id(), file, identifier);
        let first = CanonicalCheckerDiagnosticRange::new(
            anchor,
            TextRange::new(
                record.range.start,
                TextPos::new(record.range.start.get() + 1),
            ),
        );
        let second = CanonicalCheckerDiagnosticRange::new(
            anchor,
            TextRange::new(
                TextPos::new(record.range.start.get() + 1),
                TextPos::new(record.range.start.get() + 2),
            ),
        );
        let primary = Diagnostic::with_arguments(message_by_code(2300).unwrap(), ["target"]);

        diagnostics_lookup_at_ranges(first, second, primary);
    }

    #[test]
    fn ambient_diagnostics_preserve_pinned_messages_and_source_anchors() {
        let source = "function foo();\ndeclare const token: number = 1 + 2;";
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(3);
        let (function, function_record) = parsed
            .arena
            .iter()
            .find(|(_, record)| record.kind == SyntaxKind::FunctionDeclaration)
            .unwrap();
        let NodeData::FunctionDeclaration(function_data) = &function_record.data else {
            unreachable!()
        };
        let function_node = NodeRef::new(parsed.arena.id(), file, function);
        let function_name = NodeRef::new(
            parsed.arena.id(),
            file,
            function_data.name.expect("the function is named"),
        );
        let keyword_range = CanonicalCheckerDiagnosticRange::new(
            function_node,
            TextRange::new(
                function_record.range.start,
                TextPos::new(function_record.range.start.get() + 8),
            ),
        );
        let initializer = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                Some(NodeRef::new(parsed.arena.id(), file, variable.initializer?))
            })
            .unwrap();
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        diagnostics.add_at_range(
            keyword_range,
            Diagnostic::new(message_by_code(1046).unwrap()),
        );
        diagnostics.add(
            Some(function_name),
            Diagnostic::with_arguments(message_by_code(7010).unwrap(), ["foo", "any"]),
        );
        diagnostics.add(
            Some(initializer),
            Diagnostic::new(message_by_code(1039).unwrap()),
        );

        let entries = diagnostics.as_slice();
        assert_eq!(entries[0].diagnostic.code(), 1046);
        assert_eq!(entries[0].node, Some(function_node));
        assert_eq!(entries[0].range_override, Some(keyword_range));
        assert_eq!(
            entries[0].diagnostic.render().unwrap(),
            "Top-level declarations in .d.ts files must start with either a 'declare' or 'export' modifier."
        );
        assert!(keyword_range.is_valid_for(
            function_node,
            function_record.range,
            parsed.arena.get(parsed.source_file).unwrap().range,
        ));
        assert_eq!(source_range_text(source, keyword_range.range()), "function");

        assert_eq!(entries[1].diagnostic.code(), 7010);
        assert_eq!(entries[1].node, Some(function_name));
        assert!(entries[1].range_override.is_none());
        assert_eq!(
            entries[1].diagnostic.render().unwrap(),
            "'foo', which lacks return-type annotation, implicitly has an 'any' return type."
        );
        assert_eq!(
            source_range_text(source, parsed.arena.get(function_name.node).unwrap().range),
            "foo"
        );

        assert_eq!(entries[2].diagnostic.code(), 1039);
        assert_eq!(entries[2].node, Some(initializer));
        assert!(entries[2].range_override.is_none());
        assert_eq!(
            entries[2].diagnostic.render().unwrap(),
            "Initializers are not allowed in ambient contexts."
        );
        assert_eq!(
            source_range_text(source, parsed.arena.get(initializer.node).unwrap().range),
            "1 + 2"
        );
    }

    #[test]
    fn missing_declaration_modifier_ranges_cover_only_the_first_keyword() {
        for (source, kind, keyword) in [
            (
                "function missing();",
                SyntaxKind::FunctionDeclaration,
                "function",
            ),
            ("var missing: number;", SyntaxKind::VariableStatement, "var"),
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(4);
            let (declaration, record) = parsed
                .arena
                .iter()
                .find(|(_, record)| record.kind == kind)
                .unwrap();
            let anchor = NodeRef::new(parsed.arena.id(), file, declaration);
            let range = CanonicalCheckerDiagnosticRange::new(
                anchor,
                TextRange::new(
                    record.range.start,
                    TextPos::new(record.range.start.get() + u32::try_from(keyword.len()).unwrap()),
                ),
            );
            let mut diagnostics = CanonicalCheckerDiagnostics::default();
            diagnostics.add_at_range(range, Diagnostic::new(message_by_code(1046).unwrap()));

            let diagnostic = &diagnostics.as_slice()[0];
            assert_eq!(diagnostic.node, Some(anchor));
            assert_eq!(diagnostic.range_override, Some(range));
            assert!(range.is_valid_for(
                anchor,
                record.range,
                parsed.arena.get(parsed.source_file).unwrap().range,
            ));
            assert_eq!(source_range_text(source, range.range()), keyword);
        }
    }

    fn source_range_text(source: &str, range: TextRange) -> &str {
        let start = usize::try_from(range.start.get()).unwrap();
        let end = usize::try_from(range.end.get()).unwrap();
        &source[start..end]
    }

    fn diagnostics_lookup_at_ranges(
        first: CanonicalCheckerDiagnosticRange,
        second: CanonicalCheckerDiagnosticRange,
        primary: Diagnostic,
    ) {
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        diagnostics.lookup_or_issue_at_range(first, primary.clone());
        diagnostics.lookup_or_issue_at_range(first, primary.clone());
        diagnostics.lookup_or_issue_at_range(second, primary.clone());
        diagnostics
            .lookup_primary_or_issue(Some(first.anchor()), Some(first), primary.clone())
            .append_related(CanonicalCheckerRelatedInformation {
                node: None,
                diagnostic: Diagnostic::new(message_by_code(6204).unwrap()),
            });
        diagnostics.lookup_primary_or_issue(Some(second.anchor()), Some(second), primary);

        assert_eq!(diagnostics.len(), 2);
        assert_eq!(diagnostics.as_slice()[0].range_override, Some(first));
        assert_eq!(diagnostics.as_slice()[1].range_override, Some(second));
        assert_eq!(diagnostics.as_slice()[0].related_information.len(), 1);
        assert!(diagnostics.as_slice()[1].related_information.is_empty());
    }
}
