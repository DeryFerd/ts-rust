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
    use ts_ast::{FileId, NodeRef};
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
