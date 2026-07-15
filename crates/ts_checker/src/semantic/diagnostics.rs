//! Checker-owned canonical diagnostics.
//!
//! TypeScript-Go diagnostics may have no source location (for example, a
//! missing global type) and may accumulate related information after their
//! primary occurrence has already been issued. This collection preserves
//! exact insertion order while coalescing equal primary occurrences, so
//! nonfatal semantic algorithms can report and continue without later sorting
//! or replaying work.

use ts_ast::NodeRef;
use ts_diagnostics::Diagnostic;

/// Related information attached to one checker diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalCheckerRelatedInformation {
    pub node: Option<NodeRef>,
    pub diagnostic: Diagnostic,
}

/// One canonical checker diagnostic with stable related-information order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalCheckerDiagnostic {
    pub node: Option<NodeRef>,
    pub diagnostic: Diagnostic,
    pub related_information: Vec<CanonicalCheckerRelatedInformation>,
}

/// A collection-local handle returned when a primary diagnostic is issued.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct CanonicalCheckerDiagnosticId(usize);

/// Deterministic owner for nonfatal checker diagnostics.
///
/// Primary diagnostics retain first-insertion order. Issuing the same node,
/// message, arguments, and details again returns the existing handle rather
/// than appending another occurrence. Related information is likewise
/// appended only once and retains the caller's order.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CanonicalCheckerDiagnostics {
    diagnostics: Vec<CanonicalCheckerDiagnostic>,
}

impl CanonicalCheckerDiagnostics {
    /// Issues a primary diagnostic or returns its existing collection handle.
    pub fn issue(
        &mut self,
        node: Option<NodeRef>,
        diagnostic: Diagnostic,
    ) -> CanonicalCheckerDiagnosticId {
        if let Some(index) = self
            .diagnostics
            .iter()
            .position(|current| current.node == node && current.diagnostic == diagnostic)
        {
            return CanonicalCheckerDiagnosticId(index);
        }
        let id = CanonicalCheckerDiagnosticId(self.diagnostics.len());
        self.diagnostics.push(CanonicalCheckerDiagnostic {
            node,
            diagnostic,
            related_information: Vec::new(),
        });
        id
    }

    /// Appends unique related information to an issued diagnostic.
    ///
    /// Returns false for an out-of-range handle or an equal existing related
    /// occurrence. Either case leaves the collection unchanged.
    pub fn add_related_information(
        &mut self,
        id: CanonicalCheckerDiagnosticId,
        related: CanonicalCheckerRelatedInformation,
    ) -> bool {
        let Some(diagnostic) = self.diagnostics.get_mut(id.0) else {
            return false;
        };
        if diagnostic.related_information.contains(&related) {
            return false;
        }
        diagnostic.related_information.push(related);
        true
    }

    /// Returns an issued diagnostic by its collection-local handle.
    #[must_use]
    pub fn get(&self, id: CanonicalCheckerDiagnosticId) -> Option<&CanonicalCheckerDiagnostic> {
        self.diagnostics.get(id.0)
    }

    /// Primary diagnostics in exact first-insertion order.
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
    use ts_diagnostics::{Diagnostic, message_by_code};
    use ts_parser::parse_source_file;

    use super::{CanonicalCheckerDiagnostics, CanonicalCheckerRelatedInformation};

    #[test]
    fn optional_locations_deduplicate_without_reordering() {
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let missing = Diagnostic::with_arguments(message_by_code(2318).unwrap(), ["Array"]);
        let duplicate = Diagnostic::with_arguments(message_by_code(2300).unwrap(), ["Item"]);

        let first = diagnostics.issue(None, missing.clone());
        assert_eq!(diagnostics.issue(None, missing), first);
        diagnostics.issue(None, duplicate);

        assert_eq!(diagnostics.len(), 2);
        assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2318);
        assert_eq!(diagnostics.as_slice()[1].diagnostic.code(), 2300);
        assert!(
            diagnostics
                .as_slice()
                .iter()
                .all(|entry| entry.node.is_none())
        );
    }

    #[test]
    fn related_information_is_unique_and_stably_appended() {
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
        let id = diagnostics.issue(
            Some(first_node),
            Diagnostic::with_arguments(message_by_code(2451).unwrap(), ["value"]),
        );
        let first_related = CanonicalCheckerRelatedInformation {
            node: Some(second_node),
            diagnostic: Diagnostic::with_arguments(message_by_code(6203).unwrap(), ["value"]),
        };
        let second_related = CanonicalCheckerRelatedInformation {
            node: None,
            diagnostic: Diagnostic::new(message_by_code(6204).unwrap()),
        };

        assert!(diagnostics.add_related_information(id, first_related.clone()));
        assert!(!diagnostics.add_related_information(id, first_related.clone()));
        assert!(diagnostics.add_related_information(id, second_related.clone()));

        assert_eq!(
            diagnostics.get(id).unwrap().related_information,
            [first_related, second_related]
        );
    }
}
