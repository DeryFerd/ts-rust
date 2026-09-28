//! Port of Go package `internal/spanmap` (`spanmap.go`, tsgo#4712).
//!
//! Package spanmap provides bidirectional span-aware mapping between a content mapper's virtual text
//! and its original, untransformed source. Unlike a source map, which records
//! point correspondences and leaves spans and "no origin" implicit, a SpanMap records explicit segments
//! for the parts of the virtual text that correspond to the original; positions not covered by any
//! segment are synthesized (virtual content with no original counterpart). All positions are absolute
//! offsets (core.TextPos), matching the compiler's TextRange model.
//!
//! PORT: Go `core.TextPos` is `i32`. Go methods that accept a nil `*SpanMap` receiver take
//! `m: Option<&SpanMap>` (`None` is nil); call them as `SpanMap::method(m, ...)`. Go int32
//! arithmetic wraps; the port uses wrapping operations where mapper input reaches it unchecked
//! (`unmarshal`, `marshal`, the sort comparators).

// Keep this in sync with spanMap.ts

use crate::prelude::*;

use crate::flags_macros::{go_enum, go_flags};
use crate::frontend::json::{json_marshal, json_unmarshal};
use crate::gostd::slices::{binary_search_func, sort_func};
use crate::gostd::{GoError, errors};
use std::sync::OnceLock;

// Go: spanmap/spanmap.go:21 Kind
// Kind describes how positions inside a segment relate the virtual span to the original span.
go_enum!(Kind, i32 {
    // KindVerbatim segments are length-preserving: the virtual and original spans have the same
    // length and interior positions map 1:1 (OriginalPos = pos - VirtualStart + OriginalStart). A virtual span
    // fully within a verbatim segment maps to an exact original span.
    VERBATIM = 0;
    // KindAtom segments map a virtual span to an original span as a whole; interior positions are not
    // interpolatable (the lengths may differ), so positions within clamp to the segment's endpoints.
    // Used for renamed identifiers or short expressions.
    ATOM = 1;
    // KindAlias has atom geometry, but additionally asserts that the virtual and original texts are
    // names for the same logical entity. Diagnostic presentation may substitute the original name.
    ALIAS = 2;
});

// Go: spanmap/spanmap.go:40 Feature
// Feature selects which language-service operations may use a segment. Diagnostics are intentionally not
// represented: diagnostics on virtual text may not opt out of reporting. Text edits additionally require exact
// verbatim geometry regardless of feature participation.
go_flags!(Feature, i32 {
    HOVER = 1 << 0;
    SIGNATURE_HELP = 1 << 1;
    COMPLETION = 1 << 2;
    DEFINITION = 1 << 3;
    TYPE_DEFINITION = 1 << 4;
    IMPLEMENTATION = 1 << 5;
    REFERENCES = 1 << 6;
    DOCUMENT_HIGHLIGHTS = 1 << 7;
    RENAME = 1 << 8;
    CALL_HIERARCHY = 1 << 9;
    CODE_ACTIONS = 1 << 10;
    FORMATTING = 1 << 11;
    INLAY_HINTS = 1 << 12;
    SEMANTIC_TOKENS = 1 << 13;
    FOLDING_RANGES = 1 << 14;
    SELECTION_RANGES = 1 << 15;
    LINKED_EDITING = 1 << 16;
    AUTO_INSERT = 1 << 17;
    DOCUMENT_SYMBOLS = 1 << 18;
    CODE_LENS = 1 << 19;
    NONE = 0;
    ALL = ((1 << 19) << 1) - 1;
});

// Go: spanmap/spanmap.go:67 featureMask
const FEATURE_MASK: Feature = Feature::ALL;

// Go: spanmap/spanmap.go:70 Fidelity
// Fidelity describes how faithfully a mapped span reflects the original.
go_enum!(Fidelity, i32 {
    // FidelityExact means the span fell entirely within a single verbatim segment and maps precisely.
    EXACT = 0;
    // FidelityAtom means the span fell within a single atom segment and maps to that atom's span.
    ATOM = 1;
    // FidelityApproximate means the span crossed segment boundaries; its endpoints were mapped and clamped.
    APPROXIMATE = 2;
    // FidelityNone means the span had no original counterpart (it was entirely synthesized).
    NONE = 3;
});

impl Fidelity {
    // Go: spanmap/spanmap.go:85 Fidelity.IsExact
    // IsExact reports whether the mapping was fully faithful — the input fell within a single verbatim span —
    // so the result maps 1:1 and can host a text edit written back to the original.
    #[must_use]
    pub fn is_exact(self) -> bool {
        self == Fidelity::EXACT
    }

    // Go: spanmap/spanmap.go:91 Fidelity.IsSingleSegment
    // IsSingleSegment reports whether the input fell within one segment, verbatim or atom, so the result is a
    // concrete location rather than a best-effort approximation across boundaries or a synthesized gap.
    #[must_use]
    pub fn is_single_segment(self) -> bool {
        self == Fidelity::EXACT || self == Fidelity::ATOM
    }

    // Go: spanmap/spanmap.go:97 Fidelity.IsNone
    // IsNone reports whether the input had no original counterpart, meaning the mapped result is a synthesized
    // gap that does not correspond to any location in the original text.
    #[must_use]
    pub fn is_none(self) -> bool {
        self == Fidelity::NONE
    }
}

// Go: spanmap/spanmap.go:104 Segment
// Segment maps the half-open virtual range [VirtualStart, VirtualEnd) to the half-open original range
// [OriginalStart, OriginalEnd). Features controls language-service participation; diagnostics and exact edit mapping
// deliberately bypass it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Segment {
    pub virtual_start: i32,
    pub virtual_end: i32,
    pub original_start: i32,
    pub original_end: i32,
    pub kind: Kind,
    pub features: Feature,
}

// Go: spanmap/spanmap.go:114 MappedPosition
// MappedPosition is one virtual projection of an original position and its mapping fidelity.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MappedPosition {
    pub position: i32,
    pub fidelity: Fidelity,
}

// Go: spanmap/spanmap.go:120 MappedSpan
// MappedSpan is one virtual projection of an original range and its mapping fidelity.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MappedSpan {
    pub span: TextRange,
    pub fidelity: Fidelity,
}

// Go: spanmap/spanmap.go:128 SpanMap
// SpanMap is a sparse, ordered set of segments over a content mapper's virtual text. Segments do not
// need to cover the whole text: any virtual position not inside a segment is synthesized (it has no
// original counterpart). An empty SpanMap therefore describes fully synthesized virtual text.
// PORT: Go `*SpanMap` is shared by the source files and the language service; callers hold it in an
// `Arc`. Go's `origOnce` and `origSorted` are one `OnceLock`.
#[derive(Debug, Default)]
pub struct SpanMap {
    segments: Vec<Segment>,

    // origOnce guards lazy construction of origSorted, the segments ordered by OriginalStart, used for
    // original-to-virtual lookups.
    orig_sorted: OnceLock<Vec<Segment>>,
}

// Go: spanmap/spanmap.go:140 MappingErrorKind
// Validation failures. A content mapper is required to provide a valid span map; these describe the
// ways a map can be malformed, so the compiler can attribute the failure to the mapper precisely and
// point the mapper's author at the offending location.
go_enum!(MappingErrorKind, i32 {
    // MappingErrorKindOverlap means the segments overlap, run backwards, or extend past the end of the
    // virtual text (they must be ordered and disjoint in virtual space).
    OVERLAP = 0;
    // MappingErrorKindOutOfBounds means a segment's original span lies outside the original text.
    OUT_OF_BOUNDS = 1;
    // MappingErrorKindVerbatimMismatch means a verbatim segment's virtual and original text differ.
    VERBATIM_MISMATCH = 2;
    // MappingErrorKindKind means a segment uses an unsupported mapping kind.
    KIND = 3;
    // MappingErrorKindOriginalOverlap means original spans partially overlap or contain one another.
    ORIGINAL_OVERLAP = 4;
    // MappingErrorKindFeature means a feature annotation contains unsupported flags.
    FEATURE = 5;
});

// Go: spanmap/spanmap.go:161 MappingError
// MappingError describes a single span map validation failure, including the offsets involved so the mapper's
// author can locate it. VirtualPos is an offset into the virtual text; OriginalPos is an offset into the
// original content. Either may be unused (zero) depending on Kind.
// PORT: Go returns `*MappingError` as an `error`; the port wraps the value with `errors::from_value`,
// so `errors::as_type::<MappingError>` finds it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MappingError {
    pub kind: MappingErrorKind,
    pub virtual_pos: i32,
    pub original_pos: i32,
}

impl MappingError {
    // Go: spanmap/spanmap.go:168 MappingError.Error
    // Error describes the invalid mapping and the coordinate at which it was detected.
    #[must_use]
    pub fn error(&self) -> String {
        match self.kind {
            MappingErrorKind::OVERLAP => format!(
                "content mapper position mappings overlap or are out of order near virtual offset {}",
                self.virtual_pos
            ),
            MappingErrorKind::OUT_OF_BOUNDS => format!(
                "content mapper position mapping points outside the original content at original offset {}",
                self.original_pos
            ),
            MappingErrorKind::VERBATIM_MISMATCH => format!(
                "content mapper verbatim mapping does not match the original content at virtual offset {}, original offset {}",
                self.virtual_pos, self.original_pos
            ),
            MappingErrorKind::KIND => format!(
                "content mapper position mapping has an invalid kind at virtual offset {}",
                self.virtual_pos
            ),
            MappingErrorKind::ORIGINAL_OVERLAP => format!(
                "content mapper position mappings partially overlap in the original content near offset {}",
                self.original_pos
            ),
            MappingErrorKind::FEATURE => format!(
                "content mapper position mappings have invalid features near original offset {}",
                self.original_pos
            ),
            _ => "content mapper produced an invalid position mapping".to_string(),
        }
    }
}

impl std::fmt::Display for MappingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.error())
    }
}

impl SpanMap {
    // Go: spanmap/spanmap.go:192 SpanMap.Validate
    // Validate enforces the content-mapper span map contract against the virtual and original text: the
    // segments must be ordered and disjoint in virtual space and stay within the virtual text, every
    // original span must lie within the original text, and every verbatim segment's text must match the
    // original exactly. Gaps are allowed (they map as synthesized) and an empty map is valid. It returns the
    // first violation found, or nil if the map is valid.
    // PORT: `virtual` is a reserved word in Rust, so the parameter is `virtual_`.
    #[must_use]
    pub fn validate(m: Option<&SpanMap>, virtual_: &str, original: &str) -> Option<MappingError> {
        let m = m?;
        let virtual_len = virtual_.len() as i32;
        let orig_len = original.len() as i32;
        let mut previous_virtual_end: i32 = 0;
        for s in &m.segments {
            if s.virtual_start < previous_virtual_end
                || s.virtual_end < s.virtual_start
                || s.virtual_end > virtual_len
            {
                return Some(MappingError {
                    kind: MappingErrorKind::OVERLAP,
                    virtual_pos: s.virtual_start,
                    original_pos: 0,
                });
            }
            previous_virtual_end = s.virtual_end;
            if s.original_start < 0
                || s.original_end < s.original_start
                || s.original_end > orig_len
            {
                return Some(MappingError {
                    kind: MappingErrorKind::OUT_OF_BOUNDS,
                    virtual_pos: s.virtual_start,
                    original_pos: s.original_end,
                });
            }
            if s.kind != Kind::VERBATIM && s.kind != Kind::ATOM && s.kind != Kind::ALIAS {
                return Some(MappingError {
                    kind: MappingErrorKind::KIND,
                    virtual_pos: s.virtual_start,
                    original_pos: s.original_start,
                });
            }
            if s.kind == Kind::VERBATIM {
                // PORT: Go compares string slices; these are byte slices (the offsets are byte offsets
                // and need not fall on character boundaries).
                if s.virtual_end - s.virtual_start != s.original_end - s.original_start
                    || virtual_.as_bytes()[s.virtual_start as usize..s.virtual_end as usize]
                        != original.as_bytes()[s.original_start as usize..s.original_end as usize]
                {
                    return Some(MappingError {
                        kind: MappingErrorKind::VERBATIM_MISMATCH,
                        virtual_pos: s.virtual_start,
                        original_pos: s.original_start,
                    });
                }
            }
            if s.features.without(FEATURE_MASK) != Feature::NONE {
                return Some(MappingError {
                    kind: MappingErrorKind::FEATURE,
                    virtual_pos: s.virtual_start,
                    original_pos: s.original_start,
                });
            }
        }
        let original_segments = m.orig_index();
        let mut i = 0;
        while i < original_segments.len() {
            let mut group_end = i + 1;
            while group_end < original_segments.len()
                && original_segments[group_end].original_start
                    == original_segments[i].original_start
                && original_segments[group_end].original_end == original_segments[i].original_end
            {
                group_end += 1;
            }
            if i > 0 && original_segments[i].original_start < original_segments[i - 1].original_end
            {
                return Some(MappingError {
                    kind: MappingErrorKind::ORIGINAL_OVERLAP,
                    virtual_pos: original_segments[i].virtual_start,
                    original_pos: original_segments[i].original_start,
                });
            }
            i = group_end;
        }
        None
    }

    // Go: spanmap/spanmap.go:246 SpanMap.Segments
    // Segments returns the map's segments ordered by virtual start.
    #[must_use]
    pub fn segments(m: Option<&SpanMap>) -> Vec<Segment> {
        match m {
            None => Vec::new(),
            Some(m) => m.segments.clone(),
        }
    }

    // Go: spanmap/spanmap.go:256 SpanMap.VirtualToOriginalSpan
    // VirtualToOriginalSpan maps a virtual range to an original range, along with the fidelity of the result. A virtual
    // range that lies entirely in a gap between segments (or in an empty map) is synthesized: it maps to the
    // insertion point in the original with FidelityNone. A nil SpanMap maps identically.
    #[must_use]
    pub fn virtual_to_original_span(m: Option<&SpanMap>, r: TextRange) -> (TextRange, Fidelity) {
        let Some(m) = m else {
            return (r, Fidelity::EXACT);
        };
        let virtual_start = r.pos();
        let virtual_end = r.end().max(virtual_start);

        let (start_idx, start_in) = m.segment_index_at(virtual_start);
        let mut end_probe = virtual_end;
        if virtual_end > virtual_start {
            end_probe = virtual_end - 1;
        }
        let (end_idx, end_in) = m.segment_index_at(end_probe);

        if start_idx == end_idx && start_in == end_in {
            if start_in {
                let seg = &m.segments[start_idx as usize];
                if seg.kind == Kind::VERBATIM {
                    let orig_start = clamp(
                        seg.original_start + (virtual_start - seg.virtual_start),
                        seg.original_start,
                        seg.original_end,
                    );
                    let orig_end = clamp(
                        seg.original_start + (virtual_end - seg.virtual_start),
                        orig_start,
                        seg.original_end,
                    );
                    return (TextRange::new(orig_start, orig_end), Fidelity::EXACT);
                }
                return (
                    TextRange::new(seg.original_start, seg.original_end),
                    Fidelity::ATOM,
                );
            }
            // Entirely within a single synthesized gap.
            let pos = m.insertion_point(start_idx);
            return (TextRange::new(pos, pos), Fidelity::NONE);
        }

        let orig_start = m.map_low(virtual_start, start_idx, start_in);
        let orig_end = m.map_high(virtual_end, end_idx, end_in).max(orig_start);
        (TextRange::new(orig_start, orig_end), Fidelity::APPROXIMATE)
    }

    // Go: spanmap/spanmap.go:293 SpanMap.VirtualToOriginalSpanForFeature
    // VirtualToOriginalSpanForFeature maps r only when every virtual position in the non-empty range is
    // covered by contiguous segments participating in feature. A zero-length range requires its containing
    // segment to participate. Diagnostics and edit write-back intentionally use VirtualToOriginalSpan instead.
    #[must_use]
    pub fn virtual_to_original_span_for_feature(
        m: Option<&SpanMap>,
        r: TextRange,
        feature: Feature,
    ) -> (TextRange, Fidelity) {
        let (mapped, fidelity) = SpanMap::virtual_to_original_span(m, r);
        match m {
            None => (mapped, fidelity),
            Some(m) if m.virtual_span_supports_feature(r, feature) => (mapped, fidelity),
            Some(_) => (mapped, Fidelity::NONE),
        }
    }

    // Go: spanmap/spanmap.go:301 SpanMap.virtualSpanSupportsFeature
    fn virtual_span_supports_feature(&self, r: TextRange, feature: Feature) -> bool {
        let start = r.pos();
        let end = r.end().max(start);
        if start == end {
            let (index, inside) = self.segment_index_at(start);
            return inside && supports_feature(self.segments[index as usize], feature);
        }
        let (index, inside) = self.segment_index_at(start);
        if !inside {
            return false;
        }
        let mut index = index as usize;
        let mut covered_through = start;
        while index < self.segments.len() && covered_through < end {
            let segment = self.segments[index];
            if segment.virtual_start > covered_through
                || segment.virtual_end <= covered_through
                || !supports_feature(segment, feature)
            {
                return false;
            }
            covered_through = segment.virtual_end;
            index += 1;
        }
        covered_through >= end
    }

    // Go: spanmap/spanmap.go:327 SpanMap.VirtualToOriginalPosition
    // VirtualToOriginalPosition maps a single virtual position to the corresponding original position, along with the
    // fidelity of the result. It is the single-position analog of VirtualToOriginalSpan: a position in a gap (or in an empty
    // map) is synthesized and maps to the insertion point with FidelityNone. A nil SpanMap maps identically.
    #[must_use]
    pub fn virtual_to_original_position(m: Option<&SpanMap>, pos: i32) -> (i32, Fidelity) {
        let Some(m) = m else {
            return (pos, Fidelity::EXACT);
        };
        let (idx, in_) = m.segment_index_at(pos);
        if !in_ {
            return (m.insertion_point(idx), Fidelity::NONE);
        }
        let seg = &m.segments[idx as usize];
        if seg.kind == Kind::VERBATIM {
            return (
                clamp(
                    seg.original_start + (pos - seg.virtual_start),
                    seg.original_start,
                    seg.original_end,
                ),
                Fidelity::EXACT,
            );
        }
        (seg.original_start, Fidelity::ATOM)
    }

    // Go: spanmap/spanmap.go:344 SpanMap.VirtualToOriginalPositionForFeature
    // VirtualToOriginalPositionForFeature maps pos only when its virtual segment participates in feature.
    // Diagnostics and edit write-back intentionally use VirtualToOriginalPosition instead.
    #[must_use]
    pub fn virtual_to_original_position_for_feature(
        m: Option<&SpanMap>,
        pos: i32,
        feature: Feature,
    ) -> (i32, Fidelity) {
        let (mapped, fidelity) = SpanMap::virtual_to_original_position(m, pos);
        let Some(m) = m else {
            return (mapped, fidelity);
        };
        let (index, inside) = m.segment_index_at(pos);
        if !inside || !supports_feature(m.segments[index as usize], feature) {
            return (mapped, Fidelity::NONE);
        }
        (mapped, fidelity)
    }

    // Go: spanmap/spanmap.go:358 SpanMap.AliasForVirtualSpan
    // AliasForVirtualSpan returns the alias segment exactly covering r. Partial overlap does not qualify:
    // diagnostic text may be substituted only when the diagnostic identifies the complete virtual alias.
    #[must_use]
    pub fn alias_for_virtual_span(m: Option<&SpanMap>, r: TextRange) -> (Segment, bool) {
        let Some(m) = m else {
            return (Segment::default(), false);
        };
        let (index, inside) = m.segment_index_at(r.pos());
        if !inside {
            return (Segment::default(), false);
        }
        let segment = m.segments[index as usize];
        (
            segment,
            segment.kind == Kind::ALIAS
                && r.pos() == segment.virtual_start
                && r.end() == segment.virtual_end,
        )
    }

    // Go: spanmap/spanmap.go:372 SpanMap.segmentIndexAt
    // segmentIndexAt returns the index of the segment containing pos and true, or, when pos lies in a gap,
    // the index of the segment immediately before pos (-1 if none) and false.
    // PORT: Go returns an `int` that can be -1; here an `isize`.
    fn segment_index_at(&self, pos: i32) -> (isize, bool) {
        let (idx, found) = binary_search_func(&self.segments, pos, |s: &Segment, p: &i32| {
            s.virtual_start.wrapping_sub(*p)
        });
        if found {
            return (idx as isize, true);
        }
        let prev = idx as isize - 1;
        if prev >= 0 && pos < self.segments[prev as usize].virtual_end {
            return (prev, true);
        }
        (prev, false)
    }

    // Go: spanmap/spanmap.go:388 SpanMap.insertionPoint
    // insertionPoint returns the original offset where synthesized content following segment prev sits: the
    // original end of that segment, or 0 before the first segment.
    fn insertion_point(&self, prev: isize) -> i32 {
        if prev < 0 {
            return 0;
        }
        self.segments[prev as usize].original_end
    }

    // Go: spanmap/spanmap.go:397 SpanMap.mapLow
    // mapLow maps a virtual lower range boundary to original coordinates. A boundary in a synthesized
    // gap uses that gap's insertion point; an atom uses its original start.
    fn map_low(&self, pos: i32, idx: isize, in_: bool) -> i32 {
        if !in_ {
            return self.insertion_point(idx);
        }
        let seg = &self.segments[idx as usize];
        if seg.kind == Kind::VERBATIM {
            return clamp(
                seg.original_start + (pos - seg.virtual_start),
                seg.original_start,
                seg.original_end,
            );
        }
        seg.original_start
    }

    // Go: spanmap/spanmap.go:410 SpanMap.mapHigh
    // mapHigh maps a virtual upper range boundary to original coordinates. A boundary in a synthesized
    // gap uses that gap's insertion point; an atom uses its original end.
    fn map_high(&self, pos: i32, idx: isize, in_: bool) -> i32 {
        if !in_ {
            return self.insertion_point(idx);
        }
        let seg = &self.segments[idx as usize];
        if seg.kind == Kind::VERBATIM {
            return clamp(
                seg.original_start + (pos - seg.virtual_start),
                seg.original_start,
                seg.original_end,
            );
        }
        seg.original_end
    }

    // Go: spanmap/spanmap.go:425 SpanMap.OriginalToVirtualPositions
    // OriginalToVirtualPositions returns every virtual projection of an original position whose segment
    // participates in feature. Segment ends are inclusive for point mapping, so a position shared by adjacent
    // original spans returns projections from both sides. Results are ordered by virtual position. It returns
    // no results for an uncovered position or when all touching segments reject feature. A nil SpanMap maps identically.
    #[must_use]
    pub fn original_to_virtual_positions(
        m: Option<&SpanMap>,
        pos: i32,
        feature: Feature,
    ) -> Vec<MappedPosition> {
        let Some(m) = m else {
            return vec![MappedPosition {
                position: pos,
                fidelity: Fidelity::EXACT,
            }];
        };
        let groups = segment_groups_at_original_position(m.orig_index(), pos);
        if groups.is_empty() {
            return Vec::new();
        }
        let mut results: Vec<MappedPosition> = Vec::new();
        for group in &groups {
            for segment in group.segments {
                if !supports_feature(*segment, feature) {
                    continue;
                }
                let mut mapped = MappedPosition {
                    position: 0,
                    fidelity: Fidelity::ATOM,
                };
                if segment.kind == Kind::VERBATIM {
                    mapped.position = clamp(
                        segment.virtual_start + (pos - segment.original_start),
                        segment.virtual_start,
                        segment.virtual_end,
                    );
                    mapped.fidelity = Fidelity::EXACT;
                } else if group.at_end {
                    mapped.position = segment.virtual_end;
                } else {
                    mapped.position = segment.virtual_start;
                }
                if !results.contains(&mapped) {
                    results.push(mapped);
                }
            }
        }
        sort_func(&mut results, |a: &MappedPosition, b: &MappedPosition| {
            a.position.wrapping_sub(b.position)
        });
        results
    }

    // Go: spanmap/spanmap.go:476 SpanMap.OriginalToVirtualSpans
    // OriginalToVirtualSpans returns every feature-compatible virtual projection of an original range.
    // A range contained by one duplicate group produces one exact or atom result per matching group member.
    //
    // A range that starts in one group and ends in another can have several possible virtual ranges. For
    // example, suppose two original segments are each copied twice into the virtual text:
    //
    //	original:   [ A ][ B ]
    //	               [---)       range from inside A to inside B
    //
    //	virtual:    [ A ][ B ]      [ A ][ B ]
    //	               ^   ^          ^   ^
    //	             start end      start end
    //	               1   3          11  13
    //
    // The map says that the range may start at 1 or 11 and end at 3 or 13, but it does not say which copy of A
    // belongs with which copy of B. We choose the smallest range around each possible location, producing [1,3)
    // and [11,13). We do not return [1,13), because it contains both smaller candidates and would include code
    // that may be unrelated to the original range. These cross-group results have approximate fidelity.
    // If either boundary is uncovered or disabled for feature, there are no results. A nil SpanMap maps identically.
    #[must_use]
    pub fn original_to_virtual_spans(
        m: Option<&SpanMap>,
        r: TextRange,
        feature: Feature,
    ) -> Vec<MappedSpan> {
        let Some(m) = m else {
            return vec![MappedSpan {
                span: r,
                fidelity: Fidelity::EXACT,
            }];
        };
        let start = r.pos();
        let end = r.end().max(start);
        let mut last_character = end;
        if end > start {
            last_character -= 1;
        }
        let original_segments = m.orig_index();
        let (start_segments, start_inside) =
            segments_at_original_position(original_segments, start);
        let (end_segments, end_inside) =
            segments_at_original_position(original_segments, last_character);
        if !start_inside || !end_inside {
            return Vec::new();
        }
        if same_original_range(start_segments[0], end_segments[0]) {
            return original_to_virtual_spans_in_group(start_segments, start, end, feature);
        }
        let starts = original_start_projections(start_segments, start, feature);
        let ends = original_end_projections(end_segments, end, feature);
        if starts.is_empty() || ends.is_empty() {
            return Vec::new();
        }
        let mut results: Vec<MappedSpan> = Vec::with_capacity(starts.len().min(ends.len()));
        for (i, &virtual_start) in starts.iter().enumerate() {
            // Go `slices.BinarySearch(ends, virtualStart)`.
            let (end_index, _) = binary_search_func(&ends, virtual_start, |e: &i32, t: &i32| {
                if e < t {
                    -1
                } else if e > t {
                    1
                } else {
                    0
                }
            });
            if end_index == ends.len() || i + 1 < starts.len() && starts[i + 1] <= ends[end_index] {
                continue;
            }
            results.push(MappedSpan {
                span: TextRange::new(virtual_start, ends[end_index]),
                fidelity: Fidelity::APPROXIMATE,
            });
        }
        results
    }

    // Go: spanmap/spanmap.go:516 SpanMap.OriginalToVirtualIntersectingSpans
    // OriginalToVirtualIntersectingSpans maps every feature-enabled segment intersection with r.
    // Unlike OriginalToVirtualSpans, uncovered range endpoints do not suppress covered interior segments.
    #[must_use]
    pub fn original_to_virtual_intersecting_spans(
        m: Option<&SpanMap>,
        r: TextRange,
        feature: Feature,
    ) -> Vec<MappedSpan> {
        let Some(m) = m else {
            return vec![MappedSpan {
                span: r,
                fidelity: Fidelity::EXACT,
            }];
        };
        if r.pos() == r.end() {
            return SpanMap::original_to_virtual_spans(Some(m), r, feature);
        }
        let mut results: Vec<MappedSpan> = Vec::new();
        for segment in &m.segments {
            if !supports_feature(*segment, feature) {
                continue;
            }
            let start = r.pos().max(segment.original_start);
            let end = r.end().min(segment.original_end);
            if start >= end {
                continue;
            }
            if segment.kind == Kind::VERBATIM {
                results.push(MappedSpan {
                    span: TextRange::new(
                        segment.virtual_start + (start - segment.original_start),
                        segment.virtual_start + (end - segment.original_start),
                    ),
                    fidelity: Fidelity::EXACT,
                });
            } else {
                results.push(MappedSpan {
                    span: TextRange::new(segment.virtual_start, segment.virtual_end),
                    fidelity: Fidelity::ATOM,
                });
            }
        }
        results
    }

    // Go: spanmap/spanmap.go:629 SpanMap.origIndex
    // origIndex returns the segments ordered by OriginalStart, building it once on first use.
    fn orig_index(&self) -> &[Segment] {
        self.orig_sorted.get_or_init(|| {
            let mut orig_sorted = self.segments.clone();
            sort_func(&mut orig_sorted, |a: &Segment, b: &Segment| {
                let c = a.original_start.wrapping_sub(b.original_start);
                if c != 0 {
                    return c;
                }
                let c = a.original_end.wrapping_sub(b.original_end);
                if c != 0 {
                    return c;
                }
                a.virtual_start.wrapping_sub(b.virtual_start)
            });
            orig_sorted
        })
    }

    // Go: spanmap/spanmap.go:763 SpanMap.Marshal
    // Marshal encodes a SpanMap into the JSON tuple form. FeatureAll uses the backward-compatible five-element
    // tuple; every other feature mask is emitted as a sixth element.
    pub fn marshal(&self) -> Result<Vec<u8>, GoError> {
        let mut tuples: Vec<Vec<i32>> = Vec::with_capacity(self.segments.len());
        for s in &self.segments {
            let mut tuple = vec![
                s.virtual_start,
                s.virtual_end.wrapping_sub(s.virtual_start),
                s.original_start,
                s.original_end.wrapping_sub(s.original_start),
                s.kind.0,
            ];
            if s.features != Feature::ALL {
                tuple.push(s.features.0);
            }
            tuples.push(tuple);
        }
        json_marshal(&tuples, &[])
            .map(String::into_bytes)
            .map_err(errors::from_value)
    }
}

// Go: spanmap/spanmap.go:237 New
// New builds a SpanMap from segments, sorted by virtual start. Segments describe only the parts of the
// virtual text that correspond to the original; anything not covered maps as synthesized.
#[must_use]
pub fn new(segments: &[Segment]) -> SpanMap {
    let mut sorted = segments.to_vec();
    sort_func(&mut sorted, |a: &Segment, b: &Segment| {
        a.virtual_start.wrapping_sub(b.virtual_start)
    });
    SpanMap {
        segments: sorted,
        orig_sorted: OnceLock::new(),
    }
}

// Go: spanmap/spanmap.go:562 originalStartProjections
// originalStartProjections maps the inclusive start of an original range through every matching segment.
// Verbatim segments preserve the offset within the segment; atoms map to their virtual start.
//
// For duplicate verbatim segments, the start keeps the same relative offset in every copy:
//
//	original:       [---------)
//	                   ^ start
//
//	virtual:    [---------)   [---------)
//	               ^             ^
//	             result        result
fn original_start_projections(segments: &[Segment], start: i32, feature: Feature) -> Vec<i32> {
    let mut results: Vec<i32> = Vec::with_capacity(segments.len());
    for segment in segments {
        if !supports_feature(*segment, feature) {
            continue;
        }
        if segment.kind == Kind::VERBATIM {
            results.push(clamp(
                segment.virtual_start + (start - segment.original_start),
                segment.virtual_start,
                segment.virtual_end,
            ));
        } else {
            results.push(segment.virtual_start);
        }
    }
    results
}

// Go: spanmap/spanmap.go:590 originalEndProjections
// originalEndProjections maps the exclusive end of an original range through every matching segment.
// The caller uses end-1 to find the segment containing the final character, while this helper maps the end
// boundary itself. Verbatim segments preserve that boundary; atoms map to their virtual end.
//
// The lookup uses end-1 so an end at a segment boundary selects the segment on its left, not the next one:
//
//	original:       [---------)[ next segment )
//	                         ^`-- end
//	                         `--- end-1
//
//	virtual:    [---------)   [---------)
//	                      ^             ^
//	                    result        result
fn original_end_projections(segments: &[Segment], end: i32, feature: Feature) -> Vec<i32> {
    let mut results: Vec<i32> = Vec::with_capacity(segments.len());
    for segment in segments {
        if !supports_feature(*segment, feature) {
            continue;
        }
        if segment.kind == Kind::VERBATIM {
            results.push(clamp(
                segment.virtual_start + (end - segment.original_start),
                segment.virtual_start,
                segment.virtual_end,
            ));
        } else {
            results.push(segment.virtual_end);
        }
    }
    results
}

// Go: spanmap/spanmap.go:606 originalToVirtualSpansInGroup
// originalToVirtualSpansInGroup maps a range whose boundaries are known to lie in segments.
fn original_to_virtual_spans_in_group(
    segments: &[Segment],
    start: i32,
    end: i32,
    feature: Feature,
) -> Vec<MappedSpan> {
    let mut results: Vec<MappedSpan> = Vec::with_capacity(segments.len());
    for segment in segments {
        if !supports_feature(*segment, feature) {
            continue;
        }
        if segment.kind == Kind::VERBATIM {
            let virtual_start = clamp(
                segment.virtual_start + (start - segment.original_start),
                segment.virtual_start,
                segment.virtual_end,
            );
            let virtual_end = clamp(
                segment.virtual_start + (end - segment.original_start),
                virtual_start,
                segment.virtual_end,
            );
            results.push(MappedSpan {
                span: TextRange::new(virtual_start, virtual_end),
                fidelity: Fidelity::EXACT,
            });
        } else {
            results.push(MappedSpan {
                span: TextRange::new(segment.virtual_start, segment.virtual_end),
                fidelity: Fidelity::ATOM,
            });
        }
    }
    results
}

// Go: spanmap/spanmap.go:624 sameOriginalRange
// sameOriginalRange reports whether two segments belong to the same duplicate group.
fn same_original_range(left: Segment, right: Segment) -> bool {
    left.original_start == right.original_start && left.original_end == right.original_end
}

// Go: spanmap/spanmap.go:650 segmentsAtOriginalPosition
// segmentsAtOriginalPosition returns the complete duplicate group of mapping segments containing the
// original-text position pos. segments must be ordered by original start, original end, and virtual start.
// Segment ends are exclusive; a segment start, including a zero-length segment, is considered contained.
// It finds a candidate in O(log n), then scans only the duplicate group. The boolean reports whether any
// group contains pos.
fn segments_at_original_position(segments: &[Segment], pos: i32) -> (&[Segment], bool) {
    let (index, found) = binary_search_func(segments, pos, |segment: &Segment, position: &i32| {
        segment.original_start.wrapping_sub(*position)
    });
    let mut index = index as isize;
    if !found {
        index -= 1;
    }
    if index < 0
        || !(segments[index as usize].original_start == pos
            || pos < segments[index as usize].original_end)
    {
        return (&[], false);
    }
    let index = index as usize;
    let mut start = index;
    while start > 0 && same_original_range(segments[start - 1], segments[index]) {
        start -= 1;
    }
    let mut end = start + 1;
    while end < segments.len() && same_original_range(segments[end], segments[start]) {
        end += 1;
    }
    (&segments[start..end], true)
}

// Go: spanmap/spanmap.go:671 segmentGroupAtOriginalPosition
struct SegmentGroupAtOriginalPosition<'a> {
    segments: &'a [Segment],
    at_end: bool,
}

// Go: spanmap/spanmap.go:689 segmentGroupsAtOriginalPosition
// segmentGroupsAtOriginalPosition returns groups of mapping segments containing or touching the original-text
// position pos. Interior positions return one group. At a boundary between adjacent groups, both the group ending
// at pos and the group starting at pos are returned. segments must be ordered by original start, original end,
// then virtual start.
//
// At a shared boundary, segments ending at pos and segments starting there form separate groups:
//
//	original:  [--- A ---)[--- B ---)
//	                      ^ pos
//
//	virtual:   [ A1 ) [ A2 )    [ B1 ) [ B2 )
//	             left group       right group
//	             atEnd: true      atEnd: false
fn segment_groups_at_original_position(
    segments: &[Segment],
    pos: i32,
) -> Vec<SegmentGroupAtOriginalPosition<'_>> {
    let (index, starts_at_position) =
        binary_search_func(segments, pos, |segment: &Segment, position: &i32| {
            segment.original_start.wrapping_sub(*position)
        });
    if starts_at_position {
        let (right, _) = segments_at_original_position(segments, pos);
        let mut groups: Vec<SegmentGroupAtOriginalPosition<'_>> = Vec::new();
        if index > 0 {
            let left_index = index - 1;
            if segments[left_index].original_end == pos {
                let mut left_start = left_index;
                while left_start > 0
                    && same_original_range(segments[left_start - 1], segments[left_index])
                {
                    left_start -= 1;
                }
                groups.push(SegmentGroupAtOriginalPosition {
                    segments: &segments[left_start..index],
                    at_end: true,
                });
            }
        }
        groups.push(SegmentGroupAtOriginalPosition {
            segments: right,
            at_end: false,
        });
        return groups;
    }
    if index == 0 {
        return Vec::new();
    }
    let left_index = index - 1;
    let segment = segments[left_index];
    if pos > segment.original_end {
        return Vec::new();
    }
    let mut start = left_index;
    while start > 0 && same_original_range(segments[start - 1], segment) {
        start -= 1;
    }
    vec![SegmentGroupAtOriginalPosition {
        segments: &segments[start..index],
        at_end: pos == segment.original_end,
    }]
}

// Go: spanmap/spanmap.go:724 supportsFeature
// supportsFeature reports whether segment participates in feature.
fn supports_feature(segment: Segment, feature: Feature) -> bool {
    segment.features.intersects(feature)
}

// Go: spanmap/spanmap.go:729 clamp
// clamp confines v to the inclusive interval [lo, hi].
fn clamp(v: i32, lo: i32, hi: i32) -> i32 {
    lo.max(v.min(hi))
}

// Go: spanmap/spanmap.go:736 Unmarshal
// Unmarshal decodes a SpanMap from the JSON tuple form produced by an out-of-process content mapper.
// Five-element tuples omit features and are normalized to FeatureAll; six-element tuples preserve the
// explicit feature mask, including FeatureNone.
pub fn unmarshal(data: &[u8]) -> Result<SpanMap, GoError> {
    let mut tuples: Vec<Vec<i32>> = Vec::new();
    json_unmarshal(data, &mut tuples, &[]).map_err(errors::from_value)?;
    let mut segments: Vec<Segment> = vec![Segment::default(); tuples.len()];
    for (i, t) in tuples.iter().enumerate() {
        if t.len() != 5 && t.len() != 6 {
            return Err(errors::new(format!(
                "span map segment {i}: expected 5 or 6 values, got {}",
                t.len()
            )));
        }
        segments[i] = Segment {
            virtual_start: t[0],
            virtual_end: t[0].wrapping_add(t[1]),
            original_start: t[2],
            original_end: t[2].wrapping_add(t[3]),
            kind: Kind(t[4]),
            features: Feature::ALL,
        };
        if t.len() == 6 {
            segments[i].features = Feature(t[5]);
        }
    }
    Ok(new(&segments))
}

#[cfg(test)]
mod tests {
    // Go: spanmap/spanmap_test.go
    use super::*;

    fn seg(
        virtual_start: i32,
        virtual_end: i32,
        original_start: i32,
        original_end: i32,
        kind: Kind,
        features: Feature,
    ) -> Segment {
        Segment {
            virtual_start,
            virtual_end,
            original_start,
            original_end,
            kind,
            features,
        }
    }

    // Go: spanmap_test.go:11 TestVirtualToOriginalSpanVerbatim
    #[test]
    fn test_virtual_to_original_span_verbatim() {
        // Virtual [0,10) is a verbatim copy of original [100,110).
        let m = new(&[seg(0, 10, 100, 110, Kind::VERBATIM, Feature::ALL)]);

        let (got, fidelity) = SpanMap::virtual_to_original_span(Some(&m), TextRange::new(3, 7));
        assert_eq!(got.pos(), 103);
        assert_eq!(got.end(), 107);
        assert_eq!(fidelity, Fidelity::EXACT);
    }

    // Go: spanmap_test.go:25 TestVirtualToOriginalSpanAtom
    #[test]
    fn test_virtual_to_original_span_atom() {
        // Virtual [0,3) is a synthesized gap; [3,14) ("MyComponent") is an atom of the original [60,71).
        let m = new(&[seg(3, 14, 60, 71, Kind::ATOM, Feature::ALL)]);

        // A span inside the atom maps to the whole atom span.
        let (got, fidelity) = SpanMap::virtual_to_original_span(Some(&m), TextRange::new(5, 9));
        assert_eq!(got.pos(), 60);
        assert_eq!(got.end(), 71);
        assert_eq!(fidelity, Fidelity::ATOM);
    }

    // Go: spanmap_test.go:40 TestVirtualAlias
    #[test]
    fn test_virtual_alias() {
        let m = new(&[seg(3, 6, 10, 11, Kind::ALIAS, Feature::ALL)]);

        let (got, fidelity) = SpanMap::virtual_to_original_span(Some(&m), TextRange::new(3, 6));
        assert_eq!(got, TextRange::new(10, 11));
        assert_eq!(fidelity, Fidelity::ATOM);
        let (alias, ok) = SpanMap::alias_for_virtual_span(Some(&m), TextRange::new(3, 6));
        assert!(ok);
        assert_eq!(alias.kind, Kind::ALIAS);
        let (_, partial) = SpanMap::alias_for_virtual_span(Some(&m), TextRange::new(4, 6));
        assert!(!partial);

        let data = m.marshal().expect("marshal");
        let decoded = unmarshal(&data).expect("unmarshal");
        assert_eq!(SpanMap::segments(Some(&decoded))[0].kind, Kind::ALIAS);
    }

    // Go: spanmap_test.go:63 TestVirtualToOriginalSpanSynthesizedGap
    #[test]
    fn test_virtual_to_original_span_synthesized_gap() {
        // A gap between two verbatim segments is synthesized: it maps to the insertion point (the preceding
        // segment's original end) with no fidelity.
        let m = new(&[
            seg(0, 10, 100, 110, Kind::VERBATIM, Feature::ALL),
            seg(20, 30, 200, 210, Kind::VERBATIM, Feature::ALL),
        ]);

        let (got, fidelity) = SpanMap::virtual_to_original_span(Some(&m), TextRange::new(12, 15));
        assert_eq!(got.pos(), 110);
        assert_eq!(got.end(), 110);
        assert_eq!(fidelity, Fidelity::NONE);
    }

    // Go: spanmap_test.go:79 TestOriginalToVirtualIntersectingSpansAllowsUncoveredEndpoints
    #[test]
    fn test_original_to_virtual_intersecting_spans_allows_uncovered_endpoints() {
        let m = new(&[seg(
            10,
            20,
            100,
            110,
            Kind::VERBATIM,
            Feature::SEMANTIC_TOKENS | Feature::INLAY_HINTS,
        )]);

        for feature in [Feature::SEMANTIC_TOKENS, Feature::INLAY_HINTS] {
            let got = SpanMap::original_to_virtual_intersecting_spans(
                Some(&m),
                TextRange::new(90, 120),
                feature,
            );
            assert_eq!(got.len(), 1);
            assert_eq!(got[0].span, TextRange::new(10, 20));
            assert_eq!(got[0].fidelity, Fidelity::EXACT);
        }
    }

    // Go: spanmap_test.go:95 TestVirtualToOriginalSpanEmptyIsSynthesized
    #[test]
    fn test_virtual_to_original_span_empty_is_synthesized() {
        // An empty map describes fully synthesized output: everything maps to the start with no fidelity.
        let m = new(&[]);
        let (got, fidelity) = SpanMap::virtual_to_original_span(Some(&m), TextRange::new(5, 10));
        assert_eq!(got.pos(), 0);
        assert_eq!(got.end(), 0);
        assert_eq!(fidelity, Fidelity::NONE);
    }

    // Go: spanmap_test.go:106 TestVirtualToOriginalSpanCrossingSegments
    #[test]
    fn test_virtual_to_original_span_crossing_segments() {
        let m = new(&[
            seg(0, 10, 100, 110, Kind::VERBATIM, Feature::NONE),
            seg(10, 20, 200, 210, Kind::VERBATIM, Feature::NONE),
        ]);

        let (got, fidelity) = SpanMap::virtual_to_original_span(Some(&m), TextRange::new(5, 15));
        assert_eq!(got.pos(), 105);
        assert_eq!(got.end(), 205);
        assert_eq!(fidelity, Fidelity::APPROXIMATE);
    }

    // Go: spanmap_test.go:120 TestVirtualToOriginalSpanNilIdentity
    #[test]
    fn test_virtual_to_original_span_nil_identity() {
        let (got, fidelity) = SpanMap::virtual_to_original_span(None, TextRange::new(3, 7));
        assert_eq!(got.pos(), 3);
        assert_eq!(got.end(), 7);
        assert_eq!(fidelity, Fidelity::EXACT);
    }

    // Go: spanmap_test.go:130 TestVirtualToOriginalPosition
    #[test]
    fn test_virtual_to_original_position() {
        // Virtual [0,10) is a verbatim copy of original [100,110); [10,20) is an atom of original [200,210).
        let m = new(&[
            seg(0, 10, 100, 110, Kind::VERBATIM, Feature::ALL),
            seg(20, 30, 200, 210, Kind::ATOM, Feature::ALL),
        ]);

        let test_cases: [(&str, i32, i32, Fidelity); 3] = [
            ("verbatim interpolates", 3, 103, Fidelity::EXACT),
            ("atom maps to its start", 25, 200, Fidelity::ATOM),
            ("gap maps to insertion point", 15, 110, Fidelity::NONE),
        ];
        for (name, pos, want, want_fidelity) in test_cases {
            let (got, fidelity) = SpanMap::virtual_to_original_position(Some(&m), pos);
            assert_eq!(got, want, "{name}");
            assert_eq!(fidelity, want_fidelity, "{name}");
            // VirtualToOriginalPosition must agree with VirtualToOriginalSpan on a zero-length range.
            let (span, span_fidelity) =
                SpanMap::virtual_to_original_span(Some(&m), TextRange::new(pos, pos));
            assert_eq!(got, span.pos(), "{name}");
            assert_eq!(fidelity, span_fidelity, "{name}");
        }
    }

    // Go: spanmap_test.go:163 TestMapPositionNilIdentity
    #[test]
    fn test_map_position_nil_identity() {
        let (got, fidelity) = SpanMap::virtual_to_original_position(None, 7);
        assert_eq!(got, 7);
        assert_eq!(fidelity, Fidelity::EXACT);
    }

    // Go: spanmap_test.go:172 TestOriginalToVirtualSpanVerbatim
    #[test]
    fn test_original_to_virtual_span_verbatim() {
        // Virtual [0,10) is a verbatim copy of original [100,110).
        let m = new(&[seg(0, 10, 100, 110, Kind::VERBATIM, Feature::ALL)]);

        let results =
            SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(103, 107), Feature::ALL);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].span.pos(), 3);
        assert_eq!(results[0].span.end(), 7);
        assert_eq!(results[0].fidelity, Fidelity::EXACT);
    }

    // Go: spanmap_test.go:187 TestOriginalToVirtualSpanAtom
    #[test]
    fn test_original_to_virtual_span_atom() {
        // Virtual [3,14) is an atom of the original [60,71).
        let m = new(&[seg(3, 14, 60, 71, Kind::ATOM, Feature::ALL)]);

        // A span inside the original atom maps to the whole virtual span.
        let results =
            SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(63, 67), Feature::ALL);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].span.pos(), 3);
        assert_eq!(results[0].span.end(), 14);
        assert_eq!(results[0].fidelity, Fidelity::ATOM);
    }

    // Go: spanmap_test.go:203 TestOriginalToVirtualSpanGap
    #[test]
    fn test_original_to_virtual_span_gap() {
        // An original range with no covering segment has no virtual counterpart.
        let m = new(&[
            seg(0, 10, 100, 110, Kind::VERBATIM, Feature::ALL),
            seg(20, 30, 200, 210, Kind::VERBATIM, Feature::ALL),
        ]);

        assert_eq!(
            SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(150, 160), Feature::ALL)
                .len(),
            0
        );
    }

    // Go: spanmap_test.go:215 TestOriginalToVirtualSpanNilIdentity
    #[test]
    fn test_original_to_virtual_span_nil_identity() {
        let results = SpanMap::original_to_virtual_spans(None, TextRange::new(3, 7), Feature::ALL);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].span.pos(), 3);
        assert_eq!(results[0].span.end(), 7);
        assert_eq!(results[0].fidelity, Fidelity::EXACT);
    }

    // Go: spanmap_test.go:226 TestOriginalToVirtualPositions
    #[test]
    fn test_original_to_virtual_positions() {
        // Original [100,110) is a verbatim copy of virtual [0,10); [200,210) is an atom of virtual [20,30).
        let m = new(&[
            seg(0, 10, 100, 110, Kind::VERBATIM, Feature::ALL),
            seg(20, 30, 200, 210, Kind::ATOM, Feature::ALL),
        ]);

        let test_cases: [(&str, i32, i32, Fidelity); 3] = [
            ("verbatim interpolates", 103, 3, Fidelity::EXACT),
            ("atom maps to its start", 205, 20, Fidelity::ATOM),
            ("gap has no projection", 150, 0, Fidelity::NONE),
        ];
        for (name, pos, want, want_fidelity) in test_cases {
            let positions = SpanMap::original_to_virtual_positions(Some(&m), pos, Feature::ALL);
            let spans = SpanMap::original_to_virtual_spans(
                Some(&m),
                TextRange::new(pos, pos),
                Feature::ALL,
            );
            if want_fidelity.is_none() {
                assert_eq!(positions.len(), 0, "{name}");
                assert_eq!(spans.len(), 0, "{name}");
                continue;
            }
            assert_eq!(positions.len(), 1, "{name}");
            assert_eq!(positions[0].position, want, "{name}");
            assert_eq!(positions[0].fidelity, want_fidelity, "{name}");
            assert_eq!(spans.len(), 1, "{name}");
            assert_eq!(spans[0].span.pos(), want, "{name}");
            assert_eq!(spans[0].fidelity, want_fidelity, "{name}");
        }
    }

    // Go: spanmap_test.go:265 TestOriginalToVirtualPositionsAtEndpoint
    #[test]
    fn test_original_to_virtual_positions_at_endpoint() {
        let m = new(&[
            seg(2, 5, 10, 13, Kind::VERBATIM, Feature::COMPLETION),
            seg(8, 11, 13, 16, Kind::VERBATIM, Feature::COMPLETION),
            seg(20, 23, 30, 35, Kind::ATOM, Feature::COMPLETION),
        ]);

        assert_eq!(
            SpanMap::original_to_virtual_positions(Some(&m), 13, Feature::COMPLETION),
            vec![
                MappedPosition {
                    position: 5,
                    fidelity: Fidelity::EXACT
                },
                MappedPosition {
                    position: 8,
                    fidelity: Fidelity::EXACT
                },
            ]
        );
        assert_eq!(
            SpanMap::original_to_virtual_positions(Some(&m), 35, Feature::COMPLETION),
            vec![MappedPosition {
                position: 23,
                fidelity: Fidelity::ATOM
            }]
        );

        let filtered = new(&[
            seg(20, 23, 10, 13, Kind::VERBATIM, Feature::HOVER),
            seg(2, 5, 13, 16, Kind::VERBATIM, Feature::COMPLETION),
        ]);
        assert_eq!(
            SpanMap::original_to_virtual_positions(Some(&filtered), 13, Feature::ALL),
            vec![
                MappedPosition {
                    position: 2,
                    fidelity: Fidelity::EXACT
                },
                MappedPosition {
                    position: 23,
                    fidelity: Fidelity::EXACT
                },
            ]
        );
        assert_eq!(
            SpanMap::original_to_virtual_positions(Some(&filtered), 13, Feature::COMPLETION),
            vec![MappedPosition {
                position: 2,
                fidelity: Fidelity::EXACT
            }]
        );
    }

    // Go: spanmap_test.go:295 TestOriginalToVirtualDuplicateGroup
    #[test]
    fn test_original_to_virtual_duplicate_group() {
        let m = new(&[
            seg(0, 3, 10, 13, Kind::VERBATIM, Feature::DEFINITION),
            seg(10, 13, 10, 13, Kind::VERBATIM, Feature::HOVER),
            seg(20, 25, 10, 13, Kind::ATOM, Feature::DEFINITION),
        ]);

        let semantic = SpanMap::original_to_virtual_positions(Some(&m), 11, Feature::HOVER);
        assert_eq!(semantic.len(), 1);
        assert_eq!(semantic[0].position, 11);
        assert_eq!(semantic[0].fidelity, Fidelity::EXACT);

        let navigation = SpanMap::original_to_virtual_positions(Some(&m), 11, Feature::DEFINITION);
        assert_eq!(navigation.len(), 2);
        assert_eq!(navigation[0].position, 1);
        assert_eq!(navigation[0].fidelity, Fidelity::EXACT);
        assert_eq!(navigation[1].position, 20);
        assert_eq!(navigation[1].fidelity, Fidelity::ATOM);

        let spans = SpanMap::original_to_virtual_spans(
            Some(&m),
            TextRange::new(10, 13),
            Feature::DEFINITION,
        );
        assert_eq!(spans.len(), 2);
        assert_eq!(spans[0].span.pos(), 0);
        assert_eq!(spans[0].span.end(), 3);
        assert_eq!(spans[1].span.pos(), 20);
        assert_eq!(spans[1].span.end(), 25);
    }

    // Go: spanmap_test.go:324 TestOriginalToVirtualCrossGroupProjections
    #[test]
    fn test_original_to_virtual_cross_group_projections() {
        let m = new(&[
            seg(0, 2, 0, 2, Kind::VERBATIM, Feature::HOVER),
            seg(2, 4, 2, 4, Kind::VERBATIM, Feature::HOVER),
            seg(10, 12, 0, 2, Kind::VERBATIM, Feature::HOVER),
            seg(12, 14, 2, 4, Kind::VERBATIM, Feature::HOVER),
        ]);

        let spans =
            SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(1, 3), Feature::HOVER);
        assert_eq!(spans.len(), 2);
        assert_eq!(spans[0].span, TextRange::new(1, 3));
        assert_eq!(spans[1].span, TextRange::new(11, 13));
        for mapped in &spans {
            assert_eq!(mapped.fidelity, Fidelity::APPROXIMATE);
        }
    }

    // Go: spanmap_test.go:343 TestOriginalToVirtualExplicitZeroFeatures
    #[test]
    fn test_original_to_virtual_explicit_zero_features() {
        let m = new(&[seg(0, 3, 10, 13, Kind::VERBATIM, Feature::NONE)]);

        assert_eq!(
            SpanMap::original_to_virtual_positions(Some(&m), 11, Feature::HOVER).len(),
            0
        );
        assert_eq!(
            SpanMap::original_to_virtual_positions(Some(&m), 11, Feature::DEFINITION).len(),
            0
        );
        assert_eq!(
            SpanMap::original_to_virtual_spans(Some(&m), TextRange::new(10, 13), Feature::HOVER)
                .len(),
            0
        );

        let data = m.marshal().expect("marshal");
        assert_eq!(String::from_utf8(data.clone()).unwrap(), "[[0,3,10,3,0,0]]");
        let decoded = unmarshal(&data).expect("unmarshal");
        let segments = SpanMap::segments(Some(&decoded));
        assert_eq!(segments[0].features, Feature::NONE);

        let legacy = unmarshal(b"[[0,3,10,3,0]]").expect("unmarshal");
        assert_eq!(SpanMap::segments(Some(&legacy))[0].features, Feature::ALL);
        assert_eq!(
            SpanMap::original_to_virtual_positions(Some(&legacy), 11, Feature::HOVER).len(),
            1
        );
    }

    // Go: spanmap_test.go:368 TestFeatureParticipationOriginalAndVirtual
    #[test]
    fn test_feature_participation_original_and_virtual() {
        let m = new(&[
            seg(0, 3, 10, 13, Kind::VERBATIM, Feature::HOVER),
            seg(3, 6, 20, 23, Kind::VERBATIM, Feature::COMPLETION),
        ]);

        assert_eq!(
            SpanMap::original_to_virtual_positions(Some(&m), 11, Feature::HOVER).len(),
            1
        );
        assert_eq!(
            SpanMap::original_to_virtual_positions(Some(&m), 11, Feature::COMPLETION).len(),
            0
        );

        let (mapped, fidelity) = SpanMap::virtual_to_original_span_for_feature(
            Some(&m),
            TextRange::new(0, 3),
            Feature::HOVER,
        );
        assert_eq!(mapped, TextRange::new(10, 13));
        assert_eq!(fidelity, Fidelity::EXACT);
        let (_, fidelity) = SpanMap::virtual_to_original_span_for_feature(
            Some(&m),
            TextRange::new(0, 3),
            Feature::COMPLETION,
        );
        assert_eq!(fidelity, Fidelity::NONE);

        // Diagnostics and edit safety use unfiltered geometry and cannot be disabled by feature flags.
        let (mapped, fidelity) = SpanMap::virtual_to_original_span(Some(&m), TextRange::new(0, 3));
        assert_eq!(mapped, TextRange::new(10, 13));
        assert_eq!(fidelity, Fidelity::EXACT);
    }

    // Go: spanmap_test.go:390 TestOriginalToVirtualSpanRoundTrip
    #[test]
    fn test_original_to_virtual_span_round_trip() {
        // Original spans are out of order relative to virtual spans, exercising the reverse index.
        let m = new(&[
            seg(0, 10, 200, 210, Kind::VERBATIM, Feature::ALL),
            seg(10, 20, 100, 110, Kind::VERBATIM, Feature::ALL),
        ]);

        for r in [TextRange::new(2, 8), TextRange::new(12, 18)] {
            let (orig, fidelity) = SpanMap::virtual_to_original_span(Some(&m), r);
            assert_eq!(fidelity, Fidelity::EXACT);
            let back = SpanMap::original_to_virtual_spans(Some(&m), orig, Feature::ALL);
            assert_eq!(back.len(), 1);
            assert_eq!(back[0].fidelity, Fidelity::EXACT);
            assert_eq!(back[0].span.pos(), r.pos());
            assert_eq!(back[0].span.end(), r.end());
        }
    }

    // Go: spanmap_test.go:410 TestMarshalRoundTrip
    #[test]
    fn test_marshal_round_trip() {
        let original = new(&[
            seg(3, 14, 60, 71, Kind::ATOM, Feature::NONE),
            seg(14, 24, 71, 81, Kind::VERBATIM, Feature::NONE),
        ]);

        let data = original.marshal().expect("marshal");
        let decoded = unmarshal(&data).expect("unmarshal");

        for r in [
            TextRange::new(1, 2),
            TextRange::new(4, 10),
            TextRange::new(16, 20),
        ] {
            let (want_range, want_fidelity) = SpanMap::virtual_to_original_span(Some(&original), r);
            let (got_range, got_fidelity) = SpanMap::virtual_to_original_span(Some(&decoded), r);
            assert_eq!(got_range, want_range);
            assert_eq!(got_fidelity, want_fidelity);
        }
    }

    // Go: spanmap_test.go:431 TestValidate
    #[test]
    fn test_validate() {
        const TRANSFORMED: &str = "const greeting = 1;\n";
        const ORIGINAL: &str = "<x>const greeting = 1;\n</x>";
        let script_start: i32 = 3; // index of "const" in original
        let transformed_len = TRANSFORMED.len() as i32;
        let original_len = ORIGINAL.len() as i32;

        // (name, segs, want kind, want ok)
        let test_cases: Vec<(&str, Vec<Segment>, MappingErrorKind, bool)> = vec![
            (
                "valid verbatim",
                vec![seg(
                    0,
                    transformed_len,
                    script_start,
                    script_start + transformed_len,
                    Kind::VERBATIM,
                    Feature::NONE,
                )],
                MappingErrorKind::default(),
                true,
            ),
            ("empty is valid", vec![], MappingErrorKind::default(), true),
            (
                "gap is allowed",
                vec![seg(3, transformed_len, 0, 0, Kind::ATOM, Feature::NONE)],
                MappingErrorKind::default(),
                true,
            ),
            (
                "overlap",
                vec![
                    seg(0, 10, 0, 0, Kind::ATOM, Feature::NONE),
                    seg(5, transformed_len, 0, 0, Kind::ATOM, Feature::NONE),
                ],
                MappingErrorKind::OVERLAP,
                false,
            ),
            (
                "original out of bounds",
                vec![seg(
                    0,
                    transformed_len,
                    0,
                    original_len + 10,
                    Kind::ATOM,
                    Feature::NONE,
                )],
                MappingErrorKind::OUT_OF_BOUNDS,
                false,
            ),
            (
                "verbatim text mismatch",
                vec![seg(
                    0,
                    transformed_len,
                    0,
                    transformed_len,
                    Kind::VERBATIM,
                    Feature::NONE,
                )],
                MappingErrorKind::VERBATIM_MISMATCH,
                false,
            ),
            (
                "unknown kind",
                vec![seg(0, 1, 0, 1, Kind(3), Feature::NONE)],
                MappingErrorKind::KIND,
                false,
            ),
        ];

        for (name, segs, want_kind, want_ok) in test_cases {
            let m = new(&segs);
            let problem = SpanMap::validate(Some(&m), TRANSFORMED, ORIGINAL);
            if want_ok {
                assert!(problem.is_none(), "{name}: expected valid, got {problem:?}");
                continue;
            }
            let problem = problem.unwrap_or_else(|| panic!("{name}: expected a problem"));
            assert_eq!(problem.kind, want_kind, "{name}");
        }
    }

    // Go: spanmap_test.go:498 TestValidateOriginalOverlapAndFeatures
    #[test]
    fn test_validate_original_overlap_and_features() {
        let tests: Vec<(&str, Vec<Segment>, MappingErrorKind, bool)> = vec![
            (
                "identical duplicate group",
                vec![
                    seg(0, 3, 0, 3, Kind::VERBATIM, Feature::DEFINITION),
                    seg(3, 6, 0, 3, Kind::VERBATIM, Feature::HOVER),
                ],
                MappingErrorKind::default(),
                true,
            ),
            (
                "partial original overlap",
                vec![
                    seg(0, 3, 0, 3, Kind::ATOM, Feature::NONE),
                    seg(3, 6, 2, 5, Kind::ATOM, Feature::NONE),
                ],
                MappingErrorKind::ORIGINAL_OVERLAP,
                false,
            ),
            (
                "nested original overlap",
                vec![
                    seg(0, 5, 0, 5, Kind::ATOM, Feature::NONE),
                    seg(5, 6, 1, 4, Kind::ATOM, Feature::NONE),
                ],
                MappingErrorKind::ORIGINAL_OVERLAP,
                false,
            ),
            (
                "duplicate without explicit features is tolerant",
                vec![
                    seg(0, 3, 0, 3, Kind::ATOM, Feature::NONE),
                    seg(3, 6, 0, 3, Kind::ATOM, Feature::DEFINITION),
                ],
                MappingErrorKind::default(),
                true,
            ),
            (
                "duplicate with shared feature members is tolerant",
                vec![
                    seg(0, 3, 0, 3, Kind::ATOM, Feature::HOVER),
                    seg(3, 6, 0, 3, Kind::ATOM, Feature::HOVER | Feature::DEFINITION),
                ],
                MappingErrorKind::default(),
                true,
            ),
            (
                "features on sole cover are valid",
                vec![seg(0, 3, 0, 3, Kind::ATOM, Feature::DEFINITION)],
                MappingErrorKind::default(),
                true,
            ),
            (
                "unknown feature flag",
                vec![seg(0, 3, 0, 3, Kind::ATOM, Feature(1 << 22))],
                MappingErrorKind::FEATURE,
                false,
            ),
        ];

        for (name, segments, want_kind, valid) in tests {
            let m = new(&segments);
            let problem = SpanMap::validate(Some(&m), "abcabc", "abcdef");
            if valid {
                assert!(problem.is_none(), "{name}: expected valid, got {problem:?}");
                continue;
            }
            let problem = problem.unwrap_or_else(|| panic!("{name}: expected a problem"));
            assert_eq!(problem.kind, want_kind, "{name}");
        }
    }

    // Go: spanmap_test.go:577 TestValidateNilIsValid
    #[test]
    fn test_validate_nil_is_valid() {
        assert!(SpanMap::validate(None, "abc", "abc").is_none());
    }
}
