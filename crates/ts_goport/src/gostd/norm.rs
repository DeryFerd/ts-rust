//! Go `golang.org/x/text/unicode/norm` v0.38.0 with the Unicode 15.0.0
//! tables (`tables15.0.0.go`, the `!go1.27` build that the pinned oracle
//! uses), as far as `gostd::collate` (x/text `internal/colltab`) calls it:
//! `Form.Properties`, the `Properties` getters, `Form.FirstBoundary` and
//! `Form.Append` with an empty `out`.
//!
//! PORT: Go keeps `string` and `[]byte` variants of the lookups (`input`).
//! colltab passes bytes here, so there is one `&[u8]` version.
//!
//! PORT: the tables are the Go values, dumped as little-endian binary files
//! in `data/` by `target/continuation-r97-goport/complete/gen/collate/gen.sh`
//! (zz_dump_test.go in a copy of x/text v0.38.0, go1.26.8). Do not edit
//! them by hand.

// Go: unicode/norm/normalize.go:36 Form
/// A Form denotes a canonical representation of Unicode code points.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Form {
    Nfc,
    Nfd,
    Nfkc,
    Nfkd,
}

pub const NFC: Form = Form::Nfc;
pub const NFD: Form = Form::Nfd;
pub const NFKC: Form = Form::Nfkc;
pub const NFKD: Form = Form::Nfkd;

// Go: unicode/norm/composition.go:9
const MAX_NON_STARTERS: u8 = 30;
/// The maximum number of characters needed for a buffer is
/// maxNonStarters + 1 for the starter + 1 for the GCJ
const MAX_BUFFER_SIZE: usize = MAX_NON_STARTERS as usize + 2;
/// utf8.UTFMax * maxBufferSize
const MAX_BYTE_BUFFER_SIZE: usize = 4 * MAX_BUFFER_SIZE; // 128

// Go: unicode/norm/normalize.go MaxSegmentSize
/// MaxSegmentSize is the maximum size of a byte buffer needed to consider any
/// sequence of starter and non-starter runes for the purpose of normalization.
pub const MAX_SEGMENT_SIZE: usize = MAX_BYTE_BUFFER_SIZE;

// Go: unicode/norm/composition.go:91 GraphemeJoiner
/// GraphemeJoiner is inserted after maxNonStarters non-starter runes.
const GRAPHEME_JOINER: &str = "\u{034F}";

// ---------------------------------------------------------------------------
// tables15.0.0.go
// ---------------------------------------------------------------------------

// Go: unicode/norm/tables15.0.0.go:20 ccc
static CCC: [u8; 56] = [
    0, 1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
    29, 30, 31, 32, 33, 34, 35, 36, 84, 91, 103, 107, 118, 122, 129, 130, 132, 202, 214, 216, 218,
    220, 222, 224, 226, 228, 230, 232, 233, 234, 240,
];

// Go: unicode/norm/tables15.0.0.go:30
const FIRST_MULTI: u16 = 0x199A;
const FIRST_CCC: u16 = 0x2DD5;
const END_MULTI: u16 = 0x2EBF;
const FIRST_LEADING_CCC: u16 = 0x4AEF;
const FIRST_CCC_ZERO_EXCEPT: u16 = 0x4BB9;
const FIRST_STARTER_WITH_N_LEAD: u16 = 0x4BE0;

// Go: unicode/norm/tables15.0.0.go:42 decomps (19426 bytes)
static DECOMPS: &[u8] = include_bytes!("data/norm_decomps.bin");

/// Go `[]uint16` table stored as little-endian bytes.
#[derive(Clone, Copy)]
pub struct U16s(pub &'static [u8]);

impl U16s {
    pub fn get(self, i: usize) -> u16 {
        u16::from_le_bytes([self.0[2 * i], self.0[2 * i + 1]])
    }

    /// Go `s[i:]`.
    pub fn from(self, i: usize) -> U16s {
        U16s(&self.0[2 * i..])
    }
}

/// Go `[]uint32` table stored as little-endian bytes.
#[derive(Clone, Copy)]
pub struct U32s(pub &'static [u8]);

impl U32s {
    pub fn get(self, i: usize) -> u32 {
        let b = &self.0[4 * i..4 * i + 4];
        u32::from_le_bytes([b[0], b[1], b[2], b[3]])
    }

    /// Go `s[i:]`.
    pub fn from(self, i: usize) -> U32s {
        U32s(&self.0[4 * i..])
    }
}

/// `nfcIndex` is `[1408]uint8`, `nfkcIndex` is `[1408]uint16`.
#[derive(Clone, Copy)]
enum TrieIndex {
    U8(&'static [u8]),
    U16(U16s),
}

impl TrieIndex {
    fn get(self, i: usize) -> u32 {
        match self {
            TrieIndex::U8(b) => u32::from(b[i]),
            TrieIndex::U16(v) => u32::from(v.get(i)),
        }
    }
}

// Go: unicode/norm/trie.go:7 valueRange, :12 sparseBlocks
/// PORT: `values` holds Go `valueRange{value uint16; lo, hi byte}` as 4
/// bytes each: `value` little-endian, then `lo` and `hi`.
#[derive(Clone, Copy)]
struct SparseBlocks {
    values: &'static [u8],
    offset: U16s,
}

impl SparseBlocks {
    /// (value, lo, hi) of entry i.
    fn value_range(self, i: usize) -> (u16, u8, u8) {
        let b = &self.values[4 * i..4 * i + 4];
        (u16::from_le_bytes([b[0], b[1]]), b[2], b[3])
    }

    // Go: unicode/norm/trie.go:34 (*sparseBlocks).lookup
    /// lookup determines the type of block n and looks up the value for b.
    /// For n < t.cutoff, the block is a simple lookup table. Otherwise, the block
    /// is a list of ranges with an accompanying value. Given a matching range r,
    /// the value for b is by r.value + (b - r.lo) * stride.
    fn lookup(self, n: u32, b: u8) -> u16 {
        let offset = self.offset.get(n as usize);
        let (header_value, header_lo, _) = self.value_range(usize::from(offset));
        let mut lo = offset + 1;
        let mut hi = lo + u16::from(header_lo);
        while lo < hi {
            let m = lo + (hi - lo) / 2;
            let (r_value, r_lo, r_hi) = self.value_range(usize::from(m));
            if r_lo <= b && b <= r_hi {
                return r_value.wrapping_add(u16::from(b - r_lo).wrapping_mul(header_value));
            }
            if b < r_lo {
                hi = m;
            } else {
                lo = m + 1;
            }
        }
        0
    }
}

/// Go `nfcTrie` and `nfkcTrie` (tables15.0.0.go:2781 and :4496): generated
/// tries that share one code shape.
struct NormTrie {
    values: U16s,
    index: TrieIndex,
    sparse: SparseBlocks,
    /// The first block number that is sparse (Go `case n < 46` for NFC and
    /// `case n < 95` for NFKC in `lookupValue`).
    cutoff: u32,
}

// Go: unicode/norm/tables15.0.0.go:2968 nfcValues, :3487 nfcIndex,
// :3594 nfcSparseOffset, :3597 nfcSparseValues; trie.go:17 nfcSparse
static NFC_DATA: NormTrie = NormTrie {
    values: U16s(include_bytes!("data/norm_nfc_values.bin")),
    index: TrieIndex::U8(include_bytes!("data/norm_nfc_index.bin")),
    sparse: SparseBlocks {
        values: include_bytes!("data/norm_nfc_sparse_values.bin"),
        offset: U16s(include_bytes!("data/norm_nfc_sparse_offset.bin")),
    },
    cutoff: 46,
};

// Go: unicode/norm/tables15.0.0.go:4683 nfkcValues, :5744 nfkcIndex,
// :5859 nfkcSparseOffset, :5862 nfkcSparseValues; trie.go:22 nfkcSparse
static NFKC_DATA: NormTrie = NormTrie {
    values: U16s(include_bytes!("data/norm_nfkc_values.bin")),
    index: TrieIndex::U16(U16s(include_bytes!("data/norm_nfkc_index.bin"))),
    sparse: SparseBlocks {
        values: include_bytes!("data/norm_nfkc_sparse_values.bin"),
        offset: U16s(include_bytes!("data/norm_nfkc_sparse_offset.bin")),
    },
    cutoff: 95,
};

impl NormTrie {
    // Go: unicode/norm/tables15.0.0.go:2781 (*nfcTrie).lookup
    // Go: unicode/norm/tables15.0.0.go:4496 (*nfkcTrie).lookup
    /// lookup returns the trie value for the first UTF-8 encoding in s and
    /// the width in bytes of this encoding. The size will be 0 if s does not
    /// hold enough bytes to complete the encoding. len(s) must be greater than 0.
    fn lookup(&self, s: &[u8]) -> (u16, usize) {
        let c0 = s[0];
        if c0 < 0x80 {
            // is ASCII
            return (self.values.get(usize::from(c0)), 1);
        } else if c0 < 0xC2 {
            return (0, 1); // Illegal UTF-8: not a starter, not ASCII.
        } else if c0 < 0xE0 {
            // 2-byte UTF-8
            if s.len() < 2 {
                return (0, 0);
            }
            let i = self.index.get(usize::from(c0));
            let c1 = s[1];
            if !(0x80..0xC0).contains(&c1) {
                return (0, 1); // Illegal UTF-8: not a continuation byte.
            }
            return (self.lookup_value(i, c1), 2);
        } else if c0 < 0xF0 {
            // 3-byte UTF-8
            if s.len() < 3 {
                return (0, 0);
            }
            let mut i = self.index.get(usize::from(c0));
            let c1 = s[1];
            if !(0x80..0xC0).contains(&c1) {
                return (0, 1); // Illegal UTF-8: not a continuation byte.
            }
            let o = (i << 6) + u32::from(c1);
            i = self.index.get(o as usize);
            let c2 = s[2];
            if !(0x80..0xC0).contains(&c2) {
                return (0, 2); // Illegal UTF-8: not a continuation byte.
            }
            return (self.lookup_value(i, c2), 3);
        } else if c0 < 0xF8 {
            // 4-byte UTF-8
            if s.len() < 4 {
                return (0, 0);
            }
            let mut i = self.index.get(usize::from(c0));
            let c1 = s[1];
            if !(0x80..0xC0).contains(&c1) {
                return (0, 1); // Illegal UTF-8: not a continuation byte.
            }
            let mut o = (i << 6) + u32::from(c1);
            i = self.index.get(o as usize);
            let c2 = s[2];
            if !(0x80..0xC0).contains(&c2) {
                return (0, 2); // Illegal UTF-8: not a continuation byte.
            }
            o = (i << 6) + u32::from(c2);
            i = self.index.get(o as usize);
            let c3 = s[3];
            if !(0x80..0xC0).contains(&c3) {
                return (0, 3); // Illegal UTF-8: not a continuation byte.
            }
            return (self.lookup_value(i, c3), 4);
        }
        // Illegal rune
        (0, 1)
    }

    // Go: unicode/norm/tables15.0.0.go:2956 (*nfcTrie).lookupValue
    // Go: unicode/norm/tables15.0.0.go:4671 (*nfkcTrie).lookupValue
    /// lookupValue determines the type of block n and looks up the value for b.
    fn lookup_value(&self, n: u32, b: u8) -> u16 {
        if n < self.cutoff {
            self.values.get(((n << 6) + u32::from(b)) as usize)
        } else {
            self.sparse.lookup(n - self.cutoff, b)
        }
    }
}

// ---------------------------------------------------------------------------
// forminfo.go
// ---------------------------------------------------------------------------

// Go: unicode/norm/forminfo.go:36
/// to clear all but the relevant bits in a qcInfo
const QC_INFO_MASK: u8 = 0x3F;
/// extract the length value from the header byte (31 => 33)
const HEADER_LEN_MASK: u8 = 0x1F;
/// extract the qcInfo bits from the header byte
const HEADER_FLAGS_MASK: u8 = 0xE0;

// Go: unicode/norm/forminfo.go:43 Properties
/// Properties provides access to normalization properties of a rune.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Properties {
    /// start position in reorderBuffer; used in composition.go
    pos: u8,
    /// length of UTF-8 encoding of this rune
    size: u8,
    /// leading canonical combining class (ccc if not decomposition)
    ccc: u8,
    /// trailing canonical combining class (ccc if not decomposition)
    tccc: u8,
    /// number of leading non-starters.
    n_lead: u8,
    /// quick check flags (Go `qcInfo`)
    flags: u8,
    index: u16,
}

/// Go `lookupFunc`: functions dispatchable per form.
type LookupFunc = fn(&[u8], usize) -> Properties;

// Go: unicode/norm/forminfo.go:57 formInfo
/// formInfo holds Form-specific functions and tables.
/// PORT: Go `nextMain` (the iterator) is not used by colltab; not ported.
struct FormInfo {
    #[allow(dead_code)]
    form: Form,
    composing: bool,
    #[allow(dead_code)]
    compatibility: bool,
    info: LookupFunc,
}

// Go: unicode/norm/forminfo.go:64 formTable
static FORM_TABLE: [FormInfo; 4] = [
    FormInfo {
        form: NFC,
        composing: true,
        compatibility: false,
        info: lookup_info_nfc,
    },
    FormInfo {
        form: NFD,
        composing: false,
        compatibility: false,
        info: lookup_info_nfc,
    },
    FormInfo {
        form: NFKC,
        composing: true,
        compatibility: true,
        info: lookup_info_nfkc,
    },
    FormInfo {
        form: NFKD,
        composing: false,
        compatibility: true,
        info: lookup_info_nfkc,
    },
];

fn form_table(f: Form) -> &'static FormInfo {
    &FORM_TABLE[f as usize]
}

impl Properties {
    // Go: unicode/norm/forminfo.go:95 (Properties).BoundaryBefore
    /// BoundaryBefore returns true if this rune starts a new segment and
    /// cannot combine with any rune on the left.
    pub fn boundary_before(self) -> bool {
        if self.ccc == 0 && !self.combines_backward() {
            return true;
        }
        // We assume that the CCC of the first character in a decomposition
        // is always non-zero if different from info.ccc and that we can return
        // false at this point. This is verified by maketables.
        false
    }

    // Go: unicode/norm/forminfo.go:107 (Properties).BoundaryAfter
    /// BoundaryAfter returns true if runes cannot combine with or otherwise
    /// interact with this or previous runes.
    pub fn boundary_after(self) -> bool {
        // TODO: loosen these conditions.
        self.is_inert()
    }

    // Go: unicode/norm/forminfo.go:124
    #[allow(dead_code)]
    fn is_yes_c(self) -> bool {
        self.flags & 0x10 == 0
    }

    fn is_yes_d(self) -> bool {
        self.flags & 0x4 == 0
    }

    #[allow(dead_code)]
    fn combines_forward(self) -> bool {
        self.flags & 0x20 != 0
    }

    fn combines_backward(self) -> bool {
        self.flags & 0x8 != 0 // == isMaybe
    }

    fn has_decomposition(self) -> bool {
        self.flags & 0x4 != 0 // == isNoD
    }

    // Go: unicode/norm/forminfo.go:131 (Properties).isInert
    fn is_inert(self) -> bool {
        self.flags & QC_INFO_MASK == 0 && self.ccc == 0
    }

    // Go: unicode/norm/forminfo.go:135 (Properties).multiSegment
    #[allow(dead_code)]
    fn multi_segment(self) -> bool {
        self.index >= FIRST_MULTI && self.index < END_MULTI
    }

    // Go: unicode/norm/forminfo.go:139 (Properties).nLeadingNonStarters
    fn n_leading_non_starters(self) -> u8 {
        self.n_lead
    }

    // Go: unicode/norm/forminfo.go:143 (Properties).nTrailingNonStarters
    fn n_trailing_non_starters(self) -> u8 {
        self.flags & 0x03
    }

    // Go: unicode/norm/forminfo.go:149 (Properties).Decomposition
    /// Decomposition returns the decomposition for the underlying rune
    /// or nil if there is none.
    pub fn decomposition(self) -> Option<&'static [u8]> {
        // TODO: create the decomposition for Hangul?
        if self.index == 0 {
            return None;
        }
        let mut i = usize::from(self.index);
        let mut n = usize::from(DECOMPS[i] & HEADER_LEN_MASK);
        if n == 31 {
            n = 33;
        }
        i += 1;
        Some(&DECOMPS[i..i + n])
    }

    // Go: unicode/norm/forminfo.go:163 (Properties).Size
    /// Size returns the length of UTF-8 encoding of the rune.
    pub fn size(self) -> usize {
        usize::from(self.size)
    }

    // Go: unicode/norm/forminfo.go:168 (Properties).CCC
    /// CCC returns the canonical combining class of the underlying rune.
    pub fn ccc(self) -> u8 {
        if self.index >= FIRST_CCC_ZERO_EXCEPT {
            return 0;
        }
        CCC[usize::from(self.ccc)]
    }

    // Go: unicode/norm/forminfo.go:177 (Properties).LeadCCC
    /// LeadCCC returns the CCC of the first rune in the decomposition.
    /// If there is no decomposition, LeadCCC equals CCC.
    pub fn lead_ccc(self) -> u8 {
        CCC[usize::from(self.ccc)]
    }

    // Go: unicode/norm/forminfo.go:183 (Properties).TrailCCC
    /// TrailCCC returns the CCC of the last rune in the decomposition.
    /// If there is no decomposition, TrailCCC equals CCC.
    pub fn trail_ccc(self) -> u8 {
        CCC[usize::from(self.tccc)]
    }
}

// Go: unicode/norm/forminfo.go:225 lookupInfoNFC
fn lookup_info_nfc(b: &[u8], i: usize) -> Properties {
    let (v, sz) = NFC_DATA.lookup(&b[i..]);
    comp_info(v, sz)
}

// Go: unicode/norm/forminfo.go:230 lookupInfoNFKC
fn lookup_info_nfkc(b: &[u8], i: usize) -> Properties {
    let (v, sz) = NFKC_DATA.lookup(&b[i..]);
    comp_info(v, sz)
}

impl Form {
    // Go: unicode/norm/forminfo.go:236 (Form).Properties
    /// Properties returns properties for the first rune in s.
    pub fn properties(self, s: &[u8]) -> Properties {
        if self == NFC || self == NFD {
            let (v, sz) = NFC_DATA.lookup(s);
            return comp_info(v, sz);
        }
        let (v, sz) = NFKC_DATA.lookup(s);
        comp_info(v, sz)
    }
}

// Go: unicode/norm/forminfo.go:254 compInfo
/// compInfo converts the information contained in v and sz
/// to a Properties.  See the comment at the top of the file
/// for more information on the format.
fn comp_info(mut v: u16, sz: usize) -> Properties {
    if v == 0 {
        return Properties {
            size: sz as u8,
            ..Properties::default()
        };
    } else if v >= 0x8000 {
        let mut p = Properties {
            size: sz as u8,
            ccc: v as u8,
            tccc: v as u8,
            flags: (v >> 8) as u8,
            ..Properties::default()
        };
        if p.ccc > 0 || p.combines_backward() {
            p.n_lead = p.flags & 0x3;
        }
        return p;
    }
    // has decomposition
    let h = DECOMPS[usize::from(v)];
    let f = ((h & HEADER_FLAGS_MASK) >> 2) | 0x4;
    let mut p = Properties {
        size: sz as u8,
        flags: f,
        index: v,
        ..Properties::default()
    };
    if v >= FIRST_CCC {
        let mut n = u16::from(h & HEADER_LEN_MASK);
        if n == 31 {
            n = 33;
        }
        v += n + 1;
        let c = DECOMPS[usize::from(v)];
        p.tccc = c >> 2;
        p.flags |= c & 0x3;
        if v >= FIRST_LEADING_CCC {
            p.n_lead = c & 0x3;
            if v >= FIRST_STARTER_WITH_N_LEAD {
                // We were tricked. Remove the decomposition.
                p.flags &= 0x03;
                p.index = 0;
                return p;
            }
            p.ccc = DECOMPS[usize::from(v) + 1];
        }
    }
    p
}

// ---------------------------------------------------------------------------
// input.go
// ---------------------------------------------------------------------------

// Go: unicode/norm/input.go:38 (*input).skipASCII
fn skip_ascii(src: &[u8], mut p: usize, max: usize) -> usize {
    while p < max && src[p] < 0x80 {
        p += 1;
    }
    p
}

// Go: unicode/norm/input.go:50 (*input).skipContinuationBytes
fn skip_continuation_bytes(src: &[u8], mut p: usize) -> usize {
    while p < src.len() && src[p] & 0xC0 == 0x80 {
        p += 1;
    }
    p
}

// Go: unicode/norm/input.go:96 (*input).hangul
fn input_hangul(src: &[u8], p: usize) -> u32 {
    if !is_hangul(&src[p..]) {
        return 0;
    }
    let (r, size) = decode_rune(&src[p..]);
    if size != HANGUL_UTF8_SIZE {
        return 0;
    }
    r
}

/// Go `utf8.DecodeRune` for a valid encoding: the rune and its size.
/// Invalid UTF-8 gives (U+FFFD, 1).
fn decode_rune(s: &[u8]) -> (u32, usize) {
    let n = match s.first() {
        None => return (0xFFFD, 0),
        Some(&b) if b < 0x80 => return (u32::from(b), 1),
        Some(&b) if b >= 0xF0 => 4,
        Some(&b) if b >= 0xE0 => 3,
        Some(&b) if b >= 0xC0 => 2,
        Some(_) => return (0xFFFD, 1),
    };
    match s
        .get(..n)
        .and_then(|b| std::str::from_utf8(b).ok())
        .and_then(|t| t.chars().next())
    {
        Some(c) => (c as u32, n),
        None => (0xFFFD, 1),
    }
}

/// Go `utf8.EncodeRune(buf, r)` for a valid rune: writes into buf and
/// returns the size.
fn encode_rune(buf: &mut [u8], r: u32) -> usize {
    let c = char::from_u32(r).unwrap_or('\u{FFFD}');
    c.encode_utf8(buf).len()
}

// ---------------------------------------------------------------------------
// composition.go
// ---------------------------------------------------------------------------

// Go: unicode/norm/composition.go:22 ssState
/// ssState is used for reporting the segment state after inserting a rune.
/// It is returned by streamSafe.next.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SsState {
    /// Indicates a rune was successfully added to the segment.
    Success,
    /// Indicates a rune starts a new segment and should not be added.
    Starter,
    /// Indicates a rune caused a segment overflow and a CGJ should be inserted.
    Overflow,
}

// Go: unicode/norm/composition.go:35 streamSafe
/// streamSafe implements the policy of when a CGJ should be inserted.
#[derive(Clone, Copy, Debug, Default)]
struct StreamSafe(u8);

impl StreamSafe {
    // Go: unicode/norm/composition.go:44 (*streamSafe).next
    /// insert returns a ssState value to indicate whether a rune represented by p
    /// can be inserted.
    fn next(&mut self, p: Properties) -> SsState {
        if self.0 > MAX_NON_STARTERS {
            panic!("streamSafe was not reset");
        }
        let n = p.n_leading_non_starters();
        self.0 = self.0.wrapping_add(n);
        if self.0 > MAX_NON_STARTERS {
            self.0 = 0;
            return SsState::Overflow;
        }
        // The Stream-Safe Text Processing prescribes that the counting can stop
        // as soon as a starter is encountered. However, there are some starters,
        // like Jamo V and T, that can combine with other runes, leaving their
        // successive non-starters appended to the previous, possibly causing an
        // overflow. We will therefore consider any rune with a non-zero nLead to
        // be a non-starter. Note that it always hold that if nLead > 0 then
        // nLead == nTrail.
        if n == 0 {
            self.0 = p.n_trailing_non_starters();
            return SsState::Starter;
        }
        SsState::Success
    }

    // Go: unicode/norm/composition.go:86 (streamSafe).isMax
    fn is_max(self) -> bool {
        self.0 == MAX_NON_STARTERS
    }
}

// Go: unicode/norm/composition.go:98 reorderBuffer
/// reorderBuffer is used to normalize a single segment.  Characters inserted with
/// insert are decomposed and reordered based on CCC. The compose method can
/// be used to recombine characters.  Note that the byte buffer does not hold
/// the UTF-8 characters in order.  Only the rune array is maintained in sorted
/// order. flush writes the resulting segment to a byte array.
/// PORT: `flushF` is always `appendFlush` here (`Append`); the composing
/// forms are not used by colltab, so `compose` is not ported.
struct ReorderBuffer<'a> {
    /// Per character info.
    rune: [Properties; MAX_BUFFER_SIZE],
    /// UTF-8 buffer. Referenced by runeInfo.pos.
    byte: [u8; MAX_BYTE_BUFFER_SIZE],
    /// Number or bytes.
    nbyte: u8,
    /// For limiting length of non-starter sequence.
    ss: StreamSafe,
    /// Number of runeInfos.
    nrune: usize,
    f: &'static FormInfo,

    src: &'a [u8],
    nsrc: usize,

    out: Vec<u8>,
}

// Go: unicode/norm/composition.go:182 insertErr
/// insertErr is an error code returned by insert. Using this type instead
/// of error improves performance up to 20% for many of the benchmarks.
type InsertErr = i32;

const I_SUCCESS: InsertErr = 0;

impl ReorderBuffer<'_> {
    // Go: unicode/norm/composition.go:134 (*reorderBuffer).reset
    /// reset discards all characters from the buffer.
    fn reset(&mut self) {
        self.nrune = 0;
        self.nbyte = 0;
    }

    // Go: unicode/norm/composition.go:139 (*reorderBuffer).doFlush
    fn do_flush(&mut self) -> bool {
        if self.f.composing {
            unreachable!("norm: compose is not ported (colltab only decomposes)");
        }
        let res = self.append_flush();
        self.reset();
        res
    }

    // Go: unicode/norm/composition.go:149 appendFlush
    /// appendFlush appends the normalized segment to rb.out.
    fn append_flush(&mut self) -> bool {
        for i in 0..self.nrune {
            let start = usize::from(self.rune[i].pos);
            let end = start + usize::from(self.rune[i].size);
            self.out.extend_from_slice(&self.byte[start..end]);
        }
        true
    }

    // Go: unicode/norm/composition.go:184 (*reorderBuffer).insertOrdered
    /// insertOrdered inserts a rune in the buffer, ordered by Canonical Combining Class.
    /// It returns false if the buffer is not large enough to hold the rune.
    /// It is used internally by insert and insertString only.
    fn insert_ordered(&mut self, mut info: Properties) {
        let mut n = self.nrune;
        let cc = info.ccc;
        if cc > 0 {
            // Find insertion position + move elements to make room.
            while n > 0 {
                if self.rune[n - 1].ccc <= cc {
                    break;
                }
                self.rune[n] = self.rune[n - 1];
                n -= 1;
            }
        }
        self.nrune += 1;
        let pos = self.nbyte;
        self.nbyte += 4; // utf8.UTFMax
        info.pos = pos;
        self.rune[n] = info;
    }

    // Go: unicode/norm/composition.go:218 (*reorderBuffer).insertFlush
    /// insertFlush inserts the given rune in the buffer ordered by CCC.
    /// If a decomposition with multiple segments are encountered, they leading
    /// ones are flushed.
    /// It returns a non-zero error code if the rune was not inserted.
    fn insert_flush(&mut self, src: &[u8], i: usize, info: Properties) -> InsertErr {
        let rune = input_hangul(src, i);
        if rune != 0 {
            self.decompose_hangul(rune);
            return I_SUCCESS;
        }
        if info.has_decomposition() {
            return self.insert_decomposed(info.decomposition().unwrap_or_default());
        }
        self.insert_single(src, i, info);
        I_SUCCESS
    }

    // Go: unicode/norm/composition.go:249 (*reorderBuffer).insertDecomposed
    /// insertDecomposed inserts an entry in to the reorderBuffer for each rune
    /// in dcomp. dcomp must be a sequence of decomposed UTF-8-encoded runes.
    /// It flushes the buffer on each new segment start.
    fn insert_decomposed(&mut self, dcomp: &[u8]) -> InsertErr {
        // As the streamSafe accounting already handles the counting for modifiers,
        // we don't have to call next. However, we do need to keep the accounting
        // intact when flushing the buffer.
        let mut i = 0;
        while i < dcomp.len() {
            let info = (self.f.info)(dcomp, i);
            if info.boundary_before() && self.nrune > 0 && !self.do_flush() {
                return -1; // iShortDst
            }
            i += go_copy(
                &mut self.byte[usize::from(self.nbyte)..],
                &dcomp[i..i + usize::from(info.size)],
            );
            self.insert_ordered(info);
        }
        I_SUCCESS
    }

    // Go: unicode/norm/composition.go:267 (*reorderBuffer).insertSingle
    /// insertSingle inserts an entry in the reorderBuffer for the rune at
    /// position i. info is the runeInfo for the rune at position i.
    fn insert_single(&mut self, src: &[u8], i: usize, info: Properties) {
        go_copy(
            &mut self.byte[usize::from(self.nbyte)..],
            &src[i..i + usize::from(info.size)],
        );
        self.insert_ordered(info);
    }

    // Go: unicode/norm/composition.go:273 (*reorderBuffer).insertCGJ
    /// insertCGJ inserts a Combining Grapheme Joiner (0x034f) into rb.
    fn insert_cgj(&mut self) {
        self.insert_single(
            GRAPHEME_JOINER.as_bytes(),
            0,
            Properties {
                size: GRAPHEME_JOINER.len() as u8,
                ..Properties::default()
            },
        );
    }

    // Go: unicode/norm/composition.go:278 (*reorderBuffer).appendRune
    /// appendRune inserts a rune at the end of the buffer. It is used for Hangul.
    fn append_rune(&mut self, r: u32) {
        let bn = self.nbyte;
        let sz = encode_rune(&mut self.byte[usize::from(bn)..], r);
        self.nbyte += 4; // utf8.UTFMax
        self.rune[self.nrune] = Properties {
            pos: bn,
            size: sz as u8,
            ..Properties::default()
        };
        self.nrune += 1;
    }

    // Go: unicode/norm/composition.go:411 (*reorderBuffer).decomposeHangul
    /// decomposeHangul algorithmically decomposes a Hangul rune into
    /// its Jamo components.
    /// See https://unicode.org/reports/tr15/#Hangul for details on decomposing Hangul.
    fn decompose_hangul(&mut self, mut r: u32) {
        r -= HANGUL_BASE;
        let x = r % JAMO_T_COUNT;
        r /= JAMO_T_COUNT;
        self.append_rune(JAMO_L_BASE + r / JAMO_V_COUNT);
        self.append_rune(JAMO_V_BASE + r % JAMO_V_COUNT);
        if x != 0 {
            self.append_rune(JAMO_T_BASE + x);
        }
    }
}

/// Go `copy(dst, src)`: copies min(len(dst), len(src)) bytes and returns
/// that count.
fn go_copy(dst: &mut [u8], src: &[u8]) -> usize {
    let n = dst.len().min(src.len());
    dst[..n].copy_from_slice(&src[..n]);
    n
}

// Go: unicode/norm/composition.go:311
// For Hangul we combine algorithmically, instead of using tables.
/// UTF-8(hangulBase) -> EA B0 80
const HANGUL_BASE: u32 = 0xAC00;
const HANGUL_BASE0: u8 = 0xEA;
const HANGUL_BASE1: u8 = 0xB0;
/// UTF-8(0xD7A4) -> ED 9E A4
const HANGUL_END0: u8 = 0xED;
const HANGUL_END1: u8 = 0x9E;
const HANGUL_END2: u8 = 0xA4;
/// UTF-8(jamoLBase) -> E1 84 00
const JAMO_L_BASE: u32 = 0x1100;
const JAMO_V_BASE: u32 = 0x1161;
const JAMO_T_BASE: u32 = 0x11A7;
const JAMO_T_COUNT: u32 = 28;
const JAMO_V_COUNT: u32 = 21;

// Go: unicode/norm/composition.go:334 hangulUTF8Size
const HANGUL_UTF8_SIZE: usize = 3;

// Go: unicode/norm/composition.go:336 isHangul
fn is_hangul(b: &[u8]) -> bool {
    if b.len() < HANGUL_UTF8_SIZE {
        return false;
    }
    let b0 = b[0];
    if b0 < HANGUL_BASE0 {
        return false;
    }
    let b1 = b[1];
    if b0 == HANGUL_BASE0 {
        return b1 >= HANGUL_BASE1;
    } else if b0 < HANGUL_END0 {
        return true;
    } else if b0 > HANGUL_END0 {
        return false;
    } else if b1 < HANGUL_END1 {
        return true;
    }
    b1 == HANGUL_END1 && b[2] < HANGUL_END2
}

// ---------------------------------------------------------------------------
// normalize.go
// ---------------------------------------------------------------------------

// Go: unicode/norm/normalize.go:182 appendQuick
fn append_quick(rb: &mut ReorderBuffer<'_>, i: usize) -> usize {
    if rb.nsrc == i {
        return i;
    }
    let (end, _) = quick_span(rb.f, rb.src, i, rb.nsrc, true);
    rb.out.extend_from_slice(&rb.src[i..end]);
    end
}

impl Form {
    // Go: unicode/norm/normalize.go:193 (Form).Append
    /// Append returns f(append(out, b...)).
    /// The buffer out must be nil, empty, or equal to f(out).
    /// PORT: colltab always passes an empty `out` (`buf[:0]`), so only
    /// Go's `len(out) == 0` branch of `doAppend` is ported.
    pub fn append(self, src: &[u8]) -> Vec<u8> {
        // Go: unicode/norm/normalize.go:197 (Form).doAppend
        let n = src.len();
        if n == 0 {
            return Vec::new();
        }
        let ft = form_table(self);
        // Attempt to do a quickSpan first so we can avoid initializing the reorderBuffer.
        let (p, _) = quick_span(ft, src, 0, n, true);
        let out = src[..p].to_vec();
        if p == n {
            return out;
        }
        let mut rb = ReorderBuffer {
            rune: [Properties::default(); MAX_BUFFER_SIZE],
            byte: [0; MAX_BYTE_BUFFER_SIZE],
            nbyte: 0,
            ss: StreamSafe(0),
            nrune: 0,
            f: ft,
            src,
            nsrc: n,
            out,
        };
        do_append_inner(&mut rb, p)
    }

    // Go: unicode/norm/normalize.go:366 (Form).FirstBoundary
    /// FirstBoundary returns the position i of the first boundary in b
    /// or -1 if b contains no boundary.
    pub fn first_boundary(self, b: &[u8]) -> i32 {
        self.first_boundary_inner(b, b.len())
    }

    // Go: unicode/norm/normalize.go:370 (Form).firstBoundary
    fn first_boundary_inner(self, src: &[u8], nsrc: usize) -> i32 {
        let mut i = skip_continuation_bytes(src, 0);
        if i >= nsrc {
            return -1;
        }
        let fd = form_table(self);
        let mut ss = StreamSafe(0);
        // We should call ss.first here, but we can't as the first rune is
        // skipped already. This means FirstBoundary can't really determine
        // CGJ insertion points correctly. Luckily it doesn't have to.
        loop {
            let info = (fd.info)(src, i);
            if info.size == 0 {
                return -1;
            }
            if ss.next(info) != SsState::Success {
                return i as i32;
            }
            i += usize::from(info.size);
            if i >= nsrc {
                if !info.boundary_after() && !ss.is_max() {
                    return -1;
                }
                return nsrc as i32;
            }
        }
    }
}

// Go: unicode/norm/normalize.go:251 doAppendInner
fn do_append_inner(rb: &mut ReorderBuffer<'_>, mut p: usize) -> Vec<u8> {
    let n = rb.nsrc;
    while p < n {
        // PORT: Go converts the negative insertErr codes to int. With
        // `appendFlush` and `atEOF` they do not occur.
        p = decompose_segment(rb, p, true) as usize;
        p = append_quick(rb, p);
    }
    std::mem::take(&mut rb.out)
}

// Go: unicode/norm/normalize.go:304 (*formInfo).quickSpan
/// quickSpan returns a boundary n such that src[0:n] == f(src[0:n]) and
/// whether any non-normalized parts were found. If atEOF is false, n will
/// not point past the last segment if this segment might be become
/// non-normalized by appending other runes.
fn quick_span(f: &FormInfo, src: &[u8], mut i: usize, end: usize, at_eof: bool) -> (usize, bool) {
    let mut last_cc: u8 = 0;
    let mut ss = StreamSafe(0);
    let mut last_seg_start = i;
    let mut n = end;
    while i < n {
        let j = skip_ascii(src, i, n);
        if i != j {
            i = j;
            last_seg_start = i - 1;
            last_cc = 0;
            ss = StreamSafe(0);
            continue;
        }
        let info = (f.info)(src, i);
        if info.size == 0 {
            if at_eof {
                // include incomplete runes
                return (n, true);
            }
            return (last_seg_start, true);
        }
        // This block needs to be before the next, because it is possible to
        // have an overflow for runes that are starters (e.g. with U+FF9E).
        match ss.next(info) {
            SsState::Starter => last_seg_start = i,
            SsState::Overflow => return (last_seg_start, false),
            SsState::Success => {
                if last_cc > info.ccc {
                    return (last_seg_start, false);
                }
            }
        }
        if f.composing {
            if !info.is_yes_c() {
                break;
            }
        } else if !info.is_yes_d() {
            break;
        }
        last_cc = info.ccc;
        i += usize::from(info.size);
    }
    if i == n {
        if !at_eof {
            n = last_seg_start;
        }
        return (n, true);
    }
    (last_seg_start, false)
}

// Go: unicode/norm/normalize.go:504 decomposeSegment
/// decomposeSegment scans the first segment in src into rb. It inserts 0x034f
/// (Grapheme Joiner) when it encounters a sequence of more than 30 non-starters
/// and returns the number of bytes consumed from src or iShortDst or iShortSrc.
fn decompose_segment(rb: &mut ReorderBuffer<'_>, mut sp: usize, at_eof: bool) -> i32 {
    // Force one character to be consumed.
    let mut info = (rb.f.info)(rb.src, sp);
    if info.size == 0 {
        return 0;
    }
    // PORT: Go `goto end` is the labeled block `body`.
    'body: {
        let s = rb.ss.next(info);
        if s == SsState::Starter {
            // TODO: this could be removed if we don't support merging.
            if rb.nrune > 0 {
                break 'body;
            }
        } else if s == SsState::Overflow {
            rb.insert_cgj();
            break 'body;
        }
        let err = rb.insert_flush(rb.src, sp, info);
        if err != I_SUCCESS {
            return err;
        }
        loop {
            sp += usize::from(info.size);
            if sp >= rb.nsrc {
                if !at_eof && !info.boundary_after() {
                    return -2; // iShortSrc
                }
                break;
            }
            info = (rb.f.info)(rb.src, sp);
            if info.size == 0 {
                if !at_eof {
                    return -2; // iShortSrc
                }
                break;
            }
            let s = rb.ss.next(info);
            if s == SsState::Starter {
                break;
            } else if s == SsState::Overflow {
                rb.insert_cgj();
                break;
            }
            let err = rb.insert_flush(rb.src, sp, info);
            if err != I_SUCCESS {
                return err;
            }
        }
    }
    if !rb.do_flush() {
        return -1; // iShortDst
    }
    sp as i32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nfd_append_decomposes_hangul() {
        // U+AC01 HANGUL SYLLABLE GAG -> U+1100 U+1161 U+11A8
        assert_eq!(
            NFD.append("각".as_bytes()),
            "\u{1100}\u{1161}\u{11A8}".as_bytes()
        );
        // U+AC00 HANGUL SYLLABLE GA -> U+1100 U+1161
        assert_eq!(NFD.append("가".as_bytes()), "\u{1100}\u{1161}".as_bytes());
    }

    #[test]
    fn properties_and_decomposition() {
        // U+00E9 has the canonical decomposition e + U+0301.
        let p = NFD.properties("é".as_bytes());
        assert_eq!(p.size(), 2);
        assert_eq!(p.decomposition(), Some("e\u{301}".as_bytes()));
        assert_eq!(p.lead_ccc(), 0);
        // U+0301 COMBINING ACUTE ACCENT has ccc 230.
        let p = NFD.properties("\u{301}".as_bytes());
        assert_eq!((p.lead_ccc(), p.trail_ccc()), (230, 230));
        // U+FB01 LATIN SMALL LIGATURE FI decomposes only in NFKD.
        assert_eq!(NFD.properties("ﬁ".as_bytes()).decomposition(), None);
        assert_eq!(
            NFKD.properties("ﬁ".as_bytes()).decomposition(),
            Some("fi".as_bytes())
        );
    }

    #[test]
    fn first_boundary() {
        assert_eq!(NFD.first_boundary(b""), -1);
        // A starter is a boundary before itself.
        assert_eq!(NFD.first_boundary("a".as_bytes()), 0);
        // A combining mark then a starter: the boundary is before the starter.
        assert_eq!(NFD.first_boundary("\u{301}a".as_bytes()), 2);
        assert_eq!(NFD.first_boundary("\u{301}\u{302}".as_bytes()), -1);
    }
}
