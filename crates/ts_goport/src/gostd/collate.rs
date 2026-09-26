//! Go `golang.org/x/text/collate` v0.38.0 and the parts of
//! `golang.org/x/text/internal/colltab` that `Collator.CompareString` uses.
//! The only caller is `ls/lsutil/organizeimports.rs`
//! (`getOrganizeImportsUnicodeStringComparer`).
//!
//! PORT: Go's `tables.go` is 5 MB of source (1.25 MB of data) for 95 locales.
//! This file holds a generated subset of it instead (the data section at the
//! end). The subset is the root table (`und`, which 15 locales use, among
//! them `en`) for these runes:
//!
//! - U+0000-U+07FF: every 1- and 2-byte UTF-8 rune.
//! - U+2080-U+20BF and U+FF00-U+FF3F: the two 3-byte trie rows that
//!   `NewNumericWeighter` reads (subscript and fullwidth digits).
//!
//! Elements, expansions and contractions are Go's values, renumbered. The
//! generator checks every rune against Go's full table and compares
//! `CompareString` for 8 option sets on 30,020 string pairs. Where Go would
//! need data outside the subset (another rune, another locale table, other
//! `norm` data), the code calls `unported!`. It never guesses a weight.
//!
//! PORT: Go keeps verbatim `[]byte` and `string` copies of the lookup, scan
//! and append functions. Rust has one `&[u8]` version; a `&str` is passed as
//! its bytes.

use crate::locale::language::{self, Confidence, Language, Region, Script, Tag};
use crate::prelude::*;
use std::sync::LazyLock;

// ---------------------------------------------------------------------------
// internal/colltab/collelem.go
// ---------------------------------------------------------------------------

// Go: internal/colltab/collelem.go:18 Level
/// Level identifies the collation comparison level.
/// The primary level corresponds to the basic sorting of text.
/// The secondary level corresponds to accents and related linguistic elements.
/// The tertiary level corresponds to casing and related concepts.
/// The quaternary level is derived from the other levels by the
/// various algorithms for handling variable elements.
pub type Level = usize;

// Go: internal/colltab/collelem.go:20 (Level constants)
pub const PRIMARY: Level = 0;
pub const SECONDARY: Level = 1;
pub const TERTIARY: Level = 2;
pub const QUATERNARY: Level = 3;
pub const IDENTITY: Level = 4;
pub const NUM_LEVELS: usize = 5;

// Go: internal/colltab/collelem.go:30
const DEFAULT_SECONDARY: i32 = 0x20;
const DEFAULT_TERTIARY: i32 = 0x2;
const MAX_TERTIARY: u8 = 0x1F;
pub const MAX_QUATERNARY: i32 = 0x1FFFFF; // 21 bits.

// Go: internal/colltab/collelem.go:41 Elem
/// Elem is a representation of a collation element. This API provides ways to encode
/// and decode Elems. Implementations of collation tables may use values greater
/// or equal to PrivateUse for their own purposes.  However, these should never be
/// returned by AppendNext.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Elem(pub u32);

// Go: internal/colltab/collelem.go:43
const MAX_CE: u32 = 0xAFFFFFFF;
const MAX_CONTRACT: u32 = 0xDFFFFFFF;
const MAX_EXPAND: u32 = 0xEFFFFFFF;

// Go: internal/colltab/collelem.go:53 ceType
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CeType {
    /// ceNormal includes implicits (ce == 0)
    Normal,
    /// rune can be a start of a contraction
    ContractionIndex,
    /// rune expands into a sequence of collation elements
    ExpansionIndex,
    /// rune expands using NFKC decomposition
    Decompose,
}

// Go: internal/colltab/collelem.go:100
// For normal collation elements, we assume that a collation element either has
// a primary or non-default secondary value, not both.
// Collation elements with a primary value are of the form
//
//	01pppppp pppppppp ppppppp0 ssssssss
//	  - p* is primary collation value
//	  - s* is the secondary collation value
//	00pppppp pppppppp ppppppps sssttttt, where
//	  - p* is primary collation value
//	  - s* offset of secondary from default value.
//	  - t* is the tertiary collation value
//	100ttttt cccccccc pppppppp pppppppp
//	  - t* is the tertiar collation value
//	  - c* is the canonical combining class
//	  - p* is the primary collation value
//
// Collation elements with a secondary value are of the form
//
//	1010cccc ccccssss ssssssss tttttttt, where
//	  - c* is the canonical combining class
//	  - s* is the secondary collation value
//	  - t* is the tertiary collation value
//	11qqqqqq qqqqqqqq qqqqqqq0 00000000
//	  - q* quaternary value
const CE_TYPE_MASK: u32 = 0xC0000000;
const CE_TYPE_MASK_EXT: u32 = 0xE0000000;
const CE_IGNORE_MASK: u32 = 0xF00FFFFF;
const CE_TYPE1: u32 = 0x40000000;
const CE_TYPE2: u32 = 0x00000000;
const CE_TYPE3OR4: u32 = 0x80000000;
const CE_TYPE4: u32 = 0xA0000000;
const CE_TYPE_Q: u32 = 0xC0000000;
const IGNORE: u32 = CE_TYPE4;
const FIRST_NON_PRIMARY: u32 = 0x80000000;
const LAST_SPECIAL_PRIMARY: u32 = 0xA0000000;
const HAS_TERTIARY_MASK: u32 = 0x40000000;
const PRIMARY_VALUE_MASK: u32 = 0x3FFFFE00;
const MAX_PRIMARY_BITS: u32 = 21;
const COMPACT_PRIMARY_BITS: u32 = 16;
const MAX_SECONDARY_BITS: u32 = 12;
const MAX_TERTIARY_BITS: u32 = 8;
const MAX_CCC_BITS: u32 = 8;
const MAX_SECONDARY_COMPACT_BITS: u32 = 8;
const MAX_SECONDARY_DIFF_BITS: u32 = 4;
const MAX_TERTIARY_COMPACT_BITS: u32 = 5;
const PRIMARY_SHIFT: u32 = 9;
const COMPACT_SECONDARY_SHIFT: u32 = 5;
const MIN_COMPACT_SECONDARY: i32 = DEFAULT_SECONDARY - 4;

// Go: internal/colltab/collelem.go:128 makeImplicitCE
fn make_implicit_ce(primary: i32) -> Elem {
    Elem(CE_TYPE1 | ((primary as u32) << PRIMARY_SHIFT) | DEFAULT_SECONDARY as u32)
}

// Go: internal/colltab/collelem.go:134 MakeElem
/// MakeElem returns an Elem for the given values.  It will return an error
/// if the given combination of values is invalid.
pub fn make_elem(primary: i32, secondary: i32, tertiary: i32, ccc: u8) -> Result<Elem, String> {
    let w = primary;
    if w >= 1 << MAX_PRIMARY_BITS || w < 0 {
        return Err(format!(
            "makeCE: primary weight out of bounds: {:x} >= {:x}",
            w,
            1 << MAX_PRIMARY_BITS
        ));
    }
    let w = secondary;
    if w >= 1 << MAX_SECONDARY_BITS || w < 0 {
        return Err(format!(
            "makeCE: secondary weight out of bounds: {:x} >= {:x}",
            w,
            1 << MAX_SECONDARY_BITS
        ));
    }
    let w = tertiary;
    if w >= 1 << MAX_TERTIARY_BITS || w < 0 {
        return Err(format!(
            "makeCE: tertiary weight out of bounds: {:x} >= {:x}",
            w,
            1 << MAX_TERTIARY_BITS
        ));
    }
    let mut ce: u32;
    if primary != 0 {
        if ccc != 0 {
            if primary >= 1 << COMPACT_PRIMARY_BITS {
                return Err(format!(
                    "makeCE: primary weight with non-zero CCC out of bounds: {:x} >= {:x}",
                    primary,
                    1 << COMPACT_PRIMARY_BITS
                ));
            }
            if secondary != DEFAULT_SECONDARY {
                return Err(format!(
                    "makeCE: cannot combine non-default secondary value ({:x}) with non-zero CCC ({:x})",
                    secondary, ccc
                ));
            }
            ce = (tertiary as u32) << (COMPACT_PRIMARY_BITS + MAX_CCC_BITS);
            ce |= u32::from(ccc) << COMPACT_PRIMARY_BITS;
            ce |= primary as u32;
            ce |= CE_TYPE3OR4;
        } else if tertiary == DEFAULT_TERTIARY {
            if secondary >= 1 << MAX_SECONDARY_COMPACT_BITS {
                return Err(format!(
                    "makeCE: secondary weight with non-zero primary out of bounds: {:x} >= {:x}",
                    secondary,
                    1 << MAX_SECONDARY_COMPACT_BITS
                ));
            }
            ce = ((primary << (MAX_SECONDARY_COMPACT_BITS + 1)) + secondary) as u32;
            ce |= CE_TYPE1;
        } else {
            let d = secondary - DEFAULT_SECONDARY + MAX_SECONDARY_DIFF_BITS as i32;
            if d >= 1 << MAX_SECONDARY_DIFF_BITS || d < 0 {
                return Err(format!(
                    "makeCE: secondary weight diff out of bounds: {:x} < 0 || {:x} > {:x}",
                    d,
                    d,
                    1 << MAX_SECONDARY_DIFF_BITS
                ));
            }
            if tertiary >= 1 << MAX_TERTIARY_COMPACT_BITS {
                return Err(format!(
                    "makeCE: tertiary weight with non-zero primary out of bounds: {:x} > {:x}",
                    tertiary,
                    1 << MAX_TERTIARY_COMPACT_BITS
                ));
            }
            ce = ((primary << MAX_SECONDARY_DIFF_BITS) + d) as u32;
            ce = (ce << MAX_TERTIARY_COMPACT_BITS) + tertiary as u32;
        }
    } else {
        ce = ((secondary << MAX_TERTIARY_BITS) + tertiary) as u32;
        ce += u32::from(ccc) << (MAX_SECONDARY_BITS + MAX_TERTIARY_BITS);
        ce |= CE_TYPE4;
    }
    Ok(Elem(ce))
}

impl Elem {
    // Go: internal/colltab/collelem.go:62 (Elem).ctype
    fn ctype(self) -> CeType {
        let ce = self.0;
        if ce <= MAX_CE {
            return CeType::Normal;
        }
        if ce <= MAX_CONTRACT {
            CeType::ContractionIndex
        } else {
            if ce <= MAX_EXPAND {
                return CeType::ExpansionIndex;
            }
            CeType::Decompose
        }
    }

    // Go: internal/colltab/collelem.go:196 (Elem).CCC
    /// CCC returns the canonical combining class associated with the underlying character,
    /// if applicable, or 0 otherwise.
    pub fn ccc(self) -> u8 {
        let ce = self.0;
        if ce & CE_TYPE3OR4 != 0 {
            if ce & CE_TYPE4 == CE_TYPE3OR4 {
                return (ce >> 16) as u8;
            }
            return (ce >> 20) as u8;
        }
        0
    }

    // Go: internal/colltab/collelem.go:207 (Elem).Primary
    /// Primary returns the primary collation weight for ce.
    pub fn primary(self) -> i32 {
        let ce = self.0;
        if ce >= FIRST_NON_PRIMARY {
            if ce > LAST_SPECIAL_PRIMARY {
                return 0;
            }
            return i32::from(ce as u16);
        }
        ((ce & PRIMARY_VALUE_MASK) >> PRIMARY_SHIFT) as i32
    }

    // Go: internal/colltab/collelem.go:218 (Elem).Secondary
    /// Secondary returns the secondary collation weight for ce.
    pub fn secondary(self) -> i32 {
        let ce = self.0;
        match ce & CE_TYPE_MASK {
            CE_TYPE1 => i32::from(ce as u8),
            CE_TYPE2 => MIN_COMPACT_SECONDARY + ((ce >> COMPACT_SECONDARY_SHIFT) & 0xF) as i32,
            CE_TYPE3OR4 => {
                if ce < CE_TYPE4 {
                    return DEFAULT_SECONDARY;
                }
                ((ce >> 8) & 0xFFF) as i32
            }
            CE_TYPE_Q => 0,
            _ => panic!("should not reach here"),
        }
    }

    // Go: internal/colltab/collelem.go:236 (Elem).Tertiary
    /// Tertiary returns the tertiary collation weight for ce.
    pub fn tertiary(self) -> u8 {
        let ce = self.0;
        if ce & HAS_TERTIARY_MASK == 0 {
            if ce & CE_TYPE3OR4 == 0 {
                return (ce & 0x1F) as u8;
            }
            if ce & CE_TYPE4 == CE_TYPE4 {
                return ce as u8;
            }
            return ((ce >> 24) as u8) & 0x1F; // type 2
        } else if ce & CE_TYPE_MASK == CE_TYPE1 {
            return DEFAULT_TERTIARY as u8;
        }
        // ce is a quaternary value.
        0
    }

    // Go: internal/colltab/collelem.go:252 (Elem).updateTertiary
    fn update_tertiary(self, t: u8) -> Elem {
        let mut ce = self.0;
        if ce & CE_TYPE_MASK == CE_TYPE1 {
            // convert to type 4
            let mut nce = ce & PRIMARY_VALUE_MASK;
            nce |= u32::from((ce as u8).wrapping_sub(MIN_COMPACT_SECONDARY as u8))
                << COMPACT_SECONDARY_SHIFT;
            ce = nce;
        } else if ce & CE_TYPE_MASK_EXT == CE_TYPE3OR4 {
            ce &= !(u32::from(MAX_TERTIARY) << 24);
            return Elem(ce | (u32::from(t) << 24));
        } else {
            // type 2 or 4
            ce &= !u32::from(MAX_TERTIARY);
        }
        Elem(ce | u32::from(t))
    }

    // Go: internal/colltab/collelem.go:271 (Elem).Quaternary
    /// Quaternary returns the quaternary value if explicitly specified,
    /// 0 if ce == Ignore, or MaxQuaternary otherwise.
    /// Quaternary values are used only for shifted variants.
    pub fn quaternary(self) -> i32 {
        let ce = self.0;
        if ce & CE_TYPE_MASK == CE_TYPE_Q {
            return ((ce & PRIMARY_VALUE_MASK) >> PRIMARY_SHIFT) as i32;
        } else if ce & CE_IGNORE_MASK == IGNORE {
            return 0;
        }
        MAX_QUATERNARY
    }
}

// Go: internal/colltab/collelem.go:302
// For contractions, collation elements are of the form
// 110bbbbb bbbbbbbb iiiiiiii iiiinnnn, where
//   - n* is the size of the first node in the contraction trie.
//   - i* is the index of the first node in the contraction trie.
//   - b* is the offset into the contraction collation element table.
//
// See contract.go for details on the contraction trie.
const MAX_N_BITS: u32 = 4;
const MAX_TRIE_INDEX_BITS: u32 = 12;
const MAX_CONTRACT_OFFSET_BITS: u32 = 13;

// Go: internal/colltab/collelem.go:308 splitContractIndex
fn split_contract_index(ce: Elem) -> (usize, usize, usize) {
    let mut ce = ce.0;
    let n = (ce & ((1 << MAX_N_BITS) - 1)) as usize;
    ce >>= MAX_N_BITS;
    let index = (ce & ((1 << MAX_TRIE_INDEX_BITS) - 1)) as usize;
    ce >>= MAX_TRIE_INDEX_BITS;
    let offset = (ce & ((1 << MAX_CONTRACT_OFFSET_BITS) - 1)) as usize;
    (index, n, offset)
}

// Go: internal/colltab/collelem.go:321 splitExpandIndex
// For expansions, Elems are of the form 11100000 00000000 bbbbbbbb bbbbbbbb,
// where b* is the index into the expansion sequence table.
fn split_expand_index(ce: Elem) -> usize {
    usize::from(ce.0 as u16)
}

// Go: internal/colltab/collelem.go:334 splitDecompose
// Some runes can be expanded using NFKD decomposition. Instead of storing the full
// sequence of collation elements, we decompose the rune and lookup the collation
// elements for each rune in the decomposition and modify the tertiary weights.
// The Elem, in this case, is of the form 11110000 00000000 wwwwwwww vvvvvvvv, where
//   - v* is the replacement tertiary weight for the first rune,
//   - w* is the replacement tertiary weight for the second rune,
//
// Tertiary weights of subsequent runes should be replaced with maxTertiary.
// See https://www.unicode.org/reports/tr10/#Compatibility_Decompositions for more details.
fn split_decompose(ce: Elem) -> (u8, u8) {
    (ce.0 as u8, (ce.0 >> 8) as u8)
}

// Go: internal/colltab/collelem.go:338
// These constants were taken from https://www.unicode.org/versions/Unicode6.0.0/ch12.pdf.
const MIN_UNIFIED: u32 = 0x4E00;
const MAX_UNIFIED: u32 = 0x9FFF;
const MIN_COMPATIBILITY: u32 = 0xF900;
const MAX_COMPATIBILITY: u32 = 0xFAFF;

// Go: internal/colltab/collelem.go:347
const COMMON_UNIFIED_OFFSET: i32 = 0x10000;
const RARE_UNIFIED_OFFSET: i32 = 0x20000; // largest rune in common is U+FAFF
const OTHER_OFFSET: i32 = 0x50000; // largest rune in rare is U+2FA1D

// Go: internal/colltab/collelem.go:360 implicitPrimary
/// implicitPrimary returns the primary weight for the given rune
/// for which there is no entry for the rune in the collation table.
/// We take a different approach from the one specified in
/// https://unicode.org/reports/tr10/#Implicit_Weights,
/// but preserve the resulting relative ordering of the runes.
fn implicit_primary(r: u32) -> i32 {
    if unicode_is_ideographic(r) {
        if (MIN_UNIFIED..=MAX_UNIFIED).contains(&r) {
            // The most common case for CJK.
            return r as i32 + COMMON_UNIFIED_OFFSET;
        }
        if (MIN_COMPATIBILITY..=MAX_COMPATIBILITY).contains(&r) {
            // This will typically not hit. The DUCET explicitly specifies mappings
            // for all characters that do not decompose.
            return r as i32 + COMMON_UNIFIED_OFFSET;
        }
        return r as i32 + RARE_UNIFIED_OFFSET;
    }
    r as i32 + OTHER_OFFSET
}

/// Go `unicode.Is(unicode.Ideographic, r)` (Go 1.26, Unicode 15.0.0).
fn unicode_is_ideographic(r: u32) -> bool {
    const IDEOGRAPHIC: [(u32, u32); 20] = [
        (0x3006, 0x3007),
        (0x3021, 0x3029),
        (0x3038, 0x303a),
        (0x3400, 0x4dbf),
        (0x4e00, 0x9fff),
        (0xf900, 0xfa6d),
        (0xfa70, 0xfad9),
        (0x16fe4, 0x16fe4),
        (0x17000, 0x187f7),
        (0x18800, 0x18cd5),
        (0x18d00, 0x18d08),
        (0x1b170, 0x1b2fb),
        (0x20000, 0x2a6df),
        (0x2a700, 0x2b739),
        (0x2b740, 0x2b81d),
        (0x2b820, 0x2cea1),
        (0x2ceb0, 0x2ebe0),
        (0x2f800, 0x2fa1d),
        (0x30000, 0x3134a),
        (0x31350, 0x323af),
    ];
    IDEOGRAPHIC.iter().any(|&(lo, hi)| (lo..=hi).contains(&r))
}

// ---------------------------------------------------------------------------
// internal/colltab/weighter.go
// ---------------------------------------------------------------------------

// Go: internal/colltab/weighter.go:8 Weighter
/// A Weighter can be used as a source for Collator and Searcher.
/// PORT: `Start`, `StartString` and `Domain` panic in Go's `Table` and are
/// not used by `Collator.CompareString`; they are not ported.
pub trait Weighter {
    /// AppendNext appends Elems to buf corresponding to the longest match
    /// of a single character or contraction from the start of s.
    /// It returns the new buf and the number of bytes consumed.
    fn append_next(&self, buf: Vec<Elem>, s: &[u8]) -> (Vec<Elem>, usize);

    /// Top returns the highest variable primary value.
    fn top(&self) -> u32;
}

// ---------------------------------------------------------------------------
// internal/colltab/trie.go
// ---------------------------------------------------------------------------

// The trie in this file is used to associate the first full character in an
// UTF-8 string to a collation element. All but the last byte in a UTF-8 byte
// sequence are used to lookup offsets in the index table to be used for the
// next byte. The last byte is used to index into a table of collation elements.
// For a full description, see go.text/collate/build/trie.go.

// Go: internal/colltab/trie.go:15 Trie
pub struct Trie {
    /// index for first byte (0xC0-0xFF)
    pub index0: &'static [u16],
    /// index for first byte (0x00-0x7F)
    pub values0: &'static [u32],
    pub index: &'static [u16],
    pub values: &'static [u32],
}

// Go: internal/colltab/trie.go:22
const TX: u8 = 0x80; // 1000 0000
const T2: u8 = 0xC0; // 1100 0000
const T3: u8 = 0xE0; // 1110 0000
const T4: u8 = 0xF0; // 1111 0000
const T5: u8 = 0xF8; // 1111 1000

/// PORT: the subset table marks index rows that are not in the subset with
/// `SUBSET_MISSING`. Go would read a real row there.
const SUBSET_MISSING: u16 = 0xFFFF;

/// PORT: returns the trie block `i`, or stops when the subset table does not
/// hold it (a rune outside the subset).
fn subset_block(i: u16) -> u16 {
    if i == SUBSET_MISSING {
        unported!("collate tables.go (rune outside the collation subset table)");
    }
    i
}

impl Trie {
    // Go: internal/colltab/trie.go:33 (*Trie).lookupValue
    fn lookup_value(&self, n: u16, b: u8) -> Elem {
        Elem(self.values[(usize::from(subset_block(n)) << 6) + usize::from(b)])
    }

    // Go: internal/colltab/trie.go:40 (*Trie).lookup
    /// lookup returns the trie value for the first UTF-8 encoding in s and
    /// the width in bytes of this encoding. The size will be 0 if s does not
    /// hold enough bytes to complete the encoding. len(s) must be greater than 0.
    fn lookup(&self, s: &[u8]) -> (Elem, usize) {
        let c0 = s[0];
        if c0 < TX {
            return (Elem(self.values0[usize::from(c0)]), 1);
        } else if c0 < T2 {
            return (Elem(0), 1);
        } else if c0 < T3 {
            if s.len() < 2 {
                return (Elem(0), 0);
            }
            let i = self.index0[usize::from(c0)];
            let c1 = s[1];
            if c1 < TX || T2 <= c1 {
                return (Elem(0), 1);
            }
            return (self.lookup_value(i, c1), 2);
        } else if c0 < T4 {
            if s.len() < 3 {
                return (Elem(0), 0);
            }
            let mut i = self.index0[usize::from(c0)];
            let c1 = s[1];
            if c1 < TX || T2 <= c1 {
                return (Elem(0), 1);
            }
            let o = (usize::from(subset_block(i)) << 6) + usize::from(c1);
            i = self.index[o];
            let c2 = s[2];
            if c2 < TX || T2 <= c2 {
                return (Elem(0), 2);
            }
            return (self.lookup_value(i, c2), 3);
        } else if c0 < T5 {
            if s.len() < 4 {
                return (Elem(0), 0);
            }
            let mut i = self.index0[usize::from(c0)];
            let c1 = s[1];
            if c1 < TX || T2 <= c1 {
                return (Elem(0), 1);
            }
            let mut o = (usize::from(subset_block(i)) << 6) + usize::from(c1);
            i = self.index[o];
            let c2 = s[2];
            if c2 < TX || T2 <= c2 {
                return (Elem(0), 2);
            }
            o = (usize::from(subset_block(i)) << 6) + usize::from(c2);
            i = self.index[o];
            let c3 = s[3];
            if c3 < TX || T2 <= c3 {
                return (Elem(0), 3);
            }
            return (self.lookup_value(i, c3), 4);
        }
        // Illegal rune
        (Elem(0), 1)
    }
}

// ---------------------------------------------------------------------------
// internal/colltab/contract.go
// ---------------------------------------------------------------------------

// Go: internal/colltab/contract.go:11 ContractTrieSet
// For a description of ContractTrieSet, see text/collate/build/contract.go.
#[derive(Clone, Copy, Debug)]
pub struct CtEntry {
    pub l: u8,
    pub h: u8,
    pub n: u8,
    pub i: u8,
}

const fn ct(l: u8, h: u8, n: u8, i: u8) -> CtEntry {
    CtEntry { l, h, n, i }
}

pub struct ContractTrieSet(pub &'static [CtEntry]);

// Go: internal/colltab/contract.go:21 ctScanner
/// ctScanner is used to match a trie to an input sequence.
/// A contraction may match a non-contiguous sequence of bytes in an input string.
/// For example, if there is a contraction for <a, combining_ring>, it should match
/// the sequence <a, combining_cedilla, combining_ring>, as combining_cedilla does
/// not block combining_ring.
/// ctScanner does not automatically skip over non-blocking non-starters, but rather
/// retains the state of the last match and leaves it up to the user to continue
/// the match at the appropriate points.
struct CtScanner<'a> {
    states: &'static [CtEntry],
    s: &'a [u8],
    n: usize,
    index: usize,
    pindex: usize,
    done: bool,
}

impl ContractTrieSet {
    // Go: internal/colltab/contract.go:39 (ContractTrieSet).scanner
    fn scanner<'a>(&self, index: usize, n: usize, b: &'a [u8]) -> CtScanner<'a> {
        CtScanner {
            s: b,
            states: &self.0[index..],
            n,
            index: 0,
            pindex: 0,
            done: false,
        }
    }
}

// Go: internal/colltab/contract.go:57
const FINAL: u8 = 0;
const NO_INDEX: u8 = 0xFF;

impl CtScanner<'_> {
    // Go: internal/colltab/contract.go:49 (*ctScanner).result
    /// result returns the offset i and bytes consumed p so far.  If no suffix
    /// matched, i and p will be 0.
    fn result(&self) -> (usize, usize) {
        (self.index, self.pindex)
    }

    // Go: internal/colltab/contract.go:64 (*ctScanner).scan
    /// scan matches the longest suffix at the current location in the input
    /// and returns the number of bytes consumed.
    fn scan(&mut self, mut p: usize) -> usize {
        let mut pr = p; // the p at the rune start
        let str = self.s;
        let (mut states, mut n) = (self.states, self.n);
        let mut i = 0;
        while i < n && p < str.len() {
            let e = states[i];
            let c = str[p];
            // TODO: a significant number of contractions are of a form that
            // cannot match discontiguous UTF-8 in a normalized string. We could let
            // a negative value of e.n mean that we can set s.done = true and avoid
            // the need for additional matches.
            if c >= e.l {
                if e.l == c {
                    p += 1;
                    if e.i != NO_INDEX {
                        self.index = usize::from(e.i);
                        self.pindex = p;
                    }
                    if e.n != FINAL {
                        (i, states, n) = (0, &states[usize::from(e.h) + n..], usize::from(e.n));
                        if p >= str.len() || utf8_rune_start(str[p]) {
                            (self.states, self.n, pr) = (states, n, p);
                        }
                    } else {
                        self.done = true;
                        return p;
                    }
                    continue;
                } else if e.n == FINAL && c <= e.h {
                    p += 1;
                    self.done = true;
                    self.index = usize::from(c - e.l) + usize::from(e.i);
                    self.pindex = p;
                    return p;
                }
            }
            i += 1;
        }
        pr
    }
}

// ---------------------------------------------------------------------------
// internal/colltab/table.go
// ---------------------------------------------------------------------------

// Go: internal/colltab/table.go:14 Table
/// Table holds all collation data for a given collation ordering.
pub struct Table {
    /// main trie
    pub index: Trie,

    // expansion info
    pub expand_elem: &'static [u32],

    // contraction info
    pub contract_tries: ContractTrieSet,
    pub contract_elem: &'static [u32],
    pub max_contract_len: i32,
    pub variable_top: u32,
}

impl Weighter for Table {
    // Go: internal/colltab/table.go:27 (*Table).AppendNext
    // Go: internal/colltab/table.go:31 (*Table).AppendNextString
    fn append_next(&self, w: Vec<Elem>, s: &[u8]) -> (Vec<Elem>, usize) {
        self.append_next_src(w, s)
    }

    // Go: internal/colltab/table.go:50 (*Table).Top
    fn top(&self) -> u32 {
        self.variable_top
    }
}

impl Table {
    // Go: internal/colltab/table.go:100 (*Table).appendNext
    /// appendNext appends the weights corresponding to the next rune or
    /// contraction in s.  If a contraction is matched to a discontinuous
    /// sequence of runes, the weights for the interstitial runes are
    /// appended as well.  It returns a new slice that includes the appended
    /// weights and the number of bytes consumed from s.
    /// PORT: Go `source` is the byte slice `src` (see the module note).
    fn append_next_src(&self, mut w: Vec<Elem>, src: &[u8]) -> (Vec<Elem>, usize) {
        let (mut ce, mut sz) = self.index.lookup(src);
        let tp = ce.ctype();
        if tp == CeType::Normal {
            if ce.0 == 0 {
                let (r, _) = utf8_decode_rune(src);
                const FIRST_HANGUL: u32 = 0xAC00;
                const LAST_HANGUL: u32 = 0xD7A3;
                if (FIRST_HANGUL..=LAST_HANGUL).contains(&r) {
                    // PORT: Go decomposes the syllable with `norm.NFD` and looks
                    // up the jamo. Hangul is outside the subset table, so the
                    // lookup above has already stopped.
                    unported!("norm.NFD.AppendString (Hangul)");
                }
                ce = make_implicit_ce(implicit_primary(r));
            }
            w.push(ce);
        } else if tp == CeType::ExpansionIndex {
            w = self.append_expansion(w, ce);
        } else if tp == CeType::ContractionIndex {
            let suffix = &src[sz..];
            let n;
            (w, n) = self.match_contraction(w, ce, suffix);
            sz += n;
        } else if tp == CeType::Decompose {
            // Decompose using NFKD and replace tertiary weights.
            let (t1, t2) = split_decompose(ce);
            let mut i = w.len();
            let mut nfkd = norm_nfkd_decomposition(src);
            while !nfkd.is_empty() {
                let p;
                (w, p) = self.append_next_src(w, nfkd);
                nfkd = &nfkd[p..];
            }
            w[i] = w[i].update_tertiary(t1);
            i += 1;
            if i < w.len() {
                w[i] = w[i].update_tertiary(t2);
                i += 1;
                while i < w.len() {
                    w[i] = w[i].update_tertiary(MAX_TERTIARY);
                    i += 1;
                }
            }
        }
        (w, sz)
    }

    // Go: internal/colltab/table.go:154 (*Table).appendExpansion
    fn append_expansion(&self, mut w: Vec<Elem>, ce: Elem) -> Vec<Elem> {
        let mut i = split_expand_index(ce);
        let n = self.expand_elem[i] as usize;
        i += 1;
        for &ce in &self.expand_elem[i..i + n] {
            w.push(Elem(ce));
        }
        w
    }

    // Go: internal/colltab/table.go:164 (*Table).matchContraction
    // Go: internal/colltab/table.go:222 (*Table).matchContractionString
    fn match_contraction(&self, mut w: Vec<Elem>, ce: Elem, suffix: &[u8]) -> (Vec<Elem>, usize) {
        let (index, n, offset) = split_contract_index(ce);

        let mut scan = self.contract_tries.scanner(index, n, suffix);
        let p = scan.scan(0);

        if !scan.done && p < suffix.len() && suffix[p] >= UTF8_RUNE_SELF {
            // By now we should have filtered most cases.
            // PORT: Go reads `norm.NFD.Properties` of the rune at p. With a
            // lead CCC of 0 it only adds the rune size to p, which nothing
            // reads afterwards. A non-starter starts Go's search for a
            // discontiguous match (`FirstBoundary`, more `Properties`, the
            // interstitial runes in `buf`). That needs `norm` data this port
            // does not have.
            if norm_nfd_lead_ccc(&suffix[p..]) != 0 {
                unported!("norm.NFD.FirstBoundary (non-starter after a contraction start)");
            }
        }
        // Append weights for the matched contraction, which may be an expansion.
        let (i, n) = scan.result();
        let ce = Elem(self.contract_elem[i + offset]);
        if ce.ctype() == CeType::Normal {
            w.push(ce);
        } else {
            w = self.append_expansion(w, ce);
        }
        // Append weights for the runes in the segment not part of the contraction.
        // PORT: Go's `buf[:bufp]` is empty unless the unported branch above
        // ran, so there are no runes to append here.
        (w, n)
    }
}

// ---------------------------------------------------------------------------
// internal/colltab/iter.go
// ---------------------------------------------------------------------------

// Go: internal/colltab/iter.go:10 Iter
/// An Iter incrementally converts chunks of the input text to collation
/// elements, while ensuring that the collation elements are in normalized order
/// (that is, they are in the order as if the input text were normalized first).
/// PORT: Go keeps the input string; this keeps a reused copy of its bytes.
pub struct Iter {
    pub weighter: Rc<dyn Weighter>,
    pub elems: Vec<Elem>,
    /// N is the number of elements in Elems that will not be reordered on
    /// subsequent iterations, N <= len(Elems).
    pub n: usize,

    str: Vec<u8>,
    // Because the Elems buffer may contain collation elements that are needed
    // for look-ahead, we need two positions in the text (bytes or str): one for
    // the end position in the text for the current iteration and one for the
    // start of the next call to appendNext.
    /// end position in text corresponding to N.
    p_end: usize,
    /// pEnd <= pNext.
    p_next: usize,
}

// Go: internal/colltab/iter.go:163 maxCombiningCharacters
const MAX_COMBINING_CHARACTERS: usize = 30;

impl Iter {
    fn new(weighter: Rc<dyn Weighter>) -> Iter {
        Iter {
            weighter,
            elems: Vec::with_capacity(512),
            n: 0,
            str: Vec::new(),
            p_end: 0,
            p_next: 0,
        }
    }

    // Go: internal/colltab/iter.go:29 (*Iter).Reset
    /// Reset sets the position in the current input text to p and discards any
    /// results obtained so far.
    pub fn reset(&mut self, p: usize) {
        self.elems.clear();
        self.n = 0;
        self.p_end = p;
        self.p_next = p;
    }

    // Go: internal/colltab/iter.go:66 (*Iter).SetInputString
    /// SetInputString resets i to input s.
    pub fn set_input_string(&mut self, s: &str) {
        self.str.clear();
        self.str.extend_from_slice(s.as_bytes());
        self.reset(0);
    }

    // Go: internal/colltab/iter.go:72 (*Iter).done
    fn done(&self) -> bool {
        self.p_next >= self.str.len()
    }

    // Go: internal/colltab/iter.go:76 (*Iter).appendNext
    fn append_next(&mut self) -> bool {
        if self.done() {
            return false;
        }
        let elems = std::mem::take(&mut self.elems);
        let (elems, mut sz) = self.weighter.append_next(elems, &self.str[self.p_next..]);
        self.elems = elems;
        if sz == 0 {
            sz = 1;
        }
        self.p_next += sz;
        true
    }

    // Go: internal/colltab/iter.go:98 (*Iter).Next
    /// Next appends Elems to the internal array. On each iteration, it will either
    /// add starters or modifiers. In the majority of cases, an Elem with a primary
    /// value > 0 will have a CCC of 0. The CCC values of collation elements are also
    /// used to detect if the input string was not normalized and to adjust the
    /// result accordingly.
    pub fn next(&mut self) -> bool {
        if self.n == self.elems.len() && !self.append_next() {
            return false;
        }

        // Check if the current segment starts with a starter.
        let mut prev_ccc = self.elems[self.elems.len() - 1].ccc();
        if prev_ccc == 0 {
            self.n = self.elems.len();
            self.p_end = self.p_next;
            return true;
        } else if self.elems[self.n].ccc() == 0 {
            // set i.N to only cover part of i.Elems for which prevCCC == 0 and
            // use rest for the next call to next.
            self.n += 1;
            while self.n < self.elems.len() && self.elems[self.n].ccc() == 0 {
                self.n += 1;
            }
            self.p_end = self.p_next;
            return true;
        }

        // The current (partial) segment starts with modifiers. We need to collect
        // all successive modifiers to ensure that they are normalized.
        loop {
            let p = self.elems.len();
            self.p_end = self.p_next;
            if !self.append_next() {
                break;
            }

            let ccc = self.elems[p].ccc();
            if ccc == 0 || self.elems.len() - self.n > MAX_COMBINING_CHARACTERS {
                // Leave the starter for the next iteration. This ensures that we
                // do not return sequences of collation elements that cross two
                // segments.
                //
                // TODO: handle large number of combining characters by fully
                // normalizing the input segment before iteration. This ensures
                // results are consistent across the text repo.
                self.n = p;
                return true;
            } else if ccc < prev_ccc {
                self.do_norm(p, ccc); // should be rare, never occurs for NFD and FCC.
            } else {
                prev_ccc = ccc;
            }
        }

        let done = self.elems.len() != self.n;
        self.n = self.elems.len();
        done
    }

    // Go: internal/colltab/iter.go:170 (*Iter).doNorm
    /// doNorm reorders the collation elements in i.Elems.
    /// It assumes that blocks of collation elements added with appendNext
    /// either start and end with the same CCC or start with CCC == 0.
    /// This allows for a single insertion point for the entire block.
    /// The correctness of this assumption is verified in builder.go.
    fn do_norm(&mut self, mut p: usize, ccc: u8) {
        let n = self.elems.len();
        let k = p;
        p -= 1;
        while p > self.n && ccc < self.elems[p - 1].ccc() {
            p -= 1;
        }
        self.elems.extend_from_within(p..k);
        self.elems.copy_within(k.., p);
        self.elems.truncate(n);
    }
}

// ---------------------------------------------------------------------------
// internal/colltab/numeric.go
// ---------------------------------------------------------------------------

// Go: internal/colltab/numeric.go:18 NewNumericWeighter
/// NewNumericWeighter wraps w to replace individual digits to sort based on their
/// numeric value.
///
/// Weighter w must have a free primary weight after the primary weight for 9.
/// If this is not the case, numeric value will sort at the same primary level
/// as the first primary sorting after 9.
pub fn new_numeric_weighter(w: Rc<dyn Weighter>) -> Rc<dyn Weighter> {
    let get_elem = |s: &str| -> Elem {
        let (elems, _) = w.append_next(Vec::new(), s.as_bytes());
        elems[0]
    };
    let nine = get_elem("9");

    // Numbers should order before zero, but the DUCET has no room for this.
    // TODO: move before zero once we use fractional collation elements.
    let ns = make_elem(
        nine.primary() + 1,
        nine.secondary(),
        i32::from(nine.tertiary()),
        0,
    )
    .unwrap_or_default();

    Rc::new(NumericWeighter {
        // We assume that w sorts digits of different kinds in order of numeric
        // value and that the tertiary weight order is preserved.
        //
        // TODO: evaluate whether it is worth basing the ranges on the Elem
        // encoding itself once the move to fractional weights is complete.
        zero: get_elem("0"),
        zero_special_lo: get_elem("\u{FF10}"), // U+FF10 FULLWIDTH DIGIT ZERO
        zero_special_hi: get_elem("\u{2080}"), // U+2080 SUBSCRIPT ZERO
        nine,
        nine_special_hi: get_elem("\u{2089}"), // U+2089 SUBSCRIPT NINE
        number_start: ns,
        weighter: w.clone(),
    })
}

// Go: internal/colltab/numeric.go:48 numericWeighter
/// A numericWeighter translates a stream of digits into a stream of weights
/// representing the numeric value.
struct NumericWeighter {
    weighter: Rc<dyn Weighter>,

    // The Elems below all demarcate boundaries of specific ranges. With the
    // current element encoding digits are in two ranges: normal (default
    // tertiary value) and special. For most languages, digits have collation
    // elements in the normal range.
    //
    // Note: the range tests are very specific for the element encoding used by
    // this implementation. The tests in collate_test.go are designed to fail
    // if this code is not updated when an encoding has changed.
    /// normal digit zero
    zero: Elem,
    /// special digit zero, low tertiary value
    zero_special_lo: Elem,
    /// special digit zero, high tertiary value
    zero_special_hi: Elem,
    /// normal digit nine
    nine: Elem,
    /// special digit nine
    nine_special_hi: Elem,
    number_start: Elem,
}

impl Weighter for NumericWeighter {
    // Go: internal/colltab/numeric.go:70 (*numericWeighter).AppendNext
    // Go: internal/colltab/numeric.go:96 (*numericWeighter).AppendNextString
    /// AppendNext calls the namesake of the underlying weigher, but replaces single
    /// digits with weights representing their value.
    /// PORT: Go passes `buf` and keeps it in `nc.elems` while the callee
    /// appends to a shared backing array. Here the callee gets a copy.
    fn append_next(&self, buf: Vec<Elem>, s: &[u8]) -> (Vec<Elem>, usize) {
        let (ce, mut n) = self.weighter.append_next(buf.clone(), s);
        let mut nc = NumberConverter {
            elems: buf,
            w: self,
            n_digits: 0,
            len_index: 0,
            s,
        };
        let (is_zero, ok) = nc.check_next_digit(&ce);
        if !ok {
            return (ce, n);
        }
        // ce might have been grown already, so take it instead of buf.
        let old_len = nc.elems.len();
        nc.init(ce, old_len, is_zero);
        while n < s.len() {
            let (ce, sz) = self.weighter.append_next(nc.elems.clone(), &s[n..]);
            nc.s = s;
            n += sz;
            if !nc.update(ce) {
                break;
            }
        }
        (nc.result(), n)
    }

    fn top(&self) -> u32 {
        self.weighter.top()
    }
}

// Go: internal/colltab/numeric.go:119 numberConverter
struct NumberConverter<'a> {
    w: &'a NumericWeighter,

    elems: Vec<Elem>,
    n_digits: i32,
    len_index: usize,

    /// PORT: Go `s` and `b`; the input bytes.
    s: &'a [u8],
}

// Go: internal/colltab/numeric.go:215 maxDigits
/// We currently support a maximum of about 2M digits (the number of primary
/// values). Such numbers will compare correctly against small numbers, but their
/// comparison against other large numbers is undefined.
///
/// TODO: define a proper fallback, such as comparing large numbers textually or
/// actually allowing numbers of unlimited length.
///
/// TODO: cap this to a lower number (like 100) and maybe allow a larger number
/// in an option?
const MAX_DIGITS: i32 = (1 << MAX_PRIMARY_BITS) - 1;

impl NumberConverter<'_> {
    // Go: internal/colltab/numeric.go:132 (*numberConverter).init
    /// init completes initialization of a numberConverter and prepares it for adding
    /// more digits. elems is assumed to have a digit starting at oldLen.
    fn init(&mut self, mut elems: Vec<Elem>, old_len: usize, is_zero: bool) {
        // Insert a marker indicating the start of a number and a placeholder
        // for the number of digits.
        if is_zero {
            elems.truncate(old_len);
            elems.push(self.w.number_start);
            elems.push(Elem(0));
        } else {
            elems.push(Elem(0));
            elems.push(Elem(0));
            let len = elems.len();
            elems.copy_within(old_len..len - 2, old_len + 2);
            elems[old_len] = self.w.number_start;
            elems[old_len + 1] = Elem(0);

            self.n_digits = 1;
        }
        self.elems = elems;
        self.len_index = old_len + 1;
    }

    // Go: internal/colltab/numeric.go:151 (*numberConverter).checkNextDigit
    /// checkNextDigit reports whether bufNew adds a single digit relative to the old
    /// buffer. If it does, it also reports whether this digit is zero.
    fn check_next_digit(&self, buf_new: &[Elem]) -> (bool, bool) {
        if self.elems.len() >= buf_new.len() {
            return (false, false);
        }
        let e = buf_new[self.elems.len()];
        if e < self.w.zero_special_lo || self.w.nine < e {
            // Not a number.
            return (false, false);
        }
        let is_zero;
        if e < self.w.zero {
            if e > self.w.nine_special_hi {
                // Not a number.
                return (false, false);
            }
            if !self.is_digit() {
                return (false, false);
            }
            is_zero = e <= self.w.zero_special_hi;
        } else {
            // This is the common case if we encounter a digit.
            is_zero = e == self.w.zero;
        }
        // Test the remaining added collation elements have a zero primary value.
        let n = buf_new.len() - self.elems.len();
        if n > 1 {
            for i in self.elems.len() + 1..buf_new.len() {
                if buf_new[i].primary() != 0 {
                    return (false, false);
                }
            }
            // In some rare cases, collation elements will encode runes in
            // unicode.No as a digit. For example Ethiopic digits (U+1369 - U+1371)
            // are not in Nd. Also some digits that clearly belong in unicode.No,
            // like U+0C78 TELUGU FRACTION DIGIT ZERO FOR ODD POWERS OF FOUR, have
            // collation elements indistinguishable from normal digits.
            // Unfortunately, this means we need to make this check for nearly all
            // non-Latin digits.
            //
            // TODO: check the performance impact and find something better if it is
            // an issue.
            if !self.is_digit() {
                return (false, false);
            }
        }
        (is_zero, true)
    }

    // Go: internal/colltab/numeric.go:197 (*numberConverter).isDigit
    fn is_digit(&self) -> bool {
        let (r, _) = utf8_decode_rune(self.s);
        unicode_is_nd(r)
    }

    // Go: internal/colltab/numeric.go:217 (*numberConverter).update
    fn update(&mut self, elems: Vec<Elem>) -> bool {
        let (is_zero, ok) = self.check_next_digit(&elems);
        if self.n_digits == 0 && is_zero {
            return true;
        }
        self.elems = elems;
        if !ok {
            return false;
        }
        self.n_digits += 1;
        self.n_digits < MAX_DIGITS
    }

    // Go: internal/colltab/numeric.go:232 (*numberConverter).result
    /// result fills in the length element for the digit sequence and returns the
    /// completed collation elements.
    fn result(mut self) -> Vec<Elem> {
        let e =
            make_elem(self.n_digits, DEFAULT_SECONDARY, DEFAULT_TERTIARY, 0).unwrap_or_default();
        self.elems[self.len_index] = e;
        self.elems
    }
}

// ---------------------------------------------------------------------------
// internal/colltab/colltab.go
// ---------------------------------------------------------------------------

// Go: internal/colltab/colltab.go:25 MatchLang
/// MatchLang finds the index of t in tags, using a matching algorithm used for
/// collation and search. tags[0] must be language.Und, the remaining tags should
/// be sorted alphabetically.
///
/// Language matching for collation and search is different from the matching
/// defined by language.Matcher: the (inferred) base language must be an exact
/// match for the relevant fields. For example, "gsw" should not match "de".
/// Also the parent relation is different, as a parent may have a different
/// script. So usually the parent of zh-Hant is und, whereas for MatchLang it is
/// zh.
/// PORT: the language port has no `Compose`, `Parent` or `TypeForKey` for
/// tags with a region, variants or extensions. Such tags stop with
/// `unported!`. For the other tags the steps below are Go's.
pub fn match_lang(t: &Tag, tags: &[Tag]) -> usize {
    // Canonicalize the values, including collapsing macro languages.
    let mut t = canonicalize_all(t);
    if t.region_id.0 != 0 || !t.str.is_empty() {
        unported!("colltab.MatchLang (tag with a region, variant or extension)");
    }

    let (base, conf) = tag_base(&t);
    // Estimate the base language, but only use high-confidence values.
    if conf < Confidence::High {
        // The root locale supports "search" and "standard". We assume that any
        // implementation will only use one of both.
        return 0;
    }

    // Maximize base and script and normalize the tag.
    // PORT: the region branch of Go is behind the check above.
    // Set the maximized base language.
    t = raw_compose(base, t.script_id, Region(0));

    // Find start index of the language tag.
    let base_str = base.string();
    let start = 1 + tags[1..].partition_point(|tag| base_str > tag.lang_id.string());
    if start < tags.len() && tags[start].lang_id != base {
        return 0;
    }

    // Besides the base language, script and region, only the collation type and
    // the custom variant defined in the 'u' extension are used to distinguish a
    // locale.
    // Strip all variants and extensions and add back the custom variant.
    let tdef = raw_compose(t.lang_id, t.script_id, t.region_id);
    let tdef = set_type_for_key(&tdef, "va", &type_for_key(&t, "va"));

    // First search for a specialized collation type, if present.
    let mut try_ = vec![tdef.clone()];
    let co = type_for_key(&t, "co");
    if !co.is_empty() {
        let tco = set_type_for_key(&tdef, "co", &co);
        try_ = vec![tco, tdef];
    }

    for mut tx in try_ {
        while tx != Tag::UND {
            for (i, t) in tags[start..].iter().enumerate() {
                if t.lang_id != base {
                    break;
                }
                if tx == *t {
                    return start + i;
                }
            }
            tx = parent(&tx);
        }
    }
    0
}

// Go: internal/colltab/colltab.go:91 parent
/// parent computes the structural parent. This means inheritance may change
/// script. So, unlike the CLDR parent, parent(zh-Hant) == zh.
fn parent(t: &Tag) -> Tag {
    if !type_for_key(t, "va").is_empty() {
        return set_type_for_key(t, "va", "");
    }
    let mut result = Tag::UND;
    let (b, s, r) = (t.lang_id, t.script_id, t.region_id);
    if r.0 != 0 {
        result = raw_compose(b, s, Region(0));
    } else if s.0 != 0 {
        result = raw_compose(b, Script(0), Region(0));
    } else if b.0 != 0 {
        result = raw_compose(Language(0), Script(0), Region(0));
    }
    result
}

// Go: language/language.go:188 (CanonType).Canonicalize (with language.All)
fn canonicalize_all(t: &Tag) -> Tag {
    let (mut tag, changed) = language::canonicalize(language::ALL, t.clone());
    if changed {
        tag.remake_string();
    }
    tag
}

// Go: language/language.go:246 (Tag).Base
/// Base returns the base language of the language tag. If the base language is
/// unspecified, an attempt will be made to infer it from the context.
/// It uses a variant of CLDR's Add Likely Subtags algorithm. This is subject to change.
fn tag_base(t: &Tag) -> (Language, Confidence) {
    if t.lang_id.0 != 0 {
        return (t.lang_id, Confidence::Exact);
    }
    let mut c = Confidence::High;
    if t.script_id.0 == 0 && !region_is_country(t.region_id) {
        c = Confidence::Low;
    }
    let (tag, err) = t.maximize();
    if err.is_none() && tag.lang_id.0 != 0 {
        return (tag.lang_id, c);
    }
    (Language(0), Confidence::No)
}

// Go: internal/language/language.go:530 (Region).IsCountry
// PORT: only the zero region reaches this (see `match_lang`); it is not a
// country.
fn region_is_country(r: Region) -> bool {
    if r.0 == 0 {
        return false;
    }
    unported!("language.Region.IsCountry")
}

// Go: language/language.go Raw.Compose(Base, Script, Region)
// PORT: `language.Raw.Compose` with a base, script and region and no
// variants or extensions. `match_lang` and `parent` only pass tags without
// extensions.
fn raw_compose(b: Language, s: Script, r: Region) -> Tag {
    Tag {
        lang_id: b,
        script_id: s,
        region_id: r,
        ..Tag::UND
    }
}

// Go: language/language.go:419 (Tag).TypeForKey
// PORT: a tag without variants or extensions has no types, so Go returns "".
// Other tags stop here.
fn type_for_key(t: &Tag, _key: &str) -> String {
    if t.str.is_empty() {
        return String::new();
    }
    unported!("language.Tag.TypeForKey")
}

// Go: language/language.go:437 (Tag).SetTypeForKey
// PORT: removing a type from a tag without extensions returns the tag. Other
// uses stop here.
fn set_type_for_key(t: &Tag, _key: &str, value: &str) -> Tag {
    if value.is_empty() && t.str.is_empty() {
        return t.clone();
    }
    unported!("language.Tag.SetTypeForKey")
}

// ---------------------------------------------------------------------------
// collate/index.go
// ---------------------------------------------------------------------------

// Go: collate/index.go:29 tableIndex
/// tableIndex holds information for constructing a table
/// for a certain locale based on the main table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TableIndex {
    lookup_offset: u32,
    values_offset: u32,
}

// Go: collate/index.go:11 getTable
/// PORT: the subset holds only the und table, stored at offset 0 of
/// `SUBSET_LOOKUP` and `SUBSET_VALUES` (Go: `blockSize*t.lookupOffset` and
/// `blockSize*t.valuesOffset` into the full arrays). Locales with another
/// table stop here.
fn get_table(t: TableIndex) -> Table {
    if t != LOCALES[0] {
        unported!("collate tables.go (locale table outside the collation subset table)");
    }
    Table {
        index: Trie {
            index0: &SUBSET_LOOKUP[..],
            values0: &SUBSET_VALUES[..],
            index: &SUBSET_LOOKUP[..],
            values: &SUBSET_VALUES[..],
        },
        expand_elem: &SUBSET_EXPAND_ELEM[..],
        contract_tries: ContractTrieSet(&SUBSET_CT_ENTRIES[..]),
        contract_elem: &SUBSET_CONTRACT_ELEM[..],
        max_contract_len: 18,
        variable_top: VAR_TOP,
    }
}

// ---------------------------------------------------------------------------
// collate/option.go
// ---------------------------------------------------------------------------

// Go: collate/option.go:221 alternateHandling
/// alternateHandling identifies the various ways in which variables are handled.
/// A rune with a primary weight lower than the variable top is considered a
/// variable.
/// See https://www.unicode.org/reports/tr10/#Variable_Weighting for details.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum AlternateHandling {
    /// altNonIgnorable turns off special handling of variables.
    #[default]
    NonIgnorable,

    /// altBlanked sets variables and all subsequent primary ignorables to be
    /// ignorable at all levels. This is identical to removing all variables
    /// and subsequent primary ignorables from the input.
    Blanked,

    /// altShifted sets variables to be ignorable for levels one through three and
    /// adds a fourth level based on the values of the ignored levels.
    Shifted,

    /// altShiftTrimmed is a slight variant of altShifted that is used to
    /// emulate POSIX.
    ShiftTrimmed,
}

// Go: collate/option.go:37 Option
/// An Option is used to change the behavior of a Collator. Options override the
/// settings passed through the locale identifier.
/// PORT: Go `collate.Option`; renamed so it does not shadow Rust `Option`.
#[derive(Clone, Copy)]
pub struct CollateOption {
    priority: i32,
    f: fn(&mut Options),
}

// Go: collate/option.go:56 options
pub struct Options {
    /// ignore specifies which levels to ignore.
    ignore: [bool; NUM_LEVELS],

    /// caseLevel is true if there is an additional level of case matching
    /// between the secondary and tertiary levels.
    case_level: bool,

    /// backwards specifies the order of sorting at the secondary level.
    /// This option exists predominantly to support reverse sorting of accents in French.
    backwards: bool,

    /// numeric specifies whether any sequence of decimal digits (category is Nd)
    /// is sorted at a primary level with its numeric value.
    /// For example, "A-21" < "A-123".
    /// This option is set by wrapping the main Weighter with NewNumericWeighter.
    numeric: bool,

    /// alternate specifies an alternative handling of variables.
    alternate: AlternateHandling,

    /// variableTop is the largest primary value that is considered to be
    /// variable.
    #[allow(dead_code)]
    variable_top: u32,

    t: Rc<dyn Weighter>,
    // PORT: Go `f norm.Form` (always `norm.NFD`) is not read by
    // `CompareString`; it is not ported.
}

// Go: collate/option.go:16 newCollator
/// newCollator creates a new collator with default options configured.
fn new_collator(t: Rc<dyn Weighter>) -> Collator {
    // Initialize a collator with default options.
    let mut ignore = [false; NUM_LEVELS];
    ignore[QUATERNARY] = true;
    ignore[IDENTITY] = true;
    // TODO: store vt in tags or remove.
    let variable_top = t.top();
    Collator {
        options: Options {
            ignore,
            case_level: false,
            backwards: false,
            numeric: false,
            alternate: AlternateHandling::NonIgnorable,
            variable_top,
            t: t.clone(),
        },
        iter: [CollIter::new(t.clone()), CollIter::new(t)],
    }
}

impl Options {
    // Go: collate/option.go:86 (*options).setOptions
    // PORT: Go's `sort.Sort` is an insertion sort (stable) for up to 12
    // options; `sort_by_key` is stable.
    fn set_options(&mut self, mut opts: Vec<CollateOption>) {
        opts.sort_by_key(|o| o.priority);
        for x in &opts {
            (x.f)(self);
        }
    }

    // Go: collate/option.go:102 (*options).setFromTag
    fn set_from_tag(&mut self, t: &Tag) {
        self.case_level = ldml_bool(t, self.case_level, "kc");
        self.backwards = ldml_bool(t, self.backwards, "kb");
        self.numeric = ldml_bool(t, self.numeric, "kn");

        // Extract settings from the BCP47 u extension.
        match type_for_key(t, "ks").as_str() {
            // strength
            "level1" => {
                self.ignore[SECONDARY] = true;
                self.ignore[TERTIARY] = true;
            }
            "level2" => {
                self.ignore[TERTIARY] = true;
            }
            "level3" | "" => {
                // The default.
            }
            "level4" => {
                self.ignore[QUATERNARY] = false;
            }
            "identic" => {
                self.ignore[QUATERNARY] = false;
                self.ignore[IDENTITY] = false;
            }
            _ => {}
        }

        match type_for_key(t, "ka").as_str() {
            "shifted" => self.alternate = AlternateHandling::Shifted,
            // The following two types are not official BCP47, but we support them to
            // give access to this otherwise hidden functionality. The name blanked is
            // derived from the LDML name blanked and posix reflects the main use of
            // the shift-trimmed option.
            "blanked" => self.alternate = AlternateHandling::Blanked,
            "posix" => self.alternate = AlternateHandling::ShiftTrimmed,
            _ => {}
        }

        // TODO: caseFirst ("kf"), reorder ("kr"), and maybe variableTop ("vt").

        // Not used:
        // - normalization ("kk", not necessary for this implementation)
        // - hiraganaQuatenary ("kh", obsolete)
    }
}

// Go: collate/option.go:143 ldmlBool
fn ldml_bool(t: &Tag, old: bool, key: &str) -> bool {
    match type_for_key(t, key).as_str() {
        "true" => true,
        "false" => false,
        _ => old,
    }
}

// Go: collate/option.go:154 (option values)
/// IgnoreCase sets case-insensitive comparison.
pub const IGNORE_CASE: CollateOption = CollateOption {
    priority: 3,
    f: ignore_case_f,
};

/// IgnoreDiacritics causes diacritical marks to be ignored. ("o" == "ö").
pub const IGNORE_DIACRITICS: CollateOption = CollateOption {
    priority: 3,
    f: ignore_diacritics_f,
};

/// IgnoreWidth causes full-width characters to match their half-width
/// equivalents.
pub const IGNORE_WIDTH: CollateOption = CollateOption {
    priority: 2,
    f: ignore_width_f,
};

/// Loose sets the collator to ignore diacritics, case and width.
pub const LOOSE: CollateOption = CollateOption {
    priority: 4,
    f: loose_f,
};

/// Force ordering if strings are equivalent but not equal.
pub const FORCE: CollateOption = CollateOption {
    priority: 5,
    f: force_f,
};

/// Numeric specifies that numbers should sort numerically ("2" < "12").
pub const NUMERIC: CollateOption = CollateOption {
    priority: 5,
    f: numeric_f,
};

// Go: collate/option.go:181 ignoreWidthF
fn ignore_width_f(o: &mut Options) {
    o.ignore[TERTIARY] = true;
    o.case_level = true;
}

// Go: collate/option.go:186 ignoreDiacriticsF
fn ignore_diacritics_f(o: &mut Options) {
    o.ignore[SECONDARY] = true;
}

// Go: collate/option.go:190 ignoreCaseF
fn ignore_case_f(o: &mut Options) {
    o.ignore[TERTIARY] = true;
    o.case_level = false;
}

// Go: collate/option.go:195 looseF
fn loose_f(o: &mut Options) {
    ignore_width_f(o);
    ignore_diacritics_f(o);
    ignore_case_f(o);
}

// Go: collate/option.go:201 forceF
fn force_f(o: &mut Options) {
    o.ignore[IDENTITY] = false;
}

// Go: collate/option.go:205 numericF
fn numeric_f(o: &mut Options) {
    o.numeric = true;
}

// ---------------------------------------------------------------------------
// collate/collate.go
// ---------------------------------------------------------------------------

// Go: collate/collate.go:53 tags
/// PORT: Go fills `tags` in `init()` from `availableLocales`.
static TAGS: LazyLock<Vec<Tag>> = LazyLock::new(|| {
    AVAILABLE_LOCALES
        .split(',')
        .map(|s| {
            // Go: language.Raw.MustParse(s)
            let (t, err) = language::canon_type_parse(language::RAW, s);
            if let Some(err) = err {
                panic!("{}", err.error());
            }
            t
        })
        .collect()
});

// Go: collate/collate.go:23 Collator
/// Collator provides functionality for comparing strings for a given
/// collation order.
/// PORT: Go `sorter` is only used by `Sort` and `SortStrings`, which are not
/// ported.
pub struct Collator {
    options: Options,

    iter: [CollIter; 2],
}

// Go: collate/collate.go:56 New
/// New returns a new Collator initialized for the given locale.
pub fn new(t: &Tag, o: Vec<CollateOption>) -> Collator {
    let index = match_lang(t, &TAGS);
    let mut c = new_collator(Rc::new(get_table(LOCALES[index])));

    // Set options from the user-supplied tag.
    c.options.set_from_tag(t);

    // Set the user-supplied options.
    c.options.set_options(o);

    c.init();
    c
}

impl Collator {
    // Go: collate/collate.go:78 (*Collator).init
    fn init(&mut self) {
        if self.options.numeric {
            self.options.t = new_numeric_weighter(self.options.t.clone());
        }
        self.iter[0].init(self.options.t.clone());
        self.iter[1].init(self.options.t.clone());
    }

    // Go: collate/collate.go:121 (*Collator).CompareString
    /// CompareString returns an integer comparing the two strings.
    /// The result will be 0 if a==b, -1 if a < b, and +1 if a > b.
    pub fn compare_string(&mut self, a: &str, b: &str) -> i32 {
        // TODO: skip identical prefixes once we have a fast way to detect if a rune is
        // part of a contraction. This would lead to roughly a 10% speedup for the colcmp regtest.
        self.iter[0].it.set_input_string(a);
        self.iter[1].it.set_input_string(b);
        let res = self.compare();
        if res != 0 {
            return res;
        }
        if !self.options.ignore[IDENTITY] {
            if a < b {
                return -1;
            } else if a > b {
                return 1;
            }
        }
        0
    }

    // Go: collate/collate.go:157 (*Collator).compare
    fn compare(&mut self) -> i32 {
        let [ia, ib] = &mut self.iter;
        // Process primary level
        if self.options.alternate != AlternateHandling::Shifted {
            // TODO: implement script reordering
            let res = compare_level(CollIter::next_primary, ia, ib);
            if res != 0 {
                return res;
            }
        } else {
            // TODO: handle shifted
        }
        if !self.options.ignore[SECONDARY] {
            let mut f: fn(&mut CollIter) -> i32 = CollIter::next_secondary;
            if self.options.backwards {
                f = CollIter::prev_secondary;
            }
            let res = compare_level(f, ia, ib);
            if res != 0 {
                return res;
            }
        }
        // TODO: special case handling (Danish?)
        if !self.options.ignore[TERTIARY] || self.options.case_level {
            let res = compare_level(CollIter::next_tertiary, ia, ib);
            if res != 0 {
                return res;
            }
            if !self.options.ignore[QUATERNARY] {
                let res = compare_level(CollIter::next_quaternary, ia, ib);
                if res != 0 {
                    return res;
                }
            }
        }
        0
    }
}

// Go: collate/collate.go:139 compareLevel
fn compare_level(f: fn(&mut CollIter) -> i32, a: &mut CollIter, b: &mut CollIter) -> i32 {
    a.pce = 0;
    b.pce = 0;
    loop {
        let va = f(a);
        let vb = f(b);
        if va != vb {
            if va < vb {
                return -1;
            }
            return 1;
        } else if va == 0 {
            break;
        }
    }
    0
}

// Go: collate/collate.go:234 iter
/// PORT: Go embeds `colltab.Iter`; here it is the field `it`.
struct CollIter {
    it: Iter,
    pce: usize,
}

impl CollIter {
    fn new(t: Rc<dyn Weighter>) -> CollIter {
        CollIter {
            it: Iter::new(t),
            pce: 0,
        }
    }

    // Go: collate/collate.go:241 (*iter).init
    fn init(&mut self, t: Rc<dyn Weighter>) {
        self.it.weighter = t;
        self.it.elems.clear();
    }

    // Go: collate/collate.go:246 (*iter).nextPrimary
    fn next_primary(&mut self) -> i32 {
        loop {
            while self.pce < self.it.n {
                let v = self.it.elems[self.pce].primary();
                if v != 0 {
                    self.pce += 1;
                    return v;
                }
                self.pce += 1;
            }
            if !self.it.next() {
                return 0;
            }
        }
    }

    // Go: collate/collate.go:260 (*iter).nextSecondary
    fn next_secondary(&mut self) -> i32 {
        while self.pce < self.it.elems.len() {
            let v = self.it.elems[self.pce].secondary();
            if v != 0 {
                self.pce += 1;
                return v;
            }
            self.pce += 1;
        }
        0
    }

    // Go: collate/collate.go:270 (*iter).prevSecondary
    fn prev_secondary(&mut self) -> i32 {
        while self.pce < self.it.elems.len() {
            let v = self.it.elems[self.it.elems.len() - self.pce - 1].secondary();
            if v != 0 {
                self.pce += 1;
                return v;
            }
            self.pce += 1;
        }
        0
    }

    // Go: collate/collate.go:280 (*iter).nextTertiary
    fn next_tertiary(&mut self) -> i32 {
        while self.pce < self.it.elems.len() {
            let v = self.it.elems[self.pce].tertiary();
            if v != 0 {
                self.pce += 1;
                return i32::from(v);
            }
            self.pce += 1;
        }
        0
    }

    // Go: collate/collate.go:290 (*iter).nextQuaternary
    fn next_quaternary(&mut self) -> i32 {
        while self.pce < self.it.elems.len() {
            let v = self.it.elems[self.pce].quaternary();
            if v != 0 {
                self.pce += 1;
                return v;
            }
            self.pce += 1;
        }
        0
    }
}

// ---------------------------------------------------------------------------
// Go standard library and golang.org/x/text/unicode/norm helpers
// ---------------------------------------------------------------------------

/// Go `utf8.RuneSelf`.
const UTF8_RUNE_SELF: u8 = 0x80;

/// Go `utf8.RuneStart`.
fn utf8_rune_start(b: u8) -> bool {
    b & 0xC0 != 0x80
}

/// Go `utf8.DecodeRune`: the first rune of s and its size. Invalid UTF-8
/// gives (U+FFFD, 1) and an empty input (U+FFFD, 0).
fn utf8_decode_rune(s: &[u8]) -> (u32, usize) {
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

/// Whether the generated data below covers rune r.
fn in_subset(r: u32) -> bool {
    r < 0x800 || (0x2080..0x20C0).contains(&r) || (0xFF00..0xFF40).contains(&r)
}

/// Go `unicode.In(r, unicode.Nd)` for a rune in the subset.
fn unicode_is_nd(r: u32) -> bool {
    if !in_subset(r) {
        unported!("unicode.Nd (rune outside the collation subset table)");
    }
    ND_RANGES.iter().any(|&(lo, hi)| (lo..=hi).contains(&r))
}

/// Go `norm.NFKD.Properties(s).Decomposition()` for a rune whose collation
/// element is a decompose element.
fn norm_nfkd_decomposition(s: &[u8]) -> &'static [u8] {
    let (r, _) = utf8_decode_rune(s);
    match NFKD_DECOMPOSITIONS.binary_search_by_key(&r, |&(dr, _)| dr) {
        Ok(i) => NFKD_DECOMPOSITIONS[i].1.as_bytes(),
        Err(_) => unported!("norm.NFKD (rune outside the collation subset table)"),
    }
}

/// Go `norm.NFD.Properties(s).LeadCCC()` for a rune in the subset.
fn norm_nfd_lead_ccc(s: &[u8]) -> u8 {
    let (r, _) = utf8_decode_rune(s);
    if !in_subset(r) {
        unported!("norm.NFD.Properties (rune outside the collation subset table)");
    }
    let i = NFD_LEAD_CCC.partition_point(|&(_, hi, _)| hi < r);
    match NFD_LEAD_CCC.get(i) {
        Some(&(lo, _, ccc)) if lo <= r => ccc,
        _ => 0,
    }
}

// ---------------------------------------------------------------------------
// Data
// ---------------------------------------------------------------------------

// Generated by target/continuation-r97-goport/int7/c2-collate/gen/xtext/collate/zz_gen_test.go
// from golang.org/x/text v0.38.0 collate/tables.go (CLDR 23, und table) and
// unicode/norm tables15.0.0.go, Go 1.26.8 unicode. Do not edit by hand.

/// Go `availableLocales`.
const AVAILABLE_LOCALES: &str = "und,aa,af,ar,as,az,be,bg,bn,bs,bs-Cyrl,ca,cs,cy,da,de-u-co-phonebk,de,dz,ee,el,en,en-US,en-US-u-va-posix,eo,es,et,fa,fa-AF,fi,fi-u-co-standard,fil,fo,fr,fr-CA,gu,ha,haw,he,hi,hr,hu,hy,ig,is,ja,kk,kl,km,kn,ko,kok,ln-u-co-phonetic,ln,lt,lv,mk,ml,mr,mt,my,nb,nn,nso,om,or,pa,pl,ps,ro,ru,se,si,sk,sl,sq,sr,sr-Latn,ssy,sv,sv-u-co-standard,ta,te,th,tn,to,tr,uk,ur,vi,wae,yo,zh,zh-u-co-stroke,zh-Hant-u-co-pinyin,zh-Hant";

/// Go `varTop`.
const VAR_TOP: u32 = 0x30e;

/// Go `locales`: (lookupOffset, valuesOffset) per available locale.
static LOCALES: [TableIndex; 95] = [
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x0,
    }, // und
    TableIndex {
        lookup_offset: 0x1c,
        values_offset: 0x1b4,
    }, // aa
    TableIndex {
        lookup_offset: 0x1d,
        values_offset: 0x0,
    }, // af
    TableIndex {
        lookup_offset: 0x1f,
        values_offset: 0x0,
    }, // ar
    TableIndex {
        lookup_offset: 0x21,
        values_offset: 0x0,
    }, // as
    TableIndex {
        lookup_offset: 0x27,
        values_offset: 0x1d7,
    }, // az
    TableIndex {
        lookup_offset: 0x28,
        values_offset: 0x0,
    }, // be
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x0,
    }, // bg
    TableIndex {
        lookup_offset: 0x2a,
        values_offset: 0x0,
    }, // bn
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x0,
    }, // bs
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x0,
    }, // bs-Cyrl
    TableIndex {
        lookup_offset: 0x2b,
        values_offset: 0x1ec,
    }, // ca
    TableIndex {
        lookup_offset: 0x2d,
        values_offset: 0x1f0,
    }, // cs
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x1f5,
    }, // cy
    TableIndex {
        lookup_offset: 0x30,
        values_offset: 0x1f7,
    }, // da
    TableIndex {
        lookup_offset: 0x32,
        values_offset: 0x201,
    }, // de-u-co-phonebk
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x0,
    }, // de
    TableIndex {
        lookup_offset: 0x34,
        values_offset: 0x0,
    }, // dz
    TableIndex {
        lookup_offset: 0x3a,
        values_offset: 0x20a,
    }, // ee
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x0,
    }, // el
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x0,
    }, // en
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x0,
    }, // en-US
    TableIndex {
        lookup_offset: 0x41,
        values_offset: 0x219,
    }, // en-US-u-va-posix
    TableIndex {
        lookup_offset: 0x42,
        values_offset: 0x23b,
    }, // eo
    TableIndex {
        lookup_offset: 0x43,
        values_offset: 0x23f,
    }, // es
    TableIndex {
        lookup_offset: 0x49,
        values_offset: 0x242,
    }, // et
    TableIndex {
        lookup_offset: 0x4b,
        values_offset: 0x0,
    }, // fa
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x0,
    }, // fa-AF
    TableIndex {
        lookup_offset: 0x4e,
        values_offset: 0x25a,
    }, // fi
    TableIndex {
        lookup_offset: 0x54,
        values_offset: 0x265,
    }, // fi-u-co-standard
    TableIndex {
        lookup_offset: 0x43,
        values_offset: 0x272,
    }, // fil
    TableIndex {
        lookup_offset: 0x30,
        values_offset: 0x1f7,
    }, // fo
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x0,
    }, // fr
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x0,
    }, // fr-CA
    TableIndex {
        lookup_offset: 0x56,
        values_offset: 0x0,
    }, // gu
    TableIndex {
        lookup_offset: 0x57,
        values_offset: 0x275,
    }, // ha
    TableIndex {
        lookup_offset: 0x5e,
        values_offset: 0x27a,
    }, // haw
    TableIndex {
        lookup_offset: 0x5f,
        values_offset: 0x0,
    }, // he
    TableIndex {
        lookup_offset: 0x61,
        values_offset: 0x0,
    }, // hi
    TableIndex {
        lookup_offset: 0x63,
        values_offset: 0x291,
    }, // hr
    TableIndex {
        lookup_offset: 0x65,
        values_offset: 0x297,
    }, // hu
    TableIndex {
        lookup_offset: 0x66,
        values_offset: 0x0,
    }, // hy
    TableIndex {
        lookup_offset: 0x68,
        values_offset: 0x29f,
    }, // ig
    TableIndex {
        lookup_offset: 0x6a,
        values_offset: 0x2a3,
    }, // is
    TableIndex {
        lookup_offset: 0x76,
        values_offset: 0x0,
    }, // ja
    TableIndex {
        lookup_offset: 0x77,
        values_offset: 0x0,
    }, // kk
    TableIndex {
        lookup_offset: 0x78,
        values_offset: 0x414,
    }, // kl
    TableIndex {
        lookup_offset: 0x7a,
        values_offset: 0x0,
    }, // km
    TableIndex {
        lookup_offset: 0x7c,
        values_offset: 0x0,
    }, // kn
    TableIndex {
        lookup_offset: 0x88,
        values_offset: 0x0,
    }, // ko
    TableIndex {
        lookup_offset: 0x8a,
        values_offset: 0x0,
    }, // kok
    TableIndex {
        lookup_offset: 0x8b,
        values_offset: 0x570,
    }, // ln-u-co-phonetic
    TableIndex {
        lookup_offset: 0x8b,
        values_offset: 0x0,
    }, // ln
    TableIndex {
        lookup_offset: 0x91,
        values_offset: 0x574,
    }, // lt
    TableIndex {
        lookup_offset: 0x93,
        values_offset: 0x582,
    }, // lv
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x0,
    }, // mk
    TableIndex {
        lookup_offset: 0x95,
        values_offset: 0x0,
    }, // ml
    TableIndex {
        lookup_offset: 0x97,
        values_offset: 0x0,
    }, // mr
    TableIndex {
        lookup_offset: 0x9a,
        values_offset: 0x58a,
    }, // mt
    TableIndex {
        lookup_offset: 0x9c,
        values_offset: 0x0,
    }, // my
    TableIndex {
        lookup_offset: 0x30,
        values_offset: 0x593,
    }, // nb
    TableIndex {
        lookup_offset: 0x30,
        values_offset: 0x593,
    }, // nn
    TableIndex {
        lookup_offset: 0x9e,
        values_offset: 0x595,
    }, // nso
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x59b,
    }, // om
    TableIndex {
        lookup_offset: 0xa0,
        values_offset: 0x0,
    }, // or
    TableIndex {
        lookup_offset: 0xa2,
        values_offset: 0x0,
    }, // pa
    TableIndex {
        lookup_offset: 0xa4,
        values_offset: 0x5a1,
    }, // pl
    TableIndex {
        lookup_offset: 0xa7,
        values_offset: 0x0,
    }, // ps
    TableIndex {
        lookup_offset: 0xa9,
        values_offset: 0x5b3,
    }, // ro
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x0,
    }, // ru
    TableIndex {
        lookup_offset: 0xab,
        values_offset: 0x5ba,
    }, // se
    TableIndex {
        lookup_offset: 0xad,
        values_offset: 0x0,
    }, // si
    TableIndex {
        lookup_offset: 0xaf,
        values_offset: 0x5c7,
    }, // sk
    TableIndex {
        lookup_offset: 0xb0,
        values_offset: 0x5cc,
    }, // sl
    TableIndex {
        lookup_offset: 0xb2,
        values_offset: 0x5cf,
    }, // sq
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x0,
    }, // sr
    TableIndex {
        lookup_offset: 0x15,
        values_offset: 0x0,
    }, // sr-Latn
    TableIndex {
        lookup_offset: 0x1c,
        values_offset: 0x1b4,
    }, // ssy
    TableIndex {
        lookup_offset: 0xb4,
        values_offset: 0x5d3,
    }, // sv
    TableIndex {
        lookup_offset: 0xb6,
        values_offset: 0x5d9,
    }, // sv-u-co-standard
    TableIndex {
        lookup_offset: 0xb8,
        values_offset: 0x0,
    }, // ta
    TableIndex {
        lookup_offset: 0xba,
        values_offset: 0x0,
    }, // te
    TableIndex {
        lookup_offset: 0xbc,
        values_offset: 0x0,
    }, // th
    TableIndex {
        lookup_offset: 0x9e,
        values_offset: 0x595,
    }, // tn
    TableIndex {
        lookup_offset: 0xbe,
        values_offset: 0x5e1,
    }, // to
    TableIndex {
        lookup_offset: 0xc4,
        values_offset: 0x5ed,
    }, // tr
    TableIndex {
        lookup_offset: 0xc5,
        values_offset: 0x0,
    }, // uk
    TableIndex {
        lookup_offset: 0xc7,
        values_offset: 0x0,
    }, // ur
    TableIndex {
        lookup_offset: 0xc9,
        values_offset: 0x5fc,
    }, // vi
    TableIndex {
        lookup_offset: 0xca,
        values_offset: 0x610,
    }, // wae
    TableIndex {
        lookup_offset: 0xcc,
        values_offset: 0x613,
    }, // yo
    TableIndex {
        lookup_offset: 0xe6,
        values_offset: 0x618,
    }, // zh
    TableIndex {
        lookup_offset: 0xff,
        values_offset: 0x618,
    }, // zh-u-co-stroke
    TableIndex {
        lookup_offset: 0xe6,
        values_offset: 0x618,
    }, // zh-Hant-u-co-pinyin
    TableIndex {
        lookup_offset: 0xff,
        values_offset: 0x618,
    }, // zh-Hant
];

/// Subset of Go `mainLookup`. Chunk 3 holds the Index0 row (lead bytes
/// 0xC0-0xFF); index block k is chunk k+2. 0xFFFF marks a row outside the subset.
static SUBSET_LOOKUP: [u16; 384] = [
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000,
    0xffff, 0xffff, 0x0001, 0x0002, 0x0003, 0x0004, 0x0005, 0x0006, 0x0007, 0x0008, 0x0009, 0x000a,
    0x000b, 0x000c, 0x000d, 0x000e, 0x000f, 0x0010, 0x0011, 0x0012, 0x0013, 0x0014, 0x0015, 0x0016,
    0x0017, 0x0018, 0x0019, 0x001a, 0x001b, 0x001c, 0x001d, 0x001e, 0xffff, 0xffff, 0x0002, 0xffff,
    0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0x0003,
    0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
    0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0x001f, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
    0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
    0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
    0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
    0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
    0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
    0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
    0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
    0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
    0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff,
    0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0xffff, 0x0020, 0xffff, 0xffff, 0xffff,
];

/// Subset of Go `mainValues`. Chunks 0-1 are the und Values0 (ASCII),
/// chunk 2 is the null block, value block k is chunk k+2.
static SUBSET_VALUES: [u32; 2240] = [
    0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000,
    0xa0000000, 0x40020020, 0x40020220, 0x40020420, 0x40020620, 0x40020820, 0xa0000000, 0xa0000000,
    0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000,
    0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000,
    0x40021220, 0x4002ba20, 0x4003e020, 0x4004ea20, 0x4027de20, 0x4004ec20, 0x4004e620, 0x4003d220,
    0x4003f420, 0x4003f620, 0x4004d820, 0x40093820, 0x40024020, 0x40021a20, 0x4002e420, 0x4004e220,
    0x4029cc20, 0x4029ce20, 0x4029d020, 0x4029d220, 0x4029d420, 0x4029d620, 0x4029d820, 0x4029da20,
    0x4029dc20, 0x4029de20, 0x40026c20, 0x40026220, 0x40094020, 0x40094220, 0x40094420, 0x4002c420,
    0x4004d620, 0x002bde88, 0x002c0a88, 0x002c3a88, 0x002c6288, 0x002c9888, 0x002d0888, 0x002d2288,
    0x002d6888, 0x002d9a88, 0x002dcc88, 0x002dfe88, 0xc0030002, 0x002e8288, 0x002e9e88, 0x002ee288,
    0x002f2c88, 0x002f5688, 0x002f7a88, 0x002fe688, 0x00302c88, 0x00306c88, 0x0030be88, 0x0030e288,
    0x0030f688, 0x00310088, 0x00312a88, 0x4003f820, 0x4004e420, 0x4003fa20, 0x40062420, 0x40021620,
    0x40061e20, 0x402bde20, 0x402c0a20, 0x402c3a20, 0x402c6220, 0x402c9820, 0x402d0820, 0x402d2220,
    0x402d6820, 0x402d9a20, 0x402dcc20, 0x402dfe20, 0xc0000002, 0x402e8220, 0x402e9e20, 0x402ee220,
    0x402f2c20, 0x402f5620, 0x402f7a20, 0x402fe620, 0x40302c20, 0x40306c20, 0x4030be20, 0x4030e220,
    0x4030f620, 0x40310020, 0x40312a20, 0x4003fc20, 0x40094820, 0x4003fe20, 0x40094c20, 0xa0000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0x40020a20, 0xa0000000, 0xa0000000,
    0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000,
    0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000,
    0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000,
    0x0002129b, 0x4002bc20, 0x4027dc20, 0x4027e020, 0x4027da20, 0x4027e220, 0x40094a20, 0x4004ce20,
    0x40062c20, 0x40081820, 0x002bde94, 0x4003f020, 0x40094620, 0xa0000000, 0x40081a20, 0x40062620,
    0x40070420, 0x40093a20, 0x0029d094, 0x0029d294, 0x40062020, 0x00327684, 0x4004d220, 0x40030620,
    0x40063220, 0x0029ce94, 0x002ee294, 0x4003f220, 0xe000001c, 0xe0000018, 0xe0000032, 0x4002c620,
    0xe0000075, 0xe000006f, 0xe0000081, 0xe00000a9, 0xe000009b, 0xe000008d, 0xe00000d6, 0xe0000109,
    0xe000013f, 0xe0000139, 0xe000014b, 0xe0000157, 0xe00001c0, 0xe00001ba, 0xe00001cc, 0xe00001d8,
    0xe000011b, 0xe0000250, 0xe0000262, 0xe000025c, 0xe000026e, 0xe000028e, 0xe000027a, 0x40093e20,
    0xe00002aa, 0xe0000350, 0xe000034a, 0xe000035c, 0xe000036e, 0xe00003c4, 0x00318888, 0xe0000325,
    0xe0000072, 0xe000006c, 0xe000007e, 0xe00000a6, 0xe0000098, 0xe000008a, 0xe00000d2, 0xe0000106,
    0xe000013c, 0xe0000136, 0xe0000148, 0xe0000154, 0xe00001bd, 0xe00001b7, 0xe00001c9, 0xe00001d5,
    0xe0000118, 0xe000024d, 0xe000025f, 0xe0000259, 0xe000026b, 0xe000028b, 0xe0000277, 0x40093c20,
    0xe00002a7, 0xe000034d, 0xe0000347, 0xe0000359, 0xe000036b, 0xe00003c1, 0x40318820, 0xe00003cd,
    0xe00000c3, 0xe00000c0, 0xe000007b, 0xe0000078, 0xe00000bd, 0xe00000ba, 0xe00000f1, 0xe00000ee,
    0xe00000f7, 0xe00000f4, 0xe0000103, 0xe0000100, 0xe00000fd, 0xe00000fa, 0xe000010f, 0xe000010c,
    0xe0000115, 0xe0000112, 0xe000016f, 0xe000016c, 0xe0000145, 0xe0000142, 0xe000015d, 0xe000015a,
    0xe0000169, 0xe0000166, 0xe0000151, 0xe000014e, 0xe0000190, 0xe000018d, 0xe000018a, 0xe0000187,
    0xe000019c, 0xe0000199, 0xe00001a2, 0xe000019f, 0xe00001a8, 0xe00001a5, 0xe00001b4, 0xe00001b1,
    0xe00001de, 0xe00001db, 0xe00001ed, 0xe00001ea, 0xe00001c6, 0xe00001c3, 0xe00001e7, 0xe00001e4,
    0xe00001e1, 0x402da220, 0xf0000a0a, 0xf0000404, 0xe00001ff, 0xe00001fc, 0xe000020e, 0xe000020b,
    0x402f7220, 0xe0000214, 0xe0000211, 0xe0000220, 0xe000021d, 0xe000021a, 0xe0000217, 0xe0000232,
    0xe000022c, 0xe0000226, 0xe0000223, 0xe000023e, 0xe000023b, 0xe0000256, 0xe0000253, 0xe000024a,
    0xe0000247, 0xf0000404, 0x002eda88, 0x402eda20, 0xe00002c6, 0xe00002c3, 0xe0000268, 0xe0000265,
    0xe0000288, 0xe0000285, 0xe00002df, 0xe00002db, 0xe00002e9, 0xe00002e6, 0xe00002f5, 0xe00002f2,
    0xe00002ef, 0xe00002ec, 0xe0000307, 0xe0000304, 0xe000030d, 0xe000030a, 0xe0000319, 0xe0000316,
    0xe0000313, 0xe0000310, 0xe0000332, 0xe000032f, 0xe000032c, 0xe0000329, 0x00303688, 0x40303620,
    0xe000039a, 0xe0000397, 0xe00003a6, 0xe00003a3, 0xe0000356, 0xe0000353, 0xe0000368, 0xe0000365,
    0xe0000394, 0xe0000391, 0xe00003a0, 0xe000039d, 0xe00003be, 0xe00003bb, 0xe00003ca, 0xe00003c7,
    0xe00003d0, 0xe00003dc, 0xe00003d9, 0xe00003e8, 0xe00003e5, 0xe00003e2, 0xe00003df, 0xe0000322,
    0x402c1a20, 0x002c2a88, 0x002c3288, 0x402c3220, 0x0031c488, 0x4031c420, 0x002efa88, 0x002c4e88,
    0x402c4e20, 0x002c7288, 0x002c7a88, 0x002c8488, 0x402c8420, 0xe00003eb, 0x002cae88, 0x002cb888,
    0x002cc288, 0x002d1688, 0x402d1620, 0x002d4488, 0x002d5888, 0x402d7820, 0x002dc288, 0x002db688,
    0x002e0a88, 0x402e0a20, 0x402e3820, 0x402e7220, 0x0030a088, 0x002eb488, 0x402ebc20, 0x002f1088,
    0xe00002d8, 0xe00002d5, 0x002d6088, 0x402d6020, 0x002f3e88, 0x402f3e20, 0x002f8288, 0x0031b488,
    0x4031b420, 0x00300888, 0x40301220, 0x40304220, 0x00304a88, 0x40304a20, 0x00305288, 0xe00003b8,
    0xe00003b5, 0x0030b488, 0x0030cc88, 0x00311888, 0x40311820, 0x00313488, 0x40313420, 0x00316488,
    0x00316e88, 0x40316e20, 0x40317820, 0x4031a620, 0x0031bc88, 0x4031bc20, 0xe000033e, 0x40319420,
    0x40321220, 0x40321a20, 0x40322220, 0x40322a20, 0xe000012c, 0xe0000128, 0xe0000124, 0xf0000a0a,
    0xf000040a, 0xf0000404, 0xf0000a0a, 0xf000040a, 0xf0000404, 0xe0000087, 0xe0000084, 0xe00001d2,
    0xe00001cf, 0xe0000274, 0xe0000271, 0xe0000362, 0xe000035f, 0xe000038d, 0xe0000389, 0xe0000375,
    0xe0000371, 0xe0000385, 0xe0000381, 0xe000037d, 0xe0000379, 0x402cae20, 0xe00000a2, 0xe000009e,
    0xe00000b6, 0xe00000b2, 0xe00000e9, 0xe00000e4, 0x002d3a88, 0x402d3a20, 0xe0000196, 0xe0000193,
    0xe0000208, 0xe0000205, 0xe00002b8, 0xe00002b5, 0xe00002bf, 0xe00002bb, 0xe00003f1, 0xe00003ee,
    0xe0000202, 0xf0000a0a, 0xf000040a, 0xf0000404, 0xe0000184, 0xe0000181, 0x002d7888, 0x00319488,
    0xe0000244, 0xe0000241, 0xe0000094, 0xe0000090, 0xe00000df, 0xe00000da, 0xe00002b1, 0xe00002ad,
    0xe00000c9, 0xe00000c6, 0xe00000cf, 0xe00000cc, 0xe0000175, 0xe0000172, 0xe000017b, 0xe0000178,
    0xe00001f3, 0xe00001f0, 0xe00001f9, 0xe00001f6, 0xe00002cc, 0xe00002c9, 0xe00002d2, 0xe00002cf,
    0xe00002fb, 0xe00002f8, 0xe0000301, 0xe00002fe, 0xe00003ac, 0xe00003a9, 0xe00003b2, 0xe00003af,
    0xe000031f, 0xe000031c, 0xe0000338, 0xe0000335, 0x00312288, 0x40312220, 0xe00001ae, 0xe00001ab,
    0x002ebc88, 0x402c8c20, 0x002f2288, 0x402f2220, 0x00314088, 0x40314020, 0xe00000af, 0xe00000ac,
    0xe0000163, 0xe0000160, 0xe0000281, 0xe000027d, 0xe0000295, 0xe0000291, 0xe000029c, 0xe0000299,
    0xe00002a3, 0xe000029f, 0xe00003d6, 0xe00003d3, 0x402e5e20, 0x402ed020, 0x40305a20, 0x402dd420,
    0xe000011e, 0xe00002e3, 0x002be888, 0x002c4488, 0x402c4420, 0x002e3888, 0x00303e88, 0x402ffc20,
    0x40315820, 0x0031d488, 0x4031d420, 0x002c1a88, 0x00307c88, 0x0030da88, 0x002ca288, 0x402ca220,
    0x002dde88, 0x402dde20, 0x002f6a88, 0x402f6a20, 0x002f8e88, 0x402f8e20, 0x00311088, 0x40311020,
    0x402bf020, 0x402bf820, 0x402c0220, 0x402c2a20, 0x402efa20, 0x402c5620, 0x402c7220, 0x402c7a20,
    0x402ccc20, 0x402cb820, 0x402cd420, 0x402cc220, 0x402cdc20, 0x402ce820, 0x402cf020, 0x402dee20,
    0x402d4420, 0x402d2a20, 0x402d3220, 0x402d5820, 0x402d0020, 0x40308820, 0x402d8020, 0x402d8e20,
    0x402db620, 0x402dc220, 0x402daa20, 0x402e4220, 0x402e4a20, 0x402e5420, 0x402e6820, 0x4030a020,
    0x4030ac20, 0x402e9020, 0x402eb420, 0x402ec820, 0x402ea620, 0x402f1020, 0x402eee20, 0x402f1a20,
    0x402f4c20, 0x402f9820, 0x402fa220, 0x402fac20, 0x402fb620, 0x402fbe20, 0x402fc620, 0x402fd020,
    0x402f8220, 0x402fd820, 0x402ff420, 0x40300820, 0x402df620, 0x40301a20, 0x40302420, 0x40306420,
    0x40305220, 0x40307c20, 0x4030b420, 0x4030cc20, 0x4030da20, 0x4030ee20, 0x402e7a20, 0x40310820,
    0x40314820, 0x40315020, 0x40316420, 0x40318020, 0x4031cc20, 0x4031e820, 0x40320a20, 0x40323220,
    0x40323a20, 0x402c1220, 0x402cf820, 0x402d4c20, 0x402d7020, 0x402de620, 0x402e1a20, 0x402e2a20,
    0x402f6220, 0x4031fa20, 0x40320220, 0xe0000121, 0xe0000133, 0xe0000130, 0xe0000341, 0xe0000344,
    0xe000033b, 0xe000017e, 0xe0000235, 0xe0000238, 0x40324220, 0x40324a20, 0x40309020, 0x40309820,
    0x002d6894, 0x002d8094, 0x002dcc94, 0x002f7a94, 0x002f9894, 0x002fac94, 0x002fd894, 0x0030e294,
    0x00310094, 0x40064020, 0x40064420, 0x402d9620, 0x4031de20, 0x402d9820, 0x4031e220, 0x4031f020,
    0x4031dc20, 0x4031f220, 0x40064620, 0x40064820, 0x40064a20, 0x40064c20, 0x40064e20, 0x40065020,
    0x40065220, 0x40065420, 0x40065620, 0x40065820, 0x40065a20, 0x40065c20, 0x40065e20, 0x40066020,
    0x4027b220, 0x4027b420, 0x40066220, 0x40066420, 0x40066620, 0x40066820, 0x40066a20, 0x40066c20,
    0x40062820, 0x40062a20, 0x40062e20, 0x40063420, 0x40062220, 0x40063020, 0x40066e20, 0x40067020,
    0x002d5894, 0x002e2294, 0x002fe694, 0x0030f694, 0x0031e894, 0x40067220, 0x40067420, 0x40067620,
    0x40067820, 0x40067a20, 0x40067c20, 0x40067e20, 0x40068020, 0x40068220, 0x4031e020, 0x40068420,
    0x40068620, 0x40068820, 0x40068a20, 0x40068c20, 0x40068e20, 0x40069020, 0x40069220, 0x40069420,
    0x40069620, 0x40069820, 0x40069a20, 0x40069c20, 0x40069e20, 0x4006a020, 0x4006a220, 0x4006a420,
    0xae603502, 0xae603202, 0xae603c02, 0xae604e02, 0xae605b02, 0xae606302, 0xae603702, 0xae605202,
    0xae604702, 0xae606402, 0xae604302, 0xae604d02, 0xae604102, 0xae605f02, 0xae605f02, 0xae606502,
    0xae606602, 0xae606702, 0xae605f02, 0xae602202, 0xae602a02, 0xae805f02, 0xadc06002, 0xadc06002,
    0xadc06002, 0xadc06002, 0xae805f02, 0xad806802, 0xadc06002, 0xadc06002, 0xadc06002, 0xadc06002,
    0xadc06002, 0xaca06e02, 0xaca06f02, 0xadc07002, 0xadc07502, 0xadc07602, 0xadc07702, 0xaca05602,
    0xaca05902, 0xadc06002, 0xadc06002, 0xadc06002, 0xadc06002, 0xadc07802, 0xadc07902, 0xadc06002,
    0xadc07a02, 0xadc07b02, 0xadc02102, 0xadc06002, 0xa0107c02, 0xa0107d02, 0xa0106102, 0xa0106102,
    0xa0105402, 0xadc07e02, 0xadc06002, 0xadc06002, 0xadc06002, 0xae605f02, 0xae605f02, 0xae605f02,
    0xae603502, 0xae603202, 0xae604502, 0xae602202, 0xe0000000, 0xaf007f02, 0xae605f02, 0xadc06002,
    0xadc06002, 0xadc06002, 0xae605f02, 0xae605f02, 0xae605f02, 0xadc06002, 0xadc06002, 0xa0000000,
    0xae605f02, 0xae605f02, 0xae605f02, 0xadc06002, 0xadc06002, 0xadc06002, 0xadc06002, 0xae605f02,
    0xae808002, 0xadc06002, 0xadc06002, 0xae605f02, 0xae906002, 0xaea05f02, 0xaea05f02, 0xae906002,
    0xaea08102, 0xaea08202, 0xae906002, 0x84e615ef, 0x84e6164c, 0x84e616cd, 0x84e61771, 0x84e61836,
    0x84e6161d, 0x84e61631, 0x84e616b4, 0x84e61741, 0x84e617bd, 0x84e61816, 0x84e6185f, 0x84e6187b,
    0x00326688, 0x40326620, 0x0032a688, 0x4032a620, 0x40064020, 0x40064220, 0x00326088, 0x40326020,
    0x00000000, 0x00000000, 0x00326c84, 0x40329220, 0x40329020, 0x40329420, 0x40026220, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x40062020, 0xe0000003, 0xe00003f7, 0x40030620,
    0xe00003fd, 0xe0000403, 0xe0000409, 0x00000000, 0xe0000421, 0x00000000, 0xe0000427, 0xe0000437,
    0xe0000412, 0x00325288, 0x00325488, 0x00325688, 0x00325a88, 0x00325c88, 0x00326488, 0x00326888,
    0x00326a88, 0x00326c88, 0x00327088, 0x00327288, 0x00327688, 0x00327888, 0x00327a88, 0x00327c88,
    0x00327e88, 0x00328888, 0x00000000, 0x00328e88, 0x00329688, 0x00329888, 0x00329a88, 0x00329c88,
    0x00329e88, 0x0032a288, 0xe000040f, 0xe000042d, 0xe00003f4, 0xe00003fa, 0xe0000400, 0xe0000406,
    0xe0000430, 0x40325220, 0x40325420, 0x40325620, 0x40325a20, 0x40325c20, 0x40326420, 0x40326820,
    0x40326a20, 0x40326c20, 0x40327020, 0x40327220, 0x40327620, 0x40327820, 0x40327a20, 0x40327c20,
    0x40327e20, 0x40328820, 0x00328e99, 0x40328e20, 0x40329620, 0x40329820, 0x40329a20, 0x40329c20,
    0x40329e20, 0x4032a220, 0xe000040c, 0xe000042a, 0xe000041e, 0xe0000424, 0xe0000434, 0xe000041a,
    0x00325484, 0x00326a84, 0x0032988a, 0xf000020a, 0xf000020a, 0x00329a84, 0x00327e84, 0xe0000416,
    0x00328688, 0x40328620, 0x00326288, 0x40326220, 0x00325e88, 0x40325e20, 0x00328488, 0x40328420,
    0x0032a488, 0x4032a420, 0x0032e888, 0x4032e820, 0x0032f288, 0x4032f220, 0x0032f488, 0x4032f420,
    0x0032fa88, 0x4032fa20, 0x00330888, 0x40330820, 0x00330e88, 0x40330e20, 0x00331688, 0x40331620,
    0x00327084, 0x00328884, 0x00328e84, 0x40326e20, 0x00326a8a, 0x00325c84, 0x40092e20, 0x0032a888,
    0x4032a820, 0x00328e8a, 0x00328288, 0x40328220, 0x40328c20, 0x00329288, 0x00329088, 0x00329488,
    0xe0000443, 0xe0000449, 0x00339688, 0x0033a288, 0x0033c288, 0x0033fc88, 0xc02a0071, 0x00343688,
    0x00344688, 0x00349a88, 0x0034e488, 0x00356288, 0x00356a88, 0xe0000455, 0x00357a88, 0x00365488,
    0xc0090041, 0x00335288, 0x00335a88, 0xc0130092, 0x00338a88, 0xc01800d1, 0xc01c0071, 0xc0200071,
    0xc0250041, 0x00343e88, 0xc0370092, 0x00348488, 0x0034a888, 0x0034ba88, 0xc02e0071, 0x00350e88,
    0x00352888, 0x00353a88, 0x00354c88, 0xc03e00f1, 0x0035ac88, 0x0035b488, 0x00360288, 0xc0440071,
    0x00365c88, 0x00366688, 0x00367488, 0xc0480071, 0x00368e88, 0xc04c0071, 0x0036b888, 0x0036c488,
    0xc0060041, 0x40335220, 0x40335a20, 0xc0100092, 0x40338a20, 0xc01600d1, 0xc01a0071, 0xc01e0071,
    0xc0220041, 0x40343e20, 0xc0340092, 0x40348420, 0x4034a820, 0x4034ba20, 0xc02c0071, 0x40350e20,
    0x40352820, 0x40353a20, 0x40354c20, 0xc03a00f1, 0x4035ac20, 0x4035b420, 0x40360220, 0xc0420071,
    0x40365c20, 0x40366620, 0x40367420, 0xc0460071, 0x40368e20, 0xc04a0071, 0x4036b820, 0x4036c420,
    0xe0000440, 0xe0000446, 0x40339620, 0x4033a220, 0x4033c220, 0x4033fc20, 0xc0280071, 0x40343620,
    0x40344620, 0x40349a20, 0x4034e420, 0x40356220, 0x40356a20, 0xe0000452, 0x40357a20, 0x40365420,
    0x0035e088, 0x4035e020, 0x00369e88, 0x40369e20, 0x0036ce88, 0x4036ce20, 0x0036d688, 0x4036d620,
    0x0036ea88, 0x4036ea20, 0x0036e088, 0x4036e020, 0x0036f488, 0x4036f420, 0x0036fc88, 0x4036fc20,
    0x00370488, 0x40370420, 0x00370c88, 0x40370c20, 0xc0500131, 0xc04e0131, 0x00371c88, 0x40371c20,
    0x0035a488, 0x4035a420, 0x0035fa88, 0x4035fa20, 0x0035f288, 0x4035f220, 0x0035e888, 0x4035e820,
    0x00352088, 0x40352020, 0x40070620, 0xae608302, 0xae605f02, 0xae602a02, 0xae602202, 0xae605f02,
    0xa0000000, 0xa0000000, 0x00341c88, 0x40341c20, 0x00369688, 0x40369620, 0x00353088, 0x40353020,
    0xe000043d, 0xe000043a, 0x00336a88, 0x40336a20, 0x00337a88, 0x40337a20, 0x0033dc88, 0x4033dc20,
    0x0033aa88, 0x4033aa20, 0x00345888, 0x40345820, 0x00347888, 0x40347820, 0x00347088, 0x40347020,
    0x00346888, 0x40346820, 0x0034ca88, 0x4034ca20, 0x0034dc88, 0x4034dc20, 0x00351888, 0x40351820,
    0x00372688, 0x40372620, 0x00354488, 0x40354420, 0x00355888, 0x40355820, 0x00359288, 0x40359220,
    0x00359a88, 0x40359a20, 0x0035cc88, 0x4035cc20, 0x00360e88, 0x40360e20, 0x00362a88, 0x40362a20,
    0x00363a88, 0x40363a20, 0x0035d488, 0x4035d420, 0x00364488, 0x40364420, 0x00364c88, 0x40364c20,
    0x00373088, 0xe000044f, 0xe000044c, 0x00346088, 0x40346020, 0x00348e88, 0x40348e20, 0x0034d288,
    0x4034d220, 0x0034c288, 0x4034c220, 0x00363288, 0x40363220, 0x0034b088, 0x4034b020, 0x40373020,
    0x00332a88, 0x40332a20, 0x00333288, 0x40333220, 0x00334a88, 0x40334a20, 0x0033ba88, 0x4033ba20,
    0xc00e0071, 0xc00c0071, 0x00334288, 0x40334220, 0x0033d488, 0x4033d420, 0x0033f288, 0x4033f220,
    0x00340688, 0x40340620, 0xe000045b, 0xe0000458, 0x00342488, 0x40342420, 0x0034f688, 0x4034f620,
    0xc0320071, 0xc0300071, 0x00350688, 0x40350620, 0x0036b088, 0x4036b020, 0xe0000461, 0xe000045e,
    0x00358288, 0x40358220, 0x00358a88, 0x40358a20, 0x00362288, 0x40362220, 0x00338288, 0x40338220,
    0x00368688, 0x40368620, 0x00337288, 0x40337220, 0x0035bc88, 0x4035bc20, 0x0035c488, 0x4035c420,
    0x00339288, 0x40339220, 0x0033a088, 0x4033a020, 0x0033ee88, 0x4033ee20, 0x00341088, 0x40341020,
    0x0034a488, 0x4034a420, 0x0034ec88, 0x4034ec20, 0x00354288, 0x40354220, 0x00355688, 0x40355620,
    0x0033f088, 0x4033f020, 0x00349688, 0x40349620, 0x0034a688, 0x4034a620, 0x00353888, 0x40353820,
    0x0036cc88, 0x4036cc20, 0x00348288, 0x40348220, 0x00372e88, 0x40372e20, 0x00348088, 0x40348020,
    0x00349888, 0x40349820, 0x0034da88, 0x4034da20, 0x00351688, 0x40351620, 0x0035dc88, 0x4035dc20,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00384288, 0x00384488, 0x00384688, 0x00384888, 0x00384a88, 0x00384c88, 0x00384e88,
    0x00385088, 0x00385288, 0x00385488, 0x00385688, 0x00385888, 0x00385a88, 0x00385c88, 0x00385e88,
    0x00386088, 0x00386288, 0x00386488, 0x00386688, 0x00386888, 0x00386a88, 0x00386c88, 0x00386e88,
    0x00387088, 0x00387288, 0x00387488, 0x00387688, 0x00387888, 0x00387a88, 0x00387c88, 0x00387e88,
    0x00388088, 0x00388288, 0x00388488, 0x00388688, 0x00388888, 0x00388a88, 0x00388c88, 0x00000000,
    0x00000000, 0x40388e20, 0x40054e20, 0x40055020, 0x4002be20, 0x40024620, 0x4002ca20, 0x40055220,
    0x00000000, 0x40384220, 0x40384420, 0x40384620, 0x40384820, 0x40384a20, 0x40384c20, 0x40384e20,
    0x40385020, 0x40385220, 0x40385420, 0x40385620, 0x40385820, 0x40385a20, 0x40385c20, 0x40385e20,
    0x40386020, 0x40386220, 0x40386420, 0x40386620, 0x40386820, 0x40386a20, 0x40386c20, 0x40386e20,
    0x40387020, 0x40387220, 0x40387420, 0x40387620, 0x40387820, 0x40387a20, 0x40387c20, 0x40387e20,
    0x40388020, 0x40388220, 0x40388420, 0x40388620, 0x40388820, 0x40388a20, 0x40388c20, 0xf0000404,
    0x00000000, 0x40026e20, 0x40021c20, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x4027e420,
    0x00000000, 0xadc00000, 0xae600000, 0xae600000, 0xae600000, 0xae600000, 0xadc00000, 0xae600000,
    0xae600000, 0xae600000, 0xade00000, 0xadc00000, 0xae600000, 0xae600000, 0xae600000, 0xae600000,
    0xae600000, 0xae600000, 0xadc00000, 0xadc00000, 0xadc00000, 0xadc00000, 0xadc00000, 0xadc00000,
    0xae600000, 0xae600000, 0xadc00000, 0xae600000, 0xae600000, 0xade00000, 0xae400000, 0xae600000,
    0xa0a08502, 0xa0b08602, 0xa0c08702, 0xa0d08802, 0xa0e08902, 0xa0f08a02, 0xa1008b02, 0xa1108c02,
    0xa1208d02, 0xa1308e02, 0xa1308e02, 0xa1408f02, 0xa1509202, 0xa1600000, 0x40055420, 0xa1709502,
    0x40055620, 0xa1809102, 0xa1909002, 0x40055820, 0xae600000, 0xadc00000, 0x40055a20, 0xa1208d02,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x40389020, 0x40389220, 0x40389420, 0x40389620, 0x40389820, 0x40389a20, 0x40389c20, 0x40389e20,
    0x4038a020, 0x4038a220, 0x0038a499, 0x4038a420, 0x4038a620, 0x0038a899, 0x4038a820, 0x0038aa99,
    0x4038aa20, 0x4038ac20, 0x4038ae20, 0x0038b099, 0x4038b020, 0x0038b299, 0x4038b220, 0x4038b420,
    0x4038b620, 0x4038b820, 0x4038ba20, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0xe0000464, 0xe0000467, 0xe000046a, 0x40055c20, 0x40055e20, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0xa0000000, 0x00000000, 0x40096620, 0x40096a20,
    0x40070820, 0x4004f220, 0x4004f620, 0x4027e620, 0x40024820, 0x40024a20, 0x40070e20, 0x40071020,
    0xae600000, 0xae600000, 0xae600000, 0xae600000, 0xae600000, 0xae600000, 0xae600000, 0xae600000,
    0xa1e00000, 0xa1f00000, 0xa2000000, 0x40026420, 0x00000000, 0x00000000, 0x40027020, 0x4002cc20,
    0x403aa220, 0x40391c20, 0x40391e20, 0x40392020, 0x40392620, 0x40392820, 0x40393020, 0xc0520151,
    0x40393c20, 0x40395420, 0x40395620, 0x40395820, 0x40396420, 0x40397220, 0x40397420, 0x40398820,
    0x40398a20, 0x4039a420, 0x4039a620, 0x4039c620, 0x4039c820, 0x4039dc20, 0x4039de20, 0x4039e620,
    0x4039e820, 0x4039ee20, 0x4039f020, 0x403a3820, 0x403a3a20, 0x403a9c20, 0x403a9e20, 0x403aa020,
    0xa0000000, 0x4039fc20, 0x403a1220, 0x403a1a20, 0x403a4020, 0x403a4e20, 0x403a5620, 0x403a6820,
    0xc0560171, 0x403a8e20, 0xc0580171, 0xa1b0a202, 0xa1c0a502, 0xa1d0a902, 0xa1e0ad02, 0xa1f0b202,
    0xa200b602, 0xa210ba02, 0xa220bc02, 0xae60bd02, 0xae60be02, 0xadc0bf02, 0xadc0c102, 0xae60c202,
    0xae60c302, 0xae60c402, 0xae60c502, 0xae60c602, 0xadc0c702, 0xae60c802, 0xae60c902, 0xadc0c002,
    0xe0000006, 0xe000000f, 0xe0000020, 0xe0000029, 0xe0000036, 0xe000003f, 0xe0000048, 0xe0000051,
    0xe000005a, 0xe0000063, 0x4004ee20, 0x40024c20, 0x40024e20, 0x4004de20, 0x40393a20, 0x403a1020,
    0xa230d102, 0x40392420, 0x40392220, 0x40392a20, 0x00391c84, 0xf0000404, 0xf0000404, 0xf0000404,
    0xf0000404, 0x40395a20, 0x40395c20, 0x40393e20, 0x40395e20, 0x40396020, 0x40394020, 0x40396220,
    0x40394220, 0x40397620, 0x40397820, 0x40396620, 0x40396820, 0x40397a20, 0x40396a20, 0x40396e20,
    0x40398c20, 0x40398e20, 0x40399020, 0x40399220, 0x40399420, 0x40399620, 0x40399820, 0x40399a20,
    0x40399c20, 0x4039a820, 0x4039aa20, 0x4039ac20, 0x4039ae20, 0x4039b020, 0x4039b220, 0x4039b420,
    0x4039b620, 0x4039b820, 0x4039ca20, 0x4039cc20, 0x4039ce20, 0x4039e020, 0x4039e220, 0x4039ea20,
    0x4039f220, 0x4039fe20, 0x403a0020, 0x403a0220, 0x403a0420, 0x403a0820, 0x403a0a20, 0x403a1420,
    0x403a1620, 0x403a1c20, 0x403a1e20, 0x403a2020, 0x403a2220, 0x403a2620, 0x403a2820, 0x403a2a20,
    0x403a2c20, 0x403a2e20, 0x403a3020, 0x403a3220, 0x403a3420, 0x403a4220, 0x403a4420, 0x403a4620,
    0x403a4820, 0x403a6020, 0x403a5820, 0x403a5a20, 0x403a5c20, 0x403a5e20, 0x403a6a20, 0x40396c20,
    0xe0000476, 0x403a6c20, 0xe0000473, 0x403a6e20, 0x403a7620, 0x403a7820, 0x403a7a20, 0x403a7c20,
    0x403a7e20, 0x403a8020, 0x403a8220, 0x403a8420, 0x403a9220, 0x403a9420, 0x403a9620, 0x403a8620,
    0x403a9820, 0x403a9a20, 0x403aaa20, 0xe0000479, 0x4002e820, 0x403a7220, 0xae600000, 0xae600000,
    0xae600000, 0xae600000, 0xae600000, 0xae600000, 0xae600000, 0xa0000000, 0x40071220, 0xae600000,
    0xae600000, 0xae600000, 0xae600000, 0xadc00000, 0xae600000, 0x003a7484, 0x003a9084, 0xae600000,
    0xae600000, 0x40071420, 0xadc00000, 0xae600000, 0xae600000, 0xadc00000, 0x40399e20, 0x4039ba20,
    0xe0000009, 0xe0000012, 0xe0000023, 0xe000002c, 0xe0000039, 0xe0000042, 0xe000004b, 0xe0000054,
    0xe000005d, 0xe0000066, 0x4039d020, 0x4039e420, 0x4039f420, 0xe000046d, 0xe0000470, 0x403a7020,
    0x40035c20, 0x4002ea20, 0x4002ec20, 0x40027220, 0x40027420, 0x40027620, 0x40027820, 0x40027a20,
    0x40027c20, 0x4002ce20, 0x40056020, 0x40056220, 0x40056420, 0x40056620, 0x00000000, 0xa0000000,
    0x403ab020, 0xa240d202, 0x403ab220, 0x403ab420, 0xe000047f, 0x403ab820, 0x403ab620, 0x403aba20,
    0x403abc20, 0x403abe20, 0x403ac220, 0x403ac420, 0xe0000488, 0x403ac620, 0x403ac820, 0x403aca20,
    0x403ace20, 0x403ad020, 0x403ad220, 0x403ad420, 0x003ad499, 0x403ad620, 0x403ad820, 0xe000048b,
    0x403adc20, 0x403ade20, 0x403ae020, 0x403ae220, 0x403ae420, 0xe000047c, 0xe0000482, 0xe0000485,
    0xae60d302, 0xadc0d402, 0xae60d502, 0xae60d602, 0xadc0d702, 0xae60d802, 0xae60d902, 0xadc0da02,
    0xadc0db02, 0xadc0dc02, 0xae60dd02, 0xadc0de02, 0xadc0df02, 0xae60e002, 0xadc0e102, 0xae60e202,
    0xae600000, 0xae605f02, 0xadc06002, 0xae600000, 0xadc00000, 0xae605f02, 0xadc06002, 0xae600000,
    0xadc00000, 0xae600000, 0xae600000, 0x00000000, 0x00000000, 0x403ac020, 0x403acc20, 0x403ada20,
    0x40394420, 0x40394620, 0x40394820, 0x40394a20, 0x40394c20, 0x40394e20, 0x40395220, 0x40397c20,
    0x40397e20, 0x4039a020, 0x4039a220, 0x4039bc20, 0x4039d220, 0x4039f620, 0x4039f820, 0x4039fa20,
    0x403a0c20, 0x403a0e20, 0x403a3620, 0x403a3c20, 0x403a3e20, 0x403a5020, 0x403a5220, 0x403a6220,
    0x403a6420, 0x403a6620, 0x403a4a20, 0x4039be20, 0x4039c020, 0x4039d420, 0x40398020, 0x40398220,
    0x4039d620, 0x4039c220, 0x40398420, 0x40392c20, 0x40392e20, 0x403aa420, 0x403aa620, 0x403aa820,
    0x403a8820, 0x403a8a20, 0x403aac20, 0x403aae20, 0x40398620, 0x4039d820, 0x4039da20, 0x403a2420,
    0x403b1820, 0x403b1e20, 0x403b2020, 0x403b2220, 0x403b2620, 0x403b2820, 0x403b2a20, 0x403b2c20,
    0x403b3220, 0x403b3620, 0x403b3820, 0x403b3a20, 0x403b3e20, 0x403b4620, 0x403b4820, 0x403b4c20,
    0x403b4e20, 0x403b5620, 0x403b5820, 0x403b5a20, 0x403b5c20, 0x403b5e20, 0x403b6020, 0x403b6220,
    0x403b4020, 0x403b1a20, 0x403b1c20, 0x403b3c20, 0x403b2420, 0x403b5020, 0x403b5220, 0x403b5420,
    0x403b4220, 0x403b4420, 0x403b2e20, 0x403b3020, 0x403b4a20, 0x403b3420, 0x403b6620, 0x403b6820,
    0x403b6a20, 0x403b6c20, 0x403b6e20, 0x403b7020, 0x403b7220, 0x403b7420, 0x403b7620, 0x403b7820,
    0x403b7a20, 0x403b6420, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0xe000000c, 0xe0000015, 0xe0000026, 0xe000002f, 0xe000003c, 0xe0000045, 0xe000004e, 0xe0000057,
    0xe0000060, 0xe0000069, 0x403b7c20, 0x403b7e20, 0x403b8020, 0x403b8220, 0x403b8420, 0x403b8620,
    0x403b8820, 0x403b8a20, 0x403b8c20, 0x403b8e20, 0x403b9020, 0x403b9220, 0x403b9420, 0x403b9620,
    0x403b9820, 0x403b9a20, 0x403b9c20, 0x403b9e20, 0x403ba020, 0x403ba220, 0x403ba420, 0x403ba620,
    0x403ba820, 0x403baa20, 0x403bac20, 0x403bae20, 0x403bb020, 0x403bb220, 0x403bb420, 0x403bb620,
    0xe000048e, 0xe0000491, 0xe0000494, 0xae60e302, 0xae60e402, 0xae60e502, 0xae60e602, 0xae60e702,
    0xae60e802, 0xae60e902, 0xadc0ea02, 0xae60eb02, 0x403bb820, 0x403bba20, 0x40073820, 0x40035e20,
    0x40025020, 0x4002c020, 0xa0000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x0029cc95, 0x0029ce95, 0x0029d095, 0x0029d295, 0x0029d495, 0x0029d695, 0x0029d895, 0x0029da95,
    0x0029dc95, 0x0029de95, 0x00093895, 0x00094e95, 0x00094295, 0x0003f495, 0x0003f695, 0x00000000,
    0x002bde95, 0x002c9895, 0x002ee295, 0x0030f695, 0x002cb895, 0x002d6895, 0x002dfe95, 0x002e2295,
    0x002e8295, 0x002e9e95, 0x002f2c95, 0x002fe695, 0x00302c95, 0x00000000, 0x00000000, 0x00000000,
    0x4027f820, 0x4027fa20, 0x4027fc20, 0x4027fe20, 0x40280020, 0x40280220, 0x40280420, 0x40280620,
    0x40282c20, 0x40280820, 0x40280a20, 0x40280c20, 0x40280e20, 0x40281020, 0x40281220, 0x40281420,
    0x40281620, 0x40281820, 0x40281a20, 0x40281c20, 0x40281e20, 0x40282020, 0x40282220, 0x40282420,
    0x40282620, 0x40282820, 0x40282a20, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x0002ba83, 0x0003e083, 0x0004ea83, 0x0027de83, 0x0004ec83, 0x0004e683, 0x0003d283,
    0x0003f483, 0x0003f683, 0x0004d883, 0x00093883, 0x00024083, 0x00021a83, 0x0002e483, 0x0004e283,
    0x0029cc83, 0x0029ce83, 0x0029d083, 0x0029d283, 0x0029d483, 0x0029d683, 0x0029d883, 0x0029da83,
    0x0029dc83, 0x0029de83, 0x00026c83, 0x00026283, 0x00094083, 0x00094283, 0x00094483, 0x0002c483,
    0x0004d683, 0x002bde89, 0x002c0a89, 0x002c3a89, 0x002c6289, 0x002c9889, 0x002d0889, 0x002d2289,
    0x002d6889, 0x002d9a89, 0x002dcc89, 0x002dfe89, 0x002e2289, 0x002e8289, 0x002e9e89, 0x002ee289,
    0x002f2c89, 0x002f5689, 0x002f7a89, 0x002fe689, 0x00302c89, 0x00306c89, 0x0030be89, 0x0030e289,
    0x0030f689, 0x00310089, 0x00312a89, 0x0003f883, 0x0004e483, 0x0003fa83, 0x00062483, 0x00021683,
];

/// Subset of Go `mainExpandElem`.
static SUBSET_EXPAND_ELEM: [u32; 1175] = [
    0x00000002, 0xae604702, 0xae603202, 0x00000002, 0x40062c20, 0xae603202, 0x00000002, 0x4029cc20,
    0xa0013f02, 0x00000002, 0x4029cc20, 0xa0014002, 0x00000002, 0x4029cc20, 0xa0014202, 0x00000002,
    0x4029ce20, 0xa0013f02, 0x00000002, 0x4029ce20, 0xa0014002, 0x00000002, 0x4029ce20, 0xa0014202,
    0x00000003, 0x0029ce9e, 0x0009589e, 0x0029d09e, 0x00000003, 0x0029ce9e, 0x0009589e, 0x0029d49e,
    0x00000002, 0x4029d020, 0xa0013f02, 0x00000002, 0x4029d020, 0xa0014002, 0x00000002, 0x4029d020,
    0xa0014202, 0x00000002, 0x4029d220, 0xa0013f02, 0x00000002, 0x4029d220, 0xa0014002, 0x00000002,
    0x4029d220, 0xa0014202, 0x00000003, 0x0029d29e, 0x0009589e, 0x0029d49e, 0x00000002, 0x4029d420,
    0xa0013f02, 0x00000002, 0x4029d420, 0xa0014002, 0x00000002, 0x4029d420, 0xa0014202, 0x00000002,
    0x4029d620, 0xa0013f02, 0x00000002, 0x4029d620, 0xa0014002, 0x00000002, 0x4029d620, 0xa0014202,
    0x00000002, 0x4029d820, 0xa0013f02, 0x00000002, 0x4029d820, 0xa0014002, 0x00000002, 0x4029d820,
    0xa0014202, 0x00000002, 0x4029da20, 0xa0013f02, 0x00000002, 0x4029da20, 0xa0014002, 0x00000002,
    0x4029da20, 0xa0014202, 0x00000002, 0x4029dc20, 0xa0013f02, 0x00000002, 0x4029dc20, 0xa0014002,
    0x00000002, 0x4029dc20, 0xa0014202, 0x00000002, 0x4029de20, 0xa0013f02, 0x00000002, 0x4029de20,
    0xa0014002, 0x00000002, 0x4029de20, 0xa0014202, 0x00000002, 0x402bde20, 0xae603202, 0x00000002,
    0x002bde88, 0xae603202, 0x00000002, 0x402bde20, 0xae603502, 0x00000002, 0x002bde88, 0xae603502,
    0x00000002, 0x402bde20, 0xae603702, 0x00000002, 0x002bde88, 0xae603702, 0x00000002, 0x402bde20,
    0xae603c02, 0x00000002, 0x002bde88, 0xae603c02, 0x00000002, 0x402bde20, 0xae604102, 0x00000002,
    0x002bde88, 0xae604102, 0x00000002, 0x402bde20, 0xae604302, 0x00000002, 0x002bde88, 0xae604302,
    0x00000003, 0x402bde20, 0xae604302, 0xae603202, 0x00000003, 0x002bde88, 0xae604302, 0xae603202,
    0x00000002, 0x402bde20, 0xae604702, 0x00000002, 0x002bde88, 0xae604702, 0x00000003, 0x402bde20,
    0xae604702, 0xae605b02, 0x00000003, 0x002bde88, 0xae604702, 0xae605b02, 0x00000002, 0x402bde20,
    0xae604e02, 0x00000002, 0x002bde88, 0xae604e02, 0x00000002, 0x402bde20, 0xae605202, 0x00000002,
    0x002bde88, 0xae605202, 0x00000003, 0x402bde20, 0xae605202, 0xae605b02, 0x00000003, 0x002bde88,
    0xae605202, 0xae605b02, 0x00000002, 0x402bde20, 0xaca05902, 0x00000002, 0x002bde88, 0xaca05902,
    0x00000002, 0x402bde20, 0xae605b02, 0x00000002, 0x002bde88, 0xae605b02, 0x00000002, 0x402bde20,
    0xae606502, 0x00000002, 0x002bde88, 0xae606502, 0x00000002, 0x402bde20, 0xae606702, 0x00000002,
    0x002bde88, 0xae606702, 0x00000003, 0x002bde84, 0xa0013904, 0x002c9884, 0x00000003, 0x002bde8a,
    0xa0013904, 0x002c988a, 0x00000004, 0x002bde84, 0xa0013904, 0x002c9884, 0xae603202, 0x00000004,
    0x002bde8a, 0xa0013904, 0x002c988a, 0xae603202, 0x00000004, 0x002bde84, 0xa0013904, 0x002c9884,
    0xae605b02, 0x00000004, 0x002bde8a, 0xa0013904, 0x002c988a, 0xae605b02, 0x00000002, 0x402c3a20,
    0xae603202, 0x00000002, 0x002c3a88, 0xae603202, 0x00000002, 0x402c3a20, 0xae603c02, 0x00000002,
    0x002c3a88, 0xae603c02, 0x00000002, 0x402c3a20, 0xae604102, 0x00000002, 0x002c3a88, 0xae604102,
    0x00000002, 0x402c3a20, 0xae605202, 0x00000002, 0x002c3a88, 0xae605202, 0x00000002, 0x402c3a20,
    0xaca05602, 0x00000002, 0x002c3a88, 0xaca05602, 0x00000002, 0x402c6220, 0xae604102, 0x00000002,
    0x002c6288, 0xae604102, 0x00000002, 0x402c6220, 0xa0007d02, 0x00000002, 0x002c6288, 0xa0007d02,
    0x00000002, 0x002c6284, 0xa0013904, 0x00000002, 0x002c628a, 0xa0013904, 0x00000002, 0x002c6284,
    0x002c0a84, 0x00000002, 0x002c6284, 0x00312a84, 0x00000003, 0x002c6284, 0x00312a84, 0xa0004104,
    0x00000003, 0x002c628a, 0x00312a84, 0xa0004104, 0x00000003, 0x002c628a, 0x00312a8a, 0xa0004104,
    0x00000002, 0x002c6284, 0x00315084, 0x00000002, 0x002c6284, 0x00316484, 0x00000002, 0x402c9820,
    0xae603202, 0x00000002, 0x002c9888, 0xae603202, 0x00000002, 0x402c9820, 0xae603502, 0x00000002,
    0x002c9888, 0xae603502, 0x00000002, 0x402c9820, 0xae603702, 0x00000002, 0x002c9888, 0xae603702,
    0x00000002, 0x402c9820, 0xae603c02, 0x00000002, 0x002c9888, 0xae603c02, 0x00000002, 0x402c9820,
    0xae604102, 0x00000002, 0x002c9888, 0xae604102, 0x00000002, 0x402c9820, 0xae604702, 0x00000002,
    0x002c9888, 0xae604702, 0x00000002, 0x402c9820, 0xae605202, 0x00000002, 0x002c9888, 0xae605202,
    0x00000002, 0x402c9820, 0xaca05602, 0x00000002, 0x002c9888, 0xaca05602, 0x00000002, 0x402c9820,
    0xaca05902, 0x00000002, 0x002c9888, 0xaca05902, 0x00000002, 0x402c9820, 0xae605b02, 0x00000002,
    0x002c9888, 0xae605b02, 0x00000002, 0x402c9820, 0xae606502, 0x00000002, 0x002c9888, 0xae606502,
    0x00000002, 0x402c9820, 0xae606702, 0x00000002, 0x002c9888, 0xae606702, 0x00000002, 0x002d0884,
    0x002eda84, 0x00000002, 0x402d2220, 0xae603202, 0x00000002, 0x002d2288, 0xae603202, 0x00000002,
    0x402d2220, 0xae603702, 0x00000002, 0x002d2288, 0xae603702, 0x00000002, 0x402d2220, 0xae603c02,
    0x00000002, 0x002d2288, 0xae603c02, 0x00000002, 0x402d2220, 0xae604102, 0x00000002, 0x002d2288,
    0xae604102, 0x00000002, 0x402d2220, 0xae605202, 0x00000002, 0x002d2288, 0xae605202, 0x00000002,
    0x402d2220, 0xaca05602, 0x00000002, 0x002d2288, 0xaca05602, 0x00000002, 0x402d6820, 0xae603c02,
    0x00000002, 0x002d6888, 0xae603c02, 0x00000002, 0x402d6820, 0xae604102, 0x00000002, 0x002d6888,
    0xae604102, 0x00000002, 0x402d6820, 0xa0007d02, 0x00000002, 0x002d6888, 0xa0007d02, 0x00000002,
    0x402d9a20, 0xae603202, 0x00000002, 0x002d9a88, 0xae603202, 0x00000002, 0x402d9a20, 0xae603502,
    0x00000002, 0x002d9a88, 0xae603502, 0x00000002, 0x402d9a20, 0xae603702, 0x00000002, 0x002d9a88,
    0xae603702, 0x00000002, 0x402d9a20, 0xae603c02, 0x00000002, 0x002d9a88, 0xae603c02, 0x00000002,
    0x402d9a20, 0xae604102, 0x00000002, 0x002d9a88, 0xae604102, 0x00000002, 0x402d9a20, 0xae604702,
    0x00000002, 0x002d9a88, 0xae604702, 0x00000002, 0x402d9a20, 0xae604e02, 0x00000002, 0x002d9a88,
    0xae604e02, 0x00000002, 0x002d9a88, 0xae605202, 0x00000002, 0x402d9a20, 0xaca05902, 0x00000002,
    0x002d9a88, 0xaca05902, 0x00000002, 0x402d9a20, 0xae605b02, 0x00000002, 0x002d9a88, 0xae605b02,
    0x00000002, 0x402d9a20, 0xae606502, 0x00000002, 0x002d9a88, 0xae606502, 0x00000002, 0x402d9a20,
    0xae606702, 0x00000002, 0x002d9a88, 0xae606702, 0x00000002, 0x402dcc20, 0xae603c02, 0x00000002,
    0x002dcc88, 0xae603c02, 0x00000002, 0x402dcc20, 0xae604102, 0x00000002, 0x402dfe20, 0xae604102,
    0x00000002, 0x002dfe88, 0xae604102, 0x00000002, 0x402dfe20, 0xaca05602, 0x00000002, 0x002dfe88,
    0xaca05602, 0x00000002, 0x402e2220, 0xae603202, 0x00000002, 0x002e2288, 0xae603202, 0x00000002,
    0x402e2220, 0xae604102, 0x00000002, 0x002e2288, 0xae604102, 0x00000002, 0x402e2220, 0xaca05602,
    0x00000002, 0x002e2288, 0xaca05602, 0x00000002, 0x402e2220, 0xa0007d02, 0x00000002, 0x002e2288,
    0xa0007d02, 0x00000002, 0x402e2220, 0xa0013902, 0x00000002, 0x402e2220, 0xa0013902, 0x00000002,
    0x002e2288, 0xa0013902, 0x00000002, 0x002e2288, 0xa0013902, 0x00000002, 0x002e2284, 0x002fe684,
    0x00000002, 0x002e2284, 0x00312a84, 0x00000002, 0x402e9e20, 0xae603202, 0x00000002, 0x002e9e88,
    0xae603202, 0x00000002, 0x402e9e20, 0xae603502, 0x00000002, 0x002e9e88, 0xae603502, 0x00000002,
    0x402e9e20, 0xae604102, 0x00000002, 0x002e9e88, 0xae604102, 0x00000002, 0x402e9e20, 0xae604e02,
    0x00000002, 0x002e9e88, 0xae604e02, 0x00000002, 0x402e9e20, 0xaca05602, 0x00000002, 0x002e9e88,
    0xaca05602, 0x00000002, 0x402ee220, 0xae603202, 0x00000002, 0x002ee288, 0xae603202, 0x00000002,
    0x402ee220, 0xae603502, 0x00000002, 0x002ee288, 0xae603502, 0x00000002, 0x402ee220, 0xae603702,
    0x00000002, 0x002ee288, 0xae603702, 0x00000002, 0x402ee220, 0xae603c02, 0x00000002, 0x002ee288,
    0xae603c02, 0x00000002, 0x402ee220, 0xae604102, 0x00000002, 0x002ee288, 0xae604102, 0x00000002,
    0x402ee220, 0xae604702, 0x00000002, 0x002ee288, 0xae604702, 0x00000003, 0x402ee220, 0xae604702,
    0xae605b02, 0x00000003, 0x002ee288, 0xae604702, 0xae605b02, 0x00000002, 0x402ee220, 0xae604d02,
    0x00000002, 0x002ee288, 0xae604d02, 0x00000002, 0x402ee220, 0xae604e02, 0x00000002, 0x002ee288,
    0xae604e02, 0x00000003, 0x402ee220, 0xae604e02, 0xae605b02, 0x00000003, 0x002ee288, 0xae604e02,
    0xae605b02, 0x00000002, 0x402ee220, 0xae605202, 0x00000002, 0x002ee288, 0xae605202, 0x00000003,
    0x402ee220, 0xae605202, 0xae605b02, 0x00000003, 0x002ee288, 0xae605202, 0xae605b02, 0x00000002,
    0x402ee220, 0xa0005402, 0x00000002, 0x002ee288, 0xa0005402, 0x00000003, 0x402ee220, 0xa0005402,
    0xae603202, 0x00000003, 0x002ee288, 0xa0005402, 0xae603202, 0x00000002, 0x402ee220, 0xaca05902,
    0x00000002, 0x002ee288, 0xaca05902, 0x00000003, 0x402ee220, 0xaca05902, 0xae605b02, 0x00000003,
    0x002ee288, 0xaca05902, 0xae605b02, 0x00000002, 0x402ee220, 0xae605b02, 0x00000002, 0x002ee288,
    0xae605b02, 0x00000002, 0x402ee220, 0xae606502, 0x00000002, 0x002ee288, 0xae606502, 0x00000002,
    0x402ee220, 0xae606702, 0x00000002, 0x002ee288, 0xae606702, 0x00000002, 0x402ee220, 0xad806802,
    0x00000002, 0x002ee288, 0xad806802, 0x00000003, 0x002ee284, 0xa0013904, 0x002c9884, 0x00000003,
    0x002ee28a, 0xa0013904, 0x002c988a, 0x00000002, 0x002f5684, 0x002f2c84, 0x00000002, 0x402f7a20,
    0xae603202, 0x00000002, 0x002f7a88, 0xae603202, 0x00000002, 0x402f7a20, 0xae604102, 0x00000002,
    0x002f7a88, 0xae604102, 0x00000002, 0x402f7a20, 0xaca05602, 0x00000002, 0x002f7a88, 0xaca05602,
    0x00000002, 0x402f7a20, 0xae606502, 0x00000002, 0x002f7a88, 0xae606502, 0x00000002, 0x402f7a20,
    0xae606702, 0x00000002, 0x002f7a88, 0xae606702, 0x00000002, 0x402fe620, 0xae603202, 0x00000002,
    0x002fe688, 0xae603202, 0x00000002, 0x402fe620, 0xae603c02, 0x00000002, 0x002fe688, 0xae603c02,
    0x00000002, 0x402fe620, 0xae604102, 0x00000002, 0x002fe688, 0xae604102, 0x00000002, 0x402fe620,
    0xaca05602, 0x00000002, 0x002fe688, 0xaca05602, 0x00000002, 0x402fe620, 0xadc07702, 0x00000002,
    0x002fe688, 0xadc07702, 0x00000002, 0x002fe684, 0xa0013a04, 0x00000003, 0x002fe684, 0xa0013904,
    0x002fe684, 0x00000002, 0x40302c20, 0xae604102, 0x00000002, 0x00302c88, 0xae604102, 0x00000002,
    0x40302c20, 0xaca05602, 0x00000002, 0x00302c88, 0xaca05602, 0x00000002, 0x40302c20, 0xadc07702,
    0x00000002, 0x00302c88, 0xadc07702, 0x00000002, 0x00302c84, 0x002c5684, 0x00000002, 0x00302c84,
    0x002fe684, 0x00000002, 0x00302c84, 0x002fe684, 0x00000002, 0x00302c84, 0x00300884, 0x00000002,
    0x40306c20, 0xae603202, 0x00000002, 0x00306c88, 0xae603202, 0x00000002, 0x40306c20, 0xae603502,
    0x00000002, 0x00306c88, 0xae603502, 0x00000002, 0x40306c20, 0xae603702, 0x00000002, 0x00306c88,
    0xae603702, 0x00000002, 0x40306c20, 0xae603c02, 0x00000002, 0x00306c88, 0xae603c02, 0x00000002,
    0x40306c20, 0xae604102, 0x00000002, 0x00306c88, 0xae604102, 0x00000002, 0x40306c20, 0xae604302,
    0x00000002, 0x00306c88, 0xae604302, 0x00000002, 0x40306c20, 0xae604702, 0x00000002, 0x00306c88,
    0xae604702, 0x00000003, 0x40306c20, 0xae604702, 0xae603202, 0x00000003, 0x00306c88, 0xae604702,
    0xae603202, 0x00000003, 0x40306c20, 0xae604702, 0xae603502, 0x00000003, 0x00306c88, 0xae604702,
    0xae603502, 0x00000003, 0x40306c20, 0xae604702, 0xae604102, 0x00000003, 0x00306c88, 0xae604702,
    0xae604102, 0x00000003, 0x40306c20, 0xae604702, 0xae605b02, 0x00000003, 0x00306c88, 0xae604702,
    0xae605b02, 0x00000002, 0x40306c20, 0xae604d02, 0x00000002, 0x00306c88, 0xae604d02, 0x00000002,
    0x40306c20, 0xae604e02, 0x00000002, 0x00306c88, 0xae604e02, 0x00000002, 0x40306c20, 0xaca05902,
    0x00000002, 0x00306c88, 0xaca05902, 0x00000002, 0x40306c20, 0xae605b02, 0x00000002, 0x00306c88,
    0xae605b02, 0x00000002, 0x40306c20, 0xae606502, 0x00000002, 0x00306c88, 0xae606502, 0x00000002,
    0x40306c20, 0xae606702, 0x00000002, 0x00306c88, 0xae606702, 0x00000002, 0x40306c20, 0xad806802,
    0x00000002, 0x00306c88, 0xad806802, 0x00000002, 0x4030e220, 0xae603c02, 0x00000002, 0x0030e288,
    0xae603c02, 0x00000002, 0x40310020, 0xae603202, 0x00000002, 0x00310088, 0xae603202, 0x00000002,
    0x40310020, 0xae603c02, 0x00000002, 0x00310088, 0xae603c02, 0x00000002, 0x40310020, 0xae604702,
    0x00000002, 0x00310088, 0xae604702, 0x00000002, 0x40310020, 0xae605b02, 0x00000002, 0x00310088,
    0xae605b02, 0x00000002, 0x40312a20, 0xae603202, 0x00000002, 0x00312a88, 0xae603202, 0x00000002,
    0x40312a20, 0xae604102, 0x00000002, 0x00312a88, 0xae604102, 0x00000002, 0x40312a20, 0xae605202,
    0x00000002, 0x00312a88, 0xae605202, 0x00000002, 0x00312a84, 0x0030e284, 0x00000002, 0x40316420,
    0xae604102, 0x00000002, 0x00316488, 0xae604102, 0x00000002, 0x40325220, 0xae603202, 0x00000002,
    0x00325288, 0xae603202, 0x00000002, 0x40325c20, 0xae603202, 0x00000002, 0x00325c88, 0xae603202,
    0x00000002, 0x40326820, 0xae603202, 0x00000002, 0x00326888, 0xae603202, 0x00000002, 0x40326c20,
    0xae603202, 0x00000002, 0x00326c88, 0xae603202, 0x00000002, 0x40326c20, 0xae604702, 0x00000002,
    0x00326c88, 0xae604702, 0x00000003, 0x40326c20, 0xae604702, 0xae603202, 0x00000003, 0x00327084,
    0x00325284, 0x00326c84, 0x00000003, 0x0032708a, 0x00325284, 0x00326c84, 0x00000002, 0x40327c20,
    0xae603202, 0x00000002, 0x00327c88, 0xae603202, 0x00000002, 0x40329820, 0xae603202, 0x00000002,
    0x00329888, 0xae603202, 0x00000002, 0x40329820, 0xae604702, 0x00000002, 0x00329888, 0xae604702,
    0x00000003, 0x40329820, 0xae604702, 0xae603202, 0x00000002, 0x4032a220, 0xae603202, 0x00000002,
    0x0032a288, 0xae603202, 0x00000002, 0x00336284, 0xa0013a04, 0x00000002, 0x0033628a, 0xa0013a04,
    0x00000002, 0x4033b220, 0xae603502, 0x00000002, 0x0033b288, 0xae603502, 0x00000002, 0x4033b220,
    0xae604702, 0x00000002, 0x0033b288, 0xae604702, 0x00000002, 0x4033ca20, 0xae603702, 0x00000002,
    0x0033ca88, 0xae603702, 0x00000002, 0x40341420, 0xae603502, 0x00000002, 0x00341488, 0xae603502,
    0x00000002, 0x40341420, 0xae605b02, 0x00000002, 0x00341488, 0xae605b02, 0x00000002, 0x40357220,
    0xae605b02, 0x00000002, 0x00357288, 0xae605b02, 0x00000002, 0x00389a84, 0x00389a84, 0x00000002,
    0x00389a84, 0x0038a284, 0x00000002, 0x0038a284, 0x0038a284, 0x00000002, 0x00391c84, 0xa0013a04,
    0x00000002, 0x003a4e84, 0xa0013a04, 0x00000002, 0x403a6c20, 0xae60be02, 0x00000002, 0x403a7220,
    0xae60be02, 0x00000002, 0x403aaa20, 0xae60be02, 0x00000002, 0x003ab284, 0xa0013c04, 0x00000002,
    0x003ab484, 0xa0013a04, 0x00000002, 0x003ab484, 0xa0013c04, 0x00000002, 0x003ab884, 0xa0013c04,
    0x00000002, 0x003ac484, 0xa0013a04, 0x00000002, 0x003ad884, 0xa0013a04, 0x00000002, 0x003b9484,
    0xa0013904, 0x00000002, 0x003b9684, 0xa0013904, 0x00000002, 0x003b9a84, 0xa0013904,
];

/// Subset of Go `mainContractElem`.
static SUBSET_CONTRACT_ELEM: [u32; 90] = [
    0x402e2220, 0xe0000229, 0xe0000229, 0x002e2288, 0xe000022f, 0xe000022f, 0x40332220, 0x40332a20,
    0x40333220, 0x00332288, 0x00332a88, 0x00333288, 0x40333a20, 0x40334220, 0x00333a88, 0x00334288,
    0x40336220, 0x4033a220, 0x4033a220, 0x00336288, 0x0033a288, 0x0033a288, 0x4033b220, 0x4033ba20,
    0x0033b288, 0x0033ba88, 0x4033ca20, 0x4033d420, 0x0033ca88, 0x0033d488, 0x4033e420, 0x4033f220,
    0x0033e488, 0x0033f288, 0x40341420, 0x40343e20, 0x40342420, 0x00341488, 0x00343e88, 0x00342488,
    0x40342c20, 0x40343620, 0x00342c88, 0x00343688, 0x4034ee20, 0x4034f620, 0x0034ee88, 0x0034f688,
    0x4034fe20, 0x40350620, 0x0034fe88, 0x00350688, 0x40345020, 0x40356a20, 0x40356a20, 0x00345088,
    0x00356a88, 0x00356a88, 0x40357220, 0x40357a20, 0x40358220, 0x40358a20, 0x00357288, 0x00357a88,
    0x00358288, 0x00358a88, 0x40361820, 0x40362220, 0x00361888, 0x00362288, 0x40367e20, 0x40368620,
    0x00367e88, 0x00368688, 0x4036a820, 0x4036b020, 0x0036a888, 0x0036b088, 0x40371420, 0x40371c20,
    0x00371488, 0x00371c88, 0x40393820, 0x40391e20, 0x40392020, 0x40392820, 0x403a7420, 0x40392620,
    0x403a9020, 0x40393020,
];

/// Subset of Go `mainCTEntries`.
static SUBSET_CT_ENTRIES: [CtEntry; 25] = [
    ct(0xce, 0x01, 0x01, 0xff),
    ct(0xc2, 0x00, 0x01, 0xff),
    ct(0xb7, 0xb7, 0x00, 0x01),
    ct(0x87, 0x87, 0x00, 0x02),
    ct(0xcc, 0x00, 0x02, 0xff),
    ct(0x88, 0x88, 0x00, 0x02),
    ct(0x86, 0x86, 0x00, 0x01),
    ct(0xcc, 0x00, 0x01, 0xff),
    ct(0x88, 0x88, 0x00, 0x01),
    ct(0xcd, 0x01, 0x01, 0xff),
    ct(0xcc, 0x00, 0x01, 0xff),
    ct(0x81, 0x81, 0x00, 0x01),
    ct(0x81, 0x81, 0x00, 0x02),
    ct(0xcc, 0x00, 0x01, 0xff),
    ct(0x86, 0x86, 0x00, 0x01),
    ct(0xcc, 0x00, 0x03, 0xff),
    ct(0x8b, 0x8b, 0x00, 0x03),
    ct(0x88, 0x88, 0x00, 0x02),
    ct(0x86, 0x86, 0x00, 0x01),
    ct(0xcc, 0x00, 0x01, 0xff),
    ct(0x8f, 0x8f, 0x00, 0x01),
    ct(0xd9, 0x00, 0x01, 0xff),
    ct(0x93, 0x95, 0x00, 0x01),
    ct(0xd9, 0x00, 0x01, 0xff),
    ct(0x94, 0x94, 0x00, 0x01),
];

/// Go `norm.NFKD` decompositions of the runes whose element is a decompose
/// element (ceDecompose), sorted by rune.
static NFKD_DECOMPOSITIONS: [(u32, &str); 19] = [
    (0x0132, "IJ"),
    (0x0133, "ij"),
    (0x0149, "\u{2bc}n"),
    (0x01c7, "LJ"),
    (0x01c8, "Lj"),
    (0x01c9, "lj"),
    (0x01ca, "NJ"),
    (0x01cb, "Nj"),
    (0x01cc, "nj"),
    (0x01f1, "DZ"),
    (0x01f2, "Dz"),
    (0x01f3, "dz"),
    (0x03d3, "\u{3a5}\u{301}"),
    (0x03d4, "\u{3a5}\u{308}"),
    (0x0587, "\u{565}\u{582}"),
    (0x0675, "\u{627}\u{674}"),
    (0x0676, "\u{648}\u{674}"),
    (0x0677, "\u{6c7}\u{674}"),
    (0x0678, "\u{64a}\u{674}"),
];

/// Go `norm.NFD` LeadCCC for the subset runes from U+0080, as ranges
/// (first, last, ccc) of nonzero values. Other subset runes have LeadCCC 0.
static NFD_LEAD_CCC: [(u32, u32, u8); 115] = [
    (0x0300, 0x0314, 230),
    (0x0315, 0x0315, 232),
    (0x0316, 0x0319, 220),
    (0x031a, 0x031a, 232),
    (0x031b, 0x031b, 216),
    (0x031c, 0x0320, 220),
    (0x0321, 0x0322, 202),
    (0x0323, 0x0326, 220),
    (0x0327, 0x0328, 202),
    (0x0329, 0x0333, 220),
    (0x0334, 0x0338, 1),
    (0x0339, 0x033c, 220),
    (0x033d, 0x0344, 230),
    (0x0345, 0x0345, 240),
    (0x0346, 0x0346, 230),
    (0x0347, 0x0349, 220),
    (0x034a, 0x034c, 230),
    (0x034d, 0x034e, 220),
    (0x0350, 0x0352, 230),
    (0x0353, 0x0356, 220),
    (0x0357, 0x0357, 230),
    (0x0358, 0x0358, 232),
    (0x0359, 0x035a, 220),
    (0x035b, 0x035b, 230),
    (0x035c, 0x035c, 233),
    (0x035d, 0x035e, 234),
    (0x035f, 0x035f, 233),
    (0x0360, 0x0361, 234),
    (0x0362, 0x0362, 233),
    (0x0363, 0x036f, 230),
    (0x0483, 0x0487, 230),
    (0x0591, 0x0591, 220),
    (0x0592, 0x0595, 230),
    (0x0596, 0x0596, 220),
    (0x0597, 0x0599, 230),
    (0x059a, 0x059a, 222),
    (0x059b, 0x059b, 220),
    (0x059c, 0x05a1, 230),
    (0x05a2, 0x05a7, 220),
    (0x05a8, 0x05a9, 230),
    (0x05aa, 0x05aa, 220),
    (0x05ab, 0x05ac, 230),
    (0x05ad, 0x05ad, 222),
    (0x05ae, 0x05ae, 228),
    (0x05af, 0x05af, 230),
    (0x05b0, 0x05b0, 10),
    (0x05b1, 0x05b1, 11),
    (0x05b2, 0x05b2, 12),
    (0x05b3, 0x05b3, 13),
    (0x05b4, 0x05b4, 14),
    (0x05b5, 0x05b5, 15),
    (0x05b6, 0x05b6, 16),
    (0x05b7, 0x05b7, 17),
    (0x05b8, 0x05b8, 18),
    (0x05b9, 0x05ba, 19),
    (0x05bb, 0x05bb, 20),
    (0x05bc, 0x05bc, 21),
    (0x05bd, 0x05bd, 22),
    (0x05bf, 0x05bf, 23),
    (0x05c1, 0x05c1, 24),
    (0x05c2, 0x05c2, 25),
    (0x05c4, 0x05c4, 230),
    (0x05c5, 0x05c5, 220),
    (0x05c7, 0x05c7, 18),
    (0x0610, 0x0617, 230),
    (0x0618, 0x0618, 30),
    (0x0619, 0x0619, 31),
    (0x061a, 0x061a, 32),
    (0x064b, 0x064b, 27),
    (0x064c, 0x064c, 28),
    (0x064d, 0x064d, 29),
    (0x064e, 0x064e, 30),
    (0x064f, 0x064f, 31),
    (0x0650, 0x0650, 32),
    (0x0651, 0x0651, 33),
    (0x0652, 0x0652, 34),
    (0x0653, 0x0654, 230),
    (0x0655, 0x0656, 220),
    (0x0657, 0x065b, 230),
    (0x065c, 0x065c, 220),
    (0x065d, 0x065e, 230),
    (0x065f, 0x065f, 220),
    (0x0670, 0x0670, 35),
    (0x06d6, 0x06dc, 230),
    (0x06df, 0x06e2, 230),
    (0x06e3, 0x06e3, 220),
    (0x06e4, 0x06e4, 230),
    (0x06e7, 0x06e8, 230),
    (0x06ea, 0x06ea, 220),
    (0x06eb, 0x06ec, 230),
    (0x06ed, 0x06ed, 220),
    (0x0711, 0x0711, 36),
    (0x0730, 0x0730, 230),
    (0x0731, 0x0731, 220),
    (0x0732, 0x0733, 230),
    (0x0734, 0x0734, 220),
    (0x0735, 0x0736, 230),
    (0x0737, 0x0739, 220),
    (0x073a, 0x073a, 230),
    (0x073b, 0x073c, 220),
    (0x073d, 0x073d, 230),
    (0x073e, 0x073e, 220),
    (0x073f, 0x0741, 230),
    (0x0742, 0x0742, 220),
    (0x0743, 0x0743, 230),
    (0x0744, 0x0744, 220),
    (0x0745, 0x0745, 230),
    (0x0746, 0x0746, 220),
    (0x0747, 0x0747, 230),
    (0x0748, 0x0748, 220),
    (0x0749, 0x074a, 230),
    (0x07eb, 0x07f1, 230),
    (0x07f2, 0x07f2, 220),
    (0x07f3, 0x07f3, 230),
    (0x07fd, 0x07fd, 220),
];

/// Go `unicode.Nd` ranges inside the subset.
static ND_RANGES: [(u32, u32); 5] = [
    (0x0030, 0x0039),
    (0x0660, 0x0669),
    (0x06f0, 0x06f9),
    (0x07c0, 0x07c9),
    (0xff10, 0xff19),
];
