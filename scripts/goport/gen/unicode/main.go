// Command gen writes crates/ts_goport/src/gostd/unicode_tables.rs from the Go
// unicode package it is built with: the range tables, their maps and
// CaseRanges. Run it through gen.sh, which pins the
// go1.27.1 toolchain (Unicode 17.0.0).
//
//	gen -out unicode_tables.rs   write the Rust tables
//	gen -dump dump.txt           write a canonical text dump of the same data
//
// The dump has one line per map entry. checkrs/main.rs prints the same dump
// from the generated Rust file, so the two can be compared byte for byte.
package main

import (
	"bufio"
	"flag"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"runtime"
	"sort"
	"strings"
	"unicode"
)

const wantGo = "go1.27.1"
const wantUnicode = "17.0.0"

// table is one distinct *unicode.RangeTable and the Rust static that holds it.
type table struct {
	rust  string // Rust static name
	goVar string // Go variable in tables.go, for the "// Go:" comment
	t     *unicode.RangeTable
}

// goMap is one Go map[string]*RangeTable in tables.go.
type goMap struct {
	goName   string // Categories, Scripts, FoldCategory, FoldScript
	rustName string
	doc      []string
	prefix   string // Rust static prefix for this map's tables
	varFmt   string // Go variable of a table, from its key
	m        map[string]*unicode.RangeTable
}

func main() {
	out := flag.String("out", "", "Rust output file")
	dump := flag.String("dump", "", "canonical dump output file")
	flag.Parse()
	if runtime.Version() != wantGo {
		fail("built with %s, want %s (run gen.sh)", runtime.Version(), wantGo)
	}
	if unicode.Version != wantUnicode {
		fail("unicode.Version %s, want %s", unicode.Version, wantUnicode)
	}
	src := readTablesGo()

	maps := []goMap{
		{"Categories", "CATEGORIES", []string{"Categories is the set of Unicode category tables."}, "", "_%s", unicode.Categories},
		{"Scripts", "SCRIPTS", []string{"Scripts is the set of Unicode script tables."}, "", "_%s", unicode.Scripts},
		{"FoldCategory", "FOLD_CATEGORY", []string{
			"FoldCategory maps a category name to a table of",
			"code points outside the category that are equivalent under",
			"simple case folding to code points inside the category.",
			"If there is no entry for a category name, there are no such points.",
		}, "FOLD_", "fold%s", unicode.FoldCategory},
		{"FoldScript", "FOLD_SCRIPT", []string{
			"FoldScript maps a script name to a table of",
			"code points outside the script that are equivalent under",
			"simple case folding to code points inside the script.",
			"If there is no entry for a script name, there are no such points.",
		}, "FOLD_", "fold%s", unicode.FoldScript},
	}

	// One Rust static per distinct table pointer.
	byPtr := map[*unicode.RangeTable]*table{}
	var tables []*table
	rustNames := map[string]bool{}
	for _, gm := range maps {
		for _, k := range sortedKeys(gm.m) {
			t := gm.m[k]
			if t == nil {
				fail("%s[%q] is nil", gm.goName, k)
			}
			if _, ok := byPtr[t]; ok {
				continue
			}
			name := gm.prefix + strings.ToUpper(k)
			if rustNames[name] {
				fail("Rust name %s is used twice", name)
			}
			rustNames[name] = true
			tb := &table{rust: name, goVar: fmt.Sprintf(gm.varFmt, k), t: t}
			byPtr[t] = tb
			tables = append(tables, tb)
		}
	}
	// unicode.Cn is Categories["Cn"].
	if unicode.Cn != unicode.Categories["Cn"] {
		fail("unicode.Cn is not Categories[\"Cn\"]")
	}
	// Every alias must name a category, and the canonical keys must not clash
	// (regexp/syntax initCategoryAliases ranges over the map in random order).
	canon := map[string]string{}
	for _, k := range sortedKeys(unicode.CategoryAliases) {
		v := unicode.CategoryAliases[k]
		if unicode.Categories[v] == nil {
			fail("CategoryAliases[%q] = %q is not a category", k, v)
		}
		c := canonicalName(k)
		if old, ok := canon[c]; ok && old != v {
			fail("CategoryAliases: canonical %q maps to %q and %q", c, old, v)
		}
		canon[c] = v
	}

	checkCaseRanges()

	if *dump != "" {
		writeDump(*dump, maps, src)
	}
	if *out != "" {
		writeRust(*out, src, maps, tables, byPtr)
	}
	if *out == "" && *dump == "" {
		fail("need -out or -dump")
	}
}

// checkCaseRanges checks what the Rust port of lookupCaseRange and
// convertCase assumes: the ranges are sorted and do not overlap, and a
// Delta with UpperLower has it in all three places.
func checkCaseRanges() {
	var prevHi uint32
	for i, cr := range unicode.CaseRanges {
		if cr.Lo > cr.Hi || (i > 0 && cr.Lo <= prevHi) {
			fail("CaseRanges[%d] %X-%X is not sorted", i, cr.Lo, cr.Hi)
		}
		prevHi = cr.Hi
		n := 0
		for _, d := range cr.Delta {
			if d == unicode.UpperLower {
				n++
			} else if d > unicode.MaxRune || d < -unicode.MaxRune {
				fail("CaseRanges[%d] has delta %d", i, d)
			}
		}
		if n != 0 && n != unicode.MaxCase {
			fail("CaseRanges[%d] mixes UpperLower and deltas", i)
		}
	}
}

func writeRust(path string, src []string, maps []goMap, tables []*table, byPtr map[*unicode.RangeTable]*table) {
	var b strings.Builder
	p := func(format string, args ...any) { fmt.Fprintf(&b, format, args...) }
	p("//! Go `unicode` tables (%s `src/unicode/tables.go`, Unicode %s): the\n", wantGo, wantUnicode)
	p("//! category and script range tables, `Categories`, `Scripts`,\n")
	p("//! `CategoryAliases`, `FoldCategory`, `FoldScript`, `Cn` and `CaseRanges`.\n")
	p("//!\n")
	p("//! Code generated by `scripts/goport/gen/unicode/gen.sh`\n")
	p("//! from the Go %s `unicode` package. DO NOT EDIT.\n", wantGo)
	p("//!\n")
	p("//! PORT: Go maps are slices sorted by key. Read them with [`map_get`].\n")
	p("//! `Properties` and the exported aliases (`Upper`, `Letter`, ...) are not\n")
	p("//! generated. `regexp/syntax` does not use them.\n")
	p("\n")
	p("// Go: unicode/tables.go:%d Version\n", lineOf(src, "const Version = "))
	p("/// Version is the Unicode edition from which the tables are derived.\n")
	p("pub const VERSION: &str = %q;\n", unicode.Version)
	p("\n")
	p("// Go: unicode/letter.go:21 RangeTable\n")
	p("/// RangeTable defines a set of Unicode code points by listing the ranges of\n")
	p("/// code points within the set. The ranges are listed in two slices\n")
	p("/// to save space: a slice of 16-bit ranges and a slice of 32-bit ranges.\n")
	p("/// The two slices must be in sorted order and non-overlapping.\n")
	p("/// Also, R32 should contain only values >= 0x10000 (1<<16).\n")
	p("pub struct RangeTable {\n")
	p("    pub r16: &'static [Range16],\n")
	p("    pub r32: &'static [Range32],\n")
	p("    /// number of entries in R16 with Hi <= MaxLatin1\n")
	p("    pub latin_offset: usize,\n")
	p("}\n")
	p("\n")
	p("// Go: unicode/letter.go:29 Range16\n")
	p("/// Range16 represents of a range of 16-bit Unicode code points. The range runs from Lo to Hi\n")
	p("/// inclusive and has the specified stride.\n")
	p("/// PORT: the tuple (Lo, Hi, Stride).\n")
	p("pub type Range16 = (u16, u16, u16);\n")
	p("\n")
	p("// Go: unicode/letter.go:38 Range32\n")
	p("/// Range32 represents of a range of Unicode code points and is used when one or\n")
	p("/// more of the values will not fit in 16 bits. The range runs from Lo to Hi\n")
	p("/// inclusive and has the specified stride. Lo and Hi must always be >= 1<<16.\n")
	p("/// PORT: the tuple (Lo, Hi, Stride).\n")
	p("pub type Range32 = (u32, u32, u32);\n")
	p("\n")
	p("// Go: unicode/letter.go:56 CaseRange\n")
	p("/// CaseRange represents a range of Unicode code points for simple (one\n")
	p("/// code point to one code point) case conversion.\n")
	p("/// The range runs from Lo to Hi inclusive, with a fixed stride of 1. Deltas\n")
	p("/// are the number to add to the code point to reach the code point for a\n")
	p("/// different case for that character. They may be negative. If zero, it\n")
	p("/// means the character is in the corresponding case. There is a special\n")
	p("/// case representing sequences of alternating corresponding Upper and Lower\n")
	p("/// pairs. It appears with a fixed Delta of\n")
	p("/// `{UpperLower, UpperLower, UpperLower}`.\n")
	p("/// The constant UpperLower has an otherwise impossible delta value.\n")
	p("/// PORT: the tuple (Lo, Hi, Delta). Delta is Go `d`, indexed by\n")
	p("/// UpperCase (0), LowerCase (1) and TitleCase (2).\n")
	p("pub type CaseRange = (u32, u32, [i32; 3]);\n")
	p("\n")
	p("// Go: unicode/letter.go:83 UpperLower\n")
	p("/// If the Delta field of a [`CaseRange`] is UpperLower, it means\n")
	p("/// this CaseRange represents a sequence of the form (say)\n")
	p("/// `[Upper] [Lower] [Upper] [Lower]`.\n")
	p("/// PORT: Go `MaxRune + 1`.\n")
	p("pub const UPPER_LOWER: i32 = 0x%X;\n", unicode.UpperLower)
	p("\n")
	p("/// Go `m[key]` for a map generated as a slice sorted by key: `None` where Go\n")
	p("/// gives the zero value (nil or \"\").\n")
	p("pub fn map_get<V: Copy>(m: &[(&str, V)], key: &str) -> Option<V> {\n")
	p("    m.binary_search_by(|(k, _)| (*k).cmp(key)).ok().map(|i| m[i].1)\n")
	p("}\n")

	for _, gm := range maps {
		p("\n")
		p("// Go: unicode/tables.go:%d %s\n", lineOf(src, "var "+gm.goName+" = map[string]*RangeTable{"), gm.goName)
		for _, d := range gm.doc {
			p("/// %s\n", d)
		}
		p("pub static %s: &[(&str, &RangeTable)] = &[\n", gm.rustName)
		for _, k := range sortedKeys(gm.m) {
			p("    (%q, &%s),\n", k, byPtr[gm.m[k]].rust)
		}
		p("];\n")
		if gm.goName == "Categories" {
			p("\n")
			p("// Go: unicode/tables.go:%d CategoryAliases\n", lineOf(src, "var CategoryAliases = map[string]string{"))
			p("/// CategoryAliases maps category aliases to standard category names.\n")
			p("pub static CATEGORY_ALIASES: &[(&str, &str)] = &[\n")
			for _, k := range sortedKeys(unicode.CategoryAliases) {
				p("    (%q, %q),\n", k, unicode.CategoryAliases[k])
			}
			p("];\n")
		}
	}

	for _, tb := range tables {
		t := tb.t
		p("\n")
		p("// Go: unicode/tables.go:%d %s\n", lineOf(src, "var "+tb.goVar+" = &RangeTable{"), tb.goVar)
		if t == unicode.Cn {
			p("// Go: unicode/tables.go:%d Cn\n", lineOf(src, "\tCn = _Cn"))
			p("/// Cn is the set of Unicode characters in category Cn (Other, not assigned).\n")
		}
		p("pub static %s: RangeTable = RangeTable {\n", tb.rust)
		if len(t.R16) == 0 {
			p("    r16: &[],\n")
		} else {
			p("    r16: &[\n")
			for _, r := range t.R16 {
				p("        (0x%04X, 0x%04X, %d),\n", r.Lo, r.Hi, r.Stride)
			}
			p("    ],\n")
		}
		if len(t.R32) == 0 {
			p("    r32: &[],\n")
		} else {
			p("    r32: &[\n")
			for _, r := range t.R32 {
				p("        (0x%X, 0x%X, %d),\n", r.Lo, r.Hi, r.Stride)
			}
			p("    ],\n")
		}
		p("    latin_offset: %d,\n", t.LatinOffset)
		p("};\n")
	}
	p("\n")
	p("// Go: unicode/tables.go:%d _CaseRanges\n", lineOf(src, "var _CaseRanges = []CaseRange{"))
	p("// Go: unicode/tables.go:%d CaseRanges\n", lineOf(src, "var CaseRanges = _CaseRanges"))
	p("/// CaseRanges is the table describing case mappings for all letters with\n")
	p("/// non-self mappings.\n")
	p("pub static CASE_RANGES: &[CaseRange] = &[\n")
	for _, cr := range unicode.CaseRanges {
		var ds [unicode.MaxCase]string
		for i, d := range cr.Delta {
			ds[i] = fmt.Sprint(d)
			if d == unicode.UpperLower {
				ds[i] = "UPPER_LOWER"
			}
		}
		p("    (0x%04X, 0x%04X, [%s, %s, %s]),\n", cr.Lo, cr.Hi, ds[0], ds[1], ds[2])
	}
	p("];\n")
	p("\n")
	p("// Go: unicode/letter.go:331 foldPair\n")
	p("/// (From, To): `SimpleFold(From)` is `To`.\n")
	p("pub type FoldPair = (u16, u16);\n")
	p("\n")
	p("// Go: unicode/tables.go:%d caseOrbit\n", lineOf(src, "var caseOrbit = []foldPair{"))
	p("/// caseOrbit is the case folding orbits that `SimpleFold` consults before\n")
	p("/// `CaseRanges` (orbits with more than two runes).\n")
	p("pub static CASE_ORBIT: &[FoldPair] = &[\n")
	for _, fp := range caseOrbit(src) {
		p("    (0x%04X, 0x%04X),\n", fp[0], fp[1])
	}
	p("];\n")
	p("\n")
	p("// Go: unicode/tables.go:%d asciiFold\n", lineOf(src, "var asciiFold = [MaxASCII + 1]uint16{"))
	p("/// asciiFold is `SimpleFold` of each ASCII rune.\n")
	p("pub static ASCII_FOLD: [u16; 128] = [\n")
	for _, f := range asciiFold(src) {
		p("    0x%04X,\n", f)
	}
	p("];\n")
	if err := os.WriteFile(path, []byte(b.String()), 0o644); err != nil {
		fail("%v", err)
	}
}

// writeDump writes every map entry as one line. Tables print as
// "r16 lo-hi/stride ... r32 ... lo=N", maps of strings as the value.
func writeDump(path string, maps []goMap, src []string) {
	f, err := os.Create(path)
	if err != nil {
		fail("%v", err)
	}
	w := bufio.NewWriter(f)
	fmt.Fprintf(w, "Version %s\n", unicode.Version)
	for _, gm := range maps {
		for _, k := range sortedKeys(gm.m) {
			fmt.Fprintf(w, "%s %s %s\n", gm.rustName, k, dumpTable(gm.m[k]))
		}
		if gm.goName == "Categories" {
			for _, k := range sortedKeys(unicode.CategoryAliases) {
				fmt.Fprintf(w, "CATEGORY_ALIASES %s %s\n", k, unicode.CategoryAliases[k])
			}
			fmt.Fprintf(w, "CN %s\n", dumpTable(unicode.Cn))
		}
	}
	for _, cr := range unicode.CaseRanges {
		fmt.Fprintf(w, "CASE_RANGES %d-%d %d,%d,%d\n", cr.Lo, cr.Hi, cr.Delta[0], cr.Delta[1], cr.Delta[2])
	}
	for _, fp := range caseOrbit(src) {
		fmt.Fprintf(w, "CASE_ORBIT %d %d\n", fp[0], fp[1])
	}
	for r, f := range asciiFold(src) {
		fmt.Fprintf(w, "ASCII_FOLD %d %d\n", r, f)
	}
	if err := w.Flush(); err != nil {
		fail("%v", err)
	}
	if err := f.Close(); err != nil {
		fail("%v", err)
	}
}

func dumpTable(t *unicode.RangeTable) string {
	var b strings.Builder
	b.WriteString("r16")
	for _, r := range t.R16 {
		fmt.Fprintf(&b, " %d-%d/%d", r.Lo, r.Hi, r.Stride)
	}
	b.WriteString(" r32")
	for _, r := range t.R32 {
		fmt.Fprintf(&b, " %d-%d/%d", r.Lo, r.Hi, r.Stride)
	}
	fmt.Fprintf(&b, " lo=%d", t.LatinOffset)
	return b.String()
}

// canonicalName is regexp/syntax/parse.go:1675 canonicalName (unexported there).
func canonicalName(name string) string {
	var b []byte
	first := true
	for i := range len(name) {
		c := name[i]
		switch {
		case c == '_' || c == '-' || c == ' ':
			c = ' '
		case first:
			if 'a' <= c && c <= 'z' {
				c -= 'a' - 'A'
			}
			first = false
		default:
			if 'A' <= c && c <= 'Z' {
				c += 'a' - 'A'
			}
		}
		if b == nil {
			if c == name[i] && c != ' ' {
				continue
			}
			b = make([]byte, i, len(name))
			copy(b, name[:i])
		}
		if c == ' ' {
			continue
		}
		b = append(b, c)
	}
	if b == nil {
		return name
	}
	return string(b)
}

var hexPair = regexp.MustCompile(`^\t\{0x([0-9A-F]+), 0x([0-9A-F]+)\},$`)
var hexOne = regexp.MustCompile(`^\t0x([0-9A-F]+),$`)

// caseOrbit reads the unexported caseOrbit of tables.go from its source text
// and checks each pair against unicode.SimpleFold.
func caseOrbit(src []string) [][2]uint16 {
	var out [][2]uint16
	for _, l := range bodyOf(src, "var caseOrbit = []foldPair{") {
		m := hexPair.FindStringSubmatch(l)
		if m == nil {
			fail("caseOrbit line %q", l)
		}
		from, to := parseHex16(m[1]), parseHex16(m[2])
		if unicode.SimpleFold(rune(from)) != rune(to) {
			fail("caseOrbit {%X, %X} does not match SimpleFold", from, to)
		}
		out = append(out, [2]uint16{from, to})
	}
	if len(out) == 0 {
		fail("caseOrbit is empty")
	}
	return out
}

// asciiFold reads the unexported asciiFold of tables.go from its source text
// and checks each value against unicode.SimpleFold.
func asciiFold(src []string) []uint16 {
	var out []uint16
	for _, l := range bodyOf(src, "var asciiFold = [MaxASCII + 1]uint16{") {
		m := hexOne.FindStringSubmatch(l)
		if m == nil {
			fail("asciiFold line %q", l)
		}
		f := parseHex16(m[1])
		if unicode.SimpleFold(rune(len(out))) != rune(f) {
			fail("asciiFold[%d] = %X does not match SimpleFold", len(out), f)
		}
		out = append(out, f)
	}
	if len(out) != unicode.MaxASCII+1 {
		fail("asciiFold has %d entries", len(out))
	}
	return out
}

// bodyOf returns the lines after the line that starts with prefix, up to the
// closing "}".
func bodyOf(src []string, prefix string) []string {
	start := lineOf(src, prefix)
	for i := start; i < len(src); i++ {
		if src[i] == "}" {
			return src[start:i]
		}
	}
	fail("tables.go: no end for %q", prefix)
	return nil
}

func parseHex16(s string) uint16 {
	var v uint16
	if _, err := fmt.Sscanf(s, "%X", &v); err != nil {
		fail("bad hex %q: %v", s, err)
	}
	return v
}

func sortedKeys[V any](m map[string]V) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

func readTablesGo() []string {
	data, err := os.ReadFile(filepath.Join(runtime.GOROOT(), "src", "unicode", "tables.go"))
	if err != nil {
		fail("%v", err)
	}
	return strings.Split(string(data), "\n")
}

var spaces = regexp.MustCompile(` +`)

// lineOf returns the 1-based line of tables.go that starts with prefix
// (runs of spaces compared as one space).
func lineOf(src []string, prefix string) int {
	want := spaces.ReplaceAllString(prefix, " ")
	for i, l := range src {
		if strings.HasPrefix(spaces.ReplaceAllString(l, " "), want) {
			return i + 1
		}
	}
	fail("tables.go has no line %q", prefix)
	return 0
}

func fail(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "gen: "+format+"\n", args...)
	os.Exit(1)
}
