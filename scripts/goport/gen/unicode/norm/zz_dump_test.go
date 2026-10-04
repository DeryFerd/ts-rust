package norm

// Dumps the Unicode 17.0.0 normalization tables (tables17.0.0.go, the go1.27
// build of x/text v0.42.0) for ts_goport gostd/norm.rs. gen.sh copies this
// file into a copy of the norm package. Output dir: $GEN_OUT.

import (
	"encoding/binary"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestDump(t *testing.T) {
	out := os.Getenv("GEN_OUT")
	if out == "" {
		t.Skip("GEN_OUT not set")
	}
	if Version != "17.0.0" {
		t.Fatalf("norm Version %s, want 17.0.0 (build with go1.27)", Version)
	}
	write := func(name string, b []byte) {
		if err := os.WriteFile(filepath.Join(out, name), b, 0o644); err != nil {
			t.Fatal(err)
		}
	}
	u16 := func(v []uint16) []byte {
		b := make([]byte, 2*len(v))
		for i, x := range v {
			binary.LittleEndian.PutUint16(b[2*i:], x)
		}
		return b
	}
	vr := func(v []valueRange) []byte {
		b := make([]byte, 0, 4*len(v))
		for _, x := range v {
			b = binary.LittleEndian.AppendUint16(b, x.value)
			b = append(b, x.lo, x.hi)
		}
		return b
	}
	write("norm_nfc_values.bin", u16(nfcValues[:]))
	write("norm_nfc_index.bin", nfcIndex[:])
	write("norm_nfc_sparse_offset.bin", u16(nfcSparseOffset[:]))
	write("norm_nfc_sparse_values.bin", vr(nfcSparseValues[:]))
	write("norm_nfkc_values.bin", u16(nfkcValues[:]))
	write("norm_nfkc_index.bin", u16(nfkcIndex[:]))
	write("norm_nfkc_sparse_offset.bin", u16(nfkcSparseOffset[:]))
	write("norm_nfkc_sparse_values.bin", vr(nfkcSparseValues[:]))
	write("norm_decomps.bin", decomps[:])
	var s strings.Builder
	fmt.Fprintf(&s, "Version %s\n", Version)
	fmt.Fprintf(&s, "ccc %#v\n", ccc)
	fmt.Fprintf(&s, "firstMulti %#x firstCCC %#x endMulti %#x firstLeadingCCC %#x firstCCCZeroExcept %#x firstStarterWithNLead %#x lastDecomp %#x maxDecomp %#x\n",
		firstMulti, firstCCC, endMulti, firstLeadingCCC, firstCCCZeroExcept, firstStarterWithNLead, lastDecomp, maxDecomp)
	fmt.Fprintf(&s, "maxNonStarters %d maxBufferSize %d maxByteBufferSize %d MaxSegmentSize %d hangulUTF8Size %d\n",
		maxNonStarters, maxBufferSize, maxByteBufferSize, MaxSegmentSize, hangulUTF8Size)
	fmt.Fprintf(&s, "lens nfcValues %d nfcIndex %d nfcSparseOffset %d nfcSparseValues %d nfkcValues %d nfkcIndex %d nfkcSparseOffset %d nfkcSparseValues %d decomps %d\n",
		len(nfcValues), len(nfcIndex), len(nfcSparseOffset), len(nfcSparseValues), len(nfkcValues), len(nfkcIndex), len(nfkcSparseOffset), len(nfkcSparseValues), len(decomps))
	write("norm_info.txt", []byte(s.String()))
}
