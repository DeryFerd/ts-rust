#!/usr/bin/env python3
"""Generate crates/ts_goport/src/core/lib_names.rs from the bundled lib files.

Usage: gen-lib-names.py [libs-dir] [out.rs]

With no libs-dir, the lib set is the one that `src/frontend/bundled/embed.rs` embeds:
crates/ts_bundled/libs, with the files in crates/ts_goport/libs in place of
the ones with the same name.

The output is a static table of the names that the bundled lib files give to
the interner (`core.rs`, `mod intern`): identifier texts, JSDoc tag names,
the words of JSDoc comments that the parser reads (`@see` or `@link`), and
quoted property names. `intern` probes the table before its shards, so these
names get ids from a reserved range with no lock, map insert or text copy.

A text that is in the table but that the parser never interns only costs table
space. A text that is missing only costs speed. Either way one text keeps one
id, because the probe depends only on the text.

The table is bucketed by the low bits of `intern::hash_str` (rustc-hash 2.1
`FxHasher::write` + `finish`, 64-bit). `hash_str` below is a copy of it,
checked against the rustc-hash test vectors. If rustc-hash changes its hash,
the `intern::tests::lib_names_find_themselves` test in core.rs fails: update
the copy and run this script again. Run it again too when the lib files
change (a stale table is only slower).
"""
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
LIBS = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else HERE / "../../ts_bundled/libs").resolve()
OVERRIDES = None if len(sys.argv) > 1 else (HERE / "../libs").resolve()
OUT = pathlib.Path(sys.argv[2] if len(sys.argv) > 2 else HERE / "../src/core/lib_names.rs").resolve()

M64 = (1 << 64) - 1
K = 0xF1357AEA2E62A9C5
SEED1 = 0x243F6A8885A308D3
SEED2 = 0x13198A2E03707344
PREVENT_TRIVIAL_ZERO_COLLAPSE = 0xA4093822299F31D0


def multiply_mix(x, y):
    full = x * y
    return (full & M64) ^ (full >> 64)


def le(b):
    return int.from_bytes(b, "little")


def hash_bytes(b):
    n = len(b)
    s0, s1 = SEED1, SEED2
    if n <= 16:
        if n >= 8:
            s0 ^= le(b[0:8])
            s1 ^= le(b[n - 8:])
        elif n >= 4:
            s0 ^= le(b[0:4])
            s1 ^= le(b[n - 4:])
        elif n > 0:
            s0 ^= b[0]
            s1 ^= (b[n - 1] << 8) | b[n // 2]
    else:
        bulk = b[: n - 1]
        off = 0
        while len(bulk) - off >= 16:
            x = le(bulk[off : off + 8])
            y = le(bulk[off + 8 : off + 16])
            t = multiply_mix(s0 ^ x, PREVENT_TRIVIAL_ZERO_COLLAPSE ^ y)
            s0, s1 = s1, t
            off += 16
        suffix = b[n - 16 :]
        s0 ^= le(suffix[0:8])
        s1 ^= le(suffix[8:16])
    return multiply_mix(s0, s1) ^ n


def fx_write_finish(b):
    """`FxHasher::default()`, `write(b)`, `finish()`."""
    h = ((0 + hash_bytes(b)) * K) & M64
    return ((h << 26) | (h >> 38)) & M64


def hash_str(s):
    """`intern::hash_str`."""
    return fx_write_finish(s.encode())


# rustc-hash 2.1.2 `tests::bytes` (64-bit).
for data, want in [
    (b"", 17606491139363777937),
    (b"\x00", 5448590020104574886),
    (b"\x00" * 6, 16766921560080789783),
    (b"\x01", 5922447956811044110),
    (b"\x02", 5229781508510959783),
    (b"uwu", 7168164714682931527),
    (b"These are some bytes for testing rustc_hash.", 2349210501944688211),
]:
    assert fx_write_finish(data) == want, data

IDENT = r"#?[A-Za-z_$][A-Za-z0-9_$]*"
TOKEN = re.compile(
    r"(?P<doc>/\*\*.*?\*/)"
    r"|/\*.*?\*/"
    r"|//[^\n]*"
    r"|(?P<q>[\"'])(?P<str>(?:(?!(?P=q))[^\\\n]|\\.)*)(?P=q)(?P<prop>\s*\??\s*[:(])?"
    r"|`(?:[^`\\]|\\.)*`"
    r"|[0-9][A-Za-z0-9_$.]*"
    rf"|(?P<id>{IDENT})",
    re.S,
)
WORD = re.compile(IDENT)
TAG = re.compile(r"@([A-Za-z_$][A-Za-z0-9_$]*)")
# Printable ASCII with no quote or backslash, so the text is its own literal.
PLAIN = re.compile(r"[ !#-\[\]-~]+")


def names_of(text):
    names = set()
    for m in TOKEN.finditer(text):
        if m.group("id"):
            names.add(m.group("id"))
        elif m.group("doc"):
            doc = m.group("doc")
            names.update(TAG.findall(doc))
            # The parser reads a TS file's JSDoc only when it has `@see` or
            # `@link` (Go parser `withJSDoc`).
            if "@see" in doc or "@link" in doc:
                names.update(WORD.findall(doc))
        elif m.group("prop") and m.group("str") is not None:
            names.add(m.group("str"))
    return names


names = set()
by_name = {f.name: f for f in LIBS.glob("*.d.ts")}
assert by_name, f"no lib files in {LIBS}"
if OVERRIDES is not None:
    for f in OVERRIDES.glob("*.d.ts"):
        assert f.name in by_name, f"override {f} has no lib to replace"
        by_name[f.name] = f
files = [by_name[n] for n in sorted(by_name)]
for f in files:
    names |= names_of(f.read_text(encoding="utf-8"))
# "" is id 0 and "default" has the fixed id `intern::DEFAULT_ID`.
names.discard("")
names.discard("default")
names = {n for n in names if PLAIN.fullmatch(n)}

count = len(names)
assert 0 < count < 0xFFFF, count
bits = max(1, (count - 1).bit_length())
mask = (1 << bits) - 1
ordered = sorted(names, key=lambda n: (hash_str(n) & mask, n))

offsets = [0]
for n in ordered:
    offsets.append(offsets[-1] + len(n))
buckets = []
i = 0
for b in range((1 << bits) + 1):
    while i < count and (hash_str(ordered[i]) & mask) < b:
        i += 1
    buckets.append(i)
assert buckets[-1] == count


def fill(items, indent="    ", width=99):
    """Items packed on lines up to `width`, like rustfmt's mixed layout."""
    lines, line = [], indent
    for item in items:
        piece = f"{item},"
        if line != indent and len(line) + 1 + len(piece) > width:
            lines.append(line)
            line = indent
        line = line + (" " if line != indent else "") + piece
    if line != indent:
        lines.append(line)
    return "\n".join(lines)


def text_lines(width=100):
    lines, line = [], ""
    limit = width - len('    "",')
    for n in ordered:
        if line and len(line) + len(n) > limit:
            lines.append(f'    "{line}",')
            line = ""
        line += n
    if line:
        lines.append(f'    "{line}",')
    return "\n".join(lines)


out = f"""//! The names of the bundled lib files (`crates/ts_bundled/libs` with the
//! overrides in `crates/ts_goport/libs`), for the interner (`core.rs`,
//! `mod intern`).
//!
//! Code generated by `crates/ts_goport/scripts/gen-lib-names.py`. DO NOT EDIT.
//!
//! Name `i` is `TEXT[OFFSETS[i]..OFFSETS[i + 1]]`. The names of hash bucket
//! `b` (the low `BUCKET_BITS` bits of `intern::hash_str`) are the names
//! `BUCKETS[b]..BUCKETS[b + 1]`.

/// The number of names.
pub(super) const COUNT: usize = {count};

/// Bits of `intern::hash_str` that pick a bucket.
pub(super) const BUCKET_BITS: u32 = {bits};

/// Every name, in bucket order.
pub(super) static TEXT: &str = concat!(
{text_lines()}
);

/// Where each name starts in `TEXT`, and the end of `TEXT`.
pub(super) static OFFSETS: [u32; COUNT + 1] = [
{fill(offsets)}
];

/// The first name of each bucket, and `COUNT`.
pub(super) static BUCKETS: [u16; (1 << BUCKET_BITS) + 1] = [
{fill(buckets)}
];
"""
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(out, encoding="utf-8")
print(f"{OUT}: {count} names, {offsets[-1]} bytes, {1 << bits} buckets from {len(files)} files")
