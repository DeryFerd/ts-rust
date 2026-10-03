#!/usr/bin/env node
// Orders the functions of the wasm module so that gzip and brotli compress
// it better. scripts/wasm/build.sh runs it around wasm-opt:
//   hide, wasm-opt -g, key, wasm-opt --reorder-functions-by-name --strip-debug
//
// usage: node scripts/wasm/order-functions.mjs hide <linked.wasm> <out.wasm>
//        node scripts/wasm/order-functions.mjs key <opt.wasm> <linked.wasm> <out.wasm>
//
// hide  Names each defined function with its index in the code section
//       ("0", "1", ...) and drops all other custom sections. wasm-opt's
//       choices depend on function names, and these are the names that it
//       gives a module with no names. So wasm-opt makes the same code as for
//       the stripped module, and -g keeps the index names through the passes.
// key   Names each function of opt.wasm (the wasm-opt -g output of hide)
//       with its position in the new order. The real names come from the
//       name section of linked.wasm (the input of hide).
// Both fail when the input has no function names.
//
// Why the order matters: lld spreads the near-identical copies of a generic
// function (drop glue, RawVec methods, Vec::extend, ...) across the module.
// gzip only sees 32 KB back, and brotli pays more bits for a far match. The
// new order:
// 1. The 128 - <imports> functions that are used most (call, ref.func, table
//    entries, exports) get the indexes below 128, so each use is a 1-byte
//    LEB128 instead of 2 bytes.
// 2. Then all others, grouped by the first path in the demangled name, cut
//    to 3 segments (`core::ptr::drop_glue`, `alloc::vec::Vec`,
//    `ts_goport::checker::checker_p01`), and in each group sorted by body
//    bytes, so that similar bodies are neighbors.
// At 107d120d this saves 40 KB raw, 96 KB gzip and 22 KB brotli. Grouping by
// the full name or by the name without generic arguments saved 81 and 82 KB
// gzip, and sorting by body bytes only saved 47 KB gzip.
import fs from 'node:fs';

const [mode, ...files] = process.argv.slice(2);
if (mode === 'hide' && files.length === 2) {
  hide(...files);
} else if (mode === 'key' && files.length === 3) {
  key(...files);
} else {
  console.error(fs.readFileSync(new URL(import.meta.url), 'utf8').split('\nimport ')[0]);
  process.exit(2);
}

function hide(linkedPath, outPath) {
  const m = parseModule(fs.readFileSync(linkedPath));
  functionNames(m, linkedPath);
  const names = new Map(m.bodies.map((_, i) => [m.imports + i, String(i)]));
  fs.writeFileSync(outPath, writeModule(m, names));
}

function key(optPath, linkedPath, outPath) {
  const m = parseModule(fs.readFileSync(optPath));
  const linked = parseModule(fs.readFileSync(linkedPath));
  const optNames = functionNames(m, optPath);
  const realNames = functionNames(linked, linkedPath);
  const uses = countUses(m);

  const funcs = m.bodies.map((body, i) => {
    const index = m.imports + i;
    // A function that wasm-opt adds has no name or a name of its own.
    const name = optNames.get(index) ?? '';
    const real = /^\d+$/.test(name) ? realNames.get(linked.imports + Number(name)) : name;
    return { index, body, uses: uses[index], group: groupOf(real ?? '') };
  });
  const hot = [...funcs]
    .sort((a, b) => b.uses - a.uses || a.index - b.index)
    .slice(0, Math.max(0, 128 - m.imports));
  const hotSet = new Set(hot);
  const rest = funcs
    .filter((f) => !hotSet.has(f))
    .sort((a, b) => cmp(a.group, b.group) || Buffer.compare(a.body, b.body) || a.index - b.index);

  // Zero-padded positions sort as strings in the same order. Imports keep
  // theirs: wasm-opt writes them first anyway.
  const width = String(m.imports + funcs.length).length;
  const pad = (pos) => String(pos).padStart(width, '0');
  const names = new Map();
  for (let i = 0; i < m.imports; i++) names.set(i, pad(i));
  [...hot, ...rest].forEach((f, pos) => names.set(f.index, pad(m.imports + pos)));
  fs.writeFileSync(outPath, writeModule(m, names));
}

function cmp(a, b) {
  return a < b ? -1 : a > b ? 1 : 0;
}

// The sort group of a function from its symbol name: the first path in the
// demangled name (the self type of a method), cut to 3 segments.
function groupOf(symbol) {
  const name = demangle(symbol);
  const m = /^<*&?(?:mut )?(?:dyn )?([A-Za-z_]\w*(?:::[A-Za-z_]\w*)*)/.exec(name);
  return (m ? m[1] : name).split('::').slice(0, 3).join('::');
}

// --- wasm reading and writing ---

// The sections, the function import count and the code bodies of a module.
function parseModule(b) {
  if (b.readUInt32LE(0) !== 0x6d736100) throw new Error('not a wasm module');
  const r = reader(b, 8);
  const sections = [];
  let imports = 0;
  let bodies = [];
  while (r.p < b.length) {
    const start = r.p;
    const id = b[r.p++];
    const end = r.u() + r.p;
    const s = { id, start, body: r.p, end, name: id === 0 ? r.name() : '' };
    if (id === 2) {
      for (let n = r.u(); n > 0; n--) {
        r.name();
        r.name();
        const kind = b[r.p++];
        if (kind === 0) {
          r.u();
          imports++;
        } else if (kind === 1) {
          r.p++; // reftype
          if (r.u() & 1) r.u();
          r.u();
        } else if (kind === 2) {
          if (r.u() & 1) r.u();
          r.u();
        } else if (kind === 3) {
          r.p += 2;
        } else {
          throw new Error(`unknown import kind ${kind}`);
        }
      }
    } else if (id === 10) {
      bodies = [];
      for (let n = r.u(); n > 0; n--) {
        const len = r.u();
        bodies.push(b.subarray(r.p, r.p + len));
        r.p += len;
      }
    }
    sections.push(s);
    r.p = end;
  }
  return { b, sections, imports, bodies };
}

// The function names (subsection 1) of the "name" custom section.
function functionNames(m, path) {
  const names = new Map();
  const sec = m.sections.find((s) => s.id === 0 && s.name === 'name');
  if (sec) {
    const r = reader(m.b, sec.body);
    r.name();
    while (r.p < sec.end) {
      const sub = m.b[r.p++];
      const end = r.u() + r.p;
      if (sub === 1) for (let n = r.u(); n > 0; n--) names.set(r.u(), r.name());
      r.p = end;
    }
  }
  if (names.size === 0) {
    throw new Error(`${path} has no function names: link with -C strip=debuginfo, and pass -g to wasm-opt`);
  }
  return names;
}

// The module with its custom sections replaced by a name section that holds
// `names` (function index -> name).
function writeModule(m, names) {
  const parts = [m.b.subarray(0, 8)];
  for (const s of m.sections) if (s.id !== 0) parts.push(m.b.subarray(s.start, s.end));
  const entries = [...names].sort((a, b) => a[0] - b[0]);
  const sub = Buffer.concat([leb(entries.length), ...entries.flatMap(([i, name]) => [leb(i), str(name)])]);
  const body = Buffer.concat([str('name'), Buffer.from([1]), leb(sub.length), sub]);
  parts.push(Buffer.from([0]), leb(body.length), body);
  return Buffer.concat(parts);
}

// The uses of each function index: calls, ref.func, table entries, exports
// and the start function. Each use is a LEB128 of the index.
function countUses(m) {
  const uses = new Array(m.imports + m.bodies.length).fill(0);
  const use = (i) => uses[i]++;
  const b = m.b;
  for (const s of m.sections) {
    const r = reader(b, s.body);
    if (s.id === 6) {
      for (let n = r.u(); n > 0; n--) {
        r.p += 2; // valtype, mutability
        scanCode(r, use);
      }
    } else if (s.id === 7) {
      for (let n = r.u(); n > 0; n--) {
        r.name();
        const kind = b[r.p++];
        const index = r.u();
        if (kind === 0) use(index);
      }
    } else if (s.id === 8) {
      use(r.u());
    } else if (s.id === 9) {
      for (let n = r.u(); n > 0; n--) {
        const flags = r.u();
        if ((flags & 3) === 2) r.u(); // table index
        if (!(flags & 1)) scanCode(r, use); // offset
        if (flags & 3) r.p++; // elemkind or reftype
        for (let k = r.u(); k > 0; k--) {
          if (flags & 4) scanCode(r, use);
          else use(r.u());
        }
      }
    }
  }
  for (const body of m.bodies) {
    const r = reader(body, 0);
    for (let n = r.u(); n > 0; n--) {
      r.u();
      r.p++; // valtype
    }
    scanCode(r, use);
    if (r.p !== body.length) throw new Error('a function body does not end at its last end');
  }
  return uses;
}

// Reads instructions up to the `end` of the current block and calls
// use(index) for each function index (call, ref.func). Knows the opcodes of
// the features that build.sh enables, and fails on any other opcode.
function scanCode(r, use) {
  const b = r.b;
  let depth = 0;
  for (;;) {
    const op = b[r.p++];
    if (op === 0x0b) {
      if (depth-- === 0) return;
    } else if (op >= 0x02 && op <= 0x04) {
      r.u(); // block type
      depth++;
    } else if (op === 0x10 || op === 0xd2) {
      use(r.u());
    } else if (op === 0x0c || op === 0x0d || (op >= 0x20 && op <= 0x26) || (op >= 0x3f && op <= 0x42) || op === 0xd0) {
      r.u();
    } else if (op === 0x11) {
      r.u();
      r.u();
    } else if (op === 0x0e) {
      for (let n = r.u() + 1; n > 0; n--) r.u();
    } else if (op === 0x1c) {
      r.p += r.u();
    } else if (op >= 0x28 && op <= 0x3e) {
      if (r.u() & 0x40) r.u(); // align, then a memory index
      r.u(); // offset
    } else if (op === 0x43) {
      r.p += 4;
    } else if (op === 0x44) {
      r.p += 8;
    } else if (op === 0xfc) {
      const sub = r.u();
      if (sub > 17) throw new Error(`unknown opcode 0xfc ${sub}`);
      if (sub >= 8) r.u();
      if (sub === 8 || sub === 10 || sub === 12 || sub === 14) r.u();
    } else if (!(op <= 0x01 || op === 0x05 || op === 0x0f || op === 0x1a || op === 0x1b || (op >= 0x45 && op <= 0xc4) || op === 0xd1)) {
      throw new Error(`unknown opcode 0x${op.toString(16)}`);
    }
  }
}

function reader(b, p) {
  return {
    b,
    p,
    u() {
      let x = 0;
      let shift = 0;
      let byte;
      do {
        byte = b[this.p++];
        x += (byte & 0x7f) * 2 ** shift;
        shift += 7;
      } while (byte & 0x80);
      return x;
    },
    name() {
      const len = this.u();
      this.p += len;
      return b.toString('utf8', this.p - len, this.p);
    },
  };
}

function leb(x) {
  const out = [];
  do {
    const byte = x & 0x7f;
    x = Math.floor(x / 128);
    out.push(x ? byte | 0x80 : byte);
  } while (x);
  return Buffer.from(out);
}

function str(s) {
  return Buffer.concat([leb(Buffer.byteLength(s)), Buffer.from(s)]);
}

// --- symbol names ---

// Demangles a Rust symbol without its generic arguments, for example
// `<alloc::vec::Vec as core::ops::drop::Drop>::drop`. A C symbol, or a name
// that does not parse, stays as it is.
function demangle(symbol) {
  const s = symbol.replace(/\.\d+$/, ''); // LLVM's suffix for a local copy
  try {
    if (s.startsWith('_R')) return demangleV0(s.slice(2));
    if (s.startsWith('_ZN')) return demangleLegacy(s);
  } catch {
    // The raw name is the group.
  }
  return s;
}

// Legacy mangling: _ZN, then <length><identifier> for each segment, then
// 17h<hash>E.
function demangleLegacy(s) {
  const parts = [];
  let p = 3;
  while (s[p] !== 'E') {
    const len = /^\d+/.exec(s.slice(p))[0];
    p += len.length + Number(len);
    parts.push(s.slice(p - Number(len), p));
  }
  if (/^h[0-9a-f]{16}$/.test(parts.at(-1))) parts.pop();
  return parts.join('::');
}

// v0 mangling after the _R prefix:
// https://doc.rust-lang.org/rustc/symbol-mangling/v0.html
function demangleV0(s) {
  let p = 0;
  const next = () => {
    if (p >= s.length) throw new Error('v0: unexpected end');
    return s[p++];
  };
  const eat = (c) => s[p] === c && ++p;
  const base62 = () => {
    if (eat('_')) return 0;
    let x = 0;
    for (let c = next(); c !== '_'; c = next()) {
      const d = '0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'.indexOf(c);
      if (d < 0) throw new Error('v0: bad base-62 digit');
      x = x * 62 + d;
    }
    return x + 1;
  };
  const skipTagged = (tag) => eat(tag) && base62(); // disambiguator, binder
  const ident = () => {
    eat('u'); // punycode, kept as is
    const len = /^(0|[1-9]\d*)/.exec(s.slice(p))?.[0];
    if (!len) throw new Error('v0: bad identifier');
    p += len.length;
    eat('_');
    p += Number(len);
    return s.slice(p - Number(len), p);
  };
  const backref = (parse) => {
    const target = base62();
    const saved = p;
    p = target;
    const out = parse();
    p = saved;
    return out;
  };
  const list = (parse, sep) => {
    const out = [];
    while (!eat('E')) out.push(parse());
    return out.join(sep);
  };

  const path = () => {
    const tag = next();
    if (tag === 'C') {
      skipTagged('s');
      return ident();
    }
    if (tag === 'N') {
      const ns = next();
      const parent = path();
      skipTagged('s');
      const name = ident();
      if (ns === 'C') return `${parent}::{closure}`;
      if (ns >= 'A' && ns <= 'Z') return `${parent}::{shim${name ? `:${name}` : ''}}`;
      return `${parent}::${name}`;
    }
    if (tag === 'M' || tag === 'X') {
      skipTagged('s');
      path(); // the module of the impl
      const self = type();
      return tag === 'M' ? `<${self}>` : `<${self} as ${path()}>`;
    }
    if (tag === 'Y') return `<${type()} as ${path()}>`;
    if (tag === 'I') {
      const base = path();
      list(genericArg, ''); // dropped
      return base;
    }
    if (tag === 'B') return backref(path);
    throw new Error(`v0: bad path tag ${tag}`);
  };
  const genericArg = () => {
    if (eat('L')) return base62();
    if (eat('K')) return constant();
    return type();
  };
  const basic = {
    a: 'i8', b: 'bool', c: 'char', d: 'f64', e: 'str', f: 'f32', h: 'u8', i: 'isize', j: 'usize',
    l: 'i32', m: 'u32', n: 'i128', o: 'u128', s: 'i16', t: 'u16', u: '()', v: '...', x: 'i64',
    y: 'u64', z: '!', p: '_',
  };
  const type = () => {
    const tag = next();
    if (basic[tag]) return basic[tag];
    if (tag === 'R' || tag === 'Q') {
      skipTagged('L');
      return (tag === 'R' ? '&' : '&mut ') + type();
    }
    if (tag === 'P') return `*const ${type()}`;
    if (tag === 'O') return `*mut ${type()}`;
    if (tag === 'A') return `[${type()}; ${constant()}]`;
    if (tag === 'S') return `[${type()}]`;
    if (tag === 'T') return `(${list(type, ', ')})`;
    if (tag === 'F') {
      skipTagged('G');
      eat('U');
      if (eat('K') && !eat('C')) ident(); // ABI
      const params = list(type, ', ');
      return `fn(${params}) -> ${type()}`;
    }
    if (tag === 'D') {
      skipTagged('G');
      const traits = list(dynTrait, ' + ');
      if (!eat('L')) throw new Error('v0: dyn without a lifetime');
      base62();
      return `dyn ${traits}`;
    }
    if (tag === 'B') return backref(type);
    p--;
    return path();
  };
  const dynTrait = () => {
    const trait = path();
    // Associated type bindings, dropped.
    while (eat('p')) {
      ident();
      type();
    }
    return trait;
  };
  // A const generic argument; only its syntax is read.
  const constant = () => {
    const tag = next();
    if (tag === 'B') return backref(constant);
    if (tag === 'p') return '_';
    if ('hmtyojasxnilbce'.includes(tag)) {
      eat('n');
      while (next() !== '_');
    } else if (tag === 'R' || tag === 'Q') {
      constant();
    } else if (tag === 'A' || tag === 'T') {
      list(constant, '');
    } else if (tag === 'V') {
      path();
      if (eat('T')) list(constant, '');
      else if (eat('S')) list(() => (skipTagged('s'), ident(), constant()), '');
      else if (!eat('U')) throw new Error('v0: bad const variant');
    } else {
      throw new Error(`v0: bad const tag ${tag}`);
    }
    return '_';
  };

  return path();
}
