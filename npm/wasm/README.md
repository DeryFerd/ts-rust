# ts-rust-wasm

The ts-rust TypeScript compiler (`crates/ts_goport`, a Rust port of typescript-go) as one
WebAssembly module. It type-checks and emits like the native `tsgo`, in Node, Deno, Bun and
browsers. Nothing here publishes.

## Build

```sh
rustup target add wasm32-wasip1
brew install binaryen          # or a binaryen 132+ release: wasm-opt
scripts/wasm/build.sh          # writes npm/wasm/ts_rust.wasm
cd npm/wasm && npm test
```

`WASM_PROFILE=release scripts/wasm/build.sh` builds faster and larger.

## Use

Node, on the real file system:

```sh
npx tsc-wasm -p tsconfig.json
```

```js
import { tsc } from "ts-rust-wasm";

const { exitCode, stdout } = await tsc(["-p", "tsconfig.json"]);
```

In memory (Node, browsers and Deno). `files` maps absolute paths to text. The result has every
file after the run, emitted ones included:

```js
import { tsc } from "ts-rust-wasm";

const { exitCode, diagnostics, files } = await tsc(["-p", "/app"], {
    files: {
        "/app/tsconfig.json": '{ "compilerOptions": { "strict": true, "outDir": "out" } }',
        "/app/index.ts": "export const n: number = 'one';",
    },
    diagnostics: "json",
});
// diagnostics: [{ fileName: "/app/index.ts", code: 2322, category: 1, text: "...", ... }]
// files.get("/app/out/index.js")
```

`diagnostics: "json"` returns the diagnostics as objects (the TypeScript API's
`DiagnosticResponse`, with UTF-16 positions) and does not print them. Without it, `stdout` has
tsc's usual text.

In a browser, call `tsc` from a module Web Worker, as `examples/browser` does, so that a run does not
block the page. It also works on the page's main thread. A Safari worker has a small stack and no
JSPI: a run there fails at about 230 terms of `1 + 1 + ...`, or at a chain of 200 method calls.
Chrome and Firefox workers reach about 1,000 to 1,500 terms, and Safari's main thread about 7,000.
Serve `ts_rust.wasm` as `application/wasm`, so that it compiles while it downloads.
To try the example, run `python3 -m http.server -d npm/wasm` and open
`http://localhost:8000/examples/browser/`.

`runTsc` (on the calling thread) and `runTscAsync` (a promise) from `ts-rust-wasm/core` take any
`HostFileSystem` and a compiled module, for hosts that keep files elsewhere.

## How it works

- `crates/ts_wasm` is the module: `tsc` from `ts_goport` for `wasm32-wasip1`. The `wasm` cargo
  profile (opt-level z, fat LTO) and wasm-opt make it 5.1 MB (2.2 MB gzip, 1.8 MB brotli). The
  libs are in it, packed with LZMA. `scripts/wasm/build.sh` tells how to build a module that
  checks 17 to 20% faster at 6.2 MB. The diagnostic message texts are packed too.
- The host (`core.js`) gives the file system through two imports (`ts_host.fs`, `fs_take`), and a
  small WASI shim gives clocks, random bytes, stdout and stderr. There is no WASI file system and
  no `node:wasi`.
- wasm has one thread. The checkers run their jobs on the calling thread
  (`program.rs` `send_thread_job`), as Go's `--singleThreaded` runs its work groups inline. Each
  checker keeps its own node and symbol ids, as a native checker thread does.
- Each run uses a new instance of the compiled module, because the compiler keeps one program per
  process. The module is compiled once. Memory goes back when a run ends.
- The checker recurses deeply, so very deep nesting can run out of stack. Node runs each call in a
  worker thread with a 256 MB stack (about 30,000 terms of `1 + 1 + ...`). Bun ignores that
  setting, so under Bun a call runs on the calling thread. In a browser worker, `tsc` runs through
  JSPI where the engine has it, which gives about 2 times the stack in Chrome.
- `scripts/wasm/diff.mjs` compares the module with the native tsgo on Query core, Hono, the
  multiprog fixtures and more, and `scripts/wasm/corpus.mjs` on the TypeScript compiler test cases.
  Exit codes, output and emitted files are byte-identical.
- Not supported: `--watch`, `--pprofDir`, `--lsp`, `--api`, diagnostics as JSON with `--build`, and
  plugins or content mappers that start processes. `--locale` gives English: the module has no
  message catalogs, to keep it small. With `--generateTrace`, a panic in the trace's type display
  ends the run (native recovers from it).
- `tsc -b` keeps the synthetic nodes of each built project until the run ends (native frees them
  when a project is done), so a very large build uses more memory.
