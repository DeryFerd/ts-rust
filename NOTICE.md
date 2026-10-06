# Notices

ts-rust is licensed under the [MIT License](LICENSE).

ts-rust is a port of other projects. Those parts keep their original licenses and notices.

## TypeScript

Copyright (c) Microsoft Corporation. Licensed under the Apache License, Version 2.0.

- The compiler source in `crates/` is a Rust port of the native TypeScript compiler (Go), from
  [microsoft/TypeScript](https://github.com/microsoft/TypeScript) and
  [microsoft/typescript-go](https://github.com/microsoft/typescript-go). We changed it: it is
  rewritten in Rust. [UPSTREAM.md](UPSTREAM.md) records the upstream revision.
- The lib files (`crates/ts_goport/libs`), the localized diagnostic messages
  (`crates/ts_goport/data/loc`) and the JS launcher and JS API in the npm packages are copied from
  TypeScript without change.

License: [licenses/TypeScript-LICENSE.txt](licenses/TypeScript-LICENSE.txt). Third-party notices
of TypeScript: [licenses/TypeScript-NOTICE.txt](licenses/TypeScript-NOTICE.txt).

## Go

Copyright (c) 2009 The Go Authors. Licensed under the BSD 3-Clause License.

`crates/ts_goport/src/gostd` ports parts of the Go standard library and `golang.org/x/text` that
the compiler uses.

License: [licenses/Go-LICENSE.txt](licenses/Go-LICENSE.txt).
