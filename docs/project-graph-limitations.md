# Project graph limits

`Program::project_graph_snapshot` returns the loader's retained facts. It does
not certify that the graph or the canonical module manifest matches upstream.
Its `missing_evidence` field names inputs the loader does not retain.

## Mode-specific module targets

`Program::resolved_modules` keys targets by canonical containing path, module
specifier, and request mode. The canonical manifest uses the exact request mode
for each specifier node. An `.mts` source can retain different targets for these
imports:

```ts
import { value } from "pkg";
import other = require("pkg");
```

`canonical_module_resolution_modes.rs` checks this through public canonical
queries, value types, declaration owners, and replay in both source orders.
Declaration-only tests with `skipLibCheck` also check explicit `resolution-mode`
attributes, an unresolved target in only one mode, and shared ambient targets.
A JSX test checks that a successful require lookup cannot hide a missing
import-mode runtime.

Unresolved source `import = require` checking remains explicitly unsupported.
The test suite preserves that failure class. The legacy checker still projects
module targets to a map keyed only by specifier text. These bounded canonical
checks do not certify mixed-mode legacy checking, emit, or full resolution
parity. The graph snapshot remains a report of retained inputs and results.

## Missing input evidence

The config resolver retains an ordered prefix of its existing probes, reads,
extends decisions, and cycles. This adds no filesystem calls. The observation
limit is 16,384 events and 16 MiB of UTF-8 string data. Omitted events are counted.
`is_complete` describes retention only. It does not mean that the config was
valid, that resolution succeeded, or that the complete Program was observed.

Read events contain the VFS text passed to parsing, not raw disk bytes. The VFS
can remove a BOM or decode UTF-16. Report fields use `parserInputText`,
`parserInputTextUtf8ByteCount`, and `parserInputTextDigest`. Repeated reads stay
separate. The compiler still performs its later diagnostic read in the same
place. `ProgramGraphConfig::source_text` and the report's
`diagnosticSourceTextDigest` describe that later text, which can differ.

Resolved module records retain the lookup candidate before optional realpath
handling. Every resolution attempt retains the effective import or require
mode, including default-mode and failed attempts. Config parse and extends
gaps remain when observations are incomplete. A missing leaf text remains a
separate gap.

Package identities and package-scope inputs are still incomplete. Root and
path-reference loads do not record filesystem realpaths. These gaps remain
explicit in the snapshot.
