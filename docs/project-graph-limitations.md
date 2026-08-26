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

The config resolver does not return its input bytes or its full extends graph.
The retained leaf config text comes from the later diagnostic read. A file can
change between those reads, so that text alone does not prove the config
parser's input.

Module resolution records retain terminal realpaths and package JSON paths.
They do not retain the original path passed to `realpath`, package identities,
or all package-scope inputs. Root and path-reference loads do not request a
realpath. These gaps remain explicit in the snapshot.
