# JavaScript syntax diagnostic repair

All 24 affected original fixtures now match their full pinned `.errors.txt`
artifacts. All four original control records are unchanged. This includes the
existing type-argument parser mismatch, which remains visible.

## Apply order

Base: `ddbbcdc38336b28a6a6380981459348590cd1675`.

1. Parser prerequisite: `e3230f5adc1bc95704c407fd8fa4efa58f3cf8fe`.
2. The grammar implementation commit containing this report.

The parser prerequisite changes only `parse_function_declaration` and
`parse_class_member`. For JavaScript bodyless declarations, it retains the end
of a semicolon that the parser already consumed. It does not change parsing
decisions, TypeScript ranges, constructor parsing, or other parser helpers.

`Program::load_file` now collects TypeScript-only JavaScript diagnostics through
one AST walk. The helper uses original nodes and ranges, skips reparsed JSDoc
subtrees, and retains the existing option-dependent parameter decorator check.
It does not scan source text for syntax, alter module-option validation, change
`checkJs` selection, or filter checker results.

The reference rules are Go's `parser.checkJSSyntax` and
`Program.GetSyntacticDiagnostics`. The pinned Go revision is
`dc37b5249ab60e2bbce936f71b883e6c8136167e`, with TypeScript submodule
`c3bd12d888b86f676718b16e64d7d2abcb423514`.

## Original artifacts

Every case below is under `_submodules/TypeScript/tests/cases/compiler`.
Each row is a full `.errors.txt` exact match. The listed codes are the restored
diagnostics. Existing diagnostics, including TS5055, remain unchanged.

| Original case | Restored codes |
| --- | --- |
| `decoratorInJsFile.ts` | 8010 |
| `decoratorInJsFile1.ts` | 8010 |
| `jsFileCompilationAbstractModifier.ts` | 8009, 8009 |
| `jsFileCompilationAmbientVarDeclarationSyntax.ts` | 8009 |
| `jsFileCompilationConstructorOverloadSyntax.ts` | 8017 |
| `jsFileCompilationEnumSyntax.ts` | 8006 |
| `jsFileCompilationExportAssignmentSyntax.ts` | 8003 |
| `jsFileCompilationFunctionOverloadSyntax.ts` | 8017 |
| `jsFileCompilationHeritageClauseSyntaxOfClass.ts` | 8005 |
| `jsFileCompilationImportEqualsSyntax.ts` | 8002 |
| `jsFileCompilationInterfaceSyntax.ts` | 8006 |
| `jsFileCompilationMethodOverloadSyntax.ts` | 8017 |
| `jsFileCompilationModuleSyntax.ts` | 8006 |
| `jsFileCompilationOptionalClassElementSyntaxOfClass.ts` | 8009, 8009 |
| `jsFileCompilationOptionalParameter.ts` | 8009 |
| `jsFileCompilationPublicMethodSyntaxOfClass.ts` | 8009 |
| `jsFileCompilationPublicParameterModifier.ts` | 8012 |
| `jsFileCompilationReturnTypeSyntaxOfFunction.ts` | 8010 |
| `jsFileCompilationTypeAliasSyntax.ts` | 8008 |
| `jsFileCompilationTypeOfParameter.ts` | 8010 |
| `jsFileCompilationTypeParameterSyntaxOfClass.ts` | 8004 |
| `jsFileCompilationTypeParameterSyntaxOfClassExpression.ts` | 8004 |
| `jsFileCompilationTypeParameterSyntaxOfFunction.ts` | 8004 |
| `jsFileCompilationTypeSyntaxOfVar.ts` | 8010 |

The complete variant keys, options, baseline paths, and comparison scope are
unchanged. All 55 original source and baseline files retain their input hashes.
No fixture, expected artifact, skip decision, or comparator was edited.

The following full control records also remain unchanged:

- `jsFileCompilationDecoratorSyntax.ts`: exact match.
- `jsFileCompilationEmitBlockedCorrectly.ts`: exact match, retaining TS5055 and TS5056.
- `jsFileCompilationSyntaxError.ts`: exact match, retaining TS5055.
- `jsFileCompilationTypeArgumentSyntaxOfCall.ts`: existing parser mismatch, retaining all seven parser diagnostics.

## Focused verification

The seven new public tests and nine existing JavaScript source tests pass.
The range control verifies unchanged TypeScript overload spans, unchanged
automatic semicolon insertion, and JavaScript semicolon spans with comments and
annotations. Other controls cover JSDoc exclusions, TS1206 options, TS5055,
parser diagnostics, and active JavaScript semantic checking.

The first repair matched 22 affected artifacts. Function and method signatures
still had one-character TS8017 span differences. The separate parser prerequisite
fixes those two artifacts. Their diagnostic codes and messages were already
correct. Initial test and compile failures remain in the evidence directory.

| Final session | Result |
| --- | --- |
| `30751` | Focused public tests pass, exit 0 |
| `30248` | Own-target fixture runner builds, exit 0 |
| `50229` | All 28 original case records collected, exit 0 |

Collection success is separate from compatibility. `validation.json` verifies
all 24 full-artifact exact matches, each preserved preexisting diagnostic, and
the complete unchanged records for all four controls.

## Evidence

Worktree: `target/agent-worktrees/wave161/javascript-syntax-diagnostics`.
Evidence directory: `target/review-javascript-syntax` in that worktree.

The physical Cargo target was initially absent. The baseline was built from
clean `ddbbcdc3`; its executable stayed fixed while its results were collected.
Later builds used only this worktree's own target. No artifact or fingerprint
was copied or seeded. Cargo used the absolute root capped runner, absolute
manifest, original lockfile, locked offline dependencies, common build lock,
16 GiB memory, and 16 MiB stacks. Corpus runs used the diagnostics lock. TMPDIR
was unchanged.

| Evidence | SHA256 |
| --- | --- |
| `before/results.json` | `bb5aa00ec5881c8e9c77d8dc8499159e470d1d092721d909ec6e47675e0ce34e` |
| `after-2/results.json` | `760889979d4cc87d39404fa984a563566da09f234ccd8a6d1801091ab36c6df2` |
| `validation.json` | `4f684214632cfec622480b1b3dd4a6a272f9f5ba8b2db18f4d240f13170b100d` |
| `tests-3.log` | `e9d65eb680e63451748f68ac4254f7b4d9a34d598297e5adbe91279ea526de74` |
| Repaired fixture binary | `55faaab5ca5673f4e16ff7123654ab7fe39f85a4f58ceaaa21a88a31cba1760e` |

Formatting, whitespace, and frozen source-input checks pass. Both pinned upstream
checkouts are clean. All owned commands are collected. Temporary Go-control
inputs were removed after preserving their source and results in JSON. No
temporary Rust probe, broad parser rewrite, full-workspace pass, root merge,
or general JavaScript compatibility claim is included.
