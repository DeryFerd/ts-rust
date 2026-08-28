# Reserved class type names

Status: all seven focused tests pass, including the unchanged complete
ClassDeclaration24 error baseline. A clean after-scorecard replay is pending.

Base: `79d44b121fe7943a5311540e08fa5c0c6ea1f0ba`.
Original case: `_submodules/TypeScript/tests/cases/compiler/ClassDeclaration24.ts`.
Variant: `v1:f28b81000d60be77c8b86898e449cc2d`.
Options: `target=es2015`.

## Before

The accepted root79 census, run-3 attempt-00004, records a supported diagnostic
mismatch. Go expects:

```text
ClassDeclaration24.ts(1,7): error TS2414: Class name cannot be 'any'.
```

Root79 produced no diagnostic. The scorecard records clean root79 and clean
Go `dc37b5249ab60e2bbce936f71b883e6c8136167e`. No new baseline build was run.

Original source SHA256: `7b64b1307e3ce450d370112142ee969815539cc53f546be33318ad5ba526d602`.
Original error baseline SHA256: `0600ec1d55acb9f3007ca82c3daee1b1e2b21be3124cec3ba3c769d5ebab03f9`.

## Rule

Pinned Go `checkClassLikeDeclaration` calls `checkCollisionsForDeclarationName`,
which applies `checkTypeNameIsReserved` to class declarations and expressions.
The reserved decoded names are any, unknown, never, number, bigint, boolean,
string, symbol, void, object, and undefined.

The fix adds `source::issue_class_name_diagnostics` and one call in the existing
source diagnostic stage. It uses the existing TS2414 catalog message and the
actual identifier node. It neither changes class preparation nor replaces
other source diagnostics. Constructor grammar functions and classes.rs remain
unchanged. No cache, ownership record, fixture-name rule, or broader class
feature is added.

The focused tests cover the original full error artifact, class forms,
decoded escaped names, raw identifier spans, ordinary/anonymous names, and
other source diagnostics. Upstream files and baselines are read-only.

The first focused run passed the original fixture, reserved keyword/span
matrix, and neighboring diagnostics. Two whole-program test assumptions hit
existing class-form capability limits before the new diagnostic stage:
anonymous class initializers and named default-export classes. Their failed
log is preserved. No class feature was added to bypass those limits. Parsed
grammar tests cover default, generic, named-expression, and anonymous forms
directly, while whole-program tests cover admitted declaration forms.

Initial test log: `/tmp/ts-rust-wave159-class-reserved-type-name-tests.log`.
SHA256: `7a7a21fae4645f9222aac2150f27f1711618774ab9504e69bb67974669937ad9`.

The corrected focused run passed two parsed-grammar tests and five
fixture/program tests, with no failures or ignored tests. It filtered 4,269
unrelated unit tests. No broader class support was added.
Passing log: `/tmp/ts-rust-wave159-class-reserved-type-name-tests-2.log`.
SHA256: `3c4140a108729f64292a19dc09f260caaf1f4e809b922454294ef29dbc1447c6`.
