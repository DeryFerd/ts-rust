//! Port-only tests of the Effect Schema refactors and schemagen
//! (`effect::ls::refactors`, `effect::ls::schemagen`, Effect-TS/tsgo patch
//! 011; lane effectE9c) on a small stand-in for the v3 `effect/Schema`
//! module: a `Schema` interface with `ast` and the v3 variance struct, `Number`
//! and `Struct`. That is enough for the type parser to find the Schema types.
//!
//! The Go baseline cases with the real package (v3 and v4) run through
//! `scripts/effect/ls-cases.mjs`.

use std::rc::Rc;

use ts_goport::ls::LanguageService;
use ts_goport::lsp::lsproto;
use ts_goport::project::Session;

use super::projecttestutil::{self, files};
use super::util::*;

const CONFIG: &str = "/home/projects/p/tsconfig.json";
const MAIN: &str = "/home/projects/p/main.ts";
const MAIN_URI: &str = "file:///home/projects/p/main.ts";

// `User` is at 2:17-2:21, `UserSchema` at 8:13-8:23.
const MAIN_TEXT: &str = r#"import * as Schema from "effect/Schema"

export interface User {
  id: number
  name?: string
  tags: ReadonlyArray<"a" | "b">
}

export const UserSchema = Schema.Struct({ id: Schema.Number })
"#;

const EFFECT_PACKAGE_JSON: &str = r#"{"name":"effect","version":"3.0.0","types":"./index.d.ts"}"#;
const EFFECT_INDEX: &str = "export * as Schema from \"./Schema.js\"\n";
const EFFECT_SCHEMA: &str = r#"export declare const TypeId: unique symbol
export interface Schema<in out A, in out I = A, out R = never> {
  readonly Type: A
  readonly Encoded: I
  readonly ast: unknown
  readonly [TypeId]: {
    readonly _A: (_: A) => A
    readonly _I: (_: I) => I
    readonly _R: (_: never) => R
  }
}
export declare const Number: Schema<number>
export declare function Struct<A, I>(fields: { readonly id: Schema<A, I> }): Schema<{ readonly id: A }, { readonly id: I }>
"#;

const PLUGIN: &str = r#"{"name":"@effect/language-service"}"#;

// Self-recursive types: `Tree` is at 2:17-2:21, `Json` at 7:12-7:16. The
// ls-case `refactors/effect-v3-port/structuralTypeToSchema_selfRecursive`
// (scripts/effect/ls-cases.mjs) has the same declarations with the real
// package.
const TREE: &str = "/home/projects/p/tree.ts";
const TREE_URI: &str = "file:///home/projects/p/tree.ts";
const TREE_TEXT: &str = r#"import * as Schema from "effect/Schema"

export interface Tree {
  value: number
  children: Array<Tree>
}

export type Json = string | number | boolean | null | ReadonlyArray<Json> | { readonly [key: string]: Json }
"#;

/// A session on the project with the Effect plugin and main.ts open, and its
/// language service for main.ts.
fn service() -> (Rc<Session>, LanguageService) {
    service_for(MAIN_URI, MAIN_TEXT)
}

/// A session on the project with the Effect plugin and the file `file_uri`
/// (main.ts or tree.ts) open with `text`, and its language service for it.
fn service_for(file_uri: &str, text: &str) -> (Rc<Session>, LanguageService) {
    let config = format!(
        r#"{{"compilerOptions":{{"strict":true,"target":"ESNext","module":"ESNext","moduleResolution":"bundler","plugins":[{PLUGIN}]}}}}"#
    );
    let (session, _) = projecttestutil::setup(files(&[
        (CONFIG, &config),
        (MAIN, MAIN_TEXT),
        (TREE, TREE_TEXT),
        (
            "/home/projects/p/node_modules/effect/package.json",
            EFFECT_PACKAGE_JSON,
        ),
        (
            "/home/projects/p/node_modules/effect/index.d.ts",
            EFFECT_INDEX,
        ),
        (
            "/home/projects/p/node_modules/effect/Schema.d.ts",
            EFFECT_SCHEMA,
        ),
    ]));
    open(&session, file_uri, text);
    let service = session
        .get_language_service(&projecttestutil::with_request_id(&bg()), &uri(file_uri))
        .unwrap_or_else(|err| panic!("{}", err.error()));
    (session, service)
}

fn range(line: u32, start: u32, end: u32) -> lsproto::Range {
    lsproto::Range {
        start: lsproto::Position {
            line,
            character: start,
        },
        end: lsproto::Position {
            line,
            character: end,
        },
    }
}

/// The byte offset of `pos` in `text` (ASCII text: a UTF-16 character is a
/// byte).
fn offset(text: &str, pos: lsproto::Position) -> usize {
    let line_start: usize = text
        .split_inclusive('\n')
        .take(pos.line as usize)
        .map(str::len)
        .sum();
    line_start + pos.character as usize
}

/// `source` with `edits` applied, as an LSP client applies them (edits at
/// the same position keep their order).
fn apply(source: &str, edits: &[(lsproto::Range, String)]) -> String {
    let mut sorted: Vec<_> = edits.iter().enumerate().collect();
    sorted.sort_by_key(|(i, (range, _))| {
        (
            std::cmp::Reverse(offset(source, range.start)),
            std::cmp::Reverse(*i),
        )
    });
    let mut text = source.to_string();
    for (_, (range, new_text)) in sorted {
        text.replace_range(
            offset(source, range.start)..offset(source, range.end),
            new_text,
        );
    }
    text
}

/// The refactors at `range` in main.ts (`only: ["refactor"]`) as `(title,
/// kind, main.ts after the edits)`.
fn refactors(service: &LanguageService, range: lsproto::Range) -> Vec<(String, String, String)> {
    refactors_in(service, MAIN_URI, MAIN_TEXT, range)
}

/// The refactors at `range` in the file `file_uri` with the text `source`, as
/// `refactors` gives them.
fn refactors_in(
    service: &LanguageService,
    file_uri: &str,
    source: &str,
    range: lsproto::Range,
) -> Vec<(String, String, String)> {
    let response = service
        .provide_code_actions(
            &projecttestutil::with_request_id(&bg()),
            &lsproto::CodeActionParams {
                text_document: lsproto::TextDocumentIdentifier { uri: uri(file_uri) },
                range,
                context: Some(lsproto::CodeActionContext {
                    only: Some(vec![lsproto::CodeActionKind("refactor".into())]),
                    ..Default::default()
                }),
                ..Default::default()
            },
        )
        .unwrap_or_else(|err| panic!("{}", err.error()));
    response
        .command_or_code_action_array
        .unwrap_or_default()
        .into_iter()
        .map(|action| {
            let action = action.code_action.expect("a code action");
            let mut changes = action
                .edit
                .and_then(|edit| edit.changes)
                .unwrap_or_default();
            assert!(changes.len() <= 1, "edits of one file: {changes:?}");
            let edits: Vec<(lsproto::Range, String)> = changes
                .shift_remove(&uri(file_uri))
                .unwrap_or_default()
                .into_iter()
                .map(|edit| {
                    let edit = edit.expect("an edit");
                    (edit.range, edit.new_text)
                })
                .collect();
            let kind = action
                .kind
                .map(|kind| kind.0.into_owned())
                .unwrap_or_default();
            (action.title, kind, apply(source, &edits))
        })
        .collect()
}

/// MAIN_TEXT with `old` replaced by `new` (once).
fn main_with(old: &str, new: &str) -> String {
    assert!(MAIN_TEXT.contains(old), "{old}");
    MAIN_TEXT.replacen(old, new, 1)
}

const INTERFACE: &str = "export interface User {";

child_test! {
    // On an interface name: the 3 schemagen refactors come last, in Go's
    // `refactors.All` order. The AST refactors keep the declared types
    // (`name?: string` is `optional(String)`); the structural one reads the
    // checker types (`string | undefined`) and makes a `Schema.Class`, which
    // is exported because the interface is. v3 forms: `Literal("a", "b")`,
    // `Union(a, b)`.
    fn schemagen_refactors_on_an_interface() {
        let (_session, service) = service();
        let fields = |name: &str| {
            format!(
                "    id: Schema.Number,\n    name: {name},\n    tags: Schema.Array(Schema.Literal(\"a\", \"b\"))\n"
            )
        };
        let struct_text = format!(
            "export const User = Schema.Struct({{\n{}}});\n\n{INTERFACE}",
            fields("Schema.optional(Schema.String)")
        );
        let class_text = format!(
            "export class User extends Schema.Class<User>(\"User\")({{\n{}}}) {{}}\n\n{INTERFACE}",
            fields("Schema.optional(Schema.String)")
        );
        let structural_text = format!(
            "export class User extends Schema.Class<User>(\"User\")({{\n{}}}) {{}}\n\n{INTERFACE}",
            fields("Schema.optional(Schema.Union(Schema.Undefined, Schema.String))")
        );
        let actions = refactors(&service, range(2, 17, 21));
        let expected = vec![
            (
                "Wrap with pipe".to_string(),
                "refactor.rewrite.effect.wrapWithPipe".to_string(),
                main_with("User {", "pipe(User) {"),
            ),
            (
                "Generate Effect.Schema from type".to_string(),
                "refactor.rewrite.effect.typeToEffectSchema".to_string(),
                main_with(INTERFACE, &struct_text),
            ),
            (
                "Generate Schema.Class from type".to_string(),
                "refactor.rewrite.effect.typeToEffectSchemaClass".to_string(),
                main_with(INTERFACE, &class_text),
            ),
            (
                "Refactor to Schema (Recursive Structural)".to_string(),
                "refactor.rewrite.effect.structuralTypeToSchema".to_string(),
                main_with(INTERFACE, &structural_text),
            ),
        ];
        assert_eq!(actions, expected);
    }
}

child_test! {
    // On a const whose initializer is a Schema: the two opaque refactors
    // rename the const to `UserSchema_` and add the v3 opaque types and the
    // typed const after its statement (the formatted nodes of the base
    // tracker's InsertNodesAfter).
    fn make_schema_opaque_on_a_schema_const() {
        let (_session, service) = service();
        let actions = refactors(&service, range(8, 13, 23));
        let opaque: Vec<_> = actions
            .into_iter()
            .filter(|(_, kind, _)| kind.starts_with("refactor.rewrite.effect.makeSchemaOpaque"))
            .collect();
        let statement = "export const UserSchema = Schema.Struct({ id: Schema.Number })\n";
        let renamed = "export const UserSchema_ = Schema.Struct({ id: Schema.Number })\n";
        let expected = vec![
            (
                "Make Schema opaque".to_string(),
                "refactor.rewrite.effect.makeSchemaOpaque".to_string(),
                main_with(
                    statement,
                    &(renamed.to_string()
                        + "export interface UserSchema extends Schema.Schema.Type<typeof UserSchema_> { }\n"
                        + "export interface UserSchemaEncoded extends Schema.Schema.Encoded<typeof UserSchema_> { }\n"
                        + "export type UserSchemaContext = Schema.Schema.Context<typeof UserSchema_>;\n"
                        + "export const UserSchema: Schema.Schema<UserSchema, UserSchemaEncoded, UserSchemaContext> = UserSchema_;\n"),
                ),
            ),
            (
                "Make Schema opaque with namespace".to_string(),
                "refactor.rewrite.effect.makeSchemaOpaqueWithNs".to_string(),
                main_with(
                    statement,
                    &(renamed.to_string()
                        + "export interface UserSchema extends Schema.Schema.Type<typeof UserSchema_> { }\n"
                        + "export namespace UserSchema {\n"
                        + "    export interface Encoded extends Schema.Schema.Encoded<typeof UserSchema_> { }\n"
                        + "    export type Context = Schema.Schema.Context<typeof UserSchema_>;\n"
                        + "}\n"
                        + "export const UserSchema: Schema.Schema<UserSchema, UserSchema.Encoded, UserSchema.Context> = UserSchema_;\n"),
                ),
            ),
        ];
        assert_eq!(opaque, expected);
    }
}

child_test! {
    // A type that refers to itself: the structural schemagen hoists `Tree`
    // only after its members, so each `Array<Tree>` processes `Tree` again
    // until the depth limit (200), and the action inserts the error as the
    // initializer (Go: schemagen/structural.go processType, Process). The
    // same for the union `Json` through `ReadonlyArray<Json>`. effect-tsgo
    // 0.51.1 gives these texts (ls-case
    // refactors/effect-v3-port/structuralTypeToSchema_selfRecursive).
    fn structural_schema_of_a_self_recursive_type() {
        let (_session, service) = service_for(TREE_URI, TREE_TEXT);
        let structural = |range| {
            let actions: Vec<_> = refactors_in(&service, TREE_URI, TREE_TEXT, range)
                .into_iter()
                .filter(|(_, kind, _)| kind == "refactor.rewrite.effect.structuralTypeToSchema")
                .map(|(_, _, text)| text)
                .collect();
            actions
        };
        let with = |old: &str, new: &str| TREE_TEXT.replacen(old, new, 1);
        assert_eq!(
            structural(range(2, 17, 21)),
            vec![with(
                "export interface Tree {",
                "export const Tree = undefined /* maximum depth exceeded */;\n\nexport interface Tree {",
            )]
        );
        assert_eq!(
            structural(range(7, 12, 16)),
            vec![with(
                "export type Json =",
                "export const Json = undefined /* maximum depth exceeded */;\n\nexport type Json =",
            )]
        );
    }
}
