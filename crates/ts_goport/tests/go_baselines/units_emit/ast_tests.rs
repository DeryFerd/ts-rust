//! Ports of internal/ast/deepclone_test.go, diagnostic_test.go and
//! positionmap_test.go.

use super::Subtests;
use super::childprog::in_child;
use super::parsetestutil::parse_type_script_published;
use ts_diagnostics::Message;
use ts_goport::ast::{NodeVisitor, NodeVisitorHooks, compute_position_map, new_node_visitor};
use ts_goport::frontend::core_ext::get_script_kind_from_file_name;
use ts_goport::frontend::parser::{SourceFileParseOptions, parse_source_file};
use ts_goport::frontend::tspath::Path;
use ts_goport::prelude::*;

/// Go `NodeComparisonWorkItem`: (original, copy).
type NodeComparisonWorkItem = (Node, Node);

// Go: ast/deepclone_test.go:16 getChildren
fn get_children(node: Node) -> Vec<Node> {
    let mut v = new_node_visitor(
        |node: Node, v: &mut NodeVisitor<'_, Vec<Node>>| {
            v.ctx.push(node);
            node
        },
        None,
        NodeVisitorHooks::default(),
        Vec::new(),
    );
    node.visit_each_child(&mut v);
    v.ctx
}

/// Go TestDeepCloneNodeSanityCheck rows: (title, input, jsx).
#[rustfmt::skip]
const DEEP_CLONE: &[(&str, &str, bool)] = &[
    ("StringLiteral#1", r#";"test""#, false),
    ("StringLiteral#2", ";'test'", false),
    ("NumericLiteral", "0", false),
    ("BigIntLiteral", "0n", false),
    ("BooleanLiteral#1", "true", false),
    ("BooleanLiteral#2", "false", false),
    ("NoSubstitutionTemplateLiteral", "``", false),
    ("RegularExpressionLiteral#1", "/a/", false),
    ("RegularExpressionLiteral#2", "/a/g", false),
    ("NullLiteral", "null", false),
    ("ThisExpression", "this", false),
    ("SuperExpression", "super()", false),
    ("ImportExpression", "import()", false),
    ("PropertyAccess#1", "a.b", false),
    ("PropertyAccess#2", "a.#b", false),
    ("PropertyAccess#3", "a?.b", false),
    ("PropertyAccess#4", "a?.b.c", false),
    ("PropertyAccess#5", "1..b", false),
    ("PropertyAccess#6", "1.0.b", false),
    ("PropertyAccess#7", "0x1.b", false),
    ("PropertyAccess#8", "0b1.b", false),
    ("PropertyAccess#9", "0o1.b", false),
    ("PropertyAccess#10", "10e1.b", false),
    ("PropertyAccess#11", "10E1.b", false),
    ("ElementAccess#1", "a[b]", false),
    ("ElementAccess#2", "a?.[b]", false),
    ("ElementAccess#3", "a?.[b].c", false),
    ("CallExpression#1", "a()", false),
    ("CallExpression#2", "a<T>()", false),
    ("CallExpression#3", "a(b)", false),
    ("CallExpression#4", "a<T>(b)", false),
    ("CallExpression#5", "a(b).c", false),
    ("CallExpression#6", "a<T>(b).c", false),
    ("CallExpression#7", "a?.(b)", false),
    ("CallExpression#8", "a?.<T>(b)", false),
    ("CallExpression#9", "a?.(b).c", false),
    ("CallExpression#10", "a?.<T>(b).c", false),
    ("CallExpression#11", "a<T, U>()", false),
    ("CallExpression#12", "a<T,>()", false),
    ("NewExpression#1", "new a", false),
    ("NewExpression#2", "new a.b", false),
    ("NewExpression#3", "new a()", false),
    ("NewExpression#4", "new a.b()", false),
    ("NewExpression#5", "new a<T>()", false),
    ("NewExpression#6", "new a.b<T>()", false),
    ("NewExpression#7", "new a(b)", false),
    ("NewExpression#8", "new a.b(c)", false),
    ("NewExpression#9", "new a<T>(b)", false),
    ("NewExpression#10", "new a.b<T>(c)", false),
    ("NewExpression#11", "new a(b).c", false),
    ("NewExpression#12", "new a<T>(b).c", false),
    ("TaggedTemplateExpression#1", "tag``", false),
    ("TaggedTemplateExpression#2", "tag<T>``", false),
    ("TypeAssertionExpression#1", "<T>a", false),
    ("FunctionExpression#1", "(function(){})", false),
    ("FunctionExpression#2", "(function f(){})", false),
    ("FunctionExpression#3", "(function*f(){})", false),
    ("FunctionExpression#4", "(async function f(){})", false),
    ("FunctionExpression#5", "(async function*f(){})", false),
    ("FunctionExpression#6", "(function<T>(){})", false),
    ("FunctionExpression#7", "(function(a){})", false),
    ("FunctionExpression#8", "(function():T{})", false),
    ("ArrowFunction#1", "a=>{}", false),
    ("ArrowFunction#2", "()=>{}", false),
    ("ArrowFunction#3", "(a)=>{}", false),
    ("ArrowFunction#4", "<T>(a)=>{}", false),
    ("ArrowFunction#5", "async a=>{}", false),
    ("ArrowFunction#6", "async()=>{}", false),
    ("ArrowFunction#7", "async<T>()=>{}", false),
    ("ArrowFunction#8", "():T=>{}", false),
    ("ArrowFunction#9", "()=>a", false),
    ("DeleteExpression", "delete a", false),
    ("TypeOfExpression", "typeof a", false),
    ("VoidExpression", "void a", false),
    ("AwaitExpression", "await a", false),
    ("PrefixUnaryExpression#1", "+a", false),
    ("PrefixUnaryExpression#2", "++a", false),
    ("PrefixUnaryExpression#3", "+ +a", false),
    ("PrefixUnaryExpression#4", "+ ++a", false),
    ("PrefixUnaryExpression#5", "-a", false),
    ("PrefixUnaryExpression#6", "--a", false),
    ("PrefixUnaryExpression#7", "- -a", false),
    ("PrefixUnaryExpression#8", "- --a", false),
    ("PrefixUnaryExpression#9", "+-a", false),
    ("PrefixUnaryExpression#10", "+--a", false),
    ("PrefixUnaryExpression#11", "-+a", false),
    ("PrefixUnaryExpression#12", "-++a", false),
    ("PrefixUnaryExpression#13", "~a", false),
    ("PrefixUnaryExpression#14", "!a", false),
    ("PostfixUnaryExpression#1", "a++", false),
    ("PostfixUnaryExpression#2", "a--", false),
    ("BinaryExpression#1", "a,b", false),
    ("BinaryExpression#2", "a+b", false),
    ("BinaryExpression#3", "a**b", false),
    ("BinaryExpression#4", "a instanceof b", false),
    ("BinaryExpression#5", "a in b", false),
    ("ConditionalExpression", "a?b:c", false),
    ("TemplateExpression#1", "`a${b}c`", false),
    ("TemplateExpression#2", "`a${b}c${d}e`", false),
    ("YieldExpression#1", "(function*() { yield })", false),
    ("YieldExpression#2", "(function*() { yield a })", false),
    ("YieldExpression#3", "(function*() { yield*a })", false),
    ("SpreadElement", "[...a]", false),
    ("ClassExpression#1", "(class {})", false),
    ("ClassExpression#2", "(class a {})", false),
    ("ClassExpression#3", "(class<T>{})", false),
    ("ClassExpression#4", "(class a<T>{})", false),
    ("ClassExpression#5", "(class extends b {})", false),
    ("ClassExpression#6", "(class a extends b {})", false),
    ("ClassExpression#7", "(class implements b {})", false),
    ("ClassExpression#8", "(class a implements b {})", false),
    ("ClassExpression#9", "(class implements b, c {})", false),
    ("ClassExpression#10", "(class a implements b, c {})", false),
    ("ClassExpression#11", "(class extends b implements c, d {})", false),
    ("ClassExpression#12", "(class a extends b implements c, d {})", false),
    ("ClassExpression#13", "(@a class {})", false),
    ("OmittedExpression", "[,]", false),
    ("ExpressionWithTypeArguments", "a<T>", false),
    ("AsExpression", "a as T", false),
    ("SatisfiesExpression", "a satisfies T", false),
    ("NonNullExpression", "a!", false),
    ("MetaProperty#1", "new.target", false),
    ("MetaProperty#2", "import.meta", false),
    ("ArrayLiteralExpression#1", "[]", false),
    ("ArrayLiteralExpression#2", "[a]", false),
    ("ArrayLiteralExpression#3", "[a,]", false),
    ("ArrayLiteralExpression#4", "[,a]", false),
    ("ArrayLiteralExpression#5", "[...a]", false),
    ("ObjectLiteralExpression#1", "({})", false),
    ("ObjectLiteralExpression#2", "({a,})", false),
    ("ShorthandPropertyAssignment", "({a})", false),
    ("PropertyAssignment", "({a:b})", false),
    ("SpreadAssignment", "({...a})", false),
    ("Block", "{}", false),
    ("VariableStatement#1", "var a", false),
    ("VariableStatement#2", "let a", false),
    ("VariableStatement#3", "const a = b", false),
    ("VariableStatement#4", "using a = b", false),
    ("VariableStatement#5", "await using a = b", false),
    ("EmptyStatement", ";", false),
    ("IfStatement#1", "if(a);", false),
    ("IfStatement#2", "if(a);else;", false),
    ("IfStatement#3", "if(a);else{}", false),
    ("IfStatement#4", "if(a);else if(b);", false),
    ("IfStatement#5", "if(a);else if(b) {}", false),
    ("IfStatement#6", "if(a) {}", false),
    ("IfStatement#7", "if(a) {} else;", false),
    ("IfStatement#8", "if(a) {} else {}", false),
    ("IfStatement#9", "if(a) {} else if(b);", false),
    ("IfStatement#10", "if(a) {} else if(b){}", false),
    ("DoStatement#1", "do;while(a);", false),
    ("DoStatement#2", "do {} while(a);", false),
    ("WhileStatement#1", "while(a);", false),
    ("WhileStatement#2", "while(a) {}", false),
    ("ForStatement#1", "for(;;);", false),
    ("ForStatement#2", "for(a;;);", false),
    ("ForStatement#3", "for(var a;;);", false),
    ("ForStatement#4", "for(;a;);", false),
    ("ForStatement#5", "for(;;a);", false),
    ("ForStatement#6", "for(;;){}", false),
    ("ForInStatement#1", "for(a in b);", false),
    ("ForInStatement#2", "for(var a in b);", false),
    ("ForInStatement#3", "for(a in b){}", false),
    ("ForOfStatement#1", "for(a of b);", false),
    ("ForOfStatement#2", "for(var a of b);", false),
    ("ForOfStatement#3", "for(a of b){}", false),
    ("ForOfStatement#4", "for await(a of b);", false),
    ("ForOfStatement#5", "for await(var a of b);", false),
    ("ForOfStatement#6", "for await(a of b){}", false),
    ("ContinueStatement#1", "continue", false),
    ("ContinueStatement#2", "continue a", false),
    ("BreakStatement#1", "break", false),
    ("BreakStatement#2", "break a", false),
    ("ReturnStatement#1", "return", false),
    ("ReturnStatement#2", "return a", false),
    ("WithStatement#1", "with(a);", false),
    ("WithStatement#2", "with(a){}", false),
    ("SwitchStatement", "switch (a) {}", false),
    ("CaseClause#1", "switch (a) {case b:}", false),
    ("CaseClause#2", "switch (a) {case b:;}", false),
    ("DefaultClause#1", "switch (a) {default:}", false),
    ("DefaultClause#2", "switch (a) {default:;}", false),
    ("LabeledStatement", "a:;", false),
    ("ThrowStatement", "throw a", false),
    ("TryStatement#1", "try {} catch {}", false),
    ("TryStatement#2", "try {} finally {}", false),
    ("TryStatement#3", "try {} catch {} finally {}", false),
    ("DebuggerStatement", "debugger", false),
    ("FunctionDeclaration#1", "export default function(){}", false),
    ("FunctionDeclaration#2", "function f(){}", false),
    ("FunctionDeclaration#3", "function*f(){}", false),
    ("FunctionDeclaration#4", "async function f(){}", false),
    ("FunctionDeclaration#5", "async function*f(){}", false),
    ("FunctionDeclaration#6", "function f<T>(){}", false),
    ("FunctionDeclaration#7", "function f(a){}", false),
    ("FunctionDeclaration#8", "function f():T{}", false),
    ("FunctionDeclaration#9", "function f();", false),
    ("ClassDeclaration#1", "class a {}", false),
    ("ClassDeclaration#2", "class a<T>{}", false),
    ("ClassDeclaration#3", "class a extends b {}", false),
    ("ClassDeclaration#4", "class a implements b {}", false),
    ("ClassDeclaration#5", "class a implements b, c {}", false),
    ("ClassDeclaration#6", "class a extends b implements c, d {}", false),
    ("ClassDeclaration#7", "export default class {}", false),
    ("ClassDeclaration#8", "export default class<T>{}", false),
    ("ClassDeclaration#9", "export default class extends b {}", false),
    ("ClassDeclaration#10", "export default class implements b {}", false),
    ("ClassDeclaration#11", "export default class implements b, c {}", false),
    ("ClassDeclaration#12", "export default class extends b implements c, d {}", false),
    ("ClassDeclaration#13", "@a class b {}", false),
    ("ClassDeclaration#14", "@a export class b {}", false),
    ("ClassDeclaration#15", "export @a class b {}", false),
    ("InterfaceDeclaration#1", "interface a {}", false),
    ("InterfaceDeclaration#2", "interface a<T>{}", false),
    ("InterfaceDeclaration#3", "interface a extends b {}", false),
    ("InterfaceDeclaration#4", "interface a extends b, c {}", false),
    ("TypeAliasDeclaration#1", "type a = b", false),
    ("TypeAliasDeclaration#2", "type a<T> = b", false),
    ("EnumDeclaration#1", "enum a{}", false),
    ("EnumDeclaration#2", "enum a{b}", false),
    ("EnumDeclaration#3", "enum a{b=c}", false),
    ("ModuleDeclaration#1", "module a{}", false),
    ("ModuleDeclaration#2", "module a.b{}", false),
    ("ModuleDeclaration#3", r#"module "a";"#, false),
    ("ModuleDeclaration#4", r#"module "a"{}"#, false),
    ("ModuleDeclaration#5", "namespace a{}", false),
    ("ModuleDeclaration#6", "namespace a.b{}", false),
    ("ModuleDeclaration#7", "global;", false),
    ("ModuleDeclaration#8", "global{}", false),
    ("ImportEqualsDeclaration#1", "import a = b", false),
    ("ImportEqualsDeclaration#2", "import a = b.c", false),
    ("ImportEqualsDeclaration#3", r#"import a = require("b")"#, false),
    ("ImportEqualsDeclaration#4", "export import a = b", false),
    ("ImportEqualsDeclaration#5", r#"export import a = require("b")"#, false),
    ("ImportEqualsDeclaration#6", "import type a = b", false),
    ("ImportEqualsDeclaration#7", "import type a = b.c", false),
    ("ImportEqualsDeclaration#8", r#"import type a = require("b")"#, false),
    ("ImportDeclaration#1", r#"import "a""#, false),
    ("ImportDeclaration#2", r#"import a from "b""#, false),
    ("ImportDeclaration#3", r#"import type a from "b""#, false),
    ("ImportDeclaration#4", r#"import * as a from "b""#, false),
    ("ImportDeclaration#5", r#"import type * as a from "b""#, false),
    ("ImportDeclaration#6", r#"import {} from "b""#, false),
    ("ImportDeclaration#7", r#"import type {} from "b""#, false),
    ("ImportDeclaration#8", r#"import { a } from "b""#, false),
    ("ImportDeclaration#9", r#"import type { a } from "b""#, false),
    ("ImportDeclaration#8", r#"import { a as b } from "c""#, false),
    ("ImportDeclaration#9", r#"import type { a as b } from "c""#, false),
    ("ImportDeclaration#10", r#"import { "a" as b } from "c""#, false),
    ("ImportDeclaration#11", r#"import type { "a" as b } from "c""#, false),
    ("ImportDeclaration#12", r#"import a, {} from "b""#, false),
    ("ImportDeclaration#13", r#"import a, * as b from "c""#, false),
    ("ImportDeclaration#14", r#"import {} from "a" with {}"#, false),
    ("ImportDeclaration#15", r#"import {} from "a" with { b: "c" }"#, false),
    ("ImportDeclaration#16", r#"import {} from "a" with { "b": "c" }"#, false),
    ("ExportAssignment#1", "export = a", false),
    ("ExportAssignment#2", "export default a", false),
    ("NamespaceExportDeclaration", "export as namespace a", false),
    ("ExportDeclaration#1", r#"export * from "a""#, false),
    ("ExportDeclaration#2", r#"export type * from "a""#, false),
    ("ExportDeclaration#3", r#"export * as a from "b""#, false),
    ("ExportDeclaration#4", r#"export type * as a from "b""#, false),
    ("ExportDeclaration#5", r#"export { } from "a""#, false),
    ("ExportDeclaration#6", r#"export type { } from "a""#, false),
    ("ExportDeclaration#7", r#"export { a } from "b""#, false),
    ("ExportDeclaration#8", r#"export { type a } from "b""#, false),
    ("ExportDeclaration#9", r#"export type { a } from "b""#, false),
    ("ExportDeclaration#10", r#"export { a as b } from "c""#, false),
    ("ExportDeclaration#11", r#"export { type a as b } from "c""#, false),
    ("ExportDeclaration#12", r#"export type { a as b } from "c""#, false),
    ("ExportDeclaration#13", r#"export { a as "b" } from "c""#, false),
    ("ExportDeclaration#14", r#"export { type a as "b" } from "c""#, false),
    ("ExportDeclaration#15", r#"export type { a as "b" } from "c""#, false),
    ("ExportDeclaration#16", r#"export { "a" } from "b""#, false),
    ("ExportDeclaration#17", r#"export { type "a" } from "b""#, false),
    ("ExportDeclaration#18", r#"export type { "a" } from "b""#, false),
    ("ExportDeclaration#19", r#"export { "a" as b } from "c""#, false),
    ("ExportDeclaration#20", r#"export { type "a" as b } from "c""#, false),
    ("ExportDeclaration#21", r#"export type { "a" as b } from "c""#, false),
    ("ExportDeclaration#22", r#"export { "a" as "b" } from "c""#, false),
    ("ExportDeclaration#23", r#"export { type "a" as "b" } from "c""#, false),
    ("ExportDeclaration#24", r#"export type { "a" as "b" } from "c""#, false),
    ("ExportDeclaration#25", "export { }", false),
    ("ExportDeclaration#26", "export type { }", false),
    ("ExportDeclaration#27", "export { a }", false),
    ("ExportDeclaration#28", "export { type a }", false),
    ("ExportDeclaration#29", "export type { a }", false),
    ("ExportDeclaration#30", "export { a as b }", false),
    ("ExportDeclaration#31", "export { type a as b }", false),
    ("ExportDeclaration#32", "export type { a as b }", false),
    ("ExportDeclaration#33", r#"export { a as "b" }"#, false),
    ("ExportDeclaration#34", r#"export { type a as "b" }"#, false),
    ("ExportDeclaration#35", r#"export type { a as "b" }"#, false),
    ("ExportDeclaration#36", r#"export {} from "a" with {}"#, false),
    ("ExportDeclaration#37", r#"export {} from "a" with { b: "c" }"#, false),
    ("ExportDeclaration#38", r#"export {} from "a" with { "b": "c" }"#, false),
    ("KeywordTypeNode#1", "type T = any", false),
    ("KeywordTypeNode#2", "type T = unknown", false),
    ("KeywordTypeNode#3", "type T = never", false),
    ("KeywordTypeNode#4", "type T = void", false),
    ("KeywordTypeNode#5", "type T = undefined", false),
    ("KeywordTypeNode#6", "type T = null", false),
    ("KeywordTypeNode#7", "type T = object", false),
    ("KeywordTypeNode#8", "type T = string", false),
    ("KeywordTypeNode#9", "type T = symbol", false),
    ("KeywordTypeNode#10", "type T = number", false),
    ("KeywordTypeNode#11", "type T = bigint", false),
    ("KeywordTypeNode#12", "type T = boolean", false),
    ("KeywordTypeNode#13", "type T = intrinsic", false),
    ("TypePredicateNode#1", "function f(): asserts a", false),
    ("TypePredicateNode#2", "function f(): asserts a is b", false),
    ("TypePredicateNode#3", "function f(): asserts this", false),
    ("TypePredicateNode#4", "function f(): asserts this is b", false),
    ("TypeReferenceNode#1", "type T = a", false),
    ("TypeReferenceNode#2", "type T = a.b", false),
    ("TypeReferenceNode#3", "type T = a<U>", false),
    ("TypeReferenceNode#4", "type T = a.b<U>", false),
    ("FunctionTypeNode#1", "type T = () => a", false),
    ("FunctionTypeNode#2", "type T = <T>() => a", false),
    ("FunctionTypeNode#3", "type T = (a) => b", false),
    ("ConstructorTypeNode#1", "type T = new () => a", false),
    ("ConstructorTypeNode#2", "type T = new <T>() => a", false),
    ("ConstructorTypeNode#3", "type T = new (a) => b", false),
    ("ConstructorTypeNode#4", "type T = abstract new () => a", false),
    ("TypeQueryNode#1", "type T = typeof a", false),
    ("TypeQueryNode#2", "type T = typeof a.b", false),
    ("TypeQueryNode#3", "type T = typeof a<U>", false),
    ("TypeLiteralNode#1", "type T = {}", false),
    ("TypeLiteralNode#2", "type T = {a}", false),
    ("ArrayTypeNode", "type T = a[]", false),
    ("TupleTypeNode#1", "type T = []", false),
    ("TupleTypeNode#2", "type T = [a]", false),
    ("TupleTypeNode#3", "type T = [a,]", false),
    ("RestTypeNode", "type T = [...a]", false),
    ("OptionalTypeNode", "type T = [a?]", false),
    ("NamedTupleMember#1", "type T = [a: b]", false),
    ("NamedTupleMember#2", "type T = [a?: b]", false),
    ("NamedTupleMember#3", "type T = [...a: b]", false),
    ("UnionTypeNode#1", "type T = a | b", false),
    ("UnionTypeNode#2", "type T = a | b | c", false),
    ("UnionTypeNode#3", "type T = | a | b", false),
    ("IntersectionTypeNode#1", "type T = a & b", false),
    ("IntersectionTypeNode#2", "type T = a & b & c", false),
    ("IntersectionTypeNode#3", "type T = & a & b", false),
    ("ConditionalTypeNode", "type T = a extends b ? c : d", false),
    ("InferTypeNode#1", "type T = a extends infer b ? c : d", false),
    ("InferTypeNode#2", "type T = a extends infer b extends c ? d : e", false),
    ("ParenthesizedTypeNode", "type T = (U)", false),
    ("ThisTypeNode", "type T = this", false),
    ("TypeOperatorNode#1", "type T = keyof U", false),
    ("TypeOperatorNode#2", "type T = readonly U[]", false),
    ("TypeOperatorNode#3", "type T = unique symbol", false),
    ("IndexedAccessTypeNode", "type T = a[b]", false),
    ("MappedTypeNode#1", "type T = { [a in b]: c }", false),
    ("MappedTypeNode#2", "type T = { [a in b as c]: d }", false),
    ("MappedTypeNode#3", "type T = { readonly [a in b]: c }", false),
    ("MappedTypeNode#4", "type T = { +readonly [a in b]: c }", false),
    ("MappedTypeNode#5", "type T = { -readonly [a in b]: c }", false),
    ("MappedTypeNode#6", "type T = { [a in b]?: c }", false),
    ("MappedTypeNode#7", "type T = { [a in b]+?: c }", false),
    ("MappedTypeNode#8", "type T = { [a in b]-?: c }", false),
    ("MappedTypeNode#9", "type T = { [a in b]: c; d }", false),
    ("LiteralTypeNode#1", "type T = null", false),
    ("LiteralTypeNode#2", "type T = true", false),
    ("LiteralTypeNode#3", "type T = false", false),
    ("LiteralTypeNode#4", r#"type T = """#, false),
    ("LiteralTypeNode#5", "type T = ''", false),
    ("LiteralTypeNode#6", "type T = ``", false),
    ("LiteralTypeNode#7", "type T = 0", false),
    ("LiteralTypeNode#8", "type T = 0n", false),
    ("LiteralTypeNode#9", "type T = -0", false),
    ("LiteralTypeNode#10", "type T = -0n", false),
    ("TemplateTypeNode#1", "type T = `a${b}c`", false),
    ("TemplateTypeNode#2", "type T = `a${b}c${d}e`", false),
    ("ImportTypeNode#1", "type T = import(a)", false),
    ("ImportTypeNode#2", "type T = import(a).b", false),
    ("ImportTypeNode#3", "type T = import(a).b<U>", false),
    ("ImportTypeNode#4", "type T = typeof import(a)", false),
    ("ImportTypeNode#5", "type T = typeof import(a).b", false),
    ("ImportTypeNode#6", "type T = import(a, { with: { } })", false),
    ("ImportTypeNode#6", r#"type T = import(a, { with: { b: "c" } })"#, false),
    ("ImportTypeNode#7", r#"type T = import(a, { with: { "b": "c" } })"#, false),
    ("PropertySignature#1", "interface I {a}", false),
    ("PropertySignature#2", "interface I {readonly a}", false),
    ("PropertySignature#3", "interface I {\"a\"}", false),
    ("PropertySignature#4", "interface I {'a'}", false),
    ("PropertySignature#5", "interface I {0}", false),
    ("PropertySignature#6", "interface I {0n}", false),
    ("PropertySignature#7", "interface I {[a]}", false),
    ("PropertySignature#8", "interface I {a?}", false),
    ("PropertySignature#9", "interface I {a: b}", false),
    ("MethodSignature#1", "interface I {a()}", false),
    ("MethodSignature#2", "interface I {\"a\"()}", false),
    ("MethodSignature#3", "interface I {'a'()}", false),
    ("MethodSignature#4", "interface I {0()}", false),
    ("MethodSignature#5", "interface I {0n()}", false),
    ("MethodSignature#6", "interface I {[a]()}", false),
    ("MethodSignature#7", "interface I {a?()}", false),
    ("MethodSignature#8", "interface I {a<T>()}", false),
    ("MethodSignature#9", "interface I {a(): b}", false),
    ("MethodSignature#10", "interface I {a(b): c}", false),
    ("CallSignature#1", "interface I {()}", false),
    ("CallSignature#2", "interface I {():a}", false),
    ("CallSignature#3", "interface I {(p)}", false),
    ("CallSignature#4", "interface I {<T>()}", false),
    ("ConstructSignature#1", "interface I {new ()}", false),
    ("ConstructSignature#2", "interface I {new ():a}", false),
    ("ConstructSignature#3", "interface I {new (p)}", false),
    ("ConstructSignature#4", "interface I {new <T>()}", false),
    ("IndexSignatureDeclaration#1", "interface I {[a]}", false),
    ("IndexSignatureDeclaration#2", "interface I {[a: b]}", false),
    ("IndexSignatureDeclaration#3", "interface I {[a: b]: c}", false),
    ("PropertyDeclaration#1", "class C {a}", false),
    ("PropertyDeclaration#2", "class C {readonly a}", false),
    ("PropertyDeclaration#3", "class C {static a}", false),
    ("PropertyDeclaration#4", "class C {accessor a}", false),
    ("PropertyDeclaration#5", "class C {\"a\"}", false),
    ("PropertyDeclaration#6", "class C {'a'}", false),
    ("PropertyDeclaration#7", "class C {0}", false),
    ("PropertyDeclaration#8", "class C {0n}", false),
    ("PropertyDeclaration#9", "class C {[a]}", false),
    ("PropertyDeclaration#10", "class C {#a}", false),
    ("PropertyDeclaration#11", "class C {a?}", false),
    ("PropertyDeclaration#12", "class C {a!}", false),
    ("PropertyDeclaration#13", "class C {a: b}", false),
    ("PropertyDeclaration#14", "class C {a = b}", false),
    ("PropertyDeclaration#15", "class C {@a b}", false),
    ("MethodDeclaration#1", "class C {a()}", false),
    ("MethodDeclaration#2", "class C {\"a\"()}", false),
    ("MethodDeclaration#3", "class C {'a'()}", false),
    ("MethodDeclaration#4", "class C {0()}", false),
    ("MethodDeclaration#5", "class C {0n()}", false),
    ("MethodDeclaration#6", "class C {[a]()}", false),
    ("MethodDeclaration#7", "class C {#a()}", false),
    ("MethodDeclaration#8", "class C {a?()}", false),
    ("MethodDeclaration#9", "class C {a<T>()}", false),
    ("MethodDeclaration#10", "class C {a(): b}", false),
    ("MethodDeclaration#11", "class C {a(b): c}", false),
    ("MethodDeclaration#12", "class C {a() {} }", false),
    ("MethodDeclaration#13", "class C {@a b() {} }", false),
    ("MethodDeclaration#14", "class C {static a() {} }", false),
    ("MethodDeclaration#15", "class C {async a() {} }", false),
    ("GetAccessorDeclaration#1", "class C {get a()}", false),
    ("GetAccessorDeclaration#2", "class C {get \"a\"()}", false),
    ("GetAccessorDeclaration#3", "class C {get 'a'()}", false),
    ("GetAccessorDeclaration#4", "class C {get 0()}", false),
    ("GetAccessorDeclaration#5", "class C {get 0n()}", false),
    ("GetAccessorDeclaration#6", "class C {get [a]()}", false),
    ("GetAccessorDeclaration#7", "class C {get #a()}", false),
    ("GetAccessorDeclaration#8", "class C {get a(): b}", false),
    ("GetAccessorDeclaration#9", "class C {get a(b): c}", false),
    ("GetAccessorDeclaration#10", "class C {get a() {} }", false),
    ("GetAccessorDeclaration#11", "class C {@a get b() {} }", false),
    ("GetAccessorDeclaration#12", "class C {static get a() {} }", false),
    ("SetAccessorDeclaration#1", "class C {set a()}", false),
    ("SetAccessorDeclaration#2", "class C {set \"a\"()}", false),
    ("SetAccessorDeclaration#3", "class C {set 'a'()}", false),
    ("SetAccessorDeclaration#4", "class C {set 0()}", false),
    ("SetAccessorDeclaration#5", "class C {set 0n()}", false),
    ("SetAccessorDeclaration#6", "class C {set [a]()}", false),
    ("SetAccessorDeclaration#7", "class C {set #a()}", false),
    ("SetAccessorDeclaration#8", "class C {set a(): b}", false),
    ("SetAccessorDeclaration#9", "class C {set a(b): c}", false),
    ("SetAccessorDeclaration#10", "class C {set a() {} }", false),
    ("SetAccessorDeclaration#11", "class C {@a set b() {} }", false),
    ("SetAccessorDeclaration#12", "class C {static set a() {} }", false),
    ("ConstructorDeclaration#1", "class C {constructor()}", false),
    ("ConstructorDeclaration#2", "class C {constructor(): b}", false),
    ("ConstructorDeclaration#3", "class C {constructor(b): c}", false),
    ("ConstructorDeclaration#4", "class C {constructor() {} }", false),
    ("ConstructorDeclaration#5", "class C {@a constructor() {} }", false),
    ("ConstructorDeclaration#6", "class C {private constructor() {} }", false),
    ("ClassStaticBlockDeclaration", "class C {static { }}", false),
    ("SemicolonClassElement#1", "class C {;}", false),
    ("ParameterDeclaration#1", "function f(a)", false),
    ("ParameterDeclaration#2", "function f(a: b)", false),
    ("ParameterDeclaration#3", "function f(a = b)", false),
    ("ParameterDeclaration#4", "function f(a?)", false),
    ("ParameterDeclaration#5", "function f(...a)", false),
    ("ParameterDeclaration#6", "function f(this)", false),
    ("ParameterDeclaration#7", "function f(a,)", false),
    ("ObjectBindingPattern#1", "function f({})", false),
    ("ObjectBindingPattern#2", "function f({a})", false),
    ("ObjectBindingPattern#3", "function f({a = b})", false),
    ("ObjectBindingPattern#4", "function f({a: b})", false),
    ("ObjectBindingPattern#5", "function f({a: b = c})", false),
    ("ObjectBindingPattern#6", "function f({\"a\": b})", false),
    ("ObjectBindingPattern#7", "function f({'a': b})", false),
    ("ObjectBindingPattern#8", "function f({0: b})", false),
    ("ObjectBindingPattern#9", "function f({[a]: b})", false),
    ("ObjectBindingPattern#10", "function f({...a})", false),
    ("ObjectBindingPattern#11", "function f({a: {}})", false),
    ("ObjectBindingPattern#12", "function f({a: []})", false),
    ("ArrayBindingPattern#1", "function f([])", false),
    ("ArrayBindingPattern#2", "function f([,])", false),
    ("ArrayBindingPattern#3", "function f([a])", false),
    ("ArrayBindingPattern#4", "function f([a, b])", false),
    ("ArrayBindingPattern#5", "function f([a, , b])", false),
    ("ArrayBindingPattern#6", "function f([a = b])", false),
    ("ArrayBindingPattern#7", "function f([...a])", false),
    ("ArrayBindingPattern#8", "function f([{}])", false),
    ("ArrayBindingPattern#9", "function f([[]])", false),
    ("TypeParameterDeclaration#1", "function f<T>();", false),
    ("TypeParameterDeclaration#2", "function f<in T>();", false),
    ("TypeParameterDeclaration#3", "function f<T extends U>();", false),
    ("TypeParameterDeclaration#4", "function f<T = U>();", false),
    ("TypeParameterDeclaration#5", "function f<T extends U = V>();", false),
    ("TypeParameterDeclaration#6", "function f<T, U>();", false),
    ("TypeParameterDeclaration#7", "function f<T,>();", false),
    ("JsxElement1", "<a></a>", false),
    ("JsxElement2", "<this></this>", false),
    ("JsxElement3", "<a:b></a:b>", false),
    ("JsxElement4", "<a.b></a.b>", false),
    ("JsxElement5", "<a<b>></a>", false),
    ("JsxElement6", "<a b></a>", false),
    ("JsxElement7", "<a>b</a>", false),
    ("JsxElement8", "<a>{b}</a>", false),
    ("JsxElement9", "<a><b></b></a>", false),
    ("JsxElement10", "<a><b /></a>", false),
    ("JsxElement11", "<a><></></a>", false),
    ("JsxSelfClosingElement1", "<a />", false),
    ("JsxSelfClosingElement2", "<this />", false),
    ("JsxSelfClosingElement3", "<a:b />", false),
    ("JsxSelfClosingElement4", "<a.b />", false),
    ("JsxSelfClosingElement5", "<a<b> />", false),
    ("JsxSelfClosingElement6", "<a b/>", false),
    ("JsxFragment1", "<></>", false),
    ("JsxFragment2", "<>b</>", false),
    ("JsxFragment3", "<>{b}</>", false),
    ("JsxFragment4", "<><b></b></>", false),
    ("JsxFragment5", "<><b /></>", false),
    ("JsxFragment6", "<><></></>", false),
    ("JsxAttribute1", "<a b/>", false),
    ("JsxAttribute2", "<a b:c/>", false),
    ("JsxAttribute3", "<a b=\"c\"/>", false),
    ("JsxAttribute4", "<a b='c'/>", false),
    ("JsxAttribute5", "<a b={c}/>", false),
    ("JsxAttribute6", "<a b=<c></c>/>", false),
    ("JsxAttribute7", "<a b=<c />/>", false),
    ("JsxAttribute8", "<a b=<></>/>", false),
    ("JsxSpreadAttribute", "<a {...b}/>", false),
];

// Go: ast/deepclone_test.go:25 TestDeepCloneNodeSanityCheck
// PORT: runs in a child process, because the clone needs the parsed file
// published (see `parse_type_script_published`).
#[test]
fn test_deep_clone_node_sanity_check() {
    in_child(
        module_path!(),
        "test_deep_clone_node_sanity_check",
        deep_clone_node_sanity_check,
    );
}

fn deep_clone_node_sanity_check() {
    let mut t = Subtests::new("TestDeepCloneNodeSanityCheck");
    for &(title, input, _jsx) in DEEP_CLONE {
        t.run(&format!("Clone {title}"), || {
            let factory = NodeFactory::new();
            // PORT: Go parses with `jsx` false for every row, as here.
            let file = parse_type_script_published(input, false);
            let clone = factory.deep_clone_node(file);

            let mut work: Vec<NodeComparisonWorkItem> = vec![(file, clone)];

            while !work.is_empty() {
                let mut next_work = Vec::new();
                for &(original, copy) in &work {
                    if original == copy {
                        return Err(format!("assertion failed: item.original != item.copy ({:?})", original.kind()));
                    }
                    let original_children = get_children(original);
                    let copy_children = get_children(copy);
                    if original_children.len() != copy_children.len() {
                        return Err(format!(
                            "assertion failed: {} (len(originalChildren)) != {} (len(copyChildren)) under {:?}",
                            original_children.len(),
                            copy_children.len(),
                            original.kind()
                        ));
                    }
                    for (i, &child) in original_children.iter().enumerate() {
                        next_work.push((child, copy_children[i]));
                    }
                }
                work = next_work;
            }
            Ok(())
        });
    }
    t.finish();
}

// Go: ast/diagnostic_test.go:12 TestDiagnosticsCollectionDeduplicatesExactDiagnosticsOnAdd
// PORT: `add` returns `&mut Diagnostic`. Go compares the returned pointers;
// here the addresses are compared while no `add` stores a new diagnostic in
// between, and the other checks compare values.
#[test]
fn test_diagnostics_collection_deduplicates_exact_diagnostics_on_add() {
    let new_diagnostic_with_related = |name: &str| {
        let mut diagnostic = new_compiler_diagnostic(diag::Cannot_find_name_0, args!["x"]);
        diagnostic.add_related_info(Some(new_compiler_diagnostic(
            diag::X_0_is_declared_here,
            args![name],
        )));
        diagnostic
    };
    let mut collection = DiagnosticsCollection::default();
    let first = new_diagnostic_with_related("first");
    let second = new_diagnostic_with_related("first");
    let different = new_diagnostic_with_related("second");

    let got = collection.add(first.clone());
    assert!(
        equal_diagnostics(got, &first),
        "first add() did not return first"
    );
    let first_address: *const Diagnostic = got;
    let canonical: *const Diagnostic = collection.add(second);
    assert!(
        std::ptr::eq(canonical, first_address),
        "second add() returned {canonical:p}, want canonical {first_address:p}"
    );
    let got = collection.add(different.clone());
    assert!(
        equal_diagnostics(got, &different),
        "different add() did not return different"
    );

    // PORT: Go changes `canonical` through its pointer. A borrow cannot live
    // across the `add` above, so `lookup` finds the stored first again.
    let third = new_compiler_diagnostic(diag::X_0_is_declared_here, args!["third"]);
    collection
        .lookup(&first)
        .expect("first is stored")
        .add_related_info(Some(third.clone()));
    let collected = collection.get_global_diagnostics();
    assert_eq!(
        collected.len(),
        2,
        "get_global_diagnostics() returned {} diagnostics, want 2",
        collected.len()
    );
    // Go reads `first.RelatedInformation()`: the stored first now has the
    // two related diagnostics.
    let mut want = first;
    want.add_related_info(Some(third));
    let got = collection
        .lookup(&want)
        .map(|d| d.related_information().len());
    assert_eq!(
        got,
        Some(2),
        "canonical diagnostic has {got:?} related diagnostics, want 2"
    );
}

// Go `ast.NewCompilerDiagnostic(diagnostics.NewAdHocMessage(message))`.
// PORT: as `compiler_runner::harness::new_ad_hoc_compiler_diagnostic`: a
// `ts_diagnostics::Message` code is a `u32`, so the Go code -1 is set on the
// diagnostic, and the message is leaked.
fn new_ad_hoc_compiler_diagnostic(text: &'static str) -> Diagnostic {
    let message: &'static Message = Box::leak(Box::new(Message::new(
        0,
        ts_diagnostics::Category::Error,
        "-1",
        text,
        false,
        false,
        false,
    )));
    let mut diagnostic = new_compiler_diagnostic(message, Vec::new());
    diagnostic.code = -1;
    diagnostic
}

// Go: ast/diagnostic_test.go:44 TestDiagnosticsCollectionPreservesDistinctAdHocMessages
#[test]
fn test_diagnostics_collection_preserves_distinct_ad_hoc_messages() {
    let mut collection = DiagnosticsCollection::default();
    let first = new_ad_hoc_compiler_diagnostic("first");
    let second = new_ad_hoc_compiler_diagnostic("second");

    collection.add(first);
    collection.add(second);
    let collected = collection.get_global_diagnostics();
    assert_eq!(
        collected.len(),
        2,
        "get_global_diagnostics() returned {} diagnostics, want 2",
        collected.len()
    );
}

// Go: ast/diagnostic_test.go:59 TestDiagnosticsCollectionGetsDiagnosticsForEquivalentSourceFile
// PORT: Go makes two bare SourceFile values with the same path. Here each
// file is an empty parse with that name, in its own store. Go compares the
// returned pointer; here the stored diagnostic must keep its own file.
#[test]
fn test_diagnostics_collection_gets_diagnostics_for_equivalent_source_file() {
    let parse = |file_name: &str| {
        parse_source_file(
            &SourceFileParseOptions {
                file_name: file_name.to_string(),
                path: Path(file_name.to_string()),
                ..Default::default()
            },
            "",
            get_script_kind_from_file_name(file_name),
        )
        .root
    };
    let path = "/src/file.ts";
    let diagnostic_file = parse(path);
    let requested_file = parse(path);
    let diagnostic = new_diagnostic(
        diagnostic_file,
        TextRange::new(0, 0),
        diag::Cannot_find_name_0,
        args!["x"],
    );

    let mut collection = DiagnosticsCollection::default();
    collection.add(diagnostic.clone());

    let collected = collection.get_diagnostics_for_file(requested_file);
    assert!(
        collected.len() == 1
            && collected[0].file() == diagnostic_file
            && equal_diagnostics(&collected[0], &diagnostic),
        "get_diagnostics_for_file() returned {collected:?}, want diagnostic for equivalent source file"
    );
}

// Go: ast/positionmap_test.go:11 TestPositionMapASCII
#[test]
fn test_position_map_ascii() {
    let text = "const x = 1;";
    let pm = compute_position_map(text);
    assert!(pm.is_ascii_only(), "expected ASCII-only");
    let mut errors = Vec::new();
    for i in 0..=text.len() as i32 {
        let got = pm.utf8_to_utf16(i);
        if got != i {
            errors.push(format!("UTF8ToUTF16({i}) = {got}, want {i}"));
        }
        let got = pm.utf16_to_utf8(i);
        if got != i {
            errors.push(format!("UTF16ToUTF8({i}) = {got}, want {i}"));
        }
    }
    assert!(errors.is_empty(), "{}", errors.join("\n"));
}

// Go: ast/positionmap_test.go:28 TestPositionMapTwoByte
#[test]
fn test_position_map_two_byte() {
    // "café" — é (U+00E9) is 2 bytes UTF-8, 1 code unit UTF-16
    let text = "const café = 1;\nconst x = 2;";
    let pm = compute_position_map(text);
    assert!(!pm.is_ascii_only(), "expected non-ASCII");
    let mut errors = Vec::new();

    // Everything before é (byte offset 9) should be identity
    for i in 0..10 {
        let got = pm.utf8_to_utf16(i);
        if got != i {
            errors.push(format!("before é: UTF8ToUTF16({i}) = {got}, want {i}"));
        }
    }

    // é starts at UTF-8 byte 9, UTF-16 offset 9: same
    let got = pm.utf8_to_utf16(9);
    if got != 9 {
        errors.push(format!("at é: UTF8ToUTF16(9) = {got}, want 9"));
    }

    // After é (byte 11 in UTF-8 = code unit 10 in UTF-16), delta is 1
    // ' ' after café: UTF-8 byte 11, UTF-16 offset 10
    let got = pm.utf8_to_utf16(11);
    if got != 10 {
        errors.push(format!("after é: UTF8ToUTF16(11) = {got}, want 10"));
    }

    // 'x' on second line: UTF-8 byte 23, UTF-16 offset 22
    let x_utf8 = text.rfind('x').unwrap() as i32;
    let got = pm.utf8_to_utf16(x_utf8);
    if got != x_utf8 - 1 {
        errors.push(format!(
            "at x: UTF8ToUTF16({x_utf8}) = {got}, want {}",
            x_utf8 - 1
        ));
    }

    // Reverse: UTF-16 offset 22 should map to UTF-8 byte 23
    let x_utf16 = x_utf8 - 1;
    let got = pm.utf16_to_utf8(x_utf16);
    if got != x_utf8 {
        errors.push(format!(
            "reverse at x: UTF16ToUTF8({x_utf16}) = {got}, want {x_utf8}"
        ));
    }
    assert!(errors.is_empty(), "{}", errors.join("\n"));
}

// Go: ast/positionmap_test.go:68 TestPositionMapFourByte
#[test]
fn test_position_map_four_byte() {
    // 🎉 (U+1F389) is 4 bytes UTF-8, 2 code units UTF-16
    let text = "const a = \"🎉\";\nconst b = 2;";
    let pm = compute_position_map(text);
    assert!(!pm.is_ascii_only(), "expected non-ASCII");
    let mut errors = Vec::new();

    // 🎉 starts at byte 11 (after `const a = "`)
    // UTF-8: bytes 11-14 (4 bytes), UTF-16: units 11-12 (2 code units)
    // After 🎉: UTF-8 byte 15, UTF-16 offset 13. Delta = 2.

    // 'b' on second line
    let b_utf8 = text.rfind('b').unwrap() as i32;
    let b_utf16 = b_utf8 - 2; // delta of 2 from emoji
    let got = pm.utf8_to_utf16(b_utf8);
    if got != b_utf16 {
        errors.push(format!(
            "at b: UTF8ToUTF16({b_utf8}) = {got}, want {b_utf16}"
        ));
    }
    let got = pm.utf16_to_utf8(b_utf16);
    if got != b_utf8 {
        errors.push(format!(
            "reverse at b: UTF16ToUTF8({b_utf16}) = {got}, want {b_utf8}"
        ));
    }
    assert!(errors.is_empty(), "{}", errors.join("\n"));
}

// Go: ast/positionmap_test.go:92 TestPositionMapMultipleNonASCII
#[test]
fn test_position_map_multiple_non_ascii() {
    // Mix of 2-byte and 4-byte characters
    // "à" (U+00E0) = 2 bytes UTF-8, 1 code unit UTF-16 (delta +1)
    // "🎉" (U+1F389) = 4 bytes UTF-8, 2 code units UTF-16 (delta +2)
    let text = "à🎉x";
    let pm = compute_position_map(text);

    // à: UTF-8 [0,2), UTF-16 [0,1)
    // 🎉: UTF-8 [2,6), UTF-16 [1,3)
    // x: UTF-8 [6,7), UTF-16 [3,4)
    #[rustfmt::skip]
    let tests: &[(i32, i32)] = &[
        (0, 0),
        (2, 1), // start of 🎉
        (6, 3), // x
        (7, 4), // end
    ];
    let mut errors = Vec::new();
    for &(utf8, utf16) in tests {
        let got = pm.utf8_to_utf16(utf8);
        if got != utf16 {
            errors.push(format!("UTF8ToUTF16({utf8}) = {got}, want {utf16}"));
        }
        let got = pm.utf16_to_utf8(utf16);
        if got != utf8 {
            errors.push(format!("UTF16ToUTF8({utf16}) = {got}, want {utf8}"));
        }
    }
    assert!(errors.is_empty(), "{}", errors.join("\n"));
}

// Go: ast/positionmap_test.go:123 TestPositionMapLoneSurrogateSentinel
// PORT: `encode_js_string_rune` writes the port form of the lone surrogate
// (see `scanner_util::GO_STRING_MARKER`), so `text.len()` is its port length.
#[test]
fn test_position_map_lone_surrogate_sentinel() {
    let text = "a".to_string() + &encode_js_string_rune(0xD800) + "b";
    let pm = compute_position_map(&text);
    assert!(!pm.is_ascii_only(), "expected non-ASCII");

    let len = text.len() as i32;
    let mut errors = Vec::new();
    let got = pm.utf8_to_utf16(len);
    if got != 3 {
        errors.push(format!("UTF8ToUTF16({len}) = {got}, want 3"));
    }
    let got = pm.utf16_to_utf8(2);
    if got != len - 1 {
        errors.push(format!("UTF16ToUTF8(2) = {got}, want {}", len - 1));
    }
    assert!(errors.is_empty(), "{}", errors.join("\n"));
}

// Go: ast/positionmap_test.go:122 TestPositionMapRoundtrip
#[test]
fn test_position_map_roundtrip() {
    let text = "let café = \"🎉\"; // naïve";
    let pm = compute_position_map(text);

    // Convert every valid UTF-16 position to UTF-8 and back
    let utf16_len = pm.utf8_to_utf16(text.len() as i32);
    let mut errors = Vec::new();
    for i in 0..=utf16_len {
        let utf8_pos = pm.utf16_to_utf8(i);
        let back = pm.utf8_to_utf16(utf8_pos);
        if back != i {
            errors.push(format!(
                "roundtrip UTF16->UTF8->UTF16: {i} -> {utf8_pos} -> {back}"
            ));
        }
    }
    assert!(errors.is_empty(), "{}", errors.join("\n"));
}
