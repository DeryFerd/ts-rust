use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    AwaitedTypeError, CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
    TypeData, TypeId, types::TypeFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(3);
const LIBRARIES: [(&str, &str); 3] = [
    ("es5", include_str!("../../ts_bundled/libs/lib.es5.d.ts")),
    (
        "decorators",
        include_str!("../../ts_bundled/libs/lib.decorators.d.ts"),
    ),
    (
        "decorators.legacy",
        include_str!("../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
    ),
];

struct Fixture {
    source: ParseResult,
    libraries: Vec<ParseResult>,
}

impl Fixture {
    fn new(source: &str) -> Self {
        Self {
            source: parse_source_file(source),
            libraries: LIBRARIES
                .iter()
                .map(|(_, text)| parse_source_file(text))
                .collect(),
        }
    }

    fn context(&self) -> CanonicalCheckerContext<'_> {
        let files = self
            .libraries
            .iter()
            .enumerate()
            .map(|(index, parsed)| {
                (
                    FileId::new(u32::try_from(index).unwrap()),
                    parsed,
                    format!("\"/__typescript/lib/lib.{}.d.ts\"", LIBRARIES[index].0),
                    true,
                )
            })
            .chain([(
                FILE,
                &self.source,
                "\"/project/awaited-types.ts\"".to_owned(),
                false,
            )])
            .collect::<Vec<_>>();
        let mut binder = CanonicalBinder::new();
        for (file, parsed, path, library) in &files {
            assert!(
                parsed.diagnostics.is_empty(),
                "{path}: {:?}",
                parsed.diagnostics
            );
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    *file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        *library,
                        *library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for (file, parsed, _, _) in &files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, *file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed, _, _)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                strict_function_types: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn annotation(&self, expected: &str) -> NodeRef {
        self.source
            .arena
            .iter()
            .find_map(|(_, record)| {
                let (name, annotation) = match &record.data {
                    NodeData::VariableDeclaration(data) => (data.name, data.type_?),
                    NodeData::PropertyDeclaration(data) => (data.name, data.type_?),
                    _ => return None,
                };
                let NodeData::Identifier(name) = &self.source.arena.get(name)?.data else {
                    return None;
                };
                (name.text == expected)
                    .then_some(NodeRef::new(self.source.arena.id(), FILE, annotation))
            })
            .unwrap_or_else(|| panic!("missing annotation for {expected}"))
    }

    fn type_of(&self, context: &mut CanonicalCheckerContext<'_>, name: &str) -> TypeId {
        context
            .get_type_from_type_node(self.annotation(name))
            .unwrap()
    }
}

fn named_symbol(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    kind: SyntaxKind,
    expected: &str,
) -> SemanticSymbolId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            if record.kind != kind {
                return None;
            }
            let name = match &record.data {
                NodeData::ClassDeclaration(data) => data.name?,
                NodeData::InterfaceDeclaration(data) => data.name,
                NodeData::TypeParameterDeclaration(data) => data.name,
                _ => return None,
            };
            let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (name.text == expected).then_some(NodeRef::new(parsed.arena.id(), file, id))
        })
        .unwrap_or_else(|| panic!("missing {kind:?} {expected}"));
    let raw = context.file(file).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    cases: &[(TypeId, Result<TypeId, AwaitedTypeError>)],
) {
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            [
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.type_alias_len(),
            ],
            store.relation_state_snapshot(),
            context.diagnostics().clone(),
        )
    };
    for (input, expected) in cases {
        assert_eq!(&context.get_awaited_type_no_alias(*input), expected);
    }
    let warm = snapshot(context);
    for _ in 0..2 {
        for (input, expected) in cases {
            assert_eq!(&context.get_awaited_type_no_alias(*input), expected);
        }
        assert_eq!(snapshot(context), warm);
    }
    assert!(context.diagnostics().is_empty());
}

#[test]
fn awaited_native_promises_keep_named_class_and_union_identities() {
    let fixture = Fixture::new(concat!(
        "class Reply { value!: string; }\n",
        "interface Plain { value: number; }\n",
        "interface NonCallableThen { then: number; }\n",
        "declare const reply: Reply;\n",
        "declare const promised: Promise<Reply>;\n",
        "declare const nested: Promise<Promise<Reply>>;\n",
        "declare const plain: Plain;\n",
        "declare const nonCallableThen: NonCallableThen;\n",
        "declare const branded: \"brand\" & { then: (done: (value: number) => void) => void };\n",
        "declare const mixed: Promise<Reply> | Promise<number> | undefined;\n",
        "declare const expected: Reply | number | undefined;\n",
    ));
    let mut context = fixture.context();
    let reply = fixture.type_of(&mut context, "reply");
    let promised = fixture.type_of(&mut context, "promised");
    let nested = fixture.type_of(&mut context, "nested");
    let plain = fixture.type_of(&mut context, "plain");
    let non_callable = fixture.type_of(&mut context, "nonCallableThen");
    let branded = fixture.type_of(&mut context, "branded");
    let mixed = fixture.type_of(&mut context, "mixed");
    let expected = fixture.type_of(&mut context, "expected");
    let reply_symbol = named_symbol(
        &context,
        &fixture.source,
        FILE,
        SyntaxKind::ClassDeclaration,
        "Reply",
    );
    assert_eq!(
        context.store().type_payload(reply).unwrap().symbol(),
        Some(reply_symbol)
    );
    assert!(matches!(
        context.store().type_payload(branded).unwrap().data(),
        TypeData::Intersection(_)
    ));
    let promise_symbol = named_symbol(
        &context,
        &fixture.libraries[0],
        FileId::new(0),
        SyntaxKind::InterfaceDeclaration,
        "Promise",
    );
    let promise_target = context.get_declared_type_of_symbol(promise_symbol).unwrap();
    let TypeData::TypeReference(reference) =
        context.store().type_payload(promised).unwrap().data()
    else {
        panic!("the annotation must use the real library Promise target")
    };
    assert_eq!(reference.object.target, Some(promise_target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[reply][..])
    );
    let (any, unknown, never) = {
        let types = context.store().intrinsic_bootstrap().unwrap();
        (types.any_type, types.unknown_type, types.never_type)
    };
    assert_replay(
        &mut context,
        &[
            (any, Ok(any)),
            (unknown, Ok(unknown)),
            (never, Ok(never)),
            (promised, Ok(reply)),
            (nested, Ok(reply)),
            (plain, Ok(plain)),
            (non_callable, Ok(non_callable)),
            (branded, Ok(branded)),
            (mixed, Ok(expected)),
        ],
    );
}

#[test]
fn awaited_custom_thenables_keep_callback_types_and_native_failures() {
    let fixture = Fixture::new(concat!(
        "class Reply { value!: string; }\n",
        "interface Custom { then(done: (value: Promise<Reply>) => void): void; }\n",
        "interface ReplyCallback { (value: Reply): void; }\n",
        "interface Named { then(done: ReplyCallback): void; }\n",
        "interface Invalid { then(done: number): void; }\n",
        "interface BadThis { then(this: number, done: (value: Reply) => void): void; }\n",
        "interface Cycle { then(done: (value: Cycle) => void): void; }\n",
        "interface CallbackUnion {\n",
        "  then(done: ((value: number) => void) | ((value: string) => void)): void;\n",
        "}\n",
        "interface MixedArity { then(done: (() => void) | ((value: number) => void)): void; }\n",
        "declare const reply: Reply;\n",
        "declare const custom: Custom;\n",
        "declare const named: Named;\n",
        "declare const invalid: Invalid;\n",
        "declare const badThis: BadThis;\n",
        "declare const cycle: Cycle;\n",
        "declare const callbackUnion: CallbackUnion;\n",
        "declare const mixedArity: MixedArity;\n",
    ));
    let mut context = fixture.context();
    let reply = fixture.type_of(&mut context, "reply");
    let custom = fixture.type_of(&mut context, "custom");
    let named = fixture.type_of(&mut context, "named");
    let invalid = fixture.type_of(&mut context, "invalid");
    let bad_this = fixture.type_of(&mut context, "badThis");
    let cycle = fixture.type_of(&mut context, "cycle");
    let callback_union = fixture.type_of(&mut context, "callbackUnion");
    let mixed_arity = fixture.type_of(&mut context, "mixedArity");
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let never = context.store().intrinsic_bootstrap().unwrap().never_type;
    assert_replay(
        &mut context,
        &[
            (
                invalid,
                Err(AwaitedTypeError::InvalidThenable {
                    type_: invalid,
                    this_type: None,
                }),
            ),
            (
                bad_this,
                Err(AwaitedTypeError::InvalidThenable {
                    type_: bad_this,
                    this_type: Some(number),
                }),
            ),
            (cycle, Err(AwaitedTypeError::CircularThenable(cycle))),
            (custom, Ok(reply)),
            (named, Ok(reply)),
            (callback_union, Ok(never)),
            (mixed_arity, Ok(number)),
        ],
    );
}

#[test]
fn awaited_no_alias_preserves_source_formals_without_creating_wrappers() {
    let fixture = Fixture::new("class Holder<T> { value!: T; promised!: Promise<T>; }");
    let mut context = fixture.context();
    let symbol = named_symbol(
        &context,
        &fixture.source,
        FILE,
        SyntaxKind::TypeParameter,
        "T",
    );
    let formal = context.get_declared_type_of_symbol(symbol).unwrap();
    let value = fixture.type_of(&mut context, "value");
    let promised = fixture.type_of(&mut context, "promised");
    assert_eq!(value, formal);
    let record = context.store().type_payload(formal).unwrap();
    assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
    assert_eq!(record.symbol(), Some(symbol));
    let before = context.store().type_alias_len();
    assert_replay(&mut context, &[(formal, Ok(formal)), (promised, Ok(formal))]);
    assert_eq!(context.store().type_alias_len(), before);
    assert_eq!(fixture.type_of(&mut context, "value"), formal);
    assert_eq!(fixture.type_of(&mut context, "promised"), promised);
}
