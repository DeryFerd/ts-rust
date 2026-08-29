use ts_compiler::Program;
use ts_options::{CompilerOptions, ScriptTarget};
use ts_vfs::{FileSystem, MemoryFileSystem};

const SOURCE: &str =
    "type Probe = React.DetailedHTMLProps<React.AudioHTMLAttributes<number>, number>;";

fn check_attribute_override(override_member: &str, exact_optional: bool) -> Program {
    check_attribute_constraint("", override_member, SOURCE, exact_optional)
}

fn check_attribute_constraint(
    base_member: &str,
    override_member: &str,
    source: &str,
    exact_optional: bool,
) -> Program {
    let filesystem = MemoryFileSystem::new(true);
    filesystem
        .write_file(
            "/project/react.d.ts",
            &format!(
                "declare namespace React {{ \
                 type Handler<Value> = {{ bivarianceHack(value: Value): void }}['bivarianceHack']; \
                 interface DOMAttributes<T> {{}} \
                 interface HTMLAttributes<T> extends DOMAttributes<T> {{ id?: string; {base_member} }} \
                 interface HTMLAttributes<T> extends DOMAttributes<T> {{ title?: string; }} \
                 interface MediaHTMLAttributes<T> extends HTMLAttributes<T> {{ src?: string; }} \
                 interface AudioHTMLAttributes<T> extends MediaHTMLAttributes<T> {{ {override_member} }} \
                 interface Attributes {{ key?: string; }} \
                 interface ClassAttributes<T> extends Attributes {{ ref?: T; }} \
                 type DetailedHTMLProps<E extends HTMLAttributes<T>, T> = ClassAttributes<T> & E; \
                 }}",
            ),
        )
        .unwrap();
    filesystem.write_file("/project/case.ts", source).unwrap();
    let (program, replay) = Program::try_new_with_canonical_checker_and_queries(
        &filesystem,
        "/project",
        &["react.d.ts".to_owned(), "case.ts".to_owned()],
        CompilerOptions {
            target: ScriptTarget::Es2015,
            lib: Some(vec!["es2015".to_owned()]),
            skip_lib_check: true,
            exact_optional_property_types: exact_optional,
            no_emit: true,
            ..CompilerOptions::default()
        },
        |_, queries| queries.replay_sources().unwrap(),
    )
    .unwrap();
    assert_eq!(program.diagnostics(), replay.unwrap());
    program
}

#[test]
fn inherited_generic_constraints_check_overrides_with_skip_lib_check() {
    let program = check_attribute_override("id?: number;", false);
    let [diagnostic] = program.diagnostics() else {
        panic!("expected one constraint error: {:?}", program.diagnostics());
    };
    assert_eq!(diagnostic.code, Some(2344));
    assert_eq!(diagnostic.file_name.as_deref(), Some("/project/case.ts"));
    assert!(diagnostic.message.starts_with(
        "Type 'AudioHTMLAttributes<number>' does not satisfy the constraint 'HTMLAttributes<number>'."
    ));
    let span = diagnostic.range.unwrap();
    assert_eq!((span.start.get(), span.end.get()), (37, 70));
}

#[test]
fn inherited_generic_constraints_keep_valid_overrides_and_added_properties() {
    for member in ["", "id?: string;", "id: string;", "volume?: number;"] {
        let program = check_attribute_override(member, false);
        assert!(
            program.diagnostics().is_empty(),
            "{member}: {:?}",
            program.diagnostics()
        );
    }
}

#[test]
fn inherited_generic_constraints_check_each_merged_base_declaration() {
    let program = check_attribute_override("title?: number;", false);
    let [diagnostic] = program.diagnostics() else {
        panic!("expected one constraint error: {:?}", program.diagnostics());
    };
    assert_eq!(diagnostic.code, Some(2344));
    assert_eq!(diagnostic.file_name.as_deref(), Some("/project/case.ts"));
}

#[test]
fn inherited_generic_constraints_keep_optional_property_rules() {
    let loose = check_attribute_override("id: undefined;", false);
    assert!(loose.diagnostics().is_empty(), "{:?}", loose.diagnostics());
    let exact = check_attribute_override("id: undefined;", true);
    assert_eq!(exact.diagnostics().len(), 1);
    assert_eq!(exact.diagnostics()[0].code, Some(2344));
}

#[test]
fn inherited_generic_constraints_substitute_overridden_property_parameters() {
    let program = check_attribute_override("id?: T;", false);
    assert_eq!(program.diagnostics().len(), 1);
    assert_eq!(program.diagnostics()[0].code, Some(2344));
}

#[test]
fn inherited_generic_constraints_keep_member_queries_in_either_order() {
    let read = "declare const audio: React.AudioHTMLAttributes<number>; \
                const id: string | undefined = audio.id;";
    for exact in [false, true] {
        for source in [format!("{SOURCE} {read}"), format!("{read} {SOURCE}")] {
            let program = check_attribute_constraint("", "id?: string;", &source, exact);
            assert!(
                program.diagnostics().is_empty(),
                "{:?}",
                program.diagnostics()
            );
        }
    }
}

#[test]
fn inherited_generic_constraints_check_mapped_method_overrides() {
    for (override_member, expected) in [
        ("run(value: T): string;", None),
        ("run(value: T): number;", Some(2344)),
    ] {
        let program =
            check_attribute_constraint("run(value: T): string;", override_member, SOURCE, false);
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            expected.into_iter().map(Some).collect::<Vec<_>>(),
            "{:?}",
            program.diagnostics()
        );
    }
}

#[test]
fn inherited_generic_constraints_check_mapped_handler_overrides() {
    for exact in [false, true] {
        for (override_member, expected) in [
            ("onChange?: Handler<T>;", None),
            ("onChange?: Handler<string>;", Some(2344)),
        ] {
            let program = check_attribute_constraint(
                "onChange?: Handler<T>;",
                override_member,
                SOURCE,
                exact,
            );
            assert_eq!(
                program
                    .diagnostics()
                    .iter()
                    .map(|diagnostic| diagnostic.code)
                    .collect::<Vec<_>>(),
                expected.into_iter().map(Some).collect::<Vec<_>>(),
                "{:?}",
                program.diagnostics()
            );
        }
    }
}

#[test]
fn inherited_generic_constraints_do_not_demand_source_types_for_unknown_targets() {
    let deep = format!("T{}", "[]".repeat(101));
    for (marker, expected) in [("", None), ("?", Some(2344))] {
        let program = check_attribute_constraint(
            "payload: unknown;",
            &format!("payload{marker}: {deep};"),
            SOURCE,
            false,
        );
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            expected.into_iter().map(Some).collect::<Vec<_>>(),
            "{:?}",
            program.diagnostics()
        );
    }
}

#[test]
fn ordinary_generic_constraints_keep_fixed_type_arguments() {
    for (argument, expected) in [("string", None), ("number", Some(2344))] {
        let filesystem = MemoryFileSystem::new(true);
        filesystem
            .write_file(
                "/project/types.d.ts",
                "interface Base<Value> { value: Value; } \
                 interface Derived<Value> extends Base<Value> {} \
                 type Require<Actual extends Base<string>> = Actual;",
            )
            .unwrap();
        let source = format!("type Result = Require<Derived<{argument}>>;");
        filesystem.write_file("/project/case.ts", &source).unwrap();
        let (program, replay) = Program::try_new_with_canonical_checker_and_queries(
            &filesystem,
            "/project",
            &["types.d.ts".to_owned(), "case.ts".to_owned()],
            CompilerOptions {
                target: ScriptTarget::Es2015,
                lib: Some(vec!["es2015".to_owned()]),
                skip_lib_check: true,
                no_emit: true,
                ..CompilerOptions::default()
            },
            |_, queries| queries.replay_sources().unwrap(),
        )
        .unwrap();
        assert_eq!(program.diagnostics(), replay.unwrap());
        assert_eq!(
            program
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            expected.into_iter().map(Some).collect::<Vec<_>>()
        );
        if expected.is_some() {
            let diagnostic = &program.diagnostics()[0];
            assert!(diagnostic.message.starts_with(
                "Type 'Derived<number>' does not satisfy the constraint 'Base<string>'."
            ));
            let start = source.find("Derived<number>").unwrap() as u32;
            let span = diagnostic.range.unwrap();
            assert_eq!((span.start.get(), span.end.get()), (start, start + 15));
        }
    }
}

#[test]
fn ordinary_generic_constraints_compare_substituted_properties() {
    for (member, bound, argument, expected) in [
        ("value: Value;", "string | number", "string", None),
        ("value: string;", "number", "string", None),
        ("value: Value;", "string", "number", Some(2344)),
    ] {
        for source_type in ["Base", "Derived"] {
            let filesystem = MemoryFileSystem::new(true);
            filesystem
                .write_file(
                    "/project/types.d.ts",
                    &format!(
                        "interface Base<Value> {{ {member} }} \
                         interface Derived<Value> extends Base<Value> {{}} \
                         type Require<Actual extends Base<{bound}>> = Actual;"
                    ),
                )
                .unwrap();
            filesystem
                .write_file(
                    "/project/case.ts",
                    &format!("type Result = Require<{source_type}<{argument}>>;"),
                )
                .unwrap();
            let (program, replay) = Program::try_new_with_canonical_checker_and_queries(
                &filesystem,
                "/project",
                &["types.d.ts".to_owned(), "case.ts".to_owned()],
                CompilerOptions {
                    target: ScriptTarget::Es2015,
                    lib: Some(vec!["es2015".to_owned()]),
                    skip_lib_check: true,
                    no_emit: true,
                    ..CompilerOptions::default()
                },
                |_, queries| queries.replay_sources().unwrap(),
            )
            .unwrap();
            assert_eq!(program.diagnostics(), replay.unwrap());
            assert_eq!(
                program
                    .diagnostics()
                    .iter()
                    .map(|diagnostic| diagnostic.code)
                    .collect::<Vec<_>>(),
                expected.into_iter().map(Some).collect::<Vec<_>>(),
                "{member} {source_type}<{argument}> -> Base<{bound}>"
            );
        }
    }
}

#[test]
fn inherited_generic_constraints_reuse_types_before_and_after_declaration_checks() {
    use ts_ast::{FileId, NodeData, NodeRef};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_checker::semantic::{CanonicalCheckerContext, CanonicalCheckerOptions};
    use ts_parser::parse_source_file;

    const FILE: FileId = FileId::new(5_185);
    for (base, derived) in [
        ("id?: string;", "id?: string;"),
        ("run(value: T): string;", "run(value: U): string;"),
        ("onChange?: Handler<T>;", "onChange?: Handler<U>;"),
    ] {
        for early in [false, true] {
            let parsed = parse_source_file(&format!(
                "interface Array<T> {{}} interface ReadonlyArray<T> {{}} \
                 type Handler<Value> = {{ bivarianceHack(value: Value): void }}['bivarianceHack']; \
                 interface Base<T> {{ {base} }} \
                 interface Derived<U> extends Base<U> {{ {derived} }} \
                 type Require<Actual extends Base<number>> = Actual; \
                 type Result = Require<Derived<number>>;"
            ));
            assert!(parsed.diagnostics.is_empty());
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    FILE,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/inherited-constraints.ts\""),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, FILE)
                .unwrap();
            let mut context = CanonicalCheckerContext::new(
                binder.finish(),
                vec![(FILE, &parsed.arena)],
                CanonicalCheckerOptions::default(),
            )
            .unwrap();
            let annotation = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                        return None;
                    };
                    (name.text == "Result").then_some(NodeRef::new(
                        parsed.arena.id(),
                        FILE,
                        alias.type_,
                    ))
                })
                .unwrap();
            let first = early.then(|| context.get_type_from_type_node(annotation).unwrap());
            context.check_source_file(FILE).unwrap();
            let result = context.get_type_from_type_node(annotation).unwrap();
            assert!(first.is_none_or(|first| first == result));
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
            let counts = |context: &CanonicalCheckerContext<'_>| {
                let store = context.store();
                (
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                )
            };
            let warm = counts(&context);
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(context.get_type_from_type_node(annotation).unwrap(), result);
            assert_eq!(counts(&context), warm);
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
        }
    }
}

#[test]
fn inherited_this_constraints_remain_unavailable_on_repeated_queries() {
    use ts_ast::{FileId, NodeData, NodeRef};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_checker::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, DeclaredTypeError, TypeNodeUnavailable,
    };
    use ts_parser::parse_source_file;

    const FILE: FileId = FileId::new(5_186);
    for base in [
        "interface Base<T> { run: (value: this) => void; }",
        "interface Base<T> { label?: string; } \
         interface Base<T> { run: (value: this) => void; }",
    ] {
        for strict_function_types in [false, true] {
            let parsed = parse_source_file(&format!(
                "interface Array<T> {{}} interface ReadonlyArray<T> {{}} \
                 {base} interface Derived<U> extends Base<U> {{ extra: U; }} \
                 type Require<Actual extends Base<number>> = Actual; \
                 type Result = Require<Derived<number>>;"
            ));
            assert!(parsed.diagnostics.is_empty());
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    FILE,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/inherited-this.ts\""),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, FILE)
                .unwrap();
            let mut context = CanonicalCheckerContext::new(
                binder.finish(),
                vec![(FILE, &parsed.arena)],
                CanonicalCheckerOptions {
                    strict_function_types,
                    ..CanonicalCheckerOptions::default()
                },
            )
            .unwrap();
            let annotation = parsed
                .arena
                .iter()
                .find_map(|(_, record)| {
                    let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &parsed.arena.get(alias.name)?.data else {
                        return None;
                    };
                    (name.text == "Result").then_some(NodeRef::new(
                        parsed.arena.id(),
                        FILE,
                        alias.type_,
                    ))
                })
                .unwrap();
            let error = context.get_type_from_type_node(annotation).unwrap_err();
            assert!(
                matches!(
                    error,
                    DeclaredTypeError::TypeNodeUnavailable(
                        TypeNodeUnavailable::GenericReferenceUnsupported { .. }
                    )
                ),
                "{error:?}"
            );
            let counts = |context: &CanonicalCheckerContext<'_>| {
                let store = context.store();
                (
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                )
            };
            let warm = counts(&context);
            for _ in 0..2 {
                assert_eq!(context.get_type_from_type_node(annotation), Err(error));
                assert_eq!(counts(&context), warm);
                assert!(context.diagnostics().is_empty());
            }
        }
    }
}
