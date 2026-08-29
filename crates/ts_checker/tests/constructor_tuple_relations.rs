use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeId,
    signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(4_420);
const ARRAYS: &str = concat!(
    "interface Array<T> { length: number; } ",
    "interface ReadonlyArray<T> { readonly length: number; } ",
);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/constructor-tuples.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: true,
            },
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn alias_type(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult, name: &str) -> TypeId {
    let declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::TypeAliasDeclaration(alias) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(alias.name)?.data else {
                return None;
            };
            (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap_or_else(|| panic!("missing alias {name}"));
    let owner = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    let owner = context.store().get_merged_symbol(owner).unwrap();
    context
        .store()
        .type_alias_links(owner)
        .and_then(|links| links.declared_type)
        .unwrap_or_else(|| panic!("unresolved alias {name}"))
}

fn assert_relations(source: &str, cases: &[(&str, &str, bool)]) {
    assert_relations_and_comparisons(source, cases, &[]);
}

fn assert_relations_and_comparisons(
    source: &str,
    assignments: &[(&str, &str, bool)],
    comparisons: &[(&str, &str, bool)],
) {
    let parsed = parse_source_file(&format!("{ARRAYS}{source}"));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(context.diagnostics().is_empty());
    let cases = assignments
        .iter()
        .map(|case| (case, false))
        .chain(comparisons.iter().map(|case| (case, true)))
        .map(|(&(source, target, expected), comparable)| {
            (
                source,
                target,
                alias_type(&context, &parsed, source),
                alias_type(&context, &parsed, target),
                expected,
                comparable,
            )
        })
        .collect::<Vec<_>>();
    for &(source, target, source_type, target_type, expected, comparable) in &cases {
        let result = if comparable {
            context.is_type_comparable_to(source_type, target_type)
        } else {
            context.is_type_assignable_to(source_type, target_type)
        };
        assert_eq!(
            result,
            Ok(expected),
            "{source} -> {target}, comparable={comparable}",
        );
    }
    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
    );
    context.recheck_source_file(FILE).unwrap();
    for &(source, target, source_type, target_type, expected, comparable) in &cases {
        assert_eq!(alias_type(&context, &parsed, source), source_type);
        assert_eq!(alias_type(&context, &parsed, target), target_type);
        let result = if comparable {
            context.is_type_comparable_to(source_type, target_type)
        } else {
            context.is_type_assignable_to(source_type, target_type)
        };
        assert_eq!(
            result,
            Ok(expected),
            "warm {source} -> {target}, comparable={comparable}",
        );
    }
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
        ),
        warm,
    );
    assert!(context.diagnostics().is_empty());
}

#[test]
fn required_constructor_tuple_reports_assignment_error_without_changing_signature_metadata() {
    let parsed = parse_source_file(concat!(
        "declare const one: new (...args: [string]) => string; ",
        "const bad: new () => string = one;",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| diagnostic.diagnostic.code())
            .collect::<Vec<_>>(),
        [2322],
    );
    let constructor = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ConstructorTypeNode(constructor) = &record.data else {
                return None;
            };
            (!constructor.parameters.nodes.is_empty()).then_some(NodeRef::new(
                parsed.arena.id(),
                FILE,
                node,
            ))
        })
        .unwrap();
    let signature = context
        .store()
        .signature_links(constructor)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.parameters().len(), 1);
    assert_eq!(record.min_argument_count(), 0);
    assert!(record.flags().contains(SignatureFlags::HAS_REST_PARAMETER));
    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(
        context
            .store()
            .signature_links(constructor)
            .and_then(|links| links.resolved_signature.signature()),
        Some(signature),
    );
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn constructor_tuple_arity_uses_required_optional_and_void_positions() {
    assert_relations(
        concat!(
            "type Empty = new () => string; ",
            "type EmptyTuple = new (...args: []) => string; ",
            "type Required = new (...args: [string]) => string; ",
            "type Optional = new (...args: [string?]) => string; ",
            "type OptionalTail = new (...args: [string, number?]) => string; ",
            "type Two = new (...args: [string, number]) => string; ",
            "type Prefix = new (value: string, ...args: [number]) => string; ",
            "type Ordinary = new (value: string, count: number) => string; ",
            "type VoidTuple = new (...args: [void]) => string; ",
            "type VoidOrdinary = new (value: void) => string;",
        ),
        &[
            ("EmptyTuple", "Empty", true),
            ("Empty", "EmptyTuple", true),
            ("Required", "Empty", false),
            ("Empty", "Required", true),
            ("Optional", "Empty", true),
            ("Required", "Optional", false),
            ("Optional", "Required", true),
            ("OptionalTail", "Required", true),
            ("Two", "Required", false),
            ("Prefix", "Required", false),
            ("Prefix", "Ordinary", true),
            ("Ordinary", "Two", true),
            ("VoidTuple", "Empty", true),
            ("VoidOrdinary", "Empty", true),
        ],
    );
}

#[test]
fn constructor_tuple_parameter_types_are_contravariant() {
    assert_relations(
        concat!(
            "type Text = new (...args: [string]) => string; ",
            "type Numeric = new (...args: [number]) => string; ",
            "type Literal = new (...args: ['value']) => string; ",
            "type Pair = new (...args: [string, number]) => string; ",
            "type WrongPair = new (value: string, flag: boolean) => string; ",
            "type Rest = new (...args: [string, ...number[]]) => string; ",
            "type WrongRest = new (...args: [string, ...boolean[]]) => string;",
        ),
        &[
            ("Text", "Numeric", false),
            ("Numeric", "Text", false),
            ("Text", "Literal", true),
            ("Literal", "Text", false),
            ("Pair", "WrongPair", false),
            ("Rest", "Pair", true),
            ("Rest", "Text", true),
            ("Rest", "WrongPair", false),
            ("Rest", "WrongRest", false),
        ],
    );
}

#[test]
fn constructor_variable_tuple_relations_keep_required_suffix_types() {
    assert_relations(
        concat!(
            "type Suffix = new (...args: [...string[], number]) => string; ",
            "type Pair = new (value: string, count: number) => string; ",
            "type Numeric = new (count: number) => string; ",
            "type Text = new (value: string) => string; ",
            "type WrongPair = new (value: string, flag: boolean) => string; ",
            "type WrongSuffix = new (...args: [...string[], boolean]) => string; ",
            "type SameSuffix = new (...args: [...string[], number]) => string; ",
            "type AnyRest = new (...args: any[]) => string;",
        ),
        &[
            ("Suffix", "Text", false),
            ("Suffix", "Numeric", true),
            ("Suffix", "Pair", true),
            ("Suffix", "WrongPair", false),
            ("Suffix", "WrongSuffix", false),
            ("Suffix", "SameSuffix", true),
            ("Pair", "Suffix", false),
            ("Suffix", "AnyRest", true),
            ("AnyRest", "Suffix", true),
        ],
    );
}

#[test]
fn constructor_top_signatures_accept_tuple_tails_before_parameter_comparison() {
    assert_relations(
        concat!(
            "type Suffix = new (...args: [...string[], number]) => string; ",
            "type TupleUnion = new (...args: [string] | [number]) => string; ",
            "type Pair = new (value: string, count: number) => string; ",
            "type NeverUnknown = new (...args: never[]) => unknown; ",
            "type NeverAny = new (...args: never[]) => any; ",
            "type AnyUnknown = new (...args: any[]) => unknown; ",
            "type AnyAny = new (...args: any[]) => any; ",
            "type NeverString = new (...args: never[]) => string; ",
            "type NeverVoid = new (...args: never[]) => void; ",
            "type NumberUnknown = new (...args: number[]) => unknown; ",
            "type FixedNever = new (value: never) => unknown; ",
            "type TupleNever = new (...args: [never?]) => unknown; ",
            "type EmptyString = new () => string; ",
            "declare const suffix: Suffix; ",
            "declare const tupleUnion: TupleUnion; ",
            "const acceptsNeverUnknown: NeverUnknown = suffix; ",
            "const acceptsNeverAny: NeverAny = tupleUnion;",
        ),
        &[
            ("Suffix", "NeverUnknown", true),
            ("Suffix", "NeverAny", true),
            ("Suffix", "AnyUnknown", true),
            ("Suffix", "AnyAny", true),
            ("TupleUnion", "NeverUnknown", true),
            ("TupleUnion", "NeverAny", true),
            ("TupleUnion", "AnyUnknown", true),
            ("TupleUnion", "AnyAny", true),
            ("Suffix", "NeverString", false),
            ("Suffix", "NeverVoid", false),
            ("Suffix", "NumberUnknown", false),
            ("Pair", "FixedNever", false),
            ("Pair", "TupleNever", false),
            ("NeverUnknown", "EmptyString", false),
            ("AnyAny", "EmptyString", true),
        ],
    );
}

#[test]
fn constructor_tuple_unions_are_comparable_when_one_case_matches() {
    assert_relations_and_comparisons(
        concat!(
            "type Left = new (...args: [string] | [number]) => string; ",
            "type Right = new (...args: [string] | [boolean]) => string; ",
            "type BooleanOnly = new (...args: [boolean]) => string; ",
            "type WrongReturn = new (...args: [string] | [boolean]) => number;",
        ),
        &[("Left", "Right", false), ("Right", "Left", false)],
        &[
            ("Left", "Right", true),
            ("Right", "Left", true),
            ("Left", "BooleanOnly", false),
            ("BooleanOnly", "Left", false),
            ("Left", "WrongReturn", false),
        ],
    );
}

#[test]
fn constructor_tuple_unions_cover_discriminants_without_losing_correlations() {
    assert_relations(
        concat!(
            "type Either = new (...args: [true] | [false]) => string; ",
            "type OptionalEither = new (...args: [true?] | [false?]) => string; ",
            "type BooleanArgument = new (value: boolean) => string; ",
            "type BooleanOrUndefined = new (value: boolean | undefined) => string; ",
            "type Broad = new (value: string | number) => string; ",
            "type Separate = new (...args: [string] | [number]) => string; ",
            "type Pair = new (key: boolean, value: string | number) => string; ",
            "type Correlated = new (...args: [true, string] | [false, number]) => string; ",
            "type Complete = new (...args: [true, string | number] | [false, string | number]) => string; ",
            "type BooleanPair = new (first: boolean, second: boolean) => string; ",
            "type BooleanCases = new (...args: [true, true] | [true, false] | [false, true] | [false, false]) => string; ",
            "type EqualBooleans = new (...args: [true, true] | [false, false]) => string; ",
            "declare const either: Either; const acceptsBoolean: BooleanArgument = either;",
        ),
        &[
            ("Either", "BooleanArgument", true),
            ("OptionalEither", "BooleanArgument", true),
            ("OptionalEither", "BooleanOrUndefined", false),
            ("Separate", "Broad", false),
            ("Correlated", "Pair", false),
            ("Complete", "Pair", true),
            ("BooleanCases", "BooleanPair", true),
            ("EqualBooleans", "BooleanPair", false),
        ],
    );
}

#[test]
fn constructor_tuple_union_tails_normalize_optional_prefixes() {
    assert_relations(
        concat!(
            "type OptionalPrefix = new (value?: string, ...args: [number] | [boolean]) => string; ",
            "type Expanded = new (...args: [string | undefined, number] | [string | undefined, boolean]) => string; ",
            "type WrongPrefix = new (value?: number, ...args: [number] | [boolean]) => string; ",
            "declare const source: OptionalPrefix; const expanded: Expanded = source;",
        ),
        &[
            ("OptionalPrefix", "Expanded", true),
            ("Expanded", "OptionalPrefix", true),
            ("WrongPrefix", "Expanded", false),
        ],
    );
}
