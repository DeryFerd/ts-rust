//! Synchronous iterator type checks from the pinned checker.
//!
//! Source providers own lazy member resolution and its cache validation. This
//! module consumes their properties and the existing callable projections.
//! Iterator diagnostics remain local until the complete query succeeds.

use ts_ast::NodeRef;
use ts_binder::{EscapedName, EscapedNameRef};

use super::{
    CanonicalCheckerOptions, CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost,
    RelationUnavailable, TypeId,
    bootstrap::UnionReduction,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set},
    callables::ValidatedSingleCallable,
    global_types::{optional_global_type_has_arity, resolve_optional_global_type},
    reference_types::validate_direct_generic_reference,
    relater::ResolvedOwnProperty,
    signatures::ElementFlags,
    source::{SourceCheckError, UnsupportedSourceSyntax},
    type_records::TypeData,
    types::{ObjectFlags, TypeFlags},
};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct IterationTypes {
    pub(super) yield_type: Option<TypeId>,
    pub(super) return_type: Option<TypeId>,
    pub(super) next_type: Option<TypeId>,
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, IntrinsicBootstrapOptions, production::GlobalMergeCompletion,
    };

    fn parsed(text: &str) -> ParseResult {
        let result = parse_source_file(text);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        result
    }

    fn standard_library() -> Vec<ParseResult> {
        [
            include_str!("../../../ts_bundled/libs/lib.es6.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.es2015.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.es5.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.decorators.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.decorators.legacy.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.es2015.core.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.es2015.collection.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.es2015.symbol.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.es2015.symbol.wellknown.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.es2015.iterable.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.es2015.generator.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.es2015.promise.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.es2015.proxy.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.es2015.reflect.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.es2018.asynciterable.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.dom.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.dom.iterable.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.webworker.importscripts.d.ts"),
            include_str!("../../../ts_bundled/libs/lib.scripthost.d.ts"),
        ]
        .into_iter()
        .map(parsed)
        .collect()
    }

    fn context<'arena>(
        files: &[(FileId, &'arena ParseResult)],
        default_library_files: usize,
        options: CanonicalCheckerOptions,
    ) -> CanonicalCheckerContext<'arena> {
        let mut binder = CanonicalBinder::new();
        for (index, &(file, source)) in files.iter().enumerate() {
            let library = index < default_library_files;
            binder
                .bind_source_file_with_facts(
                    &source.arena,
                    source.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        library,
                        library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for &(file, source) in files {
            binder
                .bind_typescript_declaration_slice(&source.arena, file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            files
                .iter()
                .map(|(file, source)| (*file, &source.arena))
                .collect(),
            options,
        )
        .unwrap()
    }

    fn annotation(source: &ParseResult, file: FileId, name: &str) -> NodeRef {
        source
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::VariableDeclaration(variable) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &source.arena.get(variable.name)?.data
                else {
                    return None;
                };
                (identifier.text == name)
                    .then(|| NodeRef::new(source.arena.id(), file, variable.type_.unwrap()))
            })
            .unwrap()
    }

    struct NoProperties;

    impl IterationPropertyResolver for NoProperties {
        fn iterator_key(
            &mut self,
            _store: &mut CanonicalTypeMapperStore,
        ) -> Result<EscapedName, SourceCheckError> {
            panic!("a global iterator reference does not look up its iterator method")
        }

        fn property(
            &mut self,
            _store: &mut CanonicalTypeMapperStore,
            receiver: TypeId,
            _name: EscapedNameRef<'_>,
        ) -> Result<Option<ResolvedOwnProperty>, SourceCheckError> {
            Err(RelationUnavailable::UnsupportedStructuredType(receiver).into())
        }
    }

    struct StoredProperties;

    impl IterationPropertyResolver for StoredProperties {
        fn iterator_key(
            &mut self,
            _store: &mut CanonicalTypeMapperStore,
        ) -> Result<EscapedName, SourceCheckError> {
            panic!("iterator-result tests do not look up the iterator method")
        }

        fn property(
            &mut self,
            store: &mut CanonicalTypeMapperStore,
            receiver: TypeId,
            name: EscapedNameRef<'_>,
        ) -> Result<Option<ResolvedOwnProperty>, SourceCheckError> {
            let name = name
                .as_utf8()
                .ok_or(RelationUnavailable::UnsupportedStructuredType(receiver))?;
            store
                .resolved_own_property(receiver, name)
                .map_err(Into::into)
        }
    }

    #[test]
    fn real_library_iterable_references_keep_yield_return_and_next_types() {
        let library = standard_library();
        let source = parsed(concat!(
            "declare var iterable: Iterable<number, string, undefined>; ",
            "declare var iterator: Iterator<number, string, undefined>; ",
            "declare var array: ArrayIterator<number>; ",
            "declare var generator: Generator<number, string, undefined>;",
        ));
        let source_file = FileId::new(22_099);
        let mut files = library
            .iter()
            .enumerate()
            .map(|(index, file)| (FileId::new(22_000 + u32::try_from(index).unwrap()), file))
            .collect::<Vec<_>>();
        files.push((source_file, &source));
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_builtin_iterator_return: true,
            ..CanonicalCheckerOptions::default()
        };
        let mut context = context(&files, library.len(), options);
        let globals = context.global_types().clone();
        let inputs = ["iterable", "iterator", "array", "generator"].map(|name| {
            context
                .get_type_from_type_node(annotation(&source, source_file, name))
                .unwrap()
        });
        let bound = files
            .iter()
            .map(|(file, _)| context.file(*file).unwrap().1.clone())
            .collect::<Vec<_>>();
        let host = DeclaredTypeHost::new_after_global_merge(
            files
                .iter()
                .zip(&bound)
                .map(|((_, file), bound)| (&file.arena, bound)),
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let node = annotation(&source, source_file, "iterable");
        let store = context.store_mut_for_test();
        let iteration_globals = SynchronousIterationGlobals::resolve(store, &host, node).unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (number, string, undefined, unknown) = (
            bootstrap.number_type,
            bootstrap.string_type,
            bootstrap.undefined_type,
            bootstrap.unknown_type,
        );
        let expected = IterationTypes {
            yield_type: Some(number),
            return_type: Some(string),
            next_type: Some(undefined),
        };
        let before = (store.type_len(), store.mapper_len(), store.signature_len());
        for _ in 0..2 {
            let mut query = SynchronousIterationQuery::new(
                store,
                &globals,
                &iteration_globals,
                options,
                node,
                NoProperties,
            );
            for input in [inputs[0], inputs[3]] {
                let checked = query
                    .check(
                        input,
                        undefined,
                        SynchronousIterationUse::Destructuring,
                        false,
                    )
                    .unwrap();
                assert_eq!(checked.types, expected);
                assert!(checked.diagnostics.is_empty());
            }
            assert_eq!(query.iterator(inputs[1], true).unwrap().types, expected);
            assert_eq!(
                query.iterable(inputs[2], true).unwrap().types,
                IterationTypes {
                    yield_type: Some(number),
                    return_type: Some(undefined),
                    next_type: Some(unknown),
                }
            );
        }
        assert_eq!(
            (store.type_len(), store.mapper_len(), store.signature_len()),
            before
        );
    }

    #[test]
    fn real_library_next_input_is_checked_for_each_synchronous_use() {
        let library = standard_library();
        let source = parsed("declare var iterable: Iterable<string, void, number>;");
        let source_file = FileId::new(22_199);
        let mut files = library
            .iter()
            .enumerate()
            .map(|(index, file)| (FileId::new(22_100 + u32::try_from(index).unwrap()), file))
            .collect::<Vec<_>>();
        files.push((source_file, &source));
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        };
        let mut context = context(&files, library.len(), options);
        let node = annotation(&source, source_file, "iterable");
        let input = context.get_type_from_type_node(node).unwrap();
        let global_types = context.global_types().clone();
        let bound = files
            .iter()
            .map(|(file, _)| context.file(*file).unwrap().1.clone())
            .collect::<Vec<_>>();
        let host = DeclaredTypeHost::new_after_global_merge(
            files
                .iter()
                .zip(&bound)
                .map(|((_, file), bound)| (&file.arena, bound)),
            GlobalMergeCompletion::for_test(options.name_resolution),
        )
        .unwrap();
        let store = context.store_mut_for_test();
        let globals = SynchronousIterationGlobals::resolve(store, &host, node).unwrap();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (sent, expected) = (bootstrap.undefined_type, bootstrap.number_type);
        for use_ in [
            SynchronousIterationUse::ForOf,
            SynchronousIterationUse::Spread,
            SynchronousIterationUse::Destructuring,
            SynchronousIterationUse::YieldStar,
        ] {
            let checked = SynchronousIterationQuery::new(
                store,
                &global_types,
                &globals,
                options,
                node,
                NoProperties,
            )
            .check(input, sent, use_, false)
            .unwrap();
            assert_eq!(
                checked.diagnostics,
                [IterationDiagnostic::IncompatibleNext {
                    use_,
                    sent,
                    expected
                }]
            );
        }
    }

    #[test]
    fn iterator_result_done_discriminates_yield_and_return_values() {
        let source = parsed(concat!(
            "declare var result: { done?: false; value: string } | { done: true; value: number }; ",
            "declare var implicit: { value: number }; ",
            "declare var optional: { done: boolean; value?: string };",
        ));
        let file = FileId::new(22_020);
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        };
        let mut context = context(&[(file, &source)], 0, options);
        let inputs = ["result", "implicit", "optional"].map(|name| {
            context
                .get_type_from_type_node(annotation(&source, file, name))
                .unwrap()
        });
        let global_types = context.global_types().clone();
        let globals = SynchronousIterationGlobals::default();
        let node = annotation(&source, file, "result");
        let store = context.store_mut_for_test();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (number, string, void, undefined) = (
            bootstrap.number_type,
            bootstrap.string_type,
            bootstrap.void_type,
            bootstrap.undefined_type,
        );
        let optional = store
            .expression_union_type_with_global_types(
                &global_types,
                &[string, undefined],
                UnionReduction::Literal,
            )
            .unwrap();
        let mut query = SynchronousIterationQuery::new(
            store,
            &global_types,
            &globals,
            options,
            node,
            StoredProperties,
        );
        assert_eq!(
            query.iterator_result(inputs[0]).unwrap(),
            IterationTypes {
                yield_type: Some(string),
                return_type: Some(number),
                next_type: None
            }
        );
        assert_eq!(
            query.iterator_result(inputs[1]).unwrap(),
            IterationTypes {
                yield_type: Some(number),
                return_type: Some(void),
                next_type: None
            }
        );
        assert_eq!(
            query.iterator_result(inputs[2]).unwrap(),
            IterationTypes {
                yield_type: Some(optional),
                return_type: Some(optional),
                next_type: None
            }
        );
    }

    #[test]
    fn structural_iterator_methods_combine_all_three_iteration_types() {
        let source = parsed(concat!(
            "interface State { ",
            "next(value: string): { value: number }; ",
            "return(value: boolean): { value: string }; ",
            "throw(error: unknown): { done: true; value: bigint }; ",
            "} declare var iterator: State;",
        ));
        let file = FileId::new(22_021);
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        };
        let mut context = context(&[(file, &source)], 0, options);
        let node = annotation(&source, file, "iterator");
        let input = context.get_type_from_type_node(node).unwrap();
        let global_types = context.global_types().clone();
        let globals = SynchronousIterationGlobals::default();
        let store = context.store_mut_for_test();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (number, string, boolean, bigint, void) = (
            bootstrap.number_type,
            bootstrap.string_type,
            bootstrap.boolean_type,
            bootstrap.bigint_type,
            bootstrap.void_type,
        );
        let yield_type = store
            .expression_union_type_with_global_types(
                &global_types,
                &[number, string],
                UnionReduction::Literal,
            )
            .unwrap();
        let return_type = store
            .expression_union_type_with_global_types(
                &global_types,
                &[void, boolean, bigint],
                UnionReduction::Literal,
            )
            .unwrap();
        let mut query = SynchronousIterationQuery::new(
            store,
            &global_types,
            &globals,
            options,
            node,
            StoredProperties,
        );
        let checked = query.iterator(input, true).unwrap();
        assert_eq!(
            checked.types,
            IterationTypes {
                yield_type: Some(yield_type),
                return_type: Some(return_type),
                next_type: Some(string),
            }
        );
        assert!(checked.diagnostics.is_empty());
    }

    #[test]
    fn invalid_iterator_methods_preserve_pinned_recovery_and_diagnostics() {
        let source = parsed(concat!(
            "declare var missing: {}; ",
            "declare var result: { next(): { done: false } }; ",
            "declare var method: { next(): { value: string }; return: number }; ",
            "declare var dynamic: { next: any };",
        ));
        let file = FileId::new(22_022);
        let options = CanonicalCheckerOptions::default();
        let mut context = context(&[(file, &source)], 0, options);
        let inputs = ["missing", "result", "method", "dynamic"].map(|name| {
            context
                .get_type_from_type_node(annotation(&source, file, name))
                .unwrap()
        });
        let global_types = context.global_types().clone();
        let globals = SynchronousIterationGlobals::default();
        let node = annotation(&source, file, "missing");
        let store = context.store_mut_for_test();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let (any, unknown, string) = (
            bootstrap.any_type,
            bootstrap.unknown_type,
            bootstrap.string_type,
        );
        let mut query = SynchronousIterationQuery::new(
            store,
            &global_types,
            &globals,
            options,
            node,
            StoredProperties,
        );
        let missing = query.iterator(inputs[0], true).unwrap();
        assert_eq!(missing.types, IterationTypes::default());
        assert_eq!(missing.diagnostics, [IterationDiagnostic::MissingNext]);
        let result = query.iterator(inputs[1], true).unwrap();
        assert_eq!(
            result.types,
            IterationTypes {
                yield_type: Some(any),
                return_type: Some(any),
                next_type: Some(unknown),
            }
        );
        assert_eq!(
            result.diagnostics,
            [IterationDiagnostic::MissingValue("next")]
        );
        let method = query.iterator(inputs[2], true).unwrap();
        assert_eq!(method.types.yield_type, Some(string));
        assert_eq!(
            method.diagnostics,
            [IterationDiagnostic::InvalidMethod("return")]
        );
        let dynamic = query.iterator(inputs[3], true).unwrap();
        assert_eq!(dynamic.types, IterationTypes::any(any));
        assert!(dynamic.diagnostics.is_empty());
    }
}

impl IterationTypes {
    fn any(any: TypeId) -> Self {
        Self {
            yield_type: Some(any),
            return_type: Some(any),
            next_type: Some(any),
        }
    }

    fn has_types(self) -> bool {
        self.yield_type.is_some() || self.return_type.is_some() || self.next_type.is_some()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SynchronousIterationUse {
    ForOf,
    Spread,
    Destructuring,
    YieldStar,
}

impl SynchronousIterationUse {
    pub(super) const fn next_input_diagnostic(self) -> u32 {
        match self {
            Self::ForOf => 2763,
            Self::Spread => 2764,
            Self::Destructuring => 2765,
            Self::YieldStar => 2766,
        }
    }

    pub(super) const fn allows_string_fallback(self) -> bool {
        matches!(self, Self::ForOf)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum IterationDiagnostic {
    NotIterable {
        input: TypeId,
        related: Vec<Self>,
    },
    MissingNext,
    InvalidMethod(&'static str),
    MissingValue(&'static str),
    IteratorMethodRequiresArguments {
        input: TypeId,
        iterable: TypeId,
    },
    IncompatibleNext {
        use_: SynchronousIterationUse,
        sent: TypeId,
        expected: TypeId,
    },
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct CheckedIterationTypes {
    pub(super) types: IterationTypes,
    pub(super) diagnostics: Vec<IterationDiagnostic>,
}

/// The global identities used by the pinned synchronous iterator fast paths.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct SynchronousIterationGlobals {
    pub(super) iterable: Option<TypeId>,
    iterator: Option<TypeId>,
    iterator_object: Option<TypeId>,
    iterable_iterator: Option<TypeId>,
    generator: Option<TypeId>,
    builtin_iterators: Vec<TypeId>,
    yield_result: Option<TypeId>,
    return_result: Option<TypeId>,
}

impl SynchronousIterationGlobals {
    /// Proves all optional global identities before any of them are resolved.
    pub(super) fn preflight(
        store: &CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        node: NodeRef,
    ) -> Result<(), SourceCheckError> {
        for (name, arity) in Self::global_names() {
            optional_global_type_has_arity(store, host, name, arity)
                .map_err(|error| global_error(error, node))?;
        }
        Ok(())
    }

    pub(super) fn resolve(
        store: &mut CanonicalTypeMapperStore,
        host: &DeclaredTypeHost<'_>,
        node: NodeRef,
    ) -> Result<Self, SourceCheckError> {
        Self::preflight(store, host, node)?;
        let mut resolve = |name, arity| {
            resolve_optional_global_type(store, host, name, arity)
                .map_err(|error| global_error(error, node))
        };
        Ok(Self {
            iterable: resolve("Iterable", 3)?,
            iterator: resolve("Iterator", 3)?,
            iterator_object: resolve("IteratorObject", 3)?,
            iterable_iterator: resolve("IterableIterator", 3)?,
            generator: resolve("Generator", 3)?,
            builtin_iterators: [
                "ArrayIterator",
                "MapIterator",
                "SetIterator",
                "StringIterator",
            ]
            .into_iter()
            .map(|name| resolve(name, 1))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect(),
            yield_result: resolve("IteratorYieldResult", 1)?,
            return_result: resolve("IteratorReturnResult", 1)?,
        })
    }

    const fn global_names() -> [(&'static str, usize); 11] {
        [
            ("Iterable", 3),
            ("Iterator", 3),
            ("IteratorObject", 3),
            ("IterableIterator", 3),
            ("Generator", 3),
            ("ArrayIterator", 1),
            ("MapIterator", 1),
            ("SetIterator", 1),
            ("StringIterator", 1),
            ("IteratorYieldResult", 1),
            ("IteratorReturnResult", 1),
        ]
    }
}

fn global_error(
    error: super::CanonicalGlobalTypeInitializationError,
    node: NodeRef,
) -> SourceCheckError {
    match error {
        super::CanonicalGlobalTypeInitializationError::DeclaredType(error) => {
            SourceCheckError::DeclaredType(error)
        }
        _ => SourceCheckError::Element(node),
    }
}

/// A source query supplies authenticated, lazily resolved properties.
///
/// `None` means a valid missing property. Unsupported or malformed members
/// must return an error. They must not become a missing-property diagnostic.
pub(super) trait IterationPropertyResolver {
    /// Resolves the actual global `Symbol.iterator` property-name type before
    /// using the pinned internal known-symbol fallback.
    fn iterator_key(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
    ) -> Result<EscapedName, SourceCheckError>;

    fn property(
        &mut self,
        store: &mut CanonicalTypeMapperStore,
        receiver: TypeId,
        name: EscapedNameRef<'_>,
    ) -> Result<Option<ResolvedOwnProperty>, SourceCheckError>;
}

pub(super) struct SynchronousIterationQuery<'store, 'globals, P> {
    store: &'store mut CanonicalTypeMapperStore,
    global_types: &'globals CanonicalGlobalTypes,
    globals: &'globals SynchronousIterationGlobals,
    options: CanonicalCheckerOptions,
    node: NodeRef,
    properties: P,
}

impl<'store, 'globals, P: IterationPropertyResolver>
    SynchronousIterationQuery<'store, 'globals, P>
{
    pub(super) fn new(
        store: &'store mut CanonicalTypeMapperStore,
        global_types: &'globals CanonicalGlobalTypes,
        globals: &'globals SynchronousIterationGlobals,
        options: CanonicalCheckerOptions,
        node: NodeRef,
        properties: P,
    ) -> Self {
        Self {
            store,
            global_types,
            globals,
            options,
            node,
            properties,
        }
    }

    /// Checks the iterator protocol and the value sent to `next`.
    ///
    /// The caller selects this path when optional global `Iterable` has arity
    /// three. Emit target does not select between this and array fallback.
    pub(super) fn check(
        &mut self,
        input: TypeId,
        sent: TypeId,
        use_: SynchronousIterationUse,
        possibly_out_of_bounds: bool,
    ) -> Result<CheckedIterationTypes, SourceCheckError> {
        if self.is_any(input)? {
            return Ok(CheckedIterationTypes {
                types: IterationTypes {
                    yield_type: Some(input),
                    ..IterationTypes::default()
                },
                diagnostics: Vec::new(),
            });
        }
        let mut checked = self.iterable(input, true)?;
        if let Some(expected) = checked.types.next_type
            && !self.store.is_type_assignable_to_with_global_types(
                sent,
                expected,
                self.global_types,
            )?
        {
            checked
                .diagnostics
                .push(IterationDiagnostic::IncompatibleNext {
                    use_,
                    sent,
                    expected,
                });
        }
        if possibly_out_of_bounds
            && self.options.no_unchecked_indexed_access
            && self.options.intrinsic.strict_null_checks
            && let Some(yield_type) = checked.types.yield_type
        {
            let undefined = self.bootstrap()?.undefined_type;
            checked.types.yield_type = self.union(&[yield_type, undefined])?;
        }
        Ok(checked)
    }

    fn bootstrap(&self) -> Result<&super::IntrinsicBootstrap, SourceCheckError> {
        self.store
            .intrinsic_bootstrap()
            .ok_or_else(|| RelationUnavailable::MissingBootstrap.into())
    }

    fn is_any(&self, type_: TypeId) -> Result<bool, SourceCheckError> {
        Ok(self
            .store
            .type_payload(type_)
            .ok_or(RelationUnavailable::Type(type_))?
            .flags()
            .intersects(TypeFlags::ANY))
    }

    fn union(&mut self, types: &[TypeId]) -> Result<Option<TypeId>, SourceCheckError> {
        match types {
            [] => Ok(None),
            [only] => Ok(Some(*only)),
            _ => self
                .store
                .expression_union_type_with_global_types(
                    self.global_types,
                    types,
                    UnionReduction::Literal,
                )
                .map(Some)
                .map_err(Into::into),
        }
    }

    fn intersection(&mut self, types: &[TypeId]) -> Result<TypeId, SourceCheckError> {
        match types {
            [] => Ok(self.bootstrap()?.never_type),
            [only] => Ok(*only),
            _ => self
                .store
                .canonical_intersection_type(types, None)
                .map_err(|error| match error {
                    super::intersection_types::IntersectionTypeError::UnsupportedConstituent(_)
                    | super::intersection_types::IntersectionTypeError::UnsupportedPropertyType(
                        _,
                    ) => SourceCheckError::Unsupported(UnsupportedSourceSyntax::Element(self.node)),
                    _ => SourceCheckError::Element(self.node),
                }),
        }
    }

    fn combine(&mut self, types: &[IterationTypes]) -> Result<IterationTypes, SourceCheckError> {
        Ok(IterationTypes {
            yield_type: self.union(
                &types
                    .iter()
                    .filter_map(|type_| type_.yield_type)
                    .collect::<Vec<_>>(),
            )?,
            return_type: self.union(
                &types
                    .iter()
                    .filter_map(|type_| type_.return_type)
                    .collect::<Vec<_>>(),
            )?,
            next_type: self.union(
                &types
                    .iter()
                    .filter_map(|type_| type_.next_type)
                    .collect::<Vec<_>>(),
            )?,
        })
    }

    fn iterable(
        &mut self,
        input: TypeId,
        report_errors: bool,
    ) -> Result<CheckedIterationTypes, SourceCheckError> {
        if self.is_any(input)? {
            return Ok(CheckedIterationTypes {
                types: IterationTypes::any(self.bootstrap()?.any_type),
                diagnostics: Vec::new(),
            });
        }
        let record = self
            .store
            .type_payload(input)
            .ok_or(RelationUnavailable::Type(input))?;
        if let TypeData::Union(union) = record.data() {
            let constituents = union.union.types.clone();
            self.store.validate_union_constituent(input)?;
            let mut types = Vec::with_capacity(constituents.len());
            for constituent in constituents {
                let checked = self.iterable(constituent, false)?;
                if !checked.types.has_types() {
                    return Ok(Self::not_iterable(input, report_errors, Vec::new()));
                }
                types.push(checked.types);
            }
            return Ok(CheckedIterationTypes {
                types: self.combine(&types)?,
                diagnostics: Vec::new(),
            });
        }
        if input == self.bootstrap()?.never_type
            || record
                .object_flags()
                .contains(ObjectFlags::IS_NEVER_INTERSECTION)
        {
            return Ok(Self::not_iterable(input, report_errors, Vec::new()));
        }
        if let Some(types) = self.fast(input, true)? {
            return Ok(CheckedIterationTypes {
                types,
                diagnostics: Vec::new(),
            });
        }
        let name = self.properties.iterator_key(self.store)?;
        let property = self.properties.property(self.store, input, name.as_ref())?;
        let Some(property) = property.filter(|property| !property.optional) else {
            return Ok(Self::not_iterable(input, report_errors, Vec::new()));
        };
        if self.is_any(property.type_)? {
            return Ok(CheckedIterationTypes {
                types: IterationTypes::any(self.bootstrap()?.any_type),
                diagnostics: Vec::new(),
            });
        }
        let signatures = self.signatures(property.type_)?;
        let mut returns = Vec::new();
        for signature in &signatures {
            if signature.min_argument_count == 0 {
                returns.push(self.return_type(signature)?);
            }
        }
        if returns.is_empty() {
            let mut related = Vec::new();
            if report_errors
                && !signatures.is_empty()
                && let Some(iterable) = self.globals.iterable
            {
                related
                    .push(IterationDiagnostic::IteratorMethodRequiresArguments { input, iterable });
            }
            return Ok(Self::not_iterable(input, report_errors, related));
        }
        let iterator = self.intersection(&returns)?;
        let checked = self.iterator(iterator, report_errors)?;
        if checked.types.has_types() {
            Ok(checked)
        } else {
            Ok(Self::not_iterable(
                input,
                report_errors,
                checked.diagnostics,
            ))
        }
    }

    fn not_iterable(
        input: TypeId,
        report_errors: bool,
        related: Vec<IterationDiagnostic>,
    ) -> CheckedIterationTypes {
        CheckedIterationTypes {
            types: IterationTypes::default(),
            diagnostics: if report_errors {
                vec![IterationDiagnostic::NotIterable { input, related }]
            } else {
                Vec::new()
            },
        }
    }

    fn fast(
        &mut self,
        input: TypeId,
        iterable: bool,
    ) -> Result<Option<IterationTypes>, SourceCheckError> {
        let record = self
            .store
            .type_payload(input)
            .ok_or(RelationUnavailable::Type(input))?;
        if !record.object_flags().contains(ObjectFlags::REFERENCE) {
            return Ok(None);
        }
        let target = match record.data() {
            TypeData::TypeReference(reference) => reference.object.target,
            TypeData::Interface(interface) => interface.reference.object.target,
            _ => return Ok(None),
        };
        let Some(target) = target else {
            return Err(RelationUnavailable::InvalidStructuredMembers(input).into());
        };
        let three_arguments = [
            if iterable {
                self.globals.iterable
            } else {
                self.globals.iterator
            },
            self.globals.iterator_object,
            self.globals.iterable_iterator,
            self.globals.generator,
        ]
        .contains(&Some(target));
        let builtin = self.globals.builtin_iterators.contains(&target);
        if !three_arguments && !builtin {
            return Ok(None);
        }
        let reference = validate_direct_generic_reference(self.store, input)
            .map_err(|_| RelationUnavailable::InvalidStructuredMembers(input))?;
        if three_arguments {
            let [yield_type, return_type, next_type] = reference.type_arguments.as_slice() else {
                return Err(RelationUnavailable::InvalidStructuredMembers(input).into());
            };
            return Ok(Some(IterationTypes {
                yield_type: Some(*yield_type),
                return_type: Some(*return_type),
                next_type: Some(*next_type),
            }));
        }
        let [yield_type] = reference.type_arguments.as_slice() else {
            return Err(RelationUnavailable::InvalidStructuredMembers(input).into());
        };
        let bootstrap = self.bootstrap()?;
        Ok(Some(IterationTypes {
            yield_type: Some(*yield_type),
            return_type: Some(if self.options.strict_builtin_iterator_return {
                bootstrap.undefined_type
            } else {
                bootstrap.any_type
            }),
            next_type: Some(bootstrap.unknown_type),
        }))
    }

    fn iterator(
        &mut self,
        input: TypeId,
        report_errors: bool,
    ) -> Result<CheckedIterationTypes, SourceCheckError> {
        if self.is_any(input)? {
            return Ok(CheckedIterationTypes {
                types: IterationTypes::any(self.bootstrap()?.any_type),
                diagnostics: Vec::new(),
            });
        }
        if let Some(types) = self.fast(input, false)? {
            return Ok(CheckedIterationTypes {
                types,
                diagnostics: Vec::new(),
            });
        }
        let mut types = Vec::new();
        let mut diagnostics = Vec::new();
        for name in ["next", "return", "throw"] {
            let checked = self.method(input, name, report_errors)?;
            types.push(checked.types);
            diagnostics.extend(checked.diagnostics);
        }
        Ok(CheckedIterationTypes {
            types: self.combine(&types)?,
            diagnostics,
        })
    }

    fn signatures(
        &self,
        type_: TypeId,
    ) -> Result<Box<[ValidatedSingleCallable]>, SourceCheckError> {
        match validate_stored_callable_set(self.store, type_) {
            StoredCallableSetValidation::NotCallable => Ok(Box::new([])),
            StoredCallableSetValidation::Pending { .. } => {
                Err(RelationUnavailable::UnresolvedFunctionType(type_).into())
            }
            StoredCallableSetValidation::Malformed { .. } => {
                Err(RelationUnavailable::MalformedFunctionType(type_).into())
            }
            StoredCallableSetValidation::Valid { projection, .. } => Ok(projection.call_signatures),
        }
    }

    fn return_type(&self, signature: &ValidatedSingleCallable) -> Result<TypeId, SourceCheckError> {
        signature
            .return_type
            .ok_or_else(|| RelationUnavailable::UnresolvedFunctionType(signature.owner).into())
    }

    fn without_nullish(&mut self, type_: TypeId) -> Result<TypeId, SourceCheckError> {
        let record = self
            .store
            .type_payload(type_)
            .ok_or(RelationUnavailable::Type(type_))?;
        if record
            .flags()
            .intersects(TypeFlags::NULL | TypeFlags::UNDEFINED)
        {
            return Ok(self.bootstrap()?.never_type);
        }
        let TypeData::Union(union) = record.data() else {
            return Ok(type_);
        };
        let types = union.union.types.clone();
        let mut retained = Vec::new();
        for type_ in types {
            if !self
                .store
                .type_payload(type_)
                .ok_or(RelationUnavailable::Type(type_))?
                .flags()
                .intersects(TypeFlags::NULL | TypeFlags::UNDEFINED)
            {
                retained.push(type_);
            }
        }
        Ok(self
            .union(&retained)?
            .unwrap_or(self.bootstrap()?.never_type))
    }

    fn method(
        &mut self,
        input: TypeId,
        name: &'static str,
        report_errors: bool,
    ) -> Result<CheckedIterationTypes, SourceCheckError> {
        let key = EscapedName::source(name);
        let property = self.properties.property(self.store, input, key.as_ref())?;
        if property.is_none() && name != "next" {
            return Ok(CheckedIterationTypes::default());
        }
        let method_type = property
            .filter(|property| name != "next" || !property.optional)
            .map(|property| property.type_);
        let method_type = match method_type {
            Some(type_) if name != "next" => Some(self.without_nullish(type_)?),
            type_ => type_,
        };
        if let Some(type_) = method_type
            && self.is_any(type_)?
        {
            return Ok(CheckedIterationTypes {
                types: IterationTypes::any(self.bootstrap()?.any_type),
                diagnostics: Vec::new(),
            });
        }
        let signatures = method_type
            .map(|type_| self.signatures(type_))
            .transpose()?
            .unwrap_or_default();
        if signatures.is_empty() {
            return Ok(CheckedIterationTypes {
                types: IterationTypes::default(),
                diagnostics: if report_errors {
                    vec![if name == "next" {
                        IterationDiagnostic::MissingNext
                    } else {
                        IterationDiagnostic::InvalidMethod(name)
                    }]
                } else {
                    Vec::new()
                },
            });
        }

        if signatures.len() == 1
            && let Some(method_type) = method_type
            && let Some(types) = self.inherited_global_method(method_type, name)?
        {
            return Ok(CheckedIterationTypes {
                types,
                diagnostics: Vec::new(),
            });
        }

        let mut parameter_types = Vec::new();
        let mut return_types = Vec::new();
        for signature in &signatures {
            if name != "throw"
                && let Some(parameter) = self.first_parameter(signature)?
            {
                parameter_types.push(parameter);
            }
            return_types.push(self.return_type(signature)?);
        }
        let parameter_type = self
            .union(&parameter_types)?
            .unwrap_or(self.bootstrap()?.unknown_type);
        let result_type = self.intersection(&return_types)?;
        let result = self.iterator_result(result_type)?;
        let mut diagnostics = Vec::new();
        let mut returns = Vec::new();
        if name == "return" {
            returns.push(parameter_type);
        }
        let yield_type = if result.has_types() {
            returns.extend(result.return_type);
            result.yield_type
        } else {
            if report_errors {
                diagnostics.push(IterationDiagnostic::MissingValue(name));
            }
            returns.push(self.bootstrap()?.any_type);
            Some(self.bootstrap()?.any_type)
        };
        Ok(CheckedIterationTypes {
            types: IterationTypes {
                yield_type,
                return_type: self.union(&returns)?,
                next_type: (name == "next").then_some(parameter_type),
            },
            diagnostics,
        })
    }

    /// Global iterator method mappers retain `TNext` without the `undefined`
    /// introduced by the optional tuple argument in the declared signature.
    fn inherited_global_method(
        &self,
        method_type: TypeId,
        name: &str,
    ) -> Result<Option<IterationTypes>, SourceCheckError> {
        let record = self
            .store
            .type_payload(method_type)
            .ok_or(RelationUnavailable::Type(method_type))?;
        let (Some(method), TypeData::Object(object)) = (record.symbol(), record.data()) else {
            return Ok(None);
        };
        for global in [self.globals.generator, self.globals.iterator]
            .into_iter()
            .flatten()
        {
            let global_record = self
                .store
                .type_payload(global)
                .ok_or(RelationUnavailable::Type(global))?;
            let global_method = global_record
                .symbol()
                .and_then(|owner| self.store.symbol(owner))
                .and_then(ts_binder::semantic::Symbol::members)
                .and_then(|members| self.store.symbol_table(members))
                .and_then(|members| members.get_source(name));
            if global_method != Some(method) {
                continue;
            }
            let TypeData::Interface(interface) = global_record.data() else {
                return Err(RelationUnavailable::InvalidStructuredMembers(global).into());
            };
            let Some([yield_type, return_type, next_type]) =
                interface.reference.resolved_type_arguments.as_deref()
            else {
                return Err(RelationUnavailable::InvalidStructuredMembers(global).into());
            };
            let mapped = |parameter| match object.mapper {
                Some(mapper) => self
                    .store
                    .map_type(mapper, parameter)
                    .ok_or(RelationUnavailable::InvalidStructuredMembers(method_type)),
                None => Ok(parameter),
            };
            return Ok(Some(IterationTypes {
                yield_type: Some(mapped(*yield_type)?),
                return_type: Some(mapped(*return_type)?),
                next_type: (name == "next").then(|| mapped(*next_type)).transpose()?,
            }));
        }
        Ok(None)
    }

    fn first_parameter(
        &mut self,
        signature: &ValidatedSingleCallable,
    ) -> Result<Option<TypeId>, SourceCheckError> {
        if let Some(parameter) = signature.parameters.first() {
            return Ok(Some(*parameter));
        }
        let Some(rest) = signature.rest_parameter else {
            return Ok(None);
        };
        if self
            .store
            .canonical_tuple_shape(rest)
            .map_err(|_| RelationUnavailable::InvalidStructuredMembers(rest))?
            .is_some_and(|shape| shape.element_types().is_empty())
        {
            return Ok(Some(self.bootstrap()?.any_type));
        }
        self.rest_parameter_first_type(rest).map(Some)
    }

    fn rest_parameter_first_type(&mut self, type_: TypeId) -> Result<TypeId, SourceCheckError> {
        let record = self
            .store
            .type_payload(type_)
            .ok_or(RelationUnavailable::Type(type_))?;
        if let TypeData::Union(union) = record.data() {
            let constituents = union.union.types.clone();
            let mut values = Vec::new();
            for constituent in constituents {
                values.push(self.rest_parameter_first_type(constituent)?);
            }
            return self
                .union(&values)?
                .ok_or_else(|| RelationUnavailable::MalformedUnion(type_).into());
        }
        if let Some(element) = self
            .store
            .canonical_array_element_type(self.global_types, type_)?
        {
            return Ok(element);
        }
        let shape = self
            .store
            .canonical_tuple_shape(type_)
            .map_err(|_| RelationUnavailable::InvalidStructuredMembers(type_))?
            .ok_or(RelationUnavailable::UnsupportedStructuredType(type_))?;
        let Some(first) = shape.element_types().first().copied() else {
            return Ok(self.bootstrap()?.undefined_type);
        };
        let flags = shape.element_infos()[0].flags();
        if flags.contains(ElementFlags::VARIADIC) {
            return self.rest_parameter_first_type(first);
        }
        if flags.contains(ElementFlags::OPTIONAL) && self.options.intrinsic.strict_null_checks {
            let undefined = self.bootstrap()?.undefined_type;
            return self
                .union(&[first, undefined])?
                .ok_or_else(|| RelationUnavailable::InvalidStructuredMembers(type_).into());
        }
        Ok(first)
    }

    fn iterator_result(&mut self, input: TypeId) -> Result<IterationTypes, SourceCheckError> {
        if self.is_any(input)? {
            return Ok(IterationTypes::any(self.bootstrap()?.any_type));
        }
        let record = self
            .store
            .type_payload(input)
            .ok_or(RelationUnavailable::Type(input))?;
        if record.object_flags().contains(ObjectFlags::REFERENCE) {
            let target = match record.data() {
                TypeData::TypeReference(reference) => reference.object.target,
                TypeData::Interface(interface) => interface.reference.object.target,
                _ => None,
            };
            if target.is_some()
                && (target == self.globals.yield_result || target == self.globals.return_result)
            {
                let reference = validate_direct_generic_reference(self.store, input)
                    .map_err(|_| RelationUnavailable::InvalidStructuredMembers(input))?;
                let [value] = reference.type_arguments.as_slice() else {
                    return Err(RelationUnavailable::InvalidStructuredMembers(input).into());
                };
                return Ok(IterationTypes {
                    yield_type: (target == self.globals.yield_result).then_some(*value),
                    return_type: (target == self.globals.return_result).then_some(*value),
                    next_type: None,
                });
            }
        }
        let constituents = match record.data() {
            TypeData::Union(union) => union.union.types.clone(),
            _ => vec![input],
        };
        let yield_type = self.result_value(&constituents, false)?;
        let return_type = self.result_value(&constituents, true)?;
        if yield_type.is_none() && return_type.is_none() {
            return Ok(IterationTypes::default());
        }
        Ok(IterationTypes {
            yield_type,
            return_type: return_type.or(Some(self.bootstrap()?.void_type)),
            next_type: None,
        })
    }

    fn result_value(
        &mut self,
        constituents: &[TypeId],
        done: bool,
    ) -> Result<Option<TypeId>, SourceCheckError> {
        let expected_done = if done {
            self.bootstrap()?.true_type
        } else {
            self.bootstrap()?.false_type
        };
        let done_key = EscapedName::source("done");
        let value_key = EscapedName::source("value");
        let mut values = Vec::new();
        for &constituent in constituents {
            if constituent == self.bootstrap()?.never_type {
                continue;
            }
            let property = self
                .properties
                .property(self.store, constituent, done_key.as_ref())?;
            let done_type = match property {
                Some(property) => self.read_property_type(property)?,
                None => self.bootstrap()?.false_type,
            };
            if !self.store.is_type_assignable_to_with_global_types(
                expected_done,
                done_type,
                self.global_types,
            )? {
                continue;
            }
            let property = self
                .properties
                .property(self.store, constituent, value_key.as_ref())?;
            let Some(property) = property else {
                return Ok(None);
            };
            values.push(self.read_property_type(property)?);
        }
        self.union(&values)
    }

    fn read_property_type(
        &mut self,
        property: ResolvedOwnProperty,
    ) -> Result<TypeId, SourceCheckError> {
        if property.optional && self.options.intrinsic.strict_null_checks {
            let undefined = self.bootstrap()?.undefined_type;
            return self.union(&[property.type_, undefined])?.ok_or_else(|| {
                RelationUnavailable::InvalidStructuredMembers(property.type_).into()
            });
        }
        Ok(property.type_)
    }
}
