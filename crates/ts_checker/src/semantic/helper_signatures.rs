//! Context-owned helper arity queries without source-body checking.

use ts_ast::{FileId, NodeArenaRevision, NodeData, NodeRef};
use ts_binder::{SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, DeclaredTypeHostError, TypeId,
    bootstrap::LiteralTypeCacheError,
    calls::{DirectCallError, DirectCallUnsupported, call_signature_parameter_counts},
    instantiate::InstantiationSession,
    type_nodes::CanonicalTypeQuery,
    type_records::{TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

/// The helper query could not establish an exact answer for a resolved value.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalHelperSignatureError {
    InvalidSymbol(SemanticSymbolId),
    UnresolvedAlias(SemanticSymbolId),
    MissingDeclaration(SemanticSymbolId),
    InvalidDeclaration {
        symbol: SemanticSymbolId,
        declaration: NodeRef,
    },
    StaleSource {
        file: FileId,
        expected: NodeArenaRevision,
        actual: NodeArenaRevision,
    },
    ProviderUnavailable {
        symbol: SemanticSymbolId,
        declaration: NodeRef,
    },
    InvalidValueCache {
        symbol: SemanticSymbolId,
        type_: Option<TypeId>,
    },
    InvalidCallable {
        symbol: SemanticSymbolId,
        type_: TypeId,
    },
    PendingCallable {
        symbol: SemanticSymbolId,
        type_: TypeId,
    },
    ArityUnavailable {
        symbol: SemanticSymbolId,
        type_: TypeId,
    },
    SourceHost(DeclaredTypeHostError),
    DeclaredType(DeclaredTypeError),
}

impl std::fmt::Display for CanonicalHelperSignatureError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SourceHost(error) => error.fmt(formatter),
            Self::DeclaredType(error) => error.fmt(formatter),
            error => write!(formatter, "helper signature query failed: {error:?}"),
        }
    }
}

impl std::error::Error for CanonicalHelperSignatureError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::SourceHost(error) => Some(error),
            Self::DeclaredType(error) => Some(error),
            _ => None,
        }
    }
}

impl From<DeclaredTypeHostError> for CanonicalHelperSignatureError {
    fn from(error: DeclaredTypeHostError) -> Self {
        Self::SourceHost(error)
    }
}

impl From<DeclaredTypeError> for CanonicalHelperSignatureError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

pub(super) struct HelperSignatureQuery<'query, 'arena> {
    pub(super) store: &'query mut CanonicalTypeMapperStore,
    pub(super) host: &'query DeclaredTypeHost<'arena>,
    pub(super) global_types: &'query CanonicalGlobalTypes,
    pub(super) options: CanonicalCheckerOptions,
    pub(super) session: &'query mut InstantiationSession,
    pub(super) diagnostics: &'query mut CanonicalCheckerDiagnostics,
}

impl HelperSignatureQuery<'_, '_> {
    pub(super) fn has_arity_greater_than(
        &mut self,
        symbol: SemanticSymbolId,
        arity: usize,
    ) -> Result<bool, CanonicalHelperSignatureError> {
        let symbol = self
            .store
            .get_merged_symbol(symbol)
            .ok_or(CanonicalHelperSignatureError::InvalidSymbol(symbol))?;
        let record = self
            .store
            .symbol(symbol)
            .ok_or(CanonicalHelperSignatureError::InvalidSymbol(symbol))?;
        if record
            .flags()
            .intersects(SymbolFlags::ALIAS | SymbolFlags::EXPORT_VALUE)
        {
            return Err(CanonicalHelperSignatureError::UnresolvedAlias(symbol));
        }
        if !record.flags().intersects(SymbolFlags::VALUE) {
            return Err(CanonicalHelperSignatureError::InvalidSymbol(symbol));
        }
        let declarations = record.declarations().unwrap_or_default().to_vec();
        let declaration = record
            .value_declaration()
            .ok_or(CanonicalHelperSignatureError::MissingDeclaration(symbol))?;
        if declarations
            .iter()
            .filter(|node| **node == declaration)
            .count()
            != 1
        {
            return Err(CanonicalHelperSignatureError::InvalidDeclaration {
                symbol,
                declaration,
            });
        }
        for &node in &declarations {
            self.validate_declaration(symbol, node)?;
        }
        let cached = self
            .store
            .value_symbol_links(symbol)
            .and_then(|links| links.resolved_type);
        let (arena, bound) = self.host.source(declaration).ok_or(
            CanonicalHelperSignatureError::InvalidDeclaration {
                symbol,
                declaration,
            },
        )?;
        if cached.is_none()
            && bound
                .source_facts()
                .is_none_or(|facts| !facts.is_declaration_file())
        {
            return Err(CanonicalHelperSignatureError::ProviderUnavailable {
                symbol,
                declaration,
            });
        }
        let node = arena.get(declaration.node).ok_or(
            CanonicalHelperSignatureError::InvalidDeclaration {
                symbol,
                declaration,
            },
        )?;
        let type_ = match &node.data {
            NodeData::FunctionDeclaration(_) if declarations.len() == 1 => self
                .type_query()?
                .get_type_of_source_callable(declaration, symbol)?,
            NodeData::FunctionDeclaration(_) => {
                self.existing_overload_type(symbol, declaration, cached)?
            }
            NodeData::VariableDeclaration(_)
            | NodeData::PropertyDeclaration(_)
            | NodeData::PropertySignatureDeclaration(_) => {
                self.type_query()?.get_type_of_declared_value(symbol)?
            }
            _ => {
                return Err(CanonicalHelperSignatureError::ProviderUnavailable {
                    symbol,
                    declaration,
                });
            }
        };
        let counts = call_signature_parameter_counts(self.store, self.global_types, type_)
            .map_err(|error| Self::arity_error(symbol, type_, error))?;
        match counts {
            Some(counts) => Ok(counts.into_iter().any(|count| count > arity)),
            None => self.proven_non_callable(symbol, type_),
        }
    }

    fn type_query(&mut self) -> Result<CanonicalTypeQuery<'_, '_, '_, '_>, DeclaredTypeError> {
        CanonicalTypeQuery::new_with_global_types_and_session(
            self.store,
            self.host,
            self.global_types,
            self.options,
            self.session,
            self.diagnostics,
        )
    }

    fn validate_declaration(
        &self,
        symbol: SemanticSymbolId,
        declaration: NodeRef,
    ) -> Result<(), CanonicalHelperSignatureError> {
        let invalid = || CanonicalHelperSignatureError::InvalidDeclaration {
            symbol,
            declaration,
        };
        let (arena, bound) = self.host.source(declaration).ok_or_else(invalid)?;
        if arena.revision() != bound.node_arena_revision() {
            return Err(CanonicalHelperSignatureError::StaleSource {
                file: declaration.file,
                expected: bound.node_arena_revision(),
                actual: arena.revision(),
            });
        }
        if !declaration.is_for(arena.id(), bound.file_id())
            || !bound.contains(declaration)
            || !self.store.contains_node_ref(declaration)
            || !self.host.symbol_matches(self.store, declaration, symbol)
        {
            return Err(invalid());
        }
        Ok(())
    }

    fn existing_overload_type(
        &self,
        symbol: SemanticSymbolId,
        declaration: NodeRef,
        cached: Option<TypeId>,
    ) -> Result<TypeId, CanonicalHelperSignatureError> {
        let type_ = cached.ok_or(CanonicalHelperSignatureError::ProviderUnavailable {
            symbol,
            declaration,
        })?;
        if self.store.type_payload(type_).and_then(TypeRecord::symbol) != Some(symbol) {
            return Err(CanonicalHelperSignatureError::InvalidValueCache {
                symbol,
                type_: cached,
            });
        }
        Ok(type_)
    }

    fn proven_non_callable(
        &self,
        symbol: SemanticSymbolId,
        type_: TypeId,
    ) -> Result<bool, CanonicalHelperSignatureError> {
        let invalid = || CanonicalHelperSignatureError::InvalidCallable { symbol, type_ };
        let unavailable = || CanonicalHelperSignatureError::ArityUnavailable { symbol, type_ };
        let record = self.store.type_payload(type_).ok_or_else(invalid)?;
        let primitive = record.flags().intersects(
            TypeFlags::PRIMITIVE
                | TypeFlags::ANY
                | TypeFlags::UNKNOWN
                | TypeFlags::NEVER
                | TypeFlags::NON_PRIMITIVE,
        );
        let resolved_object = matches!(record.data(), TypeData::Object(_))
            && record
                .object_flags()
                .contains(ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
            && record.data().structured().is_some_and(|structured| {
                structured.signatures.as_ref().is_some_and(Vec::is_empty)
            });
        if !primitive && !resolved_object {
            return Err(unavailable());
        }
        self.store
            .validate_union_constituent_with_global_types(self.global_types, type_)
            .map_err(|error| match error {
                LiteralTypeCacheError::UnsupportedUnionConstituent(_) => unavailable(),
                _ => invalid(),
            })?;
        Ok(false)
    }

    fn arity_error(
        symbol: SemanticSymbolId,
        type_: TypeId,
        error: DirectCallError,
    ) -> CanonicalHelperSignatureError {
        match error {
            DirectCallError::Unsupported(DirectCallUnsupported::PendingCallable(_)) => {
                CanonicalHelperSignatureError::PendingCallable { symbol, type_ }
            }
            DirectCallError::Unsupported(_) | DirectCallError::Relation(_) => {
                CanonicalHelperSignatureError::ArityUnavailable { symbol, type_ }
            }
            DirectCallError::Invariant(_) => {
                CanonicalHelperSignatureError::InvalidCallable { symbol, type_ }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use ts_ast::NodeId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        AliasTargetState, CanonicalCheckerContext, TypeNodeLinks, ValueSymbolLinks,
    };

    const LIBRARY: FileId = FileId::new(24_000);
    const SOURCE: FileId = FileId::new(24_001);

    fn parsed(source: &str) -> ParseResult {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        parsed
    }

    fn library() -> ParseResult {
        parsed(concat!(
            "interface IArguments {}\ninterface Array<T> {}\n",
            "interface ReadonlyArray<T> {}\ninterface Object {}\n",
            "interface Function {}\ninterface String {}\ninterface Number {}\n",
            "interface Boolean {}\ninterface RegExp {}\n",
        ))
    }

    fn context<'a>(
        library: &'a ParseResult,
        source: &'a ParseResult,
        external: bool,
    ) -> CanonicalCheckerContext<'a> {
        context_with_source_kind(library, source, external, true)
    }

    fn context_with_source_kind<'a>(
        library: &'a ParseResult,
        source: &'a ParseResult,
        external: bool,
        declaration_file: bool,
    ) -> CanonicalCheckerContext<'a> {
        CanonicalCheckerContext::new(
            bindings(library, source, external, declaration_file),
            vec![(LIBRARY, &library.arena), (SOURCE, &source.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn bindings(
        library: &ParseResult,
        source: &ParseResult,
        external: bool,
        declaration_file: bool,
    ) -> ts_binder::CanonicalProgramBindings {
        let mut binder = CanonicalBinder::new();
        for (file, parsed, is_library, module) in [
            (LIBRARY, library, true, CanonicalModuleState::Script),
            (
                SOURCE,
                source,
                false,
                if external {
                    CanonicalModuleState::External
                } else {
                    CanonicalModuleState::Script
                },
            ),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!("\"/project/{}.d.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        is_library || declaration_file,
                        is_library,
                        module,
                    ),
                )
                .unwrap();
        }
        binder
            .bind_typescript_declaration_slice(&library.arena, LIBRARY)
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&source.arena, SOURCE)
            .unwrap();
        binder.finish()
    }

    fn declaration(source: &ParseResult, name: &str) -> NodeId {
        source.arena.iter().find_map(|(node, record)| {
            let name_node = match &record.data {
                NodeData::FunctionDeclaration(function) => function.name?,
                NodeData::VariableDeclaration(variable) => variable.name,
                NodeData::ExportSpecifier(export) => export.name,
                _ => return None,
            };
            matches!(source.arena.get(name_node).map(|node| &node.data), Some(NodeData::Identifier(identifier)) if identifier.text == name)
                .then_some(node)
        }).unwrap()
    }

    fn symbol(
        context: &CanonicalCheckerContext<'_>,
        source: &ParseResult,
        name: &str,
    ) -> SemanticSymbolId {
        context
            .file(SOURCE)
            .unwrap()
            .1
            .symbol(NodeRef::new(
                source.arena.id(),
                SOURCE,
                declaration(source, name),
            ))
            .unwrap()
    }

    fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize) {
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().symbol_len(),
        )
    }

    fn assert_unchecked(context: &CanonicalCheckerContext<'_>) {
        let source = context.source_file(SOURCE).unwrap();
        assert!(
            context
                .store()
                .source_file_links(source)
                .is_none_or(|links| !links.type_checked)
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn cold_exported_helpers_use_exact_thresholds_and_reuse_storage() {
        let lib = library();
        let source = parsed(concat!(
            "declare class Unchecked { value: MissingClassType; }\n",
            "export declare function get(a: number, b: number, c: number, d: number): MissingReturnType;\n",
            "export declare function set(a: number, b: number, c: number, d: number, e: number): void;\n",
            "export declare function oldGet(a: number, b: number, c: number): void;\n",
            "export declare function oldSet(a: number, b: number, c: number, d: number): void;\n",
        ));
        let mut context = context(&lib, &source, true);
        for (name, arity, expected) in [
            ("get", 3, true),
            ("set", 4, true),
            ("oldGet", 3, false),
            ("oldSet", 4, false),
        ] {
            let symbol = symbol(&context, &source, name);
            assert!(context.store().value_symbol_links(symbol).is_none());
            assert_eq!(
                context.has_call_signature_with_arity_greater_than(symbol, arity),
                Ok(expected),
                "{name}"
            );
            let before = counts(&context);
            assert_eq!(
                context.has_call_signature_with_arity_greater_than(symbol, arity),
                Ok(expected)
            );
            assert_eq!(counts(&context), before);
            let type_ = context
                .store()
                .value_symbol_links(symbol)
                .unwrap()
                .resolved_type
                .unwrap();
            let signature = context
                .store()
                .source_callable_provenance(type_)
                .unwrap()
                .signature;
            assert!(
                context
                    .store()
                    .signature(signature)
                    .unwrap()
                    .resolved_return_type()
                    .is_none()
            );
        }
        assert_unchecked(&context);
    }

    #[test]
    fn non_callable_export_is_false_without_checking_the_file() {
        let lib = library();
        let source = parsed("export declare const get: number;");
        let mut context = context(&lib, &source, true);
        let symbol = symbol(&context, &source, "get");
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(symbol, 3),
            Ok(false)
        );
        let before = counts(&context);
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(symbol, 0),
            Ok(false)
        );
        assert_eq!(counts(&context), before);
        assert_unchecked(&context);
    }

    #[test]
    fn generic_optional_parameters_do_not_force_the_return() {
        let lib = library();
        let source = parsed("export declare function get<T>(a: T, b?: T, c?: T, d?: T): T;");
        let mut context = context(&lib, &source, true);
        let symbol = symbol(&context, &source, "get");
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(symbol, 3),
            Ok(true)
        );
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(symbol, 4),
            Ok(false)
        );
        let type_ = context
            .store()
            .value_symbol_links(symbol)
            .unwrap()
            .resolved_type
            .unwrap();
        let signature = context
            .store()
            .source_callable_provenance(type_)
            .unwrap()
            .signature;
        let signature = context.store().signature(signature).unwrap();
        assert_eq!(signature.type_parameters().len(), 1);
        assert!(signature.resolved_return_type().is_none());
        assert_unchecked(&context);
    }

    #[test]
    fn tuple_rest_expands_but_array_rest_is_one_position() {
        let lib = library();
        let source = parsed(concat!(
            "declare function tupleRest(prefix: number, ...tail: [number, number, number]): void;\n",
            "declare function arrayRest(prefix: number, ...tail: number[]): void;\n",
        ));
        let mut context = context(&lib, &source, false);
        let tuple = symbol(&context, &source, "tupleRest");
        let array = symbol(&context, &source, "arrayRest");
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(tuple, 3),
            Ok(true)
        );
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(tuple, 4),
            Ok(false)
        );
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(array, 1),
            Ok(true)
        );
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(array, 2),
            Ok(false)
        );
        let before = counts(&context);
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(tuple, 3),
            Ok(true)
        );
        assert_eq!(counts(&context), before);
        assert_unchecked(&context);
    }

    #[test]
    fn a_later_warm_overload_can_supply_the_required_arity() {
        let lib = library();
        let source = parsed(concat!(
            "declare function get(a: number): void;\n",
            "declare function get(a: number, b: number, c: number, d: number): void;\n",
        ));
        let mut context = context(&lib, &source, false);
        let symbol = symbol(&context, &source, "get");
        context.check_source_file(SOURCE).unwrap();
        let source_root = context.source_file(SOURCE).unwrap();
        let source_links = context.store().source_file_links(source_root).cloned();
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(symbol, 3),
            Ok(true)
        );
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(symbol, 4),
            Ok(false)
        );
        let before = counts(&context);
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(symbol, 3),
            Ok(true)
        );
        assert_eq!(counts(&context), before);
        assert_eq!(
            context.store().source_file_links(source_root).cloned(),
            source_links
        );
    }

    #[test]
    fn overload_return_demand_stays_unavailable_without_publication() {
        let lib = library();
        let source = parsed(concat!(
            "declare function get(a: number): Missing;\n",
            "declare function get(a: number, b: number, c: number, d: number): Missing;\n",
        ));
        let mut context = context(&lib, &source, false);
        let symbol = symbol(&context, &source, "get");
        let before = counts(&context);
        for _ in 0..2 {
            assert!(matches!(
                context.has_call_signature_with_arity_greater_than(symbol, 3),
                Err(CanonicalHelperSignatureError::ProviderUnavailable { .. })
            ));
            assert_eq!(counts(&context), before);
            assert!(
                context
                    .store()
                    .source_overload_type_for_owner(symbol)
                    .is_none()
            );
        }
        assert_unchecked(&context);
    }

    #[test]
    fn explicit_this_requires_its_existing_provider_and_is_not_counted_as_a_fallback() {
        let lib = library();
        let source =
            parsed("declare function get(this: number, a: number, b: number, c: number): void;");
        let mut context = context(&lib, &source, false);
        let symbol = symbol(&context, &source, "get");
        let before = counts(&context);
        assert!(matches!(
            context.has_call_signature_with_arity_greater_than(symbol, 3),
            Err(CanonicalHelperSignatureError::DeclaredType(_))
        ));
        assert_eq!(counts(&context), before);
        assert!(
            context
                .store()
                .source_callable_type_for_owner(symbol)
                .is_none()
        );
        assert_unchecked(&context);
    }

    #[test]
    fn an_existing_alias_resolution_supplies_the_exact_value_symbol() {
        let lib = library();
        let source = parsed(concat!(
            "declare function helper(a: number, b: number, c: number, d: number): void;\n",
            "export { helper as get };\n",
        ));
        let mut context = context(&lib, &source, true);
        let alias = symbol(&context, &source, "get");
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(alias, 3),
            Err(CanonicalHelperSignatureError::UnresolvedAlias(alias))
        );
        let AliasTargetState::Resolved(target) = context.resolve_alias(alias).unwrap().target
        else {
            panic!("expected the existing local alias resolver")
        };
        assert_eq!(target, symbol(&context, &source, "helper"));
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(target, 3),
            Ok(true)
        );
        assert_unchecked(&context);
    }

    #[test]
    fn a_poisoned_value_cache_fails_then_retries_without_fabricated_callables() {
        let lib = library();
        let source =
            parsed("declare function get(a: number, b: number, c: number, d: number): void;");
        let mut context = context(&lib, &source, false);
        let symbol = symbol(&context, &source, "get");
        let wrong = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(wrong),
                ..ValueSymbolLinks::default()
            }
        ));
        let before = counts(&context);
        assert!(
            context
                .has_call_signature_with_arity_greater_than(symbol, 3)
                .is_err()
        );
        assert_eq!(counts(&context), before);
        assert!(
            context
                .store()
                .source_callable_type_for_owner(symbol)
                .is_none()
        );
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(symbol, ValueSymbolLinks::default())
        );
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(symbol, 3),
            Ok(true)
        );
        assert_unchecked(&context);
    }

    #[test]
    fn a_poisoned_callable_variable_does_not_materialize_its_annotation() {
        let lib = library();
        let source = parsed(
            "export declare const get: (a: number, b: number, c: number, d: number) => void;",
        );
        let mut context = context(&lib, &source, true);
        let symbol = symbol(&context, &source, "get");
        let wrong = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(wrong),
                ..ValueSymbolLinks::default()
            }
        ));
        let before = counts(&context);
        assert!(
            context
                .has_call_signature_with_arity_greater_than(symbol, 3)
                .is_err()
        );
        assert_eq!(counts(&context), before);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(symbol, ValueSymbolLinks::default())
        );
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(symbol, 3),
            Ok(true)
        );
        assert_unchecked(&context);
    }

    #[test]
    fn foreign_symbols_are_typed_errors() {
        let lib = library();
        let source = parsed("declare function get(a: number): void;");
        let mut context = context(&lib, &source, false);
        let foreign = super::tests::context(&lib, &source, false);
        let symbol = symbol(&foreign, &source, "get");
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(symbol, 0),
            Err(CanonicalHelperSignatureError::InvalidSymbol(symbol))
        );
        assert_unchecked(&context);
    }

    #[test]
    fn a_cold_source_body_is_not_checked_to_answer_helper_arity() {
        let lib = library();
        let source = parsed(
            "function get(a: number, b: number, c: number, d: number): number { return missing; }",
        );
        let mut context = context_with_source_kind(&lib, &source, false, false);
        let symbol = symbol(&context, &source, "get");
        let before = counts(&context);
        assert!(matches!(
            context.has_call_signature_with_arity_greater_than(symbol, 3),
            Err(CanonicalHelperSignatureError::ProviderUnavailable { .. })
        ));
        assert_eq!(counts(&context), before);
        assert!(
            context
                .store()
                .source_callable_type_for_owner(symbol)
                .is_none()
        );
        assert_unchecked(&context);
    }

    #[test]
    fn a_corrupt_warm_signature_parameter_cache_fails_without_republication() {
        let lib = library();
        let source =
            parsed("declare function get(a: number, b: number, c: number, d: number): void;");
        let mut context = context(&lib, &source, false);
        let symbol = symbol(&context, &source, "get");
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(symbol, 3),
            Ok(true)
        );
        let type_ = context
            .store()
            .value_symbol_links(symbol)
            .unwrap()
            .resolved_type
            .unwrap();
        let signature = context
            .store()
            .source_callable_provenance(type_)
            .unwrap()
            .signature;
        let parameter = context.store().signature(signature).unwrap().parameters()[0];
        let saved = context
            .store()
            .value_symbol_links(parameter)
            .unwrap()
            .clone();
        let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            parameter,
            ValueSymbolLinks {
                resolved_type: Some(wrong),
                ..ValueSymbolLinks::default()
            }
        ));
        let before = counts(&context);
        assert!(
            context
                .has_call_signature_with_arity_greater_than(symbol, 3)
                .is_err()
        );
        assert_eq!(counts(&context), before);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(parameter, saved)
        );
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(symbol, 3),
            Ok(true)
        );
        assert_eq!(counts(&context), before);
        assert_unchecked(&context);
    }

    #[test]
    fn stale_source_identity_is_rejected_before_a_helper_context_can_be_used() {
        let lib = library();
        let mut source = parsed("declare function get(a: number): void;");
        let bindings = bindings(&lib, &source, false, true);
        let expected = bindings.file(SOURCE).unwrap().node_arena_revision();
        let declaration = declaration(&source, "get");
        source.arena.get_mut(declaration).unwrap().parent = None;
        let actual = source.arena.revision();
        let error = CanonicalCheckerContext::new(
            bindings,
            vec![(LIBRARY, &lib.arena), (SOURCE, &source.arena)],
            CanonicalCheckerOptions::default(),
        )
        .unwrap_err();
        assert_eq!(
            error,
            crate::semantic::CanonicalCheckerContextError::ArenaRevisionMismatch {
                file: SOURCE,
                expected,
                actual,
            }
        );
    }

    #[test]
    fn unsupported_exported_overloads_are_not_reported_as_old_helpers() {
        let lib = library();
        let source = parsed(concat!(
            "export declare function get(a: number): void;\n",
            "export declare function get(a: number, b: number, c: number, d: number): void;\n",
        ));
        let mut context = context(&lib, &source, true);
        let symbol = symbol(&context, &source, "get");
        let before = counts(&context);
        assert!(matches!(
            context.has_call_signature_with_arity_greater_than(symbol, 3),
            Err(CanonicalHelperSignatureError::ProviderUnavailable { .. })
        ));
        assert_eq!(counts(&context), before);
        assert!(
            context
                .store()
                .source_overload_type_for_owner(symbol)
                .is_none()
        );
        assert_unchecked(&context);
    }

    #[test]
    fn a_poisoned_overload_sibling_rejects_an_earlier_wide_signature() {
        let lib = library();
        let source = parsed(concat!(
            "declare function get(a: number, b: number, c: number, d: number): void;\n",
            "declare function get(a: number): void;\n",
        ));
        let mut context = context(&lib, &source, false);
        context.check_source_file(SOURCE).unwrap();
        let symbol = symbol(&context, &source, "get");
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(symbol, 3),
            Ok(true)
        );
        let type_ = context
            .store()
            .value_symbol_links(symbol)
            .unwrap()
            .resolved_type
            .unwrap();
        let projection = match crate::semantic::callable_sets::validate_stored_callable_set(
            context.store(),
            type_,
        ) {
            crate::semantic::callable_sets::StoredCallableSetValidation::Valid {
                projection,
                ..
            } => projection,
            other => panic!("expected authenticated overloads: {other:?}"),
        };
        let parameter = context
            .store()
            .signature(projection.call_signatures[1].signature)
            .unwrap()
            .parameters()[0];
        let saved = context
            .store()
            .value_symbol_links(parameter)
            .unwrap()
            .clone();
        let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            parameter,
            ValueSymbolLinks {
                resolved_type: Some(wrong),
                ..ValueSymbolLinks::default()
            }
        ));
        let before = counts(&context);
        assert!(matches!(
            context.has_call_signature_with_arity_greater_than(symbol, 3),
            Err(CanonicalHelperSignatureError::InvalidCallable { .. })
        ));
        assert_eq!(counts(&context), before);
        assert!(
            context
                .store_mut_for_test()
                .set_value_symbol_links(parameter, saved)
        );
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(symbol, 3),
            Ok(true)
        );
        assert_eq!(counts(&context), before);
    }

    #[test]
    fn cold_keyword_parameter_cache_rejection_does_not_publish_a_callable() {
        let lib = library();
        let source =
            parsed("declare function get(a: number, b: number, c: number, d: number): void;");
        let mut context = context(&lib, &source, false);
        let symbol = symbol(&context, &source, "get");
        let NodeData::FunctionDeclaration(function) =
            &source.arena.get(declaration(&source, "get")).unwrap().data
        else {
            panic!("expected helper function")
        };
        let NodeData::ParameterDeclaration(parameter) =
            &source.arena.get(function.parameters.nodes[0]).unwrap().data
        else {
            panic!("expected helper parameter")
        };
        let annotation = NodeRef::new(source.arena.id(), SOURCE, parameter.type_.unwrap());
        let wrong = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(context.store_mut_for_test().set_type_node_links(
            annotation,
            TypeNodeLinks {
                resolved_type: Some(wrong),
                ..TypeNodeLinks::default()
            }
        ));
        let before = counts(&context);
        assert!(
            context
                .has_call_signature_with_arity_greater_than(symbol, 3)
                .is_err()
        );
        assert_eq!(counts(&context), before);
        assert!(
            context
                .store()
                .source_callable_type_for_owner(symbol)
                .is_none()
        );
        assert!(context.store().value_symbol_links(symbol).is_none());
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(annotation, TypeNodeLinks::default())
        );
        assert_eq!(
            context.has_call_signature_with_arity_greater_than(symbol, 3),
            Ok(true)
        );
        assert_unchecked(&context);
    }
}
