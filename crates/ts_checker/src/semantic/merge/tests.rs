use ts_ast::{FileId, NodeRef, SyntaxKind};
use ts_binder::{
    AstScope, CheckFlags, EscapedName, SemanticSymbolId, SymbolData, SymbolFlags, SymbolTableId,
};
use ts_parser::parse_source_file;

use super::{
    CheckerDiagnosticMergeHost, SymbolMergeDiagnostic, SymbolMergeDiagnosticKind, SymbolMergeError,
    SymbolMergeHost, get_excluded_symbol_flags,
};
use crate::semantic::{
    CanonicalCheckerDiagnostics, CanonicalTypeMapperStore, IntrinsicBootstrapError,
    IntrinsicBootstrapOptions, SemanticStore,
};

type Store = CanonicalTypeMapperStore;

fn alloc(store: &mut Store, flags: SymbolFlags, name: &str) -> SemanticSymbolId {
    store
        .alloc_symbol(SymbolData::new(flags, EscapedName::source(name)))
        .unwrap()
}

fn transient(store: &mut Store, flags: SymbolFlags, name: &str) -> SemanticSymbolId {
    store.alloc_transient_symbol(flags, EscapedName::source(name), CheckFlags::NONE)
}

fn table_with(
    store: &mut Store,
    entries: impl IntoIterator<Item = (&'static str, SemanticSymbolId)>,
) -> SymbolTableId {
    let table = store.alloc_symbol_table();
    for (name, symbol) in entries {
        assert_eq!(
            store.insert_symbol(table, EscapedName::source(name), symbol),
            Some(None)
        );
    }
    table
}

fn registered_nodes(store: &mut Store, file: u32, text: &str) -> Vec<(SyntaxKind, NodeRef)> {
    let parsed = parse_source_file(text);
    let file = FileId::new(file);
    assert!(
        store
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .is_some()
    );
    parsed
        .arena
        .iter()
        .map(|(node, data)| (data.kind, NodeRef::new(parsed.arena.id(), file, node)))
        .collect()
}

fn first(nodes: &[(SyntaxKind, NodeRef)], kind: SyntaxKind) -> NodeRef {
    nodes
        .iter()
        .find_map(|(candidate, node)| (*candidate == kind).then_some(*node))
        .unwrap_or_else(|| panic!("fixture has no {kind:?}"))
}

#[test]
fn excluded_flags_match_every_dynamic_pinned_branch() {
    let cases = [
        (
            SymbolFlags::BLOCK_SCOPED_VARIABLE,
            SymbolFlags::BLOCK_SCOPED_VARIABLE_EXCLUDES,
        ),
        (
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
            SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES,
        ),
        (SymbolFlags::PROPERTY, SymbolFlags::PROPERTY_EXCLUDES),
        (SymbolFlags::ENUM_MEMBER, SymbolFlags::ENUM_MEMBER_EXCLUDES),
        (SymbolFlags::FUNCTION, SymbolFlags::FUNCTION_EXCLUDES),
        (SymbolFlags::CLASS, SymbolFlags::CLASS_EXCLUDES),
        (SymbolFlags::INTERFACE, SymbolFlags::INTERFACE_EXCLUDES),
        (
            SymbolFlags::REGULAR_ENUM,
            SymbolFlags::REGULAR_ENUM_EXCLUDES,
        ),
        (SymbolFlags::CONST_ENUM, SymbolFlags::CONST_ENUM_EXCLUDES),
        (
            SymbolFlags::VALUE_MODULE,
            SymbolFlags::VALUE_MODULE_EXCLUDES,
        ),
        (SymbolFlags::METHOD, SymbolFlags::METHOD_EXCLUDES),
        (
            SymbolFlags::GET_ACCESSOR,
            SymbolFlags::GET_ACCESSOR_EXCLUDES,
        ),
        (
            SymbolFlags::SET_ACCESSOR,
            SymbolFlags::SET_ACCESSOR_EXCLUDES,
        ),
        (
            SymbolFlags::TYPE_PARAMETER,
            SymbolFlags::TYPE_PARAMETER_EXCLUDES,
        ),
        (SymbolFlags::TYPE_ALIAS, SymbolFlags::TYPE_ALIAS_EXCLUDES),
        (SymbolFlags::ALIAS, SymbolFlags::ALIAS_EXCLUDES),
    ];
    for (flag, expected) in cases {
        assert_eq!(get_excluded_symbol_flags(flag), expected, "{flag:?}");
    }
    assert_eq!(
        get_excluded_symbol_flags(SymbolFlags::NAMESPACE_MODULE),
        SymbolFlags::NONE
    );
    assert_eq!(
        get_excluded_symbol_flags(SymbolFlags::PROPERTY | SymbolFlags::REPLACEABLE_BY_METHOD),
        SymbolFlags::PROPERTY_EXCLUDES.without(SymbolFlags::METHOD)
    );
    assert_eq!(
        get_excluded_symbol_flags(SymbolFlags::REPLACEABLE_BY_METHOD),
        SymbolFlags::NONE
    );
}

#[test]
fn redirects_are_one_hop_overwritable_and_cycle_safe() {
    let mut store = Store::new();
    let a = alloc(&mut store, SymbolFlags::INTERFACE, "a");
    let b = alloc(&mut store, SymbolFlags::INTERFACE, "b");
    let c = alloc(&mut store, SymbolFlags::INTERFACE, "c");
    let child = alloc(&mut store, SymbolFlags::PROPERTY, "child");
    assert!(store.set_symbol_relationships(child, None, None, Some(a), None));

    assert_eq!(store.record_merged_symbol(b, a), Ok(None));
    assert_eq!(store.record_merged_symbol(c, b), Ok(None));
    assert_eq!(store.get_merged_symbol(a), Some(b));
    assert_eq!(store.get_merged_symbol(b), Some(c));
    assert_eq!(store.get_parent_of_symbol(child), Some(b));
    assert_eq!(store.merged_symbol_len(), 2);

    assert_eq!(store.record_merged_symbol(c, a), Ok(Some(b)));
    assert_eq!(store.get_merged_symbol(a), Some(c));
    let before = store.merged_symbol_len();
    assert!(matches!(
        store.record_merged_symbol(a, c),
        Err(super::MergedSymbolRecordError::RedirectCycle {
            source,
            target
        }) if source == c && target == a
    ));
    assert_eq!(store.get_merged_symbol(c), Some(c));
    assert_eq!(store.get_merged_symbol(a), Some(c));
    assert_eq!(store.merged_symbol_len(), before);
    assert!(matches!(
        store.record_merged_symbol(a, a),
        Err(super::MergedSymbolRecordError::SelfRedirect(symbol)) if symbol == a
    ));
    assert_eq!(store.get_merged_symbol(a), Some(c));
}

#[test]
fn redirects_reject_foreign_provenance_before_mutation() {
    let mut store = Store::new();
    let local = alloc(&mut store, SymbolFlags::INTERFACE, "local");
    let mut foreign_store = Store::new();
    let foreign = alloc(&mut foreign_store, SymbolFlags::INTERFACE, "foreign");
    assert_eq!(store.get_merged_symbol(foreign), None);
    assert!(matches!(
        store.record_merged_symbol(foreign, local),
        Err(super::MergedSymbolRecordError::InvalidTarget(symbol)) if symbol == foreign
    ));
    assert!(matches!(
        store.record_merged_symbol(local, foreign),
        Err(super::MergedSymbolRecordError::InvalidSource(symbol)) if symbol == foreign
    ));
    assert_eq!(store.merged_symbol_len(), 0);
    assert_eq!(store.get_merged_symbol(local), Some(local));
}

#[test]
fn redirects_make_prebootstrap_checker_state_non_pristine() {
    let mut store = Store::new();
    let target = alloc(&mut store, SymbolFlags::INTERFACE, "target");
    let source = alloc(&mut store, SymbolFlags::INTERFACE, "source");
    assert_eq!(store.record_merged_symbol(target, source), Ok(None));
    let error = store
        .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
        .unwrap_err();
    let IntrinsicBootstrapError::NonPristineCheckerState(snapshot) = error else {
        panic!("redirects must reject first bootstrap as non-pristine");
    };
    assert_eq!(snapshot.merged_symbols, 1);
    assert_eq!(snapshot.checker_symbols, 0);
    assert!(store.intrinsic_bootstrap().is_none());
}

#[test]
fn clone_symbol_is_shallow_transient_and_preserves_nil_shape() {
    let mut store = Store::new();
    let nodes = registered_nodes(&mut store, 1, "interface A {}\nconst value = 1;");
    let declaration = first(&nodes, SyntaxKind::InterfaceDeclaration);
    let value = first(&nodes, SyntaxKind::VariableDeclaration);
    let parent = alloc(&mut store, SymbolFlags::NAMESPACE_MODULE, "parent");
    let export_symbol = alloc(&mut store, SymbolFlags::INTERFACE, "export");
    let child = alloc(&mut store, SymbolFlags::PROPERTY, "child");
    let members = table_with(&mut store, [("child", child)]);
    let exports = store.alloc_symbol_table();
    let mut data = SymbolData::new(SymbolFlags::INTERFACE, EscapedName::source("A"));
    data.declarations = Some(vec![declaration]);
    data.value_declaration = Some(value);
    data.members = Some(members);
    data.exports = Some(exports);
    data.parent = Some(parent);
    data.export_symbol = Some(export_symbol);
    let original = store.alloc_symbol(data).unwrap();
    let original_global_id = store.global_symbol_id(original).unwrap();

    let cloned = store.clone_symbol(original).unwrap();
    let record = store.symbol(cloned).unwrap();
    assert!(record.flags().intersects(SymbolFlags::INTERFACE));
    assert!(record.flags().intersects(SymbolFlags::TRANSIENT));
    assert_eq!(record.check_flags(), CheckFlags::NONE);
    assert_eq!(record.declarations(), Some([declaration].as_slice()));
    assert_eq!(record.value_declaration(), Some(value));
    assert_eq!(record.parent(), Some(parent));
    assert_eq!(record.export_symbol(), None);
    let cloned_members = record.members().unwrap();
    let cloned_exports = record.exports().unwrap();
    assert_ne!(cloned_members, members);
    assert_ne!(cloned_exports, exports);
    assert_eq!(
        store
            .symbol_table(cloned_members)
            .unwrap()
            .get_source("child"),
        Some(child)
    );
    assert!(store.symbol_table(cloned_exports).unwrap().is_empty());
    assert_eq!(store.get_merged_symbol(original), Some(cloned));
    assert_ne!(store.global_symbol_id(cloned).unwrap(), original_global_id);

    let cloned_only_member = alloc(&mut store, SymbolFlags::PROPERTY, "cloned-only-member");
    let cloned_only_export = alloc(&mut store, SymbolFlags::INTERFACE, "ClonedOnlyExport");
    assert_eq!(
        store.insert_symbol(
            cloned_members,
            EscapedName::source("cloned-only-member"),
            cloned_only_member,
        ),
        Some(None)
    );
    assert_eq!(
        store.insert_symbol(
            cloned_exports,
            EscapedName::source("ClonedOnlyExport"),
            cloned_only_export,
        ),
        Some(None)
    );
    assert_eq!(
        store
            .symbol_table(members)
            .unwrap()
            .get_source("cloned-only-member"),
        None
    );
    assert_eq!(
        store
            .symbol_table(exports)
            .unwrap()
            .get_source("ClonedOnlyExport"),
        None
    );

    let nil = alloc(&mut store, SymbolFlags::INTERFACE, "Nil");
    let nil_clone = store.clone_symbol(nil).unwrap();
    assert_eq!(store.symbol(nil_clone).unwrap().members(), None);
    assert_eq!(store.symbol(nil_clone).unwrap().exports(), None);

    let flagged = store.alloc_transient_symbol(
        SymbolFlags::PROPERTY,
        EscapedName::source("flagged"),
        CheckFlags::LATE,
    );
    assert_eq!(
        store.symbol(flagged).unwrap().check_flags(),
        CheckFlags::LATE
    );
    let flagged_clone = store.clone_symbol(flagged).unwrap();
    assert_eq!(
        store.symbol(flagged_clone).unwrap().check_flags(),
        CheckFlags::NONE
    );
}

#[test]
fn merge_clones_bound_target_appends_in_order_and_uses_shared_value_precedence() {
    let mut store = Store::new();
    let nodes = registered_nodes(&mut store, 1, "namespace Item {}\nfunction Item() {}");
    let module = first(&nodes, SyntaxKind::ModuleDeclaration);
    let function = first(&nodes, SyntaxKind::FunctionDeclaration);
    let mut target_data = SymbolData::new(
        SymbolFlags::VALUE_MODULE | SymbolFlags::CONST_ENUM_ONLY_MODULE,
        EscapedName::source("Item"),
    );
    target_data.declarations = Some(vec![module]);
    target_data.value_declaration = Some(module);
    let target = store.alloc_symbol(target_data).unwrap();
    let mut source_data = SymbolData::new(SymbolFlags::FUNCTION, EscapedName::source("Item"));
    source_data.declarations = Some(vec![function, function]);
    source_data.value_declaration = Some(function);
    let source = store.alloc_symbol(source_data).unwrap();

    let merged = store.merge_symbol(target, source, false).unwrap();
    assert_ne!(merged, target);
    let record = store.symbol(merged).unwrap();
    assert!(record.flags().intersects(SymbolFlags::TRANSIENT));
    assert!(record.flags().intersects(SymbolFlags::VALUE_MODULE));
    assert!(record.flags().intersects(SymbolFlags::FUNCTION));
    // Checker merge clears this marker only when both inputs are value
    // modules. Binder-local function/class merging owns its separate reset.
    assert!(
        record
            .flags()
            .intersects(SymbolFlags::CONST_ENUM_ONLY_MODULE)
    );
    assert_eq!(record.value_declaration(), Some(function));
    assert_eq!(
        record.declarations(),
        Some([module, function, function].as_slice())
    );
    assert_eq!(store.get_merged_symbol(target), Some(merged));
    assert_eq!(store.get_merged_symbol(source), Some(merged));
}

#[test]
fn value_declaration_none_short_circuits_unregistered_kind_lookup() {
    let mut store = Store::new();
    let parsed = parse_source_file("incoming = 1;");
    let file = FileId::new(1);
    assert!(store.register_ast_scope(AstScope::new(file, &parsed.arena)));
    let incoming = parsed
        .arena
        .iter()
        .find_map(|(node, data)| {
            (data.kind == SyntaxKind::BinaryExpression).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .unwrap();
    let target = transient(&mut store, SymbolFlags::FUNCTION, "item");
    let mut source_data = SymbolData::new(SymbolFlags::FUNCTION, EscapedName::source("item"));
    source_data.value_declaration = Some(incoming);
    let source = store.alloc_symbol(source_data).unwrap();

    let merged = store.merge_symbol(target, source, false).unwrap();
    assert_eq!(merged, target);
    assert_eq!(
        store.symbol(merged).unwrap().value_declaration(),
        Some(incoming)
    );
}

#[test]
fn existing_value_declaration_requires_registered_kinds_before_replacement() {
    let mut store = Store::new();
    let parsed = parse_source_file("current = 0; incoming = 1;");
    let file = FileId::new(1);
    assert!(store.register_ast_scope(AstScope::new(file, &parsed.arena)));
    let binary = parsed
        .arena
        .iter()
        .filter_map(|(node, data)| {
            (data.kind == SyntaxKind::BinaryExpression).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .collect::<Vec<_>>();
    let target = transient(&mut store, SymbolFlags::FUNCTION, "item");
    assert!(store.set_symbol_declarations(target, None, Some(binary[0])));
    let mut source_data = SymbolData::new(SymbolFlags::FUNCTION, EscapedName::source("item"));
    source_data.value_declaration = Some(binary[1]);
    let source = store.alloc_symbol(source_data).unwrap();

    assert_eq!(
        store.merge_symbol(target, source, false),
        Err(SymbolMergeError::MissingValueDeclarationKind(binary[0]))
    );
    assert_eq!(
        store.symbol(target).unwrap().value_declaration(),
        Some(binary[0])
    );
}

#[test]
fn assignment_flags_force_merge_across_normal_exclusions() {
    let mut store = Store::new();
    let target = transient(&mut store, SymbolFlags::CLASS, "item");
    let source = alloc(
        &mut store,
        SymbolFlags::BLOCK_SCOPED_VARIABLE | SymbolFlags::ASSIGNMENT,
        "item",
    );
    let merged = store.merge_symbol(target, source, false).unwrap();
    assert_eq!(merged, target);
    let flags = store.symbol(merged).unwrap().flags();
    assert!(flags.intersects(SymbolFlags::CLASS));
    assert!(flags.intersects(SymbolFlags::BLOCK_SCOPED_VARIABLE));
    assert!(flags.intersects(SymbolFlags::ASSIGNMENT));
}

#[test]
fn unidirectional_merge_keeps_source_unredirected_but_clones_target() {
    let mut store = Store::new();
    let target = alloc(&mut store, SymbolFlags::INTERFACE, "item");
    let source = alloc(&mut store, SymbolFlags::INTERFACE, "item");
    let merged = store.merge_symbol(target, source, true).unwrap();
    assert_ne!(merged, target);
    assert_eq!(store.get_merged_symbol(target), Some(merged));
    assert_eq!(store.get_merged_symbol(source), Some(source));
}

#[test]
fn self_merge_is_an_exact_noop_without_redirect() {
    let mut store = Store::new();
    let symbol = alloc(&mut store, SymbolFlags::INTERFACE, "item");
    let before = store.symbol(symbol).unwrap().clone();
    assert_eq!(store.merge_symbol(symbol, symbol, false), Ok(symbol));
    assert_eq!(store.symbol(symbol), Some(&before));
    assert_eq!(store.merged_symbol_len(), 0);
}

#[test]
fn unsupported_alias_and_diagnostic_branches_fail_typed() {
    let mut store = Store::new();
    let alias = alloc(&mut store, SymbolFlags::ALIAS, "item");
    let namespace = alloc(&mut store, SymbolFlags::NAMESPACE_MODULE, "item");
    let before_symbols = store.symbol_len();
    assert_eq!(
        store.merge_symbol(alias, namespace, false),
        Err(SymbolMergeError::AliasResolutionRequired(alias))
    );
    assert_eq!(store.symbol_len(), before_symbols);
    assert_eq!(store.merged_symbol_len(), 0);

    let block = alloc(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "conflict");
    let function = alloc(&mut store, SymbolFlags::FUNCTION, "conflict");
    assert_eq!(
        store.merge_symbol(block, function, false),
        Err(SymbolMergeError::DiagnosticRequired {
            kind: SymbolMergeDiagnosticKind::IncompatibleDeclarations,
            target: block,
            source: function,
        })
    );

    let module = alloc(
        &mut store,
        SymbolFlags::NAMESPACE_MODULE | SymbolFlags::BLOCK_SCOPED_VARIABLE,
        "module",
    );
    let property = alloc(&mut store, SymbolFlags::FUNCTION, "module");
    assert_eq!(
        store.merge_symbol(module, property, false),
        Err(SymbolMergeError::DiagnosticRequired {
            kind: SymbolMergeDiagnosticKind::CannotAugmentNonModule,
            target: module,
            source: property,
        })
    );
}

#[test]
fn hosted_duplicate_diagnostics_continue_and_deduplicate_in_declaration_order() {
    let mut store = Store::new();
    let nodes = registered_nodes(&mut store, 1, "let item = 1; let item = 2;");
    let declarations = nodes
        .iter()
        .filter_map(|(kind, node)| (*kind == SyntaxKind::VariableDeclaration).then_some(*node))
        .collect::<Vec<_>>();
    assert_eq!(declarations.len(), 2);
    let mut target_data = SymbolData::new(
        SymbolFlags::BLOCK_SCOPED_VARIABLE,
        EscapedName::source("item"),
    );
    target_data.declarations = Some(vec![declarations[0]]);
    let target = store.alloc_symbol(target_data).unwrap();
    let mut source_data = SymbolData::new(
        SymbolFlags::BLOCK_SCOPED_VARIABLE,
        EscapedName::source("item"),
    );
    source_data.declarations = Some(vec![declarations[1]]);
    let source = store.alloc_symbol(source_data).unwrap();
    let mut diagnostics = CanonicalCheckerDiagnostics::default();

    {
        let mut host = CheckerDiagnosticMergeHost::new(&mut diagnostics);
        assert_eq!(
            store.merge_symbol_with_host(&mut host, target, source, false),
            Ok(target)
        );
        assert_eq!(
            store.merge_symbol_with_host(&mut host, target, source, false),
            Ok(target)
        );
    }

    assert_eq!(diagnostics.len(), 2);
    assert_eq!(diagnostics.as_slice()[0].node, Some(declarations[1]));
    assert_eq!(diagnostics.as_slice()[1].node, Some(declarations[0]));
    for (index, related_node) in [declarations[0], declarations[1]].into_iter().enumerate() {
        let diagnostic = &diagnostics.as_slice()[index];
        assert_eq!(diagnostic.diagnostic.code(), 2451);
        assert_eq!(diagnostic.diagnostic.arguments, ["item"]);
        assert_eq!(diagnostic.related_information.len(), 1);
        assert_eq!(diagnostic.related_information[0].node, Some(related_node));
        assert_eq!(diagnostic.related_information[0].diagnostic.code(), 6203);
    }
    assert_eq!(store.get_merged_symbol(target), Some(target));
    assert_eq!(store.get_merged_symbol(source), Some(source));
}

#[test]
fn hosted_nested_collision_keeps_outer_side_effects_and_continues_once() {
    let mut store = Store::new();
    let nodes = registered_nodes(
        &mut store,
        1,
        "interface First {} interface Second {} let child = 1; function child() {}",
    );
    let interfaces = nodes
        .iter()
        .filter_map(|(kind, node)| (*kind == SyntaxKind::InterfaceDeclaration).then_some(*node))
        .collect::<Vec<_>>();
    let variable = first(&nodes, SyntaxKind::VariableDeclaration);
    let function = first(&nodes, SyntaxKind::FunctionDeclaration);
    let mut target_child_data = SymbolData::new(
        SymbolFlags::BLOCK_SCOPED_VARIABLE,
        EscapedName::source("child"),
    );
    target_child_data.declarations = Some(vec![variable]);
    let target_child = store.alloc_symbol(target_child_data).unwrap();
    let mut source_child_data =
        SymbolData::new(SymbolFlags::FUNCTION, EscapedName::source("child"));
    source_child_data.declarations = Some(vec![function]);
    let source_child = store.alloc_symbol(source_child_data).unwrap();
    let target_members = table_with(&mut store, [("child", target_child)]);
    let source_members = table_with(&mut store, [("child", source_child)]);
    let target = transient(&mut store, SymbolFlags::INTERFACE, "Outer");
    assert!(store.set_symbol_declarations(target, Some(vec![interfaces[0]]), None));
    assert!(store.set_symbol_relationships(target, Some(target_members), None, None, None));
    let mut source_data = SymbolData::new(SymbolFlags::INTERFACE, EscapedName::source("Outer"));
    source_data.declarations = Some(vec![interfaces[1]]);
    source_data.members = Some(source_members);
    let source = store.alloc_symbol(source_data).unwrap();
    let mut diagnostics = CanonicalCheckerDiagnostics::default();

    {
        let mut host = CheckerDiagnosticMergeHost::new(&mut diagnostics);
        assert_eq!(
            store.merge_symbol_with_host(&mut host, target, source, false),
            Ok(target)
        );
    }

    assert_eq!(
        store.symbol(target).unwrap().declarations(),
        Some(interfaces.as_slice())
    );
    assert_eq!(
        store
            .symbol_table(target_members)
            .unwrap()
            .get_source("child"),
        Some(target_child)
    );
    assert_eq!(store.get_merged_symbol(source), Some(target));
    assert_eq!(store.get_merged_symbol(source_child), Some(source_child));
    assert_eq!(diagnostics.len(), 2);
    assert_eq!(diagnostics.as_slice()[0].node, Some(function));
    assert_eq!(diagnostics.as_slice()[1].node, Some(variable));
}

#[derive(Debug)]
struct ResolvingMergeHost {
    resolved: SemanticSymbolId,
    alias_requests: Vec<SemanticSymbolId>,
    diagnostics: Vec<SymbolMergeDiagnostic>,
}

impl<TypePayload, MapperPayload> SymbolMergeHost<TypePayload, MapperPayload>
    for ResolvingMergeHost
{
    fn resolve_alias_for_merge(
        &mut self,
        _store: &mut SemanticStore<TypePayload, MapperPayload>,
        symbol: SemanticSymbolId,
    ) -> Result<SemanticSymbolId, SymbolMergeError> {
        self.alias_requests.push(symbol);
        Ok(self.resolved)
    }

    fn report_merge_diagnostic(
        &mut self,
        _store: &SemanticStore<TypePayload, MapperPayload>,
        diagnostic: SymbolMergeDiagnostic,
    ) -> Result<(), SymbolMergeError> {
        self.diagnostics.push(diagnostic);
        Ok(())
    }
}

#[test]
fn hosted_alias_resolution_reports_then_takes_the_source_continuation() {
    let mut store = Store::new();
    let globals = store.alloc_symbol_table();
    let alias = alloc(&mut store, SymbolFlags::ALIAS, "item");
    let resolved = alloc(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "item");
    let source = alloc(&mut store, SymbolFlags::FUNCTION, "item");
    assert_eq!(
        store.insert_symbol(globals, EscapedName::source("item"), alias),
        Some(None)
    );
    let mut host = ResolvingMergeHost {
        resolved,
        alias_requests: Vec::new(),
        diagnostics: Vec::new(),
    };

    assert_eq!(
        store.merge_global_symbol_with_host(&mut host, globals, source),
        Ok(source)
    );
    assert_eq!(host.alias_requests, [alias]);
    assert_eq!(
        host.diagnostics,
        [SymbolMergeDiagnostic {
            kind: SymbolMergeDiagnosticKind::IncompatibleDeclarations,
            target: alias,
            source,
        }]
    );
    assert_eq!(
        store.symbol_table(globals).unwrap().get_source("item"),
        Some(source)
    );
    assert_eq!(store.get_merged_symbol(alias), Some(alias));
    assert_eq!(store.get_merged_symbol(source), Some(source));
}

#[test]
fn hosted_namespace_collision_reports_and_keeps_the_target() {
    let mut store = Store::new();
    let nodes = registered_nodes(&mut store, 1, "function module() {}");
    let declaration = first(&nodes, SyntaxKind::FunctionDeclaration);
    let target = alloc(
        &mut store,
        SymbolFlags::NAMESPACE_MODULE | SymbolFlags::BLOCK_SCOPED_VARIABLE,
        "module",
    );
    let mut source_data = SymbolData::new(SymbolFlags::FUNCTION, EscapedName::source("module"));
    source_data.declarations = Some(vec![declaration]);
    let source = store.alloc_symbol(source_data).unwrap();
    let mut diagnostics = CanonicalCheckerDiagnostics::default();

    {
        let mut host = CheckerDiagnosticMergeHost::new(&mut diagnostics);
        assert_eq!(
            store.merge_symbol_with_host(&mut host, target, source, false),
            Ok(target)
        );
    }

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics.as_slice()[0].node, Some(declaration));
    assert_eq!(diagnostics.as_slice()[0].diagnostic.code(), 2649);
    assert_eq!(diagnostics.as_slice()[0].diagnostic.arguments, ["module"]);
    assert_eq!(store.get_merged_symbol(source), Some(source));
}

#[test]
fn const_enum_only_is_cleared_only_by_a_non_const_value_module() {
    let mut store = Store::new();
    let target = transient(
        &mut store,
        SymbolFlags::VALUE_MODULE | SymbolFlags::CONST_ENUM_ONLY_MODULE,
        "module",
    );
    let source = alloc(&mut store, SymbolFlags::VALUE_MODULE, "module");
    store.merge_symbol(target, source, false).unwrap();
    assert!(
        !store
            .symbol(target)
            .unwrap()
            .flags()
            .intersects(SymbolFlags::CONST_ENUM_ONLY_MODULE)
    );

    let const_target = transient(
        &mut store,
        SymbolFlags::VALUE_MODULE | SymbolFlags::CONST_ENUM_ONLY_MODULE,
        "const-module",
    );
    let const_source = alloc(
        &mut store,
        SymbolFlags::VALUE_MODULE | SymbolFlags::CONST_ENUM_ONLY_MODULE,
        "const-module",
    );
    store
        .merge_symbol(const_target, const_source, false)
        .unwrap();
    assert!(
        store
            .symbol(const_target)
            .unwrap()
            .flags()
            .intersects(SymbolFlags::CONST_ENUM_ONLY_MODULE)
    );
}

#[test]
fn intrinsic_global_this_conflict_is_the_exact_diagnostic_noop_exception() {
    let mut store = Store::new();
    store
        .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
        .unwrap();
    let global_this = store.intrinsic_bootstrap().unwrap().global_this_symbol;
    let before = store.symbol(global_this).unwrap().clone();
    let property = alloc(&mut store, SymbolFlags::PROPERTY, "globalThis");
    let mut diagnostics = CanonicalCheckerDiagnostics::default();
    {
        let mut host = CheckerDiagnosticMergeHost::new(&mut diagnostics);
        assert_eq!(
            store.merge_symbol_with_host(&mut host, global_this, property, false),
            Ok(global_this)
        );
    }
    assert_eq!(store.symbol(global_this), Some(&before));
    assert_eq!(store.get_merged_symbol(property), Some(property));
    assert!(diagnostics.is_empty());
}

#[test]
fn merge_table_recurses_and_rewrites_only_collided_transient_export_parent() {
    let mut store = Store::new();
    let target_parent = transient(&mut store, SymbolFlags::VALUE_MODULE, "target-parent");
    let source_parent = alloc(&mut store, SymbolFlags::VALUE_MODULE, "source-parent");
    let target_a = alloc(&mut store, SymbolFlags::INTERFACE, "A");
    let source_a = alloc(&mut store, SymbolFlags::INTERFACE, "A");
    let source_b = alloc(&mut store, SymbolFlags::INTERFACE, "B");
    assert!(store.set_symbol_relationships(target_a, None, None, Some(target_parent), None,));
    assert!(store.set_symbol_relationships(source_a, None, None, Some(source_parent), None,));
    assert!(store.set_symbol_relationships(source_b, None, None, Some(source_parent), None,));
    let target = table_with(&mut store, [("A", target_a)]);
    let source = table_with(&mut store, [("B", source_b), ("A", source_a)]);

    store
        .merge_symbol_table(target, source, false, Some(target_parent))
        .unwrap();
    let table = store.symbol_table(target).unwrap();
    let merged_a = table.get_source("A").unwrap();
    assert_ne!(merged_a, target_a);
    assert_eq!(
        store.symbol(merged_a).unwrap().parent(),
        Some(target_parent)
    );
    assert_eq!(table.get_source("B"), Some(source_b));
    assert_eq!(
        store.symbol(source_b).unwrap().parent(),
        Some(source_parent)
    );
    assert_eq!(store.get_merged_symbol(target_a), Some(merged_a));
    assert_eq!(store.get_merged_symbol(source_a), Some(merged_a));
}

#[test]
fn nested_members_and_exports_allocate_only_for_nonnil_source_tables() {
    let mut store = Store::new();
    let target = transient(&mut store, SymbolFlags::INTERFACE, "item");
    let member = alloc(&mut store, SymbolFlags::PROPERTY, "member");
    let export = alloc(&mut store, SymbolFlags::INTERFACE, "Export");
    let source_members = table_with(&mut store, [("member", member)]);
    let source_exports = table_with(&mut store, [("Export", export)]);
    let mut source_data = SymbolData::new(SymbolFlags::INTERFACE, EscapedName::source("item"));
    source_data.members = Some(source_members);
    source_data.exports = Some(source_exports);
    let source = store.alloc_symbol(source_data).unwrap();

    store.merge_symbol(target, source, false).unwrap();
    let record = store.symbol(target).unwrap();
    let members = record.members().unwrap();
    let exports = record.exports().unwrap();
    assert_ne!(members, source_members);
    assert_ne!(exports, source_exports);
    assert_eq!(
        store.symbol_table(members).unwrap().get_source("member"),
        Some(member)
    );
    assert_eq!(
        store.symbol_table(exports).unwrap().get_source("Export"),
        Some(export)
    );

    let nil_target = transient(&mut store, SymbolFlags::INTERFACE, "nil");
    let nil_source = alloc(&mut store, SymbolFlags::INTERFACE, "nil");
    store.merge_symbol(nil_target, nil_source, false).unwrap();
    assert_eq!(store.symbol(nil_target).unwrap().members(), None);
    assert_eq!(store.symbol(nil_target).unwrap().exports(), None);
}

#[test]
fn merge_global_uses_existing_redirect_and_collision_kernel() {
    let mut store = Store::new();
    let globals = store.alloc_symbol_table();
    let original = alloc(&mut store, SymbolFlags::INTERFACE, "Item");
    let redirected = store.clone_symbol(original).unwrap();
    assert_eq!(store.merge_global_symbol(globals, original), Ok(redirected));
    assert_eq!(
        store.symbol_table(globals).unwrap().get_source("Item"),
        Some(redirected)
    );

    let source = alloc(&mut store, SymbolFlags::INTERFACE, "Item");
    let merged = store.merge_global_symbol(globals, source).unwrap();
    assert_eq!(merged, redirected);
    assert_eq!(store.get_merged_symbol(source), Some(redirected));
}

#[test]
fn table_merge_order_is_deterministic_by_escaped_bytes() {
    fn run(reverse_source_insertion: bool) -> (u32, u32) {
        let mut store = Store::new();
        let target_a = alloc(&mut store, SymbolFlags::INTERFACE, "a");
        let target_z = alloc(&mut store, SymbolFlags::INTERFACE, "z");
        let source_a = alloc(&mut store, SymbolFlags::INTERFACE, "a");
        let source_z = alloc(&mut store, SymbolFlags::INTERFACE, "z");
        let target = table_with(&mut store, [("z", target_z), ("a", target_a)]);
        let source = if reverse_source_insertion {
            table_with(&mut store, [("z", source_z), ("a", source_a)])
        } else {
            table_with(&mut store, [("a", source_a), ("z", source_z)])
        };
        store
            .merge_symbol_table(target, source, false, None)
            .unwrap();
        let table = store.symbol_table(target).unwrap();
        (
            table.get_source("a").unwrap().get(),
            table.get_source("z").unwrap().get(),
        )
    }

    let forward = run(false);
    let reverse = run(true);
    assert_eq!(forward, reverse);
    assert!(forward.0 < forward.1);
}

#[test]
fn cyclic_member_graphs_fail_with_a_recursion_guard() {
    let mut store = Store::new();
    let target = transient(&mut store, SymbolFlags::INTERFACE, "item");
    let source = alloc(&mut store, SymbolFlags::INTERFACE, "item");
    let target_members = table_with(&mut store, [("self", target)]);
    let source_members = table_with(&mut store, [("self", source)]);
    assert!(store.set_symbol_relationships(target, Some(target_members), None, None, None,));
    assert!(store.set_symbol_relationships(source, Some(source_members), None, None, None,));

    assert_eq!(
        store.merge_symbol(target, source, false),
        Err(SymbolMergeError::RecursiveMerge { target, source })
    );
}

#[test]
fn merge_entry_points_reject_foreign_symbols_tables_and_parents() {
    let mut store = Store::new();
    let local = alloc(&mut store, SymbolFlags::INTERFACE, "local");
    let local_table = table_with(&mut store, [("local", local)]);
    let mut foreign_store = Store::new();
    let foreign = alloc(&mut foreign_store, SymbolFlags::INTERFACE, "foreign");
    let foreign_table = table_with(&mut foreign_store, [("foreign", foreign)]);

    assert_eq!(
        store.merge_symbol(local, foreign, false),
        Err(SymbolMergeError::InvalidSymbol(foreign))
    );
    assert_eq!(
        store.merge_symbol_table(local_table, foreign_table, false, None),
        Err(SymbolMergeError::InvalidTable(foreign_table))
    );
    assert_eq!(
        store.merge_symbol_table(local_table, local_table, false, Some(foreign)),
        Err(SymbolMergeError::InvalidMergedParent(foreign))
    );
    assert_eq!(store.merged_symbol_len(), 0);
}
