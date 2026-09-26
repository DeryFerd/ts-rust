use crate::ls::lsutil::prelude::*;

use crate::frontend::core_binarysearch::binary_search_unique_func;
use crate::frontend::stringutil_ls;
use crate::gostd::collate;

// Port of Go `ls/lsutil/organizeimports.go`.

// PORT: Go `func(a, b string) int` values. Go stores them in slices, maps and
// structs and compares them only with nil; a nil comparer is `None`. The
// unicode comparers are closures, so this is a shared `dyn Fn` (PORTING:
// stored funcs are `Rc<dyn Fn>`).
pub type StringComparer = Rc<dyn Fn(&str, &str) -> i32>;

// PORT: Go `func(s1, s2 *ast.Node) int` values returned to callers.
pub type NodeComparer = Rc<dyn Fn(Node, Node) -> i32>;

// Go: ls/lsutil/organizeimports.go:17 caseInsensitiveOrganizeImportsComparer, caseSensitiveOrganizeImportsComparer, organizeImportsComparers
// PORT: Go package vars. `Rc` is not `Sync`, so they are thread-local; all
// language-service code runs on the dispatch thread.
thread_local! {
    static CASE_INSENSITIVE_ORGANIZE_IMPORTS_COMPARER: Vec<StringComparer> =
        vec![get_organize_imports_ordinal_string_comparer(true)];
    static CASE_SENSITIVE_ORGANIZE_IMPORTS_COMPARER: Vec<StringComparer> =
        vec![get_organize_imports_ordinal_string_comparer(false)];
    static ORGANIZE_IMPORTS_COMPARERS: Vec<StringComparer> = vec![
        CASE_INSENSITIVE_ORGANIZE_IMPORTS_COMPARER.with(|c| c[0].clone()),
        CASE_SENSITIVE_ORGANIZE_IMPORTS_COMPARER.with(|c| c[0].clone()),
    ];
}

// Go: ls/lsutil/organizeimports.go:27 FilterImportDeclarations
// FilterImportDeclarations filters out non-import declarations from a list of statements.
pub fn filter_import_declarations(statements: &[Node]) -> Vec<Node> {
    statements
        .iter()
        .copied()
        .filter(|stmt| stmt.kind() == SyntaxKind::ImportDeclaration)
        .collect()
}

// Go: ls/lsutil/organizeimports.go:34 GetDetectionLists
// GetDetectionLists returns the lists of comparers and type orders to test for organize imports detection.
pub fn get_detection_lists(
    preferences: &UserPreferences,
) -> (Vec<StringComparer>, Vec<OrganizeImportsTypeOrder>) {
    let comparers_to_test: Vec<StringComparer>;
    let type_orders_to_test: Vec<OrganizeImportsTypeOrder>;
    if !preferences.organize_imports_ignore_case.is_unknown() {
        let ignore_case = preferences.organize_imports_ignore_case.is_true();
        comparers_to_test = vec![get_organize_imports_string_comparer(
            preferences,
            ignore_case,
        )];
    } else {
        comparers_to_test = vec![
            get_organize_imports_string_comparer(preferences, true),
            get_organize_imports_string_comparer(preferences, false),
        ];
    }

    if preferences.organize_imports_type_order != OrganizeImportsTypeOrder::AUTO {
        type_orders_to_test = vec![preferences.organize_imports_type_order];
    } else {
        type_orders_to_test = vec![
            OrganizeImportsTypeOrder::LAST,
            OrganizeImportsTypeOrder::INLINE,
            OrganizeImportsTypeOrder::FIRST,
        ];
    }

    (comparers_to_test, type_orders_to_test)
}

// Go: ls/lsutil/organizeimports.go:58 getOrganizeImportsOrdinalStringComparer
fn get_organize_imports_ordinal_string_comparer(ignore_case: bool) -> StringComparer {
    if ignore_case {
        return Rc::new(stringutil_ls::compare_strings_case_insensitive_eslint_compatible);
    }
    Rc::new(stringutil_ls::compare_strings_case_sensitive)
}

// Go: ls/lsutil/organizeimports.go:65 getOrganizeImportsUnicodeStringComparer
// PORT: a Go collator keeps iterator state, so each one is in a `RefCell`.
// `gostd::collate` holds a subset of the Go collation tables; see its module
// note.
fn get_organize_imports_unicode_string_comparer(
    ignore_case: bool,
    preferences: &UserPreferences,
) -> StringComparer {
    let resolved_locale = get_organize_imports_locale(preferences);

    let case_first = preferences.organize_imports_case_first;
    let numeric = preferences.organize_imports_numeric_collation.is_true();
    let accents = !preferences.organize_imports_accent_collation.is_false();

    let (tag, _) = locale::language::parse(&resolved_locale);

    let mut opts: Vec<collate::CollateOption> = Vec::new();

    if numeric {
        opts.push(collate::NUMERIC);
    }

    let mut loose_opts = opts.clone();
    loose_opts.push(collate::LOOSE);
    let loose_collator = RefCell::new(collate::new(&tag, loose_opts));

    if !ignore_case {
        let mut case_insensitive_opts = opts.clone();
        case_insensitive_opts.push(collate::IGNORE_CASE);
        let case_insensitive_collator = RefCell::new(collate::new(&tag, case_insensitive_opts));

        let full_collator = RefCell::new(collate::new(&tag, opts.clone()));

        return Rc::new(move |a: &str, b: &str| -> i32 {
            let primary_cmp = if !accents {
                loose_collator.borrow_mut().compare_string(a, b)
            } else {
                case_insensitive_collator.borrow_mut().compare_string(a, b)
            };
            if primary_cmp != 0 {
                return primary_cmp;
            }

            let a_runes: Vec<char> = a.chars().collect();
            let b_runes: Vec<char> = b.chars().collect();
            let min_len = a_runes.len().min(b_runes.len());

            for i in 0..min_len {
                let a_upper = unicode_is_upper(a_runes[i]);
                let b_upper = unicode_is_upper(b_runes[i]);
                if a_upper != b_upper {
                    match case_first {
                        OrganizeImportsCaseFirst::UPPER => {
                            if a_upper {
                                return -1;
                            }
                            return 1;
                        }
                        OrganizeImportsCaseFirst::LOWER => {
                            if !a_upper {
                                return -1;
                            }
                            return 1;
                        }
                        _ => {
                            if a_upper {
                                return 1;
                            }
                            return -1;
                        }
                    }
                }
            }

            if !accents {
                if a_runes.len() != b_runes.len() {
                    return a_runes.len() as i32 - b_runes.len() as i32;
                }
                return 0;
            }

            full_collator.borrow_mut().compare_string(a, b)
        });
    }

    if ignore_case {
        opts.push(collate::IGNORE_CASE);
        if !accents {
            opts.push(collate::LOOSE);
        }
    }

    let collator = RefCell::new(collate::new(&tag, opts));

    Rc::new(move |a: &str, b: &str| -> i32 { collator.borrow_mut().compare_string(a, b) })
}

/// Go `unicode.IsUpper`: general category Lu.
// PORT: the Rust `Uppercase` property is Lu plus `Other_Uppercase`; the
// `Other_Uppercase` ranges are removed so the result is Go's category test
// (the same helper as in `ls/symbols.rs`).
fn unicode_is_upper(c: char) -> bool {
    if !c.is_uppercase() {
        return false;
    }
    !matches!(
        c as u32,
        0x2160..=0x216F | 0x24B6..=0x24CF | 0x1F130..=0x1F149 | 0x1F150..=0x1F169 | 0x1F170..=0x1F189
    )
}

// Go: ls/lsutil/organizeimports.go:155 getOrganizeImportsLocale
fn get_organize_imports_locale(preferences: &UserPreferences) -> String {
    let mut locale_str = "en".to_string();
    if !preferences.organize_imports_locale.is_empty() {
        locale_str = preferences.organize_imports_locale.clone();
    }

    if locale_str == "auto" {
        let default: &crate::locale::Locale = &crate::locale::DEFAULT;
        if *default != crate::locale::Locale::default() {
            let tag = default;
            return tag.0.string();
        }
        return "en".to_string();
    }

    let (locale, ok) = crate::locale::parse(&locale_str);
    if ok {
        let tag = locale;
        return tag.0.string();
    }

    "en".to_string()
}

// Go: ls/lsutil/organizeimports.go:177 getOrganizeImportsStringComparer
fn get_organize_imports_string_comparer(
    preferences: &UserPreferences,
    ignore_case: bool,
) -> StringComparer {
    let collation = preferences.organize_imports_collation;

    if collation == OrganizeImportsCollation::UNICODE {
        return get_organize_imports_unicode_string_comparer(ignore_case, preferences);
    }
    get_organize_imports_ordinal_string_comparer(ignore_case)
}

// Go: ls/lsutil/organizeimports.go:186 getModuleSpecifierExpression
fn get_module_specifier_expression(declaration: Node) -> Node {
    match declaration.kind() {
        SyntaxKind::ImportEqualsDeclaration => {
            let import_equals = declaration;
            if import_equals.module_reference().kind() == SyntaxKind::ExternalModuleReference {
                return import_equals.module_reference().expression();
            }
            Node::NIL
        }
        SyntaxKind::ImportDeclaration => declaration.module_specifier(),
        SyntaxKind::VariableStatement => {
            let declarations = declaration.declaration_list().declarations().nodes();
            if !declarations.is_empty() {
                let initializer = declarations.get(0).initializer();
                if initializer.is_some() && initializer.kind() == SyntaxKind::CallExpression {
                    let call_expr = initializer;
                    if !call_expr.arguments().is_empty() {
                        return call_expr.arguments().get(0);
                    }
                }
            }
            Node::NIL
        }
        _ => Node::NIL,
    }
}

// Go: ls/lsutil/organizeimports.go:214 GetExternalModuleName
// GetExternalModuleName returns the module name from a module specifier expression.
pub fn get_external_module_name(specifier: Node) -> String {
    if specifier.is_some() && is_string_literal_like(specifier) {
        return specifier.text().to_string();
    }
    String::new()
}

// Go: ls/lsutil/organizeimports.go:222 CompareModuleSpecifiers
// CompareModuleSpecifiers compares two module specifiers using the given comparer.
pub fn compare_module_specifiers(m1: Node, m2: Node, comparer: &dyn Fn(&str, &str) -> i32) -> i32 {
    let name1 = get_external_module_name(m1);
    let name2 = get_external_module_name(m2);
    let cmp = crate::scanner_util::compare_booleans(name1.is_empty(), name2.is_empty());
    if cmp != 0 {
        return cmp;
    }
    let cmp = crate::scanner_util::compare_booleans(
        crate::frontend::tspath::is_external_module_name_relative(&name1),
        crate::frontend::tspath::is_external_module_name_relative(&name2),
    );
    if cmp != 0 {
        return cmp;
    }
    comparer(&name1, &name2)
}

// Go: ls/lsutil/organizeimports.go:234 compareImportKind
fn compare_import_kind(s1: Node, s2: Node) -> i32 {
    get_import_kind_order(s1).cmp(&get_import_kind_order(s2)) as i32
}

// getImportKindOrder returns the sort order for different import kinds:
// 1. Side-effect imports
// 2. Type-only imports
// 3. Namespace imports
// 4. Default imports
// 5. Named imports
// 6. ImportEqualsDeclarations
// 7. Require variable statements
// Go: ls/lsutil/organizeimports.go:246 importKindOrder consts
const IMPORT_KIND_ORDER_SIDE_EFFECT: i32 = 0;
const IMPORT_KIND_ORDER_TYPE_ONLY: i32 = 1;
const IMPORT_KIND_ORDER_NAMESPACE: i32 = 2;
const IMPORT_KIND_ORDER_DEFAULT: i32 = 3;
const IMPORT_KIND_ORDER_NAMED: i32 = 4;
const IMPORT_KIND_ORDER_IMPORT_EQUALS: i32 = 5;
const IMPORT_KIND_ORDER_REQUIRE: i32 = 6;
const IMPORT_KIND_ORDER_UNKNOWN: i32 = 7;

// Go: ls/lsutil/organizeimports.go:257 getImportKindOrder
fn get_import_kind_order(s1: Node) -> i32 {
    match s1.kind() {
        SyntaxKind::ImportDeclaration => {
            let import_decl = s1;
            if import_decl.import_clause().is_nil() {
                return IMPORT_KIND_ORDER_SIDE_EFFECT;
            }
            let import_clause = import_decl.import_clause();
            if import_clause.is_type_only() {
                return IMPORT_KIND_ORDER_TYPE_ONLY;
            }
            if import_clause.named_bindings().is_some()
                && import_clause.named_bindings().kind() == SyntaxKind::NamespaceImport
            {
                return IMPORT_KIND_ORDER_NAMESPACE;
            }
            if import_clause.name().is_some() {
                return IMPORT_KIND_ORDER_DEFAULT;
            }
            IMPORT_KIND_ORDER_NAMED
        }
        SyntaxKind::ImportEqualsDeclaration => IMPORT_KIND_ORDER_IMPORT_EQUALS,
        SyntaxKind::VariableStatement => IMPORT_KIND_ORDER_REQUIRE,
        _ => IMPORT_KIND_ORDER_UNKNOWN,
    }
}

// Go: ls/lsutil/organizeimports.go:285 CompareImportsOrRequireStatements
// CompareImportsOrRequireStatements compares two import or require statements.
pub fn compare_imports_or_require_statements(
    s1: Node,
    s2: Node,
    comparer: &dyn Fn(&str, &str) -> i32,
) -> i32 {
    let cmp = compare_module_specifiers(
        get_module_specifier_expression(s1),
        get_module_specifier_expression(s2),
        comparer,
    );
    if cmp != 0 {
        return cmp;
    }
    compare_import_kind(s1, s2)
}

// Go: ls/lsutil/organizeimports.go:292 compareImportOrExportSpecifiers
fn compare_import_or_export_specifiers(
    s1: Node,
    s2: Node,
    comparer: &dyn Fn(&str, &str) -> i32,
    preferences: &UserPreferences,
) -> i32 {
    let type_order = preferences.organize_imports_type_order;

    let s1_name = s1.name().text();
    let s2_name = s2.name().text();

    match type_order {
        OrganizeImportsTypeOrder::FIRST => {
            let cmp = crate::scanner_util::compare_booleans(s2.is_type_only(), s1.is_type_only());
            if cmp != 0 {
                return cmp;
            }
            comparer(s1_name, s2_name)
        }
        OrganizeImportsTypeOrder::INLINE => comparer(s1_name, s2_name),
        _ => {
            // OrganizeImportsTypeOrderLast
            let cmp = crate::scanner_util::compare_booleans(s1.is_type_only(), s2.is_type_only());
            if cmp != 0 {
                return cmp;
            }
            comparer(s1_name, s2_name)
        }
    }
}

// Go: ls/lsutil/organizeimports.go:315 GetNamedImportSpecifierComparer
// GetNamedImportSpecifierComparer returns a comparer function for sorting import specifiers.
// PORT: the returned Go closure captures a copy of `preferences`; this one
// holds a clone.
pub fn get_named_import_specifier_comparer(
    preferences: &UserPreferences,
    comparer: Option<StringComparer>,
) -> NodeComparer {
    let mut comparer = comparer;
    if comparer.is_none() {
        let mut ignore_case = false;
        if !preferences.organize_imports_ignore_case.is_unknown() {
            ignore_case = preferences.organize_imports_ignore_case.is_true();
        }
        comparer = Some(get_organize_imports_ordinal_string_comparer(ignore_case));
    }
    let comparer = comparer.expect("set above when nil");
    let preferences = preferences.clone();
    Rc::new(move |s1: Node, s2: Node| -> i32 {
        compare_import_or_export_specifiers(s1, s2, &*comparer, &preferences)
    })
}

// Go: ls/lsutil/organizeimports.go:329 GetImportSpecifierInsertionIndex
// GetImportSpecifierInsertionIndex returns the index at which to insert a new import specifier.
pub fn get_import_specifier_insertion_index(
    sorted_imports: &[Node],
    new_import: Node,
    comparer: &dyn Fn(Node, Node) -> i32,
) -> i32 {
    binary_search_unique_func(sorted_imports, |_mid, value| comparer(value, new_import)).0
}

// Go: ls/lsutil/organizeimports.go:336 GetImportDeclarationInsertIndex
// GetImportDeclarationInsertIndex returns the index at which to insert a new import declaration.
pub fn get_import_declaration_insert_index(
    sorted_imports: &[Node],
    new_import: Node,
    comparer: &dyn Fn(Node, Node) -> i32,
) -> i32 {
    binary_search_unique_func(sorted_imports, |_mid, value| comparer(value, new_import)).0
}

// Go: ls/lsutil/organizeimports.go:343 GetOrganizeImportsStringComparerWithDetection
// GetOrganizeImportsStringComparerWithDetection returns a string comparer based on detecting the order of import statements by the module specifier
pub fn get_organize_imports_string_comparer_with_detection(
    original_import_decls: &[Node],
    preferences: &UserPreferences,
) -> (Option<StringComparer>, bool) {
    let (result, sorted) = detect_module_specifier_case_by_sort(
        &[original_import_decls.to_vec()],
        &get_comparers(preferences),
    );
    (result, sorted)
}

// Go: ls/lsutil/organizeimports.go:348 getComparers
fn get_comparers(preferences: &UserPreferences) -> Vec<StringComparer> {
    match preferences.organize_imports_ignore_case {
        Tristate::True => return CASE_INSENSITIVE_ORGANIZE_IMPORTS_COMPARER.with(|c| c.clone()),
        Tristate::False => return CASE_SENSITIVE_ORGANIZE_IMPORTS_COMPARER.with(|c| c.clone()),
        _ => {}
    }

    ORGANIZE_IMPORTS_COMPARERS.with(|c| c.clone())
}

// Go: ls/lsutil/organizeimports.go:359 namedImportSortResult
struct NamedImportSortResult {
    named_import_comparer: Option<StringComparer>,
    type_order: OrganizeImportsTypeOrder,
    is_sorted: bool,
}

// Go: ls/lsutil/organizeimports.go:366 DetectNamedImportOrganizationBySort
// DetectNamedImportOrganizationBySort detects the order of named imports throughout the file by considering the named imports in each statement as a group
// PORT: the unexported Go `detectNamedImportOrganizationBySort` has the same
// snake name, so this exported one ends in `_exported` (PORTING "Names").
pub fn detect_named_import_organization_by_sort_exported(
    original_groups: &[Node],
    comparers_to_test: &[StringComparer],
    types_to_test: &[OrganizeImportsTypeOrder],
) -> (Option<StringComparer>, OrganizeImportsTypeOrder, bool) {
    let result =
        detect_named_import_organization_by_sort(original_groups, comparers_to_test, types_to_test);
    let Some(result) = result else {
        return (None, OrganizeImportsTypeOrder::LAST, false);
    };
    (result.named_import_comparer, result.type_order, true)
}

// Go: ls/lsutil/organizeimports.go:378 detectNamedImportOrganizationBySort
// PORT: Go `map[OrganizeImportsTypeOrder]T` reads give the zero value (0 or
// nil) for a missing key; `get(..).unwrap_or(0)` and `get(..).cloned()` do
// the same. Go `math.MaxInt` is `i32::MAX` here (PORTING `int` -> `i32`);
// diffs are counts far below either.
fn detect_named_import_organization_by_sort(
    original_groups: &[Node],
    comparers_to_test: &[StringComparer],
    types_to_test: &[OrganizeImportsTypeOrder],
) -> Option<NamedImportSortResult> {
    let mut both_named_imports = false;
    let mut import_decls_with_named: Vec<Node> = Vec::new();

    for &imp in original_groups {
        if imp.import_clause().is_nil() {
            continue;
        }
        let clause = imp.import_clause();
        if clause.named_bindings().is_nil()
            || clause.named_bindings().kind() != SyntaxKind::NamedImports
        {
            continue;
        }
        let named_imports = clause.named_bindings();
        if named_imports.elements().is_empty() {
            continue;
        }

        if !both_named_imports {
            let mut has_type_only = false;
            let mut has_regular = false;
            for elem in named_imports.elements().iter() {
                if elem.is_type_only() {
                    has_type_only = true;
                } else {
                    has_regular = true;
                }
            }
            if has_type_only && has_regular {
                both_named_imports = true;
            }
        }

        import_decls_with_named.push(imp);
    }

    if import_decls_with_named.is_empty() {
        return None;
    }

    let mut named_imports_by_decl: Vec<Vec<Node>> =
        Vec::with_capacity(import_decls_with_named.len());
    for &imp in &import_decls_with_named {
        let clause = imp.import_clause();
        let named_imports = clause.named_bindings();
        named_imports_by_decl.push(named_imports.elements().to_vec());
    }

    if !both_named_imports || types_to_test.is_empty() {
        let mut names_list: Vec<Vec<String>> = Vec::with_capacity(named_imports_by_decl.len());
        for imports in &named_imports_by_decl {
            let mut names: Vec<String> = Vec::with_capacity(imports.len());
            for imp in imports {
                names.push(imp.name().text().to_string());
            }
            names_list.push(names);
        }
        let sort_state = detect_case_sensitivity_by_sort(&names_list, comparers_to_test);
        let mut type_order = OrganizeImportsTypeOrder::LAST;
        if types_to_test.len() == 1 {
            type_order = types_to_test[0];
        }
        return Some(NamedImportSortResult {
            named_import_comparer: sort_state.comparer,
            type_order,
            is_sorted: sort_state.is_sorted,
        });
    }

    let mut best_diff: FxHashMap<OrganizeImportsTypeOrder, i32> = FxHashMap::default();
    best_diff.insert(OrganizeImportsTypeOrder::FIRST, i32::MAX);
    best_diff.insert(OrganizeImportsTypeOrder::LAST, i32::MAX);
    best_diff.insert(OrganizeImportsTypeOrder::INLINE, i32::MAX);
    let mut best_comparer: FxHashMap<OrganizeImportsTypeOrder, StringComparer> =
        FxHashMap::default();
    best_comparer.insert(
        OrganizeImportsTypeOrder::FIRST,
        comparers_to_test[0].clone(),
    );
    best_comparer.insert(OrganizeImportsTypeOrder::LAST, comparers_to_test[0].clone());
    best_comparer.insert(
        OrganizeImportsTypeOrder::INLINE,
        comparers_to_test[0].clone(),
    );

    for cur_comparer in comparers_to_test {
        let mut curr_diff: FxHashMap<OrganizeImportsTypeOrder, i32> = FxHashMap::default();
        curr_diff.insert(OrganizeImportsTypeOrder::FIRST, 0);
        curr_diff.insert(OrganizeImportsTypeOrder::LAST, 0);
        curr_diff.insert(OrganizeImportsTypeOrder::INLINE, 0);

        for import_decl in &named_imports_by_decl {
            for &type_order in types_to_test {
                let prefs = UserPreferences {
                    organize_imports_type_order: type_order,
                    ..Default::default()
                };
                let diff = measure_sortedness(import_decl, |n1: &Node, n2: &Node| {
                    compare_import_or_export_specifiers(*n1, *n2, &**cur_comparer, &prefs)
                });
                let current = curr_diff.get(&type_order).copied().unwrap_or(0);
                curr_diff.insert(type_order, current + diff);
            }
        }

        for &type_order in types_to_test {
            let current = curr_diff.get(&type_order).copied().unwrap_or(0);
            if current < best_diff.get(&type_order).copied().unwrap_or(0) {
                best_diff.insert(type_order, current);
                best_comparer.insert(type_order, cur_comparer.clone());
            }
        }
    }

    for &best_type_order in types_to_test {
        let mut is_best = true;
        for &test_type_order in types_to_test {
            if best_diff.get(&test_type_order).copied().unwrap_or(0)
                < best_diff.get(&best_type_order).copied().unwrap_or(0)
            {
                is_best = false;
                break;
            }
        }
        if is_best {
            return Some(NamedImportSortResult {
                named_import_comparer: best_comparer.get(&best_type_order).cloned(),
                type_order: best_type_order,
                is_sorted: best_diff.get(&best_type_order).copied().unwrap_or(0) == 0,
            });
        }
    }

    Some(NamedImportSortResult {
        named_import_comparer: best_comparer.get(&OrganizeImportsTypeOrder::LAST).cloned(),
        type_order: OrganizeImportsTypeOrder::LAST,
        is_sorted: best_diff
            .get(&OrganizeImportsTypeOrder::LAST)
            .copied()
            .unwrap_or(0)
            == 0,
    })
}

// Go: ls/lsutil/organizeimports.go:509 caseSensitivityDetectionResult
struct CaseSensitivityDetectionResult {
    comparer: Option<StringComparer>,
    is_sorted: bool,
}

// Go: ls/lsutil/organizeimports.go:515 DetectModuleSpecifierCaseBySort
// DetectModuleSpecifierCaseBySort detects the order of module specifiers based on import statements throughout the module/file
pub fn detect_module_specifier_case_by_sort(
    import_decls_by_group: &[Vec<Node>],
    comparers_to_test: &[StringComparer],
) -> (Option<StringComparer>, bool) {
    let mut module_specifiers_by_group: Vec<Vec<String>> =
        Vec::with_capacity(import_decls_by_group.len());
    for import_group in import_decls_by_group {
        let mut module_names: Vec<String> = Vec::with_capacity(import_group.len());
        for &decl in import_group {
            let expr = get_module_specifier_expression(decl);
            if expr.is_some() {
                module_names.push(get_external_module_name(expr));
            } else {
                module_names.push(String::new());
            }
        }
        module_specifiers_by_group.push(module_names);
    }
    let result = detect_case_sensitivity_by_sort(&module_specifiers_by_group, comparers_to_test);
    (result.comparer, result.is_sorted)
}

// Go: ls/lsutil/organizeimports.go:532 detectCaseSensitivityBySort
// PORT: Go `math.MaxInt` is `i32::MAX` here (PORTING `int` -> `i32`).
fn detect_case_sensitivity_by_sort(
    original_groups: &[Vec<String>],
    comparers_to_test: &[StringComparer],
) -> CaseSensitivityDetectionResult {
    let mut best_comparer: Option<StringComparer> = None;
    let mut best_diff = i32::MAX;

    for cur_comparer in comparers_to_test {
        let mut diff_of_current_comparer = 0;

        for list_to_sort in original_groups {
            if list_to_sort.len() <= 1 {
                continue;
            }
            let diff =
                measure_sortedness(list_to_sort, |a: &String, b: &String| cur_comparer(a, b));
            diff_of_current_comparer += diff;
        }

        if diff_of_current_comparer < best_diff {
            best_diff = diff_of_current_comparer;
            best_comparer = Some(cur_comparer.clone());
        }
    }

    if best_comparer.is_none() && !comparers_to_test.is_empty() {
        best_comparer = Some(comparers_to_test[0].clone());
    }

    CaseSensitivityDetectionResult {
        comparer: best_comparer,
        is_sorted: best_diff == 0,
    }
}

// Go: ls/lsutil/organizeimports.go:563 measureSortedness
// PORT: Go passes the elements by value; this passes references.
fn measure_sortedness<T>(arr: &[T], comparer: impl Fn(&T, &T) -> i32) -> i32 {
    let mut i = 0;
    for j in 0..arr.len().saturating_sub(1) {
        if comparer(&arr[j], &arr[j + 1]) > 0 {
            i += 1;
        }
    }
    i
}

// Go: ls/lsutil/organizeimports.go:574 GetNamedImportSpecifierComparerWithDetection
// GetNamedImportSpecifierComparerWithDetection returns a specifier comparer based on detecting the existing sort order within a single import statement
pub fn get_named_import_specifier_comparer_with_detection(
    import_decl: Node,
    source_file: Node,
    preferences: &UserPreferences,
) -> (NodeComparer, Tristate) {
    let (comparers_to_test, type_orders_to_test) = get_detection_lists(preferences);

    let mut import_stmt = Node::NIL;
    if import_decl.kind() == SyntaxKind::ImportDeclaration {
        import_stmt = import_decl;
    }

    let mut specifier_comparer =
        get_named_import_specifier_comparer(preferences, Some(comparers_to_test[0].clone()));
    let mut is_sorted = Tristate::Unknown;

    if (preferences.organize_imports_ignore_case.is_unknown()
        || preferences.organize_imports_type_order == OrganizeImportsTypeOrder::AUTO)
        && import_stmt.is_some()
    {
        let detect_from_decl = detect_named_import_organization_by_sort(
            &[import_stmt],
            &comparers_to_test,
            &type_orders_to_test,
        );
        if let Some(detect_from_decl) = detect_from_decl {
            is_sorted = bool_to_tristate(detect_from_decl.is_sorted);
            specifier_comparer = get_named_import_specifier_comparer(
                &UserPreferences {
                    organize_imports_type_order: detect_from_decl.type_order,
                    ..Default::default()
                },
                detect_from_decl.named_import_comparer,
            );
        } else if source_file.is_some() {
            let all_imports = filter_import_declarations(&source_file.statements().to_vec());
            let detect_from_file = detect_named_import_organization_by_sort(
                &all_imports,
                &comparers_to_test,
                &type_orders_to_test,
            );
            if let Some(detect_from_file) = detect_from_file {
                is_sorted = bool_to_tristate(detect_from_file.is_sorted);
                specifier_comparer = get_named_import_specifier_comparer(
                    &UserPreferences {
                        organize_imports_type_order: detect_from_file.type_order,
                        ..Default::default()
                    },
                    detect_from_file.named_import_comparer,
                );
            }
        }
    }

    (specifier_comparer, is_sorted)
}
