use crate::ls::lsutil::prelude::*;

use crate::frontend::core_binarysearch::binary_search_unique_func;
use crate::frontend::stringutil_ls;
use crate::gostd::norm;
use crate::gostd::unicode;
use crate::gostd::unicode_tables::{self, RangeTable};

// Port of Go `ls/lsutil/organizeimports.go`.

// PORT: Go `func(a, b string) int` values. Go stores them in slices, maps and
// structs and compares them only with nil; a nil comparer is `None`. The
// unicode comparers are closures, so this is a shared `dyn Fn` (PORTING:
// stored funcs are `Rc<dyn Fn>`).
pub type StringComparer = Rc<dyn Fn(&str, &str) -> i32>;

// PORT: Go `func(s1, s2 *ast.Node) int` values returned to callers.
pub type NodeComparer = Rc<dyn Fn(Node, Node) -> i32>;

// Go: ls/lsutil/organizeimports.go:18 FilterImportDeclarations
// FilterImportDeclarations filters out non-import declarations from a list of statements.
pub fn filter_import_declarations(statements: &[Node]) -> Vec<Node> {
    statements
        .iter()
        .copied()
        .filter(|stmt| stmt.kind() == SyntaxKind::ImportDeclaration)
        .collect()
}

// Go: ls/lsutil/organizeimports.go:25 GetDetectionLists
// GetDetectionLists returns the lists of comparers and type orders to test for organize imports detection.
pub fn get_detection_lists(
    preferences: &UserPreferences,
) -> (Vec<StringComparer>, Vec<OrganizeImportsTypeOrder>) {
    let comparers_to_test: Vec<StringComparer>;
    let type_orders_to_test: Vec<OrganizeImportsTypeOrder>;
    if preferences.organize_imports_sort != OrganizeImportsSort::AUTO {
        comparers_to_test = vec![get_organize_imports_preset_string_comparer(
            preferences.organize_imports_sort,
        )];
    } else if !preferences.organize_imports_ignore_case.is_unknown() {
        comparers_to_test = vec![get_organize_imports_string_comparer(
            preferences,
            preferences.organize_imports_ignore_case.is_true(),
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

// Go: ls/lsutil/organizeimports.go:50 ResolveOrganizeImportsSort
pub fn resolve_organize_imports_sort(preferences: &UserPreferences) -> OrganizeImportsSort {
    if preferences.organize_imports_sort != OrganizeImportsSort::AUTO {
        return preferences.organize_imports_sort;
    }

    if preferences.organize_imports_collation == OrganizeImportsCollation::UNICODE {
        return match preferences.organize_imports_ignore_case {
            Tristate::True => OrganizeImportsSort::NATURAL_IGNORE_CASE,
            Tristate::False => OrganizeImportsSort::NATURAL,
            _ => OrganizeImportsSort::AUTO,
        };
    }

    match preferences.organize_imports_ignore_case {
        Tristate::True => OrganizeImportsSort::ORDINAL_IGNORE_CASE,
        Tristate::False => OrganizeImportsSort::ORDINAL,
        _ => OrganizeImportsSort::AUTO,
    }
}

// Go: ls/lsutil/organizeimports.go:76 getOrganizeImportsOrdinalStringComparer
fn get_organize_imports_ordinal_string_comparer(ignore_case: bool) -> StringComparer {
    if ignore_case {
        return Rc::new(stringutil_ls::compare_strings_case_insensitive_eslint_compatible);
    }
    Rc::new(stringutil_ls::compare_strings_case_sensitive)
}

// Go: ls/lsutil/organizeimports.go:83 getOrganizeImportsNaturalStringComparer
fn get_organize_imports_natural_string_comparer(case_sensitive: bool) -> StringComparer {
    Rc::new(move |a: &str, b: &str| -> i32 {
        compare_organize_imports_natural_strings(a, b, case_sensitive)
    })
}

// Go: ls/lsutil/organizeimports.go:89 getOrganizeImportsUnicodeStringComparer
fn get_organize_imports_unicode_string_comparer(
    ignore_case: bool,
    preferences: &UserPreferences,
) -> StringComparer {
    let case_first = preferences.organize_imports_case_first;
    let numeric = preferences.organize_imports_numeric_collation.is_true();
    let accents = !preferences.organize_imports_accent_collation.is_false();

    Rc::new(move |a: &str, b: &str| -> i32 {
        compare_organize_imports_unicode_strings(a, b, ignore_case, case_first, numeric, accents)
    })
}

// Go: ls/lsutil/organizeimports.go:99 compareOrganizeImportsNaturalStrings
fn compare_organize_imports_natural_strings(a: &str, b: &str, case_sensitive: bool) -> i32 {
    let cmp = compare_strings_numeric(&natural_collation_key(a), &natural_collation_key(b));
    if cmp != 0 {
        return cmp;
    }

    if case_sensitive {
        let cmp = compare_organize_imports_case_upper_first(a, b);
        if cmp != 0 {
            return cmp;
        }
    }

    a.cmp(b) as i32
}

// Go: ls/lsutil/organizeimports.go:113 compareOrganizeImportsUnicodeStrings
fn compare_organize_imports_unicode_strings(
    a: &str,
    b: &str,
    ignore_case: bool,
    case_first: OrganizeImportsCaseFirst,
    numeric: bool,
    accents: bool,
) -> i32 {
    let cmp = compare_organize_imports_unicode_keys(
        &natural_collation_key(a),
        &natural_collation_key(b),
        numeric,
    );
    if cmp != 0 {
        return cmp;
    }

    if accents {
        let cmp = compare_organize_imports_unicode_keys(
            &strings_to_lower(a),
            &strings_to_lower(b),
            numeric,
        );
        if cmp != 0 {
            return cmp;
        }
    }

    if !ignore_case {
        let cmp = compare_organize_imports_case(a, b, case_first);
        if cmp != 0 {
            return cmp;
        }
    }

    a.cmp(b) as i32
}

// Go: ls/lsutil/organizeimports.go:133 naturalCollationKey
fn natural_collation_key(s: &str) -> String {
    strings_to_lower(&remove_diacritics(s))
}

// Go: ls/lsutil/organizeimports.go:137 removeDiacritics
// PORT: Go `strings.Map` over `norm.NFD.String(s)`. The NFD form of a valid
// UTF-8 string is valid UTF-8, so the lossy conversion never replaces.
fn remove_diacritics(s: &str) -> String {
    let nfd = norm::NFD.append(s.as_bytes());
    String::from_utf8_lossy(&nfd)
        .chars()
        .filter(|&r| !unicode_is(&unicode_tables::MN, r as u32))
        .collect()
}

// Go: ls/lsutil/organizeimports.go:146 compareOrganizeImportsUnicodeKeys
fn compare_organize_imports_unicode_keys(a: &str, b: &str, numeric: bool) -> i32 {
    if numeric {
        return compare_strings_numeric(a, b);
    }
    a.cmp(b) as i32
}

// Go: ls/lsutil/organizeimports.go:153 compareStringsNumeric
// PORT: Go decodes one rune with `utf8.DecodeRuneInString`; a `&str` is
// valid UTF-8, so its first `char` is that rune.
fn compare_strings_numeric(a: &str, b: &str) -> i32 {
    let mut a = a;
    let mut b = b;
    while !a.is_empty() && !b.is_empty() {
        if is_ascii_digit(a.as_bytes()[0]) && is_ascii_digit(b.as_bytes()[0]) {
            let a_run_end = ascii_digit_run_end(a);
            let b_run_end = ascii_digit_run_end(b);

            let cmp = compare_numeric_text(&a[..a_run_end], &b[..b_run_end]);
            if cmp != 0 {
                return cmp;
            }

            a = &a[a_run_end..];
            b = &b[b_run_end..];
            continue;
        }

        let a_rune = a.chars().next().expect("a is not empty");
        let b_rune = b.chars().next().expect("b is not empty");
        if a_rune != b_rune {
            return a_rune.cmp(&b_rune) as i32;
        }

        a = &a[a_rune.len_utf8()..];
        b = &b[b_rune.len_utf8()..];
    }

    a.len().cmp(&b.len()) as i32
}

// Go: ls/lsutil/organizeimports.go:181 isASCIIDigit
fn is_ascii_digit(ch: u8) -> bool {
    ch.is_ascii_digit()
}

// Go: ls/lsutil/organizeimports.go:185 asciiDigitRunEnd
fn ascii_digit_run_end(s: &str) -> usize {
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() && is_ascii_digit(bytes[i]) {
        i += 1;
    }
    i
}

// Go: ls/lsutil/organizeimports.go:193 compareNumericText
fn compare_numeric_text(a: &str, b: &str) -> i32 {
    let mut a_digits = a.trim_start_matches('0');
    let mut b_digits = b.trim_start_matches('0');
    if a_digits.is_empty() {
        a_digits = "0";
    }
    if b_digits.is_empty() {
        b_digits = "0";
    }

    if a_digits.len() != b_digits.len() {
        return a_digits.len().cmp(&b_digits.len()) as i32;
    }
    let cmp = a_digits.cmp(b_digits) as i32;
    if cmp != 0 {
        return cmp;
    }
    a.cmp(b) as i32
}

// Go: ls/lsutil/organizeimports.go:212 compareOrganizeImportsCaseUpperFirst
fn compare_organize_imports_case_upper_first(a: &str, b: &str) -> i32 {
    compare_organize_imports_case(a, b, OrganizeImportsCaseFirst::UPPER)
}

// Go: ls/lsutil/organizeimports.go:216 compareOrganizeImportsCase
fn compare_organize_imports_case(a: &str, b: &str, case_first: OrganizeImportsCaseFirst) -> i32 {
    let a_runes: Vec<char> = a.chars().collect();
    let b_runes: Vec<char> = b.chars().collect();
    let min_len = a_runes.len().min(b_runes.len());

    for i in 0..min_len {
        let a_upper = unicode::is_upper(a_runes[i]);
        let b_upper = unicode::is_upper(b_runes[i]);
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

    a_runes.len().cmp(&b_runes.len()) as i32
}

// Go: unicode/letter.go:163 Is
/// Go `unicode.Is`: reports whether the rune is in the table of ranges.
/// PORT: the same scan as `gostd::collate`; Go's linear and binary searches
/// give the same answer.
fn unicode_is(range_tab: &RangeTable, r: u32) -> bool {
    let r16 = range_tab.r16;
    if let Some(&(_, hi, _)) = r16.last()
        && r <= u32::from(hi)
    {
        return r16.iter().any(|&(lo, hi, stride)| {
            let (lo, hi, stride) = (u32::from(lo), u32::from(hi), u32::from(stride));
            lo <= r && r <= hi && (stride == 1 || (r - lo) % stride == 0)
        });
    }
    let r32 = range_tab.r32;
    if let Some(&(lo, _, _)) = r32.first()
        && r >= lo
    {
        return r32.iter().any(|&(lo, hi, stride)| {
            lo <= r && r <= hi && (stride == 1 || (r - lo) % stride == 0)
        });
    }
    false
}

// PORT: Go `strings.ToLower` maps each rune with `unicode.ToLower`. Rust
// `str::to_lowercase` uses the full mapping of a newer Unicode and the
// final-sigma rule, which Go does not.
fn strings_to_lower(s: &str) -> String {
    s.chars().map(unicode::to_lower).collect()
}

// Go: ls/lsutil/organizeimports.go:248 getOrganizeImportsPresetStringComparer
fn get_organize_imports_preset_string_comparer(sort: OrganizeImportsSort) -> StringComparer {
    match sort {
        OrganizeImportsSort::ORDINAL_IGNORE_CASE => {
            get_organize_imports_ordinal_string_comparer(true)
        }
        OrganizeImportsSort::NATURAL => get_organize_imports_natural_string_comparer(true),
        OrganizeImportsSort::NATURAL_IGNORE_CASE => {
            get_organize_imports_natural_string_comparer(false)
        }
        _ => get_organize_imports_ordinal_string_comparer(false),
    }
}

// Go: ls/lsutil/organizeimports.go:261 getOrganizeImportsStringComparer
fn get_organize_imports_string_comparer(
    preferences: &UserPreferences,
    ignore_case: bool,
) -> StringComparer {
    if preferences.organize_imports_sort != OrganizeImportsSort::AUTO {
        return get_organize_imports_preset_string_comparer(preferences.organize_imports_sort);
    }
    if preferences.organize_imports_collation == OrganizeImportsCollation::UNICODE {
        return get_organize_imports_unicode_string_comparer(ignore_case, preferences);
    }
    get_organize_imports_ordinal_string_comparer(ignore_case)
}

// Go: ls/lsutil/organizeimports.go:271 getModuleSpecifierExpression
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

// Go: ls/lsutil/organizeimports.go:299 GetExternalModuleName
// GetExternalModuleName returns the module name from a module specifier expression.
pub fn get_external_module_name(specifier: Node) -> String {
    if specifier.is_some() && is_string_literal_like(specifier) {
        return specifier.text().to_string();
    }
    String::new()
}

// Go: ls/lsutil/organizeimports.go:307 CompareModuleSpecifiers
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

// Go: ls/lsutil/organizeimports.go:319 compareImportKind
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
// Go: ls/lsutil/organizeimports.go:331 importKindOrder consts
const IMPORT_KIND_ORDER_SIDE_EFFECT: i32 = 0;
const IMPORT_KIND_ORDER_TYPE_ONLY: i32 = 1;
const IMPORT_KIND_ORDER_NAMESPACE: i32 = 2;
const IMPORT_KIND_ORDER_DEFAULT: i32 = 3;
const IMPORT_KIND_ORDER_NAMED: i32 = 4;
const IMPORT_KIND_ORDER_IMPORT_EQUALS: i32 = 5;
const IMPORT_KIND_ORDER_REQUIRE: i32 = 6;
const IMPORT_KIND_ORDER_UNKNOWN: i32 = 7;

// Go: ls/lsutil/organizeimports.go:342 getImportKindOrder
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

// Go: ls/lsutil/organizeimports.go:370 CompareImportsOrRequireStatements
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

// Go: ls/lsutil/organizeimports.go:377 compareImportOrExportSpecifiers
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

// Go: ls/lsutil/organizeimports.go:400 GetNamedImportSpecifierComparer
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
        comparer = Some(get_organize_imports_string_comparer(
            preferences,
            ignore_case,
        ));
    }
    let comparer = comparer.expect("set above when nil");
    let preferences = preferences.clone();
    Rc::new(move |s1: Node, s2: Node| -> i32 {
        compare_import_or_export_specifiers(s1, s2, &*comparer, &preferences)
    })
}

// Go: ls/lsutil/organizeimports.go:414 GetImportSpecifierInsertionIndex
// GetImportSpecifierInsertionIndex returns the index at which to insert a new import specifier.
pub fn get_import_specifier_insertion_index(
    sorted_imports: &[Node],
    new_import: Node,
    comparer: &dyn Fn(Node, Node) -> i32,
) -> i32 {
    binary_search_unique_func(sorted_imports, |_mid, value| comparer(value, new_import)).0
}

// Go: ls/lsutil/organizeimports.go:421 GetImportDeclarationInsertIndex
// GetImportDeclarationInsertIndex returns the index at which to insert a new import declaration.
pub fn get_import_declaration_insert_index(
    sorted_imports: &[Node],
    new_import: Node,
    comparer: &dyn Fn(Node, Node) -> i32,
) -> i32 {
    binary_search_unique_func(sorted_imports, |_mid, value| comparer(value, new_import)).0
}

// Go: ls/lsutil/organizeimports.go:428 GetOrganizeImportsStringComparerWithDetection
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

// Go: ls/lsutil/organizeimports.go:433 getComparers
fn get_comparers(preferences: &UserPreferences) -> Vec<StringComparer> {
    if preferences.organize_imports_sort != OrganizeImportsSort::AUTO
        || !preferences.organize_imports_ignore_case.is_unknown()
    {
        let mut ignore_case = false;
        if !preferences.organize_imports_ignore_case.is_unknown() {
            ignore_case = preferences.organize_imports_ignore_case.is_true();
        }
        return vec![get_organize_imports_string_comparer(
            preferences,
            ignore_case,
        )];
    }
    vec![
        get_organize_imports_string_comparer(preferences, true),
        get_organize_imports_string_comparer(preferences, false),
    ]
}

// Go: ls/lsutil/organizeimports.go:447 namedImportSortResult
struct NamedImportSortResult {
    named_import_comparer: Option<StringComparer>,
    type_order: OrganizeImportsTypeOrder,
    is_sorted: bool,
}

// Go: ls/lsutil/organizeimports.go:454 DetectNamedImportOrganizationBySort
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

// Go: ls/lsutil/organizeimports.go:466 detectNamedImportOrganizationBySort
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

// Go: ls/lsutil/organizeimports.go:597 caseSensitivityDetectionResult
struct CaseSensitivityDetectionResult {
    comparer: Option<StringComparer>,
    is_sorted: bool,
}

// Go: ls/lsutil/organizeimports.go:603 DetectModuleSpecifierCaseBySort
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

// Go: ls/lsutil/organizeimports.go:620 detectCaseSensitivityBySort
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

// Go: ls/lsutil/organizeimports.go:651 measureSortedness
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

// Go: ls/lsutil/organizeimports.go:662 GetNamedImportSpecifierComparerWithDetection
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

    if (resolve_organize_imports_sort(preferences) == OrganizeImportsSort::AUTO
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

#[cfg(test)]
mod tests {
    use super::*;

    // Go: ls/lsutil/utilities_test.go:139 TestCompareOrganizeImportsNaturalStrings
    // PORT: in this file because it calls the unexported
    // `getOrganizeImportsPresetStringComparer`.
    #[test]
    fn test_compare_organize_imports_natural_strings() {
        let comparer =
            get_organize_imports_preset_string_comparer(OrganizeImportsSort::NATURAL_IGNORE_CASE);
        #[rustfmt::skip]
        let tests: &[(&str, &str, &str, i32)] = &[
            ("numeric runs sort by numeric value", "a2", "a100", -1),
            ("numeric runs with equal value use raw tie break", "a02", "a2", -1),
            ("accents are folded for primary comparison", "À", "B", -1),
            ("raw comparison breaks accent ties", "A", "À", -1),
            ("hyphen sorts before slash like Intl.Collator fallback", "app-init", "app/app", -1),
        ];
        for &(name, a, b, want) in tests {
            let got = comparer(a, b).signum();
            assert_eq!(
                got, want,
                "{name}: comparer({a:?}, {b:?}) = {got}, want sign {want}"
            );
        }
    }

    // Go `naturalCollationKey` (ls/lsutil/organizeimports.go:133) at pin N
    // runs on go1.27.1 and x/text v0.42.0 (Unicode 17.0.0): U+A7CB lowers to
    // U+0264, U+105C9 decomposes to U+105D2 U+0307 (Mn) and U+0897 is Mn.
    // The values are Go's; Unicode 15.0.0 kept all three.
    #[test]
    fn natural_collation_key_uses_unicode_17() {
        assert_eq!(natural_collation_key("\u{A7CB}a"), "\u{264}a");
        assert_eq!(natural_collation_key("\u{105C9}"), "\u{105D2}");
        assert_eq!(natural_collation_key("a\u{897}b"), "ab");
        let comparer =
            get_organize_imports_unicode_string_comparer(true, &UserPreferences::default());
        assert_eq!(comparer("./\u{A7CB}a", "./\u{264}b").signum(), -1);
    }
}
