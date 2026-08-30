use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_compiler::{Program, SourceFile};
use ts_options::CompilerOptions;
use ts_vfs::{FileSystem, MemoryFileSystem};

use crate::{
    Case, expand_option_matrix, fixture_case_sensitive, fixture_compiler_options,
    virtual_unit_path, virtual_unit_root,
};

use super::{SemanticArtifactWalk, walk_program};

// Unchanged pinned Go case at dc37b5249ab60e2bbce936f71b883e6c8136167e.
const ORIGINAL_CASE: &str = r"// @allowJs: true
// @checkJs: true
// @noEmit: true

// @filename: react.d.ts
declare namespace React {
    class Component {}
    class PureComponent {}
}

// @filename: main.js
/**
 * @extends {React.Component}
 */
class C extends React.PureComponent {}

/**
 * @extends {React.Component}
 */
class D extends React.Component {}
";

fn fixture_inputs(case: &Case) -> (MemoryFileSystem, Vec<String>, CompilerOptions) {
    let variants = expand_option_matrix(case);
    let [variant] = variants.as_slice() else {
        panic!("the control must retain one option variant")
    };
    assert!(variant.unsupported_details.is_empty());
    let options = fixture_compiler_options(case, variant);
    let filesystem = MemoryFileSystem::new(fixture_case_sensitive(case));
    let roots = case
        .units
        .iter()
        .enumerate()
        .map(|(index, unit)| {
            let path = virtual_unit_path(case, unit, index);
            filesystem
                .write_file(&path, unit.source_text.as_scannable_str())
                .unwrap();
            path
        })
        .collect();
    (filesystem, roots, options)
}

fn syntax_program(name: &str, source: &str) -> (Case, Program) {
    let case = Case::parse(name, source).unwrap();
    let (filesystem, roots, options) = fixture_inputs(&case);
    let program =
        Program::new_with_options(&filesystem, &virtual_unit_root(&case), &roots, options);
    for source in program.source_files() {
        assert!(
            source.parse.diagnostics.is_empty(),
            "{:?}",
            source.parse.diagnostics
        );
    }
    (case, program)
}

fn source_text(program: &Program, node: NodeRef) -> &str {
    let source = program.source_file_by_id(node.file).unwrap();
    let record = program.node(node).unwrap();
    &source.source_text[usize::try_from(record.range.start.get()).unwrap()
        ..usize::try_from(record.range.end.get()).unwrap()]
}

fn row_labels<'a>(program: &'a Program, nodes: &[NodeRef]) -> Vec<(&'a str, SyntaxKind, &'a str)> {
    nodes
        .iter()
        .map(|&node| {
            (
                program
                    .source_file_by_id(node.file)
                    .unwrap()
                    .file_name
                    .as_str(),
                program.node(node).unwrap().kind,
                source_text(program, node),
            )
        })
        .collect()
}

fn heritage_expressions(source: &SourceFile) -> Vec<NodeRef> {
    let mut expressions = source
        .parse
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let NodeData::ExpressionWithTypeArguments(expression) = &record.data else {
                return None;
            };
            Some(source.node_ref(expression.expression).unwrap())
        })
        .collect::<Vec<_>>();
    expressions.sort_by_key(|node| source.parse.arena.get(node.node).unwrap().range.start);
    expressions
}

fn expression_rows<'a>(
    program: &'a Program,
    nodes: &[NodeRef],
    expression: NodeRef,
) -> Vec<&'a str> {
    let expression_range = program.node(expression).unwrap().range;
    nodes
        .iter()
        .copied()
        .filter(|node| {
            let range = program.node(*node).unwrap().range;
            node.file == expression.file
                && range.start >= expression_range.start
                && range.end <= expression_range.end
        })
        .map(|node| source_text(program, node))
        .collect()
}

fn assert_repeated_walk(case: &Case, program: &Program, expected: &SemanticArtifactWalk) {
    assert_eq!(&walk_program(case, program).unwrap(), expected);
}

#[test]
#[allow(clippy::too_many_lines)] // One original fixture checks row order and actual heritage nodes.
fn original_jsdoc_extends_rows_keep_whole_and_leaf_source_order() {
    let case = Case::parse(
        "testdata/tests/cases/compiler/jsdocExtendsClauseMismatch.ts",
        ORIGINAL_CASE,
    )
    .unwrap();
    let (filesystem, roots, options) = fixture_inputs(&case);
    assert!(options.allow_js && options.check_js && options.no_emit);
    assert!(!options.no_check && !options.no_lib);
    assert_eq!(roots, ["/.src/react.d.ts", "/.src/main.js"]);
    let program = Program::try_new_with_canonical_checker(
        &filesystem,
        &virtual_unit_root(&case),
        &roots,
        options,
    )
    .unwrap();
    let [diagnostic] = program.diagnostics() else {
        panic!("the unchanged source must retain only TS8023")
    };
    assert_eq!(diagnostic.code, Some(8023));
    assert_eq!(diagnostic.file_name.as_deref(), Some("/.src/main.js"));
    assert_eq!(
        diagnostic.message,
        "JSDoc '@extends Component' does not match the 'extends PureComponent' clause."
    );
    let range = diagnostic.range.unwrap();
    assert_eq!(range.start.get(), 23);
    assert_eq!(range.len(), 9);
    assert!(diagnostic.related_information.is_empty());

    // These are the rows in both pinned Go baselines. No display query is needed.
    let expected = [
        ("/.src/react.d.ts", SyntaxKind::Identifier, "React"),
        ("/.src/react.d.ts", SyntaxKind::Identifier, "Component"),
        ("/.src/react.d.ts", SyntaxKind::Identifier, "PureComponent"),
        ("/.src/main.js", SyntaxKind::Identifier, "C"),
        (
            "/.src/main.js",
            SyntaxKind::QualifiedName,
            "React.PureComponent",
        ),
        ("/.src/main.js", SyntaxKind::Identifier, "React"),
        ("/.src/main.js", SyntaxKind::Identifier, "PureComponent"),
        ("/.src/main.js", SyntaxKind::Identifier, "D"),
        (
            "/.src/main.js",
            SyntaxKind::QualifiedName,
            "React.Component",
        ),
        ("/.src/main.js", SyntaxKind::Identifier, "React"),
        ("/.src/main.js", SyntaxKind::Identifier, "Component"),
    ];
    let walk = walk_program(&case, &program).unwrap();
    assert_eq!(row_labels(&program, &walk.types), expected);
    assert_eq!(row_labels(&program, &walk.symbols), expected);
    assert_eq!(walk.types, walk.symbols);

    let source = program.source_file("/.src/main.js").unwrap();
    let NodeData::SourceFile(root) = &source
        .parse
        .arena
        .get(source.parse.source_file)
        .unwrap()
        .data
    else {
        panic!("the main unit must retain its source-file node")
    };
    let [first, second] = root.statements.nodes.as_slice() else {
        panic!("the main unit must retain both original classes")
    };
    for (&class_node, row_start) in [first, second].into_iter().zip([3, 7]) {
        let NodeData::ClassDeclaration(class) = &source.parse.arena.get(class_node).unwrap().data
        else {
            panic!("each original statement must remain a class")
        };
        let [clause_node] = class.heritage_clauses.as_ref().unwrap().nodes.as_slice() else {
            panic!("each class must retain its real extends clause")
        };
        let clause_record = source.parse.arena.get(*clause_node).unwrap();
        assert_eq!(clause_record.parent, Some(class_node));
        let NodeData::HeritageClause(clause) = &clause_record.data else {
            panic!("the class list must contain its heritage node")
        };
        assert_eq!(clause.token, SyntaxKind::ExtendsKeyword);
        let [wrapper_node] = clause.types.nodes.as_slice() else {
            panic!("the original class must have one actual base expression")
        };
        let wrapper = source.parse.arena.get(*wrapper_node).unwrap();
        assert_eq!(wrapper.parent, Some(*clause_node));
        let NodeData::ExpressionWithTypeArguments(expression) = &wrapper.data else {
            panic!("the heritage list must retain its expression wrapper")
        };
        assert!(expression.type_arguments.is_none());
        let whole = source.node_ref(expression.expression).unwrap();
        let record = program.node(whole).unwrap();
        assert_eq!(record.parent, Some(*wrapper_node));
        let NodeData::QualifiedName(name) = &record.data else {
            panic!("the current parser retains the original base as a qualified name")
        };
        let left = source.node_ref(name.left).unwrap();
        let right = source.node_ref(name.right).unwrap();
        assert_eq!(program.node(left).unwrap().parent, Some(whole.node));
        assert_eq!(program.node(right).unwrap().parent, Some(whole.node));
        assert_eq!(
            &walk.types[row_start..row_start + 4],
            [
                source.node_ref(class.name.unwrap()).unwrap(),
                whole,
                left,
                right
            ]
        );
    }
    assert_repeated_walk(&case, &program, &walk);
}

#[test]
fn class_heritage_rows_keep_nested_names_calls_and_implements_type_filtering() {
    let (case, program) = syntax_program(
        "heritage.ts",
        concat!(
            "// @noLib: true\n",
            "class Child extends Names.Inner.Base {}\n",
            "const expression = class extends Names.Factory() {};\n",
            "class Implementation implements Names.Face {}\n",
        ),
    );
    let source = program.source_file("/.src/heritage.ts").unwrap();
    let expressions = heritage_expressions(source);
    let [nested, call, implementation] = expressions.as_slice() else {
        panic!("all three real heritage expressions must remain present")
    };
    assert_eq!(
        program.node(*nested).unwrap().kind,
        SyntaxKind::QualifiedName
    );
    assert_eq!(
        program.node(*call).unwrap().kind,
        SyntaxKind::CallExpression
    );
    let NodeData::CallExpression(call_data) = &program.node(*call).unwrap().data else {
        unreachable!()
    };
    let callee = source.node_ref(call_data.expression).unwrap();
    assert_eq!(
        program.node(callee).unwrap().kind,
        SyntaxKind::QualifiedName
    );
    assert_eq!(program.node(callee).unwrap().parent, Some(call.node));
    let walk = walk_program(&case, &program).unwrap();
    for nodes in [&walk.types, &walk.symbols] {
        assert_eq!(
            expression_rows(&program, nodes, *nested),
            ["Names.Inner.Base", "Names.Inner", "Names", "Inner", "Base"]
        );
        assert_eq!(
            expression_rows(&program, nodes, *call),
            ["Names.Factory()", "Names.Factory", "Names", "Factory"]
        );
    }
    assert_eq!(
        expression_rows(&program, &walk.symbols, *implementation),
        ["Names.Face", "Names", "Face"]
    );
    // Go's type-node filter excludes the whole implements name and its right leaf.
    assert_eq!(
        expression_rows(&program, &walk.types, *implementation),
        ["Names"]
    );
    assert_repeated_walk(&case, &program, &walk);
}

#[test]
fn heritage_row_selection_keeps_type_query_jsx_and_type_only_names_unchanged() {
    let (case, program) = syntax_program(
        "contexts.tsx",
        concat!(
            "// @noLib: true\n",
            "// @jsx: preserve\n",
            "type Query = typeof Names.Value;\n",
            "let typed: Names.Type;\n",
            "const view = <Names.Widget />;\n",
        ),
    );
    let source = program.source_file("/.src/contexts.tsx").unwrap();
    let named_node = |kind, text| {
        source
            .parse
            .arena
            .iter()
            .find_map(|(node, record)| {
                let reference = source.node_ref(node).unwrap();
                (record.kind == kind && source_text(&program, reference) == text)
                    .then_some(reference)
            })
            .unwrap()
    };
    let query = named_node(SyntaxKind::QualifiedName, "Names.Value");
    let type_only = named_node(SyntaxKind::QualifiedName, "Names.Type");
    let tag = named_node(SyntaxKind::PropertyAccessExpression, "Names.Widget");
    let walk = walk_program(&case, &program).unwrap();
    for nodes in [&walk.types, &walk.symbols] {
        assert_eq!(
            expression_rows(&program, nodes, query),
            ["Names.Value", "Names", "Value"]
        );
        assert_eq!(
            expression_rows(&program, nodes, tag),
            ["Names.Widget", "Names", "Widget"]
        );
        assert!(!nodes.contains(&type_only));
    }
    assert_repeated_walk(&case, &program, &walk);
}
