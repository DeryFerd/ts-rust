//! Port of internal/printer/namegenerator_test.go.

use super::childprog::{in_child, install_map_fs, new_program, source_file};
use crate::support::vfstest::MapFs;
use ts_goport::prelude::*;
use ts_goport::program::ls_program;

/// Go `&printer.NameGenerator{Context: ec}`, and with `with_text` also
/// `GetTextOfNode: (*ast.Node).Text`.
fn name_generator(ec: &Rc<EmitContext>, with_text: bool) -> NameGenerator {
    let mut g = NameGenerator::default();
    g.context = Some(Rc::clone(ec));
    if with_text {
        g.get_text_of_node = Some(Rc::new(|_g: &mut NameGenerator, node: Node| {
            node.text().to_string()
        }));
    }
    g
}

/// Go `file := parsetestutil.ParseTypeScript(text, false /*jsx*/);
/// binder.BindSourceFile(file)`, then `body(file)`.
// PORT: the name generator reads the locals of a bound file through the
// current program (`is_unique_local_name`). So the file is the one root
// file `/main.ts` of a program with no lib files, made and bound in a child
// process (see `childprog`), and `body` runs there with the program
// current.
fn with_bound_file(
    module_path: &'static str,
    name: &'static str,
    text: &'static str,
    body: impl FnOnce(Node) + Send + 'static,
) {
    in_child(module_path, name, move || {
        let map_fs = MapFs::from_map([("/main.ts", text)], true);
        install_map_fs(&map_fs, "/");
        let p = new_program(
            map_fs.fs(),
            "/",
            &["/main.ts"],
            CompilerOptions {
                no_lib: Tristate::True,
                ..Default::default()
            },
        );
        let _current = ls_program::enter(&p);
        ls_program::bind_source_files(&p);
        body(source_file(&p, "/main.ts").root);
    });
}

// Go: printer/namegenerator_test.go:13 TestTempVariable1
#[test]
fn temp_variable1() {
    let ec = new_emit_context();
    let name1 = ec.factory().new_temp_variable();
    let name2 = ec.factory().new_temp_variable();

    let mut g = name_generator(&ec, false);
    let text1 = g.generate_name(name1);
    let text2 = g.generate_name(name2);

    assert_eq!("_a", text1);
    assert_eq!("_b", text2);
}

// Go: printer/namegenerator_test.go:28 TestTempVariable2
#[test]
fn temp_variable2() {
    let ec = new_emit_context();
    let name1 = ec.factory().new_temp_variable_ex(AutoGenerateOptions {
        prefix: "A".into(),
        suffix: "B".into(),
        ..Default::default()
    });
    let name2 = ec.factory().new_temp_variable_ex(AutoGenerateOptions {
        prefix: "A".into(),
        suffix: "B".into(),
        ..Default::default()
    });

    let mut g = name_generator(&ec, false);
    let text1 = g.generate_name(name1);
    let text2 = g.generate_name(name2);

    assert_eq!("A_aB", text1);
    assert_eq!("A_bB", text2);
}

// Go: printer/namegenerator_test.go:49 TestTempVariable3
#[test]
fn temp_variable3() {
    let ec = new_emit_context();
    let name1 = ec.factory().new_temp_variable();

    let mut g = name_generator(&ec, false);
    let text1 = g.generate_name(name1);
    let text2 = g.generate_name(name1);

    assert_eq!("_a", text1);
    assert_eq!("_a", text2);
}

// Go: printer/namegenerator_test.go:63 TestTempVariableScoped
#[test]
fn temp_variable_scoped() {
    let ec = new_emit_context();
    let name1 = ec.factory().new_temp_variable();
    let name2 = ec.factory().new_temp_variable();

    let mut g = name_generator(&ec, false);
    let text1 = g.generate_name(name1);
    g.push_scope(false);
    let text2 = g.generate_name(name2);
    g.pop_scope(false);

    assert_eq!("_a", text1);
    assert_eq!("_a", text2);
}

// Go: printer/namegenerator_test.go:80 TestTempVariableScopedReserved
#[test]
fn temp_variable_scoped_reserved() {
    let ec = new_emit_context();
    let name1 = ec.factory().new_temp_variable_ex(AutoGenerateOptions {
        flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
        ..Default::default()
    });
    let name2 = ec.factory().new_temp_variable();

    let mut g = name_generator(&ec, false);
    let text1 = g.generate_name(name1);
    g.push_scope(false);
    let text2 = g.generate_name(name2);
    g.pop_scope(false);

    assert_eq!("_a", text1);
    assert_eq!("_b", text2);
}

// Go: printer/namegenerator_test.go:97 TestLoopVariable1
#[test]
fn loop_variable1() {
    let ec = new_emit_context();
    let name1 = ec.factory().new_loop_variable();
    let name2 = ec.factory().new_loop_variable();

    let mut g = name_generator(&ec, false);
    let text1 = g.generate_name(name1);
    let text2 = g.generate_name(name2);

    assert_eq!("_i", text1);
    assert_eq!("_a", text2);
}

// Go: printer/namegenerator_test.go:112 TestLoopVariable2
#[test]
fn loop_variable2() {
    let ec = new_emit_context();
    let name1 = ec.factory().new_loop_variable_ex(AutoGenerateOptions {
        prefix: "A".into(),
        suffix: "B".into(),
        ..Default::default()
    });
    let name2 = ec.factory().new_loop_variable_ex(AutoGenerateOptions {
        prefix: "A".into(),
        suffix: "B".into(),
        ..Default::default()
    });

    let mut g = name_generator(&ec, false);
    let text1 = g.generate_name(name1);
    let text2 = g.generate_name(name2);

    assert_eq!("A_iB", text1);
    assert_eq!("A_aB", text2);
}

// Go: printer/namegenerator_test.go:133 TestLoopVariable3
#[test]
fn loop_variable3() {
    let ec = new_emit_context();
    let name1 = ec.factory().new_loop_variable();

    let mut g = name_generator(&ec, false);
    let text1 = g.generate_name(name1);
    let text2 = g.generate_name(name1);

    assert_eq!("_i", text1);
    assert_eq!("_i", text2);
}

// Go: printer/namegenerator_test.go:147 TestLoopVariableScoped
#[test]
fn loop_variable_scoped() {
    let ec = new_emit_context();
    let name1 = ec.factory().new_loop_variable();
    let name2 = ec.factory().new_loop_variable();

    let mut g = name_generator(&ec, false);
    let text1 = g.generate_name(name1);
    g.push_scope(false);
    let text2 = g.generate_name(name2);
    g.pop_scope(false);

    assert_eq!("_i", text1);
    assert_eq!("_i", text2);
}

// Go: printer/namegenerator_test.go:164 TestUniqueName1
#[test]
fn unique_name1() {
    let ec = new_emit_context();
    let name1 = ec.factory().new_unique_name("foo");
    let name2 = ec.factory().new_unique_name("foo");

    let mut g = name_generator(&ec, false);
    let text1 = g.generate_name(name1);
    let text2 = g.generate_name(name2);

    assert_eq!("foo_1", text1);
    assert_eq!("foo_2", text2);
}

// Go: printer/namegenerator_test.go:179 TestUniqueName2
#[test]
fn unique_name2() {
    let ec = new_emit_context();
    let name1 = ec.factory().new_unique_name("foo");

    let mut g = name_generator(&ec, false);
    let text1 = g.generate_name(name1);
    let text2 = g.generate_name(name1);

    assert_eq!("foo_1", text1);
    // Expected to be same because GenerateName goes off object identity
    assert_eq!("foo_1", text2);
}

// Go: printer/namegenerator_test.go:194 TestUniqueNameScoped
#[test]
fn unique_name_scoped() {
    let ec = new_emit_context();
    let name1 = ec.factory().new_unique_name("foo");
    let name2 = ec.factory().new_unique_name("foo");

    let mut g = name_generator(&ec, false);
    assert_eq!("foo_1", g.generate_name(name1));

    g.push_scope(false);
    assert_eq!("foo_2", g.generate_name(name2)); // Matches Strada, but is incorrect
    // assert_eq!("foo_1", g.generate_name(name2)); // TODO: Fix after Strada port is complete.
    g.pop_scope(false);
}

// Go: printer/namegenerator_test.go:210 TestUniquePrivateName1
#[test]
fn unique_private_name1() {
    let ec = new_emit_context();
    let name1 = ec.factory().new_unique_private_name("#foo");
    let name2 = ec.factory().new_unique_private_name("#foo");

    let mut g = name_generator(&ec, false);
    let text1 = g.generate_name(name1);
    let text2 = g.generate_name(name2);

    assert_eq!("#foo_1", text1);
    assert_eq!("#foo_2", text2);
}

// Go: printer/namegenerator_test.go:225 TestUniquePrivateName2
#[test]
fn unique_private_name2() {
    let ec = new_emit_context();
    let name1 = ec.factory().new_unique_private_name("#foo");

    let mut g = name_generator(&ec, false);
    let text1 = g.generate_name(name1);
    let text2 = g.generate_name(name1);

    assert_eq!("#foo_1", text1);
    assert_eq!("#foo_1", text2);
}

// Go: printer/namegenerator_test.go:239 TestUniquePrivateNameScoped
#[test]
fn unique_private_name_scoped() {
    let ec = new_emit_context();
    let name1 = ec.factory().new_unique_private_name("#foo");
    let name2 = ec.factory().new_unique_private_name("#foo");

    let mut g = name_generator(&ec, false);
    assert_eq!("#foo_1", g.generate_name(name1));

    g.push_scope(false); // private names are always reserved in nested scopes
    assert_eq!("#foo_2", g.generate_name(name2));
    g.pop_scope(false);
}

// Go: printer/namegenerator_test.go:254 TestGeneratedNameForIdentifier1
#[test]
fn generated_name_for_identifier1() {
    with_bound_file(
        module_path!(),
        "generated_name_for_identifier1",
        "function f() {}",
        |file| {
            let ec = new_emit_context();

            let n = file.statements().get(0).name();
            let name1 = ec.factory().new_generated_name_for_node(n);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("f_1", text1);
        },
    );
}

// Go: printer/namegenerator_test.go:271 TestGeneratedNameForIdentifier2
#[test]
fn generated_name_for_identifier2() {
    with_bound_file(
        module_path!(),
        "generated_name_for_identifier2",
        "function f() {}",
        |file| {
            let ec = new_emit_context();

            let n = file.statements().get(0).name();
            let name1 = ec.factory().new_generated_name_for_node_ex(
                n,
                AutoGenerateOptions {
                    prefix: "a".into(),
                    suffix: "b".into(),
                    ..Default::default()
                },
            );

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("afb", text1);
        },
    );
}

// Go: printer/namegenerator_test.go:291 TestGeneratedNameForIdentifier3
#[test]
fn generated_name_for_identifier3() {
    with_bound_file(
        module_path!(),
        "generated_name_for_identifier3",
        "function f() {}",
        |file| {
            let ec = new_emit_context();

            let n = file.statements().get(0).name();
            let name1 = ec.factory().new_generated_name_for_node_ex(
                n,
                AutoGenerateOptions {
                    prefix: "a".into(),
                    suffix: "b".into(),
                    ..Default::default()
                },
            );
            let name2 = ec.factory().new_generated_name_for_node(name1);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name2);

            assert_eq!("afb_1", text1);
        },
    );
}

// namespace reuses name if it does not collide with locals
// Go: printer/namegenerator_test.go:313 TestGeneratedNameForNamespace1
#[test]
fn generated_name_for_namespace1() {
    with_bound_file(
        module_path!(),
        "generated_name_for_namespace1",
        "namespace foo { }",
        |file| {
            let ec = new_emit_context();

            let ns1 = file.statements().get(0);
            let name1 = ec.factory().new_generated_name_for_node(ns1);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("foo", text1);
        },
    );
}

// namespace uses generated name if it collides with locals
// Go: printer/namegenerator_test.go:331 TestGeneratedNameForNamespace2
#[test]
fn generated_name_for_namespace2() {
    with_bound_file(
        module_path!(),
        "generated_name_for_namespace2",
        "namespace foo { var foo; }",
        |file| {
            let ec = new_emit_context();

            let ns1 = file.statements().get(0);
            let name1 = ec.factory().new_generated_name_for_node(ns1);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("foo_1", text1);
        },
    );
}

// avoids collisions when unscoped
// Go: printer/namegenerator_test.go:349 TestGeneratedNameForNamespace3
#[test]
fn generated_name_for_namespace3() {
    with_bound_file(
        module_path!(),
        "generated_name_for_namespace3",
        "namespace ns1 { namespace foo { var foo; } } namespace ns2 { namespace foo { var foo; } }",
        |file| {
            let ec = new_emit_context();

            let ns1 = file.statements().get(0).body().statements().get(0);
            let ns2 = file.statements().get(1).body().statements().get(0);
            let name1 = ec.factory().new_generated_name_for_node(ns1);
            let name2 = ec.factory().new_generated_name_for_node(ns2);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);
            let text2 = g.generate_name(name2);

            assert_eq!("foo_1", text1);
            assert_eq!("foo_2", text2);
        },
    );
}

// reuse name when scoped
// Go: printer/namegenerator_test.go:371 TestGeneratedNameForNamespace4
#[test]
fn generated_name_for_namespace4() {
    with_bound_file(
        module_path!(),
        "generated_name_for_namespace4",
        "namespace ns1 { namespace foo { var foo; } } namespace ns2 { namespace foo { var foo; } }",
        |file| {
            let ec = new_emit_context();

            let ns1 = file.statements().get(0).body().statements().get(0);
            let ns2 = file.statements().get(1).body().statements().get(0);
            let name1 = ec.factory().new_generated_name_for_node(ns1);
            let name2 = ec.factory().new_generated_name_for_node(ns2);

            let mut g = name_generator(&ec, true);
            g.push_scope(false);
            let text1 = g.generate_name(name1);
            g.pop_scope(false);

            g.push_scope(false);
            let text2 = g.generate_name(name2);
            g.pop_scope(false);

            assert_eq!("foo_1", text1);
            assert_eq!("foo_2", text2); // Matches Strada, but is incorrect
            // assert_eq!("foo_1", text2); // TODO: Fix after Strada port is complete.
        },
    );
}

// Go: printer/namegenerator_test.go:398 TestGeneratedNameForNodeCached
#[test]
fn generated_name_for_node_cached() {
    with_bound_file(
        module_path!(),
        "generated_name_for_node_cached",
        "namespace foo { var foo; }",
        |file| {
            let ec = new_emit_context();

            let ns1 = file.statements().get(0);
            let name1 = ec.factory().new_generated_name_for_node(ns1);
            let name2 = ec.factory().new_generated_name_for_node(ns1);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);
            let text2 = g.generate_name(name2);

            assert_eq!("foo_1", text1);
            assert_eq!("foo_1", text2);
        },
    );
}

// Go: printer/namegenerator_test.go:418 TestGeneratedNameForImport
#[test]
fn generated_name_for_import() {
    with_bound_file(
        module_path!(),
        "generated_name_for_import",
        "import * as foo from 'foo'",
        |file| {
            let ec = new_emit_context();

            let n = file.statements().get(0);
            let name1 = ec.factory().new_generated_name_for_node(n);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("foo_1", text1);
        },
    );
}

// Go: printer/namegenerator_test.go:435 TestGeneratedNameForExport
#[test]
fn generated_name_for_export() {
    with_bound_file(
        module_path!(),
        "generated_name_for_export",
        "export * as foo from 'foo'",
        |file| {
            let ec = new_emit_context();

            let n = file.statements().get(0);
            let name1 = ec.factory().new_generated_name_for_node(n);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("foo_1", text1);
        },
    );
}

// Go: printer/namegenerator_test.go:452 TestGeneratedNameForFunctionDeclaration1
#[test]
fn generated_name_for_function_declaration1() {
    with_bound_file(
        module_path!(),
        "generated_name_for_function_declaration1",
        "export function f() {}",
        |file| {
            let ec = new_emit_context();

            let n = file.statements().get(0);
            let name1 = ec.factory().new_generated_name_for_node(n);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("f_1", text1);
        },
    );
}

// Go: printer/namegenerator_test.go:469 TestGeneratedNameForFunctionDeclaration2
#[test]
fn generated_name_for_function_declaration2() {
    with_bound_file(
        module_path!(),
        "generated_name_for_function_declaration2",
        "export default function () {}",
        |file| {
            let ec = new_emit_context();

            let n = file.statements().get(0);
            let name1 = ec.factory().new_generated_name_for_node(n);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("default_1", text1);
        },
    );
}

// Go: printer/namegenerator_test.go:486 TestGeneratedNameForClassDeclaration1
#[test]
fn generated_name_for_class_declaration1() {
    with_bound_file(
        module_path!(),
        "generated_name_for_class_declaration1",
        "export class C {}",
        |file| {
            let ec = new_emit_context();

            let n = file.statements().get(0);
            let name1 = ec.factory().new_generated_name_for_node(n);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("C_1", text1);
        },
    );
}

// Go: printer/namegenerator_test.go:503 TestGeneratedNameForClassDeclaration2
#[test]
fn generated_name_for_class_declaration2() {
    with_bound_file(
        module_path!(),
        "generated_name_for_class_declaration2",
        "export default class {}",
        |file| {
            let ec = new_emit_context();

            let n = file.statements().get(0);
            let name1 = ec.factory().new_generated_name_for_node(n);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("default_1", text1);
        },
    );
}

// Go: printer/namegenerator_test.go:520 TestGeneratedNameForExportAssignment
#[test]
fn generated_name_for_export_assignment() {
    with_bound_file(
        module_path!(),
        "generated_name_for_export_assignment",
        "export default 0",
        |file| {
            let ec = new_emit_context();

            let n = file.statements().get(0);
            let name1 = ec.factory().new_generated_name_for_node(n);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("default_1", text1);
        },
    );
}

// Go: printer/namegenerator_test.go:537 TestGeneratedNameForClassExpression
#[test]
fn generated_name_for_class_expression() {
    with_bound_file(
        module_path!(),
        "generated_name_for_class_expression",
        "(class {})",
        |file| {
            let ec = new_emit_context();

            let n = file.statements().get(0).expression().expression();
            let name1 = ec.factory().new_generated_name_for_node(n);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("class_1", text1);
        },
    );
}

// Go: printer/namegenerator_test.go:554 TestGeneratedNameForMethod1
#[test]
fn generated_name_for_method1() {
    with_bound_file(
        module_path!(),
        "generated_name_for_method1",
        "class C { m() {} }",
        |file| {
            let ec = new_emit_context();

            let n = file.statements().get(0).members().get(0);
            let name1 = ec.factory().new_generated_name_for_node(n);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("m_1", text1);
        },
    );
}

// Go: printer/namegenerator_test.go:571 TestGeneratedNameForMethod2
#[test]
fn generated_name_for_method2() {
    with_bound_file(
        module_path!(),
        "generated_name_for_method2",
        "class C { 0() {} }",
        |file| {
            let ec = new_emit_context();

            let n = file.statements().get(0).members().get(0);
            let name1 = ec.factory().new_generated_name_for_node(n);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("_a", text1);
        },
    );
}

// Go: printer/namegenerator_test.go:588 TestGeneratedPrivateNameForMethod
#[test]
fn generated_private_name_for_method() {
    with_bound_file(
        module_path!(),
        "generated_private_name_for_method",
        "class C { m() {} }",
        |file| {
            let ec = new_emit_context();

            let n = file.statements().get(0).members().get(0);
            let name1 = ec.factory().new_generated_private_name_for_node(n);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("#m_1", text1);
        },
    );
}

// Go: printer/namegenerator_test.go:605 TestGeneratedNameForComputedPropertyName
#[test]
fn generated_name_for_computed_property_name() {
    with_bound_file(
        module_path!(),
        "generated_name_for_computed_property_name",
        "class C { [x] }",
        |file| {
            let ec = new_emit_context();

            let n = file.statements().get(0).members().get(0).name();
            let name1 = ec.factory().new_generated_name_for_node(n);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("_a", text1);
        },
    );
}

// Go: printer/namegenerator_test.go:622 TestGeneratedNameForOther
#[test]
fn generated_name_for_other() {
    with_bound_file(
        module_path!(),
        "generated_name_for_other",
        "class C { [x] }",
        |_file| {
            let ec = new_emit_context();

            let n = ec.factory().new_object_literal_expression(
                ec.factory().new_node_list(&[]),
                false, /*multiLine*/
            );
            let name1 = ec.factory().new_generated_name_for_node(n);

            let mut g = name_generator(&ec, true);
            let text1 = g.generate_name(name1);

            assert_eq!("_a", text1);
        },
    );
}
