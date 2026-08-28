//! TS1262 from pinned `Binder.checkContextualIdentifier` and AST context helpers
//! at `dc37b5249ab60e2bbce936f71b883e6c8136167e`.

use ts_ast::{NodeArena, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{BoundFile, canonical_has_syntactic_modifier};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{CanonicalProgramCheckError, Program, ProgramDiagnostic, SourceFile};

impl Program {
    pub(super) fn add_top_level_await_identifier_diagnostics(
        &self,
        source: &SourceFile,
        bound: &BoundFile,
        diagnostics: &mut Vec<ProgramDiagnostic>,
    ) -> Result<(), CanonicalProgramCheckError> {
        let root = NodeRef::new(source.parse.arena.id(), source.id, source.parse.source_file);
        if bound.source_file() != root {
            return Err(CanonicalProgramCheckError::InvalidDiagnosticNode(root));
        }
        let facts = bound
            .source_facts()
            .ok_or(CanonicalProgramCheckError::InvalidDiagnosticNode(root))?;
        if !source.parse.diagnostics.is_empty()
            || !facts.is_external_module()
            || facts.is_declaration_file()
        {
            return Ok(());
        }

        let arena = &source.parse.arena;
        let message = message_by_code(1_262).expect("TS1262 must be in the generated catalog");
        for (id, node) in arena.iter() {
            let NodeData::Identifier(identifier) = &node.data else {
                continue;
            };
            let name = NodeRef::new(arena.id(), source.id, id);
            if identifier.text != "await"
                || !bound.contains(name)
                || await_is_identifier_name(arena, id)
                || await_in_ambient_or_jsdoc_context(arena, id)
                || !await_in_top_level_context(arena, id)
            {
                continue;
            }
            diagnostics.push(self.canonical_program_diagnostic(
                Some(name),
                None,
                &Diagnostic::with_arguments(message, [identifier.text.as_str()]),
                std::iter::empty(),
            )?);
        }
        Ok(())
    }
}

fn await_is_identifier_name(arena: &NodeArena, name: NodeId) -> bool {
    let Some(parent) = arena
        .get(name)
        .and_then(|node| node.parent)
        .and_then(|id| arena.get(id))
    else {
        return false;
    };
    match &parent.data {
        NodeData::PropertyDeclaration(data) => data.name == name,
        NodeData::PropertySignatureDeclaration(data) => data.name == name,
        NodeData::MethodDeclaration(data) => data.name == name,
        NodeData::MethodSignatureDeclaration(data) => data.name == name,
        NodeData::GetAccessorDeclaration(data) => data.name == name,
        NodeData::SetAccessorDeclaration(data) => data.name == name,
        NodeData::EnumMember(data) => data.name == name,
        NodeData::PropertyAssignment(data) => data.name == name,
        NodeData::PropertyAccessExpression(data) => data.name == name,
        NodeData::QualifiedName(data) => data.right == name,
        NodeData::BindingElement(data) => data.property_name == Some(name),
        NodeData::ImportSpecifier(data) => data.property_name == Some(name),
        _ => matches!(
            parent.kind,
            SyntaxKind::ExportSpecifier
                | SyntaxKind::JsxAttribute
                | SyntaxKind::JsxSelfClosingElement
                | SyntaxKind::JsxOpeningElement
                | SyntaxKind::JsxClosingElement
        ),
    }
}

fn await_in_ambient_or_jsdoc_context(arena: &NodeArena, mut current: NodeId) -> bool {
    while let Some(node) = arena.get(current) {
        if node.kind.is_js_doc_node()
            || matches!(
                node.kind,
                SyntaxKind::JsTypeAliasDeclaration | SyntaxKind::JsImportDeclaration
            )
            || canonical_has_syntactic_modifier(arena, current, SyntaxKind::DeclareKeyword)
        {
            return true;
        }
        let Some(parent) = node.parent else {
            break;
        };
        current = parent;
    }
    false
}

fn await_in_top_level_context(arena: &NodeArena, name: NodeId) -> bool {
    let mut current = name;
    if let Some(parent) = arena.get(name).and_then(|node| node.parent)
        && let Some(node) = arena.get(parent)
    {
        let outer_binding = match &node.data {
            NodeData::ClassDeclaration(data) if node.kind == SyntaxKind::ClassDeclaration => {
                data.name == Some(name)
            }
            NodeData::FunctionDeclaration(data) if node.kind == SyntaxKind::FunctionDeclaration => {
                data.name == Some(name)
            }
            _ => false,
        };
        if outer_binding {
            current = parent;
        }
    }

    while let Some(parent) = arena.get(current).and_then(|node| node.parent) {
        current = parent;
        let Some(node) = arena.get(current) else {
            return false;
        };
        match node.kind {
            SyntaxKind::SourceFile => return true,
            SyntaxKind::ComputedPropertyName => {
                let Some(container) = node
                    .parent
                    .and_then(|parent| arena.get(parent))
                    .and_then(|parent| parent.parent)
                else {
                    return false;
                };
                current = container;
            }
            SyntaxKind::Decorator => {
                let Some(parent) = node
                    .parent
                    .and_then(|parent| arena.get(parent).map(|record| (parent, record)))
                else {
                    return false;
                };
                if parent.1.kind == SyntaxKind::Parameter {
                    if let Some(member) = parent.1.parent
                        && arena
                            .get(member)
                            .is_some_and(|node| await_is_class_element(node.kind))
                    {
                        current = member;
                    }
                } else if await_is_class_element(parent.1.kind) {
                    current = parent.0;
                }
            }
            SyntaxKind::ArrowFunction
            | SyntaxKind::FunctionDeclaration
            | SyntaxKind::FunctionExpression
            | SyntaxKind::ModuleDeclaration
            | SyntaxKind::ClassStaticBlockDeclaration
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::PropertySignature
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::MethodSignature
            | SyntaxKind::Constructor
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::CallSignature
            | SyntaxKind::ConstructSignature
            | SyntaxKind::IndexSignature
            | SyntaxKind::EnumDeclaration => return false,
            _ => {}
        }
    }
    false
}

fn await_is_class_element(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Constructor
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::IndexSignature
            | SyntaxKind::ClassStaticBlockDeclaration
            | SyntaxKind::SemicolonClassElement
    )
}

#[cfg(test)]
mod tests {
    use ts_options::{CompilerOptions, ModuleDetectionKind, ModuleKind, ScriptTarget};
    use ts_parser::parse_source_file;
    use ts_vfs::{FileSystem, MemoryFileSystem};

    use super::{NodeData, Program, await_in_top_level_context};

    fn options() -> CompilerOptions {
        CompilerOptions {
            no_emit: true,
            module: ModuleKind::EsNext,
            module_specified: true,
            target: ScriptTarget::EsNext,
            lib: Some(vec!["es5".to_owned()]),
            ..CompilerOptions::default()
        }
    }

    fn check(source: &str, file: &str, options: CompilerOptions) -> Program {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(&format!("/project/{file}"), source).unwrap();
        Program::try_new_with_canonical_checker(&fs, "/project", &[file.to_owned()], options)
            .unwrap()
    }

    #[test]
    fn ts1262_reports_top_level_bindings_without_rejecting_identifier_names() {
        for source in [
            "export {}; var await = 1;",
            "export {}; var {await} = {await: 1};",
            "export class await {}",
            "export function await() {}",
        ] {
            let program = check(source, "input.ts", options());
            let [diagnostic] = program.diagnostics() else {
                panic!("{source}: {:?}", program.diagnostics());
            };
            assert_eq!(diagnostic.code, Some(1_262), "{source}");
            let range = diagnostic.range.unwrap();
            assert_eq!(
                &source[range.start.get() as usize..range.end.get() as usize],
                "await"
            );
        }
        for source in [
            "var await = 1;",
            "export {}; function f() { var await = 1; }",
            "export {}; declare var await: any;",
            "export {}; const value = {await: 1}; value.await;",
            "export {}; class C { await(): void {} }",
            "export {}; declare namespace N { const await: any; } import ok = N.await;",
        ] {
            let program = check(source, "input.ts", options());
            assert!(
                program.diagnostics().is_empty(),
                "{source}: {:?}",
                program.diagnostics()
            );
        }
    }

    #[test]
    fn ts1262_preserves_import_names_and_replay() {
        let fs = MemoryFileSystem::new(true);
        let source = "import { await as await } from './other';";
        fs.write_file("/project/input.ts", source).unwrap();
        fs.write_file(
            "/project/other.ts",
            "declare const value: any; export { value as await };",
        )
        .unwrap();
        let (program, cold) = Program::try_new_with_canonical_checker_and_queries(
            &fs,
            "/project",
            &["input.ts".to_owned()],
            options(),
            |_, queries| {
                let cold = queries.cold_diagnostic_snapshot();
                assert_eq!(queries.replay_sources().unwrap(), cold);
                cold
            },
        )
        .unwrap();
        assert_eq!(cold.as_deref(), Some(program.diagnostics()));
        let [diagnostic] = program.diagnostics() else {
            panic!("{:?}", program.diagnostics());
        };
        assert_eq!(diagnostic.code, Some(1_262));
        assert_eq!(
            diagnostic.range.unwrap().start.get() as usize,
            source.rfind("await").unwrap()
        );
    }

    #[test]
    fn ts1262_uses_external_module_facts_and_reports_unchecked_javascript() {
        let source = "var await = 1;";
        let forced = check(
            source,
            "input.ts",
            CompilerOptions {
                module_detection: ModuleDetectionKind::Force,
                ..options()
            },
        );
        assert_eq!(
            forced
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [Some(1_262)]
        );
        let js_options = CompilerOptions {
            allow_js: true,
            check_js: false,
            ..options()
        };
        let module = check("export {}; var await = 1;", "input.js", js_options.clone());
        assert_eq!(
            module
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.code)
                .collect::<Vec<_>>(),
            [Some(1_262)]
        );
        let commonjs = check(
            "var await = 1; module.exports = await;",
            "input.js",
            js_options,
        );
        assert!(
            commonjs.diagnostics().is_empty(),
            "{:?}",
            commonjs.diagnostics()
        );
    }

    #[test]
    fn ts1262_respects_parse_error_gate_without_hiding_semantic_errors() {
        let source = "export {}; var before = 1 var await = 1; const wrong: string = 1;";
        let program = check(source, "input.ts", options());
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(1_005))
        );
        assert!(
            program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(2_322))
        );
        assert!(
            !program
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == Some(1_262))
        );
    }

    #[test]
    fn ts1262_context_classification_matches_pinned_containers() {
        for (source, expected) in [
            ("function marker() {}", true),
            ("class marker {}", true),
            ("const f = function marker() {};", false),
            ("function outer() { function marker() {} }", false),
            ("class C { [marker]() {} }", true),
            ("function outer() { class C { [marker]() {} } }", false),
            ("class C { @marker method() {} }", true),
            ("class C { method(@marker value: any) {} }", true),
            ("class C { method() { marker; } }", false),
            ("class C { static { marker; } }", false),
            ("namespace N { marker; }", false),
            ("const f = (marker: any) => marker;", false),
        ] {
            let parsed = parse_source_file(source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}: {:?}",
                parsed.diagnostics
            );
            let mut found = 0;
            for (id, node) in parsed.arena.iter() {
                if matches!(&node.data, NodeData::Identifier(name) if name.text == "marker") {
                    found += 1;
                    assert_eq!(
                        await_in_top_level_context(&parsed.arena, id),
                        expected,
                        "{source}"
                    );
                }
            }
            assert!(found != 0, "{source}");
        }
    }
}
