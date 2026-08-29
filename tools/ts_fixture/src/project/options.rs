use serde_json::{Map, Value};
use ts_options::{
    CompilerOptions, JsxEmit, ModuleDetectionKind, ModuleKind, ModuleResolutionKind, NewLineKind,
    ScriptTarget,
};

/// Keep every typed option and report the effective module separately.
/// New compiler fields must be added to this report.
#[allow(clippy::too_many_lines)]
pub(super) fn normalized_options(options: &CompilerOptions) -> Value {
    let CompilerOptions {
        always_strict,
        allow_arbitrary_extensions,
        allow_importing_ts_extensions,
        allow_js,
        allow_js_specified,
        allow_umd_global_access,
        allow_unreachable_code,
        allow_unused_labels,
        allow_synthetic_default_imports,
        assume_changes_only_affect_direct_dependencies,
        check_js,
        composite,
        declaration,
        declaration_specified,
        declaration_map,
        deduplicate_packages,
        disable_size_limit,
        downlevel_iteration,
        emit_declaration_only,
        emit_bom,
        emit_decorator_metadata,
        erasable_syntax_only,
        experimental_decorators,
        es_module_interop,
        exact_optional_property_types,
        force_consistent_casing_in_file_names,
        isolated_modules,
        isolated_declarations,
        import_helpers,
        lib_replacement,
        module_detection,
        module_detection_specified,
        new_line,
        no_check,
        no_emit,
        no_emit_helpers,
        no_emit_on_error,
        no_error_truncation,
        remove_comments,
        rewrite_relative_import_extensions,
        no_implicit_any,
        no_implicit_any_specified,
        no_implicit_override,
        no_implicit_returns,
        no_implicit_this,
        no_implicit_this_specified,
        no_lib,
        no_fallthrough_cases_in_switch,
        no_property_access_from_index_signature,
        no_resolve,
        no_unchecked_indexed_access,
        no_unchecked_side_effect_imports,
        no_unchecked_side_effect_imports_specified,
        no_unused_locals,
        no_unused_parameters,
        preserve_const_enums,
        preserve_symlinks,
        skip_default_lib_check,
        skip_lib_check,
        stable_type_ordering,
        strip_internal,
        strict,
        strict_specified,
        strict_bind_call_apply,
        strict_bind_call_apply_specified,
        strict_builtin_iterator_return,
        strict_builtin_iterator_return_specified,
        strict_function_types,
        strict_function_types_specified,
        strict_null_checks,
        strict_null_checks_specified,
        strict_property_initialization,
        strict_property_initialization_specified,
        use_define_for_class_fields,
        use_unknown_in_catch_variables,
        use_unknown_in_catch_variables_specified,
        verbatim_module_syntax,
        lib,
        module,
        module_specified,
        module_resolution,
        target,
        jsx,
        jsx_factory,
        jsx_fragment_factory,
        jsx_import_source,
        react_namespace,
        ignore_deprecations,
        max_node_module_js_depth,
        custom_conditions,
        module_suffixes,
        resolve_json_module,
        resolve_json_module_specified,
        resolve_package_json_exports,
        resolve_package_json_imports,
        source_map,
        inline_source_map,
        inline_sources,
        map_root,
        source_root,
        incremental,
        incremental_specified,
        trace_resolution,
        out_file,
        out_dir,
        root_dir,
        declaration_dir,
        ts_build_info_file,
        base_url,
        paths,
        root_dirs,
        type_roots,
        types,
    } = options;
    let mut result = Map::new();
    macro_rules! retain {
        ($($name:ident),* $(,)?) => {
            $(result.insert(stringify!($name).to_owned(), serde_json::json!($name));)*
        };
    }
    retain!(
        always_strict,
        allow_arbitrary_extensions,
        allow_importing_ts_extensions,
        allow_js,
        allow_js_specified,
        allow_umd_global_access,
        allow_unreachable_code,
        allow_unused_labels,
        allow_synthetic_default_imports,
        assume_changes_only_affect_direct_dependencies,
        check_js,
        composite,
        declaration,
        declaration_specified,
        declaration_map,
        deduplicate_packages,
        disable_size_limit,
        downlevel_iteration,
        emit_declaration_only,
        emit_bom,
        emit_decorator_metadata,
        erasable_syntax_only,
        experimental_decorators,
        es_module_interop,
        exact_optional_property_types,
        force_consistent_casing_in_file_names,
        isolated_modules,
        isolated_declarations,
        import_helpers,
        lib_replacement,
        module_detection_specified,
        no_check,
        no_emit,
        no_emit_helpers,
        no_emit_on_error,
        no_error_truncation,
        remove_comments,
        rewrite_relative_import_extensions,
        no_implicit_any,
        no_implicit_any_specified,
        no_implicit_override,
        no_implicit_returns,
        no_implicit_this,
        no_implicit_this_specified,
        no_lib,
        no_fallthrough_cases_in_switch,
        no_property_access_from_index_signature,
        no_resolve,
        no_unchecked_indexed_access,
        no_unchecked_side_effect_imports,
        no_unchecked_side_effect_imports_specified,
        no_unused_locals,
        no_unused_parameters,
        preserve_const_enums,
        preserve_symlinks,
        skip_default_lib_check,
        skip_lib_check,
        stable_type_ordering,
        strip_internal,
        strict,
        strict_specified,
        strict_bind_call_apply,
        strict_bind_call_apply_specified,
        strict_builtin_iterator_return,
        strict_builtin_iterator_return_specified,
        strict_function_types,
        strict_function_types_specified,
        strict_null_checks,
        strict_null_checks_specified,
        strict_property_initialization,
        strict_property_initialization_specified,
        use_define_for_class_fields,
        use_unknown_in_catch_variables,
        use_unknown_in_catch_variables_specified,
        verbatim_module_syntax,
        lib,
        module_specified,
        jsx_factory,
        jsx_fragment_factory,
        jsx_import_source,
        react_namespace,
        ignore_deprecations,
        max_node_module_js_depth,
        custom_conditions,
        module_suffixes,
        resolve_json_module,
        resolve_json_module_specified,
        resolve_package_json_exports,
        resolve_package_json_imports,
        source_map,
        inline_source_map,
        inline_sources,
        map_root,
        source_root,
        incremental,
        incremental_specified,
        trace_resolution,
        out_file,
        out_dir,
        root_dir,
        declaration_dir,
        ts_build_info_file,
        base_url,
        paths,
        root_dirs,
        type_roots,
        types,
    );
    result.insert(
        "module".to_owned(),
        Value::String(module_name(*module).to_owned()),
    );
    result.insert(
        "effective_module".to_owned(),
        Value::String(module_name(module.effective_for_target(*target)).to_owned()),
    );
    result.insert(
        "module_resolution".to_owned(),
        Value::String(
            match module_resolution {
                ModuleResolutionKind::Classic => "classic",
                ModuleResolutionKind::Node10 => "node10",
                ModuleResolutionKind::Node16 => "node16",
                ModuleResolutionKind::NodeNext => "nodenext",
                ModuleResolutionKind::Bundler => "bundler",
            }
            .to_owned(),
        ),
    );
    result.insert(
        "target".to_owned(),
        Value::String(
            match target {
                ScriptTarget::Es3 => "es3",
                ScriptTarget::Es5 => "es5",
                ScriptTarget::Es2015 => "es2015",
                ScriptTarget::Es2016 => "es2016",
                ScriptTarget::Es2017 => "es2017",
                ScriptTarget::Es2018 => "es2018",
                ScriptTarget::Es2019 => "es2019",
                ScriptTarget::Es2020 => "es2020",
                ScriptTarget::Es2021 => "es2021",
                ScriptTarget::Es2022 => "es2022",
                ScriptTarget::Es2023 => "es2023",
                ScriptTarget::Es2024 => "es2024",
                ScriptTarget::Es2025 => "es2025",
                ScriptTarget::EsNext => "esnext",
            }
            .to_owned(),
        ),
    );
    result.insert(
        "jsx".to_owned(),
        Value::String(
            match jsx {
                JsxEmit::None => "none",
                JsxEmit::Preserve => "preserve",
                JsxEmit::React => "react",
                JsxEmit::ReactNative => "react-native",
                JsxEmit::ReactJsx => "react-jsx",
                JsxEmit::ReactJsxDev => "react-jsxdev",
            }
            .to_owned(),
        ),
    );
    result.insert(
        "module_detection".to_owned(),
        Value::String(
            match module_detection {
                ModuleDetectionKind::Legacy => "legacy",
                ModuleDetectionKind::Auto => "auto",
                ModuleDetectionKind::Force => "force",
            }
            .to_owned(),
        ),
    );
    result.insert(
        "new_line".to_owned(),
        Value::String(
            match new_line {
                NewLineKind::Lf => "lf",
                NewLineKind::Crlf => "crlf",
            }
            .to_owned(),
        ),
    );
    Value::Object(result)
}

pub(super) const fn module_name(module: ModuleKind) -> &'static str {
    match module {
        ModuleKind::None => "none",
        ModuleKind::CommonJs => "commonjs",
        ModuleKind::Amd => "amd",
        ModuleKind::Umd => "umd",
        ModuleKind::System => "system",
        ModuleKind::Es2015 => "es2015",
        ModuleKind::Es2020 => "es2020",
        ModuleKind::Es2022 => "es2022",
        ModuleKind::EsNext => "esnext",
        ModuleKind::Node16 => "node16",
        ModuleKind::Node18 => "node18",
        ModuleKind::Node20 => "node20",
        ModuleKind::NodeNext => "nodenext",
        ModuleKind::Preserve => "preserve",
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;
    use ts_options::{CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget};

    use super::normalized_options;

    #[test]
    fn report_separates_the_unset_module_from_its_effective_default() {
        let options = CompilerOptions::default();
        let report = normalized_options(&options);
        assert_eq!(report["target"], json!("es2025"));
        assert_eq!(report["module"], json!("none"));
        assert_eq!(report["module_specified"], json!(false));
        assert_eq!(report["effective_module"], json!("es2022"));
        assert_eq!(report["module_resolution"], json!("node10"));
        assert_eq!(report["resolve_json_module"], json!(false));
        assert_eq!(report["resolve_json_module_specified"], json!(false));
        assert_eq!(options.module, ModuleKind::None);
        assert!(!options.module_specified);
    }

    #[test]
    fn report_preserves_explicit_legacy_target_resolution_and_json_false() {
        for (resolution, name) in [
            (ModuleResolutionKind::Classic, "classic"),
            (ModuleResolutionKind::Node10, "node10"),
        ] {
            let options = CompilerOptions {
                target: ScriptTarget::Es5,
                module_resolution: resolution,
                resolve_json_module: false,
                resolve_json_module_specified: true,
                ..CompilerOptions::default()
            };
            let report = normalized_options(&options);
            assert_eq!(report["target"], json!("es5"));
            assert_eq!(report["module"], json!("none"));
            assert_eq!(report["module_specified"], json!(false));
            assert_eq!(report["effective_module"], json!("commonjs"));
            assert_eq!(report["module_resolution"], json!(name));
            assert_eq!(report["resolve_json_module"], json!(false));
            assert_eq!(report["resolve_json_module_specified"], json!(true));
            assert_eq!(options.target, ScriptTarget::Es5);
            assert_eq!(options.module_resolution, resolution);
        }
    }

    #[test]
    fn report_preserves_explicit_module_provenance() {
        for (module, raw, effective) in [
            (ModuleKind::None, "none", "es2022"),
            (ModuleKind::CommonJs, "commonjs", "commonjs"),
            (ModuleKind::System, "system", "system"),
            (ModuleKind::NodeNext, "nodenext", "nodenext"),
        ] {
            let options = CompilerOptions {
                module,
                module_specified: true,
                ..CompilerOptions::default()
            };
            let report = normalized_options(&options);
            assert_eq!(report["target"], json!("es2025"));
            assert_eq!(report["module"], json!(raw));
            assert_eq!(report["module_specified"], json!(true));
            assert_eq!(report["effective_module"], json!(effective));
            assert_eq!(options.module, module);
            assert!(options.module_specified);
        }
    }
}
