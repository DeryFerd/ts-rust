use crate::frontend::prelude::*;

// This file ports tsoptions/tsconfigparsing.go lines 901 to 1833.
// PORT: Go `any` values are `CompilerOptionsValue`. Go
// `*collections.OrderedMap[string, any]` is `IndexMap<String,
// CompilerOptionsValue>` (the `Map` variant). Go
// `collections.OrderedMap[string, string]` is `IndexMap<String, String>`.
// Go `*ast.SourceFile` is the source file `Node` (`Node::NIL` is Go nil).
// Go `[][]string` extension groups are `Vec<Vec<String>>`. Go `int` is
// `i32`.

// Go: tsoptions/tsconfigparsing.go:901 getDefaultTypeAcquisition
pub fn get_default_type_acquisition(config_file_name: &str) -> TypeAcquisition {
    let mut options = TypeAcquisition::default();
    if !config_file_name.is_empty() && get_base_file_name(config_file_name) == "jsconfig.json" {
        options.enable = Tristate::True;
    }
    options
}

// Go: tsoptions/tsconfigparsing.go:909 convertCompilerOptionsFromJsonWorker
fn convert_compiler_options_from_json_worker(
    json_options: &CompilerOptionsValue,
    base_path: &str,
    config_file_name: &str,
) -> (CompilerOptions, Vec<Diagnostic>) {
    let mut options = get_default_compiler_options(config_file_name);
    let (_, errors) = convert_options_from_json(
        &COMMAND_LINE_COMPILER_OPTIONS_MAP,
        json_options,
        base_path,
        CompilerOptionsParser {
            compiler_options: &mut options,
        },
    );
    if !config_file_name.is_empty() {
        options.config_file_path = normalize_slashes(config_file_name);
    }
    (options, errors)
}

// Go: tsoptions/tsconfigparsing.go:918 convertTypeAcquisitionFromJsonWorker
fn convert_type_acquisition_from_json_worker(
    json_options: &CompilerOptionsValue,
    base_path: &str,
    config_file_name: &str,
) -> (TypeAcquisition, Vec<Diagnostic>) {
    let mut options = get_default_type_acquisition(config_file_name);
    let (_, errors) = convert_options_from_json(
        &TYPE_ACQUISITION_DECLARATION.element_options,
        json_options,
        base_path,
        TypeAcquisitionParser {
            type_acquisition: &mut options,
        },
    );
    (options, errors)
}

// Go: tsoptions/tsconfigparsing.go:924 parseOwnConfigOfJson
// PORT: Go stores a `[]string` (maybe nil) in the `any` field, so the field
// is never Go nil. It is always `Some` here.
fn parse_own_config_of_json(
    json: &IndexMap<String, CompilerOptionsValue>,
    host: &dyn ParseConfigHost,
    base_path: &str,
    config_file_name: &str,
) -> (ParsedTsconfig, Vec<Diagnostic>) {
    let nil = CompilerOptionsValue::Nil;
    let mut errors: Vec<Diagnostic> = Vec::new();
    if json.contains_key("excludes") {
        errors.push(new_compiler_diagnostic(
            diag::Unknown_option_excludes_Did_you_mean_exclude,
            args![],
        ));
    }
    let (options, err) = convert_compiler_options_from_json_worker(
        json.get("compilerOptions").unwrap_or(&nil),
        base_path,
        config_file_name,
    );
    let (type_acquisition, err2) = convert_type_acquisition_from_json_worker(
        json.get("typeAcquisition").unwrap_or(&nil),
        base_path,
        config_file_name,
    );
    errors.extend(err);
    errors.extend(err2);
    // watchOptions := convertWatchOptionsFromJsonWorker(json.watchOptions, basePath, errors)
    // json.compileOnSave = convertCompileOnSaveOptionFromJson(json, basePath, errors)
    let mut extended_config_path: Vec<String> = Vec::new();
    let extends = json.get("extends").unwrap_or(&nil);
    if !extends.is_nil() && *extends != CompilerOptionsValue::String(String::new()) {
        let err;
        (extended_config_path, err) = get_extends_config_path_or_array(
            extends,
            host,
            base_path,
            config_file_name,
            Node::NIL,
            Node::NIL,
            Node::NIL,
        );
        errors.extend(err);
    }
    let parsed_config = ParsedTsconfig {
        raw: CompilerOptionsValue::Map(json.clone()),
        options: Some(options),
        type_acquisition: Some(type_acquisition),
        extended_config_path: Some(extended_config_path),
    };
    (parsed_config, errors)
}

// Go: tsoptions/tsconfigparsing.go:953 readJsonConfigFile
// PORT: the parser keeps source text for the program, so the text and the
// file name are leaked. The empty file gets its own node store, like the
// parsed one.
fn read_json_config_file(
    file_name: &str,
    path: Path,
    read_file: &dyn Fn(&str) -> (String, bool),
) -> (TsConfigSourceFile, Vec<Diagnostic>) {
    let (text, diagnostic) =
        try_read_file(file_name, &mut |name: &str| read_file(name), Vec::new());
    if !text.is_empty() {
        let source_file = parse_source_file(
            &SourceFileParseOptions {
                file_name: file_name.to_string(),
                path,
                ..Default::default()
            },
            Box::leak(text.into_boxed_str()),
            ScriptKind::JSON,
        );
        (
            TsConfigSourceFile {
                source_file: source_file.root,
                path: source_file.path().clone(),
                file_name: source_file.file_name().to_string(),
                ..Default::default()
            },
            diagnostic,
        )
    } else {
        let factory = NodeFactory::for_file(new_file_store(
            Box::leak(file_name.to_string().into_boxed_str()),
            "",
        ));
        let file = TsConfigSourceFile {
            path: path.clone(),
            file_name: file_name.to_string(),
            source_file: factory.new_parsed_source_file(
                &SourceFileParseOptions {
                    file_name: file_name.to_string(),
                    path,
                    ..Default::default()
                },
                "",
                factory.new_node_list(&[]),
                factory.new_token(SyntaxKind::EndOfFile),
            ),
            ..Default::default()
        };
        set_source_file_diagnostics(file.source_file, diagnostic.clone());
        (file, diagnostic)
    }
}

// Go: tsoptions/tsconfigparsing.go:972 getExtendedConfig
fn get_extended_config(
    source_file: Option<&TsConfigSourceFile>,
    extended_config_file_name: &str,
    host: &dyn ParseConfigHost,
    resolution_stack: &[Path],
    extended_config_cache: Option<&dyn ExtendedConfigCache>,
    result: &mut ExtendsResult,
) -> (Option<Rc<ParsedTsconfig>>, Vec<Diagnostic>) {
    let mut errors: Vec<Diagnostic> = Vec::new();
    let extended_config_path = to_path(
        extended_config_file_name,
        &host.get_current_directory(),
        host.fs().use_case_sensitive_file_names(),
    );

    // Bypass the cache when we detect a cycle in the resolution stack.
    // The cache locks entries during parsing, and a cycle would cause the same goroutine
    // to re-lock the same entry, resulting in a deadlock. Let parseConfig handle the
    // circularity error via its own resolution stack check.
    let cache_entry: Rc<ExtendedConfigCacheEntry> = match extended_config_cache {
        Some(cache) if !resolution_stack.contains(&extended_config_path) => cache
            .get_extended_config(
                extended_config_file_name,
                &extended_config_path,
                resolution_stack,
                host,
            ),
        _ => Rc::new(parse_extended_config(
            extended_config_file_name,
            extended_config_path,
            resolution_stack,
            host,
            extended_config_cache,
        )),
    };

    if !cache_entry.errors.is_empty() {
        errors.extend(cache_entry.errors.iter().cloned());
    }

    if let Some(extended_result) = &cache_entry.extended_result
        && source_file.is_some()
    {
        result
            .extended_source_files
            .insert(source_file_file_name(extended_result.source_file).to_string());
        for extended_source_file in &extended_result.extended_source_files {
            result
                .extended_source_files
                .insert(extended_source_file.clone());
        }
    }
    (cache_entry.extended_config.clone(), errors)
}

// Go: tsoptions/tsconfigparsing.go:1009 ParseExtendedConfig
// PORT: Go returns a pointer; this returns the value. Callers wrap it in
// `Rc` where Go shares it.
pub fn parse_extended_config(
    file_name: &str,
    path: Path,
    resolution_stack: &[Path],
    host: &dyn ParseConfigHost,
    extended_config_cache: Option<&dyn ExtendedConfigCache>,
) -> ExtendedConfigCacheEntry {
    let (mut extended_result, read_errors) =
        read_json_config_file(file_name, path, &|name| host.fs().read_file(name));
    let mut entry = ExtendedConfigCacheEntry::default();

    if !read_errors.is_empty() {
        entry.extended_result = Some(Rc::new(extended_result));
        entry.errors = read_errors;
        return entry;
    }

    let parse_diagnostics = parsed_source_file_diagnostics(extended_result.source_file);
    if !parse_diagnostics.is_empty() {
        entry.extended_result = Some(Rc::new(extended_result));
        entry.errors = parse_diagnostics.to_vec();
        return entry;
    }

    let (extended_config, parse_errors) = parse_config(
        None,
        Some(&mut extended_result),
        host,
        &get_directory_path(file_name),
        &get_base_file_name(file_name),
        resolution_stack,
        extended_config_cache,
    );
    entry.extended_result = Some(Rc::new(extended_result));
    entry.extended_config = Some(Rc::new(extended_config));
    entry.errors = parse_errors;
    entry
}

/// Go `rawMap.(*collections.OrderedMap[string, any])` with the `ok` form.
fn raw_as_map(raw: &CompilerOptionsValue) -> Option<&IndexMap<String, CompilerOptionsValue>> {
    match raw {
        CompilerOptionsValue::Map(m) => Some(m),
        _ => None,
    }
}

/// Go `ownConfig.raw.(*collections.OrderedMap[string, any])`, which panics
/// when the value is not a map.
fn raw_as_map_mut(raw: &mut CompilerOptionsValue) -> &mut IndexMap<String, CompilerOptionsValue> {
    match raw {
        CompilerOptionsValue::Map(m) => m,
        _ => panic!(
            "interface conversion: raw config is not *collections.OrderedMap[string,interface {{}}]"
        ),
    }
}

// parseConfig just extracts options/include/exclude/files out of a config file.
// It does not resolve the included files.
// Go: tsoptions/tsconfigparsing.go:1039 parseConfig
// PORT: Go `json` is a nilable map pointer (`Option`, owned). Go
// `sourceFile` is a nilable pointer that this function changes, so it is
// `Option<&mut TsConfigSourceFile>`. The Go `applyExtendedConfig` closure
// is inlined into the loop over the extended config paths. Go
// `extendedConfigPath` only ever holds a `[]string`, so the Go string case
// is not reachable and not ported.
pub fn parse_config(
    json: Option<IndexMap<String, CompilerOptionsValue>>,
    mut source_file: Option<&mut TsConfigSourceFile>,
    host: &dyn ParseConfigHost,
    base_path: &str,
    config_file_name: &str,
    resolution_stack: &[Path],
    extended_config_cache: Option<&dyn ExtendedConfigCache>,
) -> (ParsedTsconfig, Vec<Diagnostic>) {
    let base_path = normalize_slashes(base_path);
    let resolved_path = to_path(
        config_file_name,
        &base_path,
        host.fs().use_case_sensitive_file_names(),
    );
    let mut errors: Vec<Diagnostic> = Vec::new();
    if resolution_stack.contains(&resolved_path) {
        errors.push(new_compiler_diagnostic(
            diag::Circularity_detected_while_resolving_configuration_Colon_0,
            args![],
        ));
        let result;
        if json.as_ref().map_or(0, IndexMap::len) == 0 {
            // PORT: Go stores the (maybe nil) map pointer. A nil map is `Nil`.
            result = ParsedTsconfig {
                raw: json.map_or(CompilerOptionsValue::Nil, CompilerOptionsValue::Map),
                ..Default::default()
            };
        } else {
            // PORT: Go reads `sourceFile.SourceFile` here, which panics when
            // `sourceFile` is nil (the `json` path). Kept as Go does.
            let (raw_result, err) = convert_to_object(
                source_file
                    .as_deref()
                    .expect("nil pointer dereference: sourceFile")
                    .source_file,
            );
            errors.extend(err);
            result = ParsedTsconfig {
                raw: raw_result,
                ..Default::default()
            };
        }
        return (result, errors);
    }

    let (mut own_config, err) = match &json {
        Some(json) => parse_own_config_of_json(json, host, &base_path, config_file_name),
        None => parse_own_config_of_json_source_file(
            tsconfig_to_source_file(source_file.as_deref()),
            host,
            &base_path,
            config_file_name,
        ),
    };
    errors.extend(err);
    if let Some(options) = own_config.options.as_mut()
        && options.paths.is_some()
    {
        // If we end up needing to resolve relative paths from 'paths' relative to
        // the config file location, we'll need to know where that config file was.
        // Since 'paths' can be inherited from an extended config in another directory,
        // we wouldn't know which directory to use unless we store it here.
        options.paths_base_path = base_path.clone();
    }

    if let Some(extended_config_paths) = own_config.extended_config_path.clone() {
        // copy the resolution stack so it is never reused between branches in potential diamond-problem scenarios.
        let mut resolution_stack = resolution_stack.to_vec();
        resolution_stack.push(resolved_path);
        let mut result = ExtendsResult::default();
        for extended_config_path in &extended_config_paths {
            // Go: applyExtendedConfig(result, extendedConfigPath)
            let (extended_config, extended_errors) = get_extended_config(
                source_file.as_deref(),
                extended_config_path,
                host,
                &resolution_stack,
                extended_config_cache,
                &mut result,
            );
            errors.extend(extended_errors);
            if let Some(extended_config) = extended_config
                && extended_config.options.is_some()
            {
                let extends_raw = &extended_config.raw;
                let mut relative_difference = String::new();
                for property_name in ["include", "exclude", "files"] {
                    // Go: setPropertyValue(propertyName)
                    if let Some(raw_map) = raw_as_map(&own_config.raw)
                        && raw_map.contains_key(property_name)
                    {
                        continue;
                    }
                    if let Some(raw_map) = raw_as_map(extends_raw)
                        && raw_map.contains_key(property_name)
                        && let Some(CompilerOptionsValue::List(slice)) = raw_map.get(property_name)
                    {
                        // PORT: Go `path.(string)` panics for a non-string
                        // element; so does this port.
                        let value: Vec<CompilerOptionsValue> = slice
                            .iter()
                            .map(|path| {
                                let CompilerOptionsValue::String(path_str) = path else {
                                    panic!("interface conversion: path is not string");
                                };
                                if starts_with_config_dir_template(path)
                                    || is_rooted_disk_path(path_str)
                                {
                                    CompilerOptionsValue::String(path_str.clone())
                                } else {
                                    if relative_difference.is_empty() {
                                        let t = ComparePathsOptions {
                                            use_case_sensitive_file_names: host
                                                .fs()
                                                .use_case_sensitive_file_names(),
                                            current_directory: base_path.clone(),
                                        };
                                        relative_difference = convert_to_relative_path(
                                            &get_directory_path(extended_config_path),
                                            &t,
                                        );
                                    }
                                    CompilerOptionsValue::String(combine_paths(
                                        &relative_difference,
                                        &[path_str],
                                    ))
                                }
                            })
                            .collect();
                        match property_name {
                            "include" => result.include = Some(value),
                            "exclude" => result.exclude = Some(value),
                            _ => result.files = Some(value),
                        }
                    }
                }
                if let Some(extended_raw_map) = raw_as_map(extends_raw)
                    && extended_raw_map.contains_key("compileOnSave")
                    && let Some(CompilerOptionsValue::Bool(compile_on_save)) =
                        extended_raw_map.get("compileOnSave")
                {
                    result.compile_on_save = *compile_on_save;
                }
                merge_compiler_options(
                    &mut result.options,
                    extended_config.options.as_ref(),
                    raw_as_map(extends_raw),
                );
            }
        }
        if let Some(include) = result.include.take() {
            raw_as_map_mut(&mut own_config.raw)
                .insert("include".to_string(), CompilerOptionsValue::List(include));
        }
        if let Some(exclude) = result.exclude.take() {
            raw_as_map_mut(&mut own_config.raw)
                .insert("exclude".to_string(), CompilerOptionsValue::List(exclude));
        }
        if let Some(files) = result.files.take() {
            raw_as_map_mut(&mut own_config.raw)
                .insert("files".to_string(), CompilerOptionsValue::List(files));
        }
        if result.compile_on_save
            && !raw_as_map_mut(&mut own_config.raw).contains_key("compileOnSave")
        {
            raw_as_map_mut(&mut own_config.raw).insert(
                "compileOnSave".to_string(),
                CompilerOptionsValue::Bool(result.compile_on_save),
            );
        }
        if let Some(source_file) = source_file.as_deref_mut() {
            for extended_source_file in &result.extended_source_files {
                // Go: core.InsertSorted(..., cmp.Compare)
                let i = match source_file
                    .extended_source_files
                    .binary_search(extended_source_file)
                {
                    Ok(i) | Err(i) => i,
                };
                source_file
                    .extended_source_files
                    .insert(i, extended_source_file.clone());
            }
        }
        let own_options = own_config.options.take();
        merge_compiler_options(
            &mut result.options,
            own_options.as_ref(),
            raw_as_map(&own_config.raw),
        );
        own_config.options = Some(result.options);
        // ownConfig.watchOptions = ownConfig.watchOptions && result.watchOptions ?
        //     assignWatchOptions(result, ownConfig.watchOptions) :
        //     ownConfig.watchOptions || result.watchOptions;
    }
    (own_config, errors)
}

// Go: tsoptions/tsconfigparsing.go:1169 defaultIncludeSpec
const DEFAULT_INCLUDE_SPEC: &str = "**/*";

// Go: tsoptions/tsconfigparsing.go:1171 propOfRaw
// PORT: Go nil `sliceValue` is `None`.
struct PropOfRaw {
    slice_value: Option<Vec<CompilerOptionsValue>>,
    wrong_value: &'static str,
}

// Go: tsoptions/tsconfigparsing.go:1210 getPropFromRaw (closure in parseJsonConfigFileContentWorker)
// PORT: the Go closure is a private function. `is_json` is Go
// `sourceFile == nil`. Go `reflect.TypeOf(nil).Kind()` panics on a nil
// element; JSON conversion drops nil elements, so `validate_element` sees
// no `Nil`. A Go `[]string` value makes the `.([]any)` assertion panic;
// so does this port.
fn get_prop_from_raw(
    raw_config: &IndexMap<String, CompilerOptionsValue>,
    is_json: bool,
    errors: &mut Vec<Diagnostic>,
    prop: &str,
    validate_element: fn(&CompilerOptionsValue) -> bool,
    element_type_name: &str,
) -> PropOfRaw {
    if let Some(value) = raw_config.get(prop)
        && !value.is_nil()
    {
        match value {
            CompilerOptionsValue::List(result) => {
                if is_json && !result.iter().all(validate_element) {
                    errors.push(new_compiler_diagnostic(
                        diag::Compiler_option_0_requires_a_value_of_type_1,
                        args![prop, element_type_name],
                    ));
                }
                return PropOfRaw {
                    slice_value: Some(result.clone()),
                    wrong_value: "",
                };
            }
            CompilerOptionsValue::StringList(_) => {
                panic!("interface conversion: raw value is []string, not []interface {{}}");
            }
            _ => {
                if is_json {
                    errors.push(new_compiler_diagnostic(
                        diag::Compiler_option_0_requires_a_value_of_type_1,
                        args![prop, "Array"],
                    ));
                    return PropOfRaw {
                        slice_value: None,
                        wrong_value: "not-array",
                    };
                }
            }
        }
    }
    PropOfRaw {
        slice_value: None,
        wrong_value: "no-prop",
    }
}

/// Go `reflect.TypeOf(element) == orderedMapType`.
fn is_map_element(element: &CompilerOptionsValue) -> bool {
    matches!(element, CompilerOptionsValue::Map(_))
}

/// Go `reflect.TypeOf(element).Kind() == reflect.String`.
fn is_string_element(element: &CompilerOptionsValue) -> bool {
    matches!(element, CompilerOptionsValue::String(_))
}

/// Go `configFileSpecs` stores each `[]any` spec list in an `any`.
// PORT: a Go nil `[]any` in an `any` is not Go nil, but the only reader
// (the No_inputs diagnostic) prints it and a nil list alike as `[]`.
fn spec_list_value(specs: &Option<Vec<CompilerOptionsValue>>) -> CompilerOptionsValue {
    match specs {
        Some(specs) => CompilerOptionsValue::List(specs.clone()),
        None => CompilerOptionsValue::Nil,
    }
}

/// Go `core.StringifyJson(value, "", "")` for the spec lists. Go uses
/// `internal/json` (json v2): compact output, a nil slice is `[]`, and only
/// `"`, `\` and control characters are escaped.
// PORT: only the value kinds that JSON conversion makes are handled.
fn stringify_json(value: &CompilerOptionsValue, out: &mut String) {
    fn string(s: &str, out: &mut String) {
        out.push('"');
        for c in s.chars() {
            match c {
                '"' => out.push_str("\\\""),
                '\\' => out.push_str("\\\\"),
                '\u{8}' => out.push_str("\\b"),
                '\t' => out.push_str("\\t"),
                '\n' => out.push_str("\\n"),
                '\u{c}' => out.push_str("\\f"),
                '\r' => out.push_str("\\r"),
                c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
                c => out.push(c),
            }
        }
        out.push('"');
    }
    match value {
        CompilerOptionsValue::Nil => out.push_str("[]"),
        CompilerOptionsValue::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        CompilerOptionsValue::Int(i) => out.push_str(&i.to_string()),
        CompilerOptionsValue::Number(n) => out.push_str(&ts_jsnum::Number(*n).to_string()),
        CompilerOptionsValue::String(s) => string(s, out),
        CompilerOptionsValue::StringList(list) => {
            out.push('[');
            for (i, s) in list.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                string(s, out);
            }
            out.push(']');
        }
        CompilerOptionsValue::List(list) => {
            out.push('[');
            for (i, v) in list.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                if v.is_nil() {
                    out.push_str("null");
                } else {
                    stringify_json(v, out);
                }
            }
            out.push(']');
        }
        CompilerOptionsValue::Map(m) => {
            out.push('{');
            for (i, (k, v)) in m.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                string(k, out);
                out.push(':');
                if v.is_nil() {
                    out.push_str("null");
                } else {
                    stringify_json(v, out);
                }
            }
            out.push('}');
        }
        other => panic!("stringify_json: value kind not made by JSON conversion: {other:?}"),
    }
}

// parseJsonConfigFileContentWorker parses the contents of a config file from json or json source file (tsconfig.json).
// json: The contents of the config file to parse
// sourceFile: sourceFile corresponding to the Json
// host: Instance of ParseConfigHost used to enumerate files in folder.
// basePath: A root directory to resolve relative path entries in the config file to. e.g. outDir
// resolutionStack: Only present for backwards-compatibility. Should be empty.
// Go: tsoptions/tsconfigparsing.go:1182 parseJsonConfigFileContentWorker
// PORT: Go `sourceFile` is a pointer that the result keeps, so it moves in
// and into `ParsedCommandLine.config_file`. The Go `getFileNames` and
// `getProjectReferences` closures run inline, in Go order. When `parseConfig`
// hits a cycle, Go options are nil and `mergeCompilerOptions` panics if
// `existingOptions` is set; here the merge is skipped.
#[allow(clippy::too_many_arguments)]
pub fn parse_json_config_file_content_worker(
    json: Option<IndexMap<String, CompilerOptionsValue>>,
    source_file: Option<TsConfigSourceFile>,
    host: &dyn ParseConfigHost,
    base_path: &str,
    existing_options: Option<&CompilerOptions>,
    existing_options_raw: Option<&IndexMap<String, CompilerOptionsValue>>,
    config_file_name: &str,
    resolution_stack: &[Path],
    extra_file_extensions: &[FileExtensionInfo],
    extended_config_cache: Option<&dyn ExtendedConfigCache>,
) -> ParsedCommandLine {
    debug_assert!(
        (json.is_none() && source_file.is_some()) || (json.is_some() && source_file.is_none())
    );
    let mut source_file = source_file;

    let base_path_for_file_names = if !config_file_name.is_empty() {
        normalize_path(&directory_of_combined_path(config_file_name, base_path))
    } else {
        normalize_path(base_path)
    };

    let (mut parsed_config, mut errors) = parse_config(
        json,
        source_file.as_mut(),
        host,
        base_path,
        config_file_name,
        resolution_stack,
        extended_config_cache,
    );
    if let Some(options) = parsed_config.options.as_mut() {
        merge_compiler_options(options, existing_options, existing_options_raw);
    }
    handle_option_config_dir_template_substitution(
        parsed_config.options.as_mut(),
        &base_path_for_file_names,
    );
    // PORT: `parse_json_to_string_key` is always `Some`.
    let raw_config = parse_json_to_string_key(&parsed_config.raw).unwrap_or_default();
    if !config_file_name.is_empty()
        && let Some(options) = parsed_config.options.as_mut()
    {
        options.config_file_path = normalize_slashes(config_file_name);
    }
    let is_json = source_file.is_none();
    let references_of_raw = get_prop_from_raw(
        &raw_config,
        is_json,
        &mut errors,
        "references",
        is_map_element,
        "object",
    );
    let file_specs = get_prop_from_raw(
        &raw_config,
        is_json,
        &mut errors,
        "files",
        is_string_element,
        "string",
    );
    if file_specs.slice_value.is_some() || file_specs.wrong_value.is_empty() {
        let mut has_zero_or_no_references = false;
        if references_of_raw.wrong_value == "no-prop"
            || references_of_raw.wrong_value == "not-array"
            || references_of_raw.slice_value.as_ref().map_or(0, Vec::len) == 0
        {
            has_zero_or_no_references = true;
        }
        let has_extends = raw_config.get("extends").is_some_and(|v| !v.is_nil());
        if file_specs.slice_value.as_ref().is_some_and(Vec::is_empty)
            && has_zero_or_no_references
            && !has_extends
        {
            if let Some(source_file) = &source_file {
                let file_name = if !config_file_name.is_empty() {
                    config_file_name
                } else {
                    "tsconfig.json"
                };
                let diagnostic_message = diag::The_files_list_in_config_file_0_is_empty;
                let node_value =
                    for_each_tsconfig_prop_array(source_file.source_file, "files", |property| {
                        Some(property.initializer())
                    })
                    .unwrap_or(Node::NIL);
                errors.push(create_diagnostic_for_node_in_source_file(
                    source_file.source_file,
                    node_value,
                    diagnostic_message,
                    args![file_name],
                ));
            } else {
                errors.push(new_compiler_diagnostic(
                    diag::The_files_list_in_config_file_0_is_empty,
                    args![config_file_name],
                ));
            }
        }
    }
    let mut include_specs = get_prop_from_raw(
        &raw_config,
        is_json,
        &mut errors,
        "include",
        is_string_element,
        "string",
    );
    let mut exclude_specs = get_prop_from_raw(
        &raw_config,
        is_json,
        &mut errors,
        "exclude",
        is_string_element,
        "string",
    );
    let mut is_default_include_spec = false;
    if exclude_specs.wrong_value == "no-prop"
        && let Some(options) = &parsed_config.options
    {
        let out_dir = &options.out_dir;
        let declaration_dir = &options.declaration_dir;
        if !out_dir.is_empty() || !declaration_dir.is_empty() {
            let mut values: Vec<CompilerOptionsValue> = Vec::new();
            if !out_dir.is_empty() {
                values.push(CompilerOptionsValue::String(out_dir.clone()));
            }
            if !declaration_dir.is_empty() {
                values.push(CompilerOptionsValue::String(declaration_dir.clone()));
            }
            exclude_specs = PropOfRaw {
                slice_value: Some(values),
                wrong_value: "",
            };
        }
    }
    if file_specs.slice_value.is_none() && include_specs.slice_value.is_none() {
        include_specs = PropOfRaw {
            slice_value: Some(vec![CompilerOptionsValue::String(
                DEFAULT_INCLUDE_SPEC.to_string(),
            )]),
            wrong_value: "",
        };
        is_default_include_spec = true;
    }
    let mut validated_include_specs: Vec<String> = Vec::new();
    let mut validated_include_specs_before_substitution: Vec<String> = Vec::new();
    let mut validated_exclude_specs: Vec<String> = Vec::new();
    let mut validated_files_spec: Vec<String> = Vec::new();
    let mut validated_files_spec_before_substitution: Vec<String> = Vec::new();
    let tsconfig_node = tsconfig_to_source_file(source_file.as_ref());
    // The exclude spec list is converted into a regular expression, which allows us to quickly
    // test whether a file or directory should be excluded before recursively traversing the
    // file system.
    if let Some(specs) = &include_specs.slice_value {
        let err;
        (validated_include_specs_before_substitution, err) = validate_specs(
            specs,
            true, /*disallowTrailingRecursion*/
            tsconfig_node,
            "include",
        );
        errors.extend(err);
        validated_include_specs = match get_substituted_string_array_with_config_dir_template(
            &validated_include_specs_before_substitution,
            &base_path_for_file_names,
        ) {
            Some(substituted) => substituted,
            None => validated_include_specs_before_substitution.clone(),
        };
    }
    if let Some(specs) = &exclude_specs.slice_value {
        let err;
        (validated_exclude_specs, err) = validate_specs(
            specs,
            false, /*disallowTrailingRecursion*/
            tsconfig_node,
            "exclude",
        );
        errors.extend(err);
        if let Some(validated_exclude_specs_with_substitution) =
            get_substituted_string_array_with_config_dir_template(
                &validated_exclude_specs,
                &base_path_for_file_names,
            )
        {
            validated_exclude_specs = validated_exclude_specs_with_substitution;
        }
    }
    if let Some(specs) = &file_specs.slice_value {
        for spec in specs {
            if let CompilerOptionsValue::String(spec) = spec {
                validated_files_spec_before_substitution.push(spec.clone());
            }
        }
        validated_files_spec = match get_substituted_string_array_with_config_dir_template(
            &validated_files_spec_before_substitution,
            &base_path_for_file_names,
        ) {
            Some(substituted) => substituted,
            None => validated_files_spec_before_substitution.clone(),
        };
    }
    let config_file_specs = ConfigFileSpecs {
        files_specs: spec_list_value(&file_specs.slice_value),
        include_specs: spec_list_value(&include_specs.slice_value),
        exclude_specs: spec_list_value(&exclude_specs.slice_value),
        validated_files_spec,
        validated_include_specs,
        validated_exclude_specs,
        validated_files_spec_before_substitution,
        validated_include_specs_before_substitution,
        is_default_include_spec,
    };

    if let Some(source_file) = source_file.as_mut() {
        source_file.config_file_specs = Some(config_file_specs.clone());
    }

    // Go: getFileNames(basePathForFileNames)
    let (file_names, literal_file_names_len) = {
        let parsed_config_options = parsed_config.options.as_ref();
        let (file_names, literal_file_names_len) = get_file_names_from_config_specs(
            &config_file_specs,
            &base_path_for_file_names,
            parsed_config_options,
            &*host.fs(),
            extra_file_extensions,
        );
        if should_report_no_input_files(
            &file_names,
            can_json_report_no_input_files(&raw_config),
            resolution_stack,
        ) {
            let mut include_json = String::new();
            stringify_json(&config_file_specs.include_specs, &mut include_json);
            let mut exclude_json = String::new();
            stringify_json(&config_file_specs.exclude_specs, &mut exclude_json);
            errors.push(new_compiler_diagnostic(
                diag::No_inputs_were_found_in_config_file_0_Specified_include_paths_were_1_and_exclude_paths_were_2,
                args![config_file_name, include_json, exclude_json],
            ));
        }
        (file_names, literal_file_names_len)
    };

    // Go: getProjectReferences(basePathForFileNames)
    let mut project_references: Vec<ProjectReference> = Vec::new();
    let new_references_of_raw = get_prop_from_raw(
        &raw_config,
        is_json,
        &mut errors,
        "references",
        is_map_element,
        "object",
    );
    if let Some(references) = &new_references_of_raw.slice_value {
        for reference in references {
            for r in parse_project_reference(reference) {
                if r.path.is_empty() {
                    if is_json {
                        errors.push(new_compiler_diagnostic(
                            diag::Compiler_option_0_requires_a_value_of_type_1,
                            args!["reference.path", "string"],
                        ));
                    }
                } else {
                    project_references.push(ProjectReference {
                        path: get_normalized_absolute_path(&r.path, &base_path_for_file_names),
                        original_path: r.path.clone(),
                        circular: r.circular,
                    });
                }
            }
        }
    }

    ParsedCommandLine {
        parsed_config: ParsedOptions {
            // PORT: Go nil options become the default options.
            compiler_options: Rc::new(parsed_config.options.unwrap_or_default()),
            type_acquisition: parsed_config.type_acquisition,
            // WatchOptions:      nil,
            file_names,
            project_references,
        },
        config_file: source_file.map(Rc::new),
        raw: parsed_config.raw,
        errors,

        extra_file_extensions: extra_file_extensions.to_vec(),
        compare_paths_options: ComparePathsOptions {
            use_case_sensitive_file_names: host.fs().use_case_sensitive_file_names(),
            current_directory: base_path_for_file_names,
        },
        literal_file_names_len,
        ..Default::default()
    }
}

// Go: tsoptions/tsconfigparsing.go:1388 canJsonReportNoInputFiles
fn can_json_report_no_input_files(raw_config: &IndexMap<String, CompilerOptionsValue>) -> bool {
    let files_exists = raw_config.contains_key("files");
    let references_exists = raw_config.contains_key("references");
    !files_exists && !references_exists
}

// Go: tsoptions/tsconfigparsing.go:1394 shouldReportNoInputFiles
fn should_report_no_input_files(
    file_names: &[String],
    can_json_report_no_input_files: bool,
    resolution_stack: &[Path],
) -> bool {
    file_names.is_empty() && can_json_report_no_input_files && resolution_stack.is_empty()
}

// Go: tsoptions/tsconfigparsing.go:1398 validateSpecs
// PORT: Go `specs any` always holds a `[]any`, so it is a slice here.
fn validate_specs(
    specs: &[CompilerOptionsValue],
    disallow_trailing_recursion: bool,
    json_source_file: Node,
    spec_key: &str,
) -> (Vec<String>, Vec<Diagnostic>) {
    let create_diagnostic = |message: &'static Message, spec: &str| -> Diagnostic {
        let element = get_tsconfig_prop_array_element_value(json_source_file, spec_key, spec);
        create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
            json_source_file,
            element,
            message,
            args![spec],
        )
    };
    let mut errors: Vec<Diagnostic> = Vec::new();
    let mut final_specs: Vec<String> = Vec::new();
    for spec in specs {
        let CompilerOptionsValue::String(spec) = spec else {
            continue;
        };
        let diag = spec_to_diagnostic(spec, disallow_trailing_recursion);
        if let Some(diag) = diag {
            errors.push(create_diagnostic(diag, spec));
        } else {
            final_specs.push(spec.clone());
        }
    }
    (final_specs, errors)
}

// Go: tsoptions/tsconfigparsing.go:1423 specToDiagnostic
pub(crate) fn spec_to_diagnostic(
    spec: &str,
    disallow_trailing_recursion: bool,
) -> Option<&'static Message> {
    if disallow_trailing_recursion && invalid_trailing_recursion(spec) {
        return Some(diag::File_specification_cannot_end_in_a_recursive_directory_wildcard_Asterisk_Asterisk_Colon_0);
    }
    if invalid_dot_dot_after_recursive_wildcard(spec) {
        return Some(
            diag::File_specification_cannot_contain_a_parent_directory_that_appears_after_a_recursive_directory_wildcard_Asterisk_Asterisk_Colon_0,
        );
    }
    None
}

// Go: tsoptions/tsconfigparsing.go:1433 invalidTrailingRecursion
fn invalid_trailing_recursion(spec: &str) -> bool {
    // Matches **, /**, **/, and /**/, but not a**b.
    // Strip optional trailing slash, then check if it ends with /** or is just **
    let s = spec.strip_suffix('/').unwrap_or(spec);
    s == "**" || s.ends_with("/**")
}

// Go: tsoptions/tsconfigparsing.go:1440 invalidDotDotAfterRecursiveWildcard
// PORT: Go string indexes are byte offsets, as are Rust `find` results.
fn invalid_dot_dot_after_recursive_wildcard(s: &str) -> bool {
    // We used to use the regex /(^|\/)\*\*\/(.*\/)?\.\.($|\/)/ to check for this case, but
    // in v8, that has polynomial performance because the recursive wildcard match - **/ -
    // can be matched in many arbitrary positions when multiple are present, resulting
    // in bad backtracking (and we don't care which is matched - just that some /.. segment
    // comes after some **/ segment).
    let wildcard_index: i64 = if s.starts_with("**/") {
        0
    } else {
        s.find("/**/").map_or(-1, |i| i as i64)
    };
    if wildcard_index == -1 {
        return false;
    }
    let last_dot_index: i64 = if s.ends_with("/..") {
        s.len() as i64
    } else {
        s.rfind("/../").map_or(-1, |i| i as i64)
    };
    last_dot_index > wildcard_index
}

// Go: tsoptions/tsconfigparsing.go:1464 GetTsConfigPropArrayElementValue
// PORT: Go returns `*ast.StringLiteral`; that is a `Node` (`NIL` for nil).
pub fn get_tsconfig_prop_array_element_value(
    tsconfig_source_file: Node,
    prop_key: &str,
    element_value: &str,
) -> Node {
    let callback = get_callback_for_finding_property_assignment_by_value(element_value);
    for_each_tsconfig_prop_array(tsconfig_source_file, prop_key, |property| {
        callback(property)
    })
    .unwrap_or(Node::NIL)
}

// Go: tsoptions/tsconfigparsing.go:1474 ForEachTsConfigPropArray
// PORT: Go `*T` results are `Option<T>`.
pub fn for_each_tsconfig_prop_array<T>(
    tsconfig_source_file: Node,
    prop_key: &str,
    callback: impl FnMut(Node) -> Option<T>,
) -> Option<T> {
    if tsconfig_source_file.is_some() {
        return for_each_property_assignment(
            get_tsconfig_object_literal_expression(tsconfig_source_file),
            prop_key,
            callback,
            &[],
        );
    }
    None
}

// Go: tsoptions/tsconfigparsing.go:1481 CreateDiagnosticAtReferenceSyntax
// PORT: Go returns a nilable `*ast.Diagnostic`; that is `Option`. Go reads
// `config.ConfigFile.SourceFile`, which panics for a nil `ConfigFile`.
pub fn create_diagnostic_at_reference_syntax(
    config: &ParsedCommandLine,
    index: usize,
    message: &'static Message,
    args: Vec<String>,
) -> Option<Diagnostic> {
    let source_file = config
        .config_file
        .as_ref()
        .expect("nil pointer dereference: config.ConfigFile")
        .source_file;
    for_each_tsconfig_prop_array(source_file, "references", |property| {
        if is_array_literal_expression(property.initializer()) {
            let value = property.initializer().elements();
            if value.len() > index {
                return Some(create_diagnostic_for_node_in_source_file(
                    source_file,
                    value.get(index),
                    message,
                    args.clone(),
                ));
            }
        }
        None
    })
}

// Go: tsoptions/tsconfigparsing.go:1493 GetCallbackForFindingPropertyAssignmentByValue
pub fn get_callback_for_finding_property_assignment_by_value(
    value: &str,
) -> impl Fn(Node) -> Option<Node> + use<> {
    let value = value.to_string();
    move |property: Node| -> Option<Node> {
        if is_array_literal_expression(property.initializer()) {
            return property
                .initializer()
                .elements()
                .iter()
                .find(|element| is_string_literal(*element) && element.text() == value);
        }
        None
    }
}

// Go: tsoptions/tsconfigparsing.go:1504 GetOptionsSyntaxByArrayElementValue
pub fn get_options_syntax_by_array_element_value(
    object_literal: Node,
    prop_key: &str,
    element_value: &str,
) -> Node {
    for_each_property_assignment(
        object_literal,
        prop_key,
        get_callback_for_finding_property_assignment_by_value(element_value),
        &[],
    )
    .unwrap_or(Node::NIL)
}

// Go: tsoptions/tsconfigparsing.go:1508 ForEachPropertyAssignment
// PORT: Go `*T` results are `Option<T>`. The Go variadic `key2` is a slice.
pub fn for_each_property_assignment<T>(
    object_literal: Node,
    key: &str,
    mut callback: impl FnMut(Node) -> Option<T>,
    key2: &[&str],
) -> Option<T> {
    if object_literal.is_some() {
        for property in object_literal.properties().iter() {
            if !is_property_assignment(property) {
                continue;
            }
            let (prop_name, ok) = try_get_text_of_property_name(property.name());
            if ok && (prop_name == key || (!key2.is_empty() && key2[0] == prop_name)) {
                return callback(property);
            }
        }
    }
    None
}

// Go: tsoptions/tsconfigparsing.go:1524 getTsConfigObjectLiteralExpression
fn get_tsconfig_object_literal_expression(tsconfig_source_file: Node) -> Node {
    if tsconfig_source_file.is_some() {
        let statements = tsconfig_source_file.statements();
        if !statements.is_empty() {
            let expression = statements.get(0).expression();
            if is_object_literal_expression(expression) {
                return expression;
            }
        }
    }
    Node::NIL
}

// Go: tsoptions/tsconfigparsing.go:1534 getSubstitutedPathWithConfigDirTemplate
fn get_substituted_path_with_config_dir_template(value: &str, base_path: &str) -> String {
    get_normalized_absolute_path(&value.replacen(CONFIG_DIR_TEMPLATE, "./", 1), base_path)
}

// Go: tsoptions/tsconfigparsing.go:1538 getSubstitutedStringArrayWithConfigDirTemplate
// PORT: Go returns a nil slice for "no change"; that is `None`. Go passes
// the string as `any` to `startsWithConfigDirTemplate`.
fn get_substituted_string_array_with_config_dir_template(
    list: &[String],
    base_path: &str,
) -> Option<Vec<String>> {
    let mut result: Option<Vec<String>> = None;
    for (i, element) in list.iter().enumerate() {
        if starts_with_config_dir_template(&CompilerOptionsValue::String(element.clone())) {
            let result = result.get_or_insert_with(|| list.to_vec());
            result[i] = get_substituted_path_with_config_dir_template(element, base_path);
        }
    }
    result
}

// Go: tsoptions/tsconfigparsing.go:1554 handleOptionConfigDirTemplateSubstitution
// PORT: Go `mergeCompilerOptions` copies the `Paths` pointer, so in Go this
// also changes `paths` of a cached extended config. Here each options value
// owns its `paths`, so only this config changes.
fn handle_option_config_dir_template_substitution(
    compiler_options: Option<&mut CompilerOptions>,
    base_path: &str,
) {
    let Some(compiler_options) = compiler_options else {
        return;
    };

    // !!! don't hardcode this; use options declarations?

    if let Some(paths) = compiler_options.paths.as_mut() {
        for v in paths.values_mut() {
            if let Some(substitution) =
                get_substituted_string_array_with_config_dir_template(v, base_path)
            {
                *v = substitution;
            }
        }
    }

    if let Some(root_dirs) = get_substituted_string_array_with_config_dir_template(
        &compiler_options.root_dirs,
        base_path,
    ) {
        compiler_options.root_dirs = root_dirs;
    }
    if let Some(type_roots) = compiler_options.type_roots.as_deref()
        && let Some(type_roots) =
            get_substituted_string_array_with_config_dir_template(type_roots, base_path)
    {
        compiler_options.type_roots = Some(type_roots);
    }
    macro_rules! substitute_string_fields {
        ($($field:ident),*) => {
            $(
                if starts_with_config_dir_template(&CompilerOptionsValue::String(compiler_options.$field.clone())) {
                    compiler_options.$field = get_substituted_path_with_config_dir_template(&compiler_options.$field, base_path);
                }
            )*
        };
    }
    substitute_string_fields!(
        generate_cpu_profile,
        generate_trace,
        out_file,
        out_dir,
        root_dir,
        ts_build_info_file,
        base_url,
        declaration_dir
    );
}

/// Go `[]string` extension group as the `&[&str]` that tspath takes.
fn str_group(group: &[String]) -> Vec<&str> {
    group.iter().map(String::as_str).collect()
}

// hasFileWithHigherPriorityExtension determines whether a literal or wildcard file has already been included that has a higher extension priority.
// file is the path to the file.
// Go: tsoptions/tsconfigparsing.go:1601 hasFileWithHigherPriorityExtension
fn has_file_with_higher_priority_extension(
    file: &str,
    extensions: &[Vec<String>],
    has_file: impl Fn(&str) -> bool,
) -> bool {
    let mut extension_group: Vec<&str> = Vec::new();
    for group in extensions {
        if file_extension_is_one_of(file, &str_group(group)) {
            extension_group.extend(group.iter().map(String::as_str));
        }
    }
    if extension_group.is_empty() {
        return false;
    }
    for ext in extension_group {
        // d.ts files match with .ts extension and with case sensitive sorting the file order for same files with ts tsx and dts extension is
        // d.ts, .ts, .tsx in that order so we need to handle tsx and dts of same same name case here and in remove files with same extensions
        // So dont match .d.ts files with .ts extension
        if file_extension_is(file, ext)
            && (ext != EXTENSION_TS || !file_extension_is(file, EXTENSION_DTS))
        {
            return false;
        }
        if has_file(&change_extension(file, ext)) {
            if ext == EXTENSION_DTS
                && (file_extension_is(file, EXTENSION_JS) || file_extension_is(file, EXTENSION_JSX))
            {
                // LEGACY BEHAVIOR: An off-by-one bug somewhere in the extension priority system for wildcard module loading allowed declaration
                // files to be loaded alongside their js(x) counterparts. We regard this as generally undesirable, but retain the behavior to
                // prevent breakage.
                continue;
            }
            return true;
        }
    }
    false
}

// Removes files included via wildcard expansion with a lower extension priority that have already been included.
// file is the path to the file.
// Go: tsoptions/tsconfigparsing.go:1633 removeWildcardFilesWithLowerPriorityExtension
// PORT: Go `OrderedMap.Delete` keeps the order of the other keys, like
// `shift_remove`.
fn remove_wildcard_files_with_lower_priority_extension(
    file: &str,
    wildcard_files: &mut IndexMap<String, String>,
    extensions: &[Vec<String>],
    key_mapper: impl Fn(&str) -> String,
) {
    let mut extension_group: Vec<&str> = Vec::new();
    for group in extensions {
        if file_extension_is_one_of(file, &str_group(group)) {
            extension_group.extend(group.iter().map(String::as_str));
        }
    }
    if extension_group.is_empty() {
        return;
    }
    for ext in extension_group.iter().rev() {
        if file_extension_is(file, ext) {
            return;
        }
        let lower_priority_path = key_mapper(&change_extension(file, ext));
        wildcard_files.shift_remove(&lower_priority_path);
    }
}

// getFileNamesFromConfigSpecs gets the file names from the provided config file specs that contain, files, include, exclude and
// other properties needed to resolve the file names
// configFileSpecs is the config file specs extracted with file names to include, wildcards to include/exclude and other details
// basePath is the base path for any relative file specifications.
// options is the Compiler options.
// host is the host used to resolve files and directories.
// extraFileExtensions optionally file extra file extension information from host
// Go: tsoptions/tsconfigparsing.go:1660 getFileNamesFromConfigSpecs
// PORT: Go `options` can be nil only after a config cycle; Go
// `GetSupportedExtensions` then panics on the nil pointer, and so does this
// port.
pub(crate) fn get_file_names_from_config_specs(
    config_file_specs: &ConfigFileSpecs,
    base_path: &str, // considering this is the current directory
    options: Option<&CompilerOptions>,
    host: &dyn Fs,
    extra_file_extensions: &[FileExtensionInfo],
) -> (Vec<String>, i32) {
    let _ = extra_file_extensions;
    let extra_file_extensions: &[FileExtensionInfo] = &[];
    let base_path = normalize_path(base_path);
    let key_mappper = |value: &str| -> String {
        get_canonical_file_name(value, host.use_case_sensitive_file_names())
    };
    // Literal file names (provided via the "files" array in tsconfig.json) are stored in a
    // file map with a possibly case insensitive key. We use this map later when when including
    // wildcard paths.
    let mut literal_file_map: IndexMap<String, String> = IndexMap::new();
    // Wildcard paths (provided via the "includes" array in tsconfig.json) are stored in a
    // file map with a possibly case insensitive key. We use this map to store paths matched
    // via wildcard, and to handle extension priority.
    let mut wildcard_file_map: IndexMap<String, String> = IndexMap::new();
    // Wildcard paths of json files (provided via the "includes" array in tsconfig.json) are stored in a
    // file map with a possibly case insensitive key. We use this map to store paths matched
    // via wildcard of *.json kind
    let mut wild_card_json_file_map: IndexMap<String, String> = IndexMap::new();
    let validated_files_spec = &config_file_specs.validated_files_spec;
    let validated_include_specs = &config_file_specs.validated_include_specs;
    let validated_exclude_specs = &config_file_specs.validated_exclude_specs;
    // Rather than re-query this for each file and filespec, we query the supported extensions
    // once and store it on the expansion context.
    let supported_extensions = get_supported_extensions(
        options.expect("nil pointer dereference: options"),
        extra_file_extensions,
    );
    let supported_extensions_with_json_if_resolve_json_module =
        get_supported_extensions_with_json_if_resolve_json_module(
            options,
            supported_extensions.clone(),
        );
    // Literal files are always included verbatim. An "include" or "exclude" specification cannot
    // remove a literal file.
    for file_name in validated_files_spec {
        let file = get_normalized_absolute_path(file_name, &base_path);
        literal_file_map.insert(key_mappper(file_name), file);
    }

    let mut json_only_include_matchers: Option<SpecMatcher> = None;
    if !validated_include_specs.is_empty() {
        let flat_extensions: Vec<String> = supported_extensions_with_json_if_resolve_json_module
            .iter()
            .flatten()
            .cloned()
            .collect();
        let files = read_directory(
            host,
            &base_path,
            &base_path,
            &flat_extensions,
            validated_exclude_specs,
            validated_include_specs,
            UNLIMITED_DEPTH,
        );
        for file in &files {
            if file_extension_is(file, EXTENSION_JSON) {
                if json_only_include_matchers.is_none() {
                    let includes: Vec<String> = validated_include_specs
                        .iter()
                        .filter(|include| include.ends_with(EXTENSION_JSON))
                        .cloned()
                        .collect();
                    json_only_include_matchers = new_spec_matcher(
                        &includes,
                        &base_path,
                        Usage::Files,
                        host.use_case_sensitive_file_names(),
                    );
                }
                let mut include_index: i32 = -1;
                if let Some(matchers) = &json_only_include_matchers {
                    include_index = matchers.match_index(file);
                }
                if include_index != -1 {
                    let key = key_mappper(file);
                    if !literal_file_map.contains_key(&key)
                        && !wild_card_json_file_map.contains_key(&key)
                    {
                        wild_card_json_file_map.insert(key, file.clone());
                    }
                }
                continue;
            }
            // If we have already included a literal or wildcard path with a
            // higher priority extension, we should skip this file.
            //
            // This handles cases where we may encounter both <file>.ts and
            // <file>.d.ts (or <file>.js if "allowJs" is enabled) in the same
            // directory when they are compilation outputs.
            if has_file_with_higher_priority_extension(file, &supported_extensions, |file_name| {
                let canonical_file_name = key_mappper(file_name);
                literal_file_map.contains_key(&canonical_file_name)
                    || wildcard_file_map.contains_key(&canonical_file_name)
            }) {
                continue;
            }
            // We may have included a wildcard path with a lower priority
            // extension due to the user-defined order of entries in the
            // "include" array. If there is a lower priority extension in the
            // same directory, we should remove it.
            remove_wildcard_files_with_lower_priority_extension(
                file,
                &mut wildcard_file_map,
                &supported_extensions,
                key_mappper,
            );
            let key = key_mappper(file);
            if !literal_file_map.contains_key(&key) && !wildcard_file_map.contains_key(&key) {
                wildcard_file_map.insert(key, file.clone());
            }
        }
    }
    let mut files: Vec<String> = Vec::with_capacity(
        literal_file_map.len() + wildcard_file_map.len() + wild_card_json_file_map.len(),
    );
    files.extend(literal_file_map.values().cloned());
    files.extend(wildcard_file_map.values().cloned());
    files.extend(wild_card_json_file_map.values().cloned());
    (files, literal_file_map.len() as i32)
}

/// Go `[][]string` copy of a tspath extension table.
fn owned_groups(groups: &[&[&str]]) -> Vec<Vec<String>> {
    groups
        .iter()
        .map(|group| group.iter().map(|ext| (*ext).to_string()).collect())
        .collect()
}

// Go: tsoptions/tsconfigparsing.go:1753 GetSupportedExtensions
// PORT: Go returns the shared tspath tables; this returns owned copies.
pub fn get_supported_extensions(
    compiler_options: &CompilerOptions,
    extra_file_extensions: &[FileExtensionInfo],
) -> Vec<Vec<String>> {
    let need_js_extensions = compiler_options.get_allow_js();
    if extra_file_extensions.is_empty() {
        if need_js_extensions {
            return owned_groups(ALL_SUPPORTED_EXTENSIONS);
        } else {
            return owned_groups(SUPPORTED_TS_EXTENSIONS);
        }
    }
    let builtins = if need_js_extensions {
        owned_groups(ALL_SUPPORTED_EXTENSIONS)
    } else {
        owned_groups(SUPPORTED_TS_EXTENSIONS)
    };
    let flat_builtins: Vec<&String> = builtins.iter().flatten().collect();
    let mut result: Vec<Vec<String>> = Vec::new();
    for x in extra_file_extensions {
        if x.script_kind == ScriptKind::DEFERRED
            || (need_js_extensions
                && (x.script_kind == ScriptKind::JS || x.script_kind == ScriptKind::JSX))
                && !flat_builtins.contains(&&x.extension)
        {
            result.push(vec![x.extension.clone()]);
        }
    }
    let mut extensions = builtins.clone();
    extensions.extend(result);
    extensions
}

// Go: tsoptions/tsconfigparsing.go:1779 GetSupportedExtensionsWithJsonIfResolveJsonModule
// PORT: Go `core.Same` compares slice identity. Content equality gives the
// same result here: a new Go slice equal to a tspath table gets `.json`
// appended, which equals the matching `WITH_JSON` table.
pub fn get_supported_extensions_with_json_if_resolve_json_module(
    compiler_options: Option<&CompilerOptions>,
    supported_extensions: Vec<Vec<String>>,
) -> Vec<Vec<String>> {
    let Some(compiler_options) = compiler_options else {
        return supported_extensions;
    };
    if !compiler_options.get_resolve_json_module() {
        return supported_extensions;
    }
    if supported_extensions == owned_groups(ALL_SUPPORTED_EXTENSIONS) {
        return owned_groups(ALL_SUPPORTED_EXTENSIONS_WITH_JSON);
    }
    if supported_extensions == owned_groups(SUPPORTED_TS_EXTENSIONS) {
        return owned_groups(SUPPORTED_TS_EXTENSIONS_WITH_JSON);
    }
    let mut result = supported_extensions;
    result.push(vec![EXTENSION_JSON.to_string()]);
    result
}

// Reads the config file and reports errors.
// Go: tsoptions/tsconfigparsing.go:1793 GetParsedCommandLineOfConfigFile
// PORT: Go returns a nilable `*ParsedCommandLine`; that is `Option`.
pub fn get_parsed_command_line_of_config_file(
    config_file_name: &str,
    options: Option<&CompilerOptions>,
    options_raw: Option<&IndexMap<String, CompilerOptionsValue>>,
    sys: &dyn ParseConfigHost,
    extended_config_cache: Option<&dyn ExtendedConfigCache>,
) -> (Option<ParsedCommandLine>, Vec<Diagnostic>) {
    let config_file_name =
        get_normalized_absolute_path(config_file_name, &sys.get_current_directory());
    let path = to_path(
        &config_file_name,
        &sys.get_current_directory(),
        sys.fs().use_case_sensitive_file_names(),
    );
    get_parsed_command_line_of_config_file_path(
        &config_file_name,
        path,
        options,
        options_raw,
        sys,
        extended_config_cache,
    )
}

// Go: tsoptions/tsconfigparsing.go:1804 GetParsedCommandLineOfConfigFilePath
pub fn get_parsed_command_line_of_config_file_path(
    config_file_name: &str,
    path: Path,
    options: Option<&CompilerOptions>,
    options_raw: Option<&IndexMap<String, CompilerOptionsValue>>,
    sys: &dyn ParseConfigHost,
    extended_config_cache: Option<&dyn ExtendedConfigCache>,
) -> (Option<ParsedCommandLine>, Vec<Diagnostic>) {
    let errors: Vec<Diagnostic> = Vec::new();
    let (config_file_text, errors) = try_read_file(
        config_file_name,
        &mut |name: &str| sys.fs().read_file(name),
        errors,
    );
    if !errors.is_empty() {
        // these are unrecoverable errors--exit to report them as diagnostics
        return (None, errors);
    }

    let ts_config_source_file =
        new_tsconfig_source_file_from_file_path(config_file_name, path, &config_file_text);
    // tsConfigSourceFile.resolvedPath = tsConfigSourceFile.FileName()
    // tsConfigSourceFile.originalFileName = tsConfigSourceFile.FileName()
    (
        Some(parse_json_source_file_config_file_content(
            ts_config_source_file,
            sys,
            &get_directory_path(config_file_name),
            options,
            options_raw,
            config_file_name,
            &[],
            &[],
            extended_config_cache,
        )),
        Vec::new(),
    )
}
