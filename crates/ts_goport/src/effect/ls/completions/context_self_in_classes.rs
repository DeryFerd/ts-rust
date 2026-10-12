//! Port of Effect-TS/tsgo `internal/completions/context_self_in_classes.go`
//! (effect-tsgo 0.51.1), with the service tag key helpers.

use super::effect_schema_self_in_classes::{byte_span_to_range, make_extends_completion_item};
use crate::effect::keybuilder;
use crate::effect::ls::completion::{
    Completion, CompletionContext, parse_data_for_extends_class_completion,
};
use crate::effect::pluginoptions::resolve_effect_plugin_options_for_source_file;
use crate::effect::typeparser::{EffectMajorVersion, TypeParser, find_module_identifier, member};
use crate::ls::prelude::*;

// Go: completions/context_self_in_classes.go:18 contextSelfInClasses
/// contextSelfInClasses provides completion items for Effect context/service class
/// constructors when the cursor is in the extends clause of a class declaration.
pub static CONTEXT_SELF_IN_CLASSES: Completion = Completion {
    name: "contextSelfInClasses",
    description: "Provides Context.Tag / Context.Service completions in extends clauses",
    run: run_context_self_in_classes,
};

// Go: completions/context_self_in_classes.go:24 runContextSelfInClasses
fn run_context_self_in_classes(
    ctx: &mut CompletionContext<'_, '_>,
) -> Vec<lsproto::CompletionItem> {
    let Some(data) = parse_data_for_extends_class_completion(ctx.source_file, ctx.position) else {
        return Vec::new();
    };

    let version = ctx.tp.supported_effect_version();
    let class_name = data.class_name_text();
    let replacement_range =
        byte_span_to_range(ctx, data.replacement_start, data.replacement_length);
    let sort_text = "11";
    let tag_key = compute_service_tag_key(ctx.program, ctx.tp, ctx.source_file, &class_name);

    let context_identifier = find_module_identifier(ctx.source_file, "Context");
    let accessed_text = data.accessed_object_text();
    let is_fully_qualified = context_identifier == accessed_text;

    if version == EffectMajorVersion::V3 {
        if !is_fully_qualified
            && !ctx.tp.is_node_reference_to_effect_context_module_api(
                data.accessed_object,
                member!("Tag"),
            )
        {
            return Vec::new();
        }

        let insert_text = if is_fully_qualified {
            format!(r#"{context_identifier}.Tag("{tag_key}")<{class_name}, ${{0}}>(){{}}"#)
        } else {
            format!(r#"Tag("{tag_key}")<{class_name}, ${{0}}>(){{}}"#)
        };

        return vec![make_extends_completion_item(
            &accessed_text,
            format!(r#"Tag("{class_name}")"#),
            insert_text,
            sort_text,
            replacement_range,
        )];
    }

    if !is_fully_qualified
        && !ctx.tp.is_node_reference_to_effect_context_module_api(
            data.accessed_object,
            member!("Service"),
        )
    {
        return Vec::new();
    }

    let mut items = Vec::new();
    {
        let insert_text = if is_fully_qualified {
            format!(r#"{context_identifier}.Service<{class_name}, {{${{0}}}}>()("{tag_key}"){{}}"#)
        } else {
            format!(r#"Service<{class_name}, {{${{0}}}}>()("{tag_key}"){{}}"#)
        };
        items.push(make_extends_completion_item(
            &accessed_text,
            format!("Service<{class_name}, {{}}>"),
            insert_text,
            sort_text,
            replacement_range,
        ));
    }
    {
        let insert_text = if is_fully_qualified {
            format!(
                r#"{context_identifier}.Service<{class_name}>()("{tag_key}", {{ make: ${{0}} }}){{}}"#
            )
        } else {
            format!(r#"Service<{class_name}>()("{tag_key}", {{ make: ${{0}} }}){{}}"#)
        };
        items.push(make_extends_completion_item(
            &accessed_text,
            format!("Service<{class_name}>({{ make }})"),
            insert_text,
            sort_text,
            replacement_range,
        ));
    }

    items
}

// Go: completions/context_self_in_classes.go:97 computeServiceTagKey
/// computeServiceTagKey computes the deterministic tag key for a service class.
/// Falls back to the class name if keybuilder returns empty.
// PORT: Go also takes the checker (`tp.checker`), which it passes to
// `getCompletionPackageJsonDirectory`, which does not read it. Go reads
// `program.Options().Effect` without the API process gate; the hook that
// calls this runs only when the gate is open.
pub fn compute_service_tag_key(
    program: &compiler::NewProgram,
    tp: &mut TypeParser<'_>,
    sf: Node,
    class_name: &str,
) -> String {
    let Some(pkg_json) = tp.package_json_for_source_file(sf) else {
        return class_name.to_string();
    };
    let (package_name, ok) = pkg_json.fields.name.get_value();
    if !ok || package_name.is_empty() {
        return class_name.to_string();
    }

    let package_directory = get_completion_package_json_directory(sf);
    if package_directory.is_empty() {
        return class_name.to_string();
    }

    let Some(effect_config) = program.options().effect.as_deref() else {
        return class_name.to_string();
    };
    let resolved_options = resolve_effect_plugin_options_for_source_file(
        effect_config,
        source_file_file_name(sf),
        &program.options().config_file_path,
        use_case_sensitive_file_names(),
    );
    let key_patterns = resolved_options.get_key_patterns();

    let key = keybuilder::create_string(
        source_file_file_name(sf),
        &package_name,
        &package_directory,
        class_name,
        "service",
        &key_patterns,
    );
    if key.is_empty() {
        return class_name.to_string();
    }
    key
}

// Go: completions/context_self_in_classes.go:132 getCompletionPackageJsonDirectory
/// getCompletionPackageJsonDirectory gets the package.json directory for a source file.
// PORT: Go asserts the program to a `GetSourceFileMetaData` provider and
// takes an unused checker. The port's program always has it, and
// `get_source_file_meta_data` reads the current program of the thread (the
// hook's checker lease enters the program), as
// `rules::deterministic_keys::get_package_json_directory` does.
fn get_completion_package_json_directory(sf: Node) -> String {
    let meta = get_source_file_meta_data(&source_file_info(sf).path);
    meta.package_json_directory
}
