//! Go: internal/testutil/contentmappertest/editing.go (tsgo#4712).

use super::prelude::*;

// Go: editing.go:15 prefixedSupplementalHandler
pub(super) struct PrefixedSupplementalHandler;

/// A verbatim `spanmap.Segment` with these features, from the virtual range
/// `[virtual_start, virtual_end)` to the original range
/// `[original_start, original_end)`.
fn verbatim_segment(
    virtual_start: usize,
    virtual_end: usize,
    original_start: usize,
    original_end: usize,
    features: Feature,
) -> Segment {
    Segment {
        virtual_start: virtual_start as i32,
        virtual_end: virtual_end as i32,
        original_start: original_start as i32,
        original_end: original_end as i32,
        kind: Kind::VERBATIM,
        features,
    }
}

/// The `MappedOutput` of a `.ts` output with these mappings.
fn ts_output(text: String, mappings: Option<Vec<u8>>) -> MappedOutput {
    MappedOutput {
        text,
        extension: ".ts".to_string(),
        mappings: mappings.map(JsonValue).unwrap_or_default(),
        ..MappedOutput::default()
    }
}

impl MapperHandler for PrefixedSupplementalHandler {
    // Go: editing.go:17 prefixedSupplementalHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let p: TransformParams = unmarshal_params(&params)?;
                const PREFIX: &str = "/* generated */\n";
                let content = p.content.as_str();
                let mut features = Feature::ALL;
                if p.file_name.contains("folding-disabled")
                    || p.file_name.contains("codelens-disabled")
                    || p.file_name.contains("formatting-disabled")
                {
                    features = Feature::NONE;
                }
                let mut supplemental_text = format!("{PREFIX}{content}");
                let mut segments = vec![verbatim_segment(
                    PREFIX.len(),
                    PREFIX.len() + content.len(),
                    0,
                    content.len(),
                    features,
                )];
                if p.file_name.contains("formatting-split") {
                    let Some(second_start) = content.find("function second") else {
                        return Err(errors::new(
                            "contentmappertest: formatting-split input is missing function second",
                        ));
                    };
                    const GENERATED: &str = "const generated={x:1};\n";
                    supplemental_text = format!(
                        "{PREFIX}{}{GENERATED}{}",
                        &content[..second_start],
                        &content[second_start..]
                    );
                    segments = vec![
                        verbatim_segment(
                            PREFIX.len(),
                            PREFIX.len() + second_start,
                            0,
                            second_start,
                            Feature::ALL,
                        ),
                        verbatim_segment(
                            PREFIX.len() + second_start + GENERATED.len(),
                            supplemental_text.len(),
                            second_start,
                            content.len(),
                            Feature::ALL,
                        ),
                    ];
                }
                if p.file_name.contains("formatting-overlap") {
                    let (Some(second_start), Some(third_start)) = (
                        content.find("function second"),
                        content.find("function third"),
                    ) else {
                        return Err(errors::new(
                            "contentmappertest: formatting-overlap input is missing function second or third",
                        ));
                    };
                    const WRAPPER_START: &str = "if (true) {\n";
                    const WRAPPER_END: &str = "}\n";
                    supplemental_text =
                        format!("{WRAPPER_START}{}{WRAPPER_END}", &content[second_start..]);
                    segments = vec![verbatim_segment(
                        WRAPPER_START.len(),
                        WRAPPER_START.len() + content.len() - second_start,
                        second_start,
                        content.len(),
                        Feature::ALL,
                    )];
                    let canonical_mappings = spanmap::new(&[verbatim_segment(
                        0,
                        third_start,
                        0,
                        third_start,
                        Feature::ALL,
                    )])
                    .marshal()?;
                    let mappings = spanmap::new(&segments).marshal()?;
                    return reply(TransformResult {
                        mapped_output: ts_output(
                            content[..third_start].to_string(),
                            Some(canonical_mappings),
                        ),
                        supplemental: vec![SupplementalOutput {
                            mapped_output: ts_output(supplemental_text, Some(mappings)),
                        }],
                        ..TransformResult::default()
                    });
                }
                let mappings = spanmap::new(&segments).marshal()?;
                let mut canonical = ts_output("export {};".to_string(), None);
                if p.file_name.contains("folding-duplicate")
                    || p.file_name.contains("codelens-disabled")
                    || p.file_name.contains("codelens-duplicate")
                {
                    let canonical_mappings = spanmap::new(&[verbatim_segment(
                        0,
                        content.len(),
                        0,
                        content.len(),
                        Feature::ALL,
                    )])
                    .marshal()?;
                    canonical = ts_output(content.to_string(), Some(canonical_mappings));
                }
                reply(TransformResult {
                    mapped_output: canonical,
                    supplemental: vec![SupplementalOutput {
                        mapped_output: ts_output(supplemental_text, Some(mappings)),
                    }],
                    ..TransformResult::default()
                })
            }
            _ => Err(unexpected_method(method)),
        }
    }
}

// Go: editing.go:139 unmappedFoldingHandler
pub(super) struct UnmappedFoldingHandler;

impl MapperHandler for UnmappedFoldingHandler {
    // Go: editing.go:141 unmappedFoldingHandler.HandleRequest
    fn handle_request(&self, _ctx: &Context, method: &str, _params: JsonValue) -> HandlerResult {
        match method {
            contentmapper::METHOD_INITIALIZE => reply(initialize_result("mapper")),
            contentmapper::METHOD_TRANSFORM => {
                let mappings = spanmap::new(&[]).marshal()?;
                reply(TransformResult {
                    mapped_output: MappedOutput {
                        text: "import \"a\";\nimport \"b\";\n/*\n * generated\n */\nexport {};"
                            .to_string(),
                        extension: ".ts".to_string(),
                        mappings: JsonValue(mappings),
                        ..MappedOutput::default()
                    },
                    ..TransformResult::default()
                })
            }
            _ => Err(unexpected_method(method)),
        }
    }
}
