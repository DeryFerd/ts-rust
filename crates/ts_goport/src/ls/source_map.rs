//! Port of Go `ls/source_map.go`.

use crate::ls::prelude::*;

use crate::spanmap::{Feature, Fidelity};

impl<P: ProgramView> LanguageService<P> {
    // Go: ls/source_map.go:18 sourceFileRangeToLSPLocation
    // sourceFileRangeToLSPLocation maps a range from an arbitrary program SourceFile to an LSP location,
    // composing content-mapper span maps and declaration source maps as needed. LS features should use this
    // for cross-file results instead of calling getMappedLocation or lsconv.ToLSPLocation directly.
    // This unfiltered form is appropriate for diagnostics and text edits.
    pub fn source_file_range_to_lsp_location(
        &self,
        file: Node,
        file_range: TextRange,
    ) -> (lsproto::Location, Fidelity) {
        if !source_file_content_mapper(file).is_empty() {
            return self.converters.to_lsp_location(&file, file_range);
        }
        self.get_mapped_location(source_file_file_name(file), file_range)
    }

    // Go: ls/source_map.go:28 sourceFileRangeToLSPLocationForFeature
    // sourceFileRangeToLSPLocationForFeature is the preferred conversion for visible LS results that may
    // come from another file. It applies content-mapper feature filtering and follows declaration source maps.
    // Do not use it for diagnostics or text edits.
    pub fn source_file_range_to_lsp_location_for_feature(
        &self,
        file: Node,
        file_range: TextRange,
        feature: Feature,
    ) -> (lsproto::Location, Fidelity) {
        if !source_file_content_mapper(file).is_empty() {
            return self
                .converters
                .to_lsp_location_for_feature(&file, file_range, feature);
        }
        self.get_mapped_location(source_file_file_name(file), file_range)
    }

    // Go: ls/source_map.go:38 getMappedLocation
    // getMappedLocation follows declaration source maps from a .d.ts range to its source location.
    // It is an implementation detail of sourceFileRangeToLSPLocation; LS features should not call it directly,
    // because it does not preserve a content-mapper projection or apply span-map feature filtering.
    pub fn get_mapped_location(
        &self,
        file_name: &str,
        file_range: TextRange,
    ) -> (lsproto::Location, Fidelity) {
        let Some(start_pos) = self.try_get_source_position(file_name, file_range.pos()) else {
            let (lsp_range, fidelity) =
                self.create_lsp_range_from_range(file_range, &self.get_script(file_name));
            return (
                lsproto::Location {
                    uri: lsconv::file_name_to_document_uri(file_name),
                    range: lsp_range,
                },
                fidelity,
            );
        };
        let mut end_pos = self.try_get_source_position(file_name, file_range.end());
        if end_pos.as_ref().is_none_or(|end_pos| {
            end_pos.file_name != start_pos.file_name || end_pos.pos < start_pos.pos
        }) {
            // When end doesn't map, maps to a different source file (e.g. in a .d.ts with a
            // multi-source source map from --outFile compilation), or maps to a position before
            // start (non-monotonic source map mappings), approximate the end position.
            end_pos = Some(sourcemap::DocumentPosition {
                file_name: start_pos.file_name.clone(),
                pos: start_pos.pos + file_range.len(),
            });
        }
        let end_pos = end_pos.expect("set above");
        let new_range = TextRange::new(start_pos.pos, end_pos.pos);
        let (lsp_range, fidelity) =
            self.create_lsp_range_from_range(new_range, &self.get_script(&start_pos.file_name));
        (
            lsproto::Location {
                uri: lsconv::file_name_to_document_uri(&start_pos.file_name),
                range: lsp_range,
            },
            fidelity,
        )
    }
}

// Go: ls/source_map.go:65 script
// PORT: `text` is shared with the host's file (`Host::read_file`), as the Go
// string is.
#[derive(Clone, Debug, Default)]
pub struct Script {
    pub file_name: String,
    pub text: FileText,
}

impl lsconv::Script for Script {
    // Go: ls/source_map.go:70 FileName
    fn file_name(&self) -> &str {
        &self.file_name
    }

    // Go: ls/source_map.go:74 OriginalFileName
    fn original_file_name(&self) -> &str {
        &self.file_name
    }

    // Go: ls/source_map.go:76 Text
    fn text(&self) -> lsconv::ScriptText<'_> {
        lsconv::ScriptText::Borrowed(&self.text)
    }

    // Go: ls/source_map.go:80 OriginalText
    fn original_text(&self) -> lsconv::ScriptText<'_> {
        lsconv::ScriptText::Borrowed(&self.text)
    }

    // Go: ls/source_map.go:81 SpanMap
    fn span_map(&self) -> Option<&crate::spanmap::SpanMap> {
        None
    }
}

// PORT: Go passes a nil `*script` as an `lsconv.Script`; its methods then
// dereference nil and panic. `get_script` returns `Option<Script>`, and
// `&self.get_script(name)` is the Go interface value.
impl lsconv::Script for Option<Script> {
    fn file_name(&self) -> &str {
        &self
            .as_ref()
            .unwrap_or_else(|| crate::core::go_nil_dereference())
            .file_name
    }

    fn text(&self) -> lsconv::ScriptText<'_> {
        lsconv::ScriptText::Borrowed(
            &self
                .as_ref()
                .unwrap_or_else(|| crate::core::go_nil_dereference())
                .text,
        )
    }
}

impl<P: ProgramView> LanguageService<P> {
    // Go: ls/source_map.go:85 getScript
    // PORT: Go returns `*script`; nil is `None`. Go passes the result as an
    // `lsconv.Script` even when it is nil, so `Option<Script>` implements
    // `lsconv::Script` too (above); pass `&self.get_script(name)`.
    pub fn get_script(&self, file_name: &str) -> Option<Script> {
        let (text, ok) = self.host.read_file(file_name);
        if !ok {
            return None;
        }
        Some(Script {
            file_name: file_name.to_string(),
            text,
        })
    }

    // Go: ls/source_map.go:93 tryGetSourcePosition
    // PORT: Go `core.TextPos` is `i32`; the `*sourcemap.DocumentPosition`
    // result is `Option`.
    pub fn try_get_source_position(
        &self,
        file_name: &str,
        position: i32,
    ) -> Option<sourcemap::DocumentPosition> {
        let new_pos = self.try_get_source_position_worker(file_name, position);
        if let Some(new_pos) = &new_pos {
            let (_, ok) = self.read_file(&new_pos.file_name);
            if !ok {
                // File doesn't exist
                return None;
            }
        }
        new_pos
    }

    // Go: ls/source_map.go:106 tryGetSourcePositionWorker
    pub fn try_get_source_position_worker(
        &self,
        file_name: &str,
        position: i32,
    ) -> Option<sourcemap::DocumentPosition> {
        if !tspath::is_declaration_file_name(file_name) {
            return None;
        }

        let position_mapper = self.get_document_position_mapper(file_name);
        let document_pos = sourcemap::DocumentPositionMapper::get_source_position(
            position_mapper.as_deref(),
            &sourcemap::DocumentPosition {
                file_name: file_name.to_string(),
                pos: position,
            },
        )?;
        if let Some(new_pos) =
            self.try_get_source_position_worker(&document_pos.file_name, document_pos.pos)
        {
            return Some(new_pos);
        }
        Some(document_pos)
    }
}

// PORT: the generated position is read only by `getNonLocalDefinition`,
// which runs on the dispatch thread, so these two stay on `NewProgram`.
impl LanguageService {
    // Go: ls/source_map.go:125 tryGetGeneratedPosition
    pub fn try_get_generated_position(
        &self,
        file_name: &str,
        position: i32,
    ) -> Option<sourcemap::DocumentPosition> {
        let new_pos = self.try_get_generated_position_worker(file_name, position);
        if let Some(new_pos) = &new_pos {
            let (_, ok) = self.read_file(&new_pos.file_name);
            if !ok {
                // File doesn't exist
                return None;
            }
        }
        new_pos
    }

    // Go: ls/source_map.go:138 tryGetGeneratedPositionWorker
    pub fn try_get_generated_position_worker(
        &self,
        file_name: &str,
        position: i32,
    ) -> Option<sourcemap::DocumentPosition> {
        if tspath::is_declaration_file_name(file_name) {
            return None;
        }

        // PORT: Go also returns nil for a nil program; the Rust program
        // reference is never nil.
        let program = self.get_program();
        if program.get_source_file(file_name).is_none() {
            return None;
        }

        let path = self.to_path(file_name);
        // If this is source file of project reference source (instead of redirect) there is no generated position
        if program.is_source_from_project_reference(&path) {
            return None;
        }

        let declaration_file_name =
            crate::frontend::outputpaths::get_output_declaration_file_name_worker(
                file_name,
                program.options(),
                program,
            );
        let position_mapper = self.get_document_position_mapper(&declaration_file_name);
        let document_pos = sourcemap::DocumentPositionMapper::get_generated_position(
            position_mapper.as_deref(),
            &sourcemap::DocumentPosition {
                file_name: file_name.to_string(),
                pos: position,
            },
        )?;
        if let Some(new_pos) =
            self.try_get_generated_position_worker(&document_pos.file_name, document_pos.pos)
        {
            return Some(new_pos);
        }
        Some(document_pos)
    }
}
