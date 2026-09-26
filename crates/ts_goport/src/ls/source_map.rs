//! Port of Go `ls/source_map.go`.

use crate::ls::prelude::*;

impl LanguageService {
    // Go: ls/source_map.go:12 getMappedLocation
    pub fn get_mapped_location(&self, file_name: &str, file_range: TextRange) -> lsproto::Location {
        let Some(start_pos) = self.try_get_source_position(file_name, file_range.pos()) else {
            let lsp_range =
                self.create_lsp_range_from_range(file_range, &self.get_script(file_name));
            return lsproto::Location {
                uri: lsconv::file_name_to_document_uri(file_name),
                range: lsp_range,
            };
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
        let lsp_range =
            self.create_lsp_range_from_range(new_range, &self.get_script(&start_pos.file_name));
        lsproto::Location {
            uri: lsconv::file_name_to_document_uri(&start_pos.file_name),
            range: lsp_range,
        }
    }
}

// Go: ls/source_map.go:39 script
#[derive(Clone, Debug, Default)]
pub struct Script {
    pub file_name: String,
    pub text: String,
}

impl lsconv::Script for Script {
    // Go: ls/source_map.go:44 FileName
    fn file_name(&self) -> &str {
        &self.file_name
    }

    // Go: ls/source_map.go:48 Text
    fn text(&self) -> &str {
        &self.text
    }
}

// PORT: Go passes a nil `*script` as an `lsconv.Script`; its methods then
// dereference nil and panic. `get_script` returns `Option<Script>`, and
// `&self.get_script(name)` is the Go interface value.
impl lsconv::Script for Option<Script> {
    fn file_name(&self) -> &str {
        &self
            .as_ref()
            .expect("invalid memory address or nil pointer dereference")
            .file_name
    }

    fn text(&self) -> &str {
        &self
            .as_ref()
            .expect("invalid memory address or nil pointer dereference")
            .text
    }
}

impl LanguageService {
    // Go: ls/source_map.go:52 getScript
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

    // Go: ls/source_map.go:60 tryGetSourcePosition
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

    // Go: ls/source_map.go:73 tryGetSourcePositionWorker
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

    // Go: ls/source_map.go:92 tryGetGeneratedPosition
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

    // Go: ls/source_map.go:105 tryGetGeneratedPositionWorker
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
