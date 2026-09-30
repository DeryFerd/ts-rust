//! Port of internal/sourcemap/generator_test.go.
//!
//! PORT: Go `gen` is `generator` (`gen` is a Rust keyword). Go
//! `assert.NilError(t, err)` is `.unwrap()`, and Go `assert.Error(t, err,
//! msg)` compares the `Err` text.

use ts_goport::frontend::tspath::ComparePathsOptions;
use ts_goport::sourcemap::generator::{RawSourceMap, new_generator};

/// Go `&RawSourceMap{Version: 3, File: file, SourceRoot: sourceRoot,
/// Sources: sources, Mappings: mappings, Names: names, SourcesContent:
/// sourcesContent}`.
fn raw(
    file: &str,
    source_root: &str,
    sources: &[&str],
    mappings: &str,
    names: &[&str],
    sources_content: Option<&[Option<&str>]>,
) -> RawSourceMap {
    RawSourceMap {
        version: 3,
        file: file.to_string(),
        source_root: source_root.to_string(),
        sources: sources.iter().map(|s| s.to_string()).collect(),
        names: names.iter().map(|s| s.to_string()).collect(),
        mappings: mappings.to_string(),
        sources_content: sources_content
            .map(|content| content.iter().map(|c| c.map(str::to_string)).collect()),
    }
}

// Go: sourcemap/generator_test.go:10 TestSourceMapGenerator_Empty
#[test]
fn source_map_generator_empty() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_map = generator.raw_source_map();
    assert_eq!(source_map, raw("main.js", "/", &[], "", &[], None));
}

// Go: sourcemap/generator_test.go:25 TestSourceMapGenerator_Empty_Serialized
#[test]
fn source_map_generator_empty_serialized() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let actual = generator.string();
    let expected =
        r#"{"version":3,"file":"main.js","sourceRoot":"/","sources":[],"names":[],"mappings":""}"#;
    assert_eq!(actual, expected);
}

// Go: sourcemap/generator_test.go:33 TestSourceMapGenerator_AddSource
#[test]
fn source_map_generator_add_source() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    let source_map = generator.raw_source_map();
    assert_eq!(source_index, 0);
    assert_eq!(source_map, raw("main.js", "/", &["main.ts"], "", &[], None));
}

// Go: sourcemap/generator_test.go:50 TestSourceMapGenerator_SetSourceContent
#[test]
fn source_map_generator_set_source_content() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    let source_content = "foo";
    generator
        .set_source_content(source_index, source_content)
        .unwrap();
    let source_map = generator.raw_source_map();
    assert_eq!(source_index, 0);
    assert_eq!(
        source_map,
        raw(
            "main.js",
            "/",
            &["main.ts"],
            "",
            &[],
            Some(&[Some(source_content)])
        )
    );
}

// Go: sourcemap/generator_test.go:69 TestSourceMapGenerator_SetSourceContent_ForSecondSourceOnly
#[test]
fn source_map_generator_set_source_content_for_second_source_only() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    generator.add_source("/skipped.ts");
    let source_index = generator.add_source("/main.ts");
    let source_content = "foo";
    generator
        .set_source_content(source_index, source_content)
        .unwrap();
    let source_map = generator.raw_source_map();
    assert_eq!(source_index, 1);
    assert_eq!(
        source_map,
        raw(
            "main.js",
            "/",
            &["skipped.ts", "main.ts"],
            "",
            &[],
            Some(&[None, Some(source_content)])
        )
    );
}

// Go: sourcemap/generator_test.go:89 TestSourceMapGenerator_SetSourceContent_SourceIndexOutOfRange
#[test]
fn source_map_generator_set_source_content_source_index_out_of_range() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    assert_eq!(
        generator.set_source_content(-1, ""),
        Err("sourceIndex is out of range".to_string())
    );
    assert_eq!(
        generator.set_source_content(0, ""),
        Err("sourceIndex is out of range".to_string())
    );
}

// Go: sourcemap/generator_test.go:96 TestSourceMapGenerator_SetSourceContent_ForSecondSourceOnly_Serialized
#[test]
fn source_map_generator_set_source_content_for_second_source_only_serialized() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    generator.add_source("/skipped.ts");
    let source_index = generator.add_source("/main.ts");
    let source_content = "foo";
    generator
        .set_source_content(source_index, source_content)
        .unwrap();
    let actual = generator.string();
    let expected = r#"{"version":3,"file":"main.js","sourceRoot":"/","sources":["skipped.ts","main.ts"],"names":[],"mappings":"","sourcesContent":[null,"foo"]}"#;
    assert_eq!(actual, expected);
}

// Go: sourcemap/generator_test.go:108 TestSourceMapGenerator_AddName
#[test]
fn source_map_generator_add_name() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let name_index = generator.add_name("foo");
    let source_map = generator.raw_source_map();
    assert_eq!(name_index, 0);
    assert_eq!(source_map, raw("main.js", "/", &[], "", &["foo"], None));
}

// Go: sourcemap/generator_test.go:125 TestSourceMapGenerator_AddGeneratedMapping
#[test]
fn source_map_generator_add_generated_mapping() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    generator.add_generated_mapping(0, 0).unwrap();
    let source_map = generator.raw_source_map();
    assert_eq!(source_map, raw("main.js", "/", &[], "A", &[], None));
}

// Go: sourcemap/generator_test.go:141 TestSourceMapGenerator_AddGeneratedMapping_ReplacesPendingSourceMapping
#[test]
fn source_map_generator_add_generated_mapping_replaces_pending_source_mapping() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    generator
        .add_source_mapping(0, 0, source_index, 0, 0)
        .unwrap();
    generator.add_generated_mapping(0, 0).unwrap();
    let source_map = generator.raw_source_map();
    assert_eq!(source_map.mappings, "A");
}

// Go: sourcemap/generator_test.go:151 TestSourceMapGenerator_AddGeneratedMapping_IsNotReplacedBySourceMapping
#[test]
fn source_map_generator_add_generated_mapping_is_not_replaced_by_source_mapping() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    generator.add_generated_mapping(0, 0).unwrap();
    generator
        .add_source_mapping(0, 0, source_index, 0, 0)
        .unwrap();
    let source_map = generator.raw_source_map();
    assert_eq!(source_map.mappings, "A");
}

// Go: sourcemap/generator_test.go:161 TestSourceMapGenerator_AddGeneratedMapping_OnSecondLineOnly
#[test]
fn source_map_generator_add_generated_mapping_on_second_line_only() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    generator.add_generated_mapping(1, 0).unwrap();
    let source_map = generator.raw_source_map();
    assert_eq!(source_map, raw("main.js", "/", &[], ";A", &[], None));
}

// Go: sourcemap/generator_test.go:157 TestSourceMapGenerator_AddSourceMapping
#[test]
fn source_map_generator_add_source_mapping() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    generator
        .add_source_mapping(0, 0, source_index, 0, 0)
        .unwrap();
    let source_map = generator.raw_source_map();
    assert_eq!(
        source_map,
        raw("main.js", "/", &["main.ts"], "AAAA", &[], None)
    );
}

// Go: sourcemap/generator_test.go:174 TestSourceMapGenerator_AddSourceMapping_NextGeneratedCharacter
#[test]
fn source_map_generator_add_source_mapping_next_generated_character() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    generator
        .add_source_mapping(0, 0, source_index, 0, 0)
        .unwrap();
    generator
        .add_source_mapping(0, 1, source_index, 0, 0)
        .unwrap();
    let source_map = generator.raw_source_map();
    assert_eq!(
        source_map,
        raw("main.js", "/", &["main.ts"], "AAAA,CAAA", &[], None)
    );
}

// Go: sourcemap/generator_test.go:192 TestSourceMapGenerator_AddSourceMapping_NextGeneratedAndSourceCharacter
#[test]
fn source_map_generator_add_source_mapping_next_generated_and_source_character() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    generator
        .add_source_mapping(0, 0, source_index, 0, 0)
        .unwrap();
    generator
        .add_source_mapping(0, 1, source_index, 0, 1)
        .unwrap();
    let source_map = generator.raw_source_map();
    assert_eq!(
        source_map,
        raw("main.js", "/", &["main.ts"], "AAAA,CAAC", &[], None)
    );
}

// Go: sourcemap/generator_test.go:210 TestSourceMapGenerator_AddSourceMapping_NextGeneratedLine
#[test]
fn source_map_generator_add_source_mapping_next_generated_line() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    generator
        .add_source_mapping(0, 0, source_index, 0, 0)
        .unwrap();
    generator
        .add_source_mapping(1, 0, source_index, 0, 0)
        .unwrap();
    let source_map = generator.raw_source_map();
    assert_eq!(
        source_map,
        raw("main.js", "/", &["main.ts"], "AAAA;AAAA", &[], None)
    );
}

// Go: sourcemap/generator_test.go:228 TestSourceMapGenerator_AddSourceMapping_PreviousSourceCharacter
#[test]
fn source_map_generator_add_source_mapping_previous_source_character() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    generator
        .add_source_mapping(0, 0, source_index, 0, 1)
        .unwrap();
    generator
        .add_source_mapping(0, 1, source_index, 0, 0)
        .unwrap();
    let source_map = generator.raw_source_map();
    assert_eq!(
        source_map,
        raw("main.js", "/", &["main.ts"], "AAAC,CAAD", &[], None)
    );
}

// Go: sourcemap/generator_test.go:246 TestSourceMapGenerator_AddNamedSourceMapping
#[test]
fn source_map_generator_add_named_source_mapping() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    let name_index = generator.add_name("foo");
    generator
        .add_named_source_mapping(0, 0, source_index, 0, 0, name_index)
        .unwrap();
    let source_map = generator.raw_source_map();
    assert_eq!(
        source_map,
        raw("main.js", "/", &["main.ts"], "AAAAA", &["foo"], None)
    );
}

// Go: sourcemap/generator_test.go:264 TestSourceMapGenerator_AddNamedSourceMapping_WithPreviousName
#[test]
fn source_map_generator_add_named_source_mapping_with_previous_name() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    let name_index1 = generator.add_name("foo");
    let name_index2 = generator.add_name("bar");
    generator
        .add_named_source_mapping(0, 0, source_index, 0, 0, name_index2)
        .unwrap();
    generator
        .add_named_source_mapping(0, 1, source_index, 0, 0, name_index1)
        .unwrap();
    let source_map = generator.raw_source_map();
    assert_eq!(
        source_map,
        raw(
            "main.js",
            "/",
            &["main.ts"],
            "AAAAC,CAAAD",
            &["foo", "bar"],
            None
        )
    );
}

// Go: sourcemap/generator_test.go:284 TestSourceMapGenerator_AddGeneratedMapping_GeneratedLineCannotBacktrack
#[test]
fn source_map_generator_add_generated_mapping_generated_line_cannot_backtrack() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    generator.add_generated_mapping(1, 0).unwrap();
    assert_eq!(
        generator.add_generated_mapping(0, 0),
        Err("generatedLine cannot backtrack".to_string())
    );
}

// Go: sourcemap/generator_test.go:291 TestSourceMapGenerator_AddGeneratedMapping_GeneratedCharacterCannotBeNegative
#[test]
fn source_map_generator_add_generated_mapping_generated_character_cannot_be_negative() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    generator.add_generated_mapping(0, 0).unwrap();
    assert_eq!(
        generator.add_generated_mapping(0, -1),
        Err("generatedCharacter cannot be negative".to_string())
    );
}

// Go: sourcemap/generator_test.go:298 TestSourceMapGenerator_AddSourceMapping_GeneratedLineCannotBacktrack
#[test]
fn source_map_generator_add_source_mapping_generated_line_cannot_backtrack() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    generator
        .add_source_mapping(1, 0, source_index, 0, 0)
        .unwrap();
    assert_eq!(
        generator.add_source_mapping(0, 0, source_index, 0, 0),
        Err("generatedLine cannot backtrack".to_string())
    );
}

// Go: sourcemap/generator_test.go:306 TestSourceMapGenerator_AddSourceMapping_GeneratedCharacterCannotBeNegative
#[test]
fn source_map_generator_add_source_mapping_generated_character_cannot_be_negative() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    generator
        .add_source_mapping(0, 0, source_index, 0, 0)
        .unwrap();
    assert_eq!(
        generator.add_source_mapping(0, -1, source_index, 0, 0),
        Err("generatedCharacter cannot be negative".to_string())
    );
}

// Go: sourcemap/generator_test.go:314 TestSourceMapGenerator_AddSourceMapping_SourceIndexIsOutOfRange
#[test]
fn source_map_generator_add_source_mapping_source_index_is_out_of_range() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    assert_eq!(
        generator.add_source_mapping(0, 0, -1, 0, 0),
        Err("sourceIndex is out of range".to_string())
    );
    assert_eq!(
        generator.add_source_mapping(0, 0, 0, 0, 0),
        Err("sourceIndex is out of range".to_string())
    );
}

// Go: sourcemap/generator_test.go:321 TestSourceMapGenerator_AddSourceMapping_SourceLineCannotBeNegative
#[test]
fn source_map_generator_add_source_mapping_source_line_cannot_be_negative() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    assert_eq!(
        generator.add_source_mapping(0, 0, source_index, -1, 0),
        Err("sourceLine cannot be negative".to_string())
    );
}

// Go: sourcemap/generator_test.go:328 TestSourceMapGenerator_AddSourceMapping_SourceCharacterCannotBeNegative
#[test]
fn source_map_generator_add_source_mapping_source_character_cannot_be_negative() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    assert_eq!(
        generator.add_source_mapping(0, 0, source_index, 0, -1),
        Err("sourceCharacter cannot be negative".to_string())
    );
}

// Go: sourcemap/generator_test.go:335 TestSourceMapGenerator_AddNamedSourceMapping_GeneratedLineCannotBacktrack
#[test]
fn source_map_generator_add_named_source_mapping_generated_line_cannot_backtrack() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    let name_index = generator.add_name("foo");
    generator
        .add_named_source_mapping(1, 0, source_index, 0, 0, name_index)
        .unwrap();
    assert_eq!(
        generator.add_named_source_mapping(0, 0, source_index, 0, 0, name_index),
        Err("generatedLine cannot backtrack".to_string())
    );
}

// Go: sourcemap/generator_test.go:344 TestSourceMapGenerator_AddNamedSourceMapping_GeneratedCharacterCannotBeNegative
#[test]
fn source_map_generator_add_named_source_mapping_generated_character_cannot_be_negative() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    let name_index = generator.add_name("foo");
    generator
        .add_named_source_mapping(0, 0, source_index, 0, 0, name_index)
        .unwrap();
    assert_eq!(
        generator.add_named_source_mapping(0, -1, source_index, 0, 0, name_index),
        Err("generatedCharacter cannot be negative".to_string())
    );
}

// Go: sourcemap/generator_test.go:353 TestSourceMapGenerator_AddNamedSourceMapping_SourceIndexIsOutOfRange
#[test]
fn source_map_generator_add_named_source_mapping_source_index_is_out_of_range() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let name_index = generator.add_name("foo");
    assert_eq!(
        generator.add_named_source_mapping(0, 0, -1, 0, 0, name_index),
        Err("sourceIndex is out of range".to_string())
    );
    assert_eq!(
        generator.add_named_source_mapping(0, 0, 0, 0, 0, name_index),
        Err("sourceIndex is out of range".to_string())
    );
}

// Go: sourcemap/generator_test.go:361 TestSourceMapGenerator_AddNamedSourceMapping_SourceLineCannotBeNegative
#[test]
fn source_map_generator_add_named_source_mapping_source_line_cannot_be_negative() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let name_index = generator.add_name("foo");
    let source_index = generator.add_source("/main.ts");
    assert_eq!(
        generator.add_named_source_mapping(0, 0, source_index, -1, 0, name_index),
        Err("sourceLine cannot be negative".to_string())
    );
}

// Go: sourcemap/generator_test.go:369 TestSourceMapGenerator_AddNamedSourceMapping_SourceCharacterCannotBeNegative
#[test]
fn source_map_generator_add_named_source_mapping_source_character_cannot_be_negative() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let name_index = generator.add_name("foo");
    let source_index = generator.add_source("/main.ts");
    assert_eq!(
        generator.add_named_source_mapping(0, 0, source_index, 0, -1, name_index),
        Err("sourceCharacter cannot be negative".to_string())
    );
}

// Go: sourcemap/generator_test.go:377 TestSourceMapGenerator_AddNamedSourceMapping_NameIndexIsOutOfRange
#[test]
fn source_map_generator_add_named_source_mapping_name_index_is_out_of_range() {
    let mut generator = new_generator("main.js", "/", "/", ComparePathsOptions::default());
    let source_index = generator.add_source("/main.ts");
    assert_eq!(
        generator.add_named_source_mapping(0, 0, source_index, 0, 0, -1),
        Err("nameIndex is out of range".to_string())
    );
    assert_eq!(
        generator.add_named_source_mapping(0, 0, source_index, 0, 0, 0),
        Err("nameIndex is out of range".to_string())
    );
}
