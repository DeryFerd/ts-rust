//! Rust port of `internal/tsoptions/parsedcommandline_test.go`.
//!
//! PORT: Go runs the subtests in parallel (`t.Parallel`); here they run in
//! order. Nested Go subtest names are joined with `/`, as `go test` shows
//! them.

use std::collections::BTreeMap;

use ts_goport::frontend::prelude::*;

use super::tsoptionstest::{
    Subtests, file_map, get_parsed_command_line, new_vfs_parse_config_host, vfs_from_map,
};

// Go: parsedcommandline_test.go:13 TestParsedCommandLine
#[test]
fn parsed_command_line() {
    let mut t = Subtests::new("TestParsedCommandLine");

    // Go: t.Run("PossiblyMatchesFileName", ...)
    let no_files = file_map(&[]);
    let no_files_fs = vfs_from_map(&no_files, true);

    let files = file_map(&[
        ("/dev/a.ts", ""),
        ("/dev/a.d.ts", ""),
        ("/dev/a.js", ""),
        ("/dev/b.ts", ""),
        ("/dev/b.js", ""),
        ("/dev/c.d.ts", ""),
        ("/dev/z/a.ts", ""),
        ("/dev/z/abz.ts", ""),
        ("/dev/z/aba.ts", ""),
        ("/dev/z/b.ts", ""),
        ("/dev/z/bbz.ts", ""),
        ("/dev/z/bba.ts", ""),
        ("/dev/x/a.ts", ""),
        ("/dev/x/aa.ts", ""),
        ("/dev/x/b.ts", ""),
        ("/dev/x/y/a.ts", ""),
        ("/dev/x/y/b.ts", ""),
        ("/dev/js/a.js", ""),
        ("/dev/js/b.js", ""),
        ("/dev/js/d.min.js", ""),
        ("/dev/js/ab.min.js", ""),
        ("/ext/ext.ts", ""),
        ("/ext/b/a..b.ts", ""),
    ]);

    // Go: t.Run("with literal file list", ...)
    t.run(
        "PossiblyMatchesFileName/with literal file list/without exclude",
        || {
            let parsed_command_line = get_parsed_command_line(
                "{\n\t\t\t\t\t\t\"files\": [\n\t\t\t\t\t\t\t\"a.ts\",\n\t\t\t\t\t\t\t\"b.ts\"\n\t\t\t\t\t\t]\n\t\t\t\t\t}",
                &files,
                "/dev",
                /*useCaseSensitiveFileNames*/ true,
            );

            assert_matches(
                &parsed_command_line,
                &files,
                &["/dev/a.ts", "/dev/b.ts"],
            );
            Ok(())
        },
    );

    t.run(
        "PossiblyMatchesFileName/with literal file list/are not removed due to excludes",
        || {
            let parsed_command_line = get_parsed_command_line(
                "{\n\t\t\t\t\t\t\"files\": [\n\t\t\t\t\t\t\t\"a.ts\",\n\t\t\t\t\t\t\t\"b.ts\"\n\t\t\t\t\t\t],\n\t\t\t\t\t\t\"exclude\": [\n\t\t\t\t\t\t\t\"b.ts\"\n\t\t\t\t\t\t]\n\t\t\t\t\t}",
                &files,
                "/dev",
                /*useCaseSensitiveFileNames*/ true,
            );

            assert_matches(
                &parsed_command_line,
                &files,
                &["/dev/a.ts", "/dev/b.ts"],
            );

            let empty_parsed_command_line =
                parsed_command_line.reload_file_names_of_parsed_command_line(&*no_files_fs);
            assert_matches(
                &empty_parsed_command_line,
                &no_files,
                &["/dev/a.ts", "/dev/b.ts"],
            );
            Ok(())
        },
    );

    t.run(
        "PossiblyMatchesFileName/with literal file list/duplicates",
        || {
            let parsed_command_line = get_parsed_command_line(
                "{\n\t\t\t\t\t\t\"files\": [\n\t\t\t\t\t\t\t\"a.ts\",\n\t\t\t\t\t\t\t\"a.ts\",\n\t\t\t\t\t\t\t\"b.ts\",\n\t\t\t\t\t\t]\n\t\t\t\t\t}",
                &files,
                "/dev",
                /*useCaseSensitiveFileNames*/ true,
            );

            assert_eq!(
                parsed_command_line.literal_file_names().to_vec(),
                vec!["/dev/a.ts".to_string(), "/dev/b.ts".to_string()]
            );
            Ok(())
        },
    );

    // Go: t.Run("with literal include list", ...)
    t.run(
        "PossiblyMatchesFileName/with literal include list/without exclude",
        || {
            let parsed_command_line = get_parsed_command_line(
                "{\n\t\t\t\t\t\t\"include\": [\n\t\t\t\t\t\t\t\"a.ts\",\n\t\t\t\t\t\t\t\"b.ts\"\n\t\t\t\t\t\t]\n\t\t\t\t\t}",
                &files,
                "/dev",
                /*useCaseSensitiveFileNames*/ true,
            );

            assert_matches(
                &parsed_command_line,
                &files,
                &["/dev/a.ts", "/dev/b.ts"],
            );

            let empty_parsed_command_line =
                parsed_command_line.reload_file_names_of_parsed_command_line(&*no_files_fs);
            assert_matches(
                &empty_parsed_command_line,
                &no_files,
                &["/dev/a.ts", "/dev/b.ts"],
            );
            Ok(())
        },
    );

    // Go: t.Run("PossiblyMatchesFileName with content mapper extensions", ...) (tsgo#4712)
    // PORT: Go parses the same `*TsConfigSourceFile` twice. The Rust parse
    // takes the source file by value, so each parse gets a new one.
    t.run(
        "PossiblyMatchesFileName/PossiblyMatchesFileName with content mapper extensions",
        || {
            let package_json = file_map(&[(
                "/dev/node_modules/mapper/package.json",
                r#"{ "name": "mapper", "version": "1.0.0", "typescript": { "contentMapper": { "exec": ["mapper"] } } }"#,
            )]);
            let host = new_vfs_parse_config_host(&package_json, "/dev", true);
            let config_file_name = "/dev/tsconfig.json";
            let json_text = "{\n\t\t\t\"include\": [\"src\"],\n\t\t\t\"contentMappers\": [ { \"package\": \"mapper\", \"extensions\": [\".box\"] } ]\n\t\t}";
            let run_external_code = CompilerOptions {
                run_external_code: Tristate::True,
                ..Default::default()
            };
            let tsconfig_source_file = || {
                new_tsconfig_source_file_from_file_path(
                    config_file_name,
                    Path("/dev/tsconfig.json".to_string()),
                    json_text,
                )
            };
            let parsed_command_line = parse_json_source_file_config_file_content(
                tsconfig_source_file(),
                &host,
                "/dev",
                Some(&run_external_code),
                None,
                config_file_name,
                &[],
                None,
            );

            // A created content-mapped file under an included directory must be recognized as a
            // possible root file, or the config's root files are never reloaded for it.
            assert!(parsed_command_line.possibly_matches_file_name("/dev/src/new.box"));
            assert!(parsed_command_line.possibly_matches_file_name("/dev/src/new.ts"));
            assert!(!parsed_command_line.possibly_matches_file_name("/dev/src/new.vue"));
            assert!(!parsed_command_line.possibly_matches_file_name("/dev/other/new.box"));

            let insensitive_host = new_vfs_parse_config_host(&package_json, "/dev", false);
            let insensitive_command_line = parse_json_source_file_config_file_content(
                tsconfig_source_file(),
                &insensitive_host,
                "/dev",
                Some(&run_external_code),
                None,
                config_file_name,
                &[],
                None,
            );
            assert!(insensitive_command_line.possibly_matches_file_name("/dev/src/new.BOX"));
            Ok(())
        },
    );

    // Go: t.Run("WithFileNames preserves config identity", ...) (tsgo#4712)
    t.run(
        "PossiblyMatchesFileName/WithFileNames preserves config identity",
        || {
            let config_file_name = "/dev/tsconfig.json";
            let tsconfig_source_file = new_tsconfig_source_file_from_file_path(
                config_file_name,
                Path(config_file_name.to_string()),
                "{}",
            );
            let parsed_command_line = parse_json_source_file_config_file_content(
                tsconfig_source_file,
                &new_vfs_parse_config_host(&file_map(&[]), "/dev", true),
                "/dev",
                None,
                None,
                config_file_name,
                &[],
                None,
            );

            let with_typings = parsed_command_line.with_file_names(vec![
                "/dev/index.ts".to_string(),
                "/cache/@types/pkg/index.d.ts".to_string(),
            ]);
            assert_eq!(with_typings.config_name(), config_file_name);
            assert_eq!(
                with_typings.file_names().to_vec(),
                vec![
                    "/dev/index.ts".to_string(),
                    "/cache/@types/pkg/index.d.ts".to_string()
                ]
            );
            Ok(())
        },
    );

    t.finish();
}

// Go: parsedcommandline_test.go:47 assertMatches (closure in TestParsedCommandLine)
// PORT: Go `assert.Equal` is fatal, so the first mismatch panics.
fn assert_matches(
    parsed_command_line: &ParsedCommandLine,
    files: &BTreeMap<String, String>,
    matches: &[&str],
) {
    for file_name in files.keys() {
        let actual = parsed_command_line.possibly_matches_file_name(file_name);
        let expected = matches.contains(&file_name.as_str());
        assert_eq!(actual, expected, "fileName: {file_name}");
    }
    for file_name in matches {
        if !files.contains_key(*file_name) {
            let actual = parsed_command_line.possibly_matches_file_name(file_name);
            assert!(actual, "fileName: {file_name}");
        }
    }
}
