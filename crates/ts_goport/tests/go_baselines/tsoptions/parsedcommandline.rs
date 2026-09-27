//! Rust port of `internal/tsoptions/parsedcommandline_test.go`.
//!
//! PORT: Go runs the subtests in parallel (`t.Parallel`); here they run in
//! order. Nested Go subtest names are joined with `/`, as `go test` shows
//! them.

use std::collections::BTreeMap;

use ts_goport::frontend::prelude::*;

use super::tsoptionstest::{Subtests, file_map, get_parsed_command_line, vfs_from_map};

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
