//! Port of Go `internal/lsp/server_contentmapper_internal_test.go`
//! (tsgo#4712).
//!
//! PORT: Go tests package `lsp` from inside. The functions are `pub` in the
//! port. Go `&Server{stderr: &output}` is `lsp::new_server` with a stderr
//! that the test reads; the server never runs.

use std::io::Write;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use indexmap::IndexMap;
use ts_goport::frontend::bundled;
use ts_goport::frontend::json_ext::LspAny;
use ts_goport::gostd::{GoError, errors};
use ts_goport::lsp::{self, lsproto};

use crate::support::vfstest::{MapFile, MapFs};

/// Go `strings.Builder` as the server's stderr.
#[derive(Clone, Default)]
struct Output(Arc<Mutex<Vec<u8>>>);

impl Output {
    fn string(&self) -> String {
        String::from_utf8_lossy(&self.0.lock().unwrap_or_else(PoisonError::into_inner)).into_owned()
    }
}

impl Write for Output {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// A reader at end of input (the server never runs).
struct NoInput;

impl lsp::Reader for NoInput {
    fn read(&mut self) -> (Option<lsproto::Message>, Option<GoError>) {
        (None, Some(errors::EOF.clone()))
    }
}

/// A writer that drops every message (the server never runs).
struct NoOutput;

impl lsp::Writer for NoOutput {
    fn write(&mut self, _msg: &lsproto::Message) -> Result<(), GoError> {
        Ok(())
    }
}

/// Go `lsproto.ContentMapperManifest{Name: name, Exec: exec}` with the
/// other fields nil.
fn manifest(name: &str, exec: &[&str]) -> lsproto::ContentMapperManifest {
    lsproto::ContentMapperManifest {
        name: name.to_string(),
        version: None,
        exec: exec.iter().map(|arg| (*arg).to_string()).collect(),
        cwd: None,
        compiler_options: None,
        dynamic_config: None,
    }
}

child_test! {
    // Go: server_contentmapper_internal_test.go:11 TestContentMapperLoggerRequiresTrace
    fn content_mapper_logger_requires_trace() {
        let output = Output::default();
        let server = lsp::new_server(lsp::ServerOptions {
            in_: Box::new(NoInput),
            out: Box::new(NoOutput),
            err: Box::new(output.clone()),
            cwd: "/".to_string(),
            fs: bundled::wrap_fs(MapFs::from_map(Vec::<(String, MapFile)>::new(), false).fs()),
            default_library_path: bundled::lib_path(),
            typings_location: String::new(),
            parse_cache: None,
            npm_install: None,
            spawn: None,
            progress_delay: Duration::ZERO,
            set_parent_process_id: None,
        });
        let logger = server.content_mapper_logger();
        logger("hidden");
        assert!(output.string().is_empty());
        server.logger.set_verbosity(lsproto::LogVerbosity::TRACE);
        logger("visible");
        assert!(output.string().contains("visible"));
    }
}

child_test! {
    // Go: server_contentmapper_internal_test.go:24 TestParseContentMapperContributions
    fn parse_content_mapper_contributions() {
        let version = "2.3.4";
        let cwd = "/workspace/mapper";
        let mut options: IndexMap<String, LspAny> = IndexMap::new();
        options.insert("mode".to_string(), LspAny::String("embedded".to_string()));
        let contributions = lsp::parse_content_mapper_contributions(&[
            lsproto::ContentMapperContribution {
                contributor_id: "publisher.extension".to_string(),
                extensions: vec![".vue".to_string()],
                inferred_project_contribution: Some(lsproto::InferredProjectContentMapperContribution {
                    options: Some(options),
                    manifest: Some(lsproto::ContentMapperManifest {
                        name: "Vue mapper".to_string(),
                        version: Some(version.to_string()),
                        exec: vec!["node".to_string(), "mapper.js".to_string()],
                        cwd: Some(cwd.to_string()),
                        compiler_options: Some(vec!["strict".to_string()]),
                        dynamic_config: None,
                    }),
                }),
            },
            lsproto::ContentMapperContribution {
                contributor_id: "publisher.extension".to_string(),
                extensions: vec![".svelte".to_string()],
                inferred_project_contribution: None,
            },
        ])
        .unwrap_or_else(|err| panic!("parseContentMapperContributions: {}", err.error()));
        assert_eq!(contributions.mappers.len(), 1);
        assert_eq!(contributions.extensions, vec![".vue".to_string()]);
        let mapper = &contributions.mappers[0];
        assert_eq!(mapper.identity(), "publisher.extension[0] (Vue mapper@2.3.4)");
        assert_eq!(mapper.package_directory, cwd);
        assert_eq!(
            String::from_utf8_lossy(&mapper.definition.options.0),
            r#"{"mode":"embedded"}"#
        );
    }
}

child_test! {
    // Go: server_contentmapper_internal_test.go:62 TestParseContentMapperContributionsRejectsConflictingInlineMappers
    fn parse_content_mapper_contributions_rejects_conflicting_inline_mappers() {
        let inferred_project_contribution = |name: &str| lsproto::InferredProjectContentMapperContribution {
            options: None,
            manifest: Some(manifest(name, &[name])),
        };
        let result = lsp::parse_content_mapper_contributions(&[
            lsproto::ContentMapperContribution {
                contributor_id: "first".to_string(),
                extensions: vec![".vue".to_string()],
                inferred_project_contribution: Some(inferred_project_contribution("first")),
            },
            lsproto::ContentMapperContribution {
                contributor_id: "second".to_string(),
                extensions: vec![".vue".to_string()],
                inferred_project_contribution: Some(inferred_project_contribution("second")),
            },
        ]);
        match result {
            Ok(_) => panic!("expected an error"),
            Err(err) => assert!(
                err.error().contains(r#"both claim extension ".vue""#),
                "{}",
                err.error()
            ),
        }
    }
}

child_test! {
    // Go: server_contentmapper_internal_test.go:71 TestParseContentMapperContributionsUsesCaseInsensitiveExtensions (ts#63936)
    fn parse_content_mapper_contributions_uses_case_insensitive_extensions() {
        let inferred_project_contribution = |name: &str| lsproto::InferredProjectContentMapperContribution {
            options: None,
            manifest: Some(manifest(name, &[name])),
        };
        let result = lsp::parse_content_mapper_contributions(&[
            lsproto::ContentMapperContribution {
                contributor_id: "first".to_string(),
                extensions: vec![".vue".to_string()],
                inferred_project_contribution: Some(inferred_project_contribution("first")),
            },
            lsproto::ContentMapperContribution {
                contributor_id: "second".to_string(),
                extensions: vec![".VUE".to_string()],
                inferred_project_contribution: Some(inferred_project_contribution("second")),
            },
        ]);
        match result {
            Ok(_) => panic!("expected an error"),
            Err(err) => assert!(
                err.error().contains(r#"both claim extension ".VUE""#),
                "{}",
                err.error()
            ),
        }

        let result = lsp::parse_content_mapper_contributions(&[lsproto::ContentMapperContribution {
            contributor_id: "built-in".to_string(),
            extensions: vec![".TS".to_string()],
            inferred_project_contribution: None,
        }]);
        match result {
            Ok(_) => panic!("expected an error"),
            Err(err) => assert!(
                err.error().contains(r#"invalid extension ".TS""#),
                "{}",
                err.error()
            ),
        }
    }
}

child_test! {
    // Go: server_contentmapper_internal_test.go:89 TestParseContentMapperContributionsDefaultsOptionsToObject
    fn parse_content_mapper_contributions_defaults_options_to_object() {
        let contributions = lsp::parse_content_mapper_contributions(&[lsproto::ContentMapperContribution {
            contributor_id: "publisher.extension".to_string(),
            extensions: vec![".vue".to_string()],
            inferred_project_contribution: Some(lsproto::InferredProjectContentMapperContribution {
                options: None,
                manifest: Some(manifest("mapper", &["mapper"])),
            }),
        }])
        .unwrap_or_else(|err| panic!("parseContentMapperContributions: {}", err.error()));
        assert_eq!(
            String::from_utf8_lossy(&contributions.mappers[0].definition.options.0),
            "{}"
        );
    }
}
