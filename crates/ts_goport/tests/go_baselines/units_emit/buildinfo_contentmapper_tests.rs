//! Port of internal/execute/incremental/buildinfo_contentmapper_test.go
//! (tsgo#4712, package `incremental_test`).

use crate::support::vfstest::{self, MapFile};
use std::rc::Rc;
use ts_goport::contentmapper::{self, Definition, Manifest, Mapper};
use ts_goport::core::version;
use ts_goport::execute::incremental::BuildInfo;
use ts_goport::execute::incremental::build_info::content_mapper_identities;
use ts_goport::execute::incremental::incremental::BuildInfoReader;
use ts_goport::execute::incremental::program::read_build_info_program;
use ts_goport::frontend::compiler::{CompilerHost, new_compiler_host};
use ts_goport::frontend::json_ext::JsonValue;
use ts_goport::frontend::tsoptions::{ParsedCommandLine, ParsedOptions};
use ts_goport::gostd::{GoError, errors};
use ts_goport::prelude::*;

// Go: incremental/buildinfo_contentmapper_test.go:16 configWithMappers
fn config_with_mappers(mappers: Vec<Rc<Mapper>>) -> ParsedCommandLine {
    ParsedCommandLine {
        parsed_config: ParsedOptions {
            compiler_options: Rc::new(CompilerOptions::default()),
            content_mappers: mappers,
            ..Default::default()
        },
        ..Default::default()
    }
}

/// Go `&contentmapper.Mapper{Manifest: contentmapper.Manifest{Name: name, Version: version}}`.
fn manifest_mapper(name: &str, version: &str) -> Mapper {
    Mapper {
        manifest: Manifest {
            name: name.to_string(),
            version: version.to_string(),
            ..Default::default()
        },
        ..Default::default()
    }
}

// Go: incremental/buildinfo_contentmapper_test.go:25 TestStaticContentMapperTransformIdentity
#[test]
fn test_static_content_mapper_transform_identity() {
    assert_eq!(manifest_mapper("vue", "2.0.0").identity(), "vue@2.0.0");
    assert_eq!(
        Mapper {
            definition: Definition {
                package: "anon".to_string(),
                ..Default::default()
            },
            ..Default::default()
        }
        .identity(),
        ""
    );

    let jsx_mapper = Mapper {
        definition: Definition {
            package: "jsx".to_string(),
            ..Default::default()
        },
        manifest: Manifest {
            name: "jsx".to_string(),
            version: "1.0.0".to_string(),
            compiler_options: vec!["jsx".to_string()],
            ..Default::default()
        },
        ..Default::default()
    };
    let jsx_preserve_identity = jsx_mapper.transform_identity(Some(&CompilerOptions {
        jsx: JsxEmit::PRESERVE,
        ..Default::default()
    }));
    let jsx_react_identity = jsx_mapper.transform_identity(Some(&CompilerOptions {
        jsx: JsxEmit::REACT,
        ..Default::default()
    }));
    assert_ne!(jsx_preserve_identity, jsx_react_identity);

    let options_mapper = |options: &str| Mapper {
        definition: Definition {
            package: "vue".to_string(),
            options: JsonValue(options.as_bytes().to_vec()),
            ..Default::default()
        },
        manifest: Manifest {
            name: "vue".to_string(),
            version: "1.0.0".to_string(),
            ..Default::default()
        },
        ..Default::default()
    };
    let options_a = options_mapper(r#"{"mode":"a"}"#);
    let options_b = options_mapper(r#"{"mode":"b"}"#);
    assert_ne!(
        options_a.transform_identity(Some(&CompilerOptions::default())),
        options_b.transform_identity(Some(&CompilerOptions::default()))
    );
}

// Go: incremental/buildinfo_contentmapper_test.go:52 fakeBuildInfoReader
struct FakeBuildInfoReader {
    build_info: Option<BuildInfo>,
}

impl BuildInfoReader for FakeBuildInfoReader {
    fn read_build_info(&self, _config: &ParsedCommandLine) -> Option<BuildInfo> {
        self.build_info.clone()
    }
}

// Go: incremental/buildinfo_contentmapper_test.go:60 fakeContentMapperProject
// PORT: Go returns `p.identities, p.err`; with an error, the port returns
// only the error.
#[derive(Clone, Default)]
struct FakeContentMapperProject {
    identities: Vec<String>,
    err: Option<GoError>,
}

impl contentmapper::Project for FakeContentMapperProject {
    fn refresh(&self) -> std::result::Result<(), GoError> {
        Ok(())
    }
    fn identities(&self) -> std::result::Result<Vec<String>, GoError> {
        match &self.err {
            Some(err) => Err(err.clone()),
            None => Ok(self.identities.clone()),
        }
    }
    fn identity(&self, _mapper: &Rc<Mapper>) -> std::result::Result<String, GoError> {
        Ok(String::new())
    }
    fn watched_files(&self) -> std::result::Result<Vec<String>, GoError> {
        Ok(Vec::new())
    }
    fn diagnostics(&self) -> Vec<contentmapper::OptionDiagnostic> {
        Vec::new()
    }
    fn transform(
        &self,
        _mapper: &Rc<Mapper>,
        _request: contentmapper::Request,
    ) -> std::result::Result<contentmapper::Result, GoError> {
        Ok(contentmapper::Result::default())
    }
    fn close(&self) -> std::result::Result<(), GoError> {
        Ok(())
    }
}

/// Go `compiler.NewCompilerHost("/", vfstest.FromMap[any](nil, true), "", nil, nil, project)`.
fn host_with_project(project: &FakeContentMapperProject) -> Rc<dyn CompilerHost> {
    new_compiler_host(
        "/",
        vfstest::from_map(Vec::<(String, MapFile)>::new(), true),
        "",
        None,
        None,
        Some(Rc::new(project.clone()) as Rc<dyn contentmapper::Project>),
    )
}

// Go: incremental/buildinfo_contentmapper_test.go:77 TestDynamicContentMapperIdentities
#[test]
fn test_dynamic_content_mapper_identities() {
    let config = config_with_mappers(vec![Rc::new(Mapper {
        definition: Definition {
            package: "dynamic".to_string(),
            ..Default::default()
        },
        manifest: Manifest {
            name: "dynamic".to_string(),
            version: "1.0.0".to_string(),
            dynamic_config: true,
            ..Default::default()
        },
        ..Default::default()
    })]);
    let project = FakeContentMapperProject {
        identities: vec!["dynamic@1.0.0:opaque".to_string()],
        err: None,
    };
    let identities = content_mapper_identities(Some(&project)).expect("ContentMapperIdentities");
    assert_eq!(identities, Some(project.identities.clone()));

    let build_info = BuildInfo {
        version: version().to_string(),
        file_names: Some(vec!["/src/a.ts".to_string()]),
        content_mapper_identities: Some(vec!["dynamic@1.0.0:old".to_string()]),
        ..BuildInfo::default()
    };
    let host = host_with_project(&project);
    let program = read_build_info_program(
        &config,
        &FakeBuildInfoReader {
            build_info: Some(build_info),
        },
        &*host,
    );
    assert!(
        program.is_none(),
        "expected opaque mapper identity changes to discard the old program"
    );
}

// Go: incremental/buildinfo_contentmapper_test.go:98 TestContentMapperIdentityError
#[test]
fn test_content_mapper_identity_error() {
    let want = errors::new("identity failed");
    match content_mapper_identities(Some(&FakeContentMapperProject {
        identities: Vec::new(),
        err: Some(want.clone()),
    })) {
        Ok(identities) => panic!("expected the identity error, got identities {identities:?}"),
        Err(err) => assert!(errors::is(&err, &want), "got error {:?}", err.error()),
    }
}

// Go: incremental/buildinfo_contentmapper_test.go:106 TestReadBuildInfoProgramContentMapperIdentityMismatch
#[test]
fn test_read_build_info_program_content_mapper_identity_mismatch() {
    // An otherwise-valid, incremental build info whose recorded mapper identity differs from the current
    // project cannot be reused: the old program is discarded (nil) so the project is rebuilt.
    let build_info = BuildInfo {
        version: version().to_string(),
        file_names: Some(vec!["/src/a.ts".to_string()]),
        content_mapper_identities: Some(vec!["vue@1.0.0".to_string()]),
        ..BuildInfo::default()
    };
    let config = config_with_mappers(vec![Rc::new(Mapper {
        definition: Definition {
            package: "vue".to_string(),
            extensions: vec![".vue".to_string()],
            ..Default::default()
        },
        manifest: Manifest {
            name: "vue".to_string(),
            version: "2.0.0".to_string(),
            ..Default::default()
        },
        ..Default::default()
    })]);
    let project = FakeContentMapperProject {
        identities: vec!["vue@2.0.0:current".to_string()],
        err: None,
    };
    let host = host_with_project(&project);

    let program = read_build_info_program(
        &config,
        &FakeBuildInfoReader {
            build_info: Some(build_info),
        },
        &*host,
    );
    assert!(
        program.is_none(),
        "expected the old program to be discarded when the mapper identity changed"
    );
}
