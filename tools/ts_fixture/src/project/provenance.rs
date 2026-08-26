use std::{
    collections::BTreeMap,
    fs::{self, File},
    io::{self, Read},
    path::Path,
    process::Command,
    time::{Duration, SystemTime, UNIX_EPOCH},
};

use serde::Serialize;
use xxhash_rust::xxh3::Xxh3;

use super::ProjectStage;
use crate::{
    SCORECARD_DIGEST_ALGORITHM, ScorecardRepositoryRevision, git_output, repository_revision,
    stable_digest,
};

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectFileDigest {
    pub path: String,
    pub byte_count: u64,
    pub digest: String,
    pub digest_algorithm: &'static str,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProjectRunProvenance {
    pub runner_version: &'static str,
    pub process_id: u32,
    pub started_unix_ms: Option<u128>,
    pub wall_time_ms: u128,
    pub arguments: Vec<String>,
    pub working_directory: Option<String>,
    pub environment_overrides: BTreeMap<String, String>,
    pub operating_system: &'static str,
    pub architecture: &'static str,
    pub logical_processors: Option<usize>,
    pub peak_rss_kib: Option<u64>,
    pub process_limits: Option<String>,
    pub machine_memory: Option<String>,
    pub rustc_at_run_time: Option<String>,
    /// Runtime checkout state does not prove which revision built the executable.
    pub rust_source_at_run_time: ScorecardRepositoryRevision,
    pub rust_source_directory: String,
    pub project_source_at_run_time: ScorecardRepositoryRevision,
    pub project_source_directory: String,
    pub executable: ProjectStage<ProjectFileDigest>,
    pub compiled_helper_digests: BTreeMap<String, String>,
    pub project_metadata: Vec<ProjectStage<ProjectFileDigest>>,
    /// An optional external build record. The runner does not authenticate it.
    pub supplied_build_record: Option<serde_json::Value>,
    pub limitations: Vec<String>,
}

impl ProjectRunProvenance {
    pub(super) fn start(config_path: &Path) -> Self {
        let rust_directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let rust_directory = fs::canonicalize(&rust_directory).unwrap_or(rust_directory);
        let config_directory = config_path.parent().unwrap_or(config_path);
        let project_directory = git_output(config_directory, &["rev-parse", "--show-toplevel"])
            .map_or_else(|| config_directory.to_owned(), Into::into);
        let environment_overrides = [
            "TS_CARGO_MEMORY_LIMIT_KIB",
            "RUST_MIN_STACK",
            "RUSTFLAGS",
            "CARGO_ENCODED_RUSTFLAGS",
            "RUSTUP_TOOLCHAIN",
            "CARGO_TARGET_DIR",
            "CARGO_BUILD_JOBS",
        ]
        .into_iter()
        .filter_map(|key| std::env::var(key).ok().map(|value| (key.to_owned(), value)))
        .collect();
        let compiled_helper_digests = compiled_helper_digests();
        let executable = std::env::current_exe()
            .and_then(|path| digest_file(&path))
            .map_or_else(
                |error| {
                    ProjectStage::unavailable(format!("Executable digest is unavailable: {error}"))
                },
                |value| ProjectStage::Complete { value },
            );
        let project_metadata = [
            "package.json",
            "pnpm-lock.yaml",
            "package-lock.json",
            "npm-shrinkwrap.json",
            "yarn.lock",
            "bun.lock",
            "bun.lockb",
            "LICENSE",
            "LICENSE.md",
            "LICENSE.txt",
            "COPYING",
        ]
        .into_iter()
        .map(|name| project_directory.join(name))
        .filter(|path| path.is_file())
        .map(|path| {
            digest_file(&path).map_or_else(
                |error| {
                    ProjectStage::unavailable(format!("Cannot hash {}: {error}", path.display()))
                },
                |value| ProjectStage::Complete { value },
            )
        })
        .collect();
        Self {
            runner_version: env!("CARGO_PKG_VERSION"),
            process_id: std::process::id(),
            started_unix_ms: SystemTime::now().duration_since(UNIX_EPOCH).ok().map(|time| time.as_millis()),
            wall_time_ms: 0,
            arguments: std::env::args_os().map(|value| value.to_string_lossy().into_owned()).collect(),
            working_directory: std::env::current_dir().ok().map(|path| path.to_string_lossy().into_owned()),
            environment_overrides,
            operating_system: std::env::consts::OS,
            architecture: std::env::consts::ARCH,
            logical_processors: std::thread::available_parallelism().ok().map(std::num::NonZeroUsize::get),
            peak_rss_kib: None,
            process_limits: fs::read_to_string("/proc/self/limits").ok(),
            machine_memory: fs::read_to_string("/proc/meminfo").ok(),
            rustc_at_run_time: Command::new("rustc").arg("--version").output().ok()
                .filter(|output| output.status.success())
                .and_then(|output| String::from_utf8(output.stdout).ok())
                .map(|output| output.trim().to_owned()),
            rust_source_at_run_time: repository_revision(&rust_directory),
            rust_source_directory: rust_directory.to_string_lossy().into_owned(),
            project_source_at_run_time: repository_revision(&project_directory),
            project_source_directory: project_directory.to_string_lossy().into_owned(),
            executable,
            compiled_helper_digests,
            project_metadata,
            supplied_build_record: None,
            limitations: vec![
                "Runtime Git state and rustc version are observations, not authenticated executable build provenance.".to_owned(),
                "This runner does not record a Go revision, Go executable, or Go artifact digest.".to_owned(),
            ],
        }
    }

    pub(super) fn finish(&mut self, elapsed: Duration) {
        self.wall_time_ms = elapsed.as_millis();
        self.peak_rss_kib = fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|text| {
                text.lines().find_map(|line| {
                    line.strip_prefix("VmHWM:").and_then(|value| {
                        let mut fields = value.split_whitespace();
                        let amount = fields.next()?.parse().ok()?;
                        (fields.next()? == "kB").then_some(amount)
                    })
                })
            });
    }
}

fn compiled_helper_digests() -> BTreeMap<String, String> {
    [
        ("project.rs", include_bytes!("../project.rs").as_slice()),
        (
            "project_main.rs",
            include_bytes!("../project_main.rs").as_slice(),
        ),
        (
            "project/options.rs",
            include_bytes!("options.rs").as_slice(),
        ),
        ("project/graph.rs", include_bytes!("graph.rs").as_slice()),
        (
            "project/provenance.rs",
            include_bytes!("provenance.rs").as_slice(),
        ),
        (
            "artifacts/mod.rs",
            include_bytes!("../artifacts/mod.rs").as_slice(),
        ),
        (
            "artifacts/project.rs",
            include_bytes!("../artifacts/project.rs").as_slice(),
        ),
    ]
    .into_iter()
    .map(|(name, bytes)| (name.to_owned(), stable_digest(bytes)))
    .collect()
}

fn digest_file(path: &Path) -> io::Result<ProjectFileDigest> {
    let mut input = File::open(path)?;
    let mut hash = Xxh3::new();
    let mut buffer = vec![0; 65_536].into_boxed_slice();
    let mut byte_count = 0;
    loop {
        let count = input.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        hash.update(&buffer[..count]);
        byte_count += u64::try_from(count).expect("buffer size fits u64");
    }
    Ok(ProjectFileDigest {
        path: path.to_string_lossy().into_owned(),
        byte_count,
        digest: format!("{:032x}", hash.digest128()),
        digest_algorithm: SCORECARD_DIGEST_ALGORITHM,
    })
}
