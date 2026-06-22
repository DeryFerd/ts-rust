//! Deterministic build information and incremental invalidation decisions.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
};

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BuildInfo {
    pub version: String,
    pub options_hash: String,
    pub files: BTreeMap<String, String>,
    pub dependencies: BTreeMap<String, String>,
    pub outputs: Vec<String>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BuildDecision {
    UpToDate,
    Affected,
}

#[derive(Debug)]
pub enum BuildInfoError {
    InvalidJson(serde_json::Error),
    VersionMismatch { expected: String, actual: String },
}

impl fmt::Display for BuildInfoError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidJson(error) => write!(formatter, "invalid build info: {error}"),
            Self::VersionMismatch { expected, actual } => {
                write!(
                    formatter,
                    "build info version '{actual}' does not match '{expected}'"
                )
            }
        }
    }
}

impl std::error::Error for BuildInfoError {}

impl BuildInfo {
    #[must_use]
    pub fn new(
        version: impl Into<String>,
        options: &str,
        files: impl IntoIterator<Item = (String, String)>,
        dependencies: BTreeMap<String, String>,
        mut outputs: Vec<String>,
    ) -> Self {
        outputs.sort();
        outputs.dedup();
        Self {
            version: version.into(),
            options_hash: hash_text(options),
            files: files
                .into_iter()
                .map(|(path, text)| (path, hash_text(&text)))
                .collect(),
            dependencies,
            outputs,
        }
    }

    /// # Errors
    /// Returns an error for malformed JSON or a compiler version mismatch.
    pub fn from_json(source: &str, expected_version: &str) -> Result<Self, BuildInfoError> {
        let info: Self = serde_json::from_str(source).map_err(BuildInfoError::InvalidJson)?;
        if info.version != expected_version {
            return Err(BuildInfoError::VersionMismatch {
                expected: expected_version.to_owned(),
                actual: info.version,
            });
        }
        Ok(info)
    }

    /// # Errors
    /// Returns an error if JSON serialization fails.
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    #[must_use]
    pub fn decision(
        previous: Option<&Self>,
        current: &Self,
        output_exists: impl Fn(&str) -> bool,
    ) -> BuildDecision {
        let unchanged = previous.is_some_and(|previous| {
            previous.version == current.version
                && previous.options_hash == current.options_hash
                && previous.files == current.files
                && previous.dependencies == current.dependencies
                && previous.outputs == current.outputs
                && previous.outputs.iter().all(|path| output_exists(path))
        });
        if unchanged {
            BuildDecision::UpToDate
        } else {
            BuildDecision::Affected
        }
    }

    #[must_use]
    pub fn affected_files(previous: Option<&Self>, current: &Self) -> Vec<String> {
        let Some(previous) = previous else {
            return current.files.keys().cloned().collect();
        };
        previous
            .files
            .keys()
            .chain(current.files.keys())
            .cloned()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .filter(|path| previous.files.get(path) != current.files.get(path))
            .collect()
    }

    #[must_use]
    pub fn project_signature(&self) -> String {
        self.to_json()
            .map_or_else(|_| hash_text("invalid"), |json| hash_text(&json))
    }
}

#[must_use]
pub fn hash_text(text: &str) -> String {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64;
    for byte in text.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    format!("{hash:016x}")
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::{BuildDecision, BuildInfo, BuildInfoError, hash_text};

    fn info(source: &str, dependency: &str) -> BuildInfo {
        BuildInfo::new(
            "1",
            "options",
            [("/src/main.ts".into(), source.into())],
            BTreeMap::from([("/dep/tsconfig.json".into(), dependency.into())]),
            vec!["/dist/main.js".into()],
        )
    }

    #[test]
    fn hashes_and_json_are_deterministic() {
        assert_eq!(hash_text("same"), hash_text("same"));
        let first = info("const x = 1;", "a");
        let json = first.to_json().unwrap();
        assert_eq!(BuildInfo::from_json(&json, "1").unwrap(), first);
    }

    #[test]
    fn validates_compiler_version() {
        let json = info("const x = 1;", "a").to_json().unwrap();
        assert!(matches!(
            BuildInfo::from_json(&json, "2"),
            Err(BuildInfoError::VersionMismatch { .. })
        ));
    }

    #[test]
    fn tracks_sources_dependencies_and_outputs() {
        let previous = info("const x = 1;", "a");
        assert_eq!(
            BuildInfo::decision(Some(&previous), &previous, |_| true),
            BuildDecision::UpToDate
        );
        assert_eq!(
            BuildInfo::decision(Some(&previous), &info("const x = 2;", "a"), |_| true),
            BuildDecision::Affected
        );
        assert_eq!(
            BuildInfo::affected_files(Some(&previous), &info("const x = 2;", "a")),
            ["/src/main.ts"]
        );
        assert_eq!(
            BuildInfo::decision(Some(&previous), &info("const x = 1;", "b"), |_| true),
            BuildDecision::Affected
        );
        assert_eq!(
            BuildInfo::decision(Some(&previous), &previous, |_| false),
            BuildDecision::Affected
        );
        let changed_options = BuildInfo::new(
            "1",
            "changed options",
            [("/src/main.ts".into(), "const x = 1;".into())],
            BTreeMap::from([("/dep/tsconfig.json".into(), "a".into())]),
            vec!["/dist/main.js".into()],
        );
        assert_eq!(
            BuildInfo::decision(Some(&previous), &changed_options, |_| true),
            BuildDecision::Affected
        );
    }
}
