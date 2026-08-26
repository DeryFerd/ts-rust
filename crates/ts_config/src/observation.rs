//! Optional evidence from the config resolver's existing filesystem calls.

use std::io;

use crate::{ParseResult, ProjectConfig};

/// Bounds the retained event count and total UTF-8 string bytes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ConfigObservationLimits {
    pub max_events: usize,
    pub max_string_bytes: usize,
}

impl Default for ConfigObservationLimits {
    fn default() -> Self {
        Self {
            max_events: 16_384,
            max_string_bytes: 16 * 1024 * 1024,
        }
    }
}

/// Why the resolver read a file.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConfigInputKind {
    Config,
    PackageJson,
}

/// The error returned by an existing resolver read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConfigReadError {
    pub kind: io::ErrorKind,
    pub message: String,
}

/// One existing resolver operation or decision, in execution order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ConfigResolutionEvent {
    FileExists {
        path: String,
        exists: bool,
    },
    DirectoryExists {
        path: String,
        exists: bool,
    },
    /// Success retains the exact text passed to the JSONC parser.
    ReadFile {
        path: String,
        kind: ConfigInputKind,
        result: Result<String, ConfigReadError>,
    },
    /// Recorded after path lookup and before loading the selected base.
    Extends {
        config_path: String,
        specifier: String,
        resolved_path: Option<String>,
    },
    /// The closing path is not read again when a cycle is found.
    Cycle {
        path: String,
        chain: Vec<String>,
    },
}

/// An ordered prefix of config resolver evidence, without deduplication.
///
/// Once a limit prevents an event from being retained, all later events are
/// counted as omitted. No event or source text is partially retained.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ConfigResolutionObservation {
    pub events: Vec<ConfigResolutionEvent>,
    pub omitted_events: usize,
}

impl ConfigResolutionObservation {
    /// Whether every config resolver event was retained, not whether the
    /// config was valid or the complete Program graph was observed.
    #[must_use]
    pub const fn is_complete(&self) -> bool {
        self.omitted_events == 0
    }
}

/// The normal config result and evidence captured during the same resolution.
#[derive(Clone, Debug, PartialEq)]
pub struct ObservedConfigResolution {
    pub result: ParseResult<ProjectConfig>,
    pub observation: ConfigResolutionObservation,
}

pub(super) struct ConfigObservationRecorder {
    limits: ConfigObservationLimits,
    string_bytes: usize,
    observation: ConfigResolutionObservation,
}

impl ConfigObservationRecorder {
    pub(super) fn new(limits: ConfigObservationLimits) -> Self {
        Self {
            limits,
            string_bytes: 0,
            observation: ConfigResolutionObservation::default(),
        }
    }

    pub(super) fn finish(self) -> ConfigResolutionObservation {
        self.observation
    }

    fn retain(
        &mut self,
        string_bytes: Option<usize>,
        event: impl FnOnce() -> ConfigResolutionEvent,
    ) {
        let total = string_bytes.and_then(|bytes| self.string_bytes.checked_add(bytes));
        if self.observation.omitted_events != 0
            || self.observation.events.len() >= self.limits.max_events
            || total.is_none_or(|bytes| bytes > self.limits.max_string_bytes)
        {
            self.observation.omitted_events = self.observation.omitted_events.saturating_add(1);
            return;
        }
        self.string_bytes = total.expect("the retained string bytes fit the limit");
        self.observation.events.push(event());
    }

    pub(super) fn file_exists(&mut self, path: &str, exists: bool) {
        self.retain(Some(path.len()), || ConfigResolutionEvent::FileExists {
            path: path.to_owned(),
            exists,
        });
    }

    pub(super) fn directory_exists(&mut self, path: &str, exists: bool) {
        self.retain(Some(path.len()), || {
            ConfigResolutionEvent::DirectoryExists {
                path: path.to_owned(),
                exists,
            }
        });
    }

    pub(super) fn read_text(&mut self, path: &str, kind: ConfigInputKind, text: &str) {
        self.retain(path.len().checked_add(text.len()), || {
            ConfigResolutionEvent::ReadFile {
                path: path.to_owned(),
                kind,
                result: Ok(text.to_owned()),
            }
        });
    }

    pub(super) fn read_error(
        &mut self,
        path: &str,
        kind: ConfigInputKind,
        error_kind: io::ErrorKind,
        message: &str,
    ) {
        self.retain(path.len().checked_add(message.len()), || {
            ConfigResolutionEvent::ReadFile {
                path: path.to_owned(),
                kind,
                result: Err(ConfigReadError {
                    kind: error_kind,
                    message: message.to_owned(),
                }),
            }
        });
    }

    pub(super) fn extends(
        &mut self,
        config_path: &str,
        specifier: &str,
        resolved_path: Option<&str>,
    ) {
        let bytes = config_path
            .len()
            .checked_add(specifier.len())
            .and_then(|bytes| bytes.checked_add(resolved_path.map_or(0, str::len)));
        self.retain(bytes, || ConfigResolutionEvent::Extends {
            config_path: config_path.to_owned(),
            specifier: specifier.to_owned(),
            resolved_path: resolved_path.map(str::to_owned),
        });
    }

    pub(super) fn cycle(&mut self, path: &str, chain: &[String]) {
        let bytes = chain
            .iter()
            .try_fold(path.len(), |bytes, path| bytes.checked_add(path.len()));
        self.retain(bytes, || ConfigResolutionEvent::Cycle {
            path: path.to_owned(),
            chain: chain.to_vec(),
        });
    }
}
