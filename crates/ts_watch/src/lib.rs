//! Watch-mode compilation orchestration.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt, fs,
    path::{Path, PathBuf},
    sync::mpsc,
};

use ts_compiler::Program;
pub use ts_fswatch::WatchMode;
use ts_fswatch::{Event, NotifyBackend, Watch, WatchBatch, Watcher};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WatchPath {
    pub directory: PathBuf,
    pub mode: WatchMode,
}

impl WatchPath {
    #[must_use]
    pub fn new(directory: impl Into<PathBuf>, mode: WatchMode) -> Self {
        Self {
            directory: directory.into(),
            mode,
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CompileCycle {
    pub error_count: usize,
    pub watch_paths: Vec<WatchPath>,
}

pub trait WatchCompiler {
    /// Compiles once and returns the next desired watch set.
    ///
    /// # Errors
    ///
    /// Returns an error when compilation or output writing cannot continue.
    fn compile(&mut self) -> Result<CompileCycle, WatchError>;
}

impl<F> WatchCompiler for F
where
    F: FnMut() -> Result<CompileCycle, WatchError>,
{
    fn compile(&mut self) -> Result<CompileCycle, WatchError> {
        self()
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ChangeSet {
    pub paths: BTreeSet<PathBuf>,
    pub overflow: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum WatchSignal {
    Changed(ChangeSet),
    Stop,
}

#[derive(Clone, Debug)]
pub struct StopHandle {
    sender: mpsc::Sender<WatchMessage>,
}

impl StopHandle {
    /// Stops a filesystem event source that may be blocked waiting for changes.
    ///
    /// # Errors
    ///
    /// Returns an error if the event source has already been dropped.
    pub fn stop(&self) -> Result<(), WatchError> {
        self.sender
            .send(WatchMessage::Stop)
            .map_err(|error| WatchError::EventSource(error.to_string()))
    }
}

pub trait EventSource {
    /// Replaces the active watch set.
    ///
    /// # Errors
    ///
    /// Returns an error if a requested directory cannot be watched.
    fn reconcile(&mut self, paths: &[WatchPath]) -> Result<(), WatchError>;

    /// Blocks until changes or a stop signal arrive.
    ///
    /// # Errors
    ///
    /// Returns an error if the event stream terminates unexpectedly.
    fn next(&mut self) -> Result<WatchSignal, WatchError>;
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum WatchStatus {
    Starting,
    ChangeDetected,
    Waiting { error_count: usize },
}

impl WatchStatus {
    #[must_use]
    pub fn message(&self) -> String {
        match self {
            Self::Starting => "Starting compilation in watch mode...".to_owned(),
            Self::ChangeDetected => {
                "File change detected. Starting incremental compilation...".to_owned()
            }
            Self::Waiting { error_count: 1 } => {
                "Found 1 error. Watching for file changes.".to_owned()
            }
            Self::Waiting { error_count } => {
                format!("Found {error_count} errors. Watching for file changes.")
            }
        }
    }
}

pub trait StatusReporter {
    fn report(&mut self, status: WatchStatus);
}

impl<F: FnMut(WatchStatus)> StatusReporter for F {
    fn report(&mut self, status: WatchStatus) {
        self(status);
    }
}

pub trait StopCondition {
    fn should_stop(&mut self, completed_cycles: usize) -> bool;
}

#[derive(Clone, Copy, Debug, Default)]
pub struct NeverStop;

impl StopCondition for NeverStop {
    fn should_stop(&mut self, _completed_cycles: usize) -> bool {
        false
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct WatchSummary {
    pub completed_cycles: usize,
    pub last_error_count: usize,
}

pub struct Coordinator<C, E, R> {
    compiler: C,
    events: E,
    reporter: R,
}

impl<C, E, R> Coordinator<C, E, R>
where
    C: WatchCompiler,
    E: EventSource,
    R: StatusReporter,
{
    #[must_use]
    pub const fn new(compiler: C, events: E, reporter: R) -> Self {
        Self {
            compiler,
            events,
            reporter,
        }
    }

    /// Runs until the event source or stop condition requests termination.
    ///
    /// # Errors
    ///
    /// Returns a compiler or event-source failure.
    pub fn run_with_stop(
        &mut self,
        stop: &mut impl StopCondition,
    ) -> Result<WatchSummary, WatchError> {
        self.reporter.report(WatchStatus::Starting);
        let mut summary = WatchSummary::default();
        loop {
            let cycle = self.compiler.compile()?;
            summary.completed_cycles += 1;
            summary.last_error_count = cycle.error_count;
            self.events.reconcile(&cycle.watch_paths)?;
            self.reporter.report(WatchStatus::Waiting {
                error_count: cycle.error_count,
            });
            if stop.should_stop(summary.completed_cycles) {
                return Ok(summary);
            }
            loop {
                match self.events.next()? {
                    WatchSignal::Stop => return Ok(summary),
                    WatchSignal::Changed(changes)
                        if changes.paths.is_empty() && !changes.overflow => {}
                    WatchSignal::Changed(_) => {
                        self.reporter.report(WatchStatus::ChangeDetected);
                        break;
                    }
                }
            }
        }
    }

    /// Runs indefinitely unless the event source requests stop.
    ///
    /// # Errors
    ///
    /// Returns a compiler or event-source failure.
    pub fn run(&mut self) -> Result<WatchSummary, WatchError> {
        self.run_with_stop(&mut NeverStop)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum WatchError {
    Compile(String),
    EventSource(String),
}

impl fmt::Display for WatchError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Compile(message) => write!(formatter, "watch compilation: {message}"),
            Self::EventSource(message) => write!(formatter, "watch events: {message}"),
        }
    }
}

impl Error for WatchError {}

pub struct FsEventSource {
    watcher: Watcher<NotifyBackend>,
    watches: BTreeMap<PathBuf, (WatchMode, Watch)>,
    sender: mpsc::Sender<WatchMessage>,
    receiver: mpsc::Receiver<WatchMessage>,
}

#[derive(Debug)]
enum WatchMessage {
    Batch {
        directory: PathBuf,
        batch: WatchBatch,
    },
    Stop,
}

impl Default for FsEventSource {
    fn default() -> Self {
        let (sender, receiver) = mpsc::channel();
        Self {
            watcher: Watcher::default(),
            watches: BTreeMap::new(),
            sender,
            receiver,
        }
    }
}

impl FsEventSource {
    #[must_use]
    pub fn stop_handle(&self) -> StopHandle {
        StopHandle {
            sender: self.sender.clone(),
        }
    }
}

impl EventSource for FsEventSource {
    fn reconcile(&mut self, paths: &[WatchPath]) -> Result<(), WatchError> {
        let desired = resolve_watch_paths(paths);
        self.watches.retain(|directory, (mode, watch)| {
            if desired.get(directory) == Some(mode) {
                true
            } else {
                let _ = watch.close();
                false
            }
        });
        for (directory, mode) in desired {
            if self.watches.contains_key(&directory) {
                continue;
            }
            let sender = self.sender.clone();
            let watched_directory = directory.clone();
            let watch = self
                .watcher
                .watch(&directory, mode, move |batch| {
                    let _ = sender.send(WatchMessage::Batch {
                        directory: watched_directory.clone(),
                        batch,
                    });
                })
                .map_err(|error| WatchError::EventSource(error.to_string()))?;
            self.watches.insert(directory, (mode, watch));
        }
        Ok(())
    }

    fn next(&mut self) -> Result<WatchSignal, WatchError> {
        let message = self
            .receiver
            .recv()
            .map_err(|error| WatchError::EventSource(error.to_string()))?;
        let WatchMessage::Batch { directory, batch } = message else {
            self.watches.clear();
            return Ok(WatchSignal::Stop);
        };
        if let Some(error @ ts_fswatch::WatchError::Backend(_)) = &batch.error {
            return Err(WatchError::EventSource(error.to_string()));
        }
        if matches!(batch.error, Some(ts_fswatch::WatchError::Terminated(_))) {
            self.watches.remove(&directory);
        }
        let mut changes = ChangeSet {
            overflow: matches!(
                batch.error,
                Some(ts_fswatch::WatchError::Overflow(_) | ts_fswatch::WatchError::Terminated(_))
            ),
            ..ChangeSet::default()
        };
        for event in batch.events {
            match event {
                Event::Create(path) | Event::Change(path) | Event::Delete(path) => {
                    if !should_ignore_watch_path(&path) {
                        changes.paths.insert(path);
                    }
                }
                Event::Rename { from, to } => {
                    for path in [from, to] {
                        if !should_ignore_watch_path(&path) {
                            changes.paths.insert(path);
                        }
                    }
                }
            }
        }
        Ok(WatchSignal::Changed(changes))
    }
}

fn should_ignore_watch_path(path: &Path) -> bool {
    let mut parent_is_node_modules = false;
    for component in path.components() {
        let std::path::Component::Normal(component) = component else {
            parent_is_node_modules = false;
            continue;
        };
        let component = component.to_string_lossy();
        if component == ".git"
            || component.starts_with(".#")
            || parent_is_node_modules && component.starts_with('.')
        {
            return true;
        }
        parent_is_node_modules = component == "node_modules";
    }
    false
}

fn resolve_watch_paths(paths: &[WatchPath]) -> BTreeMap<PathBuf, WatchMode> {
    let mut resolved = BTreeMap::new();
    for path in paths {
        let mut directory = path.directory.as_path();
        let mut mode = path.mode;
        while !directory.is_dir() {
            let Some(parent) = directory.parent() else {
                break;
            };
            directory = parent;
            mode = WatchMode::NonRecursive;
        }
        if !directory.is_dir() {
            continue;
        }

        let directory = canonical_directory(directory);
        resolved
            .entry(directory)
            .and_modify(|existing| {
                if mode == WatchMode::Recursive {
                    *existing = WatchMode::Recursive;
                }
            })
            .or_insert(mode);
    }
    resolved
}

/// Computes config, root, and loaded import directories to watch.
#[must_use]
pub fn watch_paths_for_program(
    program: &Program,
    current_directory: &Path,
    config_path: Option<&Path>,
    roots: &[String],
) -> Vec<WatchPath> {
    let mut directories = BTreeSet::new();
    if let Some(parent) = config_path.and_then(Path::parent) {
        directories.insert(canonical_directory(parent));
    }
    for root in roots {
        let path = Path::new(root);
        let absolute = if path.is_absolute() {
            path.to_owned()
        } else {
            current_directory.join(path)
        };
        if let Some(parent) = absolute.parent() {
            directories.insert(canonical_directory(parent));
        }
    }
    for source in program
        .source_files()
        .iter()
        .filter(|source| !source.is_default_library)
    {
        if let Some(parent) = Path::new(&source.file_name).parent() {
            directories.insert(canonical_directory(parent));
        }
    }
    directories
        .into_iter()
        .map(|directory| WatchPath::new(directory, WatchMode::NonRecursive))
        .collect()
}

fn canonical_directory(path: &Path) -> PathBuf {
    fs::canonicalize(path).unwrap_or_else(|_| path.to_owned())
}

#[cfg(test)]
mod tests {
    use std::{
        collections::VecDeque,
        sync::atomic::{AtomicU64, Ordering},
    };

    use ts_vfs::{FileSystem, MemoryFileSystem};

    use super::*;

    struct FakeCompiler {
        cycles: VecDeque<CompileCycle>,
    }

    impl WatchCompiler for FakeCompiler {
        fn compile(&mut self) -> Result<CompileCycle, WatchError> {
            self.cycles
                .pop_front()
                .ok_or_else(|| WatchError::Compile("unexpected compile".to_owned()))
        }
    }

    #[derive(Default)]
    struct FakeEvents {
        reconciled: Vec<Vec<WatchPath>>,
        signals: VecDeque<WatchSignal>,
    }

    impl EventSource for FakeEvents {
        fn reconcile(&mut self, paths: &[WatchPath]) -> Result<(), WatchError> {
            self.reconciled.push(paths.to_vec());
            Ok(())
        }

        fn next(&mut self) -> Result<WatchSignal, WatchError> {
            self.signals
                .pop_front()
                .ok_or_else(|| WatchError::EventSource("unexpected wait".to_owned()))
        }
    }

    struct AfterCycles(usize);

    impl StopCondition for AfterCycles {
        fn should_stop(&mut self, completed_cycles: usize) -> bool {
            completed_cycles >= self.0
        }
    }

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn new() -> Self {
            static NEXT_ID: AtomicU64 = AtomicU64::new(0);
            let directory = std::env::temp_dir().join(format!(
                "ts-watch-{}-{}",
                std::process::id(),
                NEXT_ID.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir_all(&directory).unwrap();
            Self(directory)
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn coordinates_initial_compile_change_rebuild_and_stop() {
        let root = WatchPath::new("/project", WatchMode::NonRecursive);
        let compiler = FakeCompiler {
            cycles: VecDeque::from([
                CompileCycle {
                    error_count: 1,
                    watch_paths: vec![root.clone()],
                },
                CompileCycle {
                    error_count: 0,
                    watch_paths: vec![root.clone()],
                },
            ]),
        };
        let events = FakeEvents {
            signals: VecDeque::from([WatchSignal::Changed(ChangeSet {
                paths: BTreeSet::from([PathBuf::from("/project/main.ts")]),
                overflow: false,
            })]),
            ..FakeEvents::default()
        };
        let mut statuses = Vec::new();
        let mut coordinator = Coordinator::new(compiler, events, |status| statuses.push(status));
        let summary = coordinator.run_with_stop(&mut AfterCycles(2)).unwrap();
        let reconciled = coordinator.events.reconciled.clone();
        drop(coordinator);
        assert_eq!(summary.completed_cycles, 2);
        assert_eq!(summary.last_error_count, 0);
        assert_eq!(
            statuses,
            [
                WatchStatus::Starting,
                WatchStatus::Waiting { error_count: 1 },
                WatchStatus::ChangeDetected,
                WatchStatus::Waiting { error_count: 0 }
            ]
        );
        assert_eq!(reconciled, [vec![root.clone()], vec![root]]);
    }

    #[test]
    fn event_source_stop_ends_without_an_extra_compile() {
        let compiler = FakeCompiler {
            cycles: VecDeque::from([CompileCycle::default()]),
        };
        let events = FakeEvents {
            signals: VecDeque::from([WatchSignal::Stop]),
            ..FakeEvents::default()
        };
        let mut coordinator = Coordinator::new(compiler, events, |_| {});
        assert_eq!(coordinator.run().unwrap().completed_cycles, 1);
    }

    #[test]
    fn stop_handle_interrupts_a_blocked_filesystem_event_source() {
        let directory = TestDirectory::new();
        let mut source = FsEventSource::default();
        source
            .reconcile(&[WatchPath::new(&directory.0, WatchMode::NonRecursive)])
            .unwrap();
        let stop = source.stop_handle();
        let (ready_sender, ready_receiver) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            ready_sender.send(()).unwrap();
            let signal = source.next().unwrap();
            (signal, source.watches.len())
        });
        ready_receiver.recv().unwrap();

        stop.stop().unwrap();

        assert_eq!(worker.join().unwrap(), (WatchSignal::Stop, 0));
    }

    #[test]
    fn filesystem_events_ignore_git_and_editor_artifacts() {
        let mut source = FsEventSource::default();
        source
            .sender
            .send(WatchMessage::Batch {
                directory: "/project".into(),
                batch: WatchBatch {
                    events: vec![
                        Event::Change("/project/.git/index".into()),
                        Event::Create("/project/node_modules/.cache/state".into()),
                        Event::Delete("/project/.#index.ts".into()),
                        Event::Rename {
                            from: "/project/.#source.ts".into(),
                            to: "/project/source.ts".into(),
                        },
                        Event::Change("/project/node_modules/pkg/index.d.ts".into()),
                    ],
                    error: None,
                },
            })
            .unwrap();

        assert_eq!(
            source.next().unwrap(),
            WatchSignal::Changed(ChangeSet {
                paths: BTreeSet::from([
                    PathBuf::from("/project/node_modules/pkg/index.d.ts"),
                    PathBuf::from("/project/source.ts")
                ]),
                overflow: false,
            })
        );
    }

    #[test]
    fn terminated_watches_are_recreated_after_a_rescan() {
        let directory = TestDirectory::new();
        let watched_directory = fs::canonicalize(&directory.0).unwrap();
        let paths = [WatchPath::new(&directory.0, WatchMode::NonRecursive)];
        let mut source = FsEventSource::default();
        source.reconcile(&paths).unwrap();
        source
            .sender
            .send(WatchMessage::Batch {
                directory: watched_directory.clone(),
                batch: WatchBatch {
                    events: Vec::new(),
                    error: Some(ts_fswatch::WatchError::Terminated(
                        "watch closed".to_owned(),
                    )),
                },
            })
            .unwrap();

        assert_eq!(
            source.next().unwrap(),
            WatchSignal::Changed(ChangeSet {
                overflow: true,
                ..ChangeSet::default()
            })
        );
        assert!(!source.watches.contains_key(&watched_directory));

        source.reconcile(&paths).unwrap();

        assert!(source.watches.contains_key(&watched_directory));
    }

    #[test]
    fn missing_watch_directories_fall_back_to_existing_ancestors() {
        let directory = TestDirectory::new();
        let requested = directory.0.join("missing/nested");

        let resolved = resolve_watch_paths(&[WatchPath::new(requested, WatchMode::Recursive)]);

        assert_eq!(
            resolved,
            BTreeMap::from([(
                fs::canonicalize(&directory.0).unwrap(),
                WatchMode::NonRecursive
            )])
        );
    }

    #[test]
    fn recursive_watch_mode_wins_for_duplicate_directories() {
        let directory = TestDirectory::new();
        let paths = [
            WatchPath::new(&directory.0, WatchMode::Recursive),
            WatchPath::new(&directory.0, WatchMode::NonRecursive),
        ];

        let resolved = resolve_watch_paths(&paths);

        assert_eq!(
            resolved,
            BTreeMap::from([(
                fs::canonicalize(&directory.0).unwrap(),
                WatchMode::Recursive
            )])
        );
    }

    #[test]
    fn derives_config_root_and_import_directories_from_program() {
        let file_system = MemoryFileSystem::new(true);
        file_system
            .write_file(
                "/project/main.ts",
                "import { value } from './lib/dep'; value;",
            )
            .unwrap();
        file_system
            .write_file("/project/lib/dep.ts", "export const value = 1;")
            .unwrap();
        let program = Program::new_with_module_resolution(
            &file_system,
            "/project",
            &["main.ts".to_owned()],
            ts_module::ResolutionOptions::default(),
        );
        let paths = watch_paths_for_program(
            &program,
            Path::new("/project"),
            Some(Path::new("/project/tsconfig.json")),
            &["main.ts".to_owned()],
        );
        assert_eq!(
            paths,
            [
                WatchPath::new("/project", WatchMode::NonRecursive),
                WatchPath::new("/project/lib", WatchMode::NonRecursive)
            ]
        );
    }
}
