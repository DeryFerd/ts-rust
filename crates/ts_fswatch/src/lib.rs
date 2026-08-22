//! Portable, debounced filesystem watching.
//!
//! Backend events are normalized to canonical absolute paths, coalesced by
//! path, and delivered from one worker thread per subscription. The default
//! backend uses [`notify`]; tests and embedders can inject another backend.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt, fs,
    path::{Component, Path, PathBuf},
    sync::{Arc, mpsc},
    thread,
    time::{Duration, Instant},
};

/// Upstream-compatible quiet and maximum debounce windows.
pub const DEFAULT_MIN_WAIT: Duration = Duration::from_millis(50);
pub const DEFAULT_MAX_WAIT: Duration = Duration::from_millis(500);

/// Whether a directory watch includes only direct children or all descendants.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum WatchMode {
    #[default]
    NonRecursive,
    Recursive,
}

/// One classified filesystem change.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Event {
    Create(PathBuf),
    Change(PathBuf),
    Delete(PathBuf),
    Rename { from: PathBuf, to: PathBuf },
}

impl Event {
    fn map_paths(self, mut map: impl FnMut(PathBuf) -> PathBuf) -> Self {
        match self {
            Self::Create(path) => Self::Create(map(path)),
            Self::Change(path) => Self::Change(map(path)),
            Self::Delete(path) => Self::Delete(map(path)),
            Self::Rename { from, to } => Self::Rename {
                from: map(from),
                to: map(to),
            },
        }
    }

    fn is_visible_from(&self, root: &Path, mode: WatchMode) -> bool {
        let visible = |path: &Path| match mode {
            WatchMode::Recursive => path.starts_with(root) && path != root,
            WatchMode::NonRecursive => path.parent() == Some(root),
        };
        match self {
            Self::Create(path) | Self::Change(path) | Self::Delete(path) => visible(path),
            Self::Rename { from, to } => visible(from) || visible(to),
        }
    }
}

/// Error reported while establishing or running a watch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum WatchError {
    InvalidPath(String),
    Overflow(String),
    Terminated(String),
    Backend(String),
}

impl fmt::Display for WatchError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidPath(message) => write!(formatter, "invalid watch path: {message}"),
            Self::Overflow(message) => write!(formatter, "watch overflow: {message}"),
            Self::Terminated(message) => write!(formatter, "watch terminated: {message}"),
            Self::Backend(message) => write!(formatter, "watch backend: {message}"),
        }
    }
}

impl Error for WatchError {}

/// A batch emitted by a backend before high-level filtering and coalescing.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BackendBatch {
    pub events: Vec<Event>,
    pub error: Option<WatchError>,
}

/// A debounced batch delivered to a watcher callback.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct WatchBatch {
    pub events: Vec<Event>,
    pub error: Option<WatchError>,
}

pub type BackendSink = Arc<dyn Fn(BackendBatch) + Send + Sync>;

/// Live backend-specific watch state.
pub trait BackendWatch: Send {
    /// Stops the underlying watch. Implementations must be idempotent.
    ///
    /// # Errors
    ///
    /// Returns an error if the backend cannot release the watch.
    fn close(&mut self) -> Result<(), WatchError>;
}

/// Injectable filesystem event source.
pub trait Backend: Send + Sync + 'static {
    /// Starts emitting events for `root` into `sink`.
    ///
    /// # Errors
    ///
    /// Returns an error if the backend cannot establish the watch.
    fn watch(
        &self,
        root: &Path,
        mode: WatchMode,
        sink: BackendSink,
    ) -> Result<Box<dyn BackendWatch>, WatchError>;
}

/// Debounce timing policy.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DebounceConfig {
    pub min_wait: Duration,
    pub max_wait: Duration,
}

impl Default for DebounceConfig {
    fn default() -> Self {
        Self {
            min_wait: DEFAULT_MIN_WAIT,
            max_wait: DEFAULT_MAX_WAIT,
        }
    }
}

/// Deterministic path-based event coalescer.
#[derive(Clone, Debug, Default)]
pub struct EventCoalescer {
    paths: BTreeMap<PathBuf, PathState>,
    renames: BTreeSet<(PathBuf, PathBuf)>,
}

#[derive(Clone, Copy, Debug, Default)]
struct PathState {
    created: bool,
    deleted: bool,
}

impl EventCoalescer {
    pub fn push(&mut self, event: Event) {
        match event {
            Event::Create(path) => {
                let state = self.paths.entry(path).or_default();
                if state.deleted {
                    *state = PathState::default();
                } else {
                    state.created = true;
                }
            }
            Event::Change(path) => {
                self.paths.entry(path).or_default();
            }
            Event::Delete(path) => {
                self.paths.entry(path).or_default().deleted = true;
            }
            Event::Rename { from, to } if from == to => {
                self.paths.entry(to).or_default();
            }
            Event::Rename { from, to } => {
                self.paths.remove(&from);
                self.paths.remove(&to);
                self.renames.insert((from, to));
            }
        }
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.paths.is_empty() && self.renames.is_empty()
    }

    /// Drains a stable, path-sorted representation of the net changes.
    pub fn drain(&mut self) -> Vec<Event> {
        let mut events = Vec::new();
        for (path, state) in std::mem::take(&mut self.paths) {
            if state.created && state.deleted {
                continue;
            }
            events.push(if state.deleted {
                Event::Delete(path)
            } else if state.created {
                Event::Create(path)
            } else {
                Event::Change(path)
            });
        }
        events.extend(
            std::mem::take(&mut self.renames)
                .into_iter()
                .map(|(from, to)| Event::Rename { from, to }),
        );
        events.sort();
        events
    }
}

/// Portable watcher using an injected backend.
#[derive(Clone)]
pub struct Watcher<B = NotifyBackend> {
    backend: Arc<B>,
    debounce: DebounceConfig,
}

impl Default for Watcher<NotifyBackend> {
    fn default() -> Self {
        Self::new(NotifyBackend)
    }
}

impl<B: Backend> Watcher<B> {
    #[must_use]
    pub fn new(backend: B) -> Self {
        Self {
            backend: Arc::new(backend),
            debounce: DebounceConfig::default(),
        }
    }

    #[must_use]
    pub const fn with_debounce(mut self, debounce: DebounceConfig) -> Self {
        self.debounce = debounce;
        self
    }

    /// Starts a watch rooted at an existing directory.
    ///
    /// # Errors
    ///
    /// Returns an error for a missing/non-directory root or backend failure.
    pub fn watch(
        &self,
        path: impl AsRef<Path>,
        mode: WatchMode,
        callback: impl Fn(WatchBatch) + Send + 'static,
    ) -> Result<Watch, WatchError> {
        let root = canonical_watch_root(path.as_ref())?;
        let (sender, receiver) = mpsc::channel();
        let sink_sender = sender.clone();
        let sink: BackendSink = Arc::new(move |batch| {
            let _ = sink_sender.send(WorkerMessage::Batch(batch));
        });
        let backend_watch = self.backend.watch(&root, mode, sink)?;
        let debounce = self.debounce;
        let worker_root = root.clone();
        let worker = thread::spawn(move || {
            run_worker(&receiver, &worker_root, mode, debounce, callback);
        });
        Ok(Watch {
            root,
            backend: Some(backend_watch),
            sender,
            worker: Some(worker),
            closed: false,
        })
    }
}

/// A live high-level watch subscription.
pub struct Watch {
    root: PathBuf,
    backend: Option<Box<dyn BackendWatch>>,
    sender: mpsc::Sender<WorkerMessage>,
    worker: Option<thread::JoinHandle<()>>,
    closed: bool,
}

impl Watch {
    #[must_use]
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Stops event delivery and releases backend resources. Idempotent.
    ///
    /// # Errors
    ///
    /// Returns a backend close error or a worker panic.
    pub fn close(&mut self) -> Result<(), WatchError> {
        if self.closed {
            return Ok(());
        }
        self.closed = true;
        let _ = self.sender.send(WorkerMessage::Stop);
        let backend_result = self.backend.as_mut().map_or(Ok(()), |watch| watch.close());
        self.backend = None;
        let worker_result = self.worker.take().map_or(Ok(()), |worker| {
            worker
                .join()
                .map_err(|_| WatchError::Backend("watch worker panicked".to_owned()))
        });
        backend_result.and(worker_result)
    }
}

impl Drop for Watch {
    fn drop(&mut self) {
        let _ = self.close();
    }
}

enum WorkerMessage {
    Batch(BackendBatch),
    Stop,
}

struct DebouncedEvents {
    events: EventCoalescer,
    error: Option<WatchError>,
    last_flush: Option<Instant>,
    last_event: Option<Instant>,
    config: DebounceConfig,
}

impl DebouncedEvents {
    const fn new(config: DebounceConfig) -> Self {
        Self {
            events: EventCoalescer {
                paths: BTreeMap::new(),
                renames: BTreeSet::new(),
            },
            error: None,
            last_flush: None,
            last_event: None,
            config,
        }
    }

    fn push(&mut self, batch: BackendBatch, now: Instant) -> bool {
        for event in batch.events {
            self.events.push(event);
        }
        if self.error.is_none() {
            self.error = batch.error;
        }
        self.last_event = Some(now);
        self.last_flush
            .is_none_or(|last_flush| now.duration_since(last_flush) >= self.config.max_wait)
    }

    fn deadline(&self) -> Option<Instant> {
        let quiet = self.last_event?.checked_add(self.config.min_wait)?;
        self.last_flush
            .and_then(|last_flush| last_flush.checked_add(self.config.max_wait))
            .map_or(Some(quiet), |maximum| Some(quiet.min(maximum)))
    }

    fn is_due(&self, now: Instant) -> bool {
        self.deadline().is_some_and(|deadline| now >= deadline)
    }

    fn drain(&mut self, now: Instant) -> WatchBatch {
        self.last_flush = Some(now);
        self.last_event = None;
        WatchBatch {
            events: self.events.drain(),
            error: self.error.take(),
        }
    }
}

fn run_worker(
    receiver: &mpsc::Receiver<WorkerMessage>,
    root: &Path,
    mode: WatchMode,
    config: DebounceConfig,
    callback: impl Fn(WatchBatch),
) {
    let mut pending = DebouncedEvents::new(config);
    loop {
        let message = match pending.deadline() {
            Some(deadline) => {
                receiver.recv_timeout(deadline.saturating_duration_since(Instant::now()))
            }
            None => receiver
                .recv()
                .map_err(|_| mpsc::RecvTimeoutError::Disconnected),
        };
        match message {
            Ok(WorkerMessage::Batch(mut batch)) => {
                batch.events = batch
                    .events
                    .into_iter()
                    .map(|event| event.map_paths(|path| canonical_event_path(root, &path)))
                    .filter(|event| event.is_visible_from(root, mode))
                    .collect();
                if batch.events.is_empty() && batch.error.is_none() {
                    continue;
                }
                let now = Instant::now();
                if pending.push(batch, now) {
                    callback(pending.drain(now));
                }
            }
            Ok(WorkerMessage::Stop) | Err(mpsc::RecvTimeoutError::Disconnected) => break,
            Err(mpsc::RecvTimeoutError::Timeout) => {
                let now = Instant::now();
                if pending.is_due(now) {
                    callback(pending.drain(now));
                }
            }
        }
    }
}

fn canonical_watch_root(path: &Path) -> Result<PathBuf, WatchError> {
    let canonical = fs::canonicalize(path)
        .map_err(|error| WatchError::InvalidPath(format!("{}: {error}", path.display())))?;
    if !canonical.is_dir() {
        return Err(WatchError::InvalidPath(format!(
            "{} is not a directory",
            canonical.display()
        )));
    }
    Ok(canonical)
}

fn canonical_event_path(root: &Path, path: &Path) -> PathBuf {
    let absolute = if path.is_absolute() {
        path.to_owned()
    } else {
        root.join(path)
    };
    let absolute = normalize_path(&absolute);
    let Some(parent) = absolute.parent() else {
        return absolute;
    };
    let Some(file_name) = absolute.file_name() else {
        return absolute;
    };
    fs::canonicalize(parent).map_or(absolute.clone(), |canonical| canonical.join(file_name))
}

fn normalize_path(path: &Path) -> PathBuf {
    let mut result = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                result.pop();
            }
            _ => result.push(component.as_os_str()),
        }
    }
    result
}

/// Cross-platform backend powered by the `notify` crate.
#[derive(Clone, Copy, Debug, Default)]
pub struct NotifyBackend;

impl Backend for NotifyBackend {
    fn watch(
        &self,
        root: &Path,
        mode: WatchMode,
        sink: BackendSink,
    ) -> Result<Box<dyn BackendWatch>, WatchError> {
        use notify::Watcher as _;

        let mut watcher = notify::recommended_watcher(
            move |result: notify::Result<notify::Event>| match result {
                Ok(event) if event.need_rescan() => sink(BackendBatch {
                    events: Vec::new(),
                    error: Some(WatchError::Overflow(
                        "backend requested a filesystem rescan".to_owned(),
                    )),
                }),
                Ok(event) => {
                    let events = classify_notify_event(event);
                    if !events.is_empty() {
                        sink(BackendBatch {
                            events,
                            error: None,
                        });
                    }
                }
                Err(error) => sink(BackendBatch {
                    events: Vec::new(),
                    error: Some(classify_notify_error(&error)),
                }),
            },
        )
        .map_err(|error| WatchError::Backend(error.to_string()))?;
        let recursive_mode = match mode {
            WatchMode::NonRecursive => notify::RecursiveMode::NonRecursive,
            WatchMode::Recursive => notify::RecursiveMode::Recursive,
        };
        watcher
            .watch(root, recursive_mode)
            .map_err(|error| WatchError::Backend(error.to_string()))?;
        Ok(Box::new(NotifyWatch {
            watcher,
            root: root.to_owned(),
            closed: false,
        }))
    }
}

struct NotifyWatch {
    watcher: notify::RecommendedWatcher,
    root: PathBuf,
    closed: bool,
}

impl BackendWatch for NotifyWatch {
    fn close(&mut self) -> Result<(), WatchError> {
        use notify::Watcher as _;

        if self.closed {
            return Ok(());
        }
        self.closed = true;
        self.watcher
            .unwatch(&self.root)
            .map_err(|error| WatchError::Backend(error.to_string()))
    }
}

fn classify_notify_event(event: notify::Event) -> Vec<Event> {
    use notify::event::{ModifyKind, RenameMode};

    match event.kind {
        notify::EventKind::Create(_) => event.paths.into_iter().map(Event::Create).collect(),
        notify::EventKind::Remove(_) => event.paths.into_iter().map(Event::Delete).collect(),
        notify::EventKind::Modify(ModifyKind::Name(RenameMode::Both)) => event
            .paths
            .chunks_exact(2)
            .map(|paths| Event::Rename {
                from: paths[0].clone(),
                to: paths[1].clone(),
            })
            .collect(),
        notify::EventKind::Modify(ModifyKind::Name(RenameMode::From)) => {
            event.paths.into_iter().map(Event::Delete).collect()
        }
        notify::EventKind::Modify(ModifyKind::Name(RenameMode::To)) => {
            event.paths.into_iter().map(Event::Create).collect()
        }
        notify::EventKind::Modify(ModifyKind::Name(_)) if event.paths.len() >= 2 => event
            .paths
            .chunks_exact(2)
            .map(|paths| Event::Rename {
                from: paths[0].clone(),
                to: paths[1].clone(),
            })
            .collect(),
        notify::EventKind::Modify(_) | notify::EventKind::Any => {
            event.paths.into_iter().map(Event::Change).collect()
        }
        notify::EventKind::Access(_) | notify::EventKind::Other => Vec::new(),
    }
}

fn classify_notify_error(error: &notify::Error) -> WatchError {
    match error.kind {
        notify::ErrorKind::PathNotFound | notify::ErrorKind::WatchNotFound => {
            WatchError::Terminated(error.to_string())
        }
        _ => WatchError::Backend(error.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        path::{Path, PathBuf},
        sync::{
            Arc, Mutex,
            atomic::{AtomicBool, AtomicU64, Ordering},
            mpsc,
        },
        time::{Duration, Instant},
    };

    use super::*;

    #[derive(Clone, Default)]
    struct FakeBackend {
        state: Arc<Mutex<FakeState>>,
    }

    #[derive(Default)]
    struct FakeState {
        root: Option<PathBuf>,
        mode: Option<WatchMode>,
        sink: Option<BackendSink>,
        closed: Arc<AtomicBool>,
    }

    impl FakeBackend {
        fn emit(&self, batch: BackendBatch) {
            let sink = self.state.lock().unwrap().sink.clone().unwrap();
            sink(batch);
        }

        fn registration(&self) -> (PathBuf, WatchMode) {
            let state = self.state.lock().unwrap();
            (state.root.clone().unwrap(), state.mode.unwrap())
        }

        fn closed(&self) -> bool {
            self.state.lock().unwrap().closed.load(Ordering::SeqCst)
        }
    }

    impl Backend for FakeBackend {
        fn watch(
            &self,
            root: &Path,
            mode: WatchMode,
            sink: BackendSink,
        ) -> Result<Box<dyn BackendWatch>, WatchError> {
            let mut state = self.state.lock().unwrap();
            state.root = Some(root.to_owned());
            state.mode = Some(mode);
            state.sink = Some(sink);
            state.closed.store(false, Ordering::SeqCst);
            Ok(Box::new(FakeWatch {
                closed: Arc::clone(&state.closed),
            }))
        }
    }

    struct FakeWatch {
        closed: Arc<AtomicBool>,
    }

    impl BackendWatch for FakeWatch {
        fn close(&mut self) -> Result<(), WatchError> {
            self.closed.store(true, Ordering::SeqCst);
            Ok(())
        }
    }

    struct TestDirectory(PathBuf);

    impl TestDirectory {
        fn new() -> Self {
            static NEXT_ID: AtomicU64 = AtomicU64::new(0);
            let path = std::env::temp_dir().join(format!(
                "ts-fswatch-{}-{}",
                std::process::id(),
                NEXT_ID.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir_all(path.join("nested")).unwrap();
            Self(path)
        }
    }

    impl Drop for TestDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn coalesces_upstream_create_delete_and_recreate_sequences() {
        let mut events = EventCoalescer::default();
        events.push(Event::Create("a".into()));
        events.push(Event::Delete("a".into()));
        events.push(Event::Delete("b".into()));
        events.push(Event::Create("b".into()));
        events.push(Event::Create("c".into()));
        events.push(Event::Delete("c".into()));
        events.push(Event::Create("c".into()));
        events.push(Event::Change("d".into()));
        events.push(Event::Change("d".into()));
        events.push(Event::Rename {
            from: "old".into(),
            to: "new".into(),
        });
        events.push(Event::Rename {
            from: "old".into(),
            to: "new".into(),
        });

        assert_eq!(
            events.drain(),
            [
                Event::Change("b".into()),
                Event::Change("c".into()),
                Event::Change("d".into()),
                Event::Rename {
                    from: "old".into(),
                    to: "new".into()
                }
            ]
        );
        assert!(events.is_empty());
    }

    #[test]
    fn classifies_notify_create_change_delete_and_rename_events() {
        use notify::event::{CreateKind, DataChange, ModifyKind, RemoveKind, RenameMode};

        let path = PathBuf::from("file.ts");
        assert_eq!(
            classify_notify_event(
                notify::Event::new(notify::EventKind::Create(CreateKind::File))
                    .add_path(path.clone())
            ),
            [Event::Create(path.clone())]
        );
        assert_eq!(
            classify_notify_event(
                notify::Event::new(notify::EventKind::Modify(ModifyKind::Data(
                    DataChange::Content
                )))
                .add_path(path.clone())
            ),
            [Event::Change(path.clone())]
        );
        assert_eq!(
            classify_notify_event(
                notify::Event::new(notify::EventKind::Remove(RemoveKind::File))
                    .add_path(path.clone())
            ),
            [Event::Delete(path)]
        );
        assert_eq!(
            classify_notify_event(
                notify::Event::new(notify::EventKind::Modify(ModifyKind::Name(
                    RenameMode::Both
                )))
                .add_path("old.ts".into())
                .add_path("new.ts".into())
            ),
            [Event::Rename {
                from: "old.ts".into(),
                to: "new.ts".into()
            }]
        );
    }

    #[test]
    fn debounce_uses_quiet_window_and_maximum_latency() {
        let config = DebounceConfig::default();
        let start = Instant::now();
        let mut pending = DebouncedEvents::new(config);
        assert!(pending.push(
            BackendBatch {
                events: vec![Event::Change("first".into())],
                error: None,
            },
            start,
        ));
        assert_eq!(pending.drain(start).events.len(), 1);

        assert!(!pending.push(
            BackendBatch {
                events: vec![Event::Change("second".into())],
                error: None,
            },
            start + Duration::from_millis(10),
        ));
        assert!(!pending.push(
            BackendBatch {
                events: vec![Event::Change("third".into())],
                error: None,
            },
            start + Duration::from_millis(40),
        ));
        assert!(!pending.is_due(start + Duration::from_millis(89)));
        assert!(pending.is_due(start + Duration::from_millis(90)));
        assert!(pending.push(
            BackendBatch {
                events: vec![Event::Change("forced".into())],
                error: None,
            },
            start + DEFAULT_MAX_WAIT,
        ));
    }

    #[test]
    fn injectable_backend_canonicalizes_and_filters_nonrecursive_events() {
        let directory = TestDirectory::new();
        let backend = FakeBackend::default();
        let (sender, receiver) = mpsc::channel();
        let mut watch = Watcher::new(backend.clone())
            .with_debounce(DebounceConfig {
                min_wait: Duration::ZERO,
                max_wait: Duration::ZERO,
            })
            .watch(&directory.0, WatchMode::NonRecursive, move |batch| {
                sender.send(batch).unwrap();
            })
            .unwrap();
        let canonical = fs::canonicalize(&directory.0).unwrap();
        assert_eq!(
            backend.registration(),
            (canonical.clone(), WatchMode::NonRecursive)
        );

        backend.emit(BackendBatch {
            events: vec![
                Event::Create(canonical.join("direct.ts")),
                Event::Change(canonical.join("nested/deep.ts")),
                Event::Rename {
                    from: canonical.join("old.ts"),
                    to: canonical.join("new.ts"),
                },
            ],
            error: None,
        });
        assert_eq!(
            receiver
                .recv_timeout(Duration::from_secs(1))
                .unwrap()
                .events,
            [
                Event::Create(canonical.join("direct.ts")),
                Event::Rename {
                    from: canonical.join("old.ts"),
                    to: canonical.join("new.ts")
                }
            ]
        );
        watch.close().unwrap();
        watch.close().unwrap();
        assert!(backend.closed());
    }

    #[test]
    fn injectable_backend_delivers_recursive_descendants_and_errors() {
        let directory = TestDirectory::new();
        let backend = FakeBackend::default();
        let (sender, receiver) = mpsc::channel();
        let mut watch = Watcher::new(backend.clone())
            .with_debounce(DebounceConfig {
                min_wait: Duration::ZERO,
                max_wait: Duration::ZERO,
            })
            .watch(&directory.0, WatchMode::Recursive, move |batch| {
                sender.send(batch).unwrap();
            })
            .unwrap();
        let canonical = fs::canonicalize(&directory.0).unwrap();
        backend.emit(BackendBatch {
            events: vec![Event::Delete(canonical.join("nested/deep.ts"))],
            error: Some(WatchError::Overflow("queue full".to_owned())),
        });
        let batch = receiver.recv_timeout(Duration::from_secs(1)).unwrap();
        assert_eq!(
            batch.events,
            [Event::Delete(canonical.join("nested/deep.ts"))]
        );
        assert_eq!(
            batch.error,
            Some(WatchError::Overflow("queue full".to_owned()))
        );
        assert_eq!(backend.registration().1, WatchMode::Recursive);
        watch.close().unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn preserves_symlink_paths_in_nonrecursive_watch_events() {
        use std::os::unix::fs::symlink;

        let directory = TestDirectory::new();
        let external = TestDirectory::new();
        let target = external.0.join("target.ts");
        fs::write(&target, "export const target = 1;\n").unwrap();
        let link = directory.0.join("linked.ts");
        symlink(&target, &link).unwrap();

        let backend = FakeBackend::default();
        let (sender, receiver) = mpsc::channel();
        let mut watch = Watcher::new(backend.clone())
            .with_debounce(DebounceConfig {
                min_wait: Duration::ZERO,
                max_wait: Duration::ZERO,
            })
            .watch(&directory.0, WatchMode::NonRecursive, move |batch| {
                sender.send(batch).unwrap();
            })
            .unwrap();

        backend.emit(BackendBatch {
            events: vec![Event::Create(link.clone())],
            error: None,
        });

        let batch = receiver.recv_timeout(Duration::from_secs(1)).unwrap();
        assert_eq!(batch.events, [Event::Create(link)]);
        watch.close().unwrap();
    }
}
