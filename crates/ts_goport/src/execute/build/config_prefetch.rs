//! PORT: not in Go (perf). Go parses the configs of a build in parallel:
//! `createBuildTasks` queues the parse of each config and of its
//! references on a work group (orchestrator.go:130). Here the configs parse
//! on the orchestrator thread, because `ParsedCommandLine` is not `Send`.
//! Most of a parse is the match of the `include` specs against the file
//! system (Go `getFileNamesFromConfigSpecs`). So threads parse the configs
//! of the build ahead of the orchestrator, each on the OS file system of
//! its thread with its own caches, and keep the file names that each
//! config's specs match. The orchestrator's parse of a config takes them
//! (`BuildHost`'s `ParseConfigHost::get_file_names_from_config_specs`)
//! when it matches the same specs from the same base path with the same
//! extensions, and waits for a thread that is still matching them. The
//! file names are a function of these inputs and of the file system, and
//! the build writes nothing before its graph is made. A config that no
//! thread has started yet is the orchestrator's own: it matches the specs
//! itself and queues the references it finds.
//!
//! The orchestrator's cached file system does not get the directory
//! lookups of a match that a thread made. Go caches them for the rest of
//! the build (`cachedvfs`), but after the graph a build only lists a
//! directory again in watch mode, and a watch build takes no prefetch.

use crate::execute::build::host::TscExtendedConfigCache;
use crate::frontend::prelude::*;
use std::collections::VecDeque;
use std::sync::{Arc, Condvar, Mutex, MutexGuard, PoisonError};

/// The most threads that parse configs ahead of the orchestrator.
const MAX_CONFIG_THREADS: usize = 8;

/// What `get_file_names_from_config_specs` reads, other than the file
/// system: two matches with equal inputs give the same file names.
#[derive(Clone, PartialEq, Eq)]
struct MatchInputs {
    base_path: String,
    files: Vec<String>,
    include: Vec<String>,
    exclude: Vec<String>,
    /// `get_supported_extensions` and its `WithJsonIfResolveJsonModule`
    /// form: the only parts of the options that the match reads.
    extensions: Vec<Vec<String>>,
    extensions_with_json: Vec<Vec<String>>,
}

impl MatchInputs {
    /// The inputs of a match. `None` without options (the match panics
    /// there, and then the orchestrator's own match panics too).
    fn of(
        specs: &ConfigFileSpecs,
        base_path: &str,
        options: Option<&CompilerOptions>,
        extra_extensions: &[String],
    ) -> Option<Self> {
        let options = options?;
        let extensions = get_supported_extensions(options, extra_extensions);
        let extensions_with_json = get_supported_extensions_with_json_if_resolve_json_module(
            Some(options),
            extensions.clone(),
        );
        Some(MatchInputs {
            base_path: base_path.to_string(),
            files: specs.validated_files_spec.clone(),
            include: specs.validated_include_specs.clone(),
            exclude: specs.validated_exclude_specs.clone(),
            extensions,
            extensions_with_json,
        })
    }
}

/// The file names that a thread matched for one config.
struct MatchedFileNames {
    inputs: MatchInputs,
    file_names: Vec<String>,
    literal_file_names_len: i32,
}

enum SlotState {
    /// No thread has started the config.
    Queued,
    /// A thread parses the config.
    Running,
    /// The thread's match, `None` when the parse matched nothing (no
    /// config file, no options) or panicked.
    Done(Option<MatchedFileNames>),
    /// The orchestrator took the slot.
    Taken,
}

struct Slot {
    state: Mutex<SlotState>,
    done: Condvar,
}

struct Queue {
    /// Configs (file name and path) that no thread has taken, in the
    /// order they were found.
    pending: VecDeque<(String, Path, Arc<Slot>)>,
    closed: bool,
}

/// The parse options of the build: what `BuildHost::get_resolved_project_reference`
/// passes to `get_parsed_command_line_of_config_file_path`.
struct ParseOptions {
    compiler_options: CompilerOptions,
    command_line_raw: Option<IndexMap<String, CompilerOptionsValue>>,
    current_directory: String,
    use_case_sensitive_file_names: bool,
}

struct Shared {
    queue: Mutex<Queue>,
    ready: Condvar,
    /// Every config that was queued, by path.
    slots: Mutex<FxHashMap<Path, Arc<Slot>>>,
    options: ParseOptions,
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// The threads that parse the configs of one graph ahead of the
/// orchestrator. Dropping it closes the queue; the threads end after the
/// config they parse.
pub struct ConfigPrefetch {
    shared: Arc<Shared>,
}

impl ConfigPrefetch {
    /// Starts up to `MAX_CONFIG_THREADS` threads (at most the cores). None
    /// when no thread starts.
    pub fn start(
        compiler_options: CompilerOptions,
        command_line_raw: Option<IndexMap<String, CompilerOptionsValue>>,
        compare_paths_options: &ComparePathsOptions,
    ) -> Option<Self> {
        let shared = Arc::new(Shared {
            queue: Mutex::new(Queue {
                pending: VecDeque::new(),
                closed: false,
            }),
            ready: Condvar::new(),
            slots: Mutex::new(FxHashMap::default()),
            options: ParseOptions {
                compiler_options,
                command_line_raw,
                current_directory: compare_paths_options.current_directory.clone(),
                use_case_sensitive_file_names: compare_paths_options.use_case_sensitive_file_names,
            },
        });
        let threads = MAX_CONFIG_THREADS.min(crate::program::available_cores());
        let mut started = 0;
        for _ in 0..threads {
            let shared = shared.clone();
            // A thread that cannot start leaves its configs to the others.
            let spawned = std::thread::Builder::new()
                .name("goport-config".to_string())
                .spawn(move || run_config_thread(&shared));
            started += usize::from(spawned.is_ok());
        }
        (started > 0).then_some(ConfigPrefetch { shared })
    }

    /// Queues the parse of each config in `configs` that was not queued
    /// before.
    pub fn queue(&self, configs: &[String]) {
        queue_configs(&self.shared, configs);
    }

    /// The file names that a thread matched for the config at `path`, when
    /// its inputs equal those of the orchestrator's match (`inputs`). Waits
    /// for the thread that parses the config. A config that no thread has
    /// started becomes the orchestrator's: None, and no thread starts it.
    fn take(&self, path: &Path, inputs: &MatchInputs) -> Option<(Vec<String>, i32)> {
        let slot = lock(&self.shared.slots).get(path).cloned()?;
        let mut state = lock(&slot.state);
        loop {
            match std::mem::replace(&mut *state, SlotState::Taken) {
                SlotState::Queued | SlotState::Taken => return None,
                SlotState::Running => {
                    *state = SlotState::Running;
                    state = slot
                        .done
                        .wait(state)
                        .unwrap_or_else(PoisonError::into_inner);
                }
                SlotState::Done(matched) => {
                    let matched = matched?;
                    return (matched.inputs == *inputs)
                        .then_some((matched.file_names, matched.literal_file_names_len));
                }
            }
        }
    }

    /// Go `getFileNamesFromConfigSpecs` for the orchestrator's parse of
    /// the config `config_file_name`: the file names that a thread
    /// matched, or else its own match on `fs`.
    pub fn get_file_names_from_config_specs(
        &self,
        config_file_name: &str,
        config_file_specs: &ConfigFileSpecs,
        base_path: &str,
        options: Option<&CompilerOptions>,
        extra_extensions: &[String],
        fs: &dyn Fs,
    ) -> (Vec<String>, i32) {
        let path = to_path(
            config_file_name,
            &self.shared.options.current_directory,
            self.shared.options.use_case_sensitive_file_names,
        );
        if let Some(inputs) =
            MatchInputs::of(config_file_specs, base_path, options, extra_extensions)
            && let Some(matched) = self.take(&path, &inputs)
        {
            return matched;
        }
        get_file_names_from_config_specs(
            config_file_specs,
            base_path,
            options,
            fs,
            extra_extensions,
        )
    }
}

impl Drop for ConfigPrefetch {
    fn drop(&mut self) {
        let mut queue = lock(&self.shared.queue);
        queue.closed = true;
        queue.pending.clear();
        drop(queue);
        self.shared.ready.notify_all();
    }
}

fn queue_configs(shared: &Shared, configs: &[String]) {
    let mut added = 0;
    {
        let mut slots = lock(&shared.slots);
        let mut queue = lock(&shared.queue);
        if queue.closed {
            return;
        }
        for config in configs {
            let path = to_path(
                config,
                &shared.options.current_directory,
                shared.options.use_case_sensitive_file_names,
            );
            if slots.contains_key(&path) {
                continue;
            }
            let slot = Arc::new(Slot {
                state: Mutex::new(SlotState::Queued),
                done: Condvar::new(),
            });
            slots.insert(path.clone(), slot.clone());
            queue.pending.push_back((config.clone(), path, slot));
            added += 1;
        }
    }
    for _ in 0..added {
        shared.ready.notify_one();
    }
}

/// A config thread: parses queued configs in order until the queue
/// closes, and queues the references of each.
fn run_config_thread(shared: &Shared) {
    // Go: sys.FS() is bundled.WrapFS(osvfs.FS()), and the build host
    // caches it (`cachedvfs.From`).
    let host = ThreadConfigHost {
        fs: cachedvfs_from(crate::frontend::bundled::wrap_fs(
            crate::frontend::vfs::osvfs_fs(),
        )),
        current_directory: shared.options.current_directory.clone(),
        matched: RefCell::new(None),
    };
    let extended_config_cache = TscExtendedConfigCache::default();
    loop {
        let (config, path, slot) = {
            let mut queue = lock(&shared.queue);
            loop {
                if queue.closed {
                    return;
                }
                if let Some(next) = queue.pending.pop_front() {
                    break next;
                }
                queue = shared
                    .ready
                    .wait(queue)
                    .unwrap_or_else(PoisonError::into_inner);
            }
        };
        {
            let mut state = lock(&slot.state);
            if !matches!(*state, SlotState::Queued) {
                continue;
            }
            *state = SlotState::Running;
        }
        // A parse that panics is left to the orchestrator, which panics
        // on it too.
        let references = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            host.matched.borrow_mut().take();
            let (parsed, _) = get_parsed_command_line_of_config_file_path(
                &config,
                path.clone(),
                Some(&shared.options.compiler_options),
                shared.options.command_line_raw.as_ref(),
                &host,
                Some(&extended_config_cache),
            );
            parsed.map(|parsed| parsed.resolved_project_reference_paths().to_vec())
        }));
        let matched = match &references {
            Ok(_) => host
                .matched
                .borrow_mut()
                .take()
                .filter(|(name, _)| *name == config)
                .map(|(_, matched)| matched),
            Err(_) => None,
        };
        *lock(&slot.state) = SlotState::Done(matched);
        slot.done.notify_all();
        if let Ok(Some(references)) = references {
            queue_configs(shared, &references);
        }
    }
}

/// The parse config host of a config thread: records the match of the
/// config it parses.
struct ThreadConfigHost {
    fs: Rc<dyn Fs>,
    current_directory: String,
    /// The config name and match of the last `get_file_names_from_config_specs`.
    matched: RefCell<Option<(String, MatchedFileNames)>>,
}

impl ParseConfigHost for ThreadConfigHost {
    fn fs(&self) -> Rc<dyn Fs> {
        self.fs.clone()
    }

    fn get_current_directory(&self) -> String {
        self.current_directory.clone()
    }

    fn get_file_names_from_config_specs(
        &self,
        config_file_name: &str,
        config_file_specs: &ConfigFileSpecs,
        base_path: &str,
        options: Option<&CompilerOptions>,
        extra_extensions: &[String],
    ) -> (Vec<String>, i32) {
        let (file_names, literal_file_names_len) = get_file_names_from_config_specs(
            config_file_specs,
            base_path,
            options,
            &*self.fs,
            extra_extensions,
        );
        *self.matched.borrow_mut() =
            MatchInputs::of(config_file_specs, base_path, options, extra_extensions).map(
                |inputs| {
                    (
                        config_file_name.to_string(),
                        MatchedFileNames {
                            inputs,
                            file_names: file_names.clone(),
                            literal_file_names_len,
                        },
                    )
                },
            );
        (file_names, literal_file_names_len)
    }
}
