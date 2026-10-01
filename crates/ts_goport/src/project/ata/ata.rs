//! Go `internal/project/ata/ata.go`.
//!
//! PORT: one thread (see `project/dirty/interfaces.rs`). `sync.Once` is an
//! `OnceState` cell, `atomic.Int32` a `Cell<i32>`, and
//! `collections.SyncMap` a `RefCell` map. `TypingsInstaller` methods take
//! `&self` like the Go pointer receiver. Go `logging.Logger` parameters are
//! `&dyn logging::Logger`, so a caller can pass `&Option<Rc<dyn Logger>>`
//! or `&Option<Rc<LogTree>>` (both implement the trait, as Go's nil-safe
//! loggers do). Go `vfs.FS` parameters are `&dyn vfs::Fs`.
//!
//! PORT: Go runs each ATA request on a goroutine that blocks while npm runs.
//! The port's request is a future (the Go functions that reach npm are
//! `async fn`, and each Go blocking point is an `.await`). `run_task` polls
//! it on the dispatch thread. An executor that gives `npm_install_func`
//! (the LSP server) runs npm on a helper thread, so a slow npm does not delay
//! requests; without it (the test mock) npm runs in the first poll and the
//! whole request ends in that poll.

use crate::project::ata::prelude::*;

use crate::frontend::core_ext::TypeAcquisition;
use crate::frontend::json::{self, JsonDecoder, JsonError, UnmarshalerFrom, json_unmarshal_decode};
use crate::frontend::json_ext::{LspAny, unmarshal_struct_fields};
use crate::frontend::{module, semver, tspath, vfs};
use crate::gostd::{self, Context, GoError};
use crate::project::logging::{self, Logger as _};
use std::cell::Cell;
use std::future::{Future, poll_fn};
use std::pin::Pin;
use std::sync::Arc;
use std::sync::mpsc::{Receiver, SyncSender, TryRecvError, TrySendError};
use std::task::{Poll, Waker};
use std::time::Duration;

// Go: project/ata/ata.go:21 TypingsInfo
// PORT: the Go pointers are shared and read only, so they are `Rc`; nil is
// `None`. `UnresolvedImports *collections.Set[string]` is an
// `FxHashSet`.
#[derive(Clone, Debug, Default)]
pub struct TypingsInfo {
    pub type_acquisition: Option<Rc<TypeAcquisition>>,
    pub compiler_options: Option<Rc<CompilerOptions>>,
    pub unresolved_imports: Option<Rc<FxHashSet<String>>>,
}

impl TypingsInfo {
    // Go: project/ata/ata.go:27 Equals
    pub fn equals(&self, other: &TypingsInfo) -> bool {
        TypeAcquisition::equals(
            self.type_acquisition.as_deref(),
            other.type_acquisition.as_deref(),
        ) && self
            .compiler_options
            .as_deref()
            .unwrap_or_else(|| crate::core::go_nil_dereference())
            .get_allow_js()
            == other
                .compiler_options
                .as_deref()
                .unwrap_or_else(|| crate::core::go_nil_dereference())
                .get_allow_js()
            // Go: collections.Set.Equals (pointer equality, then nil checks,
            // then maps.Equal).
            && match (&self.unresolved_imports, &other.unresolved_imports) {
                (None, None) => true,
                (Some(a), Some(b)) => Rc::ptr_eq(a, b) || **a == **b,
                _ => false,
            }
    }
}

// Go: project/ata/ata.go:33 CachedTyping
// PORT: Go `Version *semver.Version` is never nil here (every store takes
// the address of a parsed version), so the field is the value.
#[derive(Clone, Debug)]
pub struct CachedTyping {
    pub typings_location: String,
    pub version: semver::Version,
}

// Go: project/ata/ata.go:38 TypingsInstallerOptions
#[derive(Clone, Debug, Default)]
pub struct TypingsInstallerOptions {
    pub typings_location: String,
    pub throttle_limit: i32,
}

// Go: project/ata/ata.go:43 NpmExecutor
pub trait NpmExecutor {
    // PORT: Go returns `([]byte, error)` and reads the output when the error
    // is non-nil (installWorker logs it), so the result is a pair, not a
    // `Result`. `None` is Go's nil error.
    fn npm_install(&self, cwd: &str, args: &[String]) -> (Vec<u8>, Option<GoError>);

    /// PORT: no Go counterpart. A `Send` form of `npm_install` that ATA runs
    /// on a helper thread (`TypingsInstaller::npm_install`), or `None` to run
    /// `npm_install` on the calling thread.
    fn npm_install_func(&self) -> Option<NpmInstallFunc> {
        None
    }
}

/// PORT: the `Send` form of `NpmExecutor::npm_install`.
pub type NpmInstallFunc = Arc<dyn Fn(&str, &[String]) -> (Vec<u8>, Option<GoError>) + Send + Sync>;

/// PORT: Go `sync.Once` of `TypingsInstaller.initOnce`. `Running` while the
/// first `init` waits for npm; Go blocks the other callers of `Do` until the
/// body ends, and the port's callers wait for `Done`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OnceState {
    NotStarted,
    Running,
    Done,
}

// Go: project/ata/ata.go:47 TypingsInstallerHost
// PORT: Go interfaces are structural, so every type that implements both
// traits is a host (blanket impl). `Rc<dyn TypingsInstallerHost>` upcasts to
// `Rc<dyn module::ResolutionHost>` for `module::new_resolver`.
pub trait TypingsInstallerHost: NpmExecutor + module::ResolutionHost {}

impl<T: NpmExecutor + module::ResolutionHost> TypingsInstallerHost for T {}

// Go: project/ata/ata.go:52 TypingsInstaller
// PORT: `packageNameToTypingLocation` is ranged in DiscoverTypings, so it is
// an `IndexMap` (insertion order; Go map order is random). A
// `typesRegistry` entry is `Option`: Go keeps a JSON `null` entry as a nil
// map, and DiscoverTypings tests `registryEntry != nil`. The Go
// `concurrencySemaphore chan struct{}` is the `sync_channel` pair
// (PORTING "Go runtime").
pub struct TypingsInstaller {
    pub typings_location: String,
    pub host: Rc<dyn TypingsInstallerHost>,

    pub init_once: Cell<OnceState>,

    pub package_name_to_typing_location: RefCell<IndexMap<String, Rc<CachedTyping>>>,
    pub missing_typings_set: RefCell<FxHashMap<String, bool>>,

    pub types_registry: RefCell<FxHashMap<String, Option<FxHashMap<String, String>>>>,

    pub install_run_count: Cell<i32>,
    pub concurrency_semaphore: (SyncSender<()>, Receiver<()>),
}

// Go: project/ata/ata.go:67 NewTypingsInstaller
pub fn new_typings_installer(
    options: &TypingsInstallerOptions,
    host: Rc<dyn TypingsInstallerHost>,
) -> Rc<TypingsInstaller> {
    Rc::new(TypingsInstaller {
        typings_location: options.typings_location.clone(),
        host,
        init_once: Cell::new(OnceState::NotStarted),
        package_name_to_typing_location: RefCell::new(IndexMap::default()),
        missing_typings_set: RefCell::new(FxHashMap::default()),
        types_registry: RefCell::new(FxHashMap::default()),
        install_run_count: Cell::new(0),
        concurrency_semaphore: std::sync::mpsc::sync_channel::<()>(options.throttle_limit as usize),
    })
}

// Go: project/ata/ata.go:75 ProjectID (ts#64319)
// PORT: Go `interface { fmt.Stringer }`.
pub trait ProjectID {
    fn string(&self) -> String;
}

impl TypingsInstaller {
    // Go: project/ata/ata.go:79 IsKnownTypesPackageName
    pub fn is_known_types_package_name(
        &self,
        project_id: &dyn ProjectID,
        name: &str,
        fs: &dyn vfs::Fs,
        logger: &dyn logging::Logger,
    ) -> bool {
        // We want to avoid looking this up in the registry as that is expensive. So first check that it's actually an NPM package.
        let (validation_result, _, _) = validate_package_name(name);
        if validation_result != NAME_OK {
            return false;
        }
        // Strada did this lazily - is that needed here to not waiting on and returning false on first request
        // PORT: no Go caller at pin N. Go blocks in `initOnce.Do` while an
        // ATA request runs init. That request goes on only on the dispatch
        // thread, so the port panics instead of waiting forever.
        if self.init_once.get() == OnceState::Running {
            panic!("ata: IsKnownTypesPackageName waits for an init on the dispatch thread");
        }
        block_on(self.init(&project_id.string(), fs, logger));
        self.types_registry.borrow().contains_key(name)
    }
}

// Go: project/ata/ata.go:92 tsVersionToUse
// !!! sheetal currently we use latest instead of core.VersionMajorMinor()
pub const TS_VERSION_TO_USE: &str = "latest";

// Go: project/ata/ata.go:94 TypingsInstallRequest
// PORT: Go `TypingsInfo *TypingsInfo` is never nil (the session passes the
// address of a local), so it is an `Rc`. `GetScriptKind` is a stored func.
#[derive(Clone)]
pub struct TypingsInstallRequest {
    // ts#64319. PORT: Go `ProjectID` interface value.
    pub project_id: Rc<dyn ProjectID>,
    pub typings_info: Rc<TypingsInfo>,
    pub file_names: Vec<String>,
    pub project_root_path: String,
    pub compiler_options: Option<Rc<CompilerOptions>>,
    pub current_directory: String,
    pub get_script_kind: Rc<dyn Fn(&str) -> ScriptKind>,
    pub fs: Rc<dyn vfs::Fs>,
    pub logger: Option<Rc<dyn logging::Logger>>,
}

// Go: project/ata/ata.go:106 TypingsInstallResult
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TypingsInstallResult {
    pub typings_files: Vec<String>,
    pub files_to_watch: Vec<String>,
}

impl TypingsInstaller {
    // Go: project/ata/ata.go:111 InstallTypings
    // PORT: Go also has the unexported `installTypings` on this type, so the
    // exported Go `InstallTypings` is `install_typings_exported` (PORTING
    // "Names"). Go returns `(*TypingsInstallResult, error)` with a nil
    // result on error, so the result is a `Result`. PORT: async (see the
    // file comment).
    pub async fn install_typings_exported(
        &self,
        request: &TypingsInstallRequest,
    ) -> Result<TypingsInstallResult, GoError> {
        let mut result = self.discover_and_install_typings(request).await;
        if let Ok(result) = &mut result {
            result.typings_files.sort();
            result.files_to_watch.sort();
            request.logger.log(&format!(
                "ATA:: Got install request for: {}",
                request.project_id.string()
            ));
        }
        result
    }

    // Go: project/ata/ata.go:121 discoverAndInstallTypings
    pub async fn discover_and_install_typings(
        &self,
        request: &TypingsInstallRequest,
    ) -> Result<TypingsInstallResult, GoError> {
        self.init(&request.project_id.string(), &*request.fs, &request.logger)
            .await;

        let (cached_typing_paths, new_typing_names, files_to_watch) = discover_typings(
            &*request.fs,
            &request.logger,
            &request.typings_info,
            &request.file_names,
            &request.project_root_path,
            &self.package_name_to_typing_location,
            &self.types_registry.borrow(),
        );

        let request_id = self.install_run_count.get() + 1;
        self.install_run_count.set(request_id);
        // install typings
        if !new_typing_names.is_empty() {
            let filtered_typings = self.filter_typings(&request.logger, &new_typing_names);
            if !filtered_typings.is_empty() {
                let typings_files = self
                    .install_typings(
                        request_id,
                        &cached_typing_paths,
                        &filtered_typings,
                        &request.logger,
                    )
                    .await?;
                return Ok(TypingsInstallResult {
                    typings_files,
                    files_to_watch,
                });
            }
            request.logger.log(
                "ATA:: All typings are known to be missing or invalid - no need to install more typings",
            );
        } else {
            request
                .logger
                .log("ATA:: No new typings were requested as a result of typings discovery");
        }

        Ok(TypingsInstallResult {
            typings_files: cached_typing_paths,
            files_to_watch,
        })
        // !!! sheetal events to send
        // this.event(response, "setTypings");
    }

    // Go: project/ata/ata.go:161 installTypings
    // ts#64319: no project ID or typings info parameters.
    pub async fn install_typings(
        &self,
        request_id: i32,
        currently_cached_typings: &[String],
        filtered_typings: &[String],
        logger: &dyn logging::Logger,
    ) -> Result<Vec<String>, GoError> {
        // !!! sheetal events to send
        // send progress event
        // this.sendResponse({
        // 	kind: EventBeginInstallTypes,
        // 	eventId: requestId,
        // 	typingsInstallerVersion: version,
        // 	projectName: req.projectName,
        // } as BeginInstallTypes);

        // const body: protocol.BeginInstallTypesEventBody = {
        // 	eventId: response.eventId,
        // 	packages: response.packagesToInstall,
        // };
        // const eventName: protocol.BeginInstallTypesEventName = "beginInstallTypes";
        // this.event(body, eventName);

        let mut scoped_typings: Vec<String> = vec![String::new(); filtered_typings.len()];
        for (i, package_name) in filtered_typings.iter().enumerate() {
            scoped_typings[i] = format!("@types/{package_name}@{TS_VERSION_TO_USE}"); // @tscore.VersionMajorMinor) // This is normally @tsVersionMajorMinor but for now lets use latest
        }

        let (package_names, ok) = self
            .install_worker(request_id, &scoped_typings, logger)
            .await;
        if ok {
            // PORT: Go `%v` of a slice; log text is not compared.
            logger.log(&format!("ATA:: Installed typings {package_names:?}"));
            let mut installed_typing_files: Vec<String> = Vec::new();
            let host: Rc<dyn module::ResolutionHost> = self.host.clone();
            // ts#64299
            let resolver = module::new_resolver(module::ResolverOptions {
                host: Some(host),
                compiler_options: Some(Rc::new(CompilerOptions {
                    module_resolution: ModuleResolutionKind::NODE_NEXT,
                    ..CompilerOptions::default()
                })),
                ..Default::default()
            });
            for package_name in filtered_typings {
                let typing_file = self.typing_to_file_name(&resolver, package_name);
                if typing_file.is_empty() {
                    logger.log(&format!(
                        "ATA:: Failed to find typing file for package '{package_name}'"
                    ));
                    self.missing_typings_set
                        .borrow_mut()
                        .insert(package_name.clone(), true);
                    continue;
                }

                // packageName is guaranteed to exist in typesRegistry by filterTypings
                let types_registry = self.types_registry.borrow();
                let dist_tags = types_registry.get(package_name).and_then(Option::as_ref);
                let (mut use_version, ok) = match dist_tags
                    .and_then(|d| d.get(&format!("ts{}", crate::core::version_major_minor())))
                {
                    Some(v) => (v.clone(), true),
                    None => (String::new(), false),
                };
                if !ok {
                    use_version = dist_tags
                        .and_then(|d| d.get("latest"))
                        .cloned()
                        .unwrap_or_default();
                }
                let new_version = semver::must_parse_version(&use_version);
                let new_typing = Rc::new(CachedTyping {
                    typings_location: typing_file.clone(),
                    version: new_version,
                });
                self.package_name_to_typing_location
                    .borrow_mut()
                    .insert(package_name.clone(), new_typing);
                installed_typing_files.push(typing_file);
            }
            // PORT: Go `%v` of a slice; log text is not compared.
            logger.log(&format!(
                "ATA:: Installed typing files {installed_typing_files:?}"
            ));

            let mut result = currently_cached_typings.to_vec();
            result.extend(installed_typing_files);
            return Ok(result);
        }

        // DO we really need these events
        // this.event(response, "setTypings");
        // PORT: Go `%v` of a slice; log text is not compared.
        logger.log(&format!(
            "ATA:: install request failed, marking packages as missing to prevent repeated requests: {filtered_typings:?}"
        ));
        for typing in filtered_typings {
            self.missing_typings_set
                .borrow_mut()
                .insert(typing.clone(), true);
        }

        Err(gostd::errors::new("npm install failed"))

        // !!! sheetal events to send
        // const response: EndInstallTypes = {
        // 	kind: EventEndInstallTypes,
        // 	eventId: requestId,
        // 	projectName: req.projectName,
        // 	packagesToInstall: scopedTypings,
        // 	installSuccess: ok,
        // 	typingsInstallerVersion: version,
        // };
        // this.sendResponse(response);

        // if (this.telemetryEnabled) {
        // 	const body: protocol.TypingsInstalledTelemetryEventBody = {
        // 		telemetryEventName: "typingsInstalled",
        // 		payload: {
        // 			installedPackages: response.packagesToInstall.join(","),
        // 			installSuccess: response.installSuccess,
        // 			typingsInstallerVersion: response.typingsInstallerVersion,
        // 		},
        // 	};
        // 	const eventName: protocol.TelemetryEventName = "telemetry";
        // 	this.event(body, eventName);
        // }

        // const body: protocol.EndInstallTypesEventBody = {
        // 	eventId: response.eventId,
        // 	packages: response.packagesToInstall,
        // 	success: response.installSuccess,
        // };
        // const eventName: protocol.EndInstallTypesEventName = "endInstallTypes";
        // this.event(body, eventName);
    }

    // Go: project/ata/ata.go:261 installWorker
    // ts#64319: no project ID parameter.
    pub async fn install_worker(
        &self,
        request_id: i32,
        package_names: &[String],
        logger: &dyn logging::Logger,
    ) -> (Vec<String>, bool) {
        // PORT: Go `%v` of a slice; log text is not compared.
        logger.log(&format!(
            "ATA:: #{request_id} with cwd: {} arguments: {package_names:?}",
            self.typings_location
        ));
        let ctx = gostd::context::background();
        let err = install_npm_packages_async(
            &ctx,
            package_names,
            &self.concurrency_semaphore,
            |package_names| async move {
                let mut npm_args: Vec<String> = Vec::new();
                npm_args.extend(["install".to_string(), "--ignore-scripts".to_string()]);
                npm_args.extend(package_names.iter().cloned());
                npm_args.extend([
                    "--save-dev".to_string(),
                    format!("--user-agent=\"typesInstaller/{}\"", crate::core::version()),
                ]);
                let (output, err) = self.npm_install(&self.typings_location, &npm_args).await;
                if let Some(err) = err {
                    // PORT: Go `%s` of a `[]byte`.
                    logger.log(&format!(
                        "ATA:: Output is: {}",
                        String::from_utf8_lossy(&output)
                    ));
                    return Err(err);
                }
                Ok(())
            },
        )
        .await;
        logger.log(&format!("TI:: npm install #{request_id} completed"));
        (package_names.to_vec(), err.is_ok())
    }

    /// PORT: Go `ti.host.NpmInstall(cwd, args)`. With the host's
    /// `npm_install_func`, npm runs on a helper thread and the future is
    /// ready when the thread has sent the result (Go: the goroutine blocks in
    /// `exec.Cmd.Output`). Without it, npm runs in the first poll.
    async fn npm_install(&self, cwd: &str, args: &[String]) -> (Vec<u8>, Option<GoError>) {
        let Some(npm_install) = self.host.npm_install_func() else {
            return self.host.npm_install(cwd, args);
        };
        let (cwd, args) = (cwd.to_string(), args.to_vec());
        let (tx, rx) = std::sync::mpsc::channel();
        let mut start = Some(move |waker: Waker| {
            std::thread::Builder::new()
                .name("ata-npm".to_string())
                .spawn(move || {
                    let _ = tx.send(npm_install(&cwd, &args));
                    waker.wake();
                })
                .expect("ata: failed to start the npm thread");
        });
        poll_fn(|cx| {
            if let Some(start) = start.take() {
                start(cx.waker().clone());
            }
            match rx.try_recv() {
                Ok(result) => Poll::Ready(result),
                Err(TryRecvError::Empty) => Poll::Pending,
                // The npm function panicked on the helper thread.
                Err(TryRecvError::Disconnected) => Poll::Ready((
                    Vec::new(),
                    Some(gostd::errors::new("npm install: the helper thread failed")),
                )),
            }
        })
        .await
    }
}

// Go: project/ata/ata.go:284 installNpmPackages
// PORT: the Go test entry; it runs `install_npm_packages_async` to its end
// with `install_packages` as each body.
pub fn install_npm_packages(
    ctx: &Context,
    package_names: &[String],
    concurrency_semaphore: &(SyncSender<()>, Receiver<()>),
    install_packages: &dyn Fn(&[String]) -> Result<(), GoError>,
) -> Result<(), GoError> {
    block_on(install_npm_packages_async(
        ctx,
        package_names,
        concurrency_semaphore,
        |packages| std::future::ready(install_packages(packages)),
    ))
}

// Go: project/ata/ata.go:284 installNpmPackages
// PORT: each `tg.Go` body is a future. The bodies run at the same time, each
// while it holds a semaphore slot, and the result is the first error, as
// `tg.Wait()` gives.
pub async fn install_npm_packages_async<'a, Fut>(
    ctx: &Context,
    package_names: &'a [String],
    concurrency_semaphore: &(SyncSender<()>, Receiver<()>),
    install_packages: impl Fn(&'a [String]) -> Fut,
) -> Result<(), GoError>
where
    Fut: Future<Output = Result<(), GoError>> + 'a,
{
    // Go: tg := core.NewThrottleGroup(ctx, concurrencySemaphore)
    let _ = ctx;
    let mut tg: Vec<Pin<Box<dyn Future<Output = Result<(), GoError>> + '_>>> = Vec::new();

    let mut current_command_start: usize = 0;
    let mut current_command_end: usize = 0;
    let mut current_command_size: usize = 100;

    for package_name in package_names {
        current_command_size = current_command_size + package_name.len() + 1;
        if current_command_size < 8000 {
            current_command_end += 1;
        } else {
            let packages = &package_names[current_command_start..current_command_end];
            tg.push(Box::pin(throttled(
                concurrency_semaphore,
                install_packages(packages),
            )));
            current_command_start = current_command_end;
            current_command_size = 100 + package_name.len() + 1;
            current_command_end += 1;
        }
    }

    // Handle the final batch
    if current_command_start < package_names.len() {
        let packages = &package_names[current_command_start..current_command_end];
        tg.push(Box::pin(throttled(
            concurrency_semaphore,
            install_packages(packages),
        )));
    }

    // Go: tg.Wait()
    let mut first_err: Option<GoError> = None;
    poll_fn(|cx| {
        tg.retain_mut(|body| match body.as_mut().poll(cx) {
            Poll::Ready(result) => {
                if let Err(err) = result {
                    first_err.get_or_insert(err);
                }
                false
            }
            Poll::Pending => true,
        });
        if tg.is_empty() {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    })
    .await;
    match first_err {
        Some(err) => Err(err),
        None => Ok(()),
    }
}

/// PORT: Go `ThrottleGroup.Go` takes a semaphore slot before the body
/// starts and frees it when the body ends. A full semaphore (npm calls of
/// other ATA requests) waits.
async fn throttled<T>(
    semaphore: &(SyncSender<()>, Receiver<()>),
    body: impl Future<Output = T>,
) -> T {
    poll_fn(|_| match semaphore.0.try_send(()) {
        Ok(()) => Poll::Ready(()),
        Err(TrySendError::Full(())) => Poll::Pending,
        Err(TrySendError::Disconnected(())) => panic!("ata: semaphore closed"),
    })
    .await;
    let result = body.await;
    let _ = semaphore.1.try_recv();
    result
}

/// PORT: how often `run_task` polls a waiting ATA request.
const POLL_INTERVAL: Duration = Duration::from_millis(10);

/// PORT: runs `task`, the rest of an ATA goroutine, on the dispatch thread.
/// It polls `task` now and, while `task` waits (for npm on a helper thread,
/// a semaphore slot or another request's `init`), again every
/// `POLL_INTERVAL` in a `gostd::local::after_func` timer: a timer is the
/// only wake-up of the dispatch thread. A `background::TaskHold` moved into
/// `task` keeps the background task running until `task` ends. A later poll
/// runs under `core::go_wait_group_task`, as the queue runs the task.
pub fn run_task(mut task: Pin<Box<dyn Future<Output = ()>>>) {
    let mut cx = std::task::Context::from_waker(Waker::noop());
    if task.as_mut().poll(&mut cx).is_ready() {
        return;
    }
    let mut task = Some(task);
    gostd::local::after_func(
        POLL_INTERVAL,
        Box::new(move || {
            if let Some(task) = task.take() {
                crate::core::go_wait_group_task(|| run_task(task));
            }
        }),
    );
}

/// PORT: runs `fut` to its end on this thread, for a Go caller that blocks
/// (`IsKnownTypesPackageName`, the test entry `install_npm_packages`). It
/// parks until the helper thread of an npm call wakes it.
pub fn block_on<T>(fut: impl Future<Output = T>) -> T {
    struct Unpark(std::thread::Thread);
    impl std::task::Wake for Unpark {
        fn wake(self: Arc<Self>) {
            self.0.unpark();
        }
    }
    let waker = Waker::from(Arc::new(Unpark(std::thread::current())));
    let mut cx = std::task::Context::from_waker(&waker);
    let mut fut = std::pin::pin!(fut);
    loop {
        if let Poll::Ready(value) = fut.as_mut().poll(&mut cx) {
            return value;
        }
        std::thread::park();
    }
}

impl TypingsInstaller {
    // Go: project/ata/ata.go:322 filterTypings
    // ts#64319: no project ID parameter.
    pub fn filter_typings(
        &self,
        logger: &dyn logging::Logger,
        typings_to_install: &[String],
    ) -> Vec<String> {
        let mut result: Vec<String> = Vec::new();
        for typing in typings_to_install {
            let typing_key = module::mangle_scoped_package_name(typing);
            if self.missing_typings_set.borrow().contains_key(&typing_key) {
                logger.log(&format!(
                    "ATA:: '{typing}':: '{typing_key}' is in missingTypingsSet - skipping..."
                ));
                continue;
            }
            let (validation_result, name, is_scope_name) = validate_package_name(typing);
            if validation_result != NAME_OK {
                // add typing name to missing set so we won't process it again
                self.missing_typings_set
                    .borrow_mut()
                    .insert(typing_key.clone(), true);
                logger.log(&format!(
                    "ATA:: {}",
                    render_package_name_validation_failure(
                        typing,
                        validation_result,
                        &name,
                        is_scope_name
                    )
                ));
                continue;
            }
            let types_registry = self.types_registry.borrow();
            let Some(types_registry_entry) = types_registry.get(&typing_key) else {
                logger.log(&format!(
                    "ATA:: '{typing}':: Entry for package '{typing_key}' does not exist in local types registry - skipping..."
                ));
                continue;
            };
            let typing_location = self
                .package_name_to_typing_location
                .borrow()
                .get(&typing_key)
                .cloned();
            if let Some(typing_location) = typing_location
                && is_typing_up_to_date(&typing_location, types_registry_entry.as_ref())
            {
                logger.log(&format!(
                    "ATA:: '{typing}':: '{typing_key}' already has an up-to-date typing - skipping..."
                ));
                continue;
            }
            result.push(typing_key);
        }
        result
    }

    // Go: project/ata/ata.go:354 init
    // PORT: `initOnce.Do` is the `OnceState` cell. A caller that comes while
    // another request's body waits for npm waits until it is `Done`, as Go's
    // `Do` blocks. The body sets `Done` when it ends, also on a panic (Go
    // marks the Once done even if the body panics).
    pub async fn init(&self, project_id: &str, fs: &dyn vfs::Fs, logger: &dyn logging::Logger) {
        match self.init_once.get() {
            OnceState::Done => return,
            OnceState::Running => {
                poll_fn(|_| match self.init_once.get() {
                    OnceState::Done => Poll::Ready(()),
                    _ => Poll::Pending,
                })
                .await;
                return;
            }
            OnceState::NotStarted => {}
        }
        self.init_once.set(OnceState::Running);
        struct SetDone<'a>(&'a Cell<OnceState>);
        impl Drop for SetDone<'_> {
            fn drop(&mut self) {
                self.0.set(OnceState::Done);
            }
        }
        let _done = SetDone(&self.init_once);

        logger.log(&format!(
            "ATA:: Global cache location '{}'",
            self.typings_location
        )); //, safe file path '" + safeListPath + "', types map path '" + typesMapLocation + "`")
        self.process_cache_location(project_id, fs, logger);

        // !!! sheetal handle npm path here if we would support it
        //     // If the NPM path contains spaces and isn't wrapped in quotes, do so.
        //     if (this.npmPath.includes(" ") && this.npmPath[0] !== `"`) {
        //         this.npmPath = `"${this.npmPath}"`;
        //     }
        //     if (this.log.isEnabled()) {
        //         this.log.writeLine(`Process id: ${process.pid}`);
        //         this.log.writeLine(`NPM location: ${this.npmPath} (explicit '${ts.server.Arguments.NpmLocation}' ${npmLocation === undefined ? "not " : ""} provided)`);
        //         this.log.writeLine(`validateDefaultNpmLocation: ${validateDefaultNpmLocation}`);
        //     }

        self.ensure_typings_location_exists(fs, logger);
        logger.log("ATA:: Updating types-registry@latest npm package...");
        let (_, err) = self
            .npm_install(
                &self.typings_location,
                &[
                    "install".to_string(),
                    "--ignore-scripts".to_string(),
                    "types-registry@latest".to_string(),
                ],
            )
            .await;
        match err {
            None => {
                logger.log("ATA:: Updated types-registry npm package");
            }
            Some(err) => {
                logger.log(&format!(
                    "ATA:: Error updating types-registry package: {err}"
                ));
                // !!! sheetal events to send
                //         // store error info to report it later when it is known that server is already listening to events from typings installer
                //         this.delayedInitializationError = {
                //             kind: "event::initializationFailed",
                //             message: (e as Error).message,
                //             stack: (e as Error).stack,
                //         };

                // const body: protocol.TypesInstallerInitializationFailedEventBody = {
                // 	message: response.message,
                // };
                // const eventName: protocol.TypesInstallerInitializationFailedEventName = "typesInstallerInitializationFailed";
                // this.event(body, eventName);
            }
        }

        let types_registry = self.load_types_registry_file(fs, logger);
        *self.types_registry.borrow_mut() = types_registry;
    }
}

// Go: project/ata/ata.go:395 npmConfig
// PORT: Go `map[string]any` is `IndexMap<String, LspAny>` (PORTING "JSON");
// nil is `None`. processCacheLocation ranges over it: insertion order, where
// Go map order is random.
#[derive(Clone, Debug, Default)]
pub struct NpmConfig {
    pub dev_dependencies: Option<IndexMap<String, LspAny>>,
}

// Go: project/ata/ata.go:399 npmDependecyEntry
#[derive(Clone, Debug, Default)]
pub struct NpmDependecyEntry {
    pub version: String,
}

// Go: project/ata/ata.go:402 npmLock
// PORT: nil maps are `None` (processCacheLocation tests them for nil).
#[derive(Clone, Debug, Default)]
pub struct NpmLock {
    pub dependencies: Option<FxHashMap<String, NpmDependecyEntry>>,
    pub packages: Option<FxHashMap<String, NpmDependecyEntry>>,
}

// PORT: Go decodes npmConfig, npmDependecyEntry and npmLock by reflection
// with the JSON v2 default struct rules (PORTING "JSON"): input names match
// exactly, unknown names are skipped, `null` sets the zero value. The Go
// `map[string]map[string]string` (types registry) uses the generic
// `FxHashMap<String, V>` and `Option<T>` impls in `frontend/json.rs` and
// `frontend/json_ext.rs`, so it has no impl here.
impl UnmarshalerFrom for NpmConfig {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let is_object = unmarshal_struct_fields(dec, "ata.npmConfig", |name, dec| {
            match name {
                "devDependencies" => json_unmarshal_decode(dec, &mut self.dev_dependencies)?,
                _ => return Ok(false),
            }
            Ok(true)
        })?;
        if !is_object {
            *self = NpmConfig::default();
        }
        Ok(())
    }
}

impl UnmarshalerFrom for NpmDependecyEntry {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let is_object = unmarshal_struct_fields(dec, "ata.npmDependecyEntry", |name, dec| {
            match name {
                "version" => json_unmarshal_decode(dec, &mut self.version)?,
                _ => return Ok(false),
            }
            Ok(true)
        })?;
        if !is_object {
            *self = NpmDependecyEntry::default();
        }
        Ok(())
    }
}

impl UnmarshalerFrom for NpmLock {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let is_object = unmarshal_struct_fields(dec, "ata.npmLock", |name, dec| {
            match name {
                "dependencies" => json_unmarshal_decode(dec, &mut self.dependencies)?,
                "packages" => json_unmarshal_decode(dec, &mut self.packages)?,
                _ => return Ok(false),
            }
            Ok(true)
        })?;
        if !is_object {
            *self = NpmLock::default();
        }
        Ok(())
    }
}

impl TypingsInstaller {
    // Go: project/ata/ata.go:407 processCacheLocation
    pub fn process_cache_location(
        &self,
        project_id: &str,
        fs: &dyn vfs::Fs,
        logger: &dyn logging::Logger,
    ) {
        // Go does not read `projectID`.
        let _ = project_id;
        logger.log(&format!(
            "ATA:: Processing cache location {}",
            self.typings_location
        ));
        let package_json = tspath::combine_paths(&self.typings_location, &["package.json"]);
        let package_lock_json =
            tspath::combine_paths(&self.typings_location, &["package-lock.json"]);
        logger.log(&format!("ATA:: Trying to find '{package_json}'..."));
        if fs.file_exists(&package_json) && fs.file_exists(&package_lock_json) {
            let mut npm_config = NpmConfig::default();
            let npm_config_contents =
                parse_npm_config_or_lock(fs, logger, &package_json, &mut npm_config);
            let mut npm_lock = NpmLock::default();
            let npm_lock_contents =
                parse_npm_config_or_lock(fs, logger, &package_lock_json, &mut npm_lock);

            logger.log(&format!(
                "ATA:: Loaded content of {package_json}: {npm_config_contents}"
            ));
            logger.log(&format!(
                "ATA:: Loaded content of {package_lock_json}: {npm_lock_contents}"
            ));

            // !!! sheetal strada uses Node10
            let host: Rc<dyn module::ResolutionHost> = self.host.clone();
            // ts#64299
            let resolver = module::new_resolver(module::ResolverOptions {
                host: Some(host),
                compiler_options: Some(Rc::new(CompilerOptions {
                    module_resolution: ModuleResolutionKind::NODE_NEXT,
                    ..CompilerOptions::default()
                })),
                ..Default::default()
            });
            if let Some(dev_dependencies) = &npm_config.dev_dependencies
                && (npm_lock.packages.is_some() || npm_lock.dependencies.is_some())
            {
                for key in dev_dependencies.keys() {
                    let mut npm_lock_value = npm_lock
                        .packages
                        .as_ref()
                        .and_then(|packages| packages.get(&format!("node_modules/{key}")));
                    if npm_lock_value.is_none() {
                        npm_lock_value = npm_lock
                            .dependencies
                            .as_ref()
                            .and_then(|dependencies| dependencies.get(key));
                    }
                    let Some(npm_lock_value) = npm_lock_value else {
                        // if package in package.json but not package-lock.json, skip adding to cache so it is reinstalled on next use
                        continue;
                    };
                    // key is @types/<package name>
                    let package_name = tspath::get_base_file_name(key);
                    if package_name.is_empty() {
                        continue;
                    }
                    let typing_file = self.typing_to_file_name(&resolver, &package_name);
                    if typing_file.is_empty() {
                        self.missing_typings_set
                            .borrow_mut()
                            .insert(package_name, true);
                        continue;
                    }
                    let existing_typing_file = self
                        .package_name_to_typing_location
                        .borrow()
                        .get(&package_name)
                        .cloned();
                    if let Some(existing_typing_file) = existing_typing_file {
                        if existing_typing_file.typings_location == typing_file {
                            continue;
                        }
                        logger.log(&format!(
                            "ATA:: New typing for package {package_name} from {typing_file} conflicts with existing typing file {}",
                            existing_typing_file.typings_location
                        ));
                    }
                    logger.log(&format!(
                        "ATA:: Adding entry into typings cache: {package_name} => {typing_file}"
                    ));
                    let version = &npm_lock_value.version;
                    if version.is_empty() {
                        continue;
                    }
                    let new_version = semver::must_parse_version(version);
                    let new_typing = Rc::new(CachedTyping {
                        typings_location: typing_file,
                        version: new_version,
                    });
                    self.package_name_to_typing_location
                        .borrow_mut()
                        .insert(package_name, new_typing);
                }
            }
        }
        logger.log(&format!(
            "ATA:: Finished processing cache location {}",
            self.typings_location
        ));
    }
}

// Go: project/ata/ata.go:466 parseNpmConfigOrLock
// PORT: Go `[T npmConfig | npmLock]` is any `UnmarshalerFrom`. Like Go, a
// read or decode error is ignored and a partly decoded `config` is kept.
pub fn parse_npm_config_or_lock<T: UnmarshalerFrom>(
    fs: &dyn vfs::Fs,
    logger: &dyn logging::Logger,
    location: &str,
    config: &mut T,
) -> String {
    // Go does not read `logger`.
    let _ = logger;
    let (contents, _) = fs.read_file(location);
    let _ = json::json_unmarshal(contents.as_bytes(), config, &[]);
    contents
}

impl TypingsInstaller {
    // Go: project/ata/ata.go:472 ensureTypingsLocationExists
    pub fn ensure_typings_location_exists(&self, fs: &dyn vfs::Fs, logger: &dyn logging::Logger) {
        let npm_config_path = tspath::combine_paths(&self.typings_location, &["package.json"]);
        logger.log(&format!("ATA:: Npm config file: {npm_config_path}"));

        if !fs.file_exists(&npm_config_path) {
            logger.log(&format!(
                "ATA:: Npm config file: '{npm_config_path}' is missing, creating new one..."
            ));
            let err = fs.write_file(&npm_config_path, "{ \"private\": true }");
            if let Err(err) = err {
                logger.log(&format!(
                    "ATA:: Npm config file write failed: {}",
                    crate::execute::incremental::emit_files::fs_error_text(&err)
                ));
            }
        }
    }

    // Go: project/ata/ata.go:485 typingToFileName (ts#64299: `*module.DefaultResolver`)
    pub fn typing_to_file_name(
        &self,
        resolver: &module::DefaultResolver,
        package_name: &str,
    ) -> String {
        let (result, _, _) = resolver.resolve_module_name(
            package_name,
            &tspath::combine_paths(&self.typings_location, &["index.d.ts"]),
            ModuleKind::NONE,
            None,
        );
        result.resolved_file_name.clone()
    }

    // Go: project/ata/ata.go:490 loadTypesRegistryFile
    pub fn load_types_registry_file(
        &self,
        fs: &dyn vfs::Fs,
        logger: &dyn logging::Logger,
    ) -> FxHashMap<String, Option<FxHashMap<String, String>>> {
        let types_registry_file = tspath::combine_paths(
            &self.typings_location,
            &["node_modules/types-registry/index.json"],
        );
        let (types_registry_file_contents, ok) = fs.read_file(&types_registry_file);
        if ok {
            // PORT: nil maps are `None` at each level that Go can test for
            // nil (see `TypingsInstaller.types_registry`). A nil
            // `entries["entries"]` reads like an empty map.
            let mut entries: FxHashMap<
                String,
                Option<FxHashMap<String, Option<FxHashMap<String, String>>>>,
            > = FxHashMap::default();
            let err =
                json::json_unmarshal(types_registry_file_contents.as_bytes(), &mut entries, &[]);
            if err.is_ok()
                && let Some(types_registry) = entries.remove("entries")
            {
                return types_registry.unwrap_or_default();
            }
            // PORT: Go `%v` of a nil error prints `<nil>`.
            let err_text = match &err {
                Ok(()) => "<nil>".to_string(),
                Err(err) => err.to_string(),
            };
            logger.log(&format!(
                "ATA:: Error when loading types registry file '{types_registry_file}': {err_text}"
            ));
        } else {
            logger.log(&format!(
                "ATA:: Error reading types registry file '{types_registry_file}'"
            ));
        }
        FxHashMap::default()
    }
}

#[cfg(test)]
mod npm_thread_tests {
    use super::*;
    use std::sync::{Condvar, Mutex};

    /// An ATA host whose npm runs on a helper thread and waits for `open`.
    struct GatedNpm {
        fs: Rc<dyn vfs::Fs>,
        cwd: String,
        calls: Arc<Mutex<Vec<String>>>,
        gate: Arc<(Mutex<bool>, Condvar)>,
    }

    impl NpmExecutor for GatedNpm {
        fn npm_install(&self, _cwd: &str, _args: &[String]) -> (Vec<u8>, Option<GoError>) {
            panic!("npm ran on the dispatch thread");
        }

        fn npm_install_func(&self) -> Option<NpmInstallFunc> {
            let (calls, gate) = (self.calls.clone(), self.gate.clone());
            Some(Arc::new(move |cwd: &str, args: &[String]| {
                calls.lock().unwrap().push(args.join(" "));
                let (open, cond) = &*gate;
                drop(
                    cond.wait_while(open.lock().unwrap(), |open| !*open)
                        .unwrap(),
                );
                let dir = std::path::Path::new(cwd).join("node_modules/types-registry");
                std::fs::create_dir_all(&dir).unwrap();
                std::fs::write(dir.join("index.json"), r#"{"entries":{"left-pad":{}}}"#).unwrap();
                (Vec::new(), None)
            }))
        }
    }

    impl module::ResolutionHost for GatedNpm {
        fn fs(&self) -> &dyn vfs::Fs {
            &*self.fs
        }
        fn get_current_directory(&self) -> &str {
            &self.cwd
        }
    }

    /// Go runs ATA requests on goroutines, and `initOnce.Do` blocks a second
    /// request until the first one's npm call ends. The port's requests wait
    /// for npm without blocking the thread, and npm runs once.
    #[test]
    fn second_request_waits_for_init_off_thread() {
        let dir = std::env::temp_dir().join(format!("goport-ata-{}", std::process::id()));
        let cwd = dir.to_string_lossy().replace('\\', "/");
        let host = Rc::new(GatedNpm {
            fs: vfs::osvfs::osvfs_fs(),
            cwd: cwd.clone(),
            calls: Arc::default(),
            gate: Arc::default(),
        });
        let ti = new_typings_installer(
            &TypingsInstallerOptions {
                typings_location: format!("{cwd}/cache"),
                throttle_limit: 5,
            },
            host.clone(),
        );
        let done = Rc::new(Cell::new(0));
        for _ in 0..2 {
            let (ti, fs, done) = (ti.clone(), host.fs.clone(), done.clone());
            run_task(Box::pin(async move {
                ti.init("p", &*fs, &None::<Rc<dyn logging::Logger>>).await;
                assert_eq!(ti.init_once.get(), OnceState::Done);
                done.set(done.get() + 1);
            }));
        }
        assert_eq!((done.get(), ti.init_once.get()), (0, OnceState::Running));

        let (open, cond) = &*host.gate;
        *open.lock().unwrap() = true;
        cond.notify_all();
        while done.get() < 2 && gostd::local::wait_pending() {
            gostd::local::run_pending();
        }
        assert_eq!(done.get(), 2);
        assert_eq!(
            *host.calls.lock().unwrap(),
            ["install --ignore-scripts types-registry@latest"]
        );
        assert!(ti.types_registry.borrow().contains_key("left-pad"));
        let _ = std::fs::remove_dir_all(&dir);
    }
}
