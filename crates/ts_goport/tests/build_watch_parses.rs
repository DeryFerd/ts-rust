//! How `tsc -b --watch` keeps the parses of a cycle, against Go.
//!
//! Go keeps each `.d.ts` and `.json` parse of a cycle in the build host
//! cache `sourceFiles` until the cycle ends (build/host.go `GetSourceFile`,
//! build/orchestrator.go `resetCaches`). A project that builds beside an
//! upstream project (no reference to it) can parse an upstream output
//! before that build writes it. Every later program of the cycle then gets
//! that parse. The `.d.ts` case is
//! `multi_program::build_watch_keeps_the_first_dts_parse_of_a_cycle`.
//!
//! Each test copies its fixture to a new directory under the system temp
//! dir and runs `tsgo` there, and `goport_watch` or `tsgo -b --watch`. A
//! passing test deletes the directory. A failing test keeps it and names it
//! in the message.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

const STALE_JSON_FIXTURE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/build_watch/stale-json"
);

#[cfg(target_os = "linux")]
const COARSE_MTIME_FIXTURE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/build_watch/coarse-mtime"
);

/// bwsig2: the `.json` half of bwsig1. `lib` is composite with
/// `resolveJsonModule` and writes `data.json` to its `outDir`. `side` has no
/// reference to `lib` but imports `lib/dist/data.json`, so it builds beside
/// `lib` and reads that file before `lib` writes it. The edit sets
/// `"newLine": "crlf"` in the base config: every project builds again, and
/// `lib` writes `data.json` with CRLF line ends. `app` references `lib`,
/// imports the same file, builds after `lib` and gets the parse that `side`
/// made: its build info keeps the LF version of `data.json`. `expected.txt`
/// (the output up to the end of the second build) and
/// `expected-app.tsbuildinfo.json` are from `tsgo-oracle-fed0bf24149f` for
/// the same steps (3 of 3 runs). At that pin only the `lib.dom.d.ts` and
/// `lib.es2022.array.d.ts` versions differ from `tsgo-oracle-673a5f17d713`
/// (16 of 16 runs): Go changed those two libs (#64604, #64536).
// PORT: no Go counterpart; the output is Go's.
#[test]
fn build_watch_keeps_the_first_json_parse_of_a_cycle() {
    let root = scratch_dir("stale-json");
    // The project is one level deeper, as in the Go runs of `expected.txt`.
    // Go 673a5f17d713 did not watch `/tmp/<dir>/project` (`CanWatchDirectory`
    // watched no directory 3 or fewer levels below `/`). Since #64366 Go
    // watches the directory of a config or program file at any depth.
    let project = root.join("work").join("project");
    copy_dir(Path::new(STALE_JSON_FIXTURE), &project);
    // The first build builds `side` and `app` with no `lib/dist/data.json`
    // (TS2307, as in Go: `side` looks it up first, and the cached lookup
    // stays for the build); the second builds them with it.
    for expect_success in [false, true] {
        let build = Command::new(env!("CARGO_BIN_EXE_tsgo"))
            .args(["-b", "tsconfig.json", "--pretty", "false"])
            .current_dir(&project)
            .output()
            .expect("run tsgo -b");
        assert_eq!(
            build.status.success(),
            expect_success,
            "tsgo -b in {}:\n{}",
            root.display(),
            String::from_utf8_lossy(&build.stdout)
        );
    }
    let out = root.join("watch.txt");
    let run = Command::new(env!("CARGO_BIN_EXE_goport_watch"))
        .arg(&out)
        .arg("tsconfig.base.json")
        .arg("edits/tsconfig.base.json")
        .args(["--", "-b", "--watch", "tsconfig.json", "--pretty", "false"])
        .current_dir(&project)
        .output()
        .expect("run goport_watch");
    assert!(
        run.status.success(),
        "goport_watch failed ({}) in {}:\n{}\n{}",
        run.status,
        root.display(),
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(
        normalize_watch_output(&read(&out)),
        read(&project.join("expected.txt")),
        "watch output against tsgo ({})",
        root.display()
    );
    assert!(
        read(&project.join("lib/dist/data.json")).contains("\r\n"),
        "lib wrote data.json with CRLF ({})",
        root.display()
    );
    assert_eq!(
        read(&project.join("app/dist/tsconfig.tsbuildinfo")),
        read(&project.join("expected-app.tsbuildinfo.json")),
        "app build info against tsgo ({})",
        root.display()
    );
    fs::remove_dir_all(&root).unwrap_or_else(|error| panic!("remove {}: {error}", root.display()));
}

/// The bwsig2 skeptic case, at Go fed0bf24149f. `lib` writes `a.d.ts` to
/// `out`, beside the project. `side` imports `out/a.d.ts` and has no
/// reference to `lib`. The steps, with the OS watcher, and the number of
/// builds that ended after each:
///
/// 1. The start: 1.
/// 2. A `side` edit: `side` builds and parses `out/a.d.ts` (`a: number`): 2.
/// 3. A `lib` edit (`a: string`): `lib` builds and writes `out/a.d.ts`: 3.
///    The write gives a watch event, so `side` builds in the next cycle
///    with the new `a.d.ts`: TS2322, 4.
/// 4. The test sets both times of each `out/*.d.ts` back to the time that
///    step 2 saw (it set them before the watch started too): no build, 4.
/// 5. A `side` edit: `side` builds: TS2322, 5.
///
/// Go watches `out` since #64366: `addProgramFileWatchDir` watches the
/// directory of a program file at any depth, with no `CanWatchDirectory`
/// check (execute/build/orchestrator.go:775-781), for each root file
/// (:712) and each file name of the build info (:752), here `out/a.d.ts`
/// of `side`. `ResolveDesiredDirs` checks the depth only for an ancestor
/// fallback (execute/watchmanager/watchmanager.go:219-222). The watch masks
/// have create and modify but not attrib (fswatch/inotify_linux.go:77-86,
/// fswatch/fanotify_linux.go:118-120). So the write starts a build, and a
/// change of both times does not: Linux reports it as `IN_ATTRIB`. A change
/// of the modification time alone is `IN_MODIFY`, and `side` builds again.
///
/// At Go 673a5f17d713 no watch covered `/tmp/<dir>/out`: `side` did not
/// build in step 3, no build started after step 4, and step 5 checked that
/// the next cycle parses a written `.d.ts` again although no event named
/// it and its time did not change (a coarse clock). That case does not
/// occur here. It still occurs when `side` is not incremental: its build
/// info has no file names (execute/incremental/snapshottobuildinfo.go:37,
/// :51), so no watch covers `out`. For that case the end of
/// `build_all_tasks` drops the kept parse of each written file
/// (`BuildHost::drop_written_watch_sources`); its test is
/// `execute::build::host::tests::a_written_file_is_parsed_again_in_the_next_cycle`.
/// `expected.txt` and the counts are from `tsgo-oracle-fed0bf24149f` in
/// place of `tsgo` for this test (3 of 3 runs).
// PORT: no Go counterpart; the output is Go's.
#[cfg(target_os = "linux")]
#[test]
fn build_watch_parses_a_written_dts_again_in_the_next_cycle() {
    use std::time::Duration;
    let root = scratch_dir("coarse-mtime");
    // As in the first test, the project is one level deeper. `lib` writes
    // to `<root>/out`, outside the project.
    let project = root.join("work").join("project");
    copy_dir(Path::new(COARSE_MTIME_FIXTURE), &project);
    let out_dir = root.join("out");
    let old = SystemTime::now() - Duration::from_secs(1000);
    let set_dts_times_back = || {
        for entry in fs::read_dir(&out_dir).expect("read out") {
            let path = entry.expect("out entry").path();
            if path.to_string_lossy().ends_with(".d.ts") {
                fs::File::options()
                    .write(true)
                    .open(&path)
                    .and_then(|file| {
                        file.set_times(fs::FileTimes::new().set_accessed(old).set_modified(old))
                    })
                    .unwrap_or_else(|error| panic!("set the time of {}: {error}", path.display()));
            }
        }
    };
    // The first build can build `side` before `lib` writes `out/a.d.ts`
    // (TS2307). The second builds each project with it.
    for _ in 0..2 {
        let build = Command::new(env!("CARGO_BIN_EXE_tsgo"))
            .args(["-b", "tsconfig.json", "--pretty", "false"])
            .env("GOPORT_LAUNCH", "0")
            .current_dir(&project)
            .output()
            .expect("run tsgo -b");
        if build.status.success() {
            break;
        }
    }
    set_dts_times_back();
    let watch = os_watch::Run::start(&project);
    watch.expect_builds(1, "the start", &root);
    let edit = |target: &str, source: &str| os_watch::replace(&root, &project, target, source);
    edit("side/index.ts", "edits/side-index-1.ts");
    watch.expect_builds(2, "the first side edit", &root);
    edit("lib/a.ts", "edits/lib-a.ts");
    watch.expect_builds(4, "the lib edit", &root);
    set_dts_times_back();
    std::thread::sleep(os_watch::QUIET);
    watch.expect_builds(4, "the time change", &root);
    edit("side/index.ts", "edits/side-index-2.ts");
    watch.expect_builds(5, "the second side edit", &root);
    let (stdout, stderr) = watch.stop();
    assert_eq!(
        normalize_watch_output(&stdout),
        read(&project.join("expected.txt")),
        "watch output against tsgo ({})",
        root.display()
    );
    assert_eq!(stderr, "", "stderr ({})", root.display());
    fs::remove_dir_all(&root).unwrap_or_else(|error| panic!("remove {}: {error}", root.display()));
}

/// A `tsgo -b --watch` run with the OS watcher, for
/// `build_watch_parses_a_written_dts_again_in_the_next_cycle`.
#[cfg(target_os = "linux")]
mod os_watch {
    use std::io::Read;
    use std::path::Path;
    use std::process::{Child, Command, Stdio};
    use std::sync::{Arc, Mutex};
    use std::thread::JoinHandle;
    use std::time::{Duration, Instant};

    /// The text that ends each watch build.
    const BUILD_END: &str = "Watching for file changes";

    /// How long one build may take.
    const BUILD_LIMIT: Duration = Duration::from_secs(180);

    /// How long the output stays the same before a build counts as done.
    pub const QUIET: Duration = Duration::from_millis(1500);

    /// The output so far, and the time of its last change.
    type Output = Arc<Mutex<(String, Instant)>>;

    /// Drop kills a run that still runs.
    pub struct Run {
        child: Child,
        stdout: Output,
        stderr: Output,
        readers: Vec<JoinHandle<()>>,
    }

    impl Run {
        pub fn start(project: &Path) -> Run {
            let mut child = Command::new(env!("CARGO_BIN_EXE_tsgo"))
                .args(["-b", "--watch", "tsconfig.json", "--pretty", "false"])
                .env("GOPORT_LAUNCH", "0")
                .current_dir(project)
                .stdin(Stdio::null())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .expect("start tsgo -b --watch");
            let stdout: Output = Arc::new(Mutex::new((String::new(), Instant::now())));
            let stderr: Output = Arc::new(Mutex::new((String::new(), Instant::now())));
            let readers = vec![
                read_into(child.stdout.take().expect("stdout"), stdout.clone()),
                read_into(child.stderr.take().expect("stderr"), stderr.clone()),
            ];
            Run {
                child,
                stdout,
                stderr,
                readers,
            }
        }

        /// Waits until `builds` builds ended, the output ends with the end
        /// of a build, and nothing more came for `QUIET`.
        pub fn settle(&self, builds: usize, root: &Path) {
            let end = Instant::now() + BUILD_LIMIT;
            loop {
                {
                    let output = self.stdout.lock().unwrap();
                    let last_line = output.0.lines().rev().find(|line| !line.trim().is_empty());
                    if output.0.matches(BUILD_END).count() >= builds
                        && last_line.is_some_and(|line| line.contains(BUILD_END))
                        && output.1.elapsed() >= QUIET
                    {
                        return;
                    }
                    assert!(
                        Instant::now() < end,
                        "build {builds} did not end ({}):\n{}",
                        root.display(),
                        output.0
                    );
                }
                std::thread::sleep(Duration::from_millis(50));
            }
        }

        /// `settle(builds)`, then checks that no more builds ended.
        pub fn expect_builds(&self, builds: usize, step: &str, root: &Path) {
            self.settle(builds, root);
            let output = self.stdout.lock().unwrap();
            assert_eq!(
                output.0.matches(BUILD_END).count(),
                builds,
                "builds after {step} ({}):\n{}",
                root.display(),
                output.0
            );
        }

        /// Kills the run and gives its whole stdout and stderr.
        pub fn stop(mut self) -> (String, String) {
            let _ = self.child.kill();
            let _ = self.child.wait();
            for reader in self.readers.drain(..) {
                reader.join().expect("reader thread");
            }
            let stdout = self.stdout.lock().unwrap().0.clone();
            let stderr = self.stderr.lock().unwrap().0.clone();
            (stdout, stderr)
        }
    }

    impl Drop for Run {
        fn drop(&mut self) {
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
    }

    /// A thread that appends what `from` gives to `into` until its end.
    fn read_into(mut from: impl Read + Send + 'static, into: Output) -> JoinHandle<()> {
        std::thread::spawn(move || {
            let mut buf = [0; 8192];
            while let Ok(n) = from.read(&mut buf) {
                if n == 0 {
                    break;
                }
                let mut output = into.lock().unwrap();
                output.0.push_str(&String::from_utf8_lossy(&buf[..n]));
                output.1 = Instant::now();
            }
        })
    }

    /// Puts the text of the project file `source` in place of `target`, as
    /// an editor saves: a new file under `root`, renamed over the target.
    pub fn replace(root: &Path, project: &Path, target: &str, source: &str) {
        let staged = root.join("edit.tmp");
        std::fs::copy(project.join(source), &staged)
            .unwrap_or_else(|error| panic!("copy {source}: {error}"));
        std::fs::rename(&staged, project.join(target))
            .unwrap_or_else(|error| panic!("rename to {target}: {error}"));
    }
}

/// A `--pretty false` watch output without the clear-screen codes, and with
/// each status time as `<time>`: `03:41:35 PM - ` becomes `<time> - `.
fn normalize_watch_output(output: &str) -> String {
    let is_time = |text: &str| {
        text.strip_suffix(" AM")
            .or_else(|| text.strip_suffix(" PM"))
            .is_some_and(|time| {
                !time.is_empty() && time.bytes().all(|b| b.is_ascii_digit() || b == b':')
            })
    };
    output
        .replace("\x1b[2J\x1b[3J\x1b[H", "")
        .split_inclusive('\n')
        .map(|line| match line.split_once(" - ") {
            Some((time, rest)) if is_time(time) => format!("<time> - {rest}"),
            _ => line.to_string(),
        })
        .collect()
}

/// A new directory under the system temp dir, as its real path: `tsgo`
/// sees the real current directory, and `goport_watch` sends its events
/// for paths under it. A Windows real path is verbatim (`\\?\C:\...`),
/// which a program does not take as a cwd, so it stays as made there.
fn scratch_dir(test: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock after 1970")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "goport-build-watch-{test}-{}-{nanos}",
        std::process::id()
    ));
    fs::create_dir(&dir).unwrap_or_else(|error| panic!("create {}: {error}", dir.display()));
    // tsc names the watched directories by the real path, so the test must
    // too: on Windows the temp dir can be a short name (`RUNNER~1`), and an
    // edit under it then reaches no watch.
    let real = fs::canonicalize(&dir).expect("canonical scratch dir");
    // On Windows the real path is verbatim (`\\?\C:\...`), which tsc does not
    // take as a cwd.
    #[cfg(windows)]
    let real = PathBuf::from(unverbatim(&real.to_string_lossy()));
    real
}

/// `text` without the Windows verbatim prefix: `\\?\C:\x` is `C:\x`, and
/// `\\?\UNC\server\share\x` is `\\server\share\x` (the root stays).
#[cfg(windows)]
fn unverbatim(text: &str) -> String {
    if let Some(unc) = text.strip_prefix("\\\\?\\UNC\\") {
        format!("\\\\{unc}")
    } else {
        text.strip_prefix("\\\\?\\").unwrap_or(text).to_owned()
    }
}

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap_or_else(|error| panic!("create {}: {error}", to.display()));
    for entry in fs::read_dir(from).expect("read fixture dir") {
        let entry = entry.expect("fixture dir entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("fixture file type").is_dir() {
            copy_dir(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target)
                .unwrap_or_else(|error| panic!("copy to {}: {error}", target.display()));
        }
    }
}

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()))
}
