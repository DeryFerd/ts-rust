//! Go: internal/testutil/contentmappertest/mapper_test.go (tsgo#4712).
//!
//! PORT: Go `TestMain` turns the test binary into the mapper process when
//! `TSGO_CONTENT_MAPPER_HELPER=1`. Here the mapper process is this test
//! binary running only the test `__content_mapper_helper`. The Rust test
//! harness writes its own lines to stdout before that test starts, so the
//! helper first writes `HELPER_READY`, and the spawner drops the child's
//! output up to and including it. After that, stdout carries only the
//! mapper protocol, as in Go.

use std::io::{Read, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::rc::Rc;
use std::sync::Mutex;

use ts_goport::contentmapper::{
    Definition, Manifest, Mapper, ProcessExitState, ProjectSpec, Request,
};
use ts_goport::flags::ScriptTarget;
use ts_goport::gostd::context::background;
use ts_goport::locale;
use ts_goport::options::CompilerOptions;

use super::prelude::*;
use super::{DECLARED_OPTIONS, PACKAGE_NAME, TRANSFORMING_MAPPER, serve};

// Go: mapper_test.go:22 helperEnv
// helperEnv, when set, makes the test binary act as the mapper subprocess instead of running tests. This
// lets the out-of-process test spawn a real subprocess (itself) that speaks the mapper protocol over
// stdio, exercising the same handler code that the in-process spawner runs over a pipe.
const HELPER_ENV: &str = "TSGO_CONTENT_MAPPER_HELPER";

/// The libtest name of the helper test (`__content_mapper_helper`).
const HELPER_TEST: &str = "support::contentmappertest::mapper_test::__content_mapper_helper";

/// The line that ends the test harness output of the helper process.
const HELPER_READY: &[u8] = b"TSGO_CONTENT_MAPPER_HELPER ready\n";

// Go: mapper_test.go:24 TestMain
/// The mapper process of `test_out_of_process`. Returns at once unless
/// `TSGO_CONTENT_MAPPER_HELPER=1`.
#[test]
fn __content_mapper_helper() {
    if std::env::var(HELPER_ENV).as_deref() != Ok("1") {
        return;
    }
    {
        let mut out = std::io::stdout().lock();
        let _ = out.write_all(HELPER_READY);
        let _ = out.flush();
    }
    let _ = serve(&background(), Arc::new(StdioConn));
    std::process::exit(0);
}

// Go: mapper_test.go:32 stdio
// stdio adapts the process's stdin/stdout to an io.ReadWriteCloser for the mapper server.
// PORT: Go `os.Stdout` is not buffered, so each write is flushed.
struct StdioConn;

impl ipc::ReadWriteCloser for StdioConn {
    fn read(&self, buf: &mut [u8]) -> std::io::Result<usize> {
        std::io::stdin().lock().read(buf)
    }

    fn write(&self, buf: &[u8]) -> std::io::Result<usize> {
        let mut out = std::io::stdout().lock();
        let n = out.write(buf)?;
        out.flush()?;
        Ok(n)
    }

    fn flush(&self) -> std::io::Result<()> {
        std::io::stdout().lock().flush()
    }

    fn close(&self) -> Result<(), GoError> {
        Ok(())
    }
}

// Go: mapper_test.go:36 testMapper
fn test_mapper() -> Rc<Mapper> {
    Rc::new(Mapper {
        definition: Definition {
            package: PACKAGE_NAME.to_string(),
            extensions: vec![".box".to_string()],
            ..Definition::default()
        },
        manifest: Manifest {
            name: PACKAGE_NAME.to_string(),
            version: "1.0.0".to_string(),
            exec: vec![TRANSFORMING_MAPPER.to_string()],
            compiler_options: DECLARED_OPTIONS.iter().map(ToString::to_string).collect(),
            ..Manifest::default()
        },
        package_directory: format!("/node_modules/{PACKAGE_NAME}"),
        ..Mapper::default()
    })
}

// Go: mapper_test.go:53 transformRequest
fn transform_request() -> Request {
    Request {
        file_name: "/app.box".to_string(),
        content: "export const version = #{target};\n".to_string(),
    }
}

// Go: mapper_test.go:62 TestOutOfProcess
// TestOutOfProcess exercises the real out-of-process IPC path: it spawns the test binary as a mapper
// subprocess and drives it over stdio through the production content mapper host.
// PORT: Go `defer project.Close()` and `defer host.Close()`: both close
// before the checks, in the Go order.
#[test]
fn test_out_of_process() {
    let ctx = background();
    let host = contentmapper::new_host(&ctx, Rc::new(ExecSpawner), locale::DEFAULT);
    let mapper = test_mapper();
    let request = transform_request();
    let compiler_options = Rc::new(CompilerOptions {
        target: ScriptTarget::ES2020,
        ..CompilerOptions::default()
    });
    let project = host
        .project(ProjectSpec {
            config_file_name: "/tsconfig.json".to_string(),
            mappers: vec![mapper.clone()],
            compiler_options: Some(compiler_options),
        })
        .expect("an open host returns a project");

    let result = project.transform(&mapper, request);
    let _ = project.close();
    let _ = host.close();

    let result = match result {
        Ok(result) => result,
        Err(err) => panic!("assertion failed: error is not nil: {}", err.error()),
    };
    assert!(
        result.text.contains("export const version = 7;"),
        "got {:?}",
        result.text
    );
    assert!(result.mappings.is_some());
}

// Go: mapper_test.go:86 execSpawner
// execSpawner spawns the test binary itself as the mapper subprocess (guarded by helperEnv), so the test
// talks to a genuinely separate process over real pipes.
struct ExecSpawner;

impl contentmapper::Spawner for ExecSpawner {
    // Go: mapper_test.go:88 execSpawner.Spawn
    // PORT: Go sets `cmd.Stderr = stderr`, and os/exec copies the child's
    // stderr to it on a goroutine; here a thread copies it. `None` is Go
    // `io.Discard`.
    fn spawn(
        &self,
        _command: &[String],
        _dir: &str,
        stderr: Option<Box<dyn Write + Send>>,
    ) -> Result<Arc<dyn ProcessExitState>, GoError> {
        let exe = std::env::current_exe().map_err(|err| errors::new(err.to_string()))?;
        let mut cmd = Command::new(exe);
        cmd.args(["--exact", HELPER_TEST, "--nocapture"])
            .env(HELPER_ENV, "1")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(if stderr.is_some() {
                Stdio::piped()
            } else {
                Stdio::null()
            });
        let mut child = cmd.spawn().map_err(|err| errors::new(err.to_string()))?;
        let stdin = child.stdin.take().expect("piped stdin");
        let mut stdout = child.stdout.take().expect("piped stdout");
        if let (Some(mut writer), Some(mut child_stderr)) = (stderr, child.stderr.take()) {
            std::thread::spawn(move || {
                let _ = std::io::copy(&mut child_stderr, &mut writer);
            });
        }
        if let Err(err) = skip_harness_output(&mut stdout) {
            let _ = child.kill();
            let _ = child.wait();
            return Err(errors::new(err.to_string()));
        }
        Ok(Arc::new(Process {
            cmd: Mutex::new(Some(child)),
            stdin: Mutex::new(Some(stdin)),
            stdout: Mutex::new(stdout),
        }))
    }
}

/// Reads the child's stdout up to and including `HELPER_READY`.
fn skip_harness_output(stdout: &mut ChildStdout) -> std::io::Result<()> {
    let mut seen: Vec<u8> = Vec::new();
    let mut byte = [0u8; 1];
    while !seen.ends_with(HELPER_READY) {
        if stdout.read(&mut byte)? == 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::UnexpectedEof,
                "content mapper helper exited before it was ready",
            ));
        }
        seen.push(byte[0]);
    }
    Ok(())
}

// Go: mapper_test.go:105 process
// process adapts a spawned subprocess's stdio to an io.ReadWriteCloser: reads come from its stdout, writes
// go to its stdin, and Close tears the process down.
// PORT: the fields are behind locks because the connection shares the
// process across threads. Go closes stdin by value; here `None` is closed.
struct Process {
    cmd: Mutex<Option<Child>>,
    stdin: Mutex<Option<ChildStdin>>,
    stdout: Mutex<ChildStdout>,
}

impl ipc::ReadWriteCloser for Process {
    // Go: mapper_test.go:111 process.Read
    fn read(&self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.stdout
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .read(buf)
    }

    // Go: mapper_test.go:112 process.Write
    fn write(&self, buf: &[u8]) -> std::io::Result<usize> {
        match self
            .stdin
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .as_mut()
        {
            Some(stdin) => stdin.write(buf),
            None => Err(std::io::Error::from(std::io::ErrorKind::BrokenPipe)),
        }
    }

    fn flush(&self) -> std::io::Result<()> {
        match self
            .stdin
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .as_mut()
        {
            Some(stdin) => stdin.flush(),
            None => Ok(()),
        }
    }

    // Go: mapper_test.go:114 process.Close
    fn close(&self) -> Result<(), GoError> {
        drop(
            self.stdin
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .take(),
        );
        if let Some(mut child) = self
            .cmd
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take()
        {
            let _ = child.kill();
            let _ = child.wait();
        }
        Ok(())
    }
}

// Go `process` has no `ExitCode` method.
impl ProcessExitState for Process {}
