//! PORT: not in Go (determinism). Go builds the tasks of `tsc -b` on up to
//! `numRoutines` goroutines, and each task writes its outputs when its own
//! build ends. When two tasks that run at the same time write the same
//! file, or one writes a file that the other reads, the output depends on
//! which task ends first, so Go's output can change between runs. The port
//! makes the task programs one at a time on the orchestrator thread
//! (build_task.rs), so its task end order is not Go's. `build_all_tasks`
//! finishes the tasks in the order their checks end, except in a build
//! where `outputs_overlap` finds two tasks that can see each other's
//! writes. There every task finishes in build order, so the output is the
//! same in every run, and it is Go's output when Go's tasks end in build
//! order.
//!
//! For example, when two tasks A and B (in that order) write the same
//! `.d.ts`, and D references B while E references A: A ends first here, E
//! starts and parses A's file, and D gets that parse after B ends, because
//! the build host keeps the first parse of each `.d.ts` for the whole build
//! (Go `host.sourceFiles`). Go gives D A's file too when A ends first; when
//! B ends first, D and E both get B's file.

use crate::frontend::prelude::*;

/// True when the output area of one task of `configs` (the configs of the
/// tasks of a build; None when a config did not parse) overlaps the output
/// area or a root file directory of another. `fs` is the file system of
/// the build without its cache (`sys.FS()`), and `compare` the
/// orchestrator's path options.
///
/// The output area of a task is where it can write: its output directories
/// and everything under them (`outDir`, `declarationDir`, or the directories
/// of its root files when its outputs go next to them) and its build info
/// file. Two directories overlap when one holds the other. Each path is
/// compared by its real path (`real_path`), so two names of one place
/// through a symbolic link overlap. The areas come from the configs and the
/// links on disk, so they are known before a task starts, and the same in
/// every run. A task can also emit a file that is not a root file; when that
/// file is outside the directories above, its outputs are not in the area.
pub(crate) fn outputs_overlap(
    configs: &[Option<Rc<ParsedCommandLine>>],
    fs: &Rc<dyn Fs>,
    compare: &ComparePathsOptions,
) -> bool {
    // The `Fs` trait (Go `vfs.FS`) cannot read a link, so links are read
    // on the OS file system only (not in tests).
    let read_link: fn(&str) -> Option<String> = if is_wrapped_os_fs(fs) {
        os_read_link
    } else {
        |_| None
    };
    let key = |file: &str| {
        let path = get_normalized_absolute_path(file, &compare.current_directory);
        to_path(
            &real_path(&**fs, read_link, &path),
            "",
            compare.use_case_sensitive_file_names,
        )
        .0
    };
    let areas: Vec<Area> = configs
        .iter()
        .flatten()
        .map(|config| Area::of(config, &key))
        .collect();
    areas_overlap(&areas)
}

/// The most links that `real_path` follows through names that do not
/// exist yet (Linux MAXSYMLINKS).
const MAX_LINKS: usize = 40;

/// The real path (Go `vfs.FS.Realpath`) of the absolute path `path`, found
/// through its longest prefix that exists. So a directory or file that the
/// build has not written yet gets the place where it will be written. A
/// stat follows links, so a link to a place that does not exist yet (a
/// dangling link) is not in that prefix. When the name after the prefix is
/// such a link (`read_link` gives its target), the path goes on from the
/// link target, as a write through the link does. The file system must not
/// cache lookups for the build: a directory that does not exist yet is
/// looked up here.
fn real_path(fs: &dyn Fs, read_link: fn(&str) -> Option<String>, path: &str) -> String {
    let mut path = path.to_string();
    for _ in 0..=MAX_LINKS {
        let root = get_root_length(&path);
        // `path[..end]` exists, and `path[..next]` is the name after it.
        let (mut end, mut next) = (path.len(), path.len());
        while fs.stat(&path[..end]).is_none() {
            match path[..end].rfind('/') {
                Some(i) if i >= root => (end, next) = (i, end),
                _ => return path,
            }
        }
        let real = fs.realpath(&path[..end]);
        if end == path.len() {
            return real;
        }
        match read_link(&path[..next]) {
            Some(target) => {
                path = get_normalized_absolute_path(&target, &real) + &path[next..];
            }
            None => return format!("{}{}", real.trim_end_matches('/'), &path[end..]),
        }
    }
    path
}

/// The target of the link `path` on the OS file system, or None when
/// `path` is not a link.
fn os_read_link(path: &str) -> Option<String> {
    let target = std::fs::read_link(os_path(&filepath_from_slash(path))).ok()?;
    Some(normalize_slashes(&go_string_from_os(target)))
}

/// The output area and the root file directories of one task, as path
/// keys (`to_path` of the real path). A directory key ends with '/', so a
/// directory holds each key that starts with its key.
struct Area {
    output_dirs: Vec<String>,
    build_info: Option<String>,
    root_dirs: Vec<String>,
}

impl Area {
    /// `key` gives the path key of a file or directory name.
    fn of(config: &ParsedCommandLine, key: &impl Fn(&str) -> String) -> Area {
        let dir_key = |dir: &str| {
            let mut key = key(dir);
            if !key.ends_with('/') {
                key.push('/');
            }
            key
        };
        let options = config.compiler_options();
        let root_dirs: FxHashSet<&str> = config
            .file_names()
            .iter()
            .map(|file| file.rfind('/').map_or("", |i| &file[..i]))
            .collect();
        let root_dirs: Vec<String> = root_dirs.into_iter().map(dir_key).collect();
        let emits = !options.no_emit.is_true();
        let mut dirs: Vec<&str> = Vec::new();
        if emits && !options.emit_declaration_only.is_true() {
            dirs.push(&options.out_dir);
        }
        if emits && options.get_emit_declarations() {
            dirs.push(if options.declaration_dir.is_empty() {
                &options.out_dir
            } else {
                &options.declaration_dir
            });
        }
        let mut output_dirs = Vec::new();
        for dir in dirs {
            if dir.is_empty() {
                // The outputs go next to the root files.
                output_dirs.extend(root_dirs.iter().cloned());
            } else {
                output_dirs.push(dir_key(dir));
            }
        }
        let build_info = config.get_build_info_file_name();
        Area {
            output_dirs,
            build_info: (!build_info.is_empty()).then(|| key(&build_info)),
            root_dirs,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Kind {
    OutputDir,
    OutputFile,
    RootDir,
}

fn areas_overlap(areas: &[Area]) -> bool {
    let mut entries: Vec<(&str, Kind, usize)> = Vec::new();
    for (task, area) in areas.iter().enumerate() {
        let dirs = area.output_dirs.iter().map(|key| (key, Kind::OutputDir));
        let file = area.build_info.iter().map(|key| (key, Kind::OutputFile));
        let roots = area.root_dirs.iter().map(|key| (key, Kind::RootDir));
        entries.extend(
            dirs.chain(file)
                .chain(roots)
                .map(|(key, kind)| (key.as_str(), kind, task)),
        );
    }
    entries.sort_unstable();
    // In key order, each key comes right after the keys of the directories
    // that hold it. `open` keeps the output directories that hold the
    // current key, and `file` the last output file and its task.
    let mut open: Vec<(&str, usize)> = Vec::new();
    let mut file: Option<(&str, usize)> = None;
    for &(key, kind, task) in &entries {
        while open.last().is_some_and(|(dir, _)| !key.starts_with(dir)) {
            open.pop();
        }
        if open.iter().any(|&(_, other)| other != task) {
            return true;
        }
        match kind {
            Kind::OutputDir => open.push((key, task)),
            Kind::OutputFile => {
                if file.is_some_and(|(other_key, other)| other_key == key && other != task) {
                    return true;
                }
                file = Some((key, task));
            }
            Kind::RootDir => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(unix)]
    use crate::frontend::vfs::osvfs_fs;

    fn area(output_dirs: &[&str], build_info: &str, root_dirs: &[&str]) -> Area {
        let keys = |keys: &[&str]| keys.iter().map(|key| key.to_string()).collect();
        Area {
            output_dirs: keys(output_dirs),
            build_info: (!build_info.is_empty()).then(|| build_info.to_string()),
            root_dirs: keys(root_dirs),
        }
    }

    #[test]
    fn separate_outputs_do_not_overlap() {
        // Packages that each write to their own dist (query-chain, wide).
        let areas = [
            area(
                &["/r/a/dist/", "/r/a/dist/"],
                "/r/a/dist/tsconfig.tsbuildinfo",
                &["/r/a/src/", "/r/a/"],
            ),
            area(
                &["/r/b/dist/"],
                "/r/b/dist/tsconfig.tsbuildinfo",
                &["/r/b/src/", "/r/b/"],
            ),
            area(&[], "/r/c/tsconfig.tsbuildinfo", &["/r/c/src/"]),
        ];
        assert!(!areas_overlap(&areas));
    }

    #[test]
    fn overlaps() {
        // A shared outDir, an outDir under another one, a build info in
        // another outDir, a root directory in another outDir, and a shared
        // build info alone.
        let pairs = [
            (
                area(&["/r/shared/"], "", &[]),
                area(&["/r/shared/"], "", &[]),
            ),
            (area(&["/r/dist/"], "", &[]), area(&["/r/dist/b/"], "", &[])),
            (
                area(&["/r/dist/"], "", &[]),
                area(&[], "/r/dist/b.tsbuildinfo", &[]),
            ),
            (
                area(&["/r/gen/"], "", &[]),
                area(&[], "", &["/r/gen/types/"]),
            ),
            (
                area(&[], "/r/x.tsbuildinfo", &[]),
                area(&[], "/r/x.tsbuildinfo", &[]),
            ),
        ];
        for (a, b) in pairs {
            assert!(areas_overlap(&[a, b]));
        }
        // A directory whose name starts with another's name, and an outDir
        // inside a root directory (the root files are only the ones there).
        let pairs = [
            (
                area(&["/r/dist/"], "", &[]),
                area(&["/r/dist2/"], "/r/dist.tsbuildinfo", &[]),
            ),
            (area(&["/r/a/dist/"], "", &[]), area(&[], "", &["/r/a/"])),
        ];
        for (a, b) in pairs {
            assert!(!areas_overlap(&[a, b]));
        }
    }

    #[cfg(unix)]
    struct System {
        fs: Rc<dyn Fs>,
        current_directory: String,
    }

    #[cfg(unix)]
    impl ParseConfigHost for System {
        fn fs(&self) -> Rc<dyn Fs> {
            self.fs.clone()
        }
        fn get_current_directory(&self) -> String {
            self.current_directory.clone()
        }
    }

    /// (name, target) of each link that `overlap_on_disk` writes.
    #[cfg(unix)]
    const LINKS: [(&str, &str); 6] = [
        ("lnk", "."),
        ("lnkx", "pX"),
        ("ylink.tsbuildinfo", "shared.tsbuildinfo"),
        ("pY/dl", "../pX/dist"),
        ("pY/elsewhere", "../other/dist"),
        ("loop", "loop"),
    ];

    /// Writes the projects pX and pY (with `py_options`) and the links in
    /// `LINKS` in a new temporary directory, and returns whether their
    /// outputs overlap. No output is written, so the links to outputs
    /// dangle.
    #[cfg(unix)]
    fn overlap_on_disk(label: &str, py_options: &str) -> bool {
        let dir = std::env::temp_dir().join(format!(
            "ts_goport_shared_outputs_{label}_{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        for (project, options) in [
            (
                "pX",
                r#""outDir": "dist", "tsBuildInfoFile": "../shared.tsbuildinfo""#,
            ),
            ("pY", py_options),
        ] {
            std::fs::create_dir_all(dir.join(project).join("src")).unwrap();
            std::fs::write(dir.join(project).join("src/m.ts"), "export const m = 1;\n").unwrap();
            std::fs::write(
                dir.join(project).join("tsconfig.json"),
                format!(r#"{{ "compilerOptions": {{ "composite": true, {options} }} }}"#),
            )
            .unwrap();
        }
        for (name, target) in LINKS {
            std::os::unix::fs::symlink(target, dir.join(name)).unwrap();
        }
        let cwd = dir.to_string_lossy().replace('\\', "/");
        let sys = System {
            fs: wrap_fs(osvfs_fs()),
            current_directory: cwd.clone(),
        };
        let configs: Vec<_> = ["pX", "pY"]
            .iter()
            .map(|project| {
                let (config, errors) = get_parsed_command_line_of_config_file(
                    &format!("{cwd}/{project}/tsconfig.json"),
                    None,
                    None,
                    &sys,
                    None,
                );
                assert!(errors.is_empty());
                Some(Rc::new(config.unwrap()))
            })
            .collect();
        let compare = ComparePathsOptions {
            current_directory: cwd,
            use_case_sensitive_file_names: true,
        };
        let overlap = outputs_overlap(&configs, &sys.fs, &compare);
        std::fs::remove_dir_all(&dir).unwrap();
        overlap
    }

    #[cfg(unix)]
    #[test]
    fn outputs_overlap_through_symbolic_links() {
        // The skeptic's bi2link: one build info, named through a link to
        // the root by pY. It does not exist yet.
        assert!(overlap_on_disk(
            "bi2link",
            r#""outDir": "dist", "tsBuildInfoFile": "../lnk/shared.tsbuildinfo""#,
        ));
        // pY writes to pX's outDir through a link to pX.
        assert!(overlap_on_disk(
            "outdir",
            r#""outDir": "../lnkx/dist", "tsBuildInfoFile": "../y.tsbuildinfo""#,
        ));
        // The int22 skeptic's dbi: pY's build info is a dangling link to
        // pX's build info.
        assert!(overlap_on_disk(
            "dbi",
            r#""outDir": "dist", "tsBuildInfoFile": "../ylink.tsbuildinfo""#,
        ));
        // The int22 skeptic's dout: pY's outDir is a dangling link to pX's
        // outDir.
        assert!(overlap_on_disk(
            "dout",
            r#""outDir": "dl", "tsBuildInfoFile": "../y.tsbuildinfo""#,
        ));
        // Separate outputs, each named through a link, do not overlap: a
        // link to the root, a dangling link to another place, and a link
        // loop.
        assert!(!overlap_on_disk(
            "separate",
            r#""outDir": "../lnk/pY/dist", "tsBuildInfoFile": "../lnk/y.tsbuildinfo""#,
        ));
        assert!(!overlap_on_disk(
            "elsewhere",
            r#""outDir": "elsewhere", "tsBuildInfoFile": "../y.tsbuildinfo""#,
        ));
        assert!(!overlap_on_disk(
            "loop",
            r#""outDir": "../loop/dist", "tsBuildInfoFile": "../y.tsbuildinfo""#,
        ));
    }
}
