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
/// file. A config with no root files (a solution) writes no output file.
/// Two directories overlap when one holds the other. Each path is compared
/// by its key (`PathKeys`), so two names of one place through a symbolic
/// link overlap, and an area with a key that cannot be trusted overlaps
/// every other area. The areas come from the configs and the file system,
/// so they are known before a task starts, and the same in every run. A
/// task can also emit a file that is not a root file (a file that it
/// imports). With an output directory, that output is in the directory
/// too. When its outputs go next to its sources, that output goes next to
/// the imported file, and the config does not show where. So two tasks
/// whose outputs go next to their sources overlap, as they can import one
/// file and write its outputs (R149 reviewer item 2).
pub(crate) fn outputs_overlap(
    configs: &[Option<Rc<ParsedCommandLine>>],
    fs: &Rc<dyn Fs>,
    compare: &ComparePathsOptions,
) -> bool {
    let keys = PathKeys::new(fs, compare);
    let areas: Vec<Area> = configs
        .iter()
        .flatten()
        .map(|config| Area::of(config, &keys))
        .collect();
    areas_overlap(&areas)
}

/// The keys of file and directory names that `outputs_overlap` and the
/// build info prefetch (orchestrator.rs) compare. Two names of one place
/// through a symbolic link get one key. A key is None when it cannot be
/// trusted: then the name can be any file.
pub(crate) struct PathKeys<'a> {
    fs: &'a dyn Fs,
    compare: &'a ComparePathsOptions,
    /// True on the OS file system. The `Fs` trait (Go `vfs.FS`) cannot read
    /// a link or count hard links, so these are read on the OS file system
    /// only (not in tests).
    os: bool,
}

impl<'a> PathKeys<'a> {
    /// `fs` and `compare` are as in `outputs_overlap`.
    pub(crate) fn new(fs: &'a Rc<dyn Fs>, compare: &'a ComparePathsOptions) -> Self {
        PathKeys {
            fs: &**fs,
            compare,
            os: is_wrapped_os_fs(fs),
        }
    }

    /// The key of the file or directory `name`: `to_path` of its real path
    /// (`real_path`). None when `real_path` cannot trust the real path.
    pub(crate) fn key(&self, name: &str) -> Option<String> {
        let read_link: fn(&str) -> Option<String> = if self.os { os_read_link } else { |_| None };
        let path = get_normalized_absolute_path(name, &self.compare.current_directory);
        let real = real_path(self.fs, read_link, &path)?;
        Some(to_path(&real, "", self.compare.use_case_sensitive_file_names).0)
    }

    /// `key` of the build info file `name`. None also when the file exists
    /// with more than one hard link: a write to another name of it (Go
    /// writes a file in place) changes it, and that name can be any file.
    pub(crate) fn build_info_key(&self, name: &str) -> Option<String> {
        let path = get_normalized_absolute_path(name, &self.compare.current_directory);
        if self.os && os_hard_linked(&path) {
            return None;
        }
        self.key(&path)
    }
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
/// link target, as a write through the link does. None when that target
/// has a `..` after a name (`al/../x`): the path is normalized as text,
/// but when `al` is a link, the OS goes to the parent of its target. A
/// `..` at the start of the target is the parent of the real directory
/// that holds the link, as in the text. The file system must not cache
/// lookups for the build: a directory that does not exist yet is looked up
/// here.
fn real_path(fs: &dyn Fs, read_link: fn(&str) -> Option<String>, path: &str) -> Option<String> {
    let mut path = path.to_string();
    for _ in 0..=MAX_LINKS {
        let root = get_root_length(&path);
        // `path[..end]` exists, and `path[..next]` is the name after it.
        let (mut end, mut next) = (path.len(), path.len());
        while fs.stat(&path[..end]).is_none() {
            match path[..end].rfind('/') {
                Some(i) if i >= root => (end, next) = (i, end),
                _ => return Some(path),
            }
        }
        let real = fs.realpath(&path[..end]);
        if end == path.len() {
            return Some(real);
        }
        let Some(target) = read_link(&path[..next]) else {
            return Some(format!("{}{}", real.trim_end_matches('/'), &path[end..]));
        };
        let dot_dot_after_name = target
            .split('/')
            .filter(|segment| !segment.is_empty() && *segment != ".")
            .skip_while(|segment| *segment == "..")
            .any(|segment| segment == "..");
        if dot_dot_after_name {
            return None;
        }
        path = get_normalized_absolute_path(&target, &real) + &path[next..];
    }
    Some(path)
}

/// The target of the link `path` on the OS file system, or None when
/// `path` is not a link.
fn os_read_link(path: &str) -> Option<String> {
    let target = std::fs::read_link(os_path(&filepath_from_slash(path))).ok()?;
    Some(normalize_slashes(&go_string_from_os(target)))
}

/// True when `path` is a file on the OS file system with more than one hard
/// link. PORT: Rust has no stable hard link count on Windows, so this is
/// false there.
fn os_hard_linked(path: &str) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        std::fs::metadata(os_path(&filepath_from_slash(path)))
            .is_ok_and(|meta| meta.is_file() && meta.nlink() > 1)
    }
    #[cfg(not(unix))]
    {
        let _ = path;
        false
    }
}

/// The output area and the root file directories of one task, as path
/// keys (`PathKeys`). A directory key ends with '/', so a directory holds
/// each key that starts with its key. `beside_sources` is true when some
/// outputs of the task go next to its sources. `unknown` is true when a key
/// of the task cannot be trusted, so the area can hold any place.
struct Area {
    output_dirs: Vec<String>,
    build_info: Option<String>,
    root_dirs: Vec<String>,
    beside_sources: bool,
    unknown: bool,
}

impl Area {
    fn of(config: &ParsedCommandLine, keys: &PathKeys) -> Area {
        let dir_key = |dir: &str| {
            keys.key(dir).map(|mut key| {
                if !key.ends_with('/') {
                    key.push('/');
                }
                key
            })
        };
        let options = config.compiler_options();
        let root_dirs: FxHashSet<&str> = config
            .file_names()
            .iter()
            .map(|file| file.rfind('/').map_or("", |i| &file[..i]))
            .collect();
        let root_dirs: Vec<Option<String>> = root_dirs.into_iter().map(dir_key).collect();
        // A config with no root files writes no output file: a solution
        // builds nothing (Go buildtask.go:356 `upToDateStatusTypeSolution`),
        // and any other such program has no source file (TS18003).
        let emits = !options.no_emit.is_true() && !config.file_names().is_empty();
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
        let beside_sources = dirs.iter().any(|dir| dir.is_empty());
        for dir in dirs {
            if dir.is_empty() {
                // The outputs go next to the root files.
                output_dirs.extend(root_dirs.iter().cloned());
            } else {
                output_dirs.push(dir_key(dir));
            }
        }
        let build_info = config.get_build_info_file_name();
        let build_info = (!build_info.is_empty()).then(|| keys.build_info_key(&build_info));
        let unknown = output_dirs
            .iter()
            .chain(&root_dirs)
            .chain(&build_info)
            .any(Option::is_none);
        Area {
            output_dirs: output_dirs.into_iter().flatten().collect(),
            build_info: build_info.flatten(),
            root_dirs: root_dirs.into_iter().flatten().collect(),
            beside_sources,
            unknown,
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
    if areas.len() > 1 && areas.iter().any(|area| area.unknown) {
        return true;
    }
    if areas.iter().filter(|area| area.beside_sources).count() > 1 {
        return true;
    }
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
    use crate::frontend::vfs::osvfs_fs;

    fn area(output_dirs: &[&str], build_info: &str, root_dirs: &[&str]) -> Area {
        let keys = |keys: &[&str]| keys.iter().map(|key| key.to_string()).collect();
        Area {
            output_dirs: keys(output_dirs),
            build_info: (!build_info.is_empty()).then(|| build_info.to_string()),
            root_dirs: keys(root_dirs),
            beside_sources: false,
            unknown: false,
        }
    }

    /// The area of a task whose outputs go next to its sources in
    /// `root_dir`, with the build info `build_info`.
    fn beside(root_dir: &str, build_info: &str) -> Area {
        Area {
            beside_sources: true,
            ..area(&[root_dir], build_info, &[root_dir])
        }
    }

    /// The area (`Area::of`) of a solution config: no root files, project
    /// references and no outDir. It writes nothing.
    fn solution() -> Area {
        let config = new_parsed_command_line(
            Rc::new(CompilerOptions::default()),
            Vec::new(),
            Some(Vec::new()),
            ComparePathsOptions::default(),
        );
        let compare = ComparePathsOptions::default();
        Area::of(&config, &PathKeys::new(&osvfs_fs(), &compare))
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
        // another outDir, a root directory in another outDir, a shared
        // build info alone, two tasks whose outputs go next to their
        // sources in separate directories (they can import one file, as
        // the R149 reviewer's pX and pY import ../shared/u.ts), and an area
        // with a key that cannot be trusted.
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
            (
                beside("/r/pX/src/", "/r/x.tsbuildinfo"),
                beside("/r/pY/src/", "/r/y.tsbuildinfo"),
            ),
            (
                Area {
                    unknown: true,
                    ..area(&["/r/a/dist/"], "", &[])
                },
                area(&["/r/b/dist/"], "", &[]),
            ),
        ];
        for (a, b) in pairs {
            assert!(areas_overlap(&[a, b]));
        }
        // A directory whose name starts with another's name, an outDir
        // inside a root directory (the root files are only the ones there),
        // one task whose outputs go next to its sources beside one with an
        // outDir, and solutions (the R149 tscbfix1 skeptic's nested
        // solutions, and a solution beside a task whose outputs go next to
        // its sources).
        let pairs = [
            (
                area(&["/r/dist/"], "", &[]),
                area(&["/r/dist2/"], "/r/dist.tsbuildinfo", &[]),
            ),
            (area(&["/r/a/dist/"], "", &[]), area(&[], "", &["/r/a/"])),
            (
                beside("/r/pX/src/", "/r/x.tsbuildinfo"),
                area(&["/r/pY/dist/"], "/r/y.tsbuildinfo", &["/r/pY/src/"]),
            ),
            (solution(), solution()),
            (solution(), beside("/r/pX/src/", "/r/x.tsbuildinfo")),
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
    const LINKS: [(&str, &str); 8] = [
        ("lnk", "."),
        ("lnkx", "pX"),
        ("ylink.tsbuildinfo", "shared.tsbuildinfo"),
        ("pY/dl", "../pX/dist"),
        ("pY/elsewhere", "../other/dist"),
        ("loop", "loop"),
        ("al", "d1/d2"),
        ("yb.tsbuildinfo", "al/../../shared.tsbuildinfo"),
    ];

    /// Writes the projects pX and pY (with `py_options`), the directory
    /// d1/d2, the file h1.tsbuildinfo with the hard link h2.tsbuildinfo, and
    /// the links in `LINKS` in a new temporary directory. Returns whether
    /// their outputs overlap and whether the build info prefetch leaves
    /// out pY's build info (`PathKeys::build_info_key`): it has the key of
    /// pX's build info, or a key that cannot be trusted. No output is
    /// written, so the links to outputs dangle.
    #[cfg(unix)]
    fn overlap_on_disk(label: &str, py_options: &str) -> (bool, bool) {
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
        std::fs::create_dir_all(dir.join("d1/d2")).unwrap();
        std::fs::write(dir.join("h1.tsbuildinfo"), "{}").unwrap();
        std::fs::hard_link(dir.join("h1.tsbuildinfo"), dir.join("h2.tsbuildinfo")).unwrap();
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
        let keys = PathKeys::new(&sys.fs, &compare);
        let [x, y] = [0, 1]
            .map(|i| keys.build_info_key(&configs[i].as_ref().unwrap().get_build_info_file_name()));
        std::fs::remove_dir_all(&dir).unwrap();
        (overlap, x.is_none() || y.is_none() || x == y)
    }

    #[cfg(unix)]
    #[test]
    fn outputs_overlap_through_symbolic_links() {
        // The skeptic's bi2link: one build info, named through a link to
        // the root by pY. It does not exist yet. The R149 reviewer's case
        // for the build info prefetch: the two names have one key.
        assert_eq!(
            overlap_on_disk(
                "bi2link",
                r#""outDir": "dist", "tsBuildInfoFile": "../lnk/shared.tsbuildinfo""#,
            ),
            (true, true)
        );
        // The same through the link twice.
        assert_eq!(
            overlap_on_disk(
                "bi2link2",
                r#""outDir": "dist", "tsBuildInfoFile": "../lnk/lnk/shared.tsbuildinfo""#,
            ),
            (true, true)
        );
        // pY writes to pX's outDir through a link to pX.
        assert_eq!(
            overlap_on_disk(
                "outdir",
                r#""outDir": "../lnkx/dist", "tsBuildInfoFile": "../y.tsbuildinfo""#,
            ),
            (true, false)
        );
        // The int22 skeptic's dbi: pY's build info is a dangling link to
        // pX's build info.
        assert_eq!(
            overlap_on_disk(
                "dbi",
                r#""outDir": "dist", "tsBuildInfoFile": "../ylink.tsbuildinfo""#,
            ),
            (true, true)
        );
        // The int22 skeptic's dout: pY's outDir is a dangling link to pX's
        // outDir.
        assert_eq!(
            overlap_on_disk(
                "dout",
                r#""outDir": "dl", "tsBuildInfoFile": "../y.tsbuildinfo""#,
            ),
            (true, false)
        );
        // The tscbfix1 skeptic's skhard: pY's build info is a hard link to
        // another file. A write of that file changes it.
        assert_eq!(
            overlap_on_disk(
                "hard",
                r#""outDir": "dist", "tsBuildInfoFile": "../h2.tsbuildinfo""#,
            ),
            (true, true)
        );
        // The tscbfix1 skeptic's skdotdot: pY's build info is a dangling
        // link to al/../../shared.tsbuildinfo. As text that is outside the
        // root, but the OS goes from al (d1/d2) to d1 and then to the root,
        // so it is pX's build info. The key cannot be trusted.
        assert_eq!(
            overlap_on_disk(
                "dotdot",
                r#""outDir": "dist", "tsBuildInfoFile": "../yb.tsbuildinfo""#,
            ),
            (true, true)
        );
        // Separate outputs, each named through a link, do not overlap: a
        // link to the root, a dangling link to another place (its target
        // starts with `..`), and a link loop.
        assert_eq!(
            overlap_on_disk(
                "separate",
                r#""outDir": "../lnk/pY/dist", "tsBuildInfoFile": "../lnk/y.tsbuildinfo""#,
            ),
            (false, false)
        );
        assert_eq!(
            overlap_on_disk(
                "elsewhere",
                r#""outDir": "elsewhere", "tsBuildInfoFile": "../y.tsbuildinfo""#,
            ),
            (false, false)
        );
        assert_eq!(
            overlap_on_disk(
                "loop",
                r#""outDir": "../loop/dist", "tsBuildInfoFile": "../y.tsbuildinfo""#,
            ),
            (false, false)
        );
    }
}
