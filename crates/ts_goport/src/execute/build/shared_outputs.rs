//! PORT: not in Go (determinism). Go builds the tasks of `tsc -b` on up to
//! `numRoutines` goroutines, and each task writes its outputs when its own
//! build ends. When two tasks that run at the same time write the same
//! file, or one writes a file that the other reads, the output depends on
//! which task ends first, so Go's output can change between runs. The port
//! makes the task programs one at a time on the orchestrator thread
//! (build_task.rs), so its task end order is not Go's. `build_all_tasks`
//! finishes most tasks in the order their checks end. `SharedOutputs`
//! finds the tasks where that order can change what a task writes or
//! reads. These tasks finish in build order, so the output is the same in
//! every run, and it is Go's output when Go's tasks end in build order.
//!
//! For example, when two tasks A and B (in that order) write the same
//! `.d.ts`, and D references B while E references A: A ends first here, E
//! starts and parses A's file, and D gets that parse after B ends, because
//! the build host keeps the first parse of each `.d.ts` for the whole build
//! (Go `host.sourceFiles`). Go gives D A's file too when A ends first; when
//! B ends first, D and E both get B's file.

use crate::frontend::prelude::*;

/// The tasks of one `build_all_tasks` call (by build order index) that can
/// see the writes of a task that runs at the same time.
///
/// The output area of a task is where it can write: its output directories
/// and everything under them (`outDir`, `declarationDir`, or the directories
/// of its root files when its outputs go next to them) and its build info
/// file. Two output areas overlap when one holds the other. The areas come
/// from the configs, so they are known before a task starts, and the same in
/// every run. A task can also emit a file that is not a root file; when that
/// file is outside the directories above, its outputs are not in the area.
pub(crate) struct SharedOutputs {
    /// A task whose output area overlaps the output area or a root file
    /// directory of another task, and each task downstream of such a task.
    /// A bound task is taken where it would be if all tasks finished in
    /// build order.
    pub bound: Vec<bool>,
    /// A task that finishes only in build order: a bound task, or a task
    /// with a bound downstream task (its finish starts that task).
    pub ordered: Vec<bool>,
}

/// The output area and the root file directories of one task, as path
/// keys (`to_path`). A directory key ends with '/', so a directory holds
/// each key that starts with its key.
#[derive(Default)]
struct Area {
    output_dirs: Vec<String>,
    build_info: Option<String>,
    root_dirs: Vec<String>,
}

impl Area {
    fn of(config: &ParsedCommandLine, to_path: &impl Fn(&str) -> Path) -> Area {
        let dir_key = |dir: &str| {
            let mut key = to_path(dir).0;
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
            build_info: (!build_info.is_empty()).then(|| to_path(&build_info).0),
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

impl SharedOutputs {
    /// `configs[i]` is the config of task `i` (None when it did not parse),
    /// and `upstream[i]` its upstream tasks in this build. The build order
    /// puts upstream tasks first. `to_path` is the orchestrator's `to_path`.
    pub fn new(
        configs: &[Option<Rc<ParsedCommandLine>>],
        upstream: &[Vec<usize>],
        to_path: impl Fn(&str) -> Path,
    ) -> Self {
        let areas: Vec<Area> = configs
            .iter()
            .map(|config| {
                config
                    .as_ref()
                    .map_or_else(Area::default, |config| Area::of(config, &to_path))
            })
            .collect();
        Self::of_areas(&areas, upstream)
    }

    fn of_areas(areas: &[Area], upstream: &[Vec<usize>]) -> Self {
        let n = areas.len();
        let mut entries: Vec<(&str, Kind, usize)> = Vec::new();
        for (task, area) in areas.iter().enumerate() {
            entries.extend(
                area.output_dirs
                    .iter()
                    .map(|key| (key.as_str(), Kind::OutputDir, task)),
            );
            entries.extend(
                area.build_info
                    .iter()
                    .map(|key| (key.as_str(), Kind::OutputFile, task)),
            );
            entries.extend(
                area.root_dirs
                    .iter()
                    .map(|key| (key.as_str(), Kind::RootDir, task)),
            );
        }
        entries.sort_unstable();
        entries.dedup();

        // In key order, each key comes right after the keys of the
        // directories that hold it. `open` keeps the output directories that
        // hold the current key, and `files` the tasks of the current output
        // file.
        let mut bound = vec![false; n];
        let mut open: Vec<(&str, usize)> = Vec::new();
        let mut files: (&str, Vec<usize>) = ("", Vec::new());
        for &(key, kind, task) in &entries {
            while open.last().is_some_and(|(dir, _)| !key.starts_with(dir)) {
                open.pop();
            }
            let mut others: Vec<usize> = open.iter().map(|&(_, other)| other).collect();
            if kind == Kind::OutputFile {
                if files.0 != key {
                    files = (key, Vec::new());
                }
                others.extend(&files.1);
                files.1.push(task);
            }
            if others.iter().any(|&other| other != task) {
                bound[task] = true;
                for other in others {
                    bound[other] = true;
                }
            }
            if kind == Kind::OutputDir {
                open.push((key, task));
            }
        }

        // A downstream task reads the outputs of its upstream tasks.
        for task in 0..n {
            if upstream[task].iter().any(|&up| bound[up]) {
                bound[task] = true;
            }
        }
        let mut ordered = bound.clone();
        for task in (0..n).filter(|&task| bound[task]) {
            for &up in &upstream[task] {
                ordered[up] = true;
            }
        }
        SharedOutputs { bound, ordered }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn area(output_dirs: &[&str], build_info: &str, root_dirs: &[&str]) -> Area {
        let keys = |keys: &[&str]| keys.iter().map(|key| key.to_string()).collect();
        Area {
            output_dirs: keys(output_dirs),
            build_info: (!build_info.is_empty()).then(|| build_info.to_string()),
            root_dirs: keys(root_dirs),
        }
    }

    #[test]
    fn separate_outputs_are_free() {
        // Two packages and one that references both (query-chain).
        let areas = [
            area(
                &["/r/a/dist/"],
                "/r/a/dist/tsconfig.tsbuildinfo",
                &["/r/a/src/", "/r/a/"],
            ),
            area(
                &["/r/b/dist/"],
                "/r/b/dist/tsconfig.tsbuildinfo",
                &["/r/b/src/", "/r/b/"],
            ),
            area(
                &["/r/c/dist/"],
                "/r/c/dist/tsconfig.tsbuildinfo",
                &["/r/c/src/"],
            ),
        ];
        let shared = SharedOutputs::of_areas(&areas, &[vec![], vec![], vec![0, 1]]);
        assert_eq!(shared.bound, [false; 3]);
        assert_eq!(shared.ordered, [false; 3]);
    }

    #[test]
    fn shared_outputs_are_bound() {
        // A and B share an outDir and a build info (the skeptic's dep
        // shape). D references B and E references A. F is apart, G
        // references F, and H, which also references F, writes in the
        // shared outDir.
        let shared_dir = "/r/shared/";
        let areas = [
            area(&[shared_dir], "/r/shared.tsbuildinfo", &["/r/pA/src/"]),
            area(
                &[shared_dir, shared_dir],
                "/r/shared.tsbuildinfo",
                &["/r/pB/src/"],
            ),
            area(
                &["/r/pD/dist/"],
                "/r/pD/dist/tsconfig.tsbuildinfo",
                &["/r/pD/src/"],
            ),
            area(
                &["/r/pE/dist/"],
                "/r/pE/dist/tsconfig.tsbuildinfo",
                &["/r/pE/src/"],
            ),
            area(
                &["/r/pF/dist/"],
                "/r/pF/dist/tsconfig.tsbuildinfo",
                &["/r/pF/src/"],
            ),
            area(&["/r/pG/dist/"], "/r/pG/dist/x.tsbuildinfo", &["/r/pG/"]),
            area(&[shared_dir], "/r/pH/dist/x.tsbuildinfo", &["/r/pH/"]),
        ];
        let upstream = [vec![], vec![], vec![1], vec![0], vec![], vec![4], vec![4]];
        let shared = SharedOutputs::of_areas(&areas, &upstream);
        assert_eq!(shared.bound, [true, true, true, true, false, false, true]);
        assert_eq!(shared.ordered, [true, true, true, true, true, false, true]);
    }

    #[test]
    fn overlaps_are_by_directory() {
        // An outDir under another one, a build info in another outDir, a
        // root directory in another outDir, and a shared build info alone.
        let pairs = [
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
            let shared = SharedOutputs::of_areas(&[a, b], &[vec![], vec![]]);
            assert_eq!(shared.bound, [true, true]);
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
            let shared = SharedOutputs::of_areas(&[a, b], &[vec![], vec![]]);
            assert_eq!(shared.bound, [false, false]);
        }
    }
}
