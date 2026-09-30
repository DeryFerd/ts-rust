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
/// area or a root file directory of another. `to_path` is the
/// orchestrator's `to_path`.
///
/// The output area of a task is where it can write: its output directories
/// and everything under them (`outDir`, `declarationDir`, or the directories
/// of its root files when its outputs go next to them) and its build info
/// file. Two directories overlap when one holds the other. The areas come
/// from the configs, so they are known before a task starts, and the same in
/// every run. A task can also emit a file that is not a root file; when that
/// file is outside the directories above, its outputs are not in the area.
pub(crate) fn outputs_overlap(
    configs: &[Option<Rc<ParsedCommandLine>>],
    to_path: impl Fn(&str) -> Path,
) -> bool {
    let areas: Vec<Area> = configs
        .iter()
        .flatten()
        .map(|config| Area::of(config, &to_path))
        .collect();
    areas_overlap(&areas)
}

/// The output area and the root file directories of one task, as path
/// keys (`to_path`). A directory key ends with '/', so a directory holds
/// each key that starts with its key.
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
}
