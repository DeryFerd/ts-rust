//! Go `runtime.GOMAXPROCS(0)`: the number of threads that run Go code at
//! once. The port sizes its thread pools with it (`gomaxprocs`).
//!
//! Go: runtime/proc.go:930 schedinit, runtime/cgroup_linux.go and
//! internal/runtime/cgroup (go1.27.1, the toolchain of tsc/go.mod `go
//! 1.27`, so the cgroup limit applies).
//! PORT: Go reads the CPUs and the cgroup limit again while it runs
//! (`updatemaxprocs`, sysmon). The port reads them once.
//! PORT: the port has no garbage collector, so `GOGC` and `GOMEMLIMIT` do
//! nothing (PORTING.md "Process start").

use std::sync::OnceLock;

/// Go `runtime.GOMAXPROCS(0)` at start: the `GOMAXPROCS` variable when it
/// is a positive number, else the CPUs that this process may run on,
/// lowered to the CPU limit of its cgroup (rounded up, at least 2). Read
/// once.
pub fn gomaxprocs() -> usize {
    static PROCS: OnceLock<usize> = OnceLock::new();
    *PROCS.get_or_init(|| {
        // Go: proc.go:935 strconv.ParseInt(gogetenv("GOMAXPROCS"), 10, 32), n > 0
        let set = std::env::var("GOMAXPROCS")
            .ok()
            .and_then(|value| value.parse::<i32>().ok())
            .filter(|&n| n > 0);
        match set {
            Some(n) => n as usize,
            None => default_gomaxprocs(),
        }
    })
}

// Go: cgroup_linux.go:85 defaultGOMAXPROCS and :109 adjustCgroupGOMAXPROCS
fn default_gomaxprocs() -> usize {
    let procs = cpu_count();
    #[cfg(target_os = "linux")]
    if container_max_procs()
        && let Some(limit) = cgroup::cpu_limit()
    {
        let limit = limit.ceil().max(2.0);
        if limit < procs as f64 {
            return limit as usize;
        }
    }
    procs
}

// Go: os_linux.go:101 getCPUCount: the CPUs in the sched_getaffinity mask,
// at least 1.
// PORT: the mask is `Cpus_allowed` in /proc/self/status (rustix
// `sched_getaffinity` needs its `thread` feature). Without the file, and
// off Linux, std's count.
fn cpu_count() -> usize {
    #[cfg(target_os = "linux")]
    if let Some(n) = std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|status| {
            let mask = status
                .lines()
                .find_map(|line| line.strip_prefix("Cpus_allowed:"))?;
            mask.trim()
                .chars()
                .filter(|&c| c != ',')
                .map(|c| c.to_digit(16).map(u32::count_ones))
                .sum::<Option<u32>>()
        })
    {
        return (n as usize).max(1);
    }
    std::thread::available_parallelism().map_or(1, std::num::NonZero::get)
}

// Go GODEBUG `containermaxprocs` (default 1 for a go.mod at `go 1.25` or
// later): 0 turns the cgroup limit off. The last valid setting wins.
#[cfg(target_os = "linux")]
fn container_max_procs() -> bool {
    std::env::var("GODEBUG").map_or(true, |godebug| {
        godebug
            .split(',')
            .filter_map(|setting| setting.strip_prefix("containermaxprocs="))
            .filter_map(|value| value.parse::<i32>().ok())
            .last()
            .is_none_or(|value| value > 0)
    })
}

/// Go internal/runtime/cgroup: the CPU limit of the cgroup that holds this
/// process.
#[cfg(target_os = "linux")]
mod cgroup {
    // Go: cgroup_linux.go OpenCPU and ReadCPULimit: quota / period of the
    // process's own CPU cgroup (not its parents). None when there is no
    // limit, or a file cannot be read or does not parse.
    pub(super) fn cpu_limit() -> Option<f64> {
        let read = |path: &str| std::fs::read_to_string(path).ok();
        let cgroups = read("/proc/self/cgroup")?;
        let (cgroup, v1) = parse_cpu_cgroup(&cgroups)?;
        let dir = parse_cpu_mount(&read("/proc/self/mountinfo")?, cgroup, v1)?;
        if v1 {
            let quota = parse_v1_number(&read(&format!("{dir}/cpu.cfs_quota_us"))?)?;
            let period = parse_v1_number(&read(&format!("{dir}/cpu.cfs_period_us"))?)?;
            // A quota below 0 is no limit.
            (quota >= 0).then(|| quota as f64 / period as f64)
        } else {
            parse_v2_limit(&read(&format!("{dir}/cpu.max"))?)
        }
    }

    // Go: cgroup.go:56 parseV1Number: "<value>\n".
    fn parse_v1_number(text: &str) -> Option<i64> {
        text.split_once('\n')?.0.parse().ok()
    }

    // Go: cgroup.go:72 parseV2Limit: "<quota> <period>\n". None for a quota
    // of "max" (no limit).
    fn parse_v2_limit(text: &str) -> Option<f64> {
        let (quota, period) = text.split_once(' ')?;
        if quota == "max" {
            return None;
        }
        let period: i64 = period.split_once('\n')?.0.parse().ok()?;
        Some(quota.parse::<i64>().ok()? as f64 / period as f64)
    }

    // Go: cgroup.go:109 parseCPUCgroup: the CPU cgroup path in
    // /proc/self/cgroup and true for a v1 hierarchy. Lines are
    // `hierarchy-ID:controller-list:cgroup-path`. A v1 hierarchy with the
    // `cpu` controller wins over the v2 hierarchy (ID 0).
    fn parse_cpu_cgroup(text: &str) -> Option<(&str, bool)> {
        let mut v2 = None;
        for line in text.lines() {
            let (hierarchy, rest) = line.split_once(':')?;
            let (controllers, path) = rest.split_once(':')?;
            if !path.starts_with('/') {
                return None;
            }
            if hierarchy == "0" {
                v2 = Some(path);
            } else if controllers.split(',').any(|c| c == "cpu") {
                return Some((path, true));
            }
        }
        v2.map(|path| (path, false))
    }

    // Go: cgroup.go:232 parseCPUMount: the directory of `cgroup` under the
    // mount in /proc/self/mountinfo that holds it (`cgroup` with the `cpu`
    // option for v1, `cgroup2` for v2). Lines are `id parent major:minor
    // root mount-point options [optional...] - fstype source super-options`.
    fn parse_cpu_mount(text: &str, cgroup: &str, v1: bool) -> Option<String> {
        for line in text.lines() {
            let mut fields = line.split(' ');
            let root = fields.nth(3)?;
            let mount = fields.next()?;
            let mut tail = line.split_once(" - ")?.1.split(' ');
            let fstype = tail.next()?;
            let matches = if v1 {
                fstype == "cgroup" && tail.nth(1)?.split(',').any(|o| o == "cpu")
            } else {
                fstype == "cgroup2"
            };
            if !matches {
                continue;
            }
            let root = unescape(root)?;
            if !has_path_prefix(cgroup, &root) {
                continue;
            }
            let rel = if root.len() == 1 && cgroup.len() > 1 {
                cgroup
            } else {
                &cgroup[root.len()..]
            };
            if has_path_prefix(rel, "/..") {
                continue;
            }
            return Some(unescape(mount)? + rel);
        }
        None
    }

    // Go: cgroup.go:420 hasPathPrefix
    fn has_path_prefix(p: &str, prefix: &str) -> bool {
        prefix.len() == 1
            || p.starts_with(prefix)
                && (p.len() == prefix.len() || p.as_bytes()[prefix.len()] == b'/')
    }

    // Go: cgroup.go:452 unescapePath: Linux `show_path` writes `\`, space,
    // tab and newline as `\` and three octal digits.
    fn unescape(s: &str) -> Option<String> {
        let bytes = s.as_bytes();
        let mut out = Vec::with_capacity(bytes.len());
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] != b'\\' {
                out.push(bytes[i]);
                i += 1;
                continue;
            }
            let mut c = 0u32;
            for &d in bytes.get(i + 1..i + 4)? {
                if !(b'0'..=b'7').contains(&d) {
                    return None;
                }
                c = c * 8 + u32::from(d - b'0');
            }
            out.push(u8::try_from(c).ok()?);
            i += 4;
        }
        String::from_utf8(out).ok()
    }

    // Go: internal/runtime/cgroup/cgroup_test.go (cases of TestParseV1Number,
    // TestParseV2Limit, TestParseCPUCgroup and TestParseCPUMount).
    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn parse_cpu_limit_files() {
            assert_eq!(parse_v1_number("-1\n"), Some(-1));
            assert_eq!(parse_v1_number("50000\n"), Some(50000));
            assert_eq!(parse_v1_number("50000"), None);
            assert_eq!(parse_v2_limit("max 100000\n"), None);
            assert_eq!(parse_v2_limit("150000 100000\n"), Some(1.5));
            assert_eq!(parse_v2_limit("150000 100000"), None);
        }

        #[test]
        fn parse_cpu_cgroup_lines() {
            let v1 = "12:freezer:/\n3:cpu,cpuacct:/a/b\n0::/c\n";
            assert_eq!(parse_cpu_cgroup(v1), Some(("/a/b", true)));
            assert_eq!(
                parse_cpu_cgroup("1:memory:/m\n0::/c/d\n"),
                Some(("/c/d", false))
            );
            assert_eq!(parse_cpu_cgroup("1:memory:/m\n"), None);
            assert_eq!(parse_cpu_cgroup("0::c\n"), None);
        }

        #[test]
        fn parse_cpu_mount_lines() {
            let base = "22 1 8:1 / / rw,relatime - ext4 /dev/root rw\n\
                        21 22 0:20 / /sys rw,nosuid,nodev,noexec - sysfs sysfs rw\n";
            let v1 = "56 22 0:40 / /sys/fs/cgroup/cpu rw - cgroup cgroup rw,cpu,cpuacct\n\
                      59 22 0:43 / /sys/fs/cgroup/cpuset rw - cgroup cgroup rw,cpuset\n";
            let v2 = "25 21 0:22 / /sys/fs/cgroup rw,nosuid - cgroup2 cgroup2 rw\n";
            let mixed = format!("{base}{v2}{v1}");
            let cases: &[(&str, &str, &str, bool, Option<&str>)] = &[
                (
                    "v1",
                    &format!("{base}{v1}"),
                    "/",
                    true,
                    Some("/sys/fs/cgroup/cpu"),
                ),
                (
                    "v2",
                    &format!("{base}{v2}"),
                    "/",
                    false,
                    Some("/sys/fs/cgroup"),
                ),
                ("mixed", &mixed, "/", true, Some("/sys/fs/cgroup/cpu")),
                (
                    "mixed-choose-v2",
                    &mixed,
                    "/",
                    false,
                    Some("/sys/fs/cgroup"),
                ),
                (
                    "v2-escaped",
                    "25 21 0:22 / /sys/fs/cgroup/tab\\011tab rw - cgroup2 cgroup2 rw\n",
                    "/",
                    false,
                    Some("/sys/fs/cgroup/tab\ttab"),
                ),
                (
                    "non-root_mount",
                    "25 21 0:22 /sand /unrelated/cgroup1 rw - cgroup2 cgroup2 rw\n\
                     25 21 0:22 /sandbox/container/group /sys/fs/cgroup/mygroup rw - cgroup2 cgroup2 rw\n\
                     25 21 0:22 /sandbox /sys/fs/cgroup rw - cgroup2 cgroup2 rw\n\
                     25 21 0:22 / /ignored/second/match rw - cgroup2 cgroup2 rw\n",
                    "/sandbox/container",
                    false,
                    Some("/sys/fs/cgroup/container"),
                ),
                (
                    "v2-escaped-root",
                    "25 21 0:22 /tab\\011tab /sys/fs/cgroup rw - cgroup2 cgroup2 rw\n",
                    "/tab\ttab/container",
                    false,
                    Some("/sys/fs/cgroup/container"),
                ),
                (
                    "non-root_cgroup",
                    v2,
                    "/sandbox/container",
                    false,
                    Some("/sys/fs/cgroup/sandbox/container"),
                ),
                (
                    "out_of_namespace",
                    "1243 61 0:26 /../../.. /mnt rw shared:4 - cgroup2 cgroup2 rw\n\
                     29 22 0:26 /../../../.. /sys/fs/cgroup rw shared:4 - cgroup2 cgroup2 rw",
                    "/../../../../init.scope",
                    false,
                    Some("/sys/fs/cgroup/init.scope"),
                ),
                ("v1-not-mounted", v2, "/", true, None),
                (
                    "invalid-escape",
                    "25 21 0:22 /\\0 /x rw - cgroup2 cgroup2 rw\n",
                    "/",
                    false,
                    None,
                ),
            ];
            for &(name, text, cgroup, v1, want) in cases {
                assert_eq!(parse_cpu_mount(text, cgroup, v1).as_deref(), want, "{name}");
            }
        }
    }
}
