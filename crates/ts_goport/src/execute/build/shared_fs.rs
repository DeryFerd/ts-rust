//! The build cycle's cached file system, shared with the build workers.
//!
//! PORT: not in Go. Go `tsc -b` makes one `compiler.NewCachedFSCompilerHost`
//! in `NewOrchestrator` (build/orchestrator.go:618) and uses it for every
//! status check and every program of the build. Outside watch mode it is
//! never cleared (`resetCaches`, orchestrator.go:272, runs only in `Watch`).
//! A `cachedvfs.FS` caches "does not exist" as well, and writes do not
//! update it. So a lookup made by one project, before another project
//! writes that file, is still seen by every later project.
//!
//! goport_build compiles each project in a worker process (build-mode plan
//! D1). To see the same cache, the orchestrator sends its `CachedFsState`
//! to each worker when the worker starts (stdin), and the worker loads it
//! before it parses the config. The worker sends back the entries it
//! added in two parts: the entries of `NewProgram` (module resolution and
//! file loading) on a `fsCacheProgram` line as soon as the program is
//! made, and the rest (`fsCache` in its result line) when it ends. The
//! orchestrator merges each part when it arrives, and the result part
//! before it goes on with the task (`build_project_finish`).
//!
//! Timing: with one builder (`--singleThreaded` or `--builders 1`) the
//! order is Go's order, so the cache is the same. With more builders, Go
//! tasks that run at the same time see each other's lookups as they
//! happen. Here a worker sees the lookups of the program loads that were
//! done, and of the tasks that were finished, when it started. So a task
//! that starts after a concurrent task made its program sees that
//! program's lookups, as in Go (Hono: `tsconfig.spec.json` caches that
//! `dist/types/jsx/jsx-runtime.d.ts` does not exist while
//! `tsconfig.build.json` still builds, and `runtime-tests/bun`, which
//! waits for the build, sees that). Lookups that a running task makes
//! after another task started are not shared with it. Which lookups Go
//! shares between concurrent tasks depends on timing in Go too.
//!
//! Format (JSON, compact):
//! `{"d":[[path,bool]...],"f":[[path,bool]...],
//!   "e":[[path,[files...],[dirs...],[symlinks...]|null]...],
//!   "r":[[path,realpath]...],
//!   "s":[[path,null|[name,size,mode,null|[secs,nanos]]]...]}`
//! `d` is DirectoryExists, `f` FileExists, `e` GetAccessibleEntries, `r`
//! Realpath and `s` Stat. Times are seconds and nanoseconds from the Unix
//! epoch (`secs` is negative before it; `nanos` is always 0 to 999999999).

use crate::frontend::prelude::*;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// Writes `state` as JSON (see the top of this file).
pub fn marshal_cached_fs_state(state: &CachedFsState, enc: &mut String) -> Result<(), JsonError> {
    enc.push_str("{\"d\":");
    marshal_entries(enc, &state.directory_exists, |enc, value| {
        value.marshal_json_to(enc)
    })?;
    enc.push_str(",\"f\":");
    marshal_entries(enc, &state.file_exists, |enc, value| value.marshal_json_to(enc))?;
    enc.push_str(",\"e\":");
    marshal_entries(enc, &state.get_accessible_entries, |enc, entries| {
        entries.files.marshal_json_to(enc)?;
        enc.push(',');
        entries.directories.marshal_json_to(enc)?;
        enc.push(',');
        match &entries.symlinks {
            Some(symlinks) => {
                // Sorted so the same state gives the same text.
                let mut symlinks: Vec<&String> = symlinks.iter().collect();
                symlinks.sort();
                symlinks.marshal_json_to(enc)
            }
            None => {
                enc.push_str("null");
                Ok(())
            }
        }
    })?;
    enc.push_str(",\"r\":");
    marshal_entries(enc, &state.realpath, |enc, value| value.marshal_json_to(enc))?;
    enc.push_str(",\"s\":");
    marshal_entries(enc, &state.stat, |enc, info| match info {
        None => {
            enc.push_str("null");
            Ok(())
        }
        Some(info) => {
            enc.push('[');
            info.name.marshal_json_to(enc)?;
            enc.push(',');
            enc.push_str(&info.size.to_string());
            enc.push(',');
            enc.push_str(&info.mode.0.to_string());
            enc.push(',');
            match info.mod_time {
                None => enc.push_str("null"),
                Some(time) => {
                    let (secs, nanos) = time_to_parts(time);
                    enc.push_str(&format!("[{secs},{nanos}]"));
                }
            }
            enc.push(']');
            Ok(())
        }
    })?;
    enc.push('}');
    Ok(())
}

/// `[[key,value...]...]`, with keys sorted so the same state gives the same
/// text. `value` writes the parts after the key.
fn marshal_entries<V>(
    enc: &mut String,
    map: &FxHashMap<String, V>,
    value: impl Fn(&mut String, &V) -> Result<(), JsonError>,
) -> Result<(), JsonError> {
    let mut keys: Vec<&String> = map.keys().collect();
    keys.sort();
    enc.push('[');
    for (index, key) in keys.into_iter().enumerate() {
        if index > 0 {
            enc.push(',');
        }
        enc.push('[');
        key.marshal_json_to(enc)?;
        enc.push(',');
        value(enc, &map[key])?;
        enc.push(']');
    }
    enc.push(']');
    Ok(())
}

fn time_to_parts(time: SystemTime) -> (i64, u32) {
    match time.duration_since(UNIX_EPOCH) {
        Ok(after) => (after.as_secs() as i64, after.subsec_nanos()),
        Err(err) => {
            let before = err.duration();
            let mut secs = -(before.as_secs() as i64);
            let mut nanos = before.subsec_nanos();
            if nanos > 0 {
                secs -= 1;
                nanos = 1_000_000_000 - nanos;
            }
            (secs, nanos)
        }
    }
}

fn time_from_parts(secs: i64, nanos: u32) -> SystemTime {
    if secs >= 0 {
        UNIX_EPOCH + Duration::new(secs as u64, nanos)
    } else {
        UNIX_EPOCH - Duration::from_secs(secs.unsigned_abs()) + Duration::from_nanos(u64::from(nanos))
    }
}

fn invalid() -> JsonError {
    JsonError {
        message: "invalid build file system cache".to_string(),
    }
}

/// Reads a state written by `marshal_cached_fs_state`.
pub fn decode_cached_fs_state(dec: &mut JsonDecoder<'_>) -> Result<CachedFsState, JsonError> {
    let mut state = CachedFsState::default();
    if dec.read_token()? != JsonToken::BeginObject {
        return Err(invalid());
    }
    while dec.peek_kind() != b'}' {
        let mut key = String::new();
        json_unmarshal_decode(dec, &mut key)?;
        match key.as_str() {
            "d" => decode_entries(dec, &mut state.directory_exists, decode_bool)?,
            "f" => decode_entries(dec, &mut state.file_exists, decode_bool)?,
            "e" => decode_entries(dec, &mut state.get_accessible_entries, |dec| {
                let files = decode_strings(dec)?;
                let directories = decode_strings(dec)?;
                let symlinks = if dec.peek_kind() == b'n' {
                    dec.read_token()?;
                    None
                } else {
                    Some(decode_strings(dec)?.into_iter().collect())
                };
                Ok(Entries {
                    files,
                    directories,
                    symlinks,
                })
            })?,
            "r" => decode_entries(dec, &mut state.realpath, decode_string)?,
            "s" => decode_entries(dec, &mut state.stat, |dec| {
                if dec.peek_kind() == b'n' {
                    dec.read_token()?;
                    return Ok(None);
                }
                begin_array(dec)?;
                let name = decode_string(dec)?;
                let size = decode_number(dec)? as i64;
                let mode = FileMode(decode_number(dec)? as u32);
                let mod_time = if dec.peek_kind() == b'n' {
                    dec.read_token()?;
                    None
                } else {
                    begin_array(dec)?;
                    let secs = decode_number(dec)? as i64;
                    let nanos = decode_number(dec)? as u32;
                    end_array(dec)?;
                    Some(time_from_parts(secs, nanos))
                };
                end_array(dec)?;
                Ok(Some(FileInfo {
                    name,
                    size,
                    mode,
                    mod_time,
                }))
            })?,
            _ => dec.skip_value()?,
        }
    }
    dec.read_token()?;
    Ok(state)
}

/// Reads `[[key,value...]...]` into `map`.
fn decode_entries<V>(
    dec: &mut JsonDecoder<'_>,
    map: &mut FxHashMap<String, V>,
    value: impl Fn(&mut JsonDecoder<'_>) -> Result<V, JsonError>,
) -> Result<(), JsonError> {
    begin_array(dec)?;
    while dec.peek_kind() != b']' {
        begin_array(dec)?;
        let key = decode_string(dec)?;
        let value = value(dec)?;
        end_array(dec)?;
        map.insert(key, value);
    }
    end_array(dec)
}

fn begin_array(dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
    if dec.read_token()? != JsonToken::BeginArray {
        return Err(invalid());
    }
    Ok(())
}

fn end_array(dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
    if dec.read_token()? != JsonToken::EndArray {
        return Err(invalid());
    }
    Ok(())
}

fn decode_bool(dec: &mut JsonDecoder<'_>) -> Result<bool, JsonError> {
    let mut value = false;
    json_unmarshal_decode(dec, &mut value)?;
    Ok(value)
}

fn decode_string(dec: &mut JsonDecoder<'_>) -> Result<String, JsonError> {
    let mut value = String::new();
    json_unmarshal_decode(dec, &mut value)?;
    Ok(value)
}

fn decode_number(dec: &mut JsonDecoder<'_>) -> Result<f64, JsonError> {
    let mut value = 0.0f64;
    json_unmarshal_decode(dec, &mut value)?;
    Ok(value)
}

fn decode_strings(dec: &mut JsonDecoder<'_>) -> Result<Vec<String>, JsonError> {
    begin_array(dec)?;
    let mut values = Vec::new();
    while dec.peek_kind() != b']' {
        values.push(decode_string(dec)?);
    }
    end_array(dec)?;
    Ok(values)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cached_fs_state_round_trips() {
        let mut state = CachedFsState::default();
        state.directory_exists.insert("/a".to_string(), true);
        state.file_exists.insert("/a/b.d.ts".to_string(), false);
        state.get_accessible_entries.insert(
            "/a".to_string(),
            Entries {
                files: vec!["x.ts".to_string(), "q\"\n.ts".to_string()],
                directories: vec!["node_modules".to_string()],
                symlinks: Some(std::iter::once("node_modules".to_string()).collect()),
            },
        );
        state.get_accessible_entries.insert("/b".to_string(), Entries::default());
        state.realpath.insert("/l".to_string(), "/r".to_string());
        state.stat.insert("/missing".to_string(), None);
        for (path, time) in [
            ("/new", Some(UNIX_EPOCH + Duration::new(1_758_000_000, 123_456_789))),
            ("/old", Some(UNIX_EPOCH - Duration::new(5, 250))),
            ("/zero", None),
        ] {
            state.stat.insert(
                path.to_string(),
                Some(FileInfo {
                    name: path[1..].to_string(),
                    size: 42,
                    mode: FileMode::DIR | FileMode(0o755),
                    mod_time: time,
                }),
            );
        }
        let mut text = String::new();
        marshal_cached_fs_state(&state, &mut text).unwrap();
        let mut dec = json_new_decoder(text.as_bytes());
        let back = decode_cached_fs_state(&mut dec).unwrap();
        dec.check_eof().unwrap();
        assert_eq!(back.directory_exists, state.directory_exists);
        assert_eq!(back.file_exists, state.file_exists);
        assert_eq!(back.realpath, state.realpath);
        assert_eq!(back.stat, state.stat);
        let entries = &back.get_accessible_entries["/a"];
        assert_eq!(entries.files, state.get_accessible_entries["/a"].files);
        assert_eq!(entries.symlinks, state.get_accessible_entries["/a"].symlinks);
        assert!(back.get_accessible_entries["/b"].symlinks.is_none());
        let mut again = String::new();
        marshal_cached_fs_state(&back, &mut again).unwrap();
        assert_eq!(again, text);
    }
}
