//! Port of Go `internal/project/watch_test.go`.

use ts_goport::project::{WatchedFiles, get_path_components_for_watching};

fn components(path: &str) -> Vec<String> {
    get_path_components_for_watching(path, "")
}

// Go: watch_test.go:9 TestGetPathComponentsForWatching
#[test]
fn get_path_components_for_watching_test() {
    assert_eq!(components("/project"), ["/", "project"]);
    assert_eq!(components("C:\\project"), ["C:/", "project"]);
    assert_eq!(
        components("//server/share/project/tsconfig.json"),
        ["//server/share", "project", "tsconfig.json"]
    );
    assert_eq!(
        components(r"\\server\share\project\tsconfig.json"),
        ["//server/share", "project", "tsconfig.json"]
    );
    assert_eq!(components("C:\\Users"), ["C:/Users"]);
    assert_eq!(
        components("C:\\Users\\andrew\\project"),
        ["C:/Users/andrew", "project"]
    );
    assert_eq!(components("/home"), ["/home"]);
    assert_eq!(
        components("/home/andrew/project"),
        ["/home/andrew", "project"]
    );
}

// Go: watch_test.go:22 TestNilWatchedFilesClone
#[test]
fn nil_watched_files_clone() {
    let result = WatchedFiles::<i32>::clone_(None, 42);
    assert!(
        result.is_none(),
        "clone on a nil `WatchedFiles` should return nil"
    );
}
