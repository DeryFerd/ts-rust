//! Port of Go `internal/ls/autoimport/index_test.go` (`TestIndexClone`).

use ts_goport::ls::autoimport::index::{Index, Named};

// Go: index_test.go:9 testEntry
#[derive(Clone, Debug)]
struct TestEntry {
    name: String,
    package: String,
}

impl Named for TestEntry {
    fn name(&self) -> String {
        self.name.clone()
    }
}

fn entry(name: &str, package: &str) -> TestEntry {
    TestEntry {
        name: name.to_string(),
        package: package.to_string(),
    }
}

// Go: index_test.go:19 TestIndexClone/filters entries by package
#[test]
fn filters_entries_by_package() {
    let mut idx = Index::<TestEntry>::default();
    idx.insert_as_words(entry("fooBar", "pkg-a"));
    idx.insert_as_words(entry("bazQux", "pkg-b"));
    idx.insert_as_words(entry("fooQux", "pkg-a"));

    // Clone excluding pkg-b
    let cloned =
        Index::clone_(Some(&idx), &mut |e: &TestEntry| e.package != "pkg-b").expect("cloned index");

    // Original should have all 3 entries
    assert_eq!(idx.entries.len(), 3);

    // Cloned should have 2 entries (only pkg-a)
    assert_eq!(cloned.entries.len(), 2);

    // Search should work on cloned index
    let results = cloned.find("fooBar", true);
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].name, "fooBar");

    // bazQux should not be in cloned index
    let results = cloned.find("bazQux", true);
    assert_eq!(results.len(), 0);

    // Word prefix search should work
    let results = cloned.search_word_prefix("foo");
    assert_eq!(results.len(), 2);
}

// Go: index_test.go:52 TestIndexClone/handles nil index
#[test]
fn handles_nil_index() {
    let cloned = Index::<TestEntry>::clone_(None, &mut |_e: &TestEntry| true);
    assert!(cloned.is_none());
}

// Go: index_test.go:60 TestIndexClone/handles empty index
#[test]
fn handles_empty_index() {
    let idx = Index::<TestEntry>::default();
    let cloned = Index::clone_(Some(&idx), &mut |_e: &TestEntry| true).expect("cloned index");
    assert_eq!(cloned.entries.len(), 0);
}

// Go: index_test.go:68 TestIndexClone/filters all entries
#[test]
fn filters_all_entries() {
    let mut idx = Index::<TestEntry>::default();
    idx.insert_as_words(entry("fooBar", "pkg-a"));
    idx.insert_as_words(entry("bazQux", "pkg-b"));

    let cloned = Index::clone_(Some(&idx), &mut |_e: &TestEntry| false).expect("cloned index");
    assert_eq!(cloned.entries.len(), 0);
    assert_eq!(cloned.index.len(), 0);
}
