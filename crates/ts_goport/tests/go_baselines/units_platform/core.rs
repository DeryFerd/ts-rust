//! Go: `internal/core/{bfs,pattern}_test.go`.
//!
//! PORT: Go `core.BreadthFirstSearchParallel*` is `frontend::core_bfs`; the
//! port runs each level serially in queue order (see its module comment).
//! Go `core.Pattern` is `frontend::module::Pattern`.

use std::cell::RefCell;
use std::collections::HashMap;

use rustc_hash::FxHashSet;
use ts_goport::frontend::core_bfs::{
    BreadthFirstSearchOptions, breadth_first_search_parallel, breadth_first_search_parallel_ex,
};
use ts_goport::frontend::module::try_parse_pattern;

fn graph(edges: &[(&'static str, &[&'static str])]) -> HashMap<&'static str, Vec<&'static str>> {
    edges.iter().map(|(k, v)| (*k, v.to_vec())).collect()
}

fn diamond() -> HashMap<&'static str, Vec<&'static str>> {
    graph(&[("A", &["B", "C"]), ("B", &["D"]), ("C", &["D"]), ("D", &[])])
}

// Go: bfs_test.go:13 TestBreadthFirstSearchParallel
#[test]
fn test_breadth_first_search_parallel() {
    // basic functionality
    {
        let g = diamond();
        let mut children = |node: &&'static str| g[node].clone();

        // find specific node
        let result =
            breadth_first_search_parallel("A", &mut children, &mut |node| (*node == "D", true));
        assert!(result.stopped, "Expected search to stop at D");
        assert_eq!(result.path, vec!["D", "B", "A"]);

        // visit all nodes
        let mut visited_nodes: Vec<&str> = Vec::new();
        let result = breadth_first_search_parallel("A", &mut children, &mut |node| {
            visited_nodes.push(node);
            (false, false) // Never stop early
        });
        assert!(!result.stopped, "Expected search to not stop early");
        // PORT: Go checks `result.Path == nil`; a nil slice is an empty Vec.
        assert!(
            result.path.is_empty(),
            "Expected nil path when visit function never returns true"
        );
        visited_nodes.sort();
        assert_eq!(visited_nodes, vec!["A", "B", "C", "D"]);
    }

    // early termination
    {
        let g = graph(&[
            ("Root", &["L1A", "L1B"]),
            ("L1A", &["L2A", "L2B"]),
            ("L1B", &["L2C"]),
            ("L2A", &["L3A"]),
            ("L2B", &[]),
            ("L2C", &[]),
            ("L3A", &[]),
        ]);
        let mut children = |node: &&'static str| g[node].clone();
        let visited: RefCell<FxHashSet<&str>> = RefCell::new(FxHashSet::default());
        breadth_first_search_parallel_ex(
            "Root",
            &mut children,
            &mut |node| (*node == "L2B", true), // Stop at level 2
            BreadthFirstSearchOptions {
                visited: Some(&visited),
                preprocess_level: None,
            },
            &mut |node| *node,
        );
        let visited = visited.borrow();
        for node in ["Root", "L1A", "L1B", "L2A", "L2B"] {
            assert!(visited.contains(node), "Expected to visit {node}");
        }
        // L2C is non-deterministic
        assert!(!visited.contains("L3A"), "Expected not to visit L3A");
    }

    // returns fallback when no other result found
    {
        let g = diamond();
        let mut children = |node: &&'static str| g[node].clone();
        let visited: RefCell<FxHashSet<&str>> = RefCell::new(FxHashSet::default());
        let result = breadth_first_search_parallel_ex(
            "A",
            &mut children,
            // Record A as a fallback, but do not stop
            &mut |node| (*node == "A", false),
            BreadthFirstSearchOptions {
                visited: Some(&visited),
                preprocess_level: None,
            },
            &mut |node| *node,
        );
        assert!(!result.stopped, "Expected search to not stop early");
        assert_eq!(result.path, vec!["A"]);
        let visited = visited.borrow();
        for node in ["B", "C", "D"] {
            assert!(visited.contains(node), "Expected to visit {node}");
        }
    }

    // returns a stop result over a fallback
    {
        let g = diamond();
        let mut children = |node: &&'static str| g[node].clone();
        let result = breadth_first_search_parallel("A", &mut children, &mut |node| match *node {
            "A" => (true, false), // Record fallback
            "D" => (true, true),  // Stop at D
            _ => (false, false),
        });
        assert!(result.stopped, "Expected search to stop at D");
        assert_eq!(result.path, vec!["D", "B", "A"]);
    }
}

// Go: pattern_test.go:5 TestPatternOverlappingMatch
#[test]
fn test_pattern_overlapping_match() {
    let p = try_parse_pattern("ab*ab");
    assert!(!p.matches("ab"), "expected 'ab' not to match 'ab*ab'");
    assert!(p.matches("abXab"), "expected 'abXab' to match 'ab*ab'");
    assert_eq!(p.matched_text("abXab"), "X");
    assert!(p.matches("abab"), "expected 'abab' to match 'ab*ab'");
    assert_eq!(p.matched_text("abab"), "");
}
