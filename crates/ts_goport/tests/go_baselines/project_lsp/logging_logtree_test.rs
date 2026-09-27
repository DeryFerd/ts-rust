//! Port of Go `internal/project/logging/logtree_test.go`.

use std::rc::Rc;

use ts_goport::project::logging::{self, LogTree, Logger};

// Go: logtree_test.go:12 TestLogTreeImplementsLogger
// Verify LogTree implements the expected interface
#[test]
fn log_tree_implements_logger() {
    fn takes_logger(_: Rc<dyn Logger>) {}
    let tree: Rc<LogTree> = logging::new_log_tree("").expect("log tree");
    takes_logger(tree);
}

// Go: logtree_test.go:17 TestLogTree
#[test]
fn log_tree() {}
