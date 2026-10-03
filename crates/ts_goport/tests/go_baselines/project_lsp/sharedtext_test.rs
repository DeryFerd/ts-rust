//! PORT: no Go counterpart. A Go string is shared, so a language service
//! that reads a file (Go `ls.Host.ReadFile`, ls/host.go:10) once per
//! location it converts (Go `getScript`, ls/source_map.go:85) copies
//! nothing. Here a file handle keeps its text as an `Arc<str>`, and a read
//! through the snapshot shares it (`FileText::Shared`). A copy per read made
//! references and documentHighlight on a 5 MB file 7 to 11 times slower
//! than Go (lspbig1).

use std::sync::Arc;

use ts_goport::ast::FileText;
use ts_goport::ls;

use super::projecttestutil::{self, files};
use super::util::*;

child_test! {
    fn a_language_service_read_shares_the_file_text() {
        let (session, _) = projecttestutil::setup(files(&[
            ("/p/tsconfig.json", r#"{"compilerOptions": {"noLib": true}}"#),
            ("/p/a.ts", "export const a = 1;"),
            ("/p/b.ts", "import { a } from \"./a\";\na;"),
        ]));
        open(&session, "file:///p/b.ts", "import { a } from \"./a\";\na;\n");
        let snapshot = session.snapshot();

        // b.ts is an overlay, a.ts a file the program read from disk.
        for name in ["/p/b.ts", "/p/a.ts"] {
            let file = snapshot.get_file(name).expect("the snapshot has the file");
            let (text, ok) = ls::Host::read_file(&*snapshot, name);
            assert!(ok, "{name}");
            let FileText::Shared(shared) = &text else {
                panic!("{name}: the read is not the file's shared text");
            };
            assert!(Arc::ptr_eq(shared, &file.shared_content()), "{name}: the read copied the text");
            assert_eq!(&*text, file.content(), "{name}");
        }

        let (text, ok) = ls::Host::read_file(&*snapshot, "/p/missing.ts");
        assert!(!ok);
        assert_eq!(&*text, "");
    }
}
