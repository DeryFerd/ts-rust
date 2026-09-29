//! Go: tsoptions/parsedoptions.go (tsgo#4712 moves `ParsedOptions` here
//! from core/parsedoptions.go and adds `ContentMappers`).

use crate::contentmapper::Mapper;
use crate::frontend::prelude::*;

// Go: tsoptions/parsedoptions.go:8 ParsedOptions
// PORT: Go `*CompilerOptions` is `Rc<CompilerOptions>`, so copies of the
// struct share it like Go pointers do. Go `*TypeAcquisition` is an
// `Option`. Go `[]*ProjectReference` is `Option<Vec<ProjectReference>>`:
// `None` is Go nil (no `references` in the config) and `Some(vec![])` is
// Go `"references": []`. The build checks that difference.
// PORT: the Go `WatchOptions` field is left out. The crate has no
// `WatchOptions` type, and Go `ParseJsonConfigFileContent` never sets it.
// PORT: Go `[]*contentmapper.Mapper` is `Vec<Rc<Mapper>>`; a nil slice is
// empty. Go compares and keys mappers by pointer (`Rc::ptr_eq`).
// PORT: `PartialEq` is Go `reflect.DeepEqual` (execute/watcher.go
// recheckTsConfig). The `Option` keeps the Go nil and empty slice apart for
// `project_references`; other `Vec` fields have no nil, so those two compare
// equal there.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ParsedOptions {
    pub compiler_options: Rc<CompilerOptions>,
    pub type_acquisition: Option<TypeAcquisition>,

    pub file_names: Vec<String>,
    pub project_references: Option<Vec<ProjectReference>>,
    // tsgo#4712
    pub content_mappers: Vec<Rc<Mapper>>,
}
