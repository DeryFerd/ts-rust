//! Go: internal/osutil (osutil.go and os_other.go), tsgo#4734.
//!
//! PORT: the port builds for Linux only (as `nativepath`), so os_android.go
//! (the Termux launcher case) is not ported. Go `(string, error)` is
//! `io::Result<String>`. Strings are in the port form (see
//! `vfs::osvfs::os_path`).

use std::io;

// Go: osutil.go:4 Args
// Args returns the command-line arguments with platform-specific launcher details removed.
pub fn args() -> Vec<String> {
    os_other::args()
}

// Go: osutil.go:9 Executable
// Executable returns the path of the current executable, accounting for platform-specific launchers.
pub fn executable() -> io::Result<String> {
    os_other::executable()
}

/// Go os_other.go (`//go:build !android`).
mod os_other {
    use crate::frontend::vfs::osvfs::go_string_from_os;
    use std::io;

    // Go: os_other.go:7 args
    pub fn args() -> Vec<String> {
        std::env::args_os().map(go_string_from_os).collect()
    }

    // Go: os_other.go:11 executable
    pub fn executable() -> io::Result<String> {
        std::env::current_exe().map(go_string_from_os)
    }
}
