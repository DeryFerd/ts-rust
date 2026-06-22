//! TypeScript lexical scanner.

mod byte_scanner;
mod scanner;

pub use byte_scanner::{ByteScanner, ByteToken};
pub use scanner::{LanguageVariant, Scanner, ScannerCheckpoint, Token, TokenFlags};
