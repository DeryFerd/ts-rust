//! TypeScript lexical scanner.

mod byte_scanner;
mod scanner;

pub use byte_scanner::{ByteScanner, ByteToken};
pub use scanner::{
    CommentDirective, LanguageVariant, Scanner, ScannerCheckpoint, Token, TokenFlags,
};
