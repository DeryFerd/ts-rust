//! Port of Go `internal/api/session_temporary_test.go`.
//!
//! Bump C: ts#64204 (microsoft/TypeScript 898322c5e4) removed the Go file with
//! `updateTemporarySnapshot`. Its four tests (`TestUpdateTemporarySnapshot`,
//! `TestUpdateTemporarySnapshotAddsUnopenedFile`,
//! `TestUpdateTemporarySnapshotRejectsUnsupportedExtension`,
//! `TestUpdateTemporarySnapshotUsesClientSnapshotAsBase`) are gone upstream,
//! so this module is empty. Root can drop the module.
