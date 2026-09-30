//! Port of Go `internal/api/session_apistate_test.go`.
//!
//! Bump C: ts#64204 (microsoft/TypeScript 898322c5e4) replaced
//! `updateSnapshot` and rewrote the Go file. The five O tests
//! (`TestSessionTracksAndReleasesAPIRefs` and its subtests, and
//! `TestUpdateSnapshotResponseSkipsUnloadedAncestorProject`) are gone
//! upstream. The N tests (`TestGetCurrentLanguageServerSnapshot*`,
//! `TestOpenProjectRejectsReservedProjectID`,
//! `TestOpenFilePreservesWindowsDriveLetterCase`,
//! `TestClosingAPISessionRemovesCreatedLanguageServerPrograms`,
//! `TestLanguageServerProgram*`, `TestOpeningProjectOwnedByAnotherAPISessionEnsuresProgram`,
//! `TestFailedLanguageServerSnapshotOpenIsNotAdopted`) are not ported yet.
