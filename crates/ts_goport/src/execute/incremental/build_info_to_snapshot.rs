//! Port of execute/incremental/buildinfotosnapshot.go.

use super::build_info::*;
use super::hash::FileInfo;
use super::hash::*;
use super::snapshot::*;
use crate::frontend::prelude::*;

// Go: incremental/buildinfotosnapshot.go:14 buildInfoToSnapshot
// PORT: the options read from the build info are leaked to get the
// `&'static CompilerOptions` that `Snapshot` keeps (see `Snapshot`). A
// process reads at most one build info program.
#[must_use]
pub fn build_info_to_snapshot(
    build_info: &BuildInfo,
    config: &ParsedCommandLine,
    host: &dyn CompilerHost,
) -> Snapshot {
    let build_info_directory = get_directory_path(&get_normalized_absolute_path(
        &config.get_build_info_file_name(),
        config.get_current_directory(),
    ));
    let file_paths: Vec<Path> = build_info
        .file_names
        .iter()
        .flatten()
        .map(|file_name| {
            if !file_name.starts_with('.') {
                return to_path(
                    &combine_paths(&host.default_library_path(), &[file_name]),
                    &host.get_current_directory(),
                    host.fs().use_case_sensitive_file_names(),
                );
            }
            to_path(
                file_name,
                &build_info_directory,
                config.use_case_sensitive_file_names(),
            )
        })
        .collect();
    let mut to = ToSnapshot {
        build_info,
        build_info_directory,
        // Go sets the options in `setCompilerOptions`; `Snapshot::new`
        // needs them, so they start as the empty options.
        snapshot: Snapshot::new(empty_compiler_options()),
        file_paths,
        file_path_set: Vec::new(),
    };
    let file_path_set: Vec<IndexSet<Path>> = build_info
        .file_ids_list
        .iter()
        .flatten()
        .map(|file_id_list| {
            let mut file_set =
                IndexSet::with_capacity_and_hasher(file_id_list.len(), Default::default());
            for &file_id in file_id_list {
                file_set.insert(to.to_file_path(file_id));
            }
            file_set
        })
        .collect();
    to.file_path_set = file_path_set;
    to.set_compiler_options();
    to.set_file_info_and_emit_signatures();
    to.set_referenced_map();
    to.set_change_file_set();
    to.set_semantic_diagnostics();
    to.set_emit_diagnostics();
    to.set_affected_files_pending_emit();
    if !build_info.latest_changed_dts_file.is_empty() {
        to.snapshot.latest_changed_dts_file =
            to.to_absolute_path(&build_info.latest_changed_dts_file);
    }
    to.snapshot.has_errors = if build_info.errors {
        Tristate::True
    } else {
        Tristate::False
    };
    to.snapshot.has_semantic_errors = build_info.semantic_errors;
    to.snapshot.check_pending = build_info.check_pending;
    to.snapshot
}

// Go: incremental/buildinfotosnapshot.go:50 toSnapshot
struct ToSnapshot<'a> {
    build_info: &'a BuildInfo,
    build_info_directory: String,
    snapshot: Snapshot,
    file_paths: Vec<Path>,
    file_path_set: Vec<IndexSet<Path>>,
}

impl ToSnapshot<'_> {
    // Go: incremental/buildinfotosnapshot.go:58 toAbsolutePath
    fn to_absolute_path(&self, path: &str) -> String {
        get_normalized_absolute_path(path, &self.build_info_directory)
    }

    // Go: incremental/buildinfotosnapshot.go:62 toFilePath
    fn to_file_path(&self, file_id: BuildInfoFileId) -> Path {
        self.file_paths[(file_id.0 - 1) as usize].clone()
    }

    // Go: incremental/buildinfotosnapshot.go:66 toFilePathSet
    fn to_file_path_set(&self, file_id_list_id: BuildInfoFileIdListId) -> IndexSet<Path> {
        self.file_path_set[(file_id_list_id.0 - 1) as usize].clone()
    }

    // Go: incremental/buildinfotosnapshot.go:70 toBuildInfoDiagnosticsWithFileName
    fn to_build_info_diagnostics_with_file_name(
        &self,
        diagnostics: Option<&Vec<BuildInfoDiagnostic>>,
    ) -> Vec<BuildInfoDiagnosticWithFileName> {
        diagnostics
            .into_iter()
            .flatten()
            .map(|d| {
                let mut file = Path::default();
                if d.file.0 != 0 {
                    file = self.to_file_path(d.file);
                }
                BuildInfoDiagnosticWithFileName {
                    file,
                    no_file: d.no_file,
                    pos: d.pos,
                    end: d.end,
                    code: d.code,
                    category: d.category,
                    message_key: d.message_key.clone(),
                    message_args: d.message_args.clone().unwrap_or_default(),
                    message_chain: self
                        .to_build_info_diagnostics_with_file_name(d.message_chain.as_ref()),
                    related_information: self
                        .to_build_info_diagnostics_with_file_name(d.related_information.as_ref()),
                    reports_unnecessary: d.reports_unnecessary,
                    reports_deprecated: d.reports_deprecated,
                    skipped_on_no_emit: d.skipped_on_no_emit,
                    repopulate_info: from_build_info_repopulate_info(d.repopulate_info.as_ref()),
                }
            })
            .collect()
    }

    // Go: incremental/buildinfotosnapshot.go:95 toDiagnosticsOrBuildInfoDiagnosticsWithFileName
    fn to_diagnostics_or_build_info_diagnostics_with_file_name(
        &self,
        dig: &BuildInfoDiagnosticsOfFile,
    ) -> DiagnosticsOrBuildInfoDiagnosticsWithFileName {
        DiagnosticsOrBuildInfoDiagnosticsWithFileName {
            diagnostics: None,
            build_info_diagnostics: self
                .to_build_info_diagnostics_with_file_name(Some(&dig.diagnostics)),
            // PORT: testing (see `DiagnosticsOrBuildInfoDiagnosticsWithFileName`)
            id: new_diagnostics_id(),
        }
    }

    // Go: incremental/buildinfotosnapshot.go:113 setCompilerOptions
    fn set_compiler_options(&mut self) {
        let options = self
            .build_info
            .get_compiler_options(&self.build_info_directory);
        self.snapshot.options = Box::leak(Box::new(options));
    }

    // Go: incremental/buildinfotosnapshot.go:117 setFileInfoAndEmitSignatures
    fn set_file_info_and_emit_signatures(&mut self) {
        let is_composite = self.snapshot.options.composite.is_true();
        for (index, build_info_file_info) in self.build_info.file_infos.iter().flatten().enumerate()
        {
            let path = self.to_file_path(BuildInfoFileId(index as i32 + 1));
            let info = build_info_file_info.get_file_info();
            // Add default emit signature as file's signature
            if !info.signature.is_empty() && is_composite {
                self.snapshot.emit_signatures.insert(
                    path.clone(),
                    EmitSignature {
                        signature: info.signature.clone(),
                        signature_with_different_options: None,
                    },
                );
            }
            self.snapshot.file_infos.insert(path, info);
        }
        // Fix up emit signatures
        for value in self.build_info.emit_signatures.iter().flatten() {
            if value.no_emit_signature() {
                self.snapshot
                    .emit_signatures
                    .remove(&self.to_file_path(value.file_id));
            } else {
                let path = self.to_file_path(value.file_id);
                let emit_signature = value.to_emit_signature(&path, &self.snapshot.emit_signatures);
                self.snapshot.emit_signatures.insert(path, emit_signature);
            }
        }
    }

    // Go: incremental/buildinfotosnapshot.go:138 setReferencedMap
    fn set_referenced_map(&mut self) {
        for entry in self.build_info.referenced_map.iter().flatten() {
            let path = self.to_file_path(entry.file_id);
            let set = self.to_file_path_set(entry.file_id_list_id);
            self.snapshot.referenced_map.store_references(path, set);
        }
    }

    // Go: incremental/buildinfotosnapshot.go:144 setChangeFileSet
    fn set_change_file_set(&mut self) {
        for &file_id in self.build_info.change_file_set.iter().flatten() {
            let file_path = self.to_file_path(file_id);
            self.snapshot.changed_files_set.insert(file_path);
        }
    }

    // Go: incremental/buildinfotosnapshot.go:151 setSemanticDiagnostics
    fn set_semantic_diagnostics(&mut self) {
        let paths: Vec<Path> = self.snapshot.file_infos.keys().cloned().collect();
        for path in paths {
            // Initialize to have no diagnostics if its not changed file
            if !self.snapshot.changed_files_set.contains(&path) {
                self.snapshot.semantic_diagnostics_per_file.insert(
                    path,
                    DiagnosticsOrBuildInfoDiagnosticsWithFileName::default(),
                );
            }
        }
        for diagnostic in self
            .build_info
            .semantic_diagnostics_per_file
            .iter()
            .flatten()
        {
            if diagnostic.file_id.0 != 0 {
                let file_path = self.to_file_path(diagnostic.file_id);
                self.snapshot
                    .semantic_diagnostics_per_file
                    .shift_remove(&file_path); // does not have cached diagnostics
            } else {
                let diagnostics = diagnostic
                    .diagnostics
                    .as_ref()
                    .expect("BuildInfoSemanticDiagnostic without fileId has diagnostics");
                let file_path = self.to_file_path(diagnostics.file_id);
                let value =
                    self.to_diagnostics_or_build_info_diagnostics_with_file_name(diagnostics);
                self.snapshot
                    .semantic_diagnostics_per_file
                    .insert(file_path, value);
            }
        }
    }

    // Go: incremental/buildinfotosnapshot.go:169 setEmitDiagnostics
    fn set_emit_diagnostics(&mut self) {
        for diagnostic in self.build_info.emit_diagnostics_per_file.iter().flatten() {
            let file_path = self.to_file_path(diagnostic.file_id);
            let value = self.to_diagnostics_or_build_info_diagnostics_with_file_name(diagnostic);
            self.snapshot
                .emit_diagnostics_per_file
                .insert(file_path, value);
        }
    }

    // Go: incremental/buildinfotosnapshot.go:176 setAffectedFilesPendingEmit
    fn set_affected_files_pending_emit(&mut self) {
        let Some(affected_files_pending_emit) = self
            .build_info
            .affected_files_pending_emit
            .as_ref()
            .filter(|list| !list.is_empty())
        else {
            return;
        };
        let own_options_emit_kind = get_file_emit_kind(self.snapshot.options);
        for pending_emit in affected_files_pending_emit {
            let path = self.to_file_path(pending_emit.file_id);
            self.snapshot.affected_files_pending_emit.insert(
                path,
                if pending_emit.emit_kind.is_empty() {
                    own_options_emit_kind
                } else {
                    pending_emit.emit_kind
                },
            );
        }
    }
}

// Go: incremental/buildinfotosnapshot.go:101 fromBuildInfoRepopulateInfo
#[must_use]
pub fn from_build_info_repopulate_info(
    info: Option<&BuildInfoRepopulateInfo>,
) -> Option<RepopulateInfoRef> {
    let info = info?;
    Some(RepopulateInfoRef::new(RepopulateDiagnosticInfo {
        kind: info.kind,
        module_reference: info.module_reference.clone(),
        mode: info.mode,
        package_name: info.package_name.clone(),
    }))
}
