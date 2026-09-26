//! Port of Go `ls/crossproject.go`.
//!
//! PORT notes for the whole file:
//! - Go runs the per-project searches on a parallel `core.WorkGroup` and
//!   shares `results`, `defaultDefinition`, `err` and `panicsOccured` under
//!   mutexes. Language-service state lives on the dispatch thread, so the
//!   searches run serially in Go start order (queue order), and the shared
//!   locals are `RefCell` fields of one `CrossProjectState` value. The Go
//!   closures `canSearchProject`, `enqueueItem` and the queued function are
//!   methods of that value.
//! - Go `collections.SyncMap.Range` order is random. `results` is an
//!   `IndexMap` in insertion order. Multi-project result order can differ
//!   from Go; the oracle compares it without order.
//! - Go `iter.Seq[Resp]` passed to `combineResults` is the slice of the
//!   values the iterator yields, in the same order. Go restarts the iterator
//!   when a combiner ranges over it again; here the combiner reads the slice
//!   again.

use crate::ls::prelude::*;

use crate::frontend::compiler;
use crate::frontend::tspath;
use crate::gostd::{Context, GoError};
use crate::lsp::lsproto;
use crate::lsp::lsproto::{HasLocation, HasLocations, HasTextDocumentPosition, HasTextDocumentURI};
use std::collections::VecDeque;
use std::panic::AssertUnwindSafe;

/// Go runtime panic text for a nil pointer dereference.
const NIL_DEREF: &str = "runtime error: invalid memory address or nil pointer dereference";

// Go: ls/crossproject.go:17 Project
// PORT: plan contract C4. Go `*compiler.Program` is
// `&'static compiler::NewProgram`, which is never nil.
pub trait Project {
    fn id(&self) -> tspath::Path;
    fn get_program(&self) -> &'static compiler::NewProgram;
    fn has_file(&self, file_name: &str) -> bool;
}

// Go: ls/crossproject.go:23 projectAndTextDocumentPosition
// PORT: Go `Project` values are `Rc<dyn Project>`; Go interface equality is
// `Rc::ptr_eq`. Go `ls *LanguageService` is set only for the default
// project (the caller's language service), so it is a borrow.
pub struct ProjectAndTextDocumentPosition<'l> {
    pub project: Rc<dyn Project>,
    pub ls: Option<&'l LanguageService>,
    pub uri: lsproto::DocumentUri,
    pub position: lsproto::Position,
    pub for_original_location: bool,
}

// Go: ls/crossproject.go:31 response
#[derive(Clone, Debug, Default)]
pub struct Response<Resp> {
    pub complete: bool,
    pub result: Resp,
    pub for_original_location: bool,
}

// Go: ls/crossproject.go:37 CrossProjectOrchestrator
// PORT: Go `*LanguageService` results are new language services owned by
// the caller (`Option` for nil). Go `iter.Seq[Project]` is a push iterator:
// `yield_` gets each project and returns false to stop.
pub trait CrossProjectOrchestrator {
    fn get_default_project(&self) -> Rc<dyn Project>;
    fn get_all_projects_for_initial_request(&self) -> Vec<Rc<dyn Project>>;
    fn get_language_service_for_project_with_file(
        &self,
        ctx: &Context,
        project: &Rc<dyn Project>,
        uri: &lsproto::DocumentUri,
    ) -> Option<LanguageService>;
    fn get_projects_for_file(
        &self,
        ctx: &Context,
        uri: &lsproto::DocumentUri,
    ) -> Result<Vec<Rc<dyn Project>>, GoError>;
    fn get_projects_loading_project_tree(
        &self,
        ctx: &Context,
        requested_project_trees: &FxHashSet<tspath::Path>,
        yield_: &mut dyn FnMut(Rc<dyn Project>) -> bool,
    );
}

/// Go `symbolAndEntriesToResp func(*LanguageService, context.Context, Req, SymbolAndEntriesData, symbolEntryTransformOptions) (Resp, error)`.
pub type SymbolAndEntriesToResp<Req, Resp> = fn(
    &LanguageService,
    &Context,
    &Req,
    SymbolAndEntriesData,
    SymbolEntryTransformOptions,
) -> Result<Resp, GoError>;

// Go: ls/crossproject.go:45 handleCrossProject
// PORT: Go `params Req` is a pointer type: `&Req`. Go `orchestrator` can be
// nil: `Option<&dyn CrossProjectOrchestrator>`. Go
// `combineResults func(iter.Seq[Resp]) Resp` takes the yielded values as a
// slice (see the file header).
pub fn handle_cross_project<Req, Resp>(
    default_ls: &LanguageService,
    ctx: &Context,
    params: &Req,
    orchestrator: Option<&dyn CrossProjectOrchestrator>,
    symbol_and_entries_to_resp: SymbolAndEntriesToResp<Req, Resp>,
    combine_results: fn(&[Resp]) -> Resp,
    is_rename: bool,
    implementations: bool,
    options: SymbolEntryTransformOptions,
) -> Result<Resp, GoError>
where
    Req: HasTextDocumentPosition,
    Resp: Clone + Default,
{
    let mut resp = Resp::default();

    // Single project
    let Some(orchestrator) = orchestrator else {
        let (data, _) = default_ls.provide_symbols_and_entries(
            ctx,
            &params.text_document_uri(),
            params.text_document_position(),
            is_rename,
            implementations,
        );
        return symbol_and_entries_to_resp(default_ls, ctx, params, data, options);
    };

    let default_project = orchestrator.get_default_project();
    let all_projects = orchestrator.get_all_projects_for_initial_request();
    let state = CrossProjectState {
        ctx,
        params,
        orchestrator,
        symbol_and_entries_to_resp,
        is_rename,
        implementations,
        options,
        default_project,
        all_projects,
        results: RefCell::new(IndexMap::new()),
        default_definition: RefCell::new(None),
        wg: RefCell::new(VecDeque::new()),
        err: RefCell::new(None),
        panics_occured: RefCell::new(None),
    };

    // Initial set of projects and locations in the queue, starting with default project
    state.enqueue_item(ProjectAndTextDocumentPosition {
        project: Rc::clone(&state.default_project),
        ls: Some(default_ls),
        uri: params.text_document_uri(),
        position: params.text_document_position(),
        for_original_location: false,
    });
    for project in &state.all_projects {
        if !Rc::ptr_eq(project, &state.default_project) {
            state.enqueue_item(ProjectAndTextDocumentPosition {
                project: Rc::clone(project),
                ls: None,
                // TODO!! symlinks need to change the URI
                uri: params.text_document_uri(),
                position: params.text_document_position(),
                for_original_location: false,
            });
        }
    }

    // Outer loop - to complete work if more is added after completing existing queue
    loop {
        // Process existing known projects first
        state.run_and_wait();
        // No need to use mu here since we are not in parallel at this point
        if let Some(panics_occured) = state.panics_occured.borrow().as_ref() {
            // PORT: Go `%v` of a `[]string`.
            panic!(
                "Panics occurred during cross-project handling: [{}]",
                panics_occured.join(" ")
            );
        }
        if let Some(err) = ctx.err() {
            return Err(err);
        }
        if let Some(err) = state.err.borrow().clone() {
            return Err(err);
        }

        // Go: wg = core.NewWorkGroup(false)
        // PORT: the serial queue is empty after `run_and_wait`.
        let mut has_more_work = false;
        if state.default_definition.borrow().is_some() {
            let mut requested_project_trees: FxHashSet<tspath::Path> = FxHashSet::default();
            for (key, response) in state.results.borrow().iter() {
                if response.borrow().complete {
                    requested_project_trees.insert(key.clone());
                }
            }

            // Load more projects based on default definition found
            // PORT: Go returns from inside the range loop; the push iterator
            // stops (`false`) and the error is returned after it.
            let mut ctx_err: Option<GoError> = None;
            orchestrator.get_projects_loading_project_tree(
                ctx,
                &requested_project_trees,
                &mut |loaded_project: Rc<dyn Project>| {
                    if let Some(err) = ctx.err() {
                        ctx_err = Some(err);
                        return false;
                    }

                    // Can loop forever without this (enqueue here, dequeue above, repeat)
                    // PORT: Go also skips a project whose `GetProgram()` is
                    // nil. The `Project` contract (plan C4) returns a
                    // program that is never nil, so that test is always
                    // false here.
                    if !state.can_search_project(&loaded_project) {
                        return true;
                    }

                    // Enqueue the project and location for further processing
                    let default_definition = state.default_definition.borrow();
                    let default_definition = default_definition.as_ref().expect(NIL_DEREF);
                    if loaded_project.has_file(&default_definition.text_document_uri().file_name())
                    {
                        state.enqueue_item(ProjectAndTextDocumentPosition {
                            project: loaded_project,
                            ls: None,
                            uri: default_definition.text_document_uri(),
                            position: default_definition.text_document_position(),
                            for_original_location: false,
                        });
                        has_more_work = true;
                    } else if let Some(source_pos) = (default_definition.get_source_position)()
                        && loaded_project.has_file(&source_pos.text_document_uri().file_name())
                    {
                        state.enqueue_item(ProjectAndTextDocumentPosition {
                            project: loaded_project,
                            ls: None,
                            uri: source_pos.text_document_uri(),
                            position: source_pos.text_document_position(),
                            for_original_location: false,
                        });
                        has_more_work = true;
                    } else if let Some(generated_pos) =
                        (default_definition.get_generated_position)()
                        && loaded_project.has_file(&generated_pos.text_document_uri().file_name())
                    {
                        state.enqueue_item(ProjectAndTextDocumentPosition {
                            project: loaded_project,
                            ls: None,
                            uri: generated_pos.text_document_uri(),
                            position: generated_pos.text_document_position(),
                            for_original_location: false,
                        });
                        has_more_work = true;
                    }
                    true
                },
            );
            if let Some(err) = ctx_err {
                return Err(err);
            }
        }
        if !has_more_work {
            break;
        }
    }

    let results_size = state.results.borrow().len();
    if results_size > 1 {
        resp = combine_results(&state.get_results_iterator());
    } else {
        // Single result, return that directly
        if let Some(value) = state.get_results_iterator().into_iter().next() {
            resp = value;
        }
    }
    Ok(resp)
}

/// The locals of Go `handleCrossProject` that its closures share.
struct CrossProjectState<'a, Req, Resp> {
    ctx: &'a Context,
    params: &'a Req,
    orchestrator: &'a dyn CrossProjectOrchestrator,
    symbol_and_entries_to_resp: SymbolAndEntriesToResp<Req, Resp>,
    is_rename: bool,
    implementations: bool,
    options: SymbolEntryTransformOptions,
    default_project: Rc<dyn Project>,
    all_projects: Vec<Rc<dyn Project>>,
    /// Go `results collections.SyncMap[tspath.Path, *response[Resp]]`.
    results: RefCell<IndexMap<tspath::Path, Rc<RefCell<Response<Resp>>>>>,
    /// Go `defaultDefinition *nonLocalDefinition`.
    default_definition: RefCell<Option<NonLocalDefinition<'a>>>,
    /// Go `wg`: the queued items with the response each one fills.
    wg: RefCell<
        VecDeque<(
            ProjectAndTextDocumentPosition<'a>,
            Rc<RefCell<Response<Resp>>>,
        )>,
    >,
    /// Go `err` (under `errMu`).
    err: RefCell<Option<GoError>>,
    /// Go `panicsOccured` (under `panicMu`); `None` is Go's nil slice.
    panics_occured: RefCell<Option<Vec<String>>>,
}

impl<'a, Req, Resp> CrossProjectState<'a, Req, Resp>
where
    Req: HasTextDocumentPosition,
    Resp: Clone + Default,
{
    // Go: ls/crossproject.go:69 canSearchProject (closure)
    fn can_search_project(&self, project: &Rc<dyn Project>) -> bool {
        let searched = self.results.borrow().contains_key(&project.id());
        !searched
    }

    // Go: ls/crossproject.go:78 enqueueItem (closure)
    fn enqueue_item(&self, item: ProjectAndTextDocumentPosition<'a>) {
        let response = Rc::new(RefCell::new(Response::<Resp>::default()));
        {
            // Go: results.LoadOrStore(item.project.Id(), &response)
            let mut results = self.results.borrow_mut();
            let id = item.project.id();
            if results.contains_key(&id) {
                return;
            }
            results.insert(id, Rc::clone(&response));
        }
        // Go: wg.Queue(func() { ... })
        self.wg.borrow_mut().push_back((item, response));
    }

    // Go: wg.RunAndWait()
    // PORT: runs the queued items serially in queue order, including items
    // queued while it runs.
    fn run_and_wait(&self) {
        loop {
            let next = self.wg.borrow_mut().pop_front();
            let Some((item, response)) = next else {
                return;
            };
            self.run_queued_item(item, &response);
        }
    }

    // Go: ls/crossproject.go:83 the function that enqueueItem queues
    fn run_queued_item(
        &self,
        item: ProjectAndTextDocumentPosition<'a>,
        response: &Rc<RefCell<Response<Resp>>>,
    ) {
        if self.ctx.err().is_some() {
            return;
        }
        // Go: defer func() { if r := recover(); r != nil { ... } }()
        let result =
            std::panic::catch_unwind(AssertUnwindSafe(|| self.process_item(item, response)));
        if let Err(r) = result {
            let text = if let Some(s) = r.downcast_ref::<&str>() {
                (*s).to_string()
            } else if let Some(s) = r.downcast_ref::<String>() {
                s.clone()
            } else {
                format!("{r:?}")
            };
            // PORT: Go `debug.Stack()`; the text is only logged.
            let stack = std::backtrace::Backtrace::force_capture();
            let panic_occured = format!("panic handling request: {text}\n{stack}");
            self.panics_occured
                .borrow_mut()
                .get_or_insert_with(Vec::new)
                .push(panic_occured);
        }
    }

    // Go: ls/crossproject.go:96 the body of the queued function after its
    // deferred recover
    fn process_item(
        &self,
        item: ProjectAndTextDocumentPosition<'a>,
        response: &Rc<RefCell<Response<Resp>>>,
    ) {
        let ctx = self.ctx;
        // Process the item
        let ls_holder: LanguageService;
        let ls: &LanguageService = match item.ls {
            Some(ls) => ls,
            None => {
                // Get it now
                match self
                    .orchestrator
                    .get_language_service_for_project_with_file(ctx, &item.project, &item.uri)
                {
                    Some(ls) => {
                        ls_holder = ls;
                        &ls_holder
                    }
                    None => return,
                }
            }
        };
        let (data, ok) = ls.provide_symbols_and_entries(
            ctx,
            &item.uri,
            item.position,
            self.is_rename,
            self.implementations,
        );
        if ctx.err().is_some() {
            return;
        }
        if ok {
            for entry in &data.symbols_and_entries {
                // Find the default definition that can be in another project
                // Later we will use this load ancestor tree that references this location and expand search
                if Rc::ptr_eq(&item.project, &self.default_project)
                    && self.default_definition.borrow().is_none()
                {
                    // PORT: `NonLocalDefinition` borrows the language service
                    // that made it. `results` keeps one item per project id
                    // and the default project's item is queued first with
                    // `defaultLs`, so `ls` is `item.ls` here.
                    let default_ls = item
                        .ls
                        .expect("the default project item carries the default language service");
                    let default_definition = default_ls.get_non_local_definition(ctx, entry);
                    *self.default_definition.borrow_mut() = default_definition;
                }
                ls.for_each_original_definition_location(ctx, entry, &mut |uri, position| {
                    // Get default configured project for this file
                    let def_projects = match self.orchestrator.get_projects_for_file(ctx, &uri) {
                        Ok(def_projects) => def_projects,
                        Err(_) => return,
                    };
                    for def_project in def_projects {
                        // Optimization: don't enqueue if will be discarded
                        if self.can_search_project(&def_project) {
                            self.enqueue_item(ProjectAndTextDocumentPosition {
                                project: def_project,
                                ls: None,
                                uri: uri.clone(),
                                position,
                                for_original_location: true,
                            });
                        }
                    }
                });
            }
        }

        match (self.symbol_and_entries_to_resp)(ls, ctx, self.params, data, self.options) {
            Ok(result) => {
                let mut response = response.borrow_mut();
                response.complete = true;
                response.result = result;
                response.for_original_location = item.for_original_location;
            }
            Err(err_search) => {
                let mut err = self.err.borrow_mut();
                if err.is_none() {
                    *err = Some(err_search);
                }
            }
        }
    }

    // Go: ls/crossproject.go:169 getResultsIterator (closure)
    // PORT: returns the values the Go iterator yields, in order.
    fn get_results_iterator(&self) -> Vec<Resp> {
        let mut yielded: Vec<Resp> = Vec::new();
        let results = self.results.borrow();
        let mut seen_projects: FxHashSet<tspath::Path> = FxHashSet::default();
        if let Some(response) = results.get(&self.default_project.id()) {
            let response = response.borrow();
            if response.complete {
                yielded.push(response.result.clone());
            }
        }
        seen_projects.insert(self.default_project.id());
        for project in &self.all_projects {
            if seen_projects.insert(project.id())
                && let Some(response) = results.get(&project.id())
            {
                let response = response.borrow();
                if response.complete {
                    yielded.push(response.result.clone());
                }
            }
        }
        // Prefer the searches from locations for default definition
        for (key, response) in results.iter() {
            let response = response.borrow();
            if !response.for_original_location
                && seen_projects.insert(key.clone())
                && response.complete
            {
                yielded.push(response.result.clone());
            }
        }
        // Then the searches from original locations
        for (key, response) in results.iter() {
            let response = response.borrow();
            if response.for_original_location
                && seen_projects.insert(key.clone())
                && response.complete
            {
                yielded.push(response.result.clone());
            }
        }
        yielded
    }
}

// Go: ls/crossproject.go:283 combineLocationArray
// PORT: Go `locations *[]T` is read only: `&[T]`.
pub fn combine_location_array<T: HasLocation + Clone>(
    mut combined: Vec<T>,
    locations: &[T],
    seen: &mut FxHashSet<lsproto::Location>,
) -> Vec<T> {
    for loc in locations {
        if seen.insert(loc.get_location()) {
            combined.push(loc.clone());
        }
    }
    combined
}

// Go: ls/crossproject.go:296 combineResponseLocations
// PORT: Go returns a non-nil `*[]lsproto.Location`: always `Some`.
pub fn combine_response_locations<T: HasLocations>(
    results: &[T],
) -> Option<Vec<lsproto::Location>> {
    let mut combined: Vec<lsproto::Location> = Vec::new();
    let mut seen_locations: FxHashSet<lsproto::Location> = FxHashSet::default();
    for resp in results {
        if let Some(locations) = resp.get_locations() {
            combined = combine_location_array(combined, locations, &mut seen_locations);
        }
    }
    Some(combined)
}

// Go: ls/crossproject.go:307 combineReferences
pub fn combine_references(results: &[lsproto::ReferencesResponse]) -> lsproto::ReferencesResponse {
    lsproto::LocationsOrNull {
        locations: combine_response_locations(results),
    }
}

// Go: ls/crossproject.go:311 combineVSReferences
pub fn combine_vs_references(
    results: &[lsproto::VSReferencesResponse],
) -> lsproto::VSReferencesResponse {
    let mut combined: Vec<lsproto::VSReferenceItem> = Vec::new();
    // Re-number IDs across projects to maintain unique IDs and correct definition references
    let mut next_id: i32 = 0;
    for resp in results {
        let Some(vs_reference_items) = &resp.vs_reference_items else {
            continue;
        };
        // Map old IDs to new IDs for this batch
        let mut id_map: FxHashMap<i32, i32> = FxHashMap::default();
        for item in vs_reference_items {
            let old_id = item.vs_id;
            let new_id = next_id;
            id_map.insert(old_id, new_id);
            next_id += 1;

            let mut new_item = item.clone();
            new_item.vs_id = new_id;
            if let Some(vs_definition_id) = item.vs_definition_id {
                let new_def_id = id_map.get(&vs_definition_id).copied().unwrap_or_default();
                new_item.vs_definition_id = Some(new_def_id);
            }
            combined.push(new_item);
        }
    }
    lsproto::VSReferenceItemsOrNull {
        vs_reference_items: Some(combined),
    }
}

// Go: ls/crossproject.go:339 combineImplementations
pub fn combine_implementations(
    results: &[lsproto::ImplementationResponse],
) -> lsproto::ImplementationResponse {
    let mut combined: Vec<lsproto::LocationLink> = Vec::new();
    let mut seen_locations: FxHashSet<lsproto::Location> = FxHashSet::default();
    for resp in results {
        if let Some(definition_links) = &resp.definition_links {
            combined = combine_location_array(combined, definition_links, &mut seen_locations);
        } else if resp.locations.is_some() {
            return lsproto::LocationOrLocationsOrDefinitionLinksOrNull {
                locations: combine_response_locations(results),
                ..Default::default()
            };
        }
    }
    lsproto::LocationOrLocationsOrDefinitionLinksOrNull {
        definition_links: Some(combined),
        ..Default::default()
    }
}

// Go: ls/crossproject.go:352 combineRenameResponse
// PORT: Go `combined` is a Go map, which the response marshals in random
// order. It is an `IndexMap` in first-insert order. Go ranges over each
// response's `Changes` map in random order; this uses its insertion order.
pub fn combine_rename_response(results: &[lsproto::RenameResponse]) -> lsproto::RenameResponse {
    let mut combined: IndexMap<lsproto::DocumentUri, Vec<lsproto::TextEdit>> = IndexMap::new();
    let mut seen_changes: FxHashMap<lsproto::DocumentUri, FxHashSet<lsproto::Range>> =
        FxHashMap::default();
    let mut document_changes: Vec<lsproto::TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile> =
        Vec::new();
    let mut seen_renames: FxHashSet<[lsproto::DocumentUri; 2]> = FxHashSet::default();

    for resp in results {
        if let Some(workspace_edit) = &resp.workspace_edit
            && let Some(changes) = &workspace_edit.document_changes
        {
            for change in changes {
                match &change.rename_file {
                    Some(rename_file) => {
                        let key = [rename_file.old_uri.clone(), rename_file.new_uri.clone()];
                        if seen_renames.insert(key) {
                            document_changes.push(change.clone());
                        }
                    }
                    None => {
                        document_changes.push(change.clone());
                    }
                }
            }
        }
        if let Some(workspace_edit) = &resp.workspace_edit
            && let Some(changes_by_doc) = &workspace_edit.changes
        {
            for (doc, changes) in changes_by_doc {
                let seen_set = seen_changes.entry(doc.clone()).or_default();
                let mut changes_for_doc = combined.get(doc).cloned().unwrap_or_default();
                for change in changes {
                    if !seen_set.contains(&change.range) {
                        seen_set.insert(change.range);
                        changes_for_doc.push(change.clone());
                    }
                }
                combined.insert(doc.clone(), changes_for_doc);
            }
        }
    }
    if !document_changes.is_empty() || !combined.is_empty() {
        let mut workspace_edit = lsproto::WorkspaceEdit::default();
        if !document_changes.is_empty() {
            workspace_edit.document_changes = Some(document_changes);
        }
        if !combined.is_empty() {
            workspace_edit.changes = Some(combined);
        }
        return lsproto::WorkspaceEditOrNull {
            workspace_edit: Some(workspace_edit),
        };
    }
    lsproto::WorkspaceEditOrNull::default()
}

// Go: ls/crossproject.go:408 combineIncomingCalls
pub fn combine_incoming_calls(
    results: &[lsproto::CallHierarchyIncomingCallsResponse],
) -> lsproto::CallHierarchyIncomingCallsResponse {
    let mut combined: Vec<lsproto::CallHierarchyIncomingCall> = Vec::new();
    let mut seen_calls: FxHashSet<lsproto::Location> = FxHashSet::default();
    for resp in results {
        if let Some(call_hierarchy_incoming_calls) = &resp.call_hierarchy_incoming_calls {
            for call in call_hierarchy_incoming_calls {
                if seen_calls.insert(call.from.as_ref().expect(NIL_DEREF).get_location()) {
                    combined.push(call.clone());
                }
            }
        }
    }
    lsproto::CallHierarchyIncomingCallsOrNull {
        call_hierarchy_incoming_calls: Some(combined),
    }
}
