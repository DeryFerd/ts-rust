use crate::api::prelude::*;

// Port of Go `internal/api/session.go`, lines 1272-2484: the
// `resolve*PropertyOf*` helpers, the checker query handlers, node building
// and printing, emit (tsgo#4699), intrinsic types, diagnostics, `resolveNodeHandle`,
// `computeSnapshotChanges`, `Close`, and the references, signature usage and
// completion handlers. The file header of `session_p1.rs` holds the PORT
// notes for both files (registry entries keep the owning checker; handles
// cross to the setup checker only through `checker_symbol`, `checker_type`
// and `checker_signature`).

use crate::api::encoder;
use crate::emitter::emitter::EmitOnly;
use crate::emitter::program_emit::{self, EmitOptions, EmitResult, WriteFile, WriteFileData};
use crate::execute::incremental::emit_files::fs_error_text;
use crate::frontend::compiler;
use crate::frontend::core_context::{self, CheckerLifetime};
use crate::frontend::core_ls_ext::{diff_maps, diff_ordered_maps};
use crate::frontend::json_ext::AnyValue;
use crate::frontend::parser::ParsedSourceFile;
use crate::frontend::tspath;
use crate::frontend::vfs::Fs as _;
use crate::gostd::{self, Context, GoError, errors};
use crate::program::ls_program;
use crate::project;
use std::sync::{Arc, Mutex, PoisonError};

impl Session {
    // Go: api/session.go:1273 resolveTypePropertyOfType
    // resolveTypePropertyOfType resolves a type property of type `Type` and returns a type response.
    // PORT: the getter reads the type in the arena of its checker.
    pub fn resolve_type_property_of_type(
        &self,
        params: &GetTypePropertyParams,
        getter: &dyn Fn(&Checker, TypeId) -> TypeId,
    ) -> Result<Option<TypeResponse>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let (checker, t) = sd.resolve_type_handle(&params.project, params.type_)?;
        // Node handles in the answer read lazy JSDoc (session_p1.rs header).
        let _program = ls_program::enter_version(checker.borrow().program);

        let result = getter(&checker.borrow(), t);
        if result.is_nil() {
            return Ok(None);
        }

        Ok(sd.new_type_response(&params.project, &checker, result))
    }

    // Go: api/session.go:1293 resolveTypeArrayPropertyOfType
    // resolveTypeArrayPropertyOfType resolves a type property of an array of types and returns an array of type responses.
    pub fn resolve_type_array_property_of_type(
        &self,
        params: &GetTypePropertyParams,
        getter: &dyn Fn(&Checker, TypeId) -> Vec<TypeId>,
    ) -> Result<Vec<Option<TypeResponse>>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let (checker, t) = sd.resolve_type_handle(&params.project, params.type_)?;
        // Node handles in the answer read lazy JSDoc (session_p1.rs header).
        let _program = ls_program::enter_version(checker.borrow().program);

        let types = getter(&checker.borrow(), t);
        if types.is_empty() {
            return Ok(Vec::new());
        }

        let mut results = Vec::with_capacity(types.len());
        for sub in types {
            results.push(sd.new_type_response(&params.project, &checker, sub));
        }
        Ok(results)
    }

    // Go: api/session.go:1317 resolveSymbolPropertyOfType
    // resolveSymbolPropertyOfType resolves a type property of type `Symbol` and returns a symbol response.
    pub fn resolve_symbol_property_of_type(
        &self,
        params: &GetTypePropertyParams,
        getter: &dyn Fn(&Checker, TypeId) -> SymbolId,
    ) -> Result<Option<SymbolResponse>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let (checker, t) = sd.resolve_type_handle(&params.project, params.type_)?;
        // Node handles in the answer read lazy JSDoc (session_p1.rs header).
        let _program = ls_program::enter_version(checker.borrow().program);

        let result = getter(&checker.borrow(), t);
        if result.is_nil() {
            return Ok(None);
        }
        Ok(sd.new_symbol_response(&checker, result, &params.project))
    }

    // Go: api/session.go:1336 resolveSymbolPropertyOfSymbol
    // resolveSymbolTablePropertyOfSymbol resolves a symbol property of type `Symbol` and returns a symbol response.
    pub fn resolve_symbol_property_of_symbol(
        &self,
        params: &GetSymbolPropertyParams,
        getter: &dyn Fn(&Checker, SymbolId) -> SymbolId,
    ) -> Result<Option<SymbolResponse>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let (checker, symbol) = sd.resolve_symbol_handle(params.symbol)?;
        // Node handles in the answer read lazy JSDoc (session_p1.rs header).
        let _program = ls_program::enter_version(checker.borrow().program);

        let result = getter(&checker.borrow(), symbol);
        if result.is_nil() {
            return Ok(None);
        }
        Ok(sd.new_symbol_response(&checker, result, &params.project))
    }

    // Go: api/session.go:1681 resolveSymbolTablePropertyOfSymbol
    // resolveSymbolTablePropertyOfSymbol resolves a symbol property of type `SymbolTable` and returns an array of symbol responses.
    // Results are sorted using the checker's canonical symbol ordering so that API consumers receive
    // a stable, deterministic order instead of Go's randomized map iteration order.
    pub fn resolve_symbol_table_property_of_symbol(
        &self,
        ctx: &Context,
        params: &GetSymbolPropertyParams,
        getter: &dyn Fn(&Checker, SymbolId) -> SymbolTable,
    ) -> Result<Vec<Option<SymbolResponse>>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let (checker, symbol) = sd.resolve_symbol_handle(params.symbol)?;
        // Node handles in the answer read lazy JSDoc (session_p1.rs header).
        let _program = ls_program::enter_version(checker.borrow().program);

        let symbol_table = getter(&checker.borrow(), symbol);
        let table_len = checker.borrow().symbols.len(symbol_table);
        if symbol_table.is_nil() || table_len == 0 {
            return Ok(Vec::new());
        }
        let subs = checker.borrow().symbols.values(symbol_table);
        if table_len == 1 {
            return Ok(vec![sd.new_symbol_response(
                &checker,
                subs[0],
                &params.project,
            )]);
        }

        // More than one symbol, need a checker to sort
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let mut symbols: Vec<SymbolId> = Vec::with_capacity(table_len);
        for sub in subs {
            symbols.push(checker_symbol(&setup.checker, &checker, sub));
        }
        // PORT: Go `slices.SortFunc` is not stable; `compareSymbols` gives
        // distinct symbols distinct places, so the order is the same.
        {
            let mut c = setup.checker.borrow_mut();
            symbols.sort_by(|&a, &b| c.compare_symbols_exported(a, b).cmp(&0));
        }

        let mut results = Vec::with_capacity(symbols.len());
        for sub in symbols {
            results.push(setup.new_symbol_response(sub));
        }
        Ok(results)
    }

    // Go: api/session.go:1379 resolveSymbolArrayPropertyOfSignature
    // resolveSymbolArrayPropertyOfSignature resolves a signature property of an array of symbols and returns an array of symbol responses.
    pub fn resolve_symbol_array_property_of_signature(
        &self,
        params: &GetSignaturePropertyParams,
        getter: &dyn Fn(&Checker, SignatureId) -> Vec<SymbolId>,
    ) -> Result<Vec<Option<SymbolResponse>>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let (checker, sig) = sd.resolve_signature_handle(&params.project, params.signature)?;
        // Node handles in the answer read lazy JSDoc (session_p1.rs header).
        let _program = ls_program::enter_version(checker.borrow().program);

        let symbols = getter(&checker.borrow(), sig);
        if symbols.is_empty() {
            return Ok(Vec::new());
        }

        let mut results = Vec::with_capacity(symbols.len());
        for sym in symbols {
            results.push(sd.new_symbol_response(&checker, sym, &params.project));
        }
        Ok(results)
    }

    // Go: api/session.go:1403 resolveSymbolPropertyOfSignature
    // resolveSymbolPropertyOfSignature resolves a signature property of type `Symbol` and returns a symbol response.
    pub fn resolve_symbol_property_of_signature(
        &self,
        params: &GetSignaturePropertyParams,
        getter: &dyn Fn(&Checker, SignatureId) -> SymbolId,
    ) -> Result<Option<SymbolResponse>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let (checker, sig) = sd.resolve_signature_handle(&params.project, params.signature)?;
        // Node handles in the answer read lazy JSDoc (session_p1.rs header).
        let _program = ls_program::enter_version(checker.borrow().program);

        let result = getter(&checker.borrow(), sig);
        if result.is_nil() {
            return Ok(None);
        }
        Ok(sd.new_symbol_response(&checker, result, &params.project))
    }

    // Go: api/session.go:1421 resolveTypeArrayPropertyOfSignature
    pub fn resolve_type_array_property_of_signature(
        &self,
        params: &GetSignaturePropertyParams,
        getter: &dyn Fn(&Checker, SignatureId) -> Vec<TypeId>,
    ) -> Result<Vec<Option<TypeResponse>>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let (checker, sig) = sd.resolve_signature_handle(&params.project, params.signature)?;
        // Node handles in the answer read lazy JSDoc (session_p1.rs header).
        let _program = ls_program::enter_version(checker.borrow().program);

        let types = getter(&checker.borrow(), sig);
        if types.is_empty() {
            return Ok(Vec::new());
        }

        let mut results = Vec::with_capacity(types.len());
        for sub in types {
            results.push(sd.new_type_response(&params.project, &checker, sub));
        }
        Ok(results)
    }

    // Go: api/session.go:1444 resolveSignaturePropertyOfSignature
    pub fn resolve_signature_property_of_signature(
        &self,
        params: &GetSignaturePropertyParams,
        getter: &dyn Fn(&Checker, SignatureId) -> SignatureId,
    ) -> Result<Option<SignatureResponse>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let (checker, sig) = sd.resolve_signature_handle(&params.project, params.signature)?;
        // Node handles in the answer read lazy JSDoc (session_p1.rs header).
        let _program = ls_program::enter_version(checker.borrow().program);

        let result = getter(&checker.borrow(), sig);
        if result.is_nil() {
            return Ok(None);
        }
        Ok(sd.new_signature_response(&params.project, &checker, result))
    }

    // Go: api/session.go:1463 handleGetContextualType
    // handleGetContextualType returns the contextual type for a node.
    pub fn handle_get_contextual_type(
        &self,
        ctx: &Context,
        params: &GetContextualTypeParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(setup.program, &params.location)?;
        if node.is_nil() {
            return Ok(None);
        }

        let t = setup
            .checker
            .borrow_mut()
            .get_contextual_type_exported(node, ContextFlags::NONE);
        if t.is_nil() {
            return Ok(None);
        }

        Ok(setup.new_type_response(t))
    }

    // Go: api/session.go:1487 handleGetBaseTypeOfLiteralType
    // handleGetBaseTypeOfLiteralType returns the base type of a literal type (e.g. number for 42).
    pub fn handle_get_base_type_of_literal_type(
        &self,
        ctx: &Context,
        params: &GetBaseTypeOfLiteralTypeParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let result = setup
            .checker
            .borrow_mut()
            .get_base_type_of_literal_type_exported(t);
        Ok(setup.new_type_response(result))
    }

    // Go: api/session.go:1508 handleGetNonNullableType
    // handleGetNonNullableType returns the type with null and undefined removed.
    pub fn handle_get_non_nullable_type(
        &self,
        ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let result = setup.checker.borrow_mut().get_non_nullable_type(t);
        Ok(setup.new_type_response(result))
    }

    // Go: api/session.go:1529 handleGetTypeFromTypeNode
    // handleGetTypeFromTypeNode returns the type for a type node.
    pub fn handle_get_type_from_type_node(
        &self,
        ctx: &Context,
        params: &GetTypeFromTypeNodeParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(setup.program, &params.location)?;

        let t = setup
            .checker
            .borrow_mut()
            .get_type_from_type_node_exported(node);
        Ok(setup.new_type_response(t))
    }

    // Go: api/session.go:1553 handleGetWidenedType
    // handleGetWidenedType returns the widened type.
    pub fn handle_get_widened_type(
        &self,
        ctx: &Context,
        params: &GetWidenedTypeParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let result = setup.checker.borrow_mut().get_widened_type_exported(t);
        Ok(setup.new_type_response(result))
    }

    // Go: api/session.go:1574 handleGetParameterType
    // handleGetParameterType returns the type of a parameter at a given index in a signature.
    pub fn handle_get_parameter_type(
        &self,
        ctx: &Context,
        params: &GetParameterTypeParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, sig) = setup.resolve_signature_handle(params.signature)?;
        let sig = checker_signature(&setup.checker, &owner, sig);

        if params.index < 0 {
            return Err(errors::errorf(
                format!("{}: invalid parameter index", *ERR_CLIENT_ERROR),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }

        let t = setup
            .checker
            .borrow_mut()
            .get_type_at_position_exported(sig, params.index);
        Ok(setup.new_type_response(t))
    }

    // Go: api/session.go:2398 handleGetTypeParameterAtPosition
    pub fn handle_get_type_parameter_at_position(
        &self,
        ctx: &Context,
        params: &GetParameterTypeParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, sig) = setup.resolve_signature_handle(params.signature)?;
        let sig = checker_signature(&setup.checker, &owner, sig);
        if params.index < 0 {
            return Err(errors::errorf(
                format!("{}: invalid parameter index", *ERR_CLIENT_ERROR),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }
        let t = setup
            .checker
            .borrow_mut()
            .get_type_parameter_at_position(sig, params.index);
        Ok(setup.new_type_response(t))
    }

    // Go: api/session.go:1599 handleIsArrayLikeType
    // handleIsArrayLikeType returns whether a type is array-like.
    pub fn handle_is_array_like_type(
        &self,
        ctx: &Context,
        params: &IsArrayLikeTypeParams,
    ) -> Result<bool, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let result = setup.checker.borrow_mut().is_array_like_type_exported(t);
        Ok(result)
    }

    // Go: api/session.go:1615 handleIsTypeAssignableTo
    // handleIsTypeAssignableTo returns whether source is assignable to target.
    pub fn handle_is_type_assignable_to(
        &self,
        ctx: &Context,
        params: &IsTypeAssignableToParams,
    ) -> Result<bool, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (source_owner, source) = setup.resolve_type_handle(params.source)?;
        let (target_owner, target) = setup.resolve_type_handle(params.target)?;
        let source = checker_type(&setup.checker, &source_owner, source);
        let target = checker_type(&setup.checker, &target_owner, target);

        let result = setup
            .checker
            .borrow_mut()
            .is_type_assignable_to_exported(source, target);
        Ok(result)
    }

    // Go: api/session.go:1635 handleGetShorthandAssignmentValueSymbol
    // handleGetShorthandAssignmentValueSymbol returns the value symbol of a shorthand property assignment.
    pub fn handle_get_shorthand_assignment_value_symbol(
        &self,
        ctx: &Context,
        params: &GetTypeAtLocationParams,
    ) -> Result<Option<SymbolResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(setup.program, &params.location)?;
        if node.is_nil() {
            return Ok(None);
        }

        let symbol = setup
            .checker
            .borrow_mut()
            .get_shorthand_assignment_value_symbol(node);
        if symbol.is_nil() {
            return Ok(None);
        }

        Ok(setup.new_symbol_response(symbol))
    }

    // Go: api/session.go:1659 handleGetTypeOfSymbolAtLocation
    // handleGetTypeOfSymbolAtLocation returns the narrowed type of a symbol at a specific location.
    pub fn handle_get_type_of_symbol_at_location(
        &self,
        ctx: &Context,
        params: &GetTypeOfSymbolAtLocationParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, symbol) = setup.resolve_symbol_handle(params.symbol)?;
        let symbol = checker_symbol(&setup.checker, &owner, symbol);

        let node = setup
            .sd
            .resolve_node_handle(setup.program, &params.location)?;

        let t = setup
            .checker
            .borrow_mut()
            .get_type_of_symbol_at_location(symbol, node);
        Ok(setup.new_type_response(t))
    }

    // Go: api/session.go:1691 handleTypeToTypeNode
    // handleTypeToTypeNode converts a Type to a TypeNode AST and returns it as binary-encoded data.
    pub fn handle_type_to_type_node(
        &self,
        ctx: &Context,
        params: &TypeToTypeNodeParams,
    ) -> Result<Option<Box<dyn AnyValue>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let mut enclosing_declaration = Node::NIL;
        if !params.location.0.is_empty() {
            enclosing_declaration = setup
                .sd
                .resolve_node_handle(setup.program, &params.location)?;
        }

        let type_node = setup.checker.borrow_mut().type_to_type_node_exported(
            t,
            enclosing_declaration,
            NodeBuilderFlags(params.flags as u32),
            None,
        );
        if type_node.is_nil() {
            return Ok(None);
        }

        let data = match encoder::encode_node(type_node, Node::NIL) {
            Ok((data, _)) => data,
            Err(err) => {
                return Err(errors::errorf(
                    format!("failed to encode type node: {err}"),
                    vec![err],
                ));
            }
        };

        if self.use_binary_responses {
            return Ok(to_any(RawBinary(data)));
        }
        Ok(to_any(SourceFileResponse {
            data: base64_std_encoding_encode_to_string(&data),
        }))
    }

    // Go: api/session.go:1729 handleSignatureToSignatureDeclaration
    pub fn handle_signature_to_signature_declaration(
        &self,
        ctx: &Context,
        params: &SignatureToSignatureDeclarationParams,
    ) -> Result<Option<Box<dyn AnyValue>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, sig) = setup.resolve_signature_handle(params.signature)?;
        let sig = checker_signature(&setup.checker, &owner, sig);

        let mut enclosing_declaration = Node::NIL;
        if !params.location.0.is_empty() {
            enclosing_declaration = setup
                .sd
                .resolve_node_handle(setup.program, &params.location)?;
        }

        // PORT: Go converts any int32 to `ast.Kind` (int16). A value that is
        // no SyntaxKind has no Rust value; it panics here (Go's node builder
        // has no case for it either).
        let kind = SyntaxKind::try_from(params.kind as u16)
            .unwrap_or_else(|_| panic!("ast.Kind({}) is not a syntax kind", params.kind));
        let node = setup
            .checker
            .borrow_mut()
            .signature_to_signature_declaration_exported(
                sig,
                kind,
                enclosing_declaration,
                NodeBuilderFlags(params.flags as u32),
            );
        if node.is_nil() {
            return Ok(None);
        }

        let data = match encoder::encode_node(node, Node::NIL) {
            Ok((data, _)) => data,
            Err(err) => {
                return Err(errors::errorf(
                    format!("failed to encode signature declaration: {err}"),
                    vec![err],
                ));
            }
        };

        if self.use_binary_responses {
            return Ok(to_any(RawBinary(data)));
        }
        Ok(to_any(SourceFileResponse {
            data: base64_std_encoding_encode_to_string(&data),
        }))
    }

    // Go: api/session.go:1768 handleTypeToString
    // handleTypeToString converts a Type to its string representation.
    pub fn handle_type_to_string(
        &self,
        ctx: &Context,
        params: &TypeToTypeNodeParams,
    ) -> Result<Option<Box<dyn AnyValue>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let mut enclosing_declaration = Node::NIL;
        if !params.location.0.is_empty() {
            enclosing_declaration = setup
                .sd
                .resolve_node_handle(setup.program, &params.location)?;
        }

        if params.flags != 0 {
            let text = setup.checker.borrow_mut().type_to_string_ex(
                t,
                enclosing_declaration,
                TypeFormatFlags(params.flags as u32),
                None,
            );
            return Ok(to_any(text));
        }
        let text = setup.checker.borrow_mut().type_to_string_ex(
            t,
            enclosing_declaration,
            TypeFormatFlags::ALLOW_UNIQUE_ES_SYMBOL_TYPE
                | TypeFormatFlags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE,
            None,
        );
        Ok(to_any(text))
    }

    // Go: api/session.go:1795 handlePrintNode
    // handlePrintNode decodes a binary-encoded AST node and prints it to text.
    pub fn handle_print_node(
        &self,
        _ctx: &Context,
        params: &PrintNodeParams,
    ) -> Result<String, GoError> {
        let data = match base64_std_encoding_decode_string(&params.data) {
            Ok(data) => data,
            Err(err) => {
                return Err(errors::errorf(
                    format!("{}: invalid base64 data: {}", *ERR_CLIENT_ERROR, err),
                    vec![ERR_CLIENT_ERROR.clone(), err],
                ));
            }
        };

        let node = match encoder::decode_nodes(&data) {
            Ok(node) => node,
            Err(err) => {
                return Err(errors::errorf(
                    format!("{}: failed to decode AST: {}", *ERR_CLIENT_ERROR, err),
                    vec![ERR_CLIENT_ERROR.clone(), err],
                ));
            }
        };

        let mut p = new_printer(
            PrinterOptions {
                preserve_source_newlines: params.preserve_source_newlines,
                never_ascii_escape: params.never_ascii_escape,
                terminate_unterminated_literals: params.terminate_unterminated_literals,
                ..Default::default()
            },
            PrintHandlers::default(),
            None,
        );
        Ok(p.emit(node, Node::NIL))
    }

    // Go: api/session.go:2625 handleEmit (tsgo#4699)
    // PORT: Go writes each output through the project session FS from the
    // emit goroutines. Here the write callback runs on the checker threads
    // and the FS belongs to this thread (`Rc`), so the callback keeps the
    // outputs and this thread writes them after the emit, in the order they
    // came. A failed write adds the Go "Could not write file" diagnostic
    // (named after the output that a `.map` file belongs to, as Go does)
    // at the end of the list, not in the file's own list, and the file
    // leaves `emittedFiles`.
    pub fn handle_emit(&self, ctx: &Context, params: &EmitParams) -> Result<EmitResponse, GoError> {
        let (program, mut options) = self.get_emit_options(params)?;
        // Current for the whole handler (session_p1.rs header).
        let _program = ls_program::enter(program);
        let writes: Arc<Mutex<Vec<(String, String)>>> = Arc::default();
        let pending = Arc::clone(&writes);
        let write_file: WriteFile = Arc::new(
            move |file_name: &str, text: &str, _data: &mut WriteFileData| {
                pending
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push((file_name.to_string(), text.to_string()));
                Ok(())
            },
        );
        options.write_file = Some(write_file);
        let mut result = emit_program(ctx, program, options)?;
        let writes = std::mem::take(&mut *writes.lock().unwrap_or_else(PoisonError::into_inner));
        let fs = self.project_session.fs();
        for (file_name, text) in writes {
            if let Err(err) = fs.write_file(&file_name, &text) {
                let output_file = file_name.strip_suffix(".map").unwrap_or(&file_name);
                result.diagnostics.push(new_compiler_diagnostic(
                    diag::Could_not_write_file_0_Colon_1,
                    args![output_file, fs_error_text(&err)],
                ));
                result.emitted_files.retain(|emitted| *emitted != file_name);
            }
        }
        // Go clones `EmittedFiles` and makes a nil one `[]string{}`; an empty
        // `Vec` marshals as `[]`.
        Ok(EmitResponse {
            emit_skipped: result.emit_skipped,
            diagnostics: non_nil_diagnostics(&result.diagnostics),
            emitted_files: result.emitted_files,
        })
    }

    // Go: api/session.go:2648 handleEmitToString (tsgo#4699)
    pub fn handle_emit_to_string(
        &self,
        ctx: &Context,
        params: &EmitParams,
    ) -> Result<EmitOutputResponse, GoError> {
        let (program, options) = self.get_emit_options(params)?;
        // Current for the whole handler (session_p1.rs header).
        let _program = ls_program::enter(program);
        emit_to_output(ctx, program, options)
    }

    // Go: api/session.go:2656 handleSelectedFilesEmit (tsgo#4699)
    pub fn handle_selected_files_emit(
        &self,
        ctx: &Context,
        params: &SelectedFilesEmitParams,
        emit_only: EmitOnly,
    ) -> Result<EmitOutputResponse, GoError> {
        let program = self.get_emit_program(params.snapshot, &params.project)?;
        // Current for the whole handler (session_p1.rs header).
        let _program = ls_program::enter(program);
        let Some(files) = &params.files else {
            return Err(errors::errorf(
                format!("{}: files is required", *ERR_CLIENT_ERROR),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };
        let mut target_source_files = Vec::with_capacity(files.len());
        for file in files {
            let source_file = self.resolve_optional_source_file(program, Some(file))?;
            target_source_files.push(source_file);
        }
        emit_to_output(
            ctx,
            program,
            EmitOptions {
                target_source_files: Some(target_source_files),
                emit_only,
                force_emit: true,
                write_file: None,
            },
        )
    }
}

// Go: api/session.go:2679 emitToOutput (tsgo#4699)
// PORT: the write callback runs on the checker threads, so the outputs are
// in an `Arc<Mutex>` (Go `mu`). The caller keeps `program` current.
fn emit_to_output(
    ctx: &Context,
    program: &'static compiler::NewProgram,
    mut options: EmitOptions,
) -> Result<EmitOutputResponse, GoError> {
    let output_files: Arc<Mutex<Vec<EmitOutputFile>>> = Arc::default();
    let outputs = Arc::clone(&output_files);
    let write_file: WriteFile = Arc::new(
        move |file_name: &str, text: &str, data: &mut WriteFileData| {
            let mut source_file_name = None;
            if data.source_file.is_some() {
                source_file_name = Some(source_file_file_name(data.source_file).to_string());
            }
            outputs
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(EmitOutputFile {
                    file_name: file_name.to_string(),
                    text: text.to_string(),
                    source_file_name,
                });
            Ok(())
        },
    );
    options.write_file = Some(write_file);

    let result = emit_program(ctx, program, options)?;
    let mut output_files =
        std::mem::take(&mut *output_files.lock().unwrap_or_else(PoisonError::into_inner));
    // Go `strings.Compare`: byte order, as `String` compares.
    output_files.sort_by(|a, b| a.file_name.cmp(&b.file_name));
    Ok(EmitOutputResponse {
        emit_skipped: result.emit_skipped,
        diagnostics: non_nil_diagnostics(&result.diagnostics),
        output_files,
    })
}

impl Session {
    // Go: api/session.go:2708 getEmitOptions (tsgo#4699)
    pub fn get_emit_options(
        &self,
        params: &EmitParams,
    ) -> Result<(&'static compiler::NewProgram, EmitOptions), GoError> {
        let program = self.get_emit_program(params.snapshot, &params.project)?;
        let emit_only = get_emit_only(params.emit_only)?;
        Ok((
            program,
            EmitOptions {
                emit_only,
                ..EmitOptions::default()
            },
        ))
    }

    // Go: api/session.go:2722 getEmitProgram (tsgo#4699)
    pub fn get_emit_program(
        &self,
        snapshot: SnapshotID,
        project_id: &ProjectID,
    ) -> Result<&'static compiler::NewProgram, GoError> {
        let sd = self.get_snapshot_data(snapshot)?;
        sd.get_program(project_id)
    }
}

// Go: api/session.go:2730 getEmitOnly (tsgo#4699)
// PORT: Go converts the number to `compiler.EmitOnly` (EmitAll 0,
// EmitOnlyJs 1, EmitOnlyDts 2); the port matches it to the enum.
fn get_emit_only(value: Option<u32>) -> Result<EmitOnly, GoError> {
    let Some(value) = value else {
        return Ok(EmitOnly::All);
    };
    match value {
        0 => Ok(EmitOnly::All),
        1 => Ok(EmitOnly::Js),
        2 => Ok(EmitOnly::Dts),
        _ => Err(errors::errorf(
            format!("{}: invalid emitOnly value: {}", *ERR_CLIENT_ERROR, value),
            vec![ERR_CLIENT_ERROR.clone()],
        )),
    }
}

// Go: api/session.go:2741 emitProgram (tsgo#4699)
// PORT: Go `program.Emit` of the project program. The port runs the compile
// emit (`program_emit::emit`) with the program current (`ls_program::enter`).
// The first emit of a program version makes its compile checker pool;
// `ls_program` frees it with the program.
// `program_emit::emit` takes no context and always returns a result, so
// Go's nil result branches (a canceled `ctx`) do not happen here.
fn emit_program(
    _ctx: &Context,
    program: &'static compiler::NewProgram,
    options: EmitOptions,
) -> Result<EmitResult, GoError> {
    let _program = ls_program::enter(program);
    Ok(program_emit::emit(options))
}

// Go: api/session.go:2752 nonNilDiagnostics (tsgo#4699)
// PORT: a Rust `Vec` has no nil. An empty list marshals as `[]`, the same as
// Go's non-nil empty slice.
fn non_nil_diagnostics(diags: &[Diagnostic]) -> Vec<DiagnosticResponse> {
    new_diagnostic_responses(diags)
}

impl Session {
    // Go: api/session.go:2125 handleGetWellKnownSymbols
    // handleGetWellKnownSymbols returns the handle ids of the per-checker singleton
    // symbols (unknown, undefined, arguments) so the client can identify them by id.
    pub fn handle_get_well_known_symbols(
        &self,
        ctx: &Context,
        params: &GetIntrinsicTypeParams,
    ) -> Result<Option<WellKnownSymbolsResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (unknown, undefined, arguments) = {
            let c = setup.checker.borrow();
            (
                c.get_unknown_symbol(),
                c.get_undefined_symbol(),
                c.get_arguments_symbol(),
            )
        };
        let (unknown, _) = setup
            .sd
            .register_symbol(&setup.checker, unknown, &setup.project_id);
        let (undefined, _) = setup
            .sd
            .register_symbol(&setup.checker, undefined, &setup.project_id);
        let (arguments, _) = setup
            .sd
            .register_symbol(&setup.checker, arguments, &setup.project_id);
        Ok(Some(WellKnownSymbolsResponse {
            unknown,
            undefined,
            arguments,
        }))
    }

    // Go: api/session.go:2847 handleGetWellKnownSignatures
    // handleGetWellKnownSignatures returns the handle id of the per-checker unknown
    // signature so the client can identify it by id.
    pub fn handle_get_well_known_signatures(
        &self,
        ctx: &Context,
        params: &GetIntrinsicTypeParams,
    ) -> Result<Option<WellKnownSignaturesResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let unknown = setup.checker.borrow().get_unknown_signature();
        Ok(Some(WellKnownSignaturesResponse {
            unknown: setup
                .sd
                .register_signature(&setup.project_id, &setup.checker, unknown),
        }))
    }

    // Go: api/session.go:2762 handleFormatNodeForInsertion
    // handleFormatNodeForInsertion formats a synthesized node with the correct indentation
    // for insertion at a specific position in an existing file.
    pub fn handle_format_node_for_insertion(
        &self,
        ctx: &Context,
        params: &FormatNodeForInsertionParams,
    ) -> Result<String, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let program = sd.get_program(&params.project)?;
        // The formatter reads the target file (file header, "Current program").
        let _program = ls_program::enter(program);

        let target_source_file = self.resolve_optional_source_file(program, Some(&params.file))?;

        let data = match base64_std_encoding_decode_string(&params.data) {
            Ok(data) => data,
            Err(err) => {
                return Err(errors::errorf(
                    format!("{}: invalid base64 data: {}", *ERR_CLIENT_ERROR, err),
                    vec![ERR_CLIENT_ERROR.clone(), err],
                ));
            }
        };

        let node = match encoder::decode_nodes(&data) {
            Ok(node) => node,
            Err(err) => {
                return Err(errors::errorf(
                    format!("{}: failed to decode AST: {}", *ERR_CLIENT_ERROR, err),
                    vec![ERR_CLIENT_ERROR.clone(), err],
                ));
            }
        };

        let pos =
            source_file_get_position_map(target_source_file).utf16_to_utf8(params.position as i32);
        let format_options = sd.snapshot.user_preferences().format_code_settings;
        let new_line = format_options.editor_settings.new_line_character.clone();

        let factory = NodeFactory::new();
        let (text, node_with_pos) = print_and_position_node(
            &factory,
            node,
            Node::NIL,
            &new_line,
            format_options.editor_settings.indent_size,
            None,
        );
        // PORT: Go passes `targetSourceFile.ParseOptions()`; the port keeps
        // its file name and path (see `create_synthetic_source_file`).
        let synthetic_file = create_synthetic_source_file(
            &factory,
            node_with_pos,
            &text,
            source_file_file_name(target_source_file),
            &source_file_info(target_source_file).path,
        );

        let is_at_line_start =
            crate::format::get_line_start_position_for_position(pos, target_source_file) == pos;
        let initial_indentation = crate::format::get_indentation(
            pos,
            target_source_file,
            &format_options,
            is_at_line_start,
        );

        let mut delta = 0;
        if format_options.editor_settings.indent_size != 0
            && crate::format::should_indent_child_node(
                &format_options,
                node,
                Node::NIL,
                Node::NIL,
                &[],
            )
        {
            delta = format_options.editor_settings.indent_size;
        }

        let ctx = crate::format::with_format_code_settings(ctx, &format_options, &new_line);
        let changes = crate::format::format_node_given_indentation(
            &ctx,
            node_with_pos,
            synthetic_file,
            source_file_language_variant(target_source_file),
            initial_indentation,
            delta,
        );

        Ok(crate::frontend::core_textchange::apply_bulk_edits(
            &text, &changes,
        ))
    }

    // Go: api/session.go:1815 handleGetIntrinsicType
    // handleGetIntrinsicType returns an intrinsic type (any, string, number, etc.).
    pub fn handle_get_intrinsic_type(
        &self,
        ctx: &Context,
        params: &GetIntrinsicTypeParams,
        getter: fn(&Checker) -> TypeId,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = getter(&setup.checker.borrow());
        if t.is_nil() {
            return Ok(None);
        }

        Ok(setup.new_type_response(t))
    }

    // Go: api/session.go:1831 handleIsContextSensitive
    // handleIsContextSensitive returns whether a node is context-sensitive.
    pub fn handle_is_context_sensitive(
        &self,
        ctx: &Context,
        params: &GetContextualTypeParams,
    ) -> Result<bool, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(setup.program, &params.location)?;
        if node.is_nil() {
            return Ok(false);
        }

        let result = setup
            .checker
            .borrow_mut()
            .is_context_sensitive_exported(node);
        Ok(result)
    }

    // Go: api/session.go:1850 handleGetReturnTypeOfSignature
    // handleGetReturnTypeOfSignature returns the return type of a signature.
    pub fn handle_get_return_type_of_signature(
        &self,
        ctx: &Context,
        params: &GetSignaturePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, sig) = setup.resolve_signature_handle(params.signature)?;
        let sig = checker_signature(&setup.checker, &owner, sig);

        let t = setup
            .checker
            .borrow_mut()
            .get_return_type_of_signature_exported(sig);
        Ok(setup.new_type_response(t))
    }

    // Go: api/session.go:1871 handleGetRestTypeOfSignature
    // handleGetRestTypeOfSignature returns the rest type of a signature.
    pub fn handle_get_rest_type_of_signature(
        &self,
        ctx: &Context,
        params: &CheckerSignatureParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, sig) = setup.resolve_signature_handle(params.signature)?;
        let sig = checker_signature(&setup.checker, &owner, sig);

        let t = setup
            .checker
            .borrow_mut()
            .get_rest_type_of_signature_exported(sig);
        Ok(setup.new_type_response(t))
    }

    // Go: api/session.go:1892 handleGetTypePredicateOfSignature
    // handleGetTypePredicateOfSignature returns the type predicate of a signature.
    pub fn handle_get_type_predicate_of_signature(
        &self,
        ctx: &Context,
        params: &CheckerSignatureParams,
    ) -> Result<Option<TypePredicateResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, sig) = setup.resolve_signature_handle(params.signature)?;
        let sig = checker_signature(&setup.checker, &owner, sig);

        let pred = setup
            .checker
            .borrow_mut()
            .get_type_predicate_of_signature_exported(sig);
        if pred.is_nil() {
            return Ok(None);
        }

        let (kind, parameter_index, parameter_name, pred_type) = {
            let c = setup.checker.borrow();
            let p = c.pred(pred);
            (
                p.kind().0,
                p.parameter_index(),
                p.parameter_name().to_string(),
                p.type_(),
            )
        };
        let mut resp = TypePredicateResponse {
            kind,
            parameter_index,
            parameter_name,
            ..Default::default()
        };
        if pred_type.is_some() {
            resp.type_ = setup.new_type_response(pred_type);
        }

        Ok(Some(resp))
    }

    // Go: api/session.go:2143 handleIsArrayType
    // handleIsArrayType returns whether a type is Array<T> or ReadonlyArray<T>.
    pub fn handle_is_array_type(
        &self,
        ctx: &Context,
        params: &CheckerTypeParams,
    ) -> Result<bool, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let result = setup.checker.borrow().is_array_type_exported(t);
        Ok(result)
    }

    // Go: api/session.go:2159 handleIsTupleType
    // handleIsTupleType returns whether a type is a tuple type.
    pub fn handle_is_tuple_type(
        &self,
        ctx: &Context,
        params: &CheckerTypeParams,
    ) -> Result<bool, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let result = setup.checker.borrow().is_tuple_type_exported(t);
        Ok(result)
    }

    // Go: api/session.go:1922 handleGetBaseTypes
    // handleGetBaseTypes returns the base types of an interface/class type.
    pub fn handle_get_base_types(
        &self,
        ctx: &Context,
        params: &CheckerTypeParams,
    ) -> Result<Vec<Option<TypeResponse>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let base_types = setup.checker.borrow_mut().get_base_types_exported(t);
        if base_types.is_empty() {
            return Ok(Vec::new());
        }

        let mut results = Vec::with_capacity(base_types.len());
        for bt in base_types {
            results.push(setup.new_type_response(bt));
        }

        Ok(results)
    }

    // Go: api/session.go:1948 handleGetPropertiesOfType
    // handleGetPropertiesOfType returns the properties of a type.
    pub fn handle_get_properties_of_type(
        &self,
        ctx: &Context,
        params: &CheckerTypeParams,
    ) -> Result<Vec<Option<SymbolResponse>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let props = setup
            .checker
            .borrow_mut()
            .get_properties_of_type_exported(t);
        if props.is_empty() {
            return Ok(Vec::new());
        }

        let mut results = Vec::with_capacity(props.len());
        for prop in props {
            results.push(setup.new_symbol_response(prop));
        }

        Ok(results)
    }

    // Go: api/session.go:3029 handleGetApparentPropertiesOfType
    // handleGetApparentPropertiesOfType returns the apparent properties of a type,
    // including CallableFunction or NewableFunction members where applicable.
    pub fn handle_get_apparent_properties_of_type(
        &self,
        ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Vec<Option<SymbolResponse>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let props = setup.checker.borrow_mut().get_apparent_properties(t);
        let mut results = Vec::with_capacity(props.len());
        for prop in props {
            results.push(setup.new_symbol_response(prop));
        }
        Ok(results)
    }

    // Go: api/session.go:2369 handleGetApparentType
    // handleGetApparentType returns the apparent type of a type.
    pub fn handle_get_apparent_type(
        &self,
        ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let apparent = setup.checker.borrow_mut().get_apparent_type_exported(t);
        Ok(setup.new_type_response(apparent))
    }

    // Go: api/session.go:1974 handleGetIndexInfosOfType
    // handleGetIndexInfosOfType returns the index infos of a type.
    pub fn handle_get_index_infos_of_type(
        &self,
        ctx: &Context,
        params: &CheckerTypeParams,
    ) -> Result<Vec<IndexInfoResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let infos = setup
            .checker
            .borrow_mut()
            .get_index_infos_of_type_exported(t);
        if infos.is_empty() {
            return Ok(Vec::new());
        }

        let mut results = Vec::with_capacity(infos.len());
        for info in infos {
            let (key_type, value_type, is_readonly, declaration) = {
                let c = setup.checker.borrow();
                let info = c.index_info(info);
                (
                    info.key_type(),
                    info.value_type(),
                    info.is_readonly(),
                    info.declaration(),
                )
            };
            // PORT: Go dereferences the `*TypeResponse` (`*setup.newTypeResponse(..)`),
            // which panics on nil.
            let mut result = IndexInfoResponse {
                key_type: setup
                    .new_type_response(key_type)
                    .expect("invalid memory address or nil pointer dereference"),
                value_type: setup
                    .new_type_response(value_type)
                    .expect("invalid memory address or nil pointer dereference"),
                is_readonly,
                ..Default::default()
            };
            if declaration.is_some() {
                result.declaration = setup.sd.node_handle_from(declaration);
            }
            results.push(result);
        }

        Ok(results)
    }

    // Go: api/session.go:2007 handleGetConstraintOfTypeParameter
    // handleGetConstraintOfTypeParameter returns the constraint of a type parameter.
    pub fn handle_get_constraint_of_type_parameter(
        &self,
        ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let constraint = setup
            .checker
            .borrow_mut()
            .get_constraint_of_type_parameter_exported(t);
        if constraint.is_nil() {
            return Ok(None);
        }

        Ok(setup.new_type_response(constraint))
    }

    // Go: api/session.go:3123 handleGetDefaultFromTypeParameter
    // handleGetDefaultFromTypeParameter returns the default type of a type parameter.
    pub fn handle_get_default_from_type_parameter(
        &self,
        ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let result = setup
            .checker
            .borrow_mut()
            .get_default_from_type_parameter_exported(t);
        Ok(setup.new_type_response(result))
    }

    // Go: api/session.go:2281 handleGetBaseConstraintOfType
    // handleGetBaseConstraintOfType returns the base constraint of an instantiable type.
    pub fn handle_get_base_constraint_of_type(
        &self,
        ctx: &Context,
        params: &CheckerTypeParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let constraint = setup
            .checker
            .borrow_mut()
            .get_base_constraint_of_type_exported(t);
        if constraint.is_nil() {
            return Ok(None);
        }

        Ok(setup.new_type_response(constraint))
    }

    // Go: api/session.go:2302 handleGetPropertyOfType
    // handleGetPropertyOfType returns a named property symbol of a type.
    pub fn handle_get_property_of_type(
        &self,
        ctx: &Context,
        params: &GetPropertyOfTypeParams,
    ) -> Result<Option<SymbolResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let prop = setup
            .checker
            .borrow_mut()
            .get_property_of_type_exported(t, &params.name);
        if prop.is_nil() {
            return Ok(None);
        }

        Ok(setup.new_symbol_response(prop))
    }

    // Go: api/session.go:2323 handleGetConstantValue
    // handleGetConstantValue returns the constant value of an enum member or const enum access.
    // PORT: Go returns `any`; a nil `any` (no node, or no constant value) is `None`.
    pub fn handle_get_constant_value(
        &self,
        ctx: &Context,
        params: &CheckerNodeParams,
    ) -> Result<Option<Box<dyn AnyValue>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(setup.program, &params.location)?;
        if node.is_nil() {
            return Ok(None);
        }

        let value = setup.checker.borrow_mut().get_constant_value(node);
        match literal_value_to_json(value.as_ref()) {
            LspAny::Null => Ok(None),
            value => Ok(to_any(value)),
        }
    }

    // Go: api/session.go:2342 handleGetSignatureFromDeclaration
    // handleGetSignatureFromDeclaration returns the signature of a function-like declaration.
    pub fn handle_get_signature_from_declaration(
        &self,
        ctx: &Context,
        params: &CheckerNodeParams,
    ) -> Result<Option<SignatureResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(setup.program, &params.location)?;

        let sig = setup
            .checker
            .borrow_mut()
            .get_signature_from_declaration_exported(node);
        Ok(setup.new_signature_response(sig))
    }

    // Go: api/session.go:2366 handleGetExportSpecifierLocalTargetSymbol
    // handleGetExportSpecifierLocalTargetSymbol returns the local target symbol of an export specifier.
    pub fn handle_get_export_specifier_local_target_symbol(
        &self,
        ctx: &Context,
        params: &CheckerNodeParams,
    ) -> Result<Option<SymbolResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(setup.program, &params.location)?;
        if node.is_nil() {
            return Ok(None);
        }

        let symbol = setup
            .checker
            .borrow_mut()
            .get_export_specifier_local_target_symbol(node);
        if symbol.is_nil() {
            return Ok(None);
        }

        Ok(setup.new_symbol_response(symbol))
    }

    // Go: api/session.go:2390 handleGetAliasedSymbol
    // handleGetAliasedSymbol resolves an alias symbol to its target.
    pub fn handle_get_aliased_symbol(
        &self,
        ctx: &Context,
        params: &CheckerSymbolParams,
    ) -> Result<Option<SymbolResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, symbol) = setup.resolve_symbol_handle(params.symbol)?;
        let symbol = checker_symbol(&setup.checker, &owner, symbol);

        let aliased = setup.checker.borrow_mut().get_aliased_symbol(symbol);
        Ok(setup.new_symbol_response(aliased))
    }

    // Go: api/session.go:3261 handleGetFullyQualifiedName
    // handleGetFullyQualifiedName returns the fully qualified name of a symbol
    // (e.g. `"/path/to/module".Namespace.Name`).
    pub fn handle_get_fully_qualified_name(
        &self,
        ctx: &Context,
        params: &CheckerSymbolParams,
    ) -> Result<String, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, symbol) = setup.resolve_symbol_handle(params.symbol)?;
        if symbol.is_nil() {
            return Ok(String::new());
        }
        let symbol = checker_symbol(&setup.checker, &owner, symbol);

        let result = setup
            .checker
            .borrow_mut()
            .get_fully_qualified_name_exported(symbol);
        Ok(result)
    }

    // Go: api/session.go:2416 handleGetExportsOfModule
    // handleGetExportsOfModule returns the resolved exports of a module symbol,
    // including those introduced by `export *` and re-exports.
    pub fn handle_get_exports_of_module(
        &self,
        ctx: &Context,
        params: &CheckerSymbolParams,
    ) -> Result<Vec<Option<SymbolResponse>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, symbol) = setup.resolve_symbol_handle(params.symbol)?;
        if symbol.is_nil() {
            return Ok(Vec::new());
        }
        let symbol = checker_symbol(&setup.checker, &owner, symbol);

        let mut exports = setup
            .checker
            .borrow_mut()
            .get_exports_of_module_exported(symbol);
        if exports.is_empty() {
            return Ok(Vec::new());
        }
        {
            let mut c = setup.checker.borrow_mut();
            exports.sort_by(|&a, &b| c.compare_symbols_exported(a, b).cmp(&0));
        }

        let mut results = Vec::with_capacity(exports.len());
        for exp in exports {
            results.push(setup.new_symbol_response(exp));
        }

        Ok(results)
    }

    // Go: api/session.go:2446 handleGetJSDocTags
    // handleGetJSDocTags returns the JSDoc tags of a symbol as structured name/text pairs.
    pub fn handle_get_js_doc_tags(
        &self,
        ctx: &Context,
        params: &CheckerSymbolParams,
    ) -> Result<Vec<JSDocTagInfo>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, symbol) = setup.resolve_symbol_handle(params.symbol)?;
        if symbol.is_nil() {
            return Ok(Vec::new());
        }

        // PORT: Go reads the symbol with no checker; the port reads it in
        // the arena of the checker that owns the handle.
        let tags = ls::get_symbol_js_doc_tags(&owner.borrow(), symbol);
        if tags.is_empty() {
            return Ok(Vec::new());
        }
        let mut results = Vec::with_capacity(tags.len());
        for tag in tags {
            results.push(JSDocTagInfo {
                name: tag.name,
                text: tag.text,
            });
        }
        Ok(results)
    }

    // Go: api/session.go:2476 handleGetDocumentationComment
    // handleGetDocumentationComment returns the rendered documentation comment of a symbol as plain text.
    pub fn handle_get_documentation_comment(
        &self,
        ctx: &Context,
        params: &CheckerSymbolParams,
    ) -> Result<String, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, symbol) = setup.resolve_symbol_handle(params.symbol)?;
        if symbol.is_nil() {
            return Ok(String::new());
        }
        let symbol = checker_symbol(&setup.checker, &owner, symbol);

        let result = ls::get_symbol_documentation_comment(&mut setup.checker.borrow_mut(), symbol);
        Ok(result)
    }

    // Go: api/session.go:2028 handleGetTypeArguments
    // handleGetTypeArguments returns the type arguments of a type reference.
    pub fn handle_get_type_arguments(
        &self,
        ctx: &Context,
        params: &CheckerTypeParams,
    ) -> Result<Vec<Option<TypeResponse>>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup.resolve_type_handle(params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let type_args = setup.checker.borrow_mut().get_type_arguments_exported(t);
        if type_args.is_empty() {
            return Ok(Vec::new());
        }

        let mut results = Vec::with_capacity(type_args.len());
        for ta in type_args {
            results.push(setup.new_type_response(ta));
        }

        Ok(results)
    }

    // Go: api/session.go:2577 handleGetImmediateAliasedSymbol
    // handleGetImmediateAliasedSymbol resolves one level of alias indirection.
    pub fn handle_get_immediate_aliased_symbol(
        &self,
        ctx: &Context,
        params: &CheckerSymbolParams,
    ) -> Result<Option<SymbolResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, symbol) = setup.resolve_symbol_handle(params.symbol)?;
        if symbol.is_nil() {
            return Ok(None);
        }
        let symbol = checker_symbol(&setup.checker, &owner, symbol);

        let aliased = setup
            .checker
            .borrow_mut()
            .get_immediate_aliased_symbol_exported(symbol);
        if aliased.is_nil() {
            return Ok(None);
        }

        Ok(setup.new_symbol_response(aliased))
    }

    // Go: api/session.go:2632 handleGetMemberInModuleExports
    // handleGetMemberInModuleExports returns an export by name from a module symbol.
    pub fn handle_get_member_in_module_exports(
        &self,
        ctx: &Context,
        params: &GetMemberInModuleExportsParams,
    ) -> Result<Option<SymbolResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, symbol) = setup.resolve_symbol_handle(params.symbol)?;
        if symbol.is_nil() {
            return Ok(None);
        }
        let symbol = checker_symbol(&setup.checker, &owner, symbol);

        let member = setup
            .checker
            .borrow_mut()
            .try_get_member_in_module_exports(&params.name, symbol);
        if member.is_nil() {
            return Ok(None);
        }

        Ok(setup.new_symbol_response(member))
    }
}

impl Session {
    // Go: api/session.go:2626 handleGetTrueTypeOfConditionalType
    pub fn handle_get_true_type_of_conditional_type(
        &self,
        ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup
            .sd
            .resolve_type_handle(&params.project, params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let result = setup
            .checker
            .borrow_mut()
            .get_true_type_of_conditional_type(t);
        Ok(setup
            .sd
            .new_type_response(&params.project, &setup.checker, result))
    }

    // Go: api/session.go:2641 handleGetFalseTypeOfConditionalType
    pub fn handle_get_false_type_of_conditional_type(
        &self,
        ctx: &Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, t) = setup
            .sd
            .resolve_type_handle(&params.project, params.type_)?;
        let t = checker_type(&setup.checker, &owner, t);

        let result = setup
            .checker
            .borrow_mut()
            .get_false_type_of_conditional_type(t);
        Ok(setup
            .sd
            .new_type_response(&params.project, &setup.checker, result))
    }
}

impl SnapshotData {
    // Go: api/session.go:2053 resolveNodeHandle
    pub fn resolve_node_handle(
        &self,
        program: &'static compiler::NewProgram,
        handle: &NodeHandle,
    ) -> Result<Node, GoError> {
        let s = handle.0.as_str();
        // Format: "index.kind.path" — we need index and path, kind is informational only.
        let Some(first_dot) = s.bytes().position(|b| b == b'.') else {
            return Err(errors::errorf(
                format!(
                    "{}: invalid node handle {}",
                    *ERR_CLIENT_ERROR,
                    gostd::strconv::quote(s)
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };
        let Some(second_dot) = s[first_dot + 1..].bytes().position(|b| b == b'.') else {
            return Err(errors::errorf(
                format!(
                    "{}: invalid node handle {}",
                    *ERR_CLIENT_ERROR,
                    gostd::strconv::quote(s)
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };
        let second_dot = second_dot + first_dot + 1; // adjust to absolute index

        let idx = match strconv_parse_uint(&s[..first_dot], 10, 32) {
            Ok(idx) => idx,
            Err(err) => {
                return Err(errors::errorf(
                    format!(
                        "{}: invalid node handle {}: {}",
                        *ERR_CLIENT_ERROR,
                        gostd::strconv::quote(s),
                        err
                    ),
                    vec![ERR_CLIENT_ERROR.clone(), err],
                ));
            }
        };
        let path = tspath::Path(s[second_dot + 1..].to_string());

        let source_file = program
            .get_source_file_by_path(&path)
            .map_or(Node::NIL, |f| f.root);
        if source_file.is_nil() {
            return Err(errors::errorf(
                format!(
                    "{}: node handle {} could not be resolved (file may not be loaded or handle may be stale)",
                    *ERR_CLIENT_ERROR,
                    gostd::strconv::quote(s)
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }
        let table = encoder::get_node_index_table(source_file);

        // PORT: Go also checks `table != nil`; the Rust table is never nil.
        if idx < table.nodes.len() as u64 {
            let node = table.nodes[idx as usize];
            if node.is_some() {
                return Ok(node);
            }
        }
        Err(errors::errorf(
            format!(
                "{}: node handle {} could not be resolved (file may not be loaded or handle may be stale)",
                *ERR_CLIENT_ERROR,
                gostd::strconv::quote(s)
            ),
            vec![ERR_CLIENT_ERROR.clone()],
        ))
    }
}

// Go: api/session.go:2090 computeSnapshotChanges
// computeSnapshotChanges computes the per-project source file differences between
// two snapshots. It uses DiffOrderedMaps on projects to find changed/removed projects,
// then DiffMaps on FilesByPath for each changed project to collect file-level changes.
pub fn compute_snapshot_changes(
    prev: &project::Snapshot,
    next: &project::Snapshot,
) -> SnapshotChanges {
    let prev_projects = prev.project_collection.projects_by_path();
    let next_projects = next.project_collection.projects_by_path();

    let mut changes = SnapshotChanges::default();

    diff_ordered_maps(
        &prev_projects,
        &next_projects,
        // onAdded: new project — nothing to retain from previous snapshot.
        |_, _| {},
        // onRemoved: project removed entirely.
        |_, old_proj| {
            changes
                .removed_projects
                .push(project_handle(&old_proj.borrow()));
        },
        // onModified: project changed, diff its files.
        |_, old_proj, new_proj| {
            let old_program = old_proj.borrow().get_program();
            let new_program = new_proj.borrow().get_program();
            let same_program = match (old_program, new_program) {
                (Some(a), Some(b)) => std::ptr::eq(a, b),
                (None, None) => true,
                _ => false,
            };
            if same_program {
                return;
            }
            // PORT: a nil Go map is an empty map here.
            let empty: FxHashMap<tspath::Path, Rc<ParsedSourceFile>> = FxHashMap::default();
            let old_files = match old_program {
                Some(p) => p.files_by_path(),
                None => &empty,
            };
            let new_files = match new_program {
                Some(p) => p.files_by_path(),
                None => &empty,
            };
            let mut project_changes = ProjectFileChanges::default();
            {
                // PORT: Go map order is random; the port uses FxHashMap order.
                let mut on_removed = |path: &tspath::Path, _: &Rc<ParsedSourceFile>| {
                    project_changes.deleted_files.push(path.clone());
                };
                let mut on_changed =
                    |path: &tspath::Path, _: &Rc<ParsedSourceFile>, _: &Rc<ParsedSourceFile>| {
                        project_changes.changed_files.push(path.clone());
                    };
                diff_maps::<tspath::Path, Rc<ParsedSourceFile>>(
                    old_files,
                    new_files,
                    None, // onAdded: new file in project, not a change.
                    Some(&mut on_removed),
                    Some(&mut on_changed),
                );
            }
            if !project_changes.changed_files.is_empty()
                || !project_changes.deleted_files.is_empty()
            {
                // PORT: Go makes the nil map here; an empty map is the same
                // value to the `omitempty` field.
                changes
                    .changed_projects
                    .insert(project_handle(&new_proj.borrow()), project_changes);
            }
        },
    );

    changes
}

impl Session {
    // Go: api/session.go:2855 Close
    // Close closes the session and releases all active snapshots,
    // regardless of their ref counts.
    pub fn close(&self) {
        self.release_open_refs();

        let mut snapshots = self.snapshots.borrow_mut();
        // PORT: Go deletes while it ranges over the map; the port drains it.
        for (_, sd) in snapshots.drain() {
            project::Snapshot::deref(&sd.snapshot, &self.project_session);
        }
    }

    // Go: api/session.go:2871 releaseOpenRefs
    // releaseOpenRefs releases every project and file ref this session is holding open
    // in the project session. This keeps the API's ref counts balanced when an API
    // session is shut down while sharing a longer-lived project session (e.g. one
    // backing an LSP server), so API-opened projects and files aren't leaked. Only
    // refs the session currently holds are closed, so it never over-releases.
    // PORT: the Go `updateMu` lock is not ported (one thread).
    fn release_open_refs(&self) {
        if self.open_projects.borrow().is_empty() && self.open_files.borrow().is_empty() {
            return;
        }

        let mut api_request = project::APISnapshotRequest::default();
        if !self.open_projects.borrow().is_empty() {
            api_request.close_projects = Some(self.open_projects.borrow().clone());
        }
        if !self.open_files.borrow().is_empty() {
            api_request.close_files = Some(self.open_files.borrow().clone());
        }
        let (snapshot, err) = self.project_session.api_update(
            &gostd::context::background(),
            &project::FileChangeSummary::default(),
            api_request,
        );
        // APIUpdate returns a ref'd snapshot even on error; always release it.
        project::Snapshot::deref(&snapshot, &self.project_session);
        if err.is_some() {
            return;
        }

        self.open_projects.borrow_mut().clear();
        self.open_files.borrow_mut().clear();
    }
}

// Go: api/session.go:2897 formatSessionID
pub fn format_session_id(id: u64) -> String {
    format!("api-session-{id}")
}

impl Session {
    // Go: api/session.go:2902 toPath
    // toPath converts a file name to a normalized path.
    pub fn to_path(&self, file_name: &str) -> tspath::Path {
        tspath::to_path(
            file_name,
            &self.project_session.get_current_directory(),
            self.project_session.fs().use_case_sensitive_file_names(),
        )
    }

    // Go: api/session.go:2907 toFileChangeSummary
    // toFileChangeSummary converts API file changes to a project.FileChangeSummary.
    pub fn to_file_change_summary(
        &self,
        changes: Option<&APIFileChanges>,
    ) -> project::FileChangeSummary {
        let Some(changes) = changes else {
            return project::FileChangeSummary::default();
        };
        let mut summary = project::FileChangeSummary::default();
        if changes.invalidate_all {
            summary.invalidate_all = true;
            summary.includes_watch_change_outside_node_modules = true;
            return summary;
        }
        let cwd = self.project_session.get_current_directory();
        for doc in &changes.changed {
            let uri = doc.to_uri(&cwd);
            summary.changed.insert(uri);
        }
        for doc in &changes.created {
            let uri = doc.to_uri(&cwd);
            summary.created.insert(uri);
        }
        for doc in &changes.deleted {
            let uri = doc.to_uri(&cwd);
            summary.deleted.insert(uri);
        }
        if summary.changed.len() + summary.created.len() + summary.deleted.len() > 0 {
            summary.includes_watch_change_outside_node_modules = true;
        }
        summary
    }

    // Go: api/session.go:3634 getDiagnostics
    // PORT: Go `params.Files != nil` is `Some`: an empty list gives no
    // diagnostics, and no list gives the diagnostics of all files.
    pub fn get_diagnostics(
        &self,
        ctx: &Context,
        params: &GetDiagnosticsParams,
        getter: fn(&'static compiler::NewProgram, &Context, Node) -> Vec<Diagnostic>,
    ) -> Result<Vec<DiagnosticResponse>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let program = sd.get_program(&params.project)?;
        // Current for the whole handler (session_p1.rs header).
        let _program = ls_program::enter(program);

        if let Some(files) = &params.files {
            let mut all_diags: Vec<Diagnostic> = Vec::new();
            for file in files {
                let source_file = self.resolve_optional_source_file(program, Some(file))?;
                all_diags.extend(getter(program, ctx, source_file));
            }
            return Ok(new_diagnostic_responses(&all_diags));
        }

        Ok(new_diagnostic_responses(&getter(program, ctx, Node::NIL)))
    }

    // Go: api/session.go:3661 handleGetSyntacticDiagnostics
    pub fn handle_get_syntactic_diagnostics(
        &self,
        ctx: &Context,
        params: &GetDiagnosticsParams,
    ) -> Result<Vec<DiagnosticResponse>, GoError> {
        let ctx = &core_context::with_checker_lifetime(ctx, CheckerLifetime::DIAGNOSTICS);
        self.get_diagnostics(ctx, params, ls_program::get_syntactic_diagnostics)
    }

    // Go: api/session.go:3667 handleGetBindDiagnostics
    pub fn handle_get_bind_diagnostics(
        &self,
        ctx: &Context,
        params: &GetDiagnosticsParams,
    ) -> Result<Vec<DiagnosticResponse>, GoError> {
        let ctx = &core_context::with_checker_lifetime(ctx, CheckerLifetime::DIAGNOSTICS);
        self.get_diagnostics(ctx, params, ls_program::get_bind_diagnostics)
    }

    // Go: api/session.go:3673 handleGetSemanticDiagnostics
    pub fn handle_get_semantic_diagnostics(
        &self,
        ctx: &Context,
        params: &GetDiagnosticsParams,
    ) -> Result<Vec<DiagnosticResponse>, GoError> {
        let ctx = &core_context::with_checker_lifetime(ctx, CheckerLifetime::DIAGNOSTICS);
        self.get_diagnostics(ctx, params, ls_program::get_semantic_diagnostics)
    }

    // Go: api/session.go:3679 handleGetSuggestionDiagnostics
    pub fn handle_get_suggestion_diagnostics(
        &self,
        ctx: &Context,
        params: &GetDiagnosticsParams,
    ) -> Result<Vec<DiagnosticResponse>, GoError> {
        let ctx = &core_context::with_checker_lifetime(ctx, CheckerLifetime::DIAGNOSTICS);
        self.get_diagnostics(ctx, params, ls_program::get_suggestion_diagnostics)
    }

    // Go: api/session.go:3685 handleGetDeclarationDiagnostics
    pub fn handle_get_declaration_diagnostics(
        &self,
        ctx: &Context,
        params: &GetDiagnosticsParams,
    ) -> Result<Vec<DiagnosticResponse>, GoError> {
        let ctx = &core_context::with_checker_lifetime(ctx, CheckerLifetime::DIAGNOSTICS);
        self.get_diagnostics(ctx, params, ls_program::get_declaration_diagnostics)
    }

    // Go: api/session.go:2281 handleGetConfigFileParsingDiagnostics
    // handleGetConfigFileParsingDiagnostics returns config file parsing diagnostics.
    pub fn handle_get_config_file_parsing_diagnostics(
        &self,
        _ctx: &Context,
        params: &GetProjectDiagnosticsParams,
    ) -> Result<Vec<DiagnosticResponse>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let program = sd.get_program(&params.project)?;
        // Current for the whole handler (session_p1.rs header).
        let _program = ls_program::enter(program);

        let diags = program.get_config_file_parsing_diagnostics();
        Ok(new_diagnostic_responses(&diags))
    }

    // Go: api/session.go:3063 handleGetProgramDiagnostics
    // handleGetProgramDiagnostics returns program-wide diagnostics, including options diagnostics.
    pub fn handle_get_program_diagnostics(
        &self,
        _ctx: &Context,
        params: &GetProjectDiagnosticsParams,
    ) -> Result<Vec<DiagnosticResponse>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let program = sd.get_program(&params.project)?;
        // Current for the whole handler (session_p1.rs header).
        let _program = ls_program::enter(program);

        let diags = ls_program::get_program_diagnostics(program);
        Ok(new_diagnostic_responses(&diags))
    }

    // Go: api/session.go:3079 handleGetGlobalDiagnostics
    // handleGetGlobalDiagnostics returns global (non-file-specific) semantic diagnostics.
    pub fn handle_get_global_diagnostics(
        &self,
        ctx: &Context,
        params: &GetProjectDiagnosticsParams,
    ) -> Result<Vec<DiagnosticResponse>, GoError> {
        let ctx = &core_context::with_checker_lifetime(ctx, CheckerLifetime::DIAGNOSTICS);
        let sd = self.get_snapshot_data(params.snapshot)?;

        let proj = sd.get_project(&params.project)?;

        let program = proj.borrow().get_program();
        let Some(program) = program else {
            return Err(errors::errorf(
                format!("{}: project has no program", *ERR_CLIENT_ERROR),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        };
        // Current for the whole handler (session_p1.rs header).
        let _program = ls_program::enter(program);

        // Global diagnostics are accumulated lazily by the project's checker pool as
        // files are checked. Force a full semantic pass so any global (non-file-specific)
        // diagnostics are produced; otherwise this would return an empty result for
        // projects using an external checker pool (the typical API case), since
        // compiler.Program.GetGlobalDiagnostics only reports for the internal pool.
        let _ = ls_program::get_semantic_diagnostics(program, ctx, Node::NIL);

        let diags: Vec<Diagnostic> = proj
            .borrow()
            .get_project_diagnostics(ctx)
            .into_iter()
            .filter(|d| d.file.is_nil())
            .collect();
        Ok(new_diagnostic_responses(&diags))
    }

    // Go: api/session.go:2298 resolveOptionalSourceFile
    // resolveOptionalSourceFile resolves an optional DocumentIdentifier to a source file.
    // Returns nil if the identifier is nil (meaning all files).
    pub fn resolve_optional_source_file(
        &self,
        program: &'static compiler::NewProgram,
        file: Option<&DocumentIdentifier>,
    ) -> Result<Node, GoError> {
        let Some(file) = file else {
            return Ok(Node::NIL);
        };
        let source_file = program
            .get_source_file(&file.to_file_name())
            .map_or(Node::NIL, |f| f.root);
        if source_file.is_nil() {
            return Err(errors::errorf(
                format!(
                    "{}: source file not found: {}",
                    *ERR_CLIENT_ERROR,
                    file.string()
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }
        Ok(source_file)
    }

    // Go: api/session.go:2310 handleGetReferencesToSymbolInFile
    // handleGetReferencesToSymbolInFile returns node handles for all identifiers in a file that reference the given symbol.
    pub fn handle_get_references_to_symbol_in_file(
        &self,
        ctx: &Context,
        params: &GetReferencesToSymbolInFileParams,
    ) -> Result<Vec<NodeHandle>, GoError> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let (owner, symbol) = setup.resolve_symbol_handle(params.symbol)?;
        if symbol.is_nil() {
            return Ok(Vec::new());
        }
        let symbol = checker_symbol(&setup.checker, &owner, symbol);

        let source_file = setup
            .program
            .get_source_file(&params.file.to_file_name())
            .map_or(Node::NIL, |f| f.root);
        if source_file.is_nil() {
            return Err(errors::errorf(
                format!(
                    "{}: source file not found: {}",
                    *ERR_CLIENT_ERROR,
                    params.file.string()
                ),
                vec![ERR_CLIENT_ERROR.clone()],
            ));
        }

        let nodes = setup
            .checker
            .borrow_mut()
            .get_references_to_symbol_in_file(source_file, symbol);
        let mut result = Vec::with_capacity(nodes.len());
        for node in nodes {
            result.push(setup.sd.node_handle_from(node));
        }
        Ok(result)
    }

    // Go: api/session.go:2338 handleGetSignatureUsages
    pub fn handle_get_signature_usages(
        &self,
        ctx: &Context,
        params: &GetSignatureUsagesParams,
    ) -> Result<Vec<SignatureUsageResponse>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;
        // Current for the whole handler (session_p1.rs header).
        let _program = ls_program::enter(program);

        let signature_decl = sd.resolve_node_handle(program, &params.signature_decl)?;
        if signature_decl.is_nil() {
            return Ok(Vec::new());
        }

        let lang_svc = self.setup_language_service(&sd, program, &params.project, "")?;

        let usages = lang_svc.get_signature_usages(ctx, signature_decl);
        // PORT: Go `usages == nil`. Go returns a nil slice exactly when there
        // is no usage; both results marshal as `[]`.
        if usages.is_empty() {
            return Ok(Vec::new());
        }

        let mut result = Vec::with_capacity(usages.len());
        for u in &usages {
            let mut entry = SignatureUsageResponse {
                name: sd.node_handle_from(u.name),
                ..Default::default()
            };
            if u.call.is_some() {
                entry.call = sd.node_handle_from(u.call);
            }
            result.push(entry);
        }
        Ok(result)
    }

    // Go: api/session.go:2380 handleGetCompletionsAtPosition
    // handleGetCompletionsAtPosition returns completions at a position in a document.
    pub fn handle_get_completions_at_position(
        &self,
        ctx: &Context,
        params: &GetCompletionsAtPositionParams,
    ) -> Result<Option<CompletionInfoResponse>, GoError> {
        let api_ctx;
        let ctx = if params.include_symbol {
            api_ctx = core_context::with_checker_lifetime(ctx, CheckerLifetime::API);
            &api_ctx
        } else {
            ctx
        };
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;
        // Current for the whole handler (session_p1.rs header).
        let _program = ls_program::enter(program);
        let source_file = program
            .get_source_file(&params.file.to_file_name())
            .map_or(Node::NIL, |f| f.root);
        if source_file.is_nil() {
            return Ok(None);
        }
        let lang_svc = self.setup_language_service(&sd, program, &params.project, "")?;
        let position_map = source_file_get_position_map(source_file);
        let internal_pos = position_map.utf16_to_utf8(params.position as i32);
        let result = lang_svc.get_completions_at_position_exported(
            ctx,
            source_file,
            internal_pos,
            params.trigger_character.clone(),
            params.include_symbol,
        );
        let result = match result {
            Err(err) => return Err(err),
            Ok(None) => return Ok(None),
            Ok(Some(result)) => result,
        };
        // PORT: Go reads `item.Symbol` without a checker. The symbols live in
        // the arena of the checker the completion request used, so the port
        // takes that checker again (same request context and file; the pool
        // returns the same checker) to read them.
        let mut symbol_checker: Option<(Rc<RefCell<Checker>>, ls_program::Release)> = None;
        let mut entries = Vec::with_capacity(result.items.len());
        for item in &result.items {
            let mut entry = CompletionEntryResponse {
                name: item.label.clone(),
                sort_text: item.sort_text.clone(),
                insert_text: item.insert_text.clone(),
                filter_text: item.filter_text.clone(),
                detail: item.detail.clone(),
                ..Default::default()
            };
            if let Some(kind) = item.kind {
                entry.kind = kind.0;
            }
            if let Some(label_details) = &item.label_details {
                entry.label_details = Some(CompletionEntryLabelDetailsResponse {
                    detail: label_details.detail.clone(),
                    description: label_details.description.clone(),
                });
            }
            if item.symbol.is_some() {
                let (checker, _) = symbol_checker.get_or_insert_with(|| {
                    ls_program::get_type_checker_for_file(program, ctx, source_file)
                });
                entry.symbol = sd.new_symbol_response(checker, item.symbol, &params.project);
            }
            entries.push(entry);
        }
        Ok(Some(CompletionInfoResponse {
            is_incomplete: result.is_incomplete,
            entries,
        }))
    }

    // Go: api/session.go:2433 handleGetReferencedSymbolsForNode
    // handleGetReferencedSymbolsForNode returns node handles for all references found at a node.
    pub fn handle_get_referenced_symbols_for_node(
        &self,
        ctx: &Context,
        params: &GetReferencedSymbolsForNodeParams,
    ) -> Result<Vec<ReferencedSymbolEntry>, GoError> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;
        // Current for the whole handler (session_p1.rs header).
        let _program = ls_program::enter(program);

        let node = sd.resolve_node_handle(program, &params.node)?;
        if node.is_nil() {
            return Ok(Vec::new());
        }

        let lang_svc = self.setup_language_service(&sd, program, &params.project, "")?;

        let source_files: Vec<Node> = program.get_source_files().iter().map(|f| f.root).collect();
        let entries = lang_svc.get_referenced_symbols_for_node_exported(
            ctx,
            params.position,
            node,
            &source_files,
        );
        // PORT: Go `entries == nil`; an empty result marshals as `[]` either way.
        if entries.is_empty() {
            return Ok(Vec::new());
        }

        // PORT: Go reads `symbol.Declarations` (DefinitionNode) and the
        // definition symbols without a checker. They live in the arena of the
        // request checker, which the language service took with
        // `GetTypeChecker(ctx)`; the port takes it again to read them
        // (ls/findallreferences_p1.rs header).
        let (checker, _done) = ls_program::get_type_checker(program, ctx);

        let mut result: Vec<ReferencedSymbolEntry> = Vec::new();
        for entry in &entries {
            let entry = entry.borrow();
            let def_node = entry.definition_node(&checker.borrow().symbols);
            if def_node.is_nil() {
                continue;
            }
            let mut refs: Vec<NodeHandle> = Vec::new();
            for ref_ in entry.references() {
                let ref_ = ref_.borrow();
                if ref_.is_node_entry() {
                    refs.push(sd.node_handle_from(ref_.node()));
                }
            }
            let mut re = ReferencedSymbolEntry {
                definition: sd.node_handle_from(def_node),
                references: refs,
                ..Default::default()
            };
            let sym = entry.definition_symbol();
            if sym.is_some() {
                re.symbol = sd.new_symbol_response(&checker, sym, &params.project);
            }
            result.push(re);
        }
        Ok(result)
    }
}

// Go: encoding/base64/base64.go:139 (*Encoding).EncodeToString (StdEncoding)
// PORT: the crate has no base64 dependency. Go `base64.StdEncoding`: the
// standard alphabet with `=` padding.
pub fn base64_std_encoding_encode_to_string(src: &[u8]) -> String {
    const ENCODE_STD: &[u8; 64] =
        b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut dst = String::with_capacity(src.len().div_ceil(3) * 4);
    for chunk in src.chunks(3) {
        let b0 = u32::from(chunk[0]);
        let b1 = chunk.get(1).map_or(0, |&b| u32::from(b));
        let b2 = chunk.get(2).map_or(0, |&b| u32::from(b));
        let val = (b0 << 16) | (b1 << 8) | b2;
        dst.push(ENCODE_STD[((val >> 18) & 0x3F) as usize] as char);
        dst.push(ENCODE_STD[((val >> 12) & 0x3F) as usize] as char);
        if chunk.len() > 1 {
            dst.push(ENCODE_STD[((val >> 6) & 0x3F) as usize] as char);
        } else {
            dst.push('=');
        }
        if chunk.len() > 2 {
            dst.push(ENCODE_STD[(val & 0x3F) as usize] as char);
        } else {
            dst.push('=');
        }
    }
    dst
}

// Go: encoding/base64/base64.go:429 (*Encoding).DecodeString (StdEncoding)
// PORT: the crate has no base64 dependency. This is Go `Decode` as a loop of
// `decodeQuantum` (base64.go:312): the standard alphabet, `=` padding
// required, not strict, `\r` and `\n` skipped. Go's 8- and 4-byte fast paths
// decode valid input the same way and fall back to `decodeQuantum` at the
// same offset, so results and error offsets are equal. Go returns the
// partial data with the error; the only caller uses the error alone. Go
// `CorruptInputError` is a `GoError` with the same text.
pub fn base64_std_encoding_decode_string(s: &str) -> Result<Vec<u8>, GoError> {
    fn decode_map(c: u8) -> u8 {
        match c {
            b'A'..=b'Z' => c - b'A',
            b'a'..=b'z' => c - b'a' + 26,
            b'0'..=b'9' => c - b'0' + 52,
            b'+' => 62,
            b'/' => 63,
            _ => 0xFF,
        }
    }
    // Go: base64.go:303 CorruptInputError.Error
    fn corrupt_input_error(offset: usize) -> GoError {
        errors::new(format!("illegal base64 data at input byte {offset}"))
    }

    let src = s.as_bytes();
    let mut dst: Vec<u8> = Vec::with_capacity(src.len() / 4 * 3);
    if src.is_empty() {
        return Ok(dst);
    }
    let mut si = 0usize;
    while si < src.len() {
        // Go: base64.go:312 decodeQuantum
        let mut dbuf = [0u8; 4];
        let mut dlen = 4usize;
        let mut err: Option<GoError> = None;

        let mut j = 0usize;
        while j < dbuf.len() {
            if src.len() == si {
                if j == 0 {
                    return Ok(dst);
                }
                // j == 1, or padding is required (StdEncoding)
                return Err(corrupt_input_error(si - j));
            }
            let input = src[si];
            si += 1;

            let out = decode_map(input);
            if out != 0xFF {
                dbuf[j] = out;
                j += 1;
                continue;
            }

            if input == b'\n' || input == b'\r' {
                continue;
            }

            if input != b'=' {
                return Err(corrupt_input_error(si - 1));
            }

            // We've reached the end and there's padding
            match j {
                0 | 1 => {
                    // incorrect padding
                    return Err(corrupt_input_error(si - 1));
                }
                2 => {
                    // "==" is expected, the first "=" is already consumed.
                    // skip over newlines
                    while si < src.len() && (src[si] == b'\n' || src[si] == b'\r') {
                        si += 1;
                    }
                    if si == src.len() {
                        // not enough padding
                        return Err(corrupt_input_error(src.len()));
                    }
                    if src[si] != b'=' {
                        // incorrect padding
                        return Err(corrupt_input_error(si - 1));
                    }

                    si += 1;
                }
                _ => {}
            }

            // skip over newlines
            while si < src.len() && (src[si] == b'\n' || src[si] == b'\r') {
                si += 1;
            }
            if si < src.len() {
                // trailing garbage
                err = Some(corrupt_input_error(si));
            }
            dlen = j;
            break;
        }

        // Convert 4x 6bit source bytes into 3 bytes
        let val = u32::from(dbuf[0]) << 18
            | u32::from(dbuf[1]) << 12
            | u32::from(dbuf[2]) << 6
            | u32::from(dbuf[3]);
        let bytes = [(val >> 16) as u8, (val >> 8) as u8, val as u8];
        match dlen {
            4 => dst.extend_from_slice(&bytes[..3]),
            3 => dst.extend_from_slice(&bytes[..2]),
            2 => dst.extend_from_slice(&bytes[..1]),
            _ => {}
        }

        if let Some(err) = err {
            return Err(err);
        }
    }
    Ok(dst)
}

// Go: strconv/number.go:104 ParseUint and internal/strconv/atoi.go:47 ParseUint
// PORT: Go stdlib. Only `2 <= base <= 36` is ported (the caller passes 10);
// Go `*strconv.NumError` is a `GoError` with the same text.
fn strconv_parse_uint(s: &str, base: u32, bit_size: u32) -> Result<u64, GoError> {
    // Go: strconv/number.go:258 (*NumError).Error
    let num_error = |reason: &str| {
        errors::new(format!(
            "strconv.ParseUint: parsing {}: {}",
            gostd::strconv::quote(s),
            reason
        ))
    };

    if s.is_empty() {
        return Err(num_error("invalid syntax"));
    }

    debug_assert!((2..=36).contains(&base) && (1..=64).contains(&bit_size));

    // Cutoff is the smallest number such that cutoff*base > maxUint64.
    let cutoff = u64::MAX / u64::from(base) + 1;

    let max_val: u64 = if bit_size == 64 {
        u64::MAX
    } else {
        (1u64 << bit_size) - 1
    };

    let mut n: u64 = 0;
    for &c in s.as_bytes() {
        let lower = c | (b'x' - b'X');
        let d: u8 = if c.is_ascii_digit() {
            c - b'0'
        } else if lower.is_ascii_lowercase() {
            lower - b'a' + 10
        } else {
            return Err(num_error("invalid syntax"));
        };

        if u32::from(d) >= base {
            return Err(num_error("invalid syntax"));
        }

        if n >= cutoff {
            // n*base overflows
            return Err(num_error("value out of range"));
        }
        n *= u64::from(base);

        let n1 = n.wrapping_add(u64::from(d));
        if n1 < n || n1 > max_val {
            // n+d overflows
            return Err(num_error("value out of range"));
        }
        n = n1;
    }

    Ok(n)
}
