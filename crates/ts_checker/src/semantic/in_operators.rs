//! Operand checks for ordinary `in` and class `instanceof` expressions.
//!
//! This follows the pinned membership and non-null operand checks.
//! The source executor checks both expressions first and publishes this batch
//! only after the complete operation succeeds. Private names remain outside
//! this entry. Generic non-null projections remain typed unsupported results.

use std::collections::HashSet;

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::SymbolFlags;
use ts_diagnostics::{Diagnostic, message_by_code};
use ts_scanner::Scanner;

use super::{
    CanonicalCheckerDiagnostic, CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost,
    TypeId,
    bootstrap::UnionReduction,
    classes::{ClassMembers, completed_source_class_members},
    formatter::{
        CanonicalTypeFormatFlags,
        get_type_names_for_assignability_error_with_host_global_types_and_flags,
        type_to_string_with_host_global_types_and_flags,
    },
    instantiate::InstantiationSession,
    logical_operators::{LogicalBinaryError, LogicalBinaryInvariant, base_type_of_literal_type},
    primitive_operators::{
        PrimitiveBinaryError, PrimitiveBinaryInvariant, PrimitiveBinaryRecovery,
        PrimitiveBinaryRequest, PrimitiveBinaryResolution, PrimitiveBinaryUnsupported,
    },
    relater::RelationUnavailable,
    type_records::TypeData,
    types::{ObjectFlags, TypeFlags},
};

/// Checks a completed class shell without changing source or type caches.
pub(super) fn instanceof_class_members(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_: TypeId,
    constructor: bool,
) -> Result<Option<ClassMembers>, RelationUnavailable> {
    let invalid = || RelationUnavailable::InvalidStructuredMembers(type_);
    let record = store.type_payload(type_).ok_or_else(invalid)?;
    let Some(symbol) = record.symbol() else {
        return Ok(None);
    };
    let Some(members) =
        completed_source_class_members(store, host, symbol).map_err(|_| invalid())?
    else {
        return Ok(None);
    };
    let shells = members.shells();
    let expected = if constructor {
        shells.value_type()
    } else {
        shells.instance_type()
    };
    if expected != type_ {
        // Applied generic class references need their own instance projection.
        return Ok(None);
    }
    if constructor && members.static_properties() != [members.prototype()] {
        // A static member can supply Symbol.hasInstance. That needs call resolution.
        return Ok(None);
    }
    Ok(Some(members))
}

/// Checks both operands before returning the canonical boolean result.
pub(super) fn check_instanceof_binary(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    request: PrimitiveBinaryRequest,
) -> Result<PrimitiveBinaryResolution, PrimitiveBinaryError> {
    if request.operator != SyntaxKind::InstanceOfKeyword {
        return Err(PrimitiveBinaryUnsupported::Operator(request.operator).into());
    }
    for (node, type_, recovery) in [
        (request.left, request.left_type, request.left_recovery),
        (request.right, request.right_type, request.right_recovery),
    ] {
        if host.node(node).is_none() {
            return Err(unsupported(node, type_));
        }
        validate_operand(store, global_types, node, type_, recovery)?;
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(PrimitiveBinaryInvariant::MissingBootstrap)?;
    if request.left_type == bootstrap.silent_never_type
        || request.right_type == bootstrap.silent_never_type
    {
        return Ok(PrimitiveBinaryResolution {
            result_type: bootstrap.silent_never_type,
            recovery: None,
            diagnostics: Vec::new(),
        });
    }
    store.validate_union_constituent(bootstrap.boolean_type)?;
    let mut diagnostics = Vec::new();
    let left = operand_leaves(store, request.left, request.left_type)?;
    if left.iter().all(|type_| {
        store.type_payload(*type_).is_some_and(|record| {
            record
                .flags()
                .intersects(TypeFlags::PRIMITIVE | TypeFlags::NEVER)
        })
    }) {
        diagnostics.push(diagnostic(request.left, 2358, Vec::new())?);
    }
    let right = store
        .type_payload(request.right_type)
        .ok_or(PrimitiveBinaryInvariant::InvalidType(request.right_type))?;
    if !right.flags().intersects(TypeFlags::ANY) {
        let leaves = operand_leaves(store, request.right, request.right_type)?;
        if leaves.iter().all(|type_| {
            store.type_payload(*type_).is_some_and(|record| {
                record
                    .flags()
                    .intersects(TypeFlags::PRIMITIVE | TypeFlags::UNKNOWN)
            })
        }) {
            diagnostics.push(diagnostic(request.right, 2359, Vec::new())?);
        } else if instanceof_class_members(store, host, request.right_type, true)?.is_none() {
            return Err(unsupported(request.right, request.right_type));
        }
    }
    Ok(PrimitiveBinaryResolution {
        result_type: bootstrap.boolean_type,
        recovery: None,
        diagnostics,
    })
}

/// Checks both operands without publishing expression links or diagnostics.
pub(super) fn check_in_binary_with_session(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    display_flags: CanonicalTypeFormatFlags,
    session: &mut InstantiationSession,
    request: PrimitiveBinaryRequest,
) -> Result<PrimitiveBinaryResolution, PrimitiveBinaryError> {
    if request.operator != SyntaxKind::InKeyword {
        return Err(PrimitiveBinaryUnsupported::Operator(request.operator).into());
    }
    for (node, type_) in [
        (request.left, request.left_type),
        (request.right, request.right_type),
    ] {
        if host.node(node).is_none() {
            return Err(unsupported(node, type_));
        }
    }
    if host
        .node(request.left)
        .is_some_and(|node| node.kind == SyntaxKind::PrivateIdentifier)
    {
        return Err(unsupported(request.left, request.left_type));
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(PrimitiveBinaryInvariant::MissingBootstrap)?;
    let boolean = bootstrap.boolean_type;
    let silent_never = bootstrap.silent_never_type;
    let key_type = bootstrap.string_number_symbol_type;
    let object_type = bootstrap.non_primitive_type;
    for type_ in [boolean, key_type, object_type] {
        store.validate_union_constituent(type_)?;
    }
    validate_operand(
        store,
        global_types,
        request.left,
        request.left_type,
        request.left_recovery,
    )?;
    validate_operand(
        store,
        global_types,
        request.right,
        request.right_type,
        request.right_recovery,
    )?;
    if request.left_type == silent_never || request.right_type == silent_never {
        return Ok(PrimitiveBinaryResolution {
            result_type: silent_never,
            recovery: None,
            diagnostics: Vec::new(),
        });
    }
    let limit_mark = session.limit_event_mark();
    let mut checker = InOperandChecker {
        store,
        host,
        global_types,
        strict_function_types,
        display_flags,
        session,
        diagnostics: Vec::new(),
    };
    let left = checker.non_null_type(request.left, request.left_type)?;
    checker.check_assignable(request.left, left, key_type)?;
    let right = checker.non_null_type(request.right, request.right_type)?;
    if checker.check_assignable(request.right, right, object_type)?
        && contains_unknown_empty_object(checker.store, request.right, request.right_type)?
    {
        let name = type_to_string_with_host_global_types_and_flags(
            checker.store,
            checker.host,
            checker.global_types,
            request.right_type,
            checker.display_flags,
        )?;
        checker
            .diagnostics
            .push(diagnostic(request.right, 2638, vec![name])?);
    }
    if checker.session.limit_event_occurred_since(limit_mark) {
        checker
            .diagnostics
            .insert(0, diagnostic(request.expression, 2589, Vec::new())?);
    }
    Ok(PrimitiveBinaryResolution {
        result_type: boolean,
        recovery: None,
        diagnostics: checker.diagnostics,
    })
}

fn validate_operand(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    node: NodeRef,
    type_: TypeId,
    recovery: Option<PrimitiveBinaryRecovery>,
) -> Result<(), PrimitiveBinaryError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(PrimitiveBinaryInvariant::MissingBootstrap)?;
    let record = store
        .type_payload(type_)
        .ok_or(PrimitiveBinaryInvariant::InvalidType(type_))?;
    if let Some(recovery) = recovery {
        let expected = match recovery {
            PrimitiveBinaryRecovery::Any => bootstrap.any_type,
            PrimitiveBinaryRecovery::Error => bootstrap.error_type,
        };
        if type_ != expected {
            return Err(PrimitiveBinaryInvariant::InvalidRecovery { type_, recovery }.into());
        }
    }
    if type_ == bootstrap.silent_never_type {
        if record.flags() != TypeFlags::NEVER
            || record.object_flags() != ObjectFlags::NON_INFERRABLE_TYPE
            || record.symbol().is_some()
            || record.alias().is_some()
            || !matches!(record.data(), TypeData::Intrinsic(data) if data.intrinsic_name == "never")
        {
            return Err(PrimitiveBinaryInvariant::InvalidType(type_).into());
        }
        return Ok(());
    }
    if record.flags().intersects(TypeFlags::ANY)
        && type_ != bootstrap.any_type
        && type_ != bootstrap.error_type
    {
        return Err(unsupported(node, type_));
    }
    store.validate_union_constituent_with_global_types(global_types, type_)?;
    Ok(())
}

struct InOperandChecker<'store, 'host, 'source> {
    store: &'store mut CanonicalTypeMapperStore,
    host: &'host DeclaredTypeHost<'source>,
    global_types: &'host CanonicalGlobalTypes,
    strict_function_types: bool,
    display_flags: CanonicalTypeFormatFlags,
    session: &'store mut InstantiationSession,
    diagnostics: Vec<CanonicalCheckerDiagnostic>,
}

impl InOperandChecker<'_, '_, '_> {
    fn non_null_type(
        &mut self,
        node: NodeRef,
        type_: TypeId,
    ) -> Result<TypeId, PrimitiveBinaryError> {
        let bootstrap = self
            .store
            .intrinsic_bootstrap()
            .ok_or(PrimitiveBinaryInvariant::MissingBootstrap)?;
        let strict = bootstrap.options.strict_null_checks;
        let error_type = bootstrap.error_type;
        if strict && type_ == bootstrap.unknown_type {
            let (code, arguments) = match entity_name_text(self.host, node, type_)? {
                Some(name) if name.len() < 100 => (18_046, vec![name]),
                _ => (2571, Vec::new()),
            };
            self.diagnostics.push(diagnostic(node, code, arguments)?);
            self.store.validate_union_constituent(error_type)?;
            return Ok(error_type);
        }
        let leaves = operand_leaves(self.store, node, type_)?;
        let mut is_null = false;
        let mut is_undefined = false;
        let mut retained = Vec::new();
        for leaf in leaves {
            let flags = self
                .store
                .type_payload(leaf)
                .ok_or(PrimitiveBinaryInvariant::InvalidType(leaf))?
                .flags();
            is_null |= flags.intersects(TypeFlags::NULL);
            is_undefined |= flags.intersects(TypeFlags::UNDEFINED);
            if !flags.intersects(TypeFlags::NULLABLE | TypeFlags::VOID | TypeFlags::NEVER) {
                retained.push(leaf);
            }
        }
        if !is_null && !is_undefined {
            return Ok(type_);
        }
        self.diagnostics.push(nullish_diagnostic(
            self.host,
            node,
            type_,
            is_null,
            is_undefined,
        )?);
        let non_null = if strict {
            // Filtering an origin-bearing union needs the pinned origin rewrite.
            // Do not discard an alias path while that operation is unavailable.
            if matches!(self.store.type_payload(type_).map(|record| record.data()), Some(TypeData::Union(union)) if union.origin.is_some())
            {
                return Err(unsupported(node, type_));
            }
            self.store
                .expression_union_type_with_global_types_and_session(
                    self.global_types,
                    &retained,
                    UnionReduction::None,
                    self.session,
                )?
        } else {
            type_
        };
        let flags = self
            .store
            .type_payload(non_null)
            .ok_or(PrimitiveBinaryInvariant::InvalidType(non_null))?
            .flags();
        if flags.intersects(TypeFlags::NULLABLE | TypeFlags::NEVER) {
            self.store.validate_union_constituent(error_type)?;
            Ok(error_type)
        } else {
            Ok(non_null)
        }
    }

    fn check_assignable(
        &mut self,
        node: NodeRef,
        source: TypeId,
        target: TypeId,
    ) -> Result<bool, PrimitiveBinaryError> {
        let assignable = self.store.is_type_assignable_to_with_session(
            source,
            target,
            Some(self.global_types),
            Some(self.strict_function_types),
            self.session,
        )?;
        if !assignable {
            let mut result = self.assignability_diagnostic(node, source, target)?;
            let source_record = self
                .store
                .type_payload(source)
                .ok_or(PrimitiveBinaryInvariant::InvalidType(source))?;
            if let TypeData::Union(union) = source_record.data()
                && !source_record.flags().intersects(TypeFlags::PRIMITIVE)
            {
                let members = union.union.types.clone();
                for member in members {
                    if !self.store.is_type_assignable_to_with_session(
                        member,
                        target,
                        Some(self.global_types),
                        Some(self.strict_function_types),
                        self.session,
                    )? {
                        let detail = self.assignability_diagnostic(node, member, target)?;
                        let text = detail
                            .diagnostic
                            .render()
                            .expect("TS2322 has both type names");
                        result
                            .diagnostic
                            .details
                            .extend(text.lines().map(|line| format!("  {line}")));
                        break;
                    }
                }
            }
            self.diagnostics.push(result);
        }
        Ok(assignable)
    }

    fn assignability_diagnostic(
        &mut self,
        node: NodeRef,
        source: TypeId,
        target: TypeId,
    ) -> Result<CanonicalCheckerDiagnostic, PrimitiveBinaryError> {
        self.validate_key_error_details(node, source, target)?;
        let (source_name, target_name) = if let Some(generalized) =
            self.generalized_literal_type(node, source)?
        {
            let flags = self.display_flags | CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
            (
                type_to_string_with_host_global_types_and_flags(
                    self.store,
                    self.host,
                    self.global_types,
                    generalized,
                    flags,
                )?,
                type_to_string_with_host_global_types_and_flags(
                    self.store,
                    self.host,
                    self.global_types,
                    target,
                    flags,
                )?,
            )
        } else {
            let names = get_type_names_for_assignability_error_with_host_global_types_and_flags(
                self.store,
                self.host,
                self.global_types,
                source,
                target,
                self.display_flags,
            )?;
            (names.source, names.target)
        };
        let mut result = diagnostic(node, 2322, vec![source_name, target_name])?;
        let record = self
            .store
            .type_payload(source)
            .ok_or(PrimitiveBinaryInvariant::InvalidType(source))?;
        if source == self.global_types.object_type
            && record.flags().intersects(TypeFlags::OBJECT)
            && record.symbol().is_some()
        {
            let note = diagnostic(node, 2696, Vec::new())?
                .diagnostic
                .render()
                .expect("TS2696 has no formatting arguments");
            result.diagnostic.details.push(format!("  {note}"));
        }
        Ok(result)
    }

    /// A primitive target union can use augmented interfaces to explain an error.
    fn validate_key_error_details(
        &self,
        node: NodeRef,
        source: TypeId,
        target: TypeId,
    ) -> Result<(), PrimitiveBinaryError> {
        let bootstrap = self
            .store
            .intrinsic_bootstrap()
            .ok_or(PrimitiveBinaryInvariant::MissingBootstrap)?;
        let record = self
            .store
            .type_payload(source)
            .ok_or(PrimitiveBinaryInvariant::InvalidType(source))?;
        if target != bootstrap.string_number_symbol_type
            || !record.flags().intersects(TypeFlags::OBJECT)
        {
            return Ok(());
        }
        // An authenticated empty, non-literal object cannot select a target
        // through discriminants, object-literal matching, or signatures.
        if !record
            .object_flags()
            .contains(ObjectFlags::MEMBERS_RESOLVED)
            || record
                .object_flags()
                .intersects(ObjectFlags::OBJECT_LITERAL)
            || record.data().structured().is_none_or(|members| {
                members
                    .properties
                    .as_ref()
                    .is_some_and(|values| !values.is_empty())
                    || members
                        .signatures
                        .as_ref()
                        .is_some_and(|values| !values.is_empty())
                    || members.call_signature_count != 0
            })
        {
            return Err(unsupported(node, source));
        }
        Ok(())
    }

    /// Keeps literal-union widening and enum display in canonical type space.
    fn generalized_literal_type(
        &mut self,
        node: NodeRef,
        source: TypeId,
    ) -> Result<Option<TypeId>, PrimitiveBinaryError> {
        let record = self
            .store
            .type_payload(source)
            .ok_or(PrimitiveBinaryInvariant::InvalidType(source))?;
        if record.flags().intersects(TypeFlags::ENUM_LIKE) {
            return self.atomic_literal_base(node, source).map(Some);
        }
        let TypeData::Union(union) = record.data() else {
            return Ok(None);
        };
        if record.flags().intersects(TypeFlags::BOOLEAN) {
            return Ok(None);
        }
        for member in &union.union.types {
            let member_record = self
                .store
                .type_payload(*member)
                .ok_or(PrimitiveBinaryInvariant::InvalidType(*member))?;
            if !member_record.flags().intersects(TypeFlags::UNIT) {
                return Ok(None);
            }
        }
        if union.origin.is_some() {
            return Err(unsupported(node, source));
        }
        let members = union.union.types.clone();
        let mut bases = Vec::with_capacity(members.len());
        for member in &members {
            bases.push(self.atomic_literal_base(node, *member)?);
        }
        if bases == members {
            return Ok(Some(source));
        }
        self.store
            .expression_union_type_with_global_types_and_session(
                self.global_types,
                &bases,
                UnionReduction::Literal,
                self.session,
            )
            .map(Some)
            .map_err(Into::into)
    }

    fn atomic_literal_base(
        &mut self,
        node: NodeRef,
        source: TypeId,
    ) -> Result<TypeId, PrimitiveBinaryError> {
        let record = self
            .store
            .type_payload(source)
            .ok_or(PrimitiveBinaryInvariant::InvalidType(source))?;
        // The shared helper's union arm has no caller session. Enum identity
        // and atomic literals do not enter that arm.
        if matches!(record.data(), TypeData::Union(_))
            && !record.flags().intersects(TypeFlags::ENUM_LIKE)
        {
            return Err(unsupported(node, source));
        }
        let base = base_type_of_literal_type(self.store, Some(self.global_types), source)
            .map_err(|error| literal_base_error(node, source, error))?;
        self.store
            .validate_union_constituent_with_global_types(self.global_types, base)?;
        let base_record = self
            .store
            .type_payload(base)
            .ok_or(PrimitiveBinaryInvariant::InvalidType(base))?;
        // A single-member enum keeps its member identity as the declared type.
        // Native errors display the enum name, which the shared formatter cannot.
        if base_record.flags().intersects(TypeFlags::ENUM_LIKE)
            && matches!(base_record.data(), TypeData::Literal(_))
            && base_record
                .symbol()
                .and_then(|symbol| self.store.symbol(symbol))
                .is_some_and(|symbol| symbol.flags() == SymbolFlags::ENUM_MEMBER)
        {
            return Err(unsupported(node, source));
        }
        Ok(base)
    }
}

fn literal_base_error(
    node: NodeRef,
    source: TypeId,
    error: LogicalBinaryError,
) -> PrimitiveBinaryError {
    match error {
        LogicalBinaryError::Literal(error) => error.into(),
        LogicalBinaryError::Invariant(LogicalBinaryInvariant::MissingBootstrap) => {
            PrimitiveBinaryInvariant::MissingBootstrap.into()
        }
        LogicalBinaryError::Invariant(
            LogicalBinaryInvariant::InvalidType(type_)
            | LogicalBinaryInvariant::CyclicUnion(type_)
            | LogicalBinaryInvariant::InvalidUnion(type_),
        ) => PrimitiveBinaryInvariant::InvalidType(type_).into(),
        LogicalBinaryError::Unsupported(_) => unsupported(node, source),
    }
}

/// All leaves were authenticated before this walk. Repeated union members share work.
fn operand_leaves(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    type_: TypeId,
) -> Result<Vec<TypeId>, PrimitiveBinaryError> {
    let mut pending = vec![type_];
    let mut visited = HashSet::new();
    let mut leaves = Vec::new();
    while let Some(current) = pending.pop() {
        if !visited.insert(current) {
            continue;
        }
        let record = store
            .type_payload(current)
            .ok_or(PrimitiveBinaryInvariant::InvalidType(current))?;
        if record
            .flags()
            .intersects(TypeFlags::INSTANTIABLE | TypeFlags::INTERSECTION)
        {
            return Err(unsupported(node, current));
        }
        if let TypeData::Union(union) = record.data() {
            pending.extend(union.union.types.iter().rev().copied());
        } else {
            leaves.push(current);
        }
    }
    Ok(leaves)
}

fn contains_unknown_empty_object(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    type_: TypeId,
) -> Result<bool, PrimitiveBinaryError> {
    let unknown_empty = store
        .intrinsic_bootstrap()
        .ok_or(PrimitiveBinaryInvariant::MissingBootstrap)?
        .unknown_empty_object_type;
    Ok(operand_leaves(store, node, type_)?.contains(&unknown_empty))
}

fn nullish_diagnostic(
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    type_: TypeId,
    is_null: bool,
    is_undefined: bool,
) -> Result<CanonicalCheckerDiagnostic, PrimitiveBinaryError> {
    let record = host.node(node).ok_or_else(|| unsupported(node, type_))?;
    if record.kind == SyntaxKind::NullKeyword {
        return diagnostic(node, 18_050, vec!["null".to_owned()]);
    }
    if let Some(name) = entity_name_text(host, node, type_)?
        && !name.is_empty()
        && name.len() < 100
    {
        if record.kind == SyntaxKind::Identifier && name == "undefined" {
            return diagnostic(node, 18_050, vec![name]);
        }
        let code = match (is_null, is_undefined) {
            (true, true) => 18_049,
            (false, true) => 18_048,
            _ => 18_047,
        };
        return diagnostic(node, code, vec![name]);
    }
    let code = match (is_null, is_undefined) {
        (true, true) => 2533,
        (false, true) => 2532,
        _ => 2531,
    };
    diagnostic(node, code, Vec::new())
}

/// Uses source spelling, including escaped identifiers, as the Go reporter does.
fn entity_name_text(
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
    type_: TypeId,
) -> Result<Option<String>, PrimitiveBinaryError> {
    let mut current = node;
    let mut visited = HashSet::new();
    let mut parts = Vec::new();
    loop {
        if !visited.insert(current) {
            return Err(unsupported(node, type_));
        }
        let record = host.node(current).ok_or_else(|| unsupported(node, type_))?;
        let name = match &record.data {
            NodeData::Identifier(_) => current,
            NodeData::PropertyAccessExpression(access) => {
                NodeRef::new(current.arena, current.file, access.name)
            }
            _ => return Ok(None),
        };
        let name_record = host.node(name).ok_or_else(|| unsupported(node, type_))?;
        if name_record.kind != SyntaxKind::Identifier {
            return Ok(None);
        }
        let (arena, _) = host.source(name).ok_or_else(|| unsupported(node, type_))?;
        let fragment = arena
            .source_text()
            .and_then(|text| {
                text.get(
                    name_record.range.start.get() as usize..name_record.range.end.get() as usize,
                )
            })
            .ok_or_else(|| unsupported(node, type_))?;
        let mut scanner = Scanner::new(fragment);
        let token = scanner.scan();
        if token.text.is_empty()
            || !scanner.diagnostics().is_empty()
            || scanner.scan().kind != SyntaxKind::EndOfFile
        {
            return Err(unsupported(node, type_));
        }
        parts.push(token.text.to_owned());
        if let NodeData::PropertyAccessExpression(access) = &record.data {
            current = NodeRef::new(current.arena, current.file, access.expression);
        } else {
            break;
        }
    }
    parts.reverse();
    Ok(Some(parts.join(".")))
}

fn diagnostic(
    node: NodeRef,
    code: u32,
    arguments: Vec<String>,
) -> Result<CanonicalCheckerDiagnostic, PrimitiveBinaryError> {
    let message = message_by_code(code).ok_or(PrimitiveBinaryInvariant::MissingDiagnostic(code))?;
    Ok(CanonicalCheckerDiagnostic {
        node: Some(node),
        range_override: None,
        diagnostic: Diagnostic::with_arguments(message, arguments),
        related_information: Vec::new(),
    })
}

fn unsupported(node: NodeRef, type_: TypeId) -> PrimitiveBinaryError {
    PrimitiveBinaryUnsupported::Operand { node, type_ }.into()
}
