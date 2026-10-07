//! Port of Effect-TS/tsgo `internal/typeparser/data_first_signature.go`.

use crate::effect::typeparser::*;
use crate::prelude::*;

/// Go `ParsedDataFirstOrLastCall`.
#[derive(Clone, Debug)]
pub struct ParsedDataFirstOrLastCall {
    pub node: Node,
    pub callee: Node,
    pub subject: Node,
    pub args: Vec<Node>,
    pub subject_index: i32,
}

/// Go `PipeableSignatureWitness`.
#[derive(Clone, Debug)]
pub struct PipeableSignatureWitness {
    pub argument_types: Vec<TypeId>,
    pub subject_type: TypeId,
}

impl TypeParser<'_> {
    // Go: typeparser/data_first_signature.go TypeParser.DataFirstOrLastCall
    pub fn data_first_or_last_call(&mut self, node: Node) -> Option<Rc<ParsedDataFirstOrLastCall>> {
        if node.is_nil() || node.kind() != SyntaxKind::CallExpression {
            return None;
        }
        let call = node;
        if call.expression().is_nil() || call.argument_list().is_nil() || call.arguments().len() < 2
        {
            return None;
        }
        let call_arguments = call.arguments().to_vec();

        for &arg in &call_arguments {
            if arg.is_nil() || arg.kind() == SyntaxKind::SpreadElement {
                return None;
            }
        }

        let resolved = self.checker.get_resolved_signature_exported(node);
        if resolved.is_nil() {
            return None;
        }
        if (call_arguments.len() as i32) < self.checker.sig(resolved).min_argument_count()
            || (call_arguments.len() > self.checker.sig(resolved).parameters().len()
                && !self.checker.sig(resolved).has_rest_parameter())
        {
            return None;
        }

        let resolved_declaration = {
            let raw = raw_signature(self.checker, resolved);
            self.checker.sig(raw).declaration()
        };
        let mut resolved_symbol = SymbolId::NIL;
        if resolved_declaration.is_some() {
            resolved_symbol = self.checker.get_symbol_of_declaration(resolved_declaration);
        }
        if resolved_declaration.is_some() && resolved_symbol.is_nil() {
            return None;
        }
        let callee_type = self.get_type_at_location(call.expression());
        if callee_type.is_nil() {
            return None;
        }
        let candidates = self
            .checker
            .get_signatures_of_type_exported(callee_type, SignatureKind::CALL);

        let mut subject_indexes: Vec<usize> = vec![0];
        if call_arguments.len() == 2 {
            let last = call_arguments.len() - 1;
            let mut prefer_first = false;
            let params = self.checker.sig(resolved).parameters().to_vec();
            if !params.is_empty() {
                prefer_first = is_likely_self_parameter(self.checker, params[0]);
            }
            if prefer_first {
                subject_indexes = vec![0, last];
            } else {
                subject_indexes = vec![last, 0];
            }
        }

        let mut matched: Option<Rc<ParsedDataFirstOrLastCall>> = None;
        for subject_index in subject_indexes {
            let subject_type = self.get_type_at_location(call_arguments[subject_index]);
            if subject_type.is_nil() {
                continue;
            }
            let args = omit_arg_at(&call_arguments, subject_index);
            let mut argument_types: Vec<TypeId> = Vec::with_capacity(args.len());
            for &arg in &args {
                argument_types.push(self.get_type_at_location(arg));
            }
            let witness = PipeableSignatureWitness {
                argument_types,
                subject_type,
            };

            for &candidate in &candidates {
                if candidate.is_nil() {
                    continue;
                }
                if resolved_symbol.is_some() {
                    let candidate_declaration = {
                        let raw = raw_signature(self.checker, candidate);
                        self.checker.sig(raw).declaration()
                    };
                    if candidate_declaration.is_nil() {
                        continue;
                    }
                    let candidate_symbol = self
                        .checker
                        .get_symbol_of_declaration(candidate_declaration);
                    if candidate_symbol.is_nil()
                        || self
                            .checker
                            .get_symbol_if_same_reference(resolved_symbol, candidate_symbol)
                            .is_nil()
                    {
                        continue;
                    }
                }
                if !matches_pipeable_signature(
                    self.checker,
                    resolved,
                    candidate,
                    subject_index as i32,
                    Some(&witness),
                ) {
                    continue;
                }

                if let Some(matched) = &matched
                    && matched.subject_index != subject_index as i32
                {
                    let resolved_parameters = self.checker.sig(resolved).parameters().to_vec();
                    if (matched.subject_index as usize) < resolved_parameters.len()
                        && is_likely_self_parameter(
                            self.checker,
                            resolved_parameters[matched.subject_index as usize],
                        )
                    {
                        return Some(matched.clone());
                    }
                    return None;
                }
                matched = Some(Rc::new(ParsedDataFirstOrLastCall {
                    node: call,
                    callee: call.expression(),
                    subject: call_arguments[subject_index],
                    args,
                    subject_index: subject_index as i32,
                }));
                break;
            }
        }

        matched
    }
}

// Go: typeparser/data_first_signature.go MatchesPipeableSignature
/// MatchesPipeableSignature reports whether candidate is the pipeable form of
/// dataFirst with the parameter at subjectIndex moved into a returned unary function.
/// When witness is nil, parameter types from dataFirst are used for comparison.
pub fn matches_pipeable_signature(
    c: &mut Checker,
    data_first: SignatureId,
    candidate: SignatureId,
    subject_index: i32,
    witness: Option<&PipeableSignatureWitness>,
) -> bool {
    if data_first.is_nil() || candidate.is_nil() {
        return false;
    }
    let params = c.sig(data_first).parameters().to_vec();
    if subject_index < 0 || subject_index as usize >= params.len() {
        return false;
    }

    let argument_types: Vec<TypeId>;
    let mut subject_type = TypeId::NIL;
    if let Some(witness) = witness {
        argument_types = witness.argument_types.clone();
        subject_type = witness.subject_type;
    } else {
        let mut types = Vec::with_capacity(params.len() - 1);
        for (i, &param) in params.iter().enumerate() {
            if i as i32 == subject_index {
                subject_type = c.get_type_of_symbol_exported(param);
                continue;
            }
            types.push(c.get_type_of_symbol_exported(param));
        }
        argument_types = types;
    }

    argument_types_match_parameters(c, &argument_types, candidate)
        && candidate_accepts_subject(c, candidate, subject_type)
        && pipeable_signature_shapes_match(c, data_first, candidate, subject_index)
}

// Go: typeparser/data_first_signature.go argumentTypesMatchParameters
pub fn argument_types_match_parameters(c: &mut Checker, args: &[TypeId], sig: SignatureId) -> bool {
    if sig.is_nil() || (args.len() as i32) < c.sig(sig).min_argument_count() {
        return false;
    }
    let params = c.sig(sig).parameters().to_vec();
    if params.is_empty() {
        return args.is_empty();
    }
    if args.len() > params.len() && !c.sig(sig).has_rest_parameter() {
        return false;
    }
    let has_type_parameters = !c.sig(sig).type_parameters().is_empty();
    for (i, &arg_type) in args.iter().enumerate() {
        let mut param_index = i;
        if param_index >= params.len() {
            param_index = params.len() - 1;
        }
        let param_type = c.get_type_of_symbol_exported(params[param_index]);
        if !type_accepts_argument(c, arg_type, param_type)
            && (!has_type_parameters || !has_compatible_call_shape(c, arg_type, param_type))
        {
            return false;
        }
    }
    true
}

// Go: typeparser/data_first_signature.go candidateAcceptsSubject
pub fn candidate_accepts_subject(
    c: &mut Checker,
    candidate: SignatureId,
    subject_type: TypeId,
) -> bool {
    if candidate.is_nil() || subject_type.is_nil() {
        return false;
    }
    let candidate_return = c.get_return_type_of_signature_exported(candidate);
    if candidate_return.is_nil() {
        return false;
    }
    for returned in c.get_signatures_of_type_exported(candidate_return, SignatureKind::CALL) {
        if returned.is_nil()
            || c.sig(returned).parameters().len() != 1
            || c.sig(returned).has_rest_parameter()
        {
            continue;
        }
        let returned_parameter = c.sig(returned).parameters()[0];
        let parameter_type = c.get_type_of_symbol_exported(returned_parameter);
        if type_accepts_argument(c, subject_type, parameter_type)
            || (!c.sig(candidate).type_parameters().is_empty()
                || !c.sig(returned).type_parameters().is_empty())
                && has_compatible_call_shape(c, subject_type, parameter_type)
        {
            return true;
        }
    }
    false
}

// Go: typeparser/data_first_signature.go hasCompatibleCallShape
pub fn has_compatible_call_shape(c: &mut Checker, left: TypeId, right: TypeId) -> bool {
    if left.is_nil() || right.is_nil() {
        return false;
    }
    let left_callable = !c
        .get_signatures_of_type_exported(left, SignatureKind::CALL)
        .is_empty();
    let right_callable = !c
        .get_signatures_of_type_exported(right, SignatureKind::CALL)
        .is_empty();
    left_callable == right_callable
}

// Go: typeparser/data_first_signature.go typeAcceptsArgument
pub fn type_accepts_argument(c: &mut Checker, argument: TypeId, parameter: TypeId) -> bool {
    if argument.is_nil() || parameter.is_nil() {
        return false;
    }
    if c.ty(parameter)
        .flags()
        .intersects(TypeFlags::TYPE_PARAMETER)
    {
        let constraint = c.get_constraint_of_type_parameter_exported(parameter);
        return constraint.is_nil() || type_accepts_argument(c, argument, constraint);
    }
    same_shallow_type_origin(c, argument, parameter) || c.is_type_assignable_to(argument, parameter)
}

// Go: typeparser/data_first_signature.go sameShallowTypeOrigin
pub fn same_shallow_type_origin(c: &mut Checker, left: TypeId, right: TypeId) -> bool {
    if left == right {
        return true;
    }
    if left.is_nil() || right.is_nil() {
        return false;
    }

    let left_object_flags = c.ty(left).object_flags();
    let right_object_flags = c.ty(right).object_flags();
    if left_object_flags.intersects(ObjectFlags::REFERENCE)
        || right_object_flags.intersects(ObjectFlags::REFERENCE)
    {
        if !left_object_flags.intersects(ObjectFlags::REFERENCE)
            || !right_object_flags.intersects(ObjectFlags::REFERENCE)
        {
            return false;
        }
        let left_target = c.ty(left).target();
        let right_target = c.ty(right).target();
        if left_target == right_target {
            return true;
        }
        let left_target_symbol = c.ty(left_target).symbol();
        let right_target_symbol = c.ty(right_target).symbol();
        return same_symbol_reference(c, left_target_symbol, right_target_symbol);
    }

    let left_alias = c.ty(left).alias();
    let right_alias = c.ty(right).alias();
    if left_alias.is_some() || right_alias.is_some() {
        return match (left_alias, right_alias) {
            (Some(left_alias), Some(right_alias)) => {
                same_symbol_reference(c, left_alias.symbol(), right_alias.symbol())
            }
            _ => false,
        };
    }

    let left_symbol = c.ty(left).symbol();
    let right_symbol = c.ty(right).symbol();
    if left_symbol.is_some() || right_symbol.is_some() {
        return same_symbol_reference(c, left_symbol, right_symbol);
    }

    c.ty(left).flags() == c.ty(right).flags() && c.ty(left).flags().intersects(TypeFlags::SINGLETON)
}

// Go: typeparser/data_first_signature.go sameSymbolReference
pub fn same_symbol_reference(c: &mut Checker, left: SymbolId, right: SymbolId) -> bool {
    left.is_some() && right.is_some() && c.get_symbol_if_same_reference(left, right).is_some()
}

// Go: typeparser/data_first_signature.go DerivePipeableSignatureFromDataFirst
/// DerivePipeableSignatureFromDataFirst removes the subject parameter from a
/// data-first signature and moves it to a unary function in the return type.
pub fn derive_pipeable_signature_from_data_first(
    c: &mut Checker,
    sig: SignatureId,
    subject_index: i32,
) -> SignatureId {
    if sig.is_nil() {
        return SignatureId::NIL;
    }
    let params = c.sig(sig).parameters().to_vec();
    if subject_index < 0 || subject_index as usize >= params.len() {
        return SignatureId::NIL;
    }
    let subject = params[subject_index as usize];
    if subject.is_nil() {
        return SignatureId::NIL;
    }

    let mut outer_params: Vec<SymbolId> = Vec::with_capacity(params.len() - 1);
    for (i, &param) in params.iter().enumerate() {
        if i as i32 == subject_index {
            continue;
        }
        outer_params.push(param);
    }

    let return_type = c.get_return_type_of_signature_exported(sig);
    let inner_fn_type = c.new_function_type(&[], SymbolId::NIL, &[subject], return_type);
    if inner_fn_type.is_nil() {
        return SignatureId::NIL;
    }
    let type_parameters = c.sig(sig).type_parameters().to_vec();
    let this_parameter = c.sig(sig).this_parameter();
    c.new_call_signature(
        &type_parameters,
        this_parameter,
        &outer_params,
        inner_fn_type,
    )
}

// Go: typeparser/data_first_signature.go isLikelySelfParameter
// PORT: Go reads `sym.Name` without a checker; the symbol arena is on the
// checker here. Go `strings.ToLower` maps each rune with `unicode.ToLower`.
pub fn is_likely_self_parameter(c: &Checker, sym: SymbolId) -> bool {
    if sym.is_nil() {
        return false;
    }
    let name: String = c
        .sym(sym)
        .name
        .as_str()
        .chars()
        .map(crate::gostd::unicode::to_lower)
        .collect();
    name == "self" || name.starts_with("self") || name == "this"
}

// Go: typeparser/data_first_signature.go omitArgAt
pub fn omit_arg_at(nodes: &[Node], index: usize) -> Vec<Node> {
    let mut result = Vec::with_capacity(nodes.len().saturating_sub(1));
    for (i, &node) in nodes.iter().enumerate() {
        if i == index {
            continue;
        }
        result.push(node);
    }
    result
}
