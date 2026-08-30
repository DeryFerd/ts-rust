use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, NodeLinks,
    SignatureId, SignatureLinks, SourceCheckError, SourceFileLinks, SymbolNodeLinks, TypeData,
    TypeId, TypeNodeLinks, UnsupportedSourceSyntax, ValueSymbolLinks, VariableUnsupported,
    artifact_queries::CanonicalArtifactQueryError, signatures::SignatureFlags,
    type_records::LiteralValue, types::TypeFlags,
};
use ts_jsnum::Number;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(58_440);

// Keep the complete pinned blockedScopeVariableNotUnused1.ts source.
const ORIGINAL: &str = r#"// @strict: true

export function foo() {
  const _fn = () => {
    ;(() => numFilesSelected)()
  }

  const numFilesSelected = 1
}
"#;

const SIBLINGS: &str = concat!(
    "const value = 'outer';\n",
    "export function siblings() {\n",
    "  const left = () => { const copy = value; (() => copy)(); };\n",
    "  const right = () => { const copy = value; (() => copy)(); };\n",
    "  const value = 1;\n",
    "}\n",
);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/deferred-arrow-scope.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::External,
            )
            .with_always_strict(true),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            strict_bind_call_apply: true,
            strict_builtin_iterator_return: true,
            strict_function_types: true,
            strict_property_initialization: true,
            use_unknown_in_catch_variables: true,
            no_implicit_any: true,
            no_implicit_this: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn child(parsed: &ParseResult, parent: NodeRef, id: NodeId) -> NodeRef {
    let record = parsed.arena.get(id).unwrap();
    assert_eq!(record.parent, Some(parent.node));
    let parent_range = parsed.arena.get(parent.node).unwrap().range;
    assert!(parent_range.start <= record.range.start);
    assert!(record.range.end <= parent_range.end);
    node(parsed, id)
}

fn identifier(parsed: &ParseResult, location: NodeRef, expected: &str) {
    let record = parsed.arena.get(location.node).unwrap();
    assert_eq!(record.kind, SyntaxKind::Identifier);
    let NodeData::Identifier(identifier) = &record.data else {
        panic!("expected identifier {expected}")
    };
    assert_eq!(identifier.text, expected);
}

#[derive(Clone, Copy)]
struct Function {
    declaration: NodeRef,
    name: NodeRef,
    body: NodeRef,
}

fn function(parsed: &ParseResult, expected: &str) -> Function {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::FunctionDeclaration(function) = &record.data else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(function.name?).unwrap().data else {
            return None;
        };
        (name.text == expected).then_some((node(parsed, id), function))
    });
    let (declaration, function) = matches.next().expect("the named function must exist");
    assert!(matches.next().is_none());
    assert!(function.parameters.nodes.is_empty());
    assert!(function.type_parameters.is_none());
    assert!(function.type_.is_none());
    Function {
        declaration,
        name: child(parsed, declaration, function.name.unwrap()),
        body: child(parsed, declaration, function.body.unwrap()),
    }
}

#[derive(Clone, Copy)]
struct Binding {
    declaration: NodeRef,
    name: NodeRef,
    initializer: NodeRef,
}

fn binding(parsed: &ParseResult, block: NodeRef, expected: &str) -> Binding {
    let mut matches = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::VariableDeclaration(variable) = &record.data else {
            return None;
        };
        let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
            return None;
        };
        let list = parsed.arena.get(record.parent?)?;
        let statement = parsed.arena.get(list.parent?)?;
        (name.text == expected && statement.parent == Some(block.node)).then_some((
            node(parsed, id),
            variable,
            record.parent?,
            list.parent?,
        ))
    });
    let (declaration, variable, list, statement) =
        matches.next().expect("the block must own this binding");
    assert!(matches.next().is_none(), "duplicate binding {expected}");
    let statement = child(parsed, block, statement);
    assert_eq!(
        parsed.arena.get(statement.node).unwrap().kind,
        SyntaxKind::VariableStatement
    );
    let list = child(parsed, statement, list);
    assert_eq!(
        parsed.arena.get(list.node).unwrap().kind,
        SyntaxKind::VariableDeclarationList
    );
    assert_eq!(child(parsed, list, declaration.node), declaration);
    assert!(variable.type_.is_none());
    Binding {
        declaration,
        name: child(parsed, declaration, variable.name),
        initializer: child(parsed, declaration, variable.initializer.unwrap()),
    }
}

#[derive(Clone, Copy)]
struct ArrowCall {
    outer: NodeRef,
    body: NodeRef,
    call: NodeRef,
    callee: NodeRef,
    inner: NodeRef,
    read: NodeRef,
}

fn arrow_call(parsed: &ParseResult, outer: NodeRef) -> ArrowCall {
    let NodeData::ArrowFunction(arrow) = &parsed.arena.get(outer.node).unwrap().data else {
        panic!("the stored initializer must be the real arrow")
    };
    assert!(arrow.parameters.nodes.is_empty());
    assert!(arrow.type_parameters.is_none());
    assert!(arrow.type_.is_none());
    let body = child(parsed, outer, arrow.body);
    let NodeData::Block(block) = &parsed.arena.get(body.node).unwrap().data else {
        panic!("the stored arrow must retain its block")
    };
    let mut calls = block.statements.nodes.iter().filter_map(|&id| {
        let statement = child(parsed, body, id);
        let NodeData::ExpressionStatement(expression) =
            &parsed.arena.get(statement.node).unwrap().data
        else {
            return None;
        };
        Some(child(parsed, statement, expression.expression))
    });
    let call = calls.next().expect("the body must contain its IIFE");
    assert!(calls.next().is_none());
    let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("the expression statement must retain the call")
    };
    assert!(call_data.arguments.nodes.is_empty());
    assert!(call_data.type_arguments.is_none());
    let callee = child(parsed, call, call_data.expression);
    let NodeData::ParenthesizedExpression(parenthesized) =
        &parsed.arena.get(callee.node).unwrap().data
    else {
        panic!("the IIFE callee must retain its parentheses")
    };
    let inner = child(parsed, callee, parenthesized.expression);
    let NodeData::ArrowFunction(arrow) = &parsed.arena.get(inner.node).unwrap().data else {
        panic!("the callee must be the inner source arrow")
    };
    assert!(arrow.parameters.nodes.is_empty());
    assert!(arrow.type_parameters.is_none());
    assert!(arrow.type_.is_none());
    ArrowCall {
        outer,
        body,
        call,
        callee,
        inner,
        read: child(parsed, inner, arrow.body),
    }
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn value_type(context: &CanonicalCheckerContext<'_>, owner: SemanticSymbolId) -> TypeId {
    context
        .store()
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .expect("source checking must publish the actual binding type")
}

fn cached_type(context: &CanonicalCheckerContext<'_>, location: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(location)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("source checking must publish the type at {location:?}"))
}

fn signature(context: &CanonicalCheckerContext<'_>, location: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(location)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the real callable or call must retain its signature")
}

fn is_checked(context: &CanonicalCheckerContext<'_>) -> bool {
    context
        .store()
        .source_file_links(context.source_file(FILE).unwrap())
        .is_some_and(|links| links.type_checked)
}

#[derive(Debug, Eq, PartialEq)]
struct Callable {
    declaration: NodeRef,
    owner: SemanticSymbolId,
    type_: TypeId,
    signature: SignatureId,
    returned: TypeId,
}

fn callable(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> Callable {
    let owner = symbol(context, declaration);
    let owner_record = context.store().symbol(owner).unwrap();
    assert_eq!(owner_record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(owner_record.declarations(), Some(&[declaration][..]));
    assert_eq!(owner_record.value_declaration(), Some(declaration));
    let type_ = value_type(context, owner);
    let signature = signature(context, declaration);
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("the source callable must have its actual object type")
    };
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    assert_eq!(object.target, None);
    assert_eq!(object.mapper, None);
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert!(record.type_parameters().is_empty());
    assert!(record.parameters().is_empty());
    assert_eq!(record.min_argument_count(), 0);
    assert_eq!(record.this_parameter(), None);
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    Callable {
        declaration,
        owner,
        type_,
        signature,
        returned: record
            .resolved_return_type()
            .expect("source checking must finish the real return"),
    }
}

fn binding_owner(
    context: &CanonicalCheckerContext<'_>,
    binding: Binding,
    scope: NodeRef,
    name: &str,
) -> SemanticSymbolId {
    let owner = symbol(context, binding.declaration);
    let record = context.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::BLOCK_SCOPED_VARIABLE);
    assert_eq!(record.declarations(), Some(&[binding.declaration][..]));
    assert_eq!(record.value_declaration(), Some(binding.declaration));
    let (_, bound) = context.file(FILE).unwrap();
    assert_eq!(
        bound.block_scope_container(binding.declaration),
        Some(scope)
    );
    assert_eq!(
        context
            .store()
            .symbol_table(bound.locals(scope).unwrap())
            .unwrap()
            .get_source(name),
        Some(owner)
    );
    owner
}

fn literal_one(context: &CanonicalCheckerContext<'_>, type_: TypeId) {
    let record = context.store().type_payload(type_).unwrap();
    assert_eq!(record.flags(), TypeFlags::NUMBER_LITERAL);
    let TypeData::Literal(literal) = record.data() else {
        panic!("the later const must keep its checked literal")
    };
    let LiteralValue::Number(value) = &literal.value else {
        panic!("the source literal must be numeric")
    };
    assert_eq!(*value, Number::new(1.0));
    assert_eq!(literal.fresh_type, Some(type_));
    assert_ne!(literal.regular_type, type_);
    let TypeData::Literal(regular) = context
        .store()
        .type_payload(literal.regular_type)
        .unwrap()
        .data()
    else {
        panic!("the fresh literal must retain its regular pair")
    };
    assert_eq!(regular.value, literal.value);
    assert_eq!(regular.regular_type, literal.regular_type);
    assert_eq!(regular.fresh_type, Some(type_));
}

#[derive(Debug, Eq, PartialEq)]
struct Proof {
    callables: Vec<Callable>,
    types: Vec<(NodeRef, TypeId)>,
    symbols: Vec<(NodeRef, SemanticSymbolId)>,
}

fn append_arrow_proof(
    context: &CanonicalCheckerContext<'_>,
    proof: &mut Proof,
    binding: Binding,
    pair: ArrowCall,
    binding_owner: SemanticSymbolId,
    read_owner: SemanticSymbolId,
    literal: TypeId,
) {
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let outer = callable(context, pair.outer);
    let inner = callable(context, pair.inner);
    assert_eq!(outer.returned, bootstrap.void_type);
    assert_eq!(inner.returned, bootstrap.number_type);
    assert_ne!(outer.owner, inner.owner);
    assert_ne!(outer.owner, binding_owner);
    assert_ne!(inner.owner, binding_owner);
    assert_ne!(outer.signature, inner.signature);
    assert_eq!(value_type(context, binding_owner), outer.type_);
    assert_eq!(cached_type(context, pair.outer), outer.type_);
    assert_eq!(cached_type(context, pair.inner), inner.type_);
    assert_eq!(cached_type(context, pair.callee), inner.type_);
    assert_eq!(cached_type(context, pair.call), bootstrap.number_type);
    assert_eq!(signature(context, pair.call), inner.signature);
    assert_eq!(cached_type(context, pair.read), literal);
    assert_eq!(
        context
            .store()
            .symbol_node_links(pair.read)
            .unwrap()
            .resolved_symbol,
        Some(read_owner)
    );
    proof.types.extend([
        (binding.name, outer.type_),
        (pair.outer, outer.type_),
        (pair.callee, inner.type_),
        (pair.inner, inner.type_),
        (pair.call, bootstrap.number_type),
        (pair.read, literal),
    ]);
    proof
        .symbols
        .extend([(binding.name, binding_owner), (pair.read, read_owner)]);
    proof.callables.extend([outer, inner]);
}

fn function_proof(context: &CanonicalCheckerContext<'_>, function: Function) -> Proof {
    let callable = callable(context, function.declaration);
    assert_eq!(
        callable.returned,
        context.store().intrinsic_bootstrap().unwrap().void_type
    );
    let (_, bound) = context.file(FILE).unwrap();
    let local = context
        .store()
        .get_merged_symbol(bound.local_symbol(function.declaration).unwrap())
        .unwrap();
    assert_ne!(local, callable.owner);
    let local_record = context.store().symbol(local).unwrap();
    assert_eq!(local_record.flags(), SymbolFlags::EXPORT_VALUE);
    assert_eq!(local_record.export_symbol(), Some(callable.owner));
    assert_eq!(
        local_record.declarations(),
        Some(&[function.declaration][..])
    );
    Proof {
        types: vec![
            (function.declaration, callable.type_),
            (function.name, callable.type_),
        ],
        symbols: vec![(function.name, callable.owner)],
        callables: vec![callable],
    }
}

fn original_proof(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Proof {
    let function = function(parsed, "foo");
    let stored = binding(parsed, function.body, "_fn");
    let value = binding(parsed, function.body, "numFilesSelected");
    assert_ne!(stored.declaration, value.declaration);
    assert!(
        parsed
            .arena
            .get(stored.declaration.node)
            .unwrap()
            .range
            .start
            < parsed
                .arena
                .get(value.declaration.node)
                .unwrap()
                .range
                .start
    );
    let pair = arrow_call(parsed, stored.initializer);
    identifier(parsed, pair.read, "numFilesSelected");
    let NodeData::Block(block) = &parsed.arena.get(pair.body.node).unwrap().data else {
        unreachable!()
    };
    let [empty, expression] = block.statements.nodes.as_slice() else {
        panic!("the unchanged arrow block must keep both original statements")
    };
    let empty = child(parsed, pair.body, *empty);
    assert_eq!(
        parsed.arena.get(empty.node).unwrap().kind,
        SyntaxKind::EmptyStatement
    );
    assert_eq!(
        parsed.arena.get(*expression).unwrap().kind,
        SyntaxKind::ExpressionStatement
    );
    let stored_owner = binding_owner(context, stored, function.declaration, "_fn");
    let value_owner = binding_owner(context, value, function.declaration, "numFilesSelected");
    let literal = value_type(context, value_owner);
    literal_one(context, literal);
    assert_eq!(cached_type(context, value.initializer), literal);
    let mut proof = function_proof(context, function);
    append_arrow_proof(
        context,
        &mut proof,
        stored,
        pair,
        stored_owner,
        value_owner,
        literal,
    );
    assert!(
        proof
            .callables
            .iter()
            .skip(1)
            .all(|callable| callable.owner != proof.callables[0].owner)
    );
    proof
        .types
        .extend([(value.name, literal), (value.initializer, literal)]);
    proof.symbols.push((value.name, value_owner));
    proof
}

#[derive(Debug, Eq, PartialEq)]
struct NodeState {
    node: NodeRef,
    common: Option<NodeLinks>,
    symbol: Option<SymbolNodeLinks>,
    type_: Option<TypeNodeLinks>,
    signature: Option<SignatureLinks>,
}

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 7],
    nodes: Vec<NodeState>,
    values: Vec<(SemanticSymbolId, Option<ValueSymbolLinks>)>,
    source: Option<SourceFileLinks>,
}

fn publication(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Publication {
    let store = context.store();
    Publication {
        counts: [
            store.type_len(),
            store.type_alias_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        nodes: parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = node(parsed, id);
                NodeState {
                    node,
                    common: store.node_links(node).cloned(),
                    symbol: store.symbol_node_links(node).cloned(),
                    type_: store.type_node_links(node).cloned(),
                    signature: store.signature_links(node).cloned(),
                }
            })
            .collect(),
        values: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect(),
        source: store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
    }
}

fn public_queries(context: &mut CanonicalCheckerContext<'_>, proof: &Proof) {
    for &(node, type_) in &proof.types {
        assert_eq!(context.get_type_at_location(node), Ok(type_), "{node:?}");
    }
    for &(node, symbol) in &proof.symbols {
        assert_eq!(
            context.get_symbol_at_location(node),
            Ok(Some(symbol)),
            "{node:?}"
        );
    }
    for callable in &proof.callables {
        assert_eq!(
            context.get_return_type_of_signature(callable.signature),
            Ok(callable.returned)
        );
        assert_eq!(
            context.get_symbol_declarations(callable.owner).unwrap(),
            [callable.declaration]
        );
        let expected =
            if callable.returned == context.store().intrinsic_bootstrap().unwrap().void_type {
                "() => void"
            } else {
                "() => number"
            };
        assert_eq!(context.type_to_string(callable.type_).unwrap(), expected);
    }
}

fn assert_replay(context: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult, proof: &Proof) {
    public_queries(context, proof);
    let warm = publication(context, parsed);
    let diagnostics = context.diagnostics().clone();
    for _ in 0..2 {
        context.check_source_file(FILE).unwrap();
        public_queries(context, proof);
        context.recheck_source_file(FILE).unwrap();
        public_queries(context, proof);
        assert!(is_checked(context));
        assert_eq!(publication(context, parsed), warm);
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

#[test]
fn blocked_scope_original_keeps_deferred_local_and_callable_identities_in_both_query_orders() {
    let parsed = parse_source_file(ORIGINAL);
    let function = function(&parsed, "foo");
    let stored = binding(&parsed, function.body, "_fn");
    let pair = arrow_call(&parsed, stored.initializer);
    for first_query in [None, Some(function.name), Some(pair.outer), Some(pair.call)] {
        let mut context = context(&parsed);
        assert!(!is_checked(&context));
        let first_type =
            first_query.map(|location| context.get_type_at_location(location).unwrap());
        if first_query.is_some() {
            assert!(is_checked(&context));
        }
        context.check_source_file(FILE).unwrap();
        assert!(is_checked(&context));
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        // Check the stored source result before any later-local artifact query.
        let proof = original_proof(&context, &parsed);
        if let Some(location) = first_query {
            assert_eq!(
                first_type,
                proof
                    .types
                    .iter()
                    .find_map(|&(node, type_)| (node == location).then_some(type_))
            );
        }
        assert_replay(&mut context, &parsed, &proof);
        assert_eq!(original_proof(&context, &parsed), proof);
    }
}

#[test]
fn deferred_sibling_bodies_keep_the_shadowed_value_and_distinct_local_owners() {
    let parsed = parse_source_file(SIBLINGS);
    let function = function(&parsed, "siblings");
    let left = binding(&parsed, function.body, "left");
    let right = binding(&parsed, function.body, "right");
    let left_pair = arrow_call(&parsed, left.initializer);
    let right_pair = arrow_call(&parsed, right.initializer);
    let value = binding(&parsed, function.body, "value");
    let shadowed = binding(&parsed, node(&parsed, parsed.source_file), "value");
    for first_query in [None, Some(right_pair.call)] {
        let mut context = context(&parsed);
        if let Some(location) = first_query {
            context.get_type_at_location(location).unwrap();
            assert!(is_checked(&context));
        }
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let value_owner = binding_owner(&context, value, function.declaration, "value");
        let shadowed_owner = symbol(&context, shadowed.declaration);
        assert_ne!(value_owner, shadowed_owner);
        let literal = value_type(&context, value_owner);
        literal_one(&context, literal);
        let shadowed_type = value_type(&context, shadowed_owner);
        assert_ne!(literal, shadowed_type);
        assert_eq!(
            context.store().type_payload(shadowed_type).unwrap().flags(),
            TypeFlags::STRING_LITERAL
        );
        let mut proof = function_proof(&context, function);
        let mut copy_owners = Vec::new();
        for (stored, pair, name) in [(left, left_pair, "left"), (right, right_pair, "right")] {
            let stored_owner = binding_owner(&context, stored, function.declaration, name);
            let copy = binding(&parsed, pair.body, "copy");
            let copy_owner = binding_owner(&context, copy, pair.outer, "copy");
            identifier(&parsed, copy.initializer, "value");
            identifier(&parsed, pair.read, "copy");
            assert_eq!(value_type(&context, copy_owner), literal);
            assert_eq!(cached_type(&context, copy.initializer), literal);
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(copy.initializer)
                    .unwrap()
                    .resolved_symbol,
                Some(value_owner)
            );
            append_arrow_proof(
                &context,
                &mut proof,
                stored,
                pair,
                stored_owner,
                copy_owner,
                literal,
            );
            proof
                .types
                .extend([(copy.name, literal), (copy.initializer, literal)]);
            proof
                .symbols
                .extend([(copy.name, copy_owner), (copy.initializer, value_owner)]);
            copy_owners.push(copy_owner);
        }
        assert_ne!(copy_owners[0], copy_owners[1]);
        assert!(
            copy_owners
                .iter()
                .all(|owner| *owner != value_owner && *owner != shadowed_owner)
        );
        for (index, callable) in proof.callables.iter().enumerate() {
            for other in &proof.callables[..index] {
                assert_ne!(callable.owner, other.owner);
                assert_ne!(callable.signature, other.signature);
            }
        }
        proof.types.extend([
            (value.name, literal),
            (value.initializer, literal),
            (shadowed.name, shadowed_type),
        ]);
        proof
            .symbols
            .extend([(value.name, value_owner), (shadowed.name, shadowed_owner)]);
        assert_replay(&mut context, &parsed, &proof);
    }
}

fn assert_unsupported(
    source: &str,
    function_name: &str,
    expected_forward_read: Option<fn(&ParseResult, Function) -> NodeRef>,
) {
    let parsed = parse_source_file(source);
    let function = function(&parsed, function_name);
    for query_first in [false, true] {
        let mut context = context(&parsed);
        let cold = publication(&context, &parsed);
        let error = if query_first {
            let CanonicalArtifactQueryError::SourceCheck(error) =
                context.get_type_at_location(function.name).unwrap_err()
            else {
                panic!("the first query must report the source boundary: {source}")
            };
            error
        } else {
            context.check_source_file(FILE).unwrap_err()
        };
        assert!(
            matches!(error, SourceCheckError::Unsupported(_)),
            "{source}: {error:?}"
        );
        if let Some(read) = expected_forward_read {
            let later = binding(&parsed, function.body, "later");
            assert_eq!(
                error,
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Variable(
                    VariableUnsupported::IdentifierNotPrior {
                        node: read(&parsed, function),
                        symbol: symbol(&context, later.declaration),
                        declaration: later.declaration,
                    }
                )),
                "{source}"
            );
        }
        for _ in 0..2 {
            assert_eq!(context.check_source_file(FILE), Err(error), "{source}");
            assert_eq!(context.recheck_source_file(FILE), Err(error), "{source}");
            assert_eq!(
                context.get_type_at_location(function.name),
                Err(CanonicalArtifactQueryError::SourceCheck(error)),
                "{source}"
            );
            assert_eq!(publication(&context, &parsed), cold, "{source}");
            assert!(!is_checked(&context), "{source}");
            assert!(context.diagnostics().is_empty(), "{source}");
        }
    }
}

#[test]
fn eager_forward_reads_do_not_gain_the_deferred_body_scope() {
    assert_unsupported(
        "export function eager() { const read = later; const later = 1; }",
        "eager",
        Some(|parsed, function| binding(parsed, function.body, "read").initializer),
    );
    assert_unsupported(
        "export function eager() { const read = (() => later)(); const later = 1; }",
        "eager",
        Some(|parsed, _| {
            let mut arrows = parsed.arena.iter().filter_map(|(id, record)| {
                let NodeData::ArrowFunction(arrow) = &record.data else {
                    return None;
                };
                Some(child(parsed, node(parsed, id), arrow.body))
            });
            let read = arrows.next().unwrap();
            assert!(arrows.next().is_none());
            identifier(parsed, read, "later");
            read
        }),
    );
}

#[test]
fn deferred_return_cycles_and_value_returning_bodies_keep_their_prior_boundary() {
    for (name, source) in [
        (
            "cycle",
            "export function cycle() { const first = () => second(); const second = () => first(); }",
        ),
        (
            "value",
            "export function value() { const fn = () => { return later; }; const later = 1; }",
        ),
        (
            "outer",
            "export function outer() { const fn = () => { (() => later)(); }; const later = 1; return later; }",
        ),
    ] {
        assert_unsupported(source, name, None);
    }
}
