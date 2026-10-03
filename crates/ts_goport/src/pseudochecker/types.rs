//! Port of Go `pseudochecker/type.go`.

use crate::prelude::*;

use crate::flags_macros::go_enum;

// `PseudoType`s are skeletons of types - partially interpreted expressions and type nodes
// composed to represent how you *should* construct a type out of them. They can be trivially
// mapped into actual types by a real `Checker`, or into a tree of `Node`s directly, without
// needing to make any intermediate types, by a `NodeBuilder`. Unlike checker `Type`s, these are
// never normalized, and multiple pseudo-types may refer to the same underlying `Type`.

// In strada, these were implicit in the AST nodes constructed in `expressionToTypeNode.ts`, which
// repurposed AST nodes for this purpose, but in so doing, often confused weather or not it had validated
// nested nodes for use at a given use-site. By keeping the mapping deferred like this, we can know we haven't
// done any use-site checks until we're ready to map the `PseudoType` into a `Node`, and can cache
// `PseudoType`s across multiple target positions.

go_enum!(PseudoTypeKind, i16 {
    DIRECT = 0; // PseudoTypeKindDirect
    INFERRED = 1; // PseudoTypeKindInferred
    NO_RESULT = 2; // PseudoTypeKindNoResult
    MAYBE_CONST_LOCATION = 3; // PseudoTypeKindMaybeConstLocation
    UNION = 4; // PseudoTypeKindUnion
    UNDEFINED = 5; // PseudoTypeKindUndefined
    NULL = 6; // PseudoTypeKindNull
    ANY = 7; // PseudoTypeKindAny
    STRING = 8; // PseudoTypeKindString
    NUMBER = 9; // PseudoTypeKindNumber
    BIG_INT = 10; // PseudoTypeKindBigInt
    BOOLEAN = 11; // PseudoTypeKindBoolean
    FALSE = 12; // PseudoTypeKindFalse
    TRUE = 13; // PseudoTypeKindTrue
    SINGLE_CALL_SIGNATURE = 14; // PseudoTypeKindSingleCallSignature
    TUPLE = 15; // PseudoTypeKindTuple
    OBJECT_LITERAL = 16; // PseudoTypeKindObjectLiteral
    STRING_LITERAL = 17; // PseudoTypeKindStringLiteral
    NUMERIC_LITERAL = 18; // PseudoTypeKindNumericLiteral
    BIG_INT_LITERAL = 19; // PseudoTypeKindBigIntLiteral
});

/// Go `*PseudoType`. Go `*PseudoType` values are `Rc<PseudoType>`.
// PORT: Go stores the kind plus a `pseudoTypeData` interface that embeds the
// `PseudoType` header. Here the header holds the kind and an enum with one
// variant per Go data struct. `PseudoTypeBase`/`PseudoTypeDefault` carry no
// fields and are the `Base` variant. A Go type assertion on the wrong data
// panics, and so do the `as_*` accessors.
#[derive(Debug)]
pub struct PseudoType {
    pub kind: PseudoTypeKind,
    data: PseudoTypeData,
}

#[derive(Debug)]
pub enum PseudoTypeData {
    Base,
    Direct(PseudoTypeDirect),
    Inferred(PseudoTypeInferred),
    NoResult(PseudoTypeNoResult),
    MaybeConstLocation(PseudoTypeMaybeConstLocation),
    Union(PseudoTypeUnion),
    SingleCallSignature(PseudoTypeSingleCallSignature),
    Tuple(PseudoTypeTuple),
    ObjectLiteral(PseudoTypeObjectLiteral),
    Literal(PseudoTypeLiteral),
}

// Go: pseudochecker/type.go:49 newPseudoType
fn new_pseudo_type(kind: PseudoTypeKind, data: PseudoTypeData) -> Rc<PseudoType> {
    Rc::new(PseudoType { kind, data })
}

// PORT: Go package vars. `Rc` is not `Sync`, so each is a thread-local
// singleton returned by a function with the snake name of the Go var. The
// same `Rc` comes back on each call, as the Go pointer does.
thread_local! {
    static PSEUDO_TYPE_UNDEFINED: Rc<PseudoType> = new_pseudo_type(PseudoTypeKind::UNDEFINED, PseudoTypeData::Base);
    static PSEUDO_TYPE_NULL: Rc<PseudoType> = new_pseudo_type(PseudoTypeKind::NULL, PseudoTypeData::Base);
    static PSEUDO_TYPE_ANY: Rc<PseudoType> = new_pseudo_type(PseudoTypeKind::ANY, PseudoTypeData::Base);
    static PSEUDO_TYPE_STRING: Rc<PseudoType> = new_pseudo_type(PseudoTypeKind::STRING, PseudoTypeData::Base);
    static PSEUDO_TYPE_NUMBER: Rc<PseudoType> = new_pseudo_type(PseudoTypeKind::NUMBER, PseudoTypeData::Base);
    static PSEUDO_TYPE_BIG_INT: Rc<PseudoType> = new_pseudo_type(PseudoTypeKind::BIG_INT, PseudoTypeData::Base);
    static PSEUDO_TYPE_BOOLEAN: Rc<PseudoType> = new_pseudo_type(PseudoTypeKind::BOOLEAN, PseudoTypeData::Base);
    static PSEUDO_TYPE_FALSE: Rc<PseudoType> = new_pseudo_type(PseudoTypeKind::FALSE, PseudoTypeData::Base);
    static PSEUDO_TYPE_TRUE: Rc<PseudoType> = new_pseudo_type(PseudoTypeKind::TRUE, PseudoTypeData::Base);
}

// Go: pseudochecker/type.go:71 PseudoTypeUndefined
pub fn pseudo_type_undefined() -> Rc<PseudoType> {
    PSEUDO_TYPE_UNDEFINED.with(Rc::clone)
}

// Go: pseudochecker/type.go:72 PseudoTypeNull
pub fn pseudo_type_null() -> Rc<PseudoType> {
    PSEUDO_TYPE_NULL.with(Rc::clone)
}

// Go: pseudochecker/type.go:73 PseudoTypeAny
pub fn pseudo_type_any() -> Rc<PseudoType> {
    PSEUDO_TYPE_ANY.with(Rc::clone)
}

// Go: pseudochecker/type.go:74 PseudoTypeString
pub fn pseudo_type_string() -> Rc<PseudoType> {
    PSEUDO_TYPE_STRING.with(Rc::clone)
}

// Go: pseudochecker/type.go:75 PseudoTypeNumber
pub fn pseudo_type_number() -> Rc<PseudoType> {
    PSEUDO_TYPE_NUMBER.with(Rc::clone)
}

// Go: pseudochecker/type.go:76 PseudoTypeBigInt
pub fn pseudo_type_big_int() -> Rc<PseudoType> {
    PSEUDO_TYPE_BIG_INT.with(Rc::clone)
}

// Go: pseudochecker/type.go:77 PseudoTypeBoolean
pub fn pseudo_type_boolean() -> Rc<PseudoType> {
    PSEUDO_TYPE_BOOLEAN.with(Rc::clone)
}

// Go: pseudochecker/type.go:78 PseudoTypeFalse
pub fn pseudo_type_false() -> Rc<PseudoType> {
    PSEUDO_TYPE_FALSE.with(Rc::clone)
}

// Go: pseudochecker/type.go:79 PseudoTypeTrue
pub fn pseudo_type_true() -> Rc<PseudoType> {
    PSEUDO_TYPE_TRUE.with(Rc::clone)
}

/// PseudoTypeDirect directly encodes the type referred to by a given TypeNode
#[derive(Debug)]
pub struct PseudoTypeDirect {
    pub type_node: Node,
}

// Go: pseudochecker/type.go:88 NewPseudoTypeDirect
pub fn new_pseudo_type_direct(type_node: Node) -> Rc<PseudoType> {
    new_pseudo_type(
        PseudoTypeKind::DIRECT,
        PseudoTypeData::Direct(PseudoTypeDirect { type_node }),
    )
}

/// PseudoTypeInferred directly encodes the type referred to by a given Expression
/// These represent cases where the expression was too complex for the pseudochecker.
/// Most of the time, these locations will produce an error under ID.
/// Specific error nodes (shorthand properties, spread assignments, etc.) are stored on the
/// ErrorNodes field, collected during pseudochecker construction.
#[derive(Debug)]
pub struct PseudoTypeInferred {
    pub expression: Node,
    pub error_nodes: Vec<Node>,
    pub is_signature_return: bool,
}

// Go: pseudochecker/type.go:106 NewPseudoTypeInferred
pub fn new_pseudo_type_inferred(expr: Node, is_signature_return: bool) -> Rc<PseudoType> {
    new_pseudo_type(
        PseudoTypeKind::INFERRED,
        PseudoTypeData::Inferred(PseudoTypeInferred {
            expression: expr,
            error_nodes: Vec::new(),
            is_signature_return,
        }),
    )
}

// Go: pseudochecker/type.go:110 NewPseudoTypeInferredWithErrors
pub fn new_pseudo_type_inferred_with_errors(
    expr: Node,
    is_signature_return: bool,
    error_nodes: Vec<Node>,
) -> Rc<PseudoType> {
    new_pseudo_type(
        PseudoTypeKind::INFERRED,
        PseudoTypeData::Inferred(PseudoTypeInferred {
            expression: expr,
            error_nodes,
            is_signature_return,
        }),
    )
}

/// PseudoTypeNoResult is analogous to PseudoTypeInferred in that it references a case
/// where the type was too complex for the pseudochecker. Rather than an expression, however,
/// it is referring to the return type of a signature or declaration.
#[derive(Debug)]
pub struct PseudoTypeNoResult {
    pub declaration: Node,
}

// Go: pseudochecker/type.go:124 NewPseudoTypeNoResult
pub fn new_pseudo_type_no_result(decl: Node) -> Rc<PseudoType> {
    new_pseudo_type(
        PseudoTypeKind::NO_RESULT,
        PseudoTypeData::NoResult(PseudoTypeNoResult { declaration: decl }),
    )
}

/// PseudoTypeMaybeConstLocation encodes the const/regular types of a location so the builder
/// can later select the appropriate pseudotype based on the location's context. This is used
/// to ensure accuracy in nested expressions without exposing type-based functionality to the pseudochecker.
/// A nodebuilder that doesn't do contextual typing would need to, as policy, reject these types if they
/// are in a contextually typed position! (Otherwise they could pick one, but either type could be wrong, depending on context!)
/// At the top-level, which is generally what ID is concerned with, nothing is contextually typed, so these cases don't generally
/// cause problems. Once you get into reused nodes in nested expressions, however, this becomes important.
/// In strada, checker `isConstContext` functionality exposed to the pseudochecker + type comparison sanity checking
/// on nested results masks the need for this abstraction, but with it present it clearly highlights a shortcoming
/// of the ID infernce model and how "standalone" it can(n't) truly be without substantial restrictions on expression inference.
#[derive(Debug)]
pub struct PseudoTypeMaybeConstLocation {
    pub node: Node,
    pub const_type: Rc<PseudoType>,
    pub regular_type: Rc<PseudoType>,
}

// Go: pseudochecker/type.go:147 NewPseudoTypeMaybeConstLocation
pub fn new_pseudo_type_maybe_const_location(
    loc: Node,
    ct: Rc<PseudoType>,
    reg: Rc<PseudoType>,
) -> Rc<PseudoType> {
    new_pseudo_type(
        PseudoTypeKind::MAYBE_CONST_LOCATION,
        PseudoTypeData::MaybeConstLocation(PseudoTypeMaybeConstLocation {
            node: loc,
            const_type: ct,
            regular_type: reg,
        }),
    )
}

/// PseudoTypeUnion is a collection of psudotypes joined into a union
#[derive(Debug)]
pub struct PseudoTypeUnion {
    pub types: Vec<Rc<PseudoType>>,
}

// Go: pseudochecker/type.go:161 NewPseudoTypeUnion
pub fn new_pseudo_type_union(types: Vec<Rc<PseudoType>>) -> Rc<PseudoType> {
    new_pseudo_type(
        PseudoTypeKind::UNION,
        PseudoTypeData::Union(PseudoTypeUnion { types }),
    )
}

/// Go `pseudochecker.PseudoParameter`. Go `*PseudoParameter` is `Rc<PseudoParameter>`.
#[derive(Debug)]
pub struct PseudoParameter {
    pub rest: bool,
    pub name: Node,
    pub optional: bool,
    pub type_: Rc<PseudoType>,
}

// Go: pseudochecker/type.go:176 NewPseudoParameter
pub fn new_pseudo_parameter(
    is_rest: bool,
    name: Node,
    is_optional: bool,
    t: Rc<PseudoType>,
) -> Rc<PseudoParameter> {
    Rc::new(PseudoParameter {
        rest: is_rest,
        name,
        optional: is_optional,
        type_: t,
    })
}

/// PseudoTypeSingleCallSignature represents an object type with a single call signature, like an arrow or function expression
#[derive(Debug)]
pub struct PseudoTypeSingleCallSignature {
    pub signature: Node,
    pub parameters: Vec<Rc<PseudoParameter>>,
    /// Go `[]*ast.TypeParameterDeclaration`.
    pub type_parameters: Vec<Node>,
    pub return_type: Rc<PseudoType>,
}

// Go: pseudochecker/type.go:189 NewPseudoTypeSingleCallSignature
pub fn new_pseudo_type_single_call_signature(
    signature: Node,
    parameters: Vec<Rc<PseudoParameter>>,
    type_parameters: Vec<Node>,
    return_type: Rc<PseudoType>,
) -> Rc<PseudoType> {
    new_pseudo_type(
        PseudoTypeKind::SINGLE_CALL_SIGNATURE,
        PseudoTypeData::SingleCallSignature(PseudoTypeSingleCallSignature {
            signature,
            parameters,
            type_parameters,
            return_type,
        }),
    )
}

/// PseudoTypeTuple represents a tuple originaing from an `as const` array literal
#[derive(Debug)]
pub struct PseudoTypeTuple {
    pub elements: Vec<Rc<PseudoType>>,
}

// Go: pseudochecker/type.go:208 NewPseudoTypeTuple
pub fn new_pseudo_type_tuple(elements: Vec<Rc<PseudoType>>) -> Rc<PseudoType> {
    new_pseudo_type(
        PseudoTypeKind::TUPLE,
        PseudoTypeData::Tuple(PseudoTypeTuple { elements }),
    )
}

/// PseudoTypeObjectLiteral represents an object type originaing from an object literal
#[derive(Debug)]
pub struct PseudoTypeObjectLiteral {
    pub elements: Vec<Rc<PseudoObjectElement>>,
}

// Go: pseudochecker/type.go:340 NewPseudoTypeObjectLiteral
pub fn new_pseudo_type_object_literal(elements: Vec<Rc<PseudoObjectElement>>) -> Rc<PseudoType> {
    new_pseudo_type(
        PseudoTypeKind::OBJECT_LITERAL,
        PseudoTypeData::ObjectLiteral(PseudoTypeObjectLiteral { elements }),
    )
}

/// PseudoTypeLiteral represents a literal type
#[derive(Debug)]
pub struct PseudoTypeLiteral {
    pub node: Node,
}

// Go: pseudochecker/type.go:356 NewPseudoTypeStringLiteral
pub fn new_pseudo_type_string_literal(node: Node) -> Rc<PseudoType> {
    new_pseudo_type(
        PseudoTypeKind::STRING_LITERAL,
        PseudoTypeData::Literal(PseudoTypeLiteral { node }),
    )
}

// Go: pseudochecker/type.go:362 NewPseudoTypeNumericLiteral
pub fn new_pseudo_type_numeric_literal(node: Node) -> Rc<PseudoType> {
    new_pseudo_type(
        PseudoTypeKind::NUMERIC_LITERAL,
        PseudoTypeData::Literal(PseudoTypeLiteral { node }),
    )
}

// Go: pseudochecker/type.go:368 NewPseudoTypeBigIntLiteral
pub fn new_pseudo_type_big_int_literal(node: Node) -> Rc<PseudoType> {
    new_pseudo_type(
        PseudoTypeKind::BIG_INT_LITERAL,
        PseudoTypeData::Literal(PseudoTypeLiteral { node }),
    )
}

impl PseudoType {
    // Go: pseudochecker/type.go:92 AsPseudoTypeDirect
    pub fn as_pseudo_type_direct(&self) -> &PseudoTypeDirect {
        match &self.data {
            PseudoTypeData::Direct(d) => d,
            _ => panic!("PseudoType is not PseudoTypeDirect: {:?}", self.kind),
        }
    }

    // Go: pseudochecker/type.go:114 AsPseudoTypeInferred
    pub fn as_pseudo_type_inferred(&self) -> &PseudoTypeInferred {
        match &self.data {
            PseudoTypeData::Inferred(d) => d,
            _ => panic!("PseudoType is not PseudoTypeInferred: {:?}", self.kind),
        }
    }

    // Go: pseudochecker/type.go:128 AsPseudoTypeNoResult
    pub fn as_pseudo_type_no_result(&self) -> &PseudoTypeNoResult {
        match &self.data {
            PseudoTypeData::NoResult(d) => d,
            _ => panic!("PseudoType is not PseudoTypeNoResult: {:?}", self.kind),
        }
    }

    // Go: pseudochecker/type.go:151 AsPseudoTypeMaybeConstLocation
    pub fn as_pseudo_type_maybe_const_location(&self) -> &PseudoTypeMaybeConstLocation {
        match &self.data {
            PseudoTypeData::MaybeConstLocation(d) => d,
            _ => panic!(
                "PseudoType is not PseudoTypeMaybeConstLocation: {:?}",
                self.kind
            ),
        }
    }

    // Go: pseudochecker/type.go:165 AsPseudoTypeUnion
    pub fn as_pseudo_type_union(&self) -> &PseudoTypeUnion {
        match &self.data {
            PseudoTypeData::Union(d) => d,
            _ => panic!("PseudoType is not PseudoTypeUnion: {:?}", self.kind),
        }
    }

    // Go: pseudochecker/type.go:198 AsPseudoTypeSingleCallSignature
    pub fn as_pseudo_type_single_call_signature(&self) -> &PseudoTypeSingleCallSignature {
        match &self.data {
            PseudoTypeData::SingleCallSignature(d) => d,
            _ => panic!(
                "PseudoType is not PseudoTypeSingleCallSignature: {:?}",
                self.kind
            ),
        }
    }

    // Go: pseudochecker/type.go:214 AsPseudoTypeTuple
    pub fn as_pseudo_type_tuple(&self) -> &PseudoTypeTuple {
        match &self.data {
            PseudoTypeData::Tuple(d) => d,
            _ => panic!("PseudoType is not PseudoTypeTuple: {:?}", self.kind),
        }
    }

    // Go: pseudochecker/type.go:346 AsPseudoTypeObjectLiteral
    pub fn as_pseudo_type_object_literal(&self) -> &PseudoTypeObjectLiteral {
        match &self.data {
            PseudoTypeData::ObjectLiteral(d) => d,
            _ => panic!("PseudoType is not PseudoTypeObjectLiteral: {:?}", self.kind),
        }
    }

    // Go: pseudochecker/type.go:374 AsPseudoTypeLiteral
    pub fn as_pseudo_type_literal(&self) -> &PseudoTypeLiteral {
        match &self.data {
            PseudoTypeData::Literal(d) => d,
            _ => panic!("PseudoType is not PseudoTypeLiteral: {:?}", self.kind),
        }
    }
}

go_enum!(PseudoObjectElementKind, i8 {
    METHOD = 0; // PseudoObjectElementKindMethod
    PROPERTY_ASSIGNMENT = 1; // PseudoObjectElementKindPropertyAssignment
    SET_ACCESSOR = 2; // PseudoObjectElementKindSetAccessor
    GET_ACCESSOR = 3; // PseudoObjectElementKindGetAccessor
});

/// Go `*PseudoObjectElement`. Go pointers are `Rc<PseudoObjectElement>`.
// PORT: same shape as `PseudoType`: shared header fields plus an enum with
// one variant per Go data struct.
#[derive(Debug)]
pub struct PseudoObjectElement {
    pub name: Node,
    pub optional: bool,
    pub kind: PseudoObjectElementKind,
    data: PseudoObjectElementData,
}

#[derive(Debug)]
pub enum PseudoObjectElementData {
    Method(PseudoObjectMethod),
    PropertyAssignment(PseudoPropertyAssignment),
    SetAccessor(PseudoSetAccessor),
    GetAccessor(PseudoGetAccessor),
}

impl PseudoObjectElement {
    // Go: pseudochecker/type.go:227 Signature
    pub fn signature(&self) -> Node {
        match self.kind {
            PseudoObjectElementKind::METHOD => self.as_pseudo_object_method().signature,
            PseudoObjectElementKind::SET_ACCESSOR => self.as_pseudo_set_accessor().signature,
            PseudoObjectElementKind::GET_ACCESSOR => self.as_pseudo_get_accessor().signature,
            _ => Node::NIL,
        }
    }

    // Go: pseudochecker/type.go:279 AsPseudoObjectMethod
    pub fn as_pseudo_object_method(&self) -> &PseudoObjectMethod {
        match &self.data {
            PseudoObjectElementData::Method(d) => d,
            _ => panic!(
                "PseudoObjectElement is not PseudoObjectMethod: {:?}",
                self.kind
            ),
        }
    }

    // Go: pseudochecker/type.go:296 AsPseudoPropertyAssignment
    pub fn as_pseudo_property_assignment(&self) -> &PseudoPropertyAssignment {
        match &self.data {
            PseudoObjectElementData::PropertyAssignment(d) => d,
            _ => panic!(
                "PseudoObjectElement is not PseudoPropertyAssignment: {:?}",
                self.kind
            ),
        }
    }

    // Go: pseudochecker/type.go:313 AsPseudoSetAccessor
    pub fn as_pseudo_set_accessor(&self) -> &PseudoSetAccessor {
        match &self.data {
            PseudoObjectElementData::SetAccessor(d) => d,
            _ => panic!(
                "PseudoObjectElement is not PseudoSetAccessor: {:?}",
                self.kind
            ),
        }
    }

    // Go: pseudochecker/type.go:330 AsPseudoGetAccessor
    pub fn as_pseudo_get_accessor(&self) -> &PseudoGetAccessor {
        match &self.data {
            PseudoObjectElementData::GetAccessor(d) => d,
            _ => panic!(
                "PseudoObjectElement is not PseudoGetAccessor: {:?}",
                self.kind
            ),
        }
    }
}

// Go: pseudochecker/type.go:253 newPseudoObjectElement
fn new_pseudo_object_element(
    kind: PseudoObjectElementKind,
    name: Node,
    optional: bool,
    data: PseudoObjectElementData,
) -> Rc<PseudoObjectElement> {
    Rc::new(PseudoObjectElement {
        name,
        optional,
        kind,
        data,
    })
}

#[derive(Debug)]
pub struct PseudoObjectMethod {
    pub signature: Node,
    /// Go `[]*ast.TypeParameterDeclaration`.
    pub type_parameters: Vec<Node>,
    pub parameters: Vec<Rc<PseudoParameter>>,
    pub return_type: Rc<PseudoType>,
}

// Go: pseudochecker/type.go:270 NewPseudoObjectMethod
pub fn new_pseudo_object_method(
    signature: Node,
    name: Node,
    optional: bool,
    type_parameters: Vec<Node>,
    parameters: Vec<Rc<PseudoParameter>>,
    return_type: Rc<PseudoType>,
) -> Rc<PseudoObjectElement> {
    new_pseudo_object_element(
        PseudoObjectElementKind::METHOD,
        name,
        optional,
        PseudoObjectElementData::Method(PseudoObjectMethod {
            signature,
            type_parameters,
            parameters,
            return_type,
        }),
    )
}

#[derive(Debug)]
pub struct PseudoPropertyAssignment {
    pub readonly: bool,
    pub type_: Rc<PseudoType>,
}

// Go: pseudochecker/type.go:289 NewPseudoPropertyAssignment
pub fn new_pseudo_property_assignment(
    readonly: bool,
    name: Node,
    optional: bool,
    t: Rc<PseudoType>,
) -> Rc<PseudoObjectElement> {
    new_pseudo_object_element(
        PseudoObjectElementKind::PROPERTY_ASSIGNMENT,
        name,
        optional,
        PseudoObjectElementData::PropertyAssignment(PseudoPropertyAssignment {
            readonly,
            type_: t,
        }),
    )
}

#[derive(Debug)]
pub struct PseudoSetAccessor {
    pub signature: Node,
    pub parameter: Rc<PseudoParameter>,
}

// Go: pseudochecker/type.go:306 NewPseudoSetAccessor
pub fn new_pseudo_set_accessor(
    signature: Node,
    name: Node,
    optional: bool,
    p: Rc<PseudoParameter>,
) -> Rc<PseudoObjectElement> {
    new_pseudo_object_element(
        PseudoObjectElementKind::SET_ACCESSOR,
        name,
        optional,
        PseudoObjectElementData::SetAccessor(PseudoSetAccessor {
            signature,
            parameter: p,
        }),
    )
}

#[derive(Debug)]
pub struct PseudoGetAccessor {
    pub signature: Node,
    pub type_: Rc<PseudoType>,
}

// Go: pseudochecker/type.go:323 NewPseudoGetAccessor
pub fn new_pseudo_get_accessor(
    signature: Node,
    name: Node,
    optional: bool,
    t: Rc<PseudoType>,
) -> Rc<PseudoObjectElement> {
    new_pseudo_object_element(
        PseudoObjectElementKind::GET_ACCESSOR,
        name,
        optional,
        PseudoObjectElementData::GetAccessor(PseudoGetAccessor {
            signature,
            type_: t,
        }),
    )
}
