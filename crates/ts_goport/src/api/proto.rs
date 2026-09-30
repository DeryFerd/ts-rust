//! Port of internal/api/proto.go.
//!
//! PORT: Go marshals and unmarshals the tagged structs by reflection (JSON
//! v2 default rules). Here each struct gets a hand-written `MarshalerTo`
//! and, when the server decodes it, an `UnmarshalerFrom`. `proto_json!`
//! writes both from a field list in Go declaration order with the Go tag
//! options (`plain`, `omitzero`, `omitempty`). Structs whose fields have no
//! JSON impls of their own (`TypeResponse`, `DiagnosticResponse`,
//! `ProjectResponse`, `ConfigFileResponse`, `SnapshotChanges`,
//! `ProjectFileChanges`) have their impls written out below the struct.
//!
//! Go `*T` fields are `Option<T>`; Go `[]*T` fields are `Vec<T>` (no Go
//! code stores a nil element). Go `any` in `TypeResponse.Value` only holds
//! JSON primitives, so it is `LspAny`.
//!
//! PORT: tsgo#4915 generates the TS API from this Go source
//! (`_tools/gen-proto`). Its `nonnil`, `deprecated` and `internal` struct
//! tags and the `@gen-proto-*` comments on the session handlers only steer
//! that generator. They do not change the JSON, so the port leaves them out.

use crate::api::prelude::*;

use crate::execute::tsc::diagnostics as diagnosticwriter;
use crate::frontend::json::{
    JsonDecoder, JsonError, JsonToken, MarshalerTo, UnmarshalerFrom, json_unmarshal_decode,
};
use crate::frontend::json_ext::{
    AnyValue, ErrorPos, IsZero, JsonValue, LspAny, SemanticError, go_type_name, marshal_field,
    marshal_field_omitzero, marshal_opt_field, unmarshal_root, unmarshal_struct_fields,
    wrap_method_error, write_object_end, write_object_start,
};
use crate::frontend::tspath;
use crate::gostd::{GoError, errors, strconv};
use crate::ls::lsconv;
use crate::lsp::lsproto;
use crate::project;
use std::borrow::Cow;
use std::sync::LazyLock;

/// Go JSON v2 default struct arshalers for the tagged proto structs.
///
/// `marshal` writes the members in Go declaration order. Each field names
/// its Go tag option: `plain` (always written), `omitzero` (skipped when
/// `IsZero`), `omitempty` (skipped when the value marshals as `null`, `""`,
/// `{}` or `[]`). `both` adds the v2 default unmarshal: names match
/// exactly, unknown names are skipped and `null` sets the zero value.
macro_rules! proto_json {
    (marshal $ty:ident { $($field:ident : $name:literal $mode:ident),* $(,)? }) => {
        impl MarshalerTo for $ty {
            fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
                write_object_start(enc);
                let mut first = true;
                $( proto_json!(@field $mode, enc, first, $name, &self.$field); )*
                write_object_end(enc);
                Ok(())
            }
        }
    };
    (both $ty:ident { $($field:ident : $name:literal $mode:ident),* $(,)? }) => {
        proto_json!(marshal $ty { $($field : $name $mode),* });

        impl UnmarshalerFrom for $ty {
            fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
                let is_object = unmarshal_struct_fields(
                    dec,
                    concat!("api.", stringify!($ty)),
                    |name, dec| {
                        match name {
                            $($name => json_unmarshal_decode(dec, &mut self.$field)?,)*
                            _ => return Ok(false),
                        }
                        Ok(true)
                    },
                )?;
                if !is_object {
                    *self = $ty::default();
                }
                Ok(())
            }
        }
    };
    (@field plain, $enc:ident, $first:ident, $name:literal, $value:expr) => {
        marshal_field($enc, &mut $first, $name, $value)?;
    };
    (@field omitzero, $enc:ident, $first:ident, $name:literal, $value:expr) => {
        marshal_field_omitzero($enc, &mut $first, $name, $value)?;
    };
    (@field omitempty, $enc:ident, $first:ident, $name:literal, $value:expr) => {
        marshal_field_omitempty($enc, &mut $first, $name, $value)?;
    };
}

// Go: proto.go:20
pub static ERR_INVALID_REQUEST: LazyLock<GoError> =
    LazyLock::new(|| errors::new("api: invalid request"));
pub static ERR_CLIENT_ERROR: LazyLock<GoError> = LazyLock::new(|| errors::new("api: client error"));

// Go: proto.go:25 Method
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Method(pub Cow<'static, str>);

impl std::fmt::Display for Method {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

// PORT: `Method` is a Go string type; `BatchRequest.Method` and
// `BatchResponse.Method` (ts#63937) use the v2 string arshaler.
impl MarshalerTo for Method {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        self.0.as_ref().marshal_json_to(enc)
    }
}

impl UnmarshalerFrom for Method {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let mut s = String::new();
        json_ext::unmarshal_string_as(dec, &mut s, &go_type_name::<Self>())?;
        self.0 = Cow::Owned(s);
        Ok(())
    }
}

impl IsZero for Method {
    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
}

// Go: proto.go:27
// PORT: Go named integer and string types are newtypes. Their JSON form,
// zero test and `%v` text are those of the underlying Go type.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SnapshotID(pub u64);
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ProjectID(pub String);
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SymbolID(pub u64);
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeID(pub u32);
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SignatureID(pub u64);
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeHandle(pub String);

// `uint` handles use the v2 uint arshaler, `string` handles the string
// arshaler. Unmarshal errors name the Go type (`api.SnapshotID`), not the
// underlying one.
macro_rules! handle_json {
    (@unmarshal uint, $self:ident, $dec:ident) => {{
        $self.0 = json_ext::unmarshal_uint_as($dec, &go_type_name::<Self>())?;
        Ok(())
    }};
    (@unmarshal string, $self:ident, $dec:ident) => {
        json_ext::unmarshal_string_as($dec, &mut $self.0, &go_type_name::<Self>())
    };
    ($kind:ident: $($name:ident),*) => {$(
        impl MarshalerTo for $name {
            fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
                self.0.marshal_json_to(enc)
            }
        }

        impl UnmarshalerFrom for $name {
            fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
                handle_json!(@unmarshal $kind, self, dec)
            }
        }

        impl IsZero for $name {
            fn is_zero(&self) -> bool {
                self.0.is_zero()
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(&self.0, f)
            }
        }
    )*};
}

handle_json!(uint: SnapshotID, SymbolID, TypeID, SignatureID);
handle_json!(string: ProjectID, NodeHandle);

// Go: proto.go:36 ProjectHandle
pub fn project_handle(p: &project::Project) -> ProjectID {
    ProjectID(p.id().0)
}

// Go: proto.go:40 SymbolHandle
// PORT: `symbols` is the arena that holds `symbol` (the rule for `ast`
// functions that take a symbol). Go dereferences a nil symbol and panics.
pub fn symbol_handle(symbols: &SymbolArena, symbol: SymbolId) -> SymbolID {
    if symbol.is_nil() {
        panic!("runtime error: invalid memory address or nil pointer dereference");
    }
    SymbolID(get_symbol_id(symbols, symbol))
}

// Go: proto.go:44 TypeHandle
// PORT: Go reads `t.Id()`. A `TypeId` is the checker arena index, which
// equals the Go type id, so no checker is needed.
pub fn type_handle(t: TypeId) -> TypeID {
    if t.is_nil() {
        panic!("runtime error: invalid memory address or nil pointer dereference");
    }
    TypeID(t.0)
}

// Go: proto.go:48 SignatureHandle
// PORT: Go reads `sig.Id()`. A `SignatureId` is the checker arena index,
// which equals the Go signature id (`newSignature` numbers them from 1).
pub fn signature_handle(sig: SignatureId) -> SignatureID {
    if sig.is_nil() {
        panic!("runtime error: invalid memory address or nil pointer dereference");
    }
    SignatureID(u64::from(sig.0))
}

// Go: proto.go:52 parseProjectHandle
pub fn parse_project_handle(handle: &ProjectID) -> tspath::Path {
    tspath::Path(handle.0.clone())
}

// Go: proto.go:56
impl Method {
    pub const RELEASE: Method = Method(Cow::Borrowed("release"));

    // ts#63937
    pub const BATCH_REQUESTS: Method = Method(Cow::Borrowed("batchRequests"));

    // tsgo#4915: MethodGetServerTiming and MethodResetServerTiming are gone;
    // the connection answers them (`ipc::timing`).
    pub const INITIALIZE: Method = Method(Cow::Borrowed("initialize"));
    pub const UPDATE_SNAPSHOT: Method = Method(Cow::Borrowed("updateSnapshot"));
    // tsgo#4642
    pub const UPDATE_TEMPORARY_SNAPSHOT: Method = Method(Cow::Borrowed("updateTemporarySnapshot"));
    pub const PARSE_COMMAND_LINE: Method = Method(Cow::Borrowed("parseCommandLine"));
    pub const READ_CONFIG_FILE: Method = Method(Cow::Borrowed("readConfigFile"));
    pub const PARSE_JSON_CONFIG_FILE: Method = Method(Cow::Borrowed("parseJsonConfigFileContent"));
    pub const PARSE_CONFIG_FILE: Method = Method(Cow::Borrowed("parseConfigFile"));
    // tsgo#4849
    pub const TRANSPILE_MODULE: Method = Method(Cow::Borrowed("transpileModule"));
    pub const TRANSPILE_MODULE_FROM_FILE: Method = Method(Cow::Borrowed("transpileModuleFromFile"));
    pub const TRANSPILE_DECLARATION: Method = Method(Cow::Borrowed("transpileDeclaration"));
    pub const TRANSPILE_DECLARATION_FROM_FILE: Method =
        Method(Cow::Borrowed("transpileDeclarationFromFile"));
    pub const GET_DEFAULT_PROJECT_FOR_FILE: Method =
        Method(Cow::Borrowed("getDefaultProjectForFile"));
    pub const GET_SYMBOL_AT_POSITION: Method = Method(Cow::Borrowed("getSymbolAtPosition"));
    pub const GET_SYMBOLS_AT_POSITIONS: Method = Method(Cow::Borrowed("getSymbolsAtPositions"));
    pub const GET_SYMBOL_AT_LOCATION: Method = Method(Cow::Borrowed("getSymbolAtLocation"));
    pub const GET_SYMBOLS_AT_LOCATIONS: Method = Method(Cow::Borrowed("getSymbolsAtLocations"));
    pub const GET_SYMBOL_OF_SOURCE_FILE: Method = Method(Cow::Borrowed("getSymbolOfSourceFile"));
    pub const GET_SYMBOLS_OF_SOURCE_FILES: Method =
        Method(Cow::Borrowed("getSymbolsOfSourceFiles"));
    pub const GET_TYPE_OF_SYMBOL: Method = Method(Cow::Borrowed("getTypeOfSymbol"));
    pub const GET_TYPES_OF_SYMBOLS: Method = Method(Cow::Borrowed("getTypesOfSymbols"));
    pub const GET_DECLARED_TYPE_OF_SYMBOL: Method =
        Method(Cow::Borrowed("getDeclaredTypeOfSymbol"));
    // ts#63956
    pub const GET_NON_MISSING_TYPE_OF_SYMBOL: Method =
        Method(Cow::Borrowed("getNonMissingTypeOfSymbol"));
    pub const GET_SOURCE_FILE: Method = Method(Cow::Borrowed("getSourceFile"));
    pub const GET_SOURCE_FILE_NAMES: Method = Method(Cow::Borrowed("getSourceFileNames"));
    pub const GET_SOURCE_FILE_METADATA: Method = Method(Cow::Borrowed("getSourceFileMetadata"));
    // ts#64247
    pub const GET_RESOLVED_MODULE: Method = Method(Cow::Borrowed("getResolvedModule"));
    pub const GET_RESOLVED_MODULE_FROM_MODULE_SPECIFIER: Method =
        Method(Cow::Borrowed("getResolvedModuleFromModuleSpecifier"));
    pub const GET_RESOLVED_TYPE_REFERENCE_DIRECTIVE: Method =
        Method(Cow::Borrowed("getResolvedTypeReferenceDirective"));
    pub const GET_RESOLVED_TYPE_REFERENCE_DIRECTIVE_FROM_REFERENCE: Method = Method(Cow::Borrowed(
        "getResolvedTypeReferenceDirectiveFromTypeReferenceDirective",
    ));
    pub const GET_CONFIG_FILE_NAMES: Method = Method(Cow::Borrowed("getConfigFileNames"));
    pub const GET_CONFIG_SOURCE_FILE: Method = Method(Cow::Borrowed("getConfigSourceFile"));
    pub const RESOLVE_NAME: Method = Method(Cow::Borrowed("resolveName"));
    pub const GET_SYMBOLS_IN_SCOPE: Method = Method(Cow::Borrowed("getSymbolsInScope"));
    pub const GET_SIGNATURES_OF_TYPE: Method = Method(Cow::Borrowed("getSignaturesOfType"));
    pub const GET_RESOLVED_SIGNATURE: Method = Method(Cow::Borrowed("getResolvedSignature"));
    pub const GET_TYPE_AT_LOCATION: Method = Method(Cow::Borrowed("getTypeAtLocation"));
    pub const GET_TYPE_AT_LOCATIONS: Method = Method(Cow::Borrowed("getTypeAtLocations"));
    pub const GET_TYPE_AT_POSITION: Method = Method(Cow::Borrowed("getTypeAtPosition"));
    pub const GET_TYPES_AT_POSITIONS: Method = Method(Cow::Borrowed("getTypesAtPositions"));

    // Symbol sub-property methods
    pub const GET_PARENT_OF_SYMBOL: Method = Method(Cow::Borrowed("getParentOfSymbol"));
    pub const GET_MEMBERS_OF_SYMBOL: Method = Method(Cow::Borrowed("getMembersOfSymbol"));
    pub const GET_EXPORTS_OF_SYMBOL: Method = Method(Cow::Borrowed("getExportsOfSymbol"));
    pub const GET_EXPORT_SYMBOL_OF_SYMBOL: Method =
        Method(Cow::Borrowed("getExportSymbolOfSymbol"));

    // Type sub-property methods
    pub const GET_SYMBOL_OF_TYPE: Method = Method(Cow::Borrowed("getSymbolOfType"));
    pub const GET_TARGET_OF_TYPE: Method = Method(Cow::Borrowed("getTargetOfType"));
    pub const GET_FRESH_TYPE_OF_TYPE: Method = Method(Cow::Borrowed("getFreshTypeOfType"));
    pub const GET_REGULAR_TYPE_OF_TYPE: Method = Method(Cow::Borrowed("getRegularTypeOfType"));
    pub const GET_TYPES_OF_TYPE: Method = Method(Cow::Borrowed("getTypesOfType"));
    pub const GET_TYPE_PARAMETERS_OF_TYPE: Method =
        Method(Cow::Borrowed("getTypeParametersOfType"));
    pub const GET_OUTER_TYPE_PARAMETERS_OF_TYPE: Method =
        Method(Cow::Borrowed("getOuterTypeParametersOfType"));
    pub const GET_LOCAL_TYPE_PARAMETERS_OF_TYPE: Method =
        Method(Cow::Borrowed("getLocalTypeParametersOfType"));
    // ts#64264
    pub const GET_THIS_TYPE_OF_TYPE: Method = Method(Cow::Borrowed("getThisTypeOfType"));
    pub const GET_ALIAS_TYPE_ARGUMENTS_OF_TYPE: Method =
        Method(Cow::Borrowed("getAliasTypeArgumentsOfType"));
    pub const GET_ALIAS_SYMBOL_OF_TYPE: Method = Method(Cow::Borrowed("getAliasSymbolOfType"));
    pub const GET_OBJECT_TYPE_OF_TYPE: Method = Method(Cow::Borrowed("getObjectTypeOfType"));
    pub const GET_INDEX_TYPE_OF_TYPE: Method = Method(Cow::Borrowed("getIndexTypeOfType"));
    pub const GET_CHECK_TYPE_OF_TYPE: Method = Method(Cow::Borrowed("getCheckTypeOfType"));
    pub const GET_EXTENDS_TYPE_OF_TYPE: Method = Method(Cow::Borrowed("getExtendsTypeOfType"));
    pub const GET_BASE_TYPE_OF_TYPE: Method = Method(Cow::Borrowed("getBaseTypeOfType"));
    pub const GET_CONSTRAINT_OF_TYPE: Method = Method(Cow::Borrowed("getConstraintOfType"));

    // Signature sub-property methods
    pub const GET_TYPE_PARAMETERS_OF_SIGNATURE: Method =
        Method(Cow::Borrowed("getTypeParametersOfSignature"));
    pub const GET_PARAMETERS_OF_SIGNATURE: Method =
        Method(Cow::Borrowed("getParametersOfSignature"));
    pub const GET_THIS_PARAMETER_OF_SIGNATURE: Method =
        Method(Cow::Borrowed("getThisParameterOfSignature"));
    pub const GET_TARGET_OF_SIGNATURE: Method = Method(Cow::Borrowed("getTargetOfSignature"));

    // Checker methods
    pub const GET_CONTEXTUAL_TYPE: Method = Method(Cow::Borrowed("getContextualType"));
    // ts#64264
    pub const GET_CONTEXTUAL_TYPE_FOR_ARGUMENT: Method =
        Method(Cow::Borrowed("getContextualTypeForArgument"));
    pub const GET_AWAITED_TYPE: Method = Method(Cow::Borrowed("getAwaitedType"));
    pub const GET_BASE_TYPE_OF_LITERAL_TYPE: Method =
        Method(Cow::Borrowed("getBaseTypeOfLiteralType"));
    pub const GET_NON_NULLABLE_TYPE: Method = Method(Cow::Borrowed("getNonNullableType"));
    pub const GET_TYPE_FROM_TYPE_NODE: Method = Method(Cow::Borrowed("getTypeFromTypeNode"));
    pub const GET_WIDENED_TYPE: Method = Method(Cow::Borrowed("getWidenedType"));
    pub const GET_PARAMETER_TYPE: Method = Method(Cow::Borrowed("getParameterType"));
    pub const GET_TYPE_PARAMETER_AT_POSITION: Method =
        Method(Cow::Borrowed("getTypeParameterAtPosition"));
    pub const IS_ARRAY_LIKE_TYPE: Method = Method(Cow::Borrowed("isArrayLikeType"));
    pub const IS_TYPE_ASSIGNABLE_TO: Method = Method(Cow::Borrowed("isTypeAssignableTo"));
    pub const GET_SHORTHAND_ASSIGNMENT_VALUE_SYMBOL: Method =
        Method(Cow::Borrowed("getShorthandAssignmentValueSymbol"));
    pub const GET_TYPE_OF_SYMBOL_AT_LOCATION: Method =
        Method(Cow::Borrowed("getTypeOfSymbolAtLocation"));
    pub const TYPE_TO_TYPE_NODE: Method = Method(Cow::Borrowed("typeToTypeNode"));
    pub const SIGNATURE_TO_SIGNATURE_DECLARATION: Method =
        Method(Cow::Borrowed("signatureToSignatureDeclaration"));
    pub const TYPE_TO_STRING: Method = Method(Cow::Borrowed("typeToString"));
    pub const IS_CONTEXT_SENSITIVE: Method = Method(Cow::Borrowed("isContextSensitive"));
    pub const GET_RETURN_TYPE_OF_SIGNATURE: Method =
        Method(Cow::Borrowed("getReturnTypeOfSignature"));
    pub const GET_REST_TYPE_OF_SIGNATURE: Method = Method(Cow::Borrowed("getRestTypeOfSignature"));
    pub const GET_TYPE_PREDICATE_OF_SIGNATURE: Method =
        Method(Cow::Borrowed("getTypePredicateOfSignature"));
    pub const GET_BASE_TYPES: Method = Method(Cow::Borrowed("getBaseTypes"));
    pub const GET_PROPERTIES_OF_TYPE: Method = Method(Cow::Borrowed("getPropertiesOfType"));
    pub const GET_APPARENT_PROPERTIES_OF_TYPE: Method =
        Method(Cow::Borrowed("getApparentPropertiesOfType"));
    pub const GET_APPARENT_TYPE: Method = Method(Cow::Borrowed("getApparentType"));
    // ts#63899
    pub const GET_REDUCED_TYPE: Method = Method(Cow::Borrowed("getReducedType"));
    pub const GET_PROPERTY_OF_TYPE: Method = Method(Cow::Borrowed("getPropertyOfType"));
    // ts#64264 (MethodGetIndexTypeOfTypeByKind is not ported: ts#64408
    // removes it)
    pub const GET_TYPE_OF_PROPERTY_OF_TYPE: Method =
        Method(Cow::Borrowed("getTypeOfPropertyOfType"));
    pub const GET_INDEX_INFO_OF_TYPE: Method = Method(Cow::Borrowed("getIndexInfoOfType"));
    pub const GET_INDEX_INFOS_OF_TYPE: Method = Method(Cow::Borrowed("getIndexInfosOfType"));
    pub const GET_CONSTRAINT_OF_TYPE_PARAMETER: Method =
        Method(Cow::Borrowed("getConstraintOfTypeParameter"));
    pub const GET_DEFAULT_FROM_TYPE_PARAMETER: Method =
        Method(Cow::Borrowed("getDefaultFromTypeParameter"));
    pub const GET_BASE_CONSTRAINT_OF_TYPE: Method =
        Method(Cow::Borrowed("getBaseConstraintOfType"));
    pub const GET_TYPE_ARGUMENTS: Method = Method(Cow::Borrowed("getTypeArguments"));
    // tsgo#3881
    pub const GET_IMPORT_ADDER_EDITS: Method = Method(Cow::Borrowed("getImportAdderEdits"));
    pub const GET_TRUE_TYPE_OF_CONDITIONAL_TYPE: Method =
        Method(Cow::Borrowed("getTrueTypeOfConditionalType"));
    pub const GET_FALSE_TYPE_OF_CONDITIONAL_TYPE: Method =
        Method(Cow::Borrowed("getFalseTypeOfConditionalType"));
    pub const GET_CONSTANT_VALUE: Method = Method(Cow::Borrowed("getConstantValue"));
    pub const GET_SIGNATURE_FROM_DECLARATION: Method =
        Method(Cow::Borrowed("getSignatureFromDeclaration"));
    pub const GET_EXPORT_SPECIFIER_LOCAL_TARGET: Method =
        Method(Cow::Borrowed("getExportSpecifierLocalTargetSymbol"));
    pub const GET_ALIASED_SYMBOL: Method = Method(Cow::Borrowed("getAliasedSymbol"));
    pub const GET_IMMEDIATE_ALIASED_SYMBOL: Method =
        Method(Cow::Borrowed("getImmediateAliasedSymbol"));
    // ts#63945
    pub const GET_TARGET_SYMBOL: Method = Method(Cow::Borrowed("getTargetSymbol"));
    // ts#64264
    pub const GET_EXPORT_SYMBOL_OF_SYMBOL_FOR_CHECKER: Method =
        Method(Cow::Borrowed("getExportSymbolOfSymbolForChecker"));
    pub const GET_FULLY_QUALIFIED_NAME: Method = Method(Cow::Borrowed("getFullyQualifiedName"));
    pub const GET_EXPORTS_OF_MODULE: Method = Method(Cow::Borrowed("getExportsOfModule"));
    pub const GET_MEMBER_IN_MODULE_EXPORTS: Method =
        Method(Cow::Borrowed("getMemberInModuleExports"));
    pub const GET_JS_DOC_TAGS: Method = Method(Cow::Borrowed("getJsDocTags"));
    pub const GET_DOCUMENTATION_COMMENT: Method = Method(Cow::Borrowed("getDocumentationComment"));
    pub const IS_ARRAY_TYPE: Method = Method(Cow::Borrowed("isArrayType"));
    // ts#64080: MethodIsTupleType is gone; TypeResponse.IsTupleType replaces it.
    // ts#63943
    pub const IS_READONLY_SYMBOL: Method = Method(Cow::Borrowed("isReadonlySymbol"));

    // Reference methods
    pub const GET_REFERENCES_TO_SYMBOL_IN_FILE: Method =
        Method(Cow::Borrowed("getReferencesToSymbolInFile"));
    pub const GET_REFERENCED_SYMBOLS_FOR_NODE: Method =
        Method(Cow::Borrowed("getReferencedSymbolsForNode"));
    pub const GET_SIGNATURE_USAGES: Method = Method(Cow::Borrowed("getSignatureUsages"));

    // Language service methods
    pub const GET_COMPLETIONS_AT_POSITION: Method =
        Method(Cow::Borrowed("getCompletionsAtPosition"));

    // Diagnostic methods
    pub const GET_SYNTACTIC_DIAGNOSTICS: Method = Method(Cow::Borrowed("getSyntacticDiagnostics"));
    pub const GET_BIND_DIAGNOSTICS: Method = Method(Cow::Borrowed("getBindDiagnostics"));
    pub const GET_SEMANTIC_DIAGNOSTICS: Method = Method(Cow::Borrowed("getSemanticDiagnostics"));
    pub const GET_SUGGESTION_DIAGNOSTICS: Method =
        Method(Cow::Borrowed("getSuggestionDiagnostics"));
    pub const GET_DECLARATION_DIAGNOSTICS: Method =
        Method(Cow::Borrowed("getDeclarationDiagnostics"));
    pub const GET_PROGRAM_DIAGNOSTICS: Method = Method(Cow::Borrowed("getProgramDiagnostics"));
    pub const GET_GLOBAL_DIAGNOSTICS: Method = Method(Cow::Borrowed("getGlobalDiagnostics"));
    pub const GET_CONFIG_FILE_PARSING_DIAGNOSTICS: Method =
        Method(Cow::Borrowed("getConfigFileParsingDiagnostics"));

    // Emitter methods
    pub const PRINT_NODE: Method = Method(Cow::Borrowed("printNode"));
    pub const FORMAT_NODE_FOR_INSERTION: Method = Method(Cow::Borrowed("formatNodeForInsertion"));
    // tsgo#4699
    pub const EMIT: Method = Method(Cow::Borrowed("emit"));
    pub const EMIT_TO_STRING: Method = Method(Cow::Borrowed("emitToString"));
    pub const GET_JAVA_SCRIPT_EMIT: Method = Method(Cow::Borrowed("getJavaScriptEmit"));
    pub const GET_DECLARATION_EMIT: Method = Method(Cow::Borrowed("getDeclarationEmit"));

    // Intrinsic type getters
    pub const GET_ANY_TYPE: Method = Method(Cow::Borrowed("getAnyType"));
    pub const GET_STRING_TYPE: Method = Method(Cow::Borrowed("getStringType"));
    pub const GET_NUMBER_TYPE: Method = Method(Cow::Borrowed("getNumberType"));
    pub const GET_BOOLEAN_TYPE: Method = Method(Cow::Borrowed("getBooleanType"));
    pub const GET_VOID_TYPE: Method = Method(Cow::Borrowed("getVoidType"));
    pub const GET_UNDEFINED_TYPE: Method = Method(Cow::Borrowed("getUndefinedType"));
    pub const GET_NULL_TYPE: Method = Method(Cow::Borrowed("getNullType"));
    pub const GET_NEVER_TYPE: Method = Method(Cow::Borrowed("getNeverType"));
    pub const GET_UNKNOWN_TYPE: Method = Method(Cow::Borrowed("getUnknownType"));
    pub const GET_BIG_INT_TYPE: Method = Method(Cow::Borrowed("getBigIntType"));
    pub const GET_ES_SYMBOL_TYPE: Method = Method(Cow::Borrowed("getESSymbolType"));
    pub const GET_NON_PRIMITIVE_TYPE: Method = Method(Cow::Borrowed("getNonPrimitiveType"));

    // Well-known per-checker symbols
    pub const GET_WELL_KNOWN_SYMBOLS: Method = Method(Cow::Borrowed("getWellKnownSymbols"));

    // Well-known per-checker signatures
    pub const GET_WELL_KNOWN_SIGNATURES: Method = Method(Cow::Borrowed("getWellKnownSignatures"));

    // Profiling methods
    pub const START_CPU_PROFILE: Method = Method(Cow::Borrowed("startCPUProfile"));
    pub const STOP_CPU_PROFILE: Method = Method(Cow::Borrowed("stopCPUProfile"));
    pub const SAVE_HEAP_PROFILE: Method = Method(Cow::Borrowed("saveHeapProfile"));
}

// InitializeResponse is returned by the initialize method.
// Go: proto.go:171 InitializeResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct InitializeResponse {
    // UseCaseSensitiveFileNames indicates whether the host file system is case-sensitive.
    pub use_case_sensitive_file_names: bool,
    // CurrentDirectory is the server's current working directory.
    pub current_directory: String,
}

proto_json!(marshal InitializeResponse {
    use_case_sensitive_file_names: "useCaseSensitiveFileNames" plain,
    current_directory: "currentDirectory" plain,
});

// DocumentIdentifier identifies a document by either a file name (plain string) or a URI object.
// On the wire it is string | { uri: string }.
//
// @example
//
// Using a file name:
//
//	project.program.getSourceFile("/path/to/file.ts");
//
// Using a URI:
//
//	project.program.getSourceFile({ uri: "file:///path/to/file.ts" });
// Go: proto.go:180 DocumentIdentifier
#[derive(Clone, Debug, Default, PartialEq)]
pub struct DocumentIdentifier {
    pub file_name: String,
    pub uri: lsproto::DocumentUri,
}

proto_json!(marshal DocumentIdentifier {
    file_name: "fileName" omitempty,
    uri: "uri" omitempty,
});

// Go: proto.go:187 UnmarshalJSONFrom
impl UnmarshalerFrom for DocumentIdentifier {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        // Try reading as a plain string first
        let tok = dec.read_token()?;
        match tok.kind() {
            b'"' => {
                self.file_name = token_string(&tok);
                Ok(())
            }
            b'{' => {
                // Read the object fields
                while dec.peek_kind() != b'}' {
                    let key = dec.read_token()?;
                    let is_uri = token_string(&key) == "uri";
                    let val = dec.read_token()?;
                    if is_uri {
                        self.uri = lsproto::DocumentUri(token_string(&val));
                    }
                }
                // Consume the closing brace
                dec.read_token()?;
                Ok(())
            }
            // Go wraps the error of the method with the type (one token
            // was read).
            _ => Err(wrap_method_error::<Self>(SemanticError::method(
                ErrorPos::After,
                format!(
                    "DocumentIdentifier: expected string or object, got {}",
                    kind_string(tok.kind())
                ),
            ))),
        }
    }
}

// Go jsontext `Token.String`: the unquoted text of a string token, else the
// raw JSON text of the token.
fn token_string(tok: &JsonToken) -> String {
    match tok {
        JsonToken::Null => "null".to_string(),
        JsonToken::False => "false".to_string(),
        JsonToken::True => "true".to_string(),
        JsonToken::String(s) => s.clone(),
        JsonToken::Number(raw) => raw.clone(),
        JsonToken::BeginObject => "{".to_string(),
        JsonToken::EndObject => "}".to_string(),
        JsonToken::BeginArray => "[".to_string(),
        JsonToken::EndArray => "]".to_string(),
    }
}

// Go jsontext `Kind.String` (the `%v` text of a token kind).
fn kind_string(k: u8) -> String {
    match k {
        b'n' => "null".to_string(),
        b'f' => "false".to_string(),
        b't' => "true".to_string(),
        b'"' => "string".to_string(),
        b'0' => "number".to_string(),
        b'{' => "{".to_string(),
        b'}' => "}".to_string(),
        b'[' => "[".to_string(),
        b']' => "]".to_string(),
        _ => format!(
            "<invalid jsontext.Kind: {}>",
            crate::frontend::json_ext::quote_rune(&[k])
        ),
    }
}

impl DocumentIdentifier {
    // Go: proto.go:223 ToFileName
    pub fn to_file_name(&self) -> String {
        if !self.uri.0.is_empty() {
            return self.uri.file_name();
        }
        self.file_name.clone()
    }

    // Go: proto.go:268 ToURI
    // ToURI returns the document URI for this identifier. An explicitly provided URI
    // is returned as-is; a file name is first normalized to an absolute path against
    // cwd before being converted to a URI.
    pub fn to_uri(&self, cwd: &str) -> lsproto::DocumentUri {
        if !self.uri.0.is_empty() {
            return self.uri.clone();
        }
        lsconv::file_name_to_document_uri(&tspath::get_normalized_absolute_path(
            &self.file_name,
            cwd,
        ))
    }

    // Go: proto.go:237 ToAbsoluteFileName
    pub fn to_absolute_file_name(&self, cwd: &str) -> String {
        if !self.uri.0.is_empty() {
            return self.uri.file_name();
        }
        tspath::get_normalized_absolute_path(&self.file_name, cwd)
    }

    // Go: proto.go:244 String
    pub fn string(&self) -> String {
        if !self.uri.0.is_empty() {
            return self.uri.0.clone();
        }
        self.file_name.clone()
    }
}

// Go `%v` of a DocumentIdentifier calls its String method.
impl std::fmt::Display for DocumentIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string())
    }
}

// APIFileChangeSummary lists documents that have been changed, created, or deleted.
// Go: proto.go:252 APIFileChangeSummary
#[derive(Clone, Debug, Default, PartialEq)]
pub struct APIFileChangeSummary {
    pub changed: Vec<DocumentIdentifier>,
    pub created: Vec<DocumentIdentifier>,
    pub deleted: Vec<DocumentIdentifier>,
}

proto_json!(marshal APIFileChangeSummary {
    changed: "changed" omitempty,
    created: "created" omitempty,
    deleted: "deleted" omitempty,
});

// APIFileChanges describes file changes to apply when updating a snapshot.
// Either InvalidateAll is true (discard all caches) or Changed/Created/Deleted
// list individual documents.
// Go: proto.go:261 APIFileChanges
#[derive(Clone, Debug, Default, PartialEq)]
pub struct APIFileChanges {
    pub invalidate_all: bool,
    pub changed: Vec<DocumentIdentifier>,
    pub created: Vec<DocumentIdentifier>,
    pub deleted: Vec<DocumentIdentifier>,
}

proto_json!(both APIFileChanges {
    invalidate_all: "invalidateAll" omitempty,
    changed: "changed" omitempty,
    created: "created" omitempty,
    deleted: "deleted" omitempty,
});

// UpdateSnapshotParams are the parameters for creating a new snapshot.
// All fields are optional. With no fields set, the server adopts the latest LSP state.
// Go: proto.go:308 UpdateSnapshotParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct UpdateSnapshotParams {
    // OpenProjects lists tsconfig.json files to open/load in the new snapshot.
    // Opens are ref-counted and persist across snapshots until closed.
    pub open_projects: Vec<DocumentIdentifier>,
    // CloseProjects lists tsconfig.json files to release in the new snapshot.
    // A project is only unloaded once every API client that opened it closes it.
    pub close_projects: Vec<DocumentIdentifier>,
    // FileChanges describes file system changes since the last snapshot.
    pub file_changes: Option<APIFileChanges>,
    // OpenFiles lists files to keep open for the API client, mirroring LSP's
    // textDocument/didOpen. For each file, ancestor directories are searched for a
    // tsconfig that contains it; if found, that configured project is loaded and
    // becomes the file's default project. Otherwise the file is loaded into the
    // inferred project (e.g. a node_modules d.ts not in any project's import graph).
    // Opens persist across snapshots until the file is closed.
    pub open_files: Vec<DocumentIdentifier>,
    // CloseFiles lists files to release in the new snapshot. A file is only fully
    // closed once every API client that opened it closes it.
    pub close_files: Vec<DocumentIdentifier>,
}

proto_json!(both UpdateSnapshotParams {
    open_projects: "openProjects" omitempty,
    close_projects: "closeProjects" omitempty,
    file_changes: "fileChanges" omitempty,
    open_files: "openFiles" omitempty,
    close_files: "closeFiles" omitempty,
});

// UpdateTemporarySnapshotParams are the parameters for creating a temporary
// snapshot that overrides a single file's content.
// Go: proto.go:360 UpdateTemporarySnapshotParams (tsgo#4642)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct UpdateTemporarySnapshotParams {
    // Snapshot is the current client snapshot on which to layer the temporary update.
    pub snapshot: SnapshotID,
    // File identifies the file whose content is temporarily overridden.
    pub file: DocumentIdentifier,
    // NewText is the temporary content for the file.
    pub new_text: String,
}

proto_json!(both UpdateTemporarySnapshotParams {
    snapshot: "snapshot" plain,
    file: "file" plain,
    new_text: "newText" plain,
});

// ProjectFileChanges describes what source files changed within a single project.
// Go: proto.go:278 ProjectFileChanges
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ProjectFileChanges {
    // ChangedFiles lists source file paths whose content differs.
    pub changed_files: Vec<tspath::Path>,
    // DeletedFiles lists source file paths removed from the project's program.
    pub deleted_files: Vec<tspath::Path>,
}

impl MarshalerTo for ProjectFileChanges {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        // PORT: `tspath.Path` is a Go string type; it writes as a string.
        let changed_files: Vec<&str> = self.changed_files.iter().map(|p| p.as_str()).collect();
        let deleted_files: Vec<&str> = self.deleted_files.iter().map(|p| p.as_str()).collect();
        write_object_start(enc);
        let mut first = true;
        marshal_field_omitempty(enc, &mut first, "changedFiles", &changed_files)?;
        marshal_field_omitempty(enc, &mut first, "deletedFiles", &deleted_files)?;
        write_object_end(enc);
        Ok(())
    }
}

// SnapshotChanges describes what changed between the previous latest snapshot
// and the newly created snapshot. Changes are reported per-project so clients
// can track cache refs at the (snapshot, project) level.
// Go: proto.go:288 SnapshotChanges
#[derive(Clone, Debug, Default, PartialEq)]
pub struct SnapshotChanges {
    // ChangedProjects maps project handles to the file changes within that project.
    // Projects not listed here (and not in RemovedProjects) are unchanged.
    pub changed_projects: IndexMap<ProjectID, ProjectFileChanges>,
    // RemovedProjects lists project handles that were present in the previous
    // snapshot but absent from the new one.
    pub removed_projects: Vec<ProjectID>,
}

impl MarshalerTo for SnapshotChanges {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        let mut first = true;
        marshal_field_omitempty(
            enc,
            &mut first,
            "changedProjects",
            &ProjectChangesJSON(&self.changed_projects),
        )?;
        marshal_field_omitempty(enc, &mut first, "removedProjects", &self.removed_projects)?;
        write_object_end(enc);
        Ok(())
    }
}

// Go v2 map marshal of `map[ProjectID]*ProjectFileChanges`: an object with
// the handles as names.
// PORT: Go map order is random; the port writes insertion order. Go values
// are never nil pointers, so the map holds values.
struct ProjectChangesJSON<'a>(&'a IndexMap<ProjectID, ProjectFileChanges>);

impl MarshalerTo for ProjectChangesJSON<'_> {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        enc.push('{');
        for (i, (k, v)) in self.0.iter().enumerate() {
            if i > 0 {
                enc.push(',');
            }
            k.marshal_json_to(enc)?;
            enc.push(':');
            v.marshal_json_to(enc)?;
        }
        enc.push('}');
        Ok(())
    }
}

// UpdateSnapshotResponse is returned by updateSnapshot.
// Go: proto.go:298 UpdateSnapshotResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct UpdateSnapshotResponse {
    // Snapshot is the handle for the newly created snapshot.
    pub snapshot: SnapshotID,
    // Projects is the list of projects in the snapshot.
    pub projects: Vec<ProjectResponse>,
    // Changes describes source file differences from the previous snapshot.
    // Nil for the first snapshot in a session.
    pub changes: Option<SnapshotChanges>,
}

proto_json!(marshal UpdateSnapshotResponse {
    snapshot: "snapshot" plain,
    projects: "projects" plain,
    changes: "changes" omitempty,
});

/// Go `func([]byte) (any, error)` in `unmarshalers`.
pub type Unmarshaler = fn(&[u8]) -> Result<Option<Box<dyn AnyValue>>, GoError>;

// Go: proto.go:308 unmarshalers
pub static UNMARSHALERS: LazyLock<FxHashMap<Method, Unmarshaler>> = LazyLock::new(|| {
    let mut m: FxHashMap<Method, Unmarshaler> = FxHashMap::default();
    // ts#63937
    m.insert(
        Method::BATCH_REQUESTS,
        unmarshaller_for::<BatchRequestsParams>,
    );
    m.insert(Method::RELEASE, unmarshaller_for::<ReleaseParams>);
    m.insert(Method::INITIALIZE, no_params);
    m.insert(
        Method::UPDATE_SNAPSHOT,
        unmarshaller_for::<UpdateSnapshotParams>,
    );
    m.insert(
        Method::UPDATE_TEMPORARY_SNAPSHOT,
        unmarshaller_for::<UpdateTemporarySnapshotParams>,
    );
    m.insert(
        Method::PARSE_COMMAND_LINE,
        unmarshaller_for::<ParseCommandLineParams>,
    );
    m.insert(
        Method::READ_CONFIG_FILE,
        unmarshaller_for::<ReadConfigFileParams>,
    );
    m.insert(
        Method::PARSE_JSON_CONFIG_FILE,
        unmarshaller_for::<ParseJsonConfigFileContentParams>,
    );
    m.insert(
        Method::PARSE_CONFIG_FILE,
        unmarshaller_for::<ParseConfigFileParams>,
    );
    // tsgo#4849
    m.insert(
        Method::TRANSPILE_MODULE,
        unmarshaller_for::<TranspileParams>,
    );
    m.insert(
        Method::TRANSPILE_MODULE_FROM_FILE,
        unmarshaller_for::<TranspileFromFileParams>,
    );
    m.insert(
        Method::TRANSPILE_DECLARATION,
        unmarshaller_for::<TranspileParams>,
    );
    m.insert(
        Method::TRANSPILE_DECLARATION_FROM_FILE,
        unmarshaller_for::<TranspileFromFileParams>,
    );
    m.insert(
        Method::GET_DEFAULT_PROJECT_FOR_FILE,
        unmarshaller_for::<GetDefaultProjectForFileParams>,
    );
    m.insert(
        Method::GET_SOURCE_FILE,
        unmarshaller_for::<GetSourceFileParams>,
    );
    m.insert(
        Method::GET_SOURCE_FILE_NAMES,
        unmarshaller_for::<GetSourceFileNamesParams>,
    );
    m.insert(
        Method::GET_SOURCE_FILE_METADATA,
        unmarshaller_for::<GetSourceFileParams>,
    );
    // ts#64247
    m.insert(
        Method::GET_RESOLVED_MODULE,
        unmarshaller_for::<GetResolvedModuleParams>,
    );
    m.insert(
        Method::GET_RESOLVED_MODULE_FROM_MODULE_SPECIFIER,
        unmarshaller_for::<GetResolvedModuleFromModuleSpecifierParams>,
    );
    m.insert(
        Method::GET_RESOLVED_TYPE_REFERENCE_DIRECTIVE,
        unmarshaller_for::<GetResolvedTypeReferenceDirectiveParams>,
    );
    m.insert(
        Method::GET_RESOLVED_TYPE_REFERENCE_DIRECTIVE_FROM_REFERENCE,
        unmarshaller_for::<GetResolvedTypeReferenceDirectiveFromReferenceParams>,
    );
    m.insert(
        Method::GET_CONFIG_FILE_NAMES,
        unmarshaller_for::<GetProjectDiagnosticsParams>,
    );
    m.insert(
        Method::GET_CONFIG_SOURCE_FILE,
        unmarshaller_for::<GetSourceFileParams>,
    );
    m.insert(
        Method::GET_SYMBOL_AT_POSITION,
        unmarshaller_for::<GetSymbolAtPositionParams>,
    );
    m.insert(
        Method::GET_SYMBOLS_AT_POSITIONS,
        unmarshaller_for::<GetSymbolsAtPositionsParams>,
    );
    m.insert(
        Method::GET_SYMBOL_AT_LOCATION,
        unmarshaller_for::<GetSymbolAtLocationParams>,
    );
    m.insert(
        Method::GET_SYMBOLS_AT_LOCATIONS,
        unmarshaller_for::<GetSymbolsAtLocationsParams>,
    );
    m.insert(
        Method::GET_SYMBOL_OF_SOURCE_FILE,
        unmarshaller_for::<GetSymbolOfSourceFileParams>,
    );
    m.insert(
        Method::GET_SYMBOLS_OF_SOURCE_FILES,
        unmarshaller_for::<GetSymbolsOfSourceFilesParams>,
    );
    m.insert(
        Method::GET_TYPE_OF_SYMBOL,
        unmarshaller_for::<GetTypeOfSymbolParams>,
    );
    m.insert(
        Method::GET_TYPES_OF_SYMBOLS,
        unmarshaller_for::<GetTypesOfSymbolsParams>,
    );
    m.insert(
        Method::GET_DECLARED_TYPE_OF_SYMBOL,
        unmarshaller_for::<GetTypeOfSymbolParams>,
    );
    // ts#63956
    m.insert(
        Method::GET_NON_MISSING_TYPE_OF_SYMBOL,
        unmarshaller_for::<GetTypeOfSymbolParams>,
    );
    m.insert(Method::RESOLVE_NAME, unmarshaller_for::<ResolveNameParams>);
    m.insert(
        Method::GET_SYMBOLS_IN_SCOPE,
        unmarshaller_for::<GetSymbolsInScopeParams>,
    );
    m.insert(
        Method::GET_SIGNATURES_OF_TYPE,
        unmarshaller_for::<GetSignaturesOfTypeParams>,
    );
    m.insert(
        Method::GET_RESOLVED_SIGNATURE,
        unmarshaller_for::<GetResolvedSignatureParams>,
    );
    m.insert(
        Method::GET_TYPE_AT_LOCATION,
        unmarshaller_for::<GetTypeAtLocationParams>,
    );
    m.insert(
        Method::GET_TYPE_AT_LOCATIONS,
        unmarshaller_for::<GetTypeAtLocationsParams>,
    );
    m.insert(
        Method::GET_TYPE_AT_POSITION,
        unmarshaller_for::<GetTypeAtPositionParams>,
    );
    m.insert(
        Method::GET_TYPES_AT_POSITIONS,
        unmarshaller_for::<GetTypesAtPositionsParams>,
    );

    m.insert(
        Method::GET_PARENT_OF_SYMBOL,
        unmarshaller_for::<GetSymbolPropertyParams>,
    );
    m.insert(
        Method::GET_MEMBERS_OF_SYMBOL,
        unmarshaller_for::<GetSymbolPropertyParams>,
    );
    m.insert(
        Method::GET_EXPORTS_OF_SYMBOL,
        unmarshaller_for::<GetSymbolPropertyParams>,
    );
    m.insert(
        Method::GET_EXPORT_SYMBOL_OF_SYMBOL,
        unmarshaller_for::<GetSymbolPropertyParams>,
    );

    m.insert(
        Method::GET_SYMBOL_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_TARGET_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_FRESH_TYPE_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_REGULAR_TYPE_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_TYPES_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_TYPE_PARAMETERS_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_OUTER_TYPE_PARAMETERS_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_LOCAL_TYPE_PARAMETERS_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    // ts#64264
    m.insert(
        Method::GET_THIS_TYPE_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_ALIAS_TYPE_ARGUMENTS_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_ALIAS_SYMBOL_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_OBJECT_TYPE_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_INDEX_TYPE_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_CHECK_TYPE_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_EXTENDS_TYPE_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_BASE_TYPE_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_CONSTRAINT_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_TRUE_TYPE_OF_CONDITIONAL_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_FALSE_TYPE_OF_CONDITIONAL_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );

    m.insert(
        Method::GET_TYPE_PARAMETERS_OF_SIGNATURE,
        unmarshaller_for::<GetSignaturePropertyParams>,
    );
    m.insert(
        Method::GET_PARAMETERS_OF_SIGNATURE,
        unmarshaller_for::<GetSignaturePropertyParams>,
    );
    m.insert(
        Method::GET_THIS_PARAMETER_OF_SIGNATURE,
        unmarshaller_for::<GetSignaturePropertyParams>,
    );
    m.insert(
        Method::GET_TARGET_OF_SIGNATURE,
        unmarshaller_for::<GetSignaturePropertyParams>,
    );

    m.insert(
        Method::GET_CONTEXTUAL_TYPE,
        unmarshaller_for::<GetContextualTypeParams>,
    );
    // ts#64264
    m.insert(
        Method::GET_CONTEXTUAL_TYPE_FOR_ARGUMENT,
        unmarshaller_for::<GetContextualTypeForArgumentParams>,
    );
    m.insert(
        Method::GET_AWAITED_TYPE,
        unmarshaller_for::<CheckerTypeParams>,
    );
    m.insert(
        Method::GET_BASE_TYPE_OF_LITERAL_TYPE,
        unmarshaller_for::<GetBaseTypeOfLiteralTypeParams>,
    );
    m.insert(
        Method::GET_NON_NULLABLE_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_TYPE_FROM_TYPE_NODE,
        unmarshaller_for::<GetTypeFromTypeNodeParams>,
    );
    m.insert(
        Method::GET_WIDENED_TYPE,
        unmarshaller_for::<GetWidenedTypeParams>,
    );
    m.insert(
        Method::GET_PARAMETER_TYPE,
        unmarshaller_for::<GetParameterTypeParams>,
    );
    m.insert(
        Method::GET_TYPE_PARAMETER_AT_POSITION,
        unmarshaller_for::<GetParameterTypeParams>,
    );
    m.insert(
        Method::IS_ARRAY_LIKE_TYPE,
        unmarshaller_for::<IsArrayLikeTypeParams>,
    );
    m.insert(
        Method::IS_TYPE_ASSIGNABLE_TO,
        unmarshaller_for::<IsTypeAssignableToParams>,
    );
    m.insert(
        Method::GET_SHORTHAND_ASSIGNMENT_VALUE_SYMBOL,
        unmarshaller_for::<GetTypeAtLocationParams>,
    );
    m.insert(
        Method::GET_TYPE_OF_SYMBOL_AT_LOCATION,
        unmarshaller_for::<GetTypeOfSymbolAtLocationParams>,
    );
    m.insert(
        Method::TYPE_TO_TYPE_NODE,
        unmarshaller_for::<TypeToTypeNodeParams>,
    );
    m.insert(
        Method::SIGNATURE_TO_SIGNATURE_DECLARATION,
        unmarshaller_for::<SignatureToSignatureDeclarationParams>,
    );
    m.insert(
        Method::TYPE_TO_STRING,
        unmarshaller_for::<TypeToTypeNodeParams>,
    );
    m.insert(
        Method::IS_CONTEXT_SENSITIVE,
        unmarshaller_for::<GetContextualTypeParams>,
    );
    m.insert(
        Method::GET_RETURN_TYPE_OF_SIGNATURE,
        unmarshaller_for::<GetSignaturePropertyParams>,
    );
    m.insert(
        Method::GET_REST_TYPE_OF_SIGNATURE,
        unmarshaller_for::<CheckerSignatureParams>,
    );
    m.insert(
        Method::GET_TYPE_PREDICATE_OF_SIGNATURE,
        unmarshaller_for::<CheckerSignatureParams>,
    );
    m.insert(
        Method::GET_BASE_TYPES,
        unmarshaller_for::<CheckerTypeParams>,
    );
    m.insert(
        Method::GET_PROPERTIES_OF_TYPE,
        unmarshaller_for::<CheckerTypeParams>,
    );
    m.insert(
        Method::GET_APPARENT_PROPERTIES_OF_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_APPARENT_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    // ts#63899
    m.insert(
        Method::GET_REDUCED_TYPE,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_PROPERTY_OF_TYPE,
        unmarshaller_for::<GetPropertyOfTypeParams>,
    );
    // ts#64264
    m.insert(
        Method::GET_TYPE_OF_PROPERTY_OF_TYPE,
        unmarshaller_for::<GetPropertyOfTypeParams>,
    );
    m.insert(
        Method::GET_INDEX_INFO_OF_TYPE,
        unmarshaller_for::<GetIndexInfoOfTypeParams>,
    );
    m.insert(
        Method::GET_INDEX_INFOS_OF_TYPE,
        unmarshaller_for::<CheckerTypeParams>,
    );
    m.insert(
        Method::GET_CONSTRAINT_OF_TYPE_PARAMETER,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_BASE_CONSTRAINT_OF_TYPE,
        unmarshaller_for::<CheckerTypeParams>,
    );
    m.insert(
        Method::GET_DEFAULT_FROM_TYPE_PARAMETER,
        unmarshaller_for::<GetTypePropertyParams>,
    );
    m.insert(
        Method::GET_TYPE_ARGUMENTS,
        unmarshaller_for::<CheckerTypeParams>,
    );
    m.insert(
        Method::GET_IMPORT_ADDER_EDITS,
        unmarshaller_for::<GetImportAdderEditsParams>,
    );
    m.insert(
        Method::GET_CONSTANT_VALUE,
        unmarshaller_for::<CheckerNodeParams>,
    );
    m.insert(
        Method::GET_SIGNATURE_FROM_DECLARATION,
        unmarshaller_for::<CheckerNodeParams>,
    );
    m.insert(
        Method::GET_EXPORT_SPECIFIER_LOCAL_TARGET,
        unmarshaller_for::<CheckerNodeParams>,
    );
    m.insert(
        Method::GET_ALIASED_SYMBOL,
        unmarshaller_for::<CheckerSymbolParams>,
    );
    m.insert(
        Method::GET_IMMEDIATE_ALIASED_SYMBOL,
        unmarshaller_for::<CheckerSymbolParams>,
    );
    // ts#63945
    m.insert(
        Method::GET_TARGET_SYMBOL,
        unmarshaller_for::<CheckerSymbolParams>,
    );
    // ts#64264
    m.insert(
        Method::GET_EXPORT_SYMBOL_OF_SYMBOL_FOR_CHECKER,
        unmarshaller_for::<CheckerSymbolParams>,
    );
    m.insert(
        Method::GET_FULLY_QUALIFIED_NAME,
        unmarshaller_for::<CheckerSymbolParams>,
    );
    m.insert(
        Method::GET_EXPORTS_OF_MODULE,
        unmarshaller_for::<CheckerSymbolParams>,
    );
    m.insert(
        Method::GET_MEMBER_IN_MODULE_EXPORTS,
        unmarshaller_for::<GetMemberInModuleExportsParams>,
    );
    m.insert(
        Method::GET_JS_DOC_TAGS,
        unmarshaller_for::<CheckerSymbolParams>,
    );
    m.insert(
        Method::GET_DOCUMENTATION_COMMENT,
        unmarshaller_for::<CheckerSymbolParams>,
    );
    m.insert(Method::IS_ARRAY_TYPE, unmarshaller_for::<CheckerTypeParams>);
    // ts#63943
    m.insert(
        Method::IS_READONLY_SYMBOL,
        unmarshaller_for::<CheckerSymbolParams>,
    );
    m.insert(
        Method::GET_REFERENCES_TO_SYMBOL_IN_FILE,
        unmarshaller_for::<GetReferencesToSymbolInFileParams>,
    );
    m.insert(
        Method::GET_REFERENCED_SYMBOLS_FOR_NODE,
        unmarshaller_for::<GetReferencedSymbolsForNodeParams>,
    );
    m.insert(
        Method::GET_SIGNATURE_USAGES,
        unmarshaller_for::<GetSignatureUsagesParams>,
    );
    m.insert(
        Method::GET_COMPLETIONS_AT_POSITION,
        unmarshaller_for::<GetCompletionsAtPositionParams>,
    );
    m.insert(Method::PRINT_NODE, unmarshaller_for::<PrintNodeParams>);
    m.insert(
        Method::FORMAT_NODE_FOR_INSERTION,
        unmarshaller_for::<FormatNodeForInsertionParams>,
    );
    // tsgo#4699
    m.insert(Method::EMIT, unmarshaller_for::<EmitParams>);
    m.insert(Method::EMIT_TO_STRING, unmarshaller_for::<EmitParams>);
    m.insert(
        Method::GET_JAVA_SCRIPT_EMIT,
        unmarshaller_for::<SelectedFilesEmitParams>,
    );
    m.insert(
        Method::GET_DECLARATION_EMIT,
        unmarshaller_for::<SelectedFilesEmitParams>,
    );
    m.insert(
        Method::GET_ANY_TYPE,
        unmarshaller_for::<GetIntrinsicTypeParams>,
    );
    m.insert(
        Method::GET_STRING_TYPE,
        unmarshaller_for::<GetIntrinsicTypeParams>,
    );
    m.insert(
        Method::GET_NUMBER_TYPE,
        unmarshaller_for::<GetIntrinsicTypeParams>,
    );
    m.insert(
        Method::GET_BOOLEAN_TYPE,
        unmarshaller_for::<GetIntrinsicTypeParams>,
    );
    m.insert(
        Method::GET_VOID_TYPE,
        unmarshaller_for::<GetIntrinsicTypeParams>,
    );
    m.insert(
        Method::GET_UNDEFINED_TYPE,
        unmarshaller_for::<GetIntrinsicTypeParams>,
    );
    m.insert(
        Method::GET_NULL_TYPE,
        unmarshaller_for::<GetIntrinsicTypeParams>,
    );
    m.insert(
        Method::GET_NEVER_TYPE,
        unmarshaller_for::<GetIntrinsicTypeParams>,
    );
    m.insert(
        Method::GET_UNKNOWN_TYPE,
        unmarshaller_for::<GetIntrinsicTypeParams>,
    );
    m.insert(
        Method::GET_BIG_INT_TYPE,
        unmarshaller_for::<GetIntrinsicTypeParams>,
    );
    m.insert(
        Method::GET_ES_SYMBOL_TYPE,
        unmarshaller_for::<GetIntrinsicTypeParams>,
    );
    m.insert(
        Method::GET_NON_PRIMITIVE_TYPE,
        unmarshaller_for::<GetIntrinsicTypeParams>,
    );
    m.insert(
        Method::GET_WELL_KNOWN_SYMBOLS,
        unmarshaller_for::<GetIntrinsicTypeParams>,
    );
    m.insert(
        Method::GET_WELL_KNOWN_SIGNATURES,
        unmarshaller_for::<GetIntrinsicTypeParams>,
    );
    m.insert(
        Method::GET_SYNTACTIC_DIAGNOSTICS,
        unmarshaller_for::<GetDiagnosticsParams>,
    );
    m.insert(
        Method::GET_BIND_DIAGNOSTICS,
        unmarshaller_for::<GetDiagnosticsParams>,
    );
    m.insert(
        Method::GET_SEMANTIC_DIAGNOSTICS,
        unmarshaller_for::<GetDiagnosticsParams>,
    );
    m.insert(
        Method::GET_SUGGESTION_DIAGNOSTICS,
        unmarshaller_for::<GetDiagnosticsParams>,
    );
    m.insert(
        Method::GET_DECLARATION_DIAGNOSTICS,
        unmarshaller_for::<GetDiagnosticsParams>,
    );
    m.insert(
        Method::GET_PROGRAM_DIAGNOSTICS,
        unmarshaller_for::<GetProjectDiagnosticsParams>,
    );
    m.insert(
        Method::GET_GLOBAL_DIAGNOSTICS,
        unmarshaller_for::<GetProjectDiagnosticsParams>,
    );
    m.insert(
        Method::GET_CONFIG_FILE_PARSING_DIAGNOSTICS,
        unmarshaller_for::<GetProjectDiagnosticsParams>,
    );
    m.insert(Method::START_CPU_PROFILE, unmarshaller_for::<ProfileParams>);
    m.insert(Method::STOP_CPU_PROFILE, no_params);
    m.insert(Method::SAVE_HEAP_PROFILE, unmarshaller_for::<ProfileParams>);
    m
});

// Go: proto.go:405 ParseConfigFileParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ParseConfigFileParams {
    pub file: DocumentIdentifier,
}

proto_json!(both ParseConfigFileParams {
    file: "file" plain,
});

// Go: proto.go:550 ParseCommandLineParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ParseCommandLineParams {
    pub command_line: Vec<String>,
}

proto_json!(both ParseCommandLineParams {
    command_line: "commandLine" plain,
});

// Go: proto.go:554 ReadConfigFileParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ReadConfigFileParams {
    pub file: DocumentIdentifier,
}

proto_json!(both ReadConfigFileParams {
    file: "file" plain,
});

// Go: proto.go:558 ParseJsonConfigFileContentParams
// PORT: Go `JSON packagejson.JSONValue` is `LspAny`. A decoded request value
// must be `Send` (`AnyValue`), and `packagejson::JSONValue` holds `Rc`.
// Both decode a JSON value to the same tree: null, bool, float64, string,
// array, and an object that keeps its member order.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ParseJsonConfigFileContentParams {
    pub json: LspAny,
    pub config_directory: Option<String>,
    pub config_file_name: Option<DocumentIdentifier>,
}

proto_json!(both ParseJsonConfigFileContentParams {
    json: "json" plain,
    config_directory: "configDirectory" omitempty,
    config_file_name: "configFileName" omitempty,
});

// Go: proto.go:564 jsonValueToAny
// PORT: Go `any` from the tsoptions JSON code is `CompilerOptionsValue`
// (nil, string, float64, bool, `[]any`, `*collections.OrderedMap`). The
// input is the `LspAny` that stands for `packagejson.JSONValue` (see
// `ParseJsonConfigFileContentParams`); Go's "not present" is `Null` there.
pub fn json_value_to_any(value: &LspAny) -> tsoptions::CompilerOptionsValue {
    use crate::frontend::tsoptions::CompilerOptionsValue;
    match value {
        LspAny::Null => CompilerOptionsValue::Nil,
        LspAny::String(value) => CompilerOptionsValue::String(value.clone()),
        LspAny::Number(value) => CompilerOptionsValue::Number(*value),
        LspAny::Bool(value) => CompilerOptionsValue::Bool(*value),
        LspAny::Array(array) => {
            let mut result = Vec::with_capacity(array.len());
            for child in array {
                result.push(json_value_to_any(child));
            }
            CompilerOptionsValue::List(result)
        }
        LspAny::Object(object) => {
            let mut result = IndexMap::with_capacity(object.len());
            for (key, child) in object {
                result.insert(key.clone(), json_value_to_any(child));
            }
            CompilerOptionsValue::Map(result)
        }
    }
}

// Go: proto.go:589 TranspileOptions (tsgo#4849)
// PORT: Go `*core.CompilerOptions` is `Option<CompilerOptions>` (nil is
// `None`). Its JSON form is the Go struct default (`CompilerOptionsJSON` to
// write, the `CompilerOptions` `UnmarshalerFrom` below to read).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct TranspileOptions {
    pub compiler_options: Option<CompilerOptions>,
    pub file_name: String,
    pub report_diagnostics: bool,
}

impl MarshalerTo for TranspileOptions {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        let mut first = true;
        marshal_field_omitempty(
            enc,
            &mut first,
            "compilerOptions",
            &self.compiler_options.as_ref().map(CompilerOptionsJSON),
        )?;
        marshal_field_omitempty(enc, &mut first, "fileName", &self.file_name)?;
        marshal_field_omitempty(
            enc,
            &mut first,
            "reportDiagnostics",
            &self.report_diagnostics,
        )?;
        write_object_end(enc);
        Ok(())
    }
}

impl UnmarshalerFrom for TranspileOptions {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let is_object = unmarshal_struct_fields(dec, "api.TranspileOptions", |name, dec| {
            match name {
                "compilerOptions" => json_unmarshal_decode(dec, &mut self.compiler_options)?,
                "fileName" => json_unmarshal_decode(dec, &mut self.file_name)?,
                "reportDiagnostics" => json_unmarshal_decode(dec, &mut self.report_diagnostics)?,
                _ => return Ok(false),
            }
            Ok(true)
        })?;
        if !is_object {
            *self = TranspileOptions::default();
        }
        Ok(())
    }
}

// Go: proto.go:595 TranspileParams (tsgo#4849)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct TranspileParams {
    pub input: String,
    pub options: TranspileOptions,
}

proto_json!(both TranspileParams {
    input: "input" plain,
    options: "options" plain,
});

// Go: proto.go:600 TranspileFromFileParams (tsgo#4849)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct TranspileFromFileParams {
    pub file_name: String,
    pub options: TranspileOptions,
}

proto_json!(both TranspileFromFileParams {
    file_name: "fileName" plain,
    options: "options" plain,
});

// Go: proto.go:605 TranspileOutputResponse (tsgo#4849)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct TranspileOutputResponse {
    pub output_text: String,
    pub diagnostics: Vec<DiagnosticResponse>,
    pub source_map_text: String,
}

proto_json!(marshal TranspileOutputResponse {
    output_text: "outputText" plain,
    diagnostics: "diagnostics" omitempty,
    source_map_text: "sourceMapText" omitempty,
});

// Go: proto.go BatchRequestsParams (ts#63937)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct BatchRequestsParams {
    pub requests: Vec<BatchRequest>,
    // ts#64061
    pub continuation_token: String,
    pub max_response_bytes_per_page: i32,
}

proto_json!(both BatchRequestsParams {
    requests: "requests" plain,
    continuation_token: "continuationToken" omitempty,
    max_response_bytes_per_page: "maxResponseBytesPerPage" omitempty,
});

// Go: proto.go BatchRequest (ts#63937)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct BatchRequest {
    pub method: Method,
    pub params: JsonValue,
}

proto_json!(both BatchRequest {
    method: "method" plain,
    params: "params" omitempty,
});

// Go: proto.go BatchRequestsResponse (ts#63937, ts#64061)
// PORT: Go `encodedResponses []json.Value` is `Option`: `None` is nil.
#[derive(Debug, Default)]
pub struct BatchRequestsResponse {
    pub responses: Vec<BatchResponse>,
    pub continuation_token: String,
    pub encoded_responses: Option<Vec<JsonValue>>,
}

// Go: proto.go BatchRequestsResponse.MarshalJSONTo (ts#64061)
impl MarshalerTo for BatchRequestsResponse {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        enc.push_str("\"responses\":[");
        if let Some(encoded_responses) = &self.encoded_responses {
            for (i, response) in encoded_responses.iter().enumerate() {
                if i > 0 {
                    enc.push(',');
                }
                json_ext::write_value(enc, &response.0)?;
            }
        } else {
            for (i, response) in self.responses.iter().enumerate() {
                if i > 0 {
                    enc.push(',');
                }
                response.marshal_json_to(enc)?;
            }
        }
        enc.push(']');
        if !self.continuation_token.is_empty() {
            enc.push_str(",\"continuationToken\":");
            self.continuation_token.marshal_json_to(enc)?;
        }
        write_object_end(enc);
        Ok(())
    }
}

// Go: proto.go BatchResponse (ts#63937)
// PORT: Go `Result any` is the handler result (`None` is a nil `any`).
#[derive(Debug, Default)]
pub struct BatchResponse {
    pub method: Method,
    pub result: Option<Box<dyn AnyValue>>,
    pub error: String,
}

proto_json!(marshal BatchResponse {
    method: "method" plain,
    result: "result" plain,
    error: "error" omitempty,
});

// ReleaseParams are the parameters for the release method.
// Go: proto.go:410 ReleaseParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ReleaseParams {
    pub snapshot: SnapshotID,
}

proto_json!(both ReleaseParams {
    snapshot: "snapshot" plain,
});

// Go: proto.go:414 ProfileParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ProfileParams {
    pub dir: String,
}

proto_json!(both ProfileParams {
    dir: "dir" plain,
});

// Go: proto.go:418 ProfileResult
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ProfileResult {
    pub file: String,
}

proto_json!(marshal ProfileResult {
    file: "file" plain,
});

// Go: proto.go:422 ConfigFileResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ConfigFileResponse {
    pub file_names: Vec<String>,
    pub options: Option<CompilerOptions>,
    pub project_references: Vec<crate::frontend::core_ext::ProjectReference>,
    pub type_acquisition: Option<crate::frontend::core_ext::TypeAcquisition>,
    pub compile_on_save: Option<bool>,
    pub raw: tsoptions::CompilerOptionsValue,
    pub errors: Vec<DiagnosticResponse>,
}

impl MarshalerTo for ConfigFileResponse {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        let mut first = true;
        marshal_field(enc, &mut first, "fileNames", &self.file_names)?;
        marshal_field(
            enc,
            &mut first,
            "options",
            &self.options.as_ref().map(CompilerOptionsJSON),
        )?;
        marshal_field_omitempty(
            enc,
            &mut first,
            "projectReferences",
            &self.project_references,
        )?;
        marshal_field_omitempty(
            enc,
            &mut first,
            "typeAcquisition",
            &self.type_acquisition.as_ref().map(TypeAcquisitionJSON),
        )?;
        marshal_field_omitempty(enc, &mut first, "compileOnSave", &self.compile_on_save)?;
        marshal_field_omitempty(enc, &mut first, "raw", &AnyJSON(&self.raw))?;
        marshal_field(enc, &mut first, "errors", &self.errors)?;
        write_object_end(enc);
        Ok(())
    }
}

// Go: proto.go:634 ReadConfigFileResponse
// PORT: Go `Config any` is `CompilerOptionsValue` (see `json_value_to_any`).
#[derive(Clone, Debug, PartialEq)]
pub struct ReadConfigFileResponse {
    pub config: tsoptions::CompilerOptionsValue,
    pub error: Option<DiagnosticResponse>,
}

impl MarshalerTo for ReadConfigFileResponse {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        let mut first = true;
        marshal_field(enc, &mut first, "config", &AnyJSON(&self.config))?;
        marshal_field_omitempty(enc, &mut first, "error", &self.error)?;
        write_object_end(enc);
        Ok(())
    }
}

/// Go `any` that holds a tsoptions JSON value: the v2 marshaler of its
/// dynamic type (`build_info::marshal_any`).
pub struct AnyJSON<'a>(pub &'a tsoptions::CompilerOptionsValue);

impl MarshalerTo for AnyJSON<'_> {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        crate::execute::incremental::build_info::marshal_any(enc, self.0)
    }
}

// Go: proto.go:427 GetDefaultProjectForFileParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetDefaultProjectForFileParams {
    pub snapshot: SnapshotID,
    pub file: DocumentIdentifier,
}

proto_json!(both GetDefaultProjectForFileParams {
    snapshot: "snapshot" plain,
    file: "file" plain,
});

// Go: proto.go:432 ProjectResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ProjectResponse {
    pub id: ProjectID,
    pub config_file_name: String,
    // ts#63935
    pub current_directory: String,
    pub parsed_command_line: Option<ConfigFileResponse>,
    // Deprecated: Use parsedCommandLine.fileNames.
    pub root_files: Vec<String>,
    // Deprecated: Use parsedCommandLine.options.
    pub compiler_options: Option<CompilerOptions>,
}

impl MarshalerTo for ProjectResponse {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        let mut first = true;
        marshal_field(enc, &mut first, "id", &self.id)?;
        marshal_field(enc, &mut first, "configFileName", &self.config_file_name)?;
        marshal_field(enc, &mut first, "currentDirectory", &self.current_directory)?;
        marshal_field(
            enc,
            &mut first,
            "parsedCommandLine",
            &self.parsed_command_line,
        )?;
        marshal_field(enc, &mut first, "rootFiles", &self.root_files)?;
        marshal_field(
            enc,
            &mut first,
            "compilerOptions",
            &self.compiler_options.as_ref().map(CompilerOptionsJSON),
        )?;
        write_object_end(enc);
        Ok(())
    }
}

// Go: proto.go:654 NewConfigFileResponse
// PORT: Go shares the `*core.CompilerOptions`, `*core.TypeAcquisition` and
// project reference pointers; the response keeps copies (see
// `new_project_response`). Go `Raw.(*collections.OrderedMap[string, any])`
// is `CompilerOptionsValue::Map`.
pub fn new_config_file_response(
    parsed_command_line: Option<&tsoptions::ParsedCommandLine>,
) -> Option<ConfigFileResponse> {
    let parsed_command_line = parsed_command_line?;
    let mut compile_on_save = parsed_command_line.compile_on_save;
    if compile_on_save.is_none()
        && let tsoptions::CompilerOptionsValue::Map(raw_config) = &parsed_command_line.raw
        && let Some(tsoptions::CompilerOptionsValue::Bool(value)) = raw_config.get("compileOnSave")
    {
        compile_on_save = Some(*value);
    }
    let compiler_options = parsed_command_line.compiler_options();
    // PORT: Go replaces a nil slice with an empty one; a `Vec` is never nil.
    let errors = new_diagnostic_responses(&parsed_command_line.errors);
    Some(ConfigFileResponse {
        file_names: parsed_command_line.file_names().to_vec(),
        options: Some((**compiler_options).clone()),
        project_references: parsed_command_line.project_references().to_vec(),
        type_acquisition: parsed_command_line.type_acquisition().cloned(),
        compile_on_save,
        raw: to_protocol_json_value(&parsed_command_line.raw),
        errors,
    })
}

// Go: proto.go:682 toProtocolJSONValue
pub fn to_protocol_json_value(
    value: &tsoptions::CompilerOptionsValue,
) -> tsoptions::CompilerOptionsValue {
    use crate::frontend::tsoptions::CompilerOptionsValue;
    match value {
        CompilerOptionsValue::WatchFileKind(value) => CompilerOptionsValue::Int(value.0 - 1),
        CompilerOptionsValue::WatchDirectoryKind(value) => CompilerOptionsValue::Int(value.0 - 1),
        CompilerOptionsValue::PollingKind(value) => CompilerOptionsValue::Int(value.0 - 1),
        CompilerOptionsValue::Map(value) => {
            let mut result = IndexMap::with_capacity(value.len());
            for (key, child) in value {
                result.insert(key.clone(), to_protocol_json_value(child));
            }
            CompilerOptionsValue::Map(result)
        }
        CompilerOptionsValue::List(value) => {
            let mut result = Vec::with_capacity(value.len());
            for child in value {
                result.push(to_protocol_json_value(child));
            }
            CompilerOptionsValue::List(result)
        }
        value => value.clone(),
    }
}

// Go: proto.go:707 NewProjectResponse
// PORT: Go shares the `*core.CompilerOptions` pointer; the response keeps
// a copy (responses cross into `Box<dyn AnyValue>`, which is `Send`).
pub fn new_project_response(p: &project::Project) -> ProjectResponse {
    let Some(command_line) = p.command_line.as_ref() else {
        panic!("NewProjectResponse called with unloaded project");
    };
    ProjectResponse {
        id: project_handle(p),
        config_file_name: p.name(),
        // PORT: Go `p.CurrentDirectory()` (ts#63935) returns this field.
        current_directory: p.current_directory.clone(),
        parsed_command_line: new_config_file_response(Some(command_line)),
        root_files: command_line.file_names().to_vec(),
        compiler_options: Some((**command_line.compiler_options()).clone()),
    }
}

// Go: proto.go:448 GetSymbolAtPositionParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetSymbolAtPositionParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub file: DocumentIdentifier,
    pub position: u32,
}

proto_json!(both GetSymbolAtPositionParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    file: "file" plain,
    position: "position" plain,
});

// Go: proto.go:455 GetSymbolsAtPositionsParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetSymbolsAtPositionsParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub file: DocumentIdentifier,
    pub positions: Vec<u32>,
}

proto_json!(both GetSymbolsAtPositionsParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    file: "file" plain,
    positions: "positions" plain,
});

// Go: proto.go:734 GetSymbolOfSourceFileParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetSymbolOfSourceFileParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub file: DocumentIdentifier,
}

proto_json!(both GetSymbolOfSourceFileParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    file: "file" plain,
});

// Go: proto.go:740 GetSymbolsOfSourceFilesParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetSymbolsOfSourceFilesParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub files: Vec<DocumentIdentifier>,
}

proto_json!(both GetSymbolsOfSourceFilesParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    files: "files" plain,
});

// Go: proto.go:462 GetSymbolAtLocationParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetSymbolAtLocationParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub location: NodeHandle,
}

proto_json!(both GetSymbolAtLocationParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    location: "location" plain,
});

// Go: proto.go:468 GetSymbolsAtLocationsParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetSymbolsAtLocationsParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub locations: Vec<NodeHandle>,
}

proto_json!(both GetSymbolsAtLocationsParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    locations: "locations" plain,
});

// Go: proto.go:474 SymbolResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct SymbolResponse {
    pub id: SymbolID,
    // Project is the project in which the symbol was first observed. It is the
    // default project for follow-up lookups whose results can vary by project.
    pub project: ProjectID,
    pub name: String,
    pub flags: u32,
    pub check_flags: u32,
    pub declarations: Vec<NodeHandle>,
    pub value_declaration: NodeHandle,
    pub parent: SymbolID,
    pub export_symbol: SymbolID,
}

proto_json!(marshal SymbolResponse {
    id: "id" plain,
    project: "project" plain,
    name: "name" plain,
    flags: "flags" plain,
    check_flags: "checkFlags" plain,
    declarations: "declarations" omitempty,
    value_declaration: "valueDeclaration" omitempty,
    parent: "parent" omitzero,
    export_symbol: "exportSymbol" omitzero,
});

// Go: proto.go:485 symbolHandles
pub fn symbol_handles(symbols: &SymbolArena, symbol_list: &[SymbolId]) -> Vec<SymbolID> {
    if symbol_list.is_empty() {
        return Vec::new();
    }
    let mut handles = Vec::with_capacity(symbol_list.len());
    for &t in symbol_list {
        handles.push(symbol_handle(symbols, t));
    }
    handles
}

// Go: proto.go:496 GetTypeOfSymbolParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetTypeOfSymbolParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub symbol: SymbolID,
}

proto_json!(both GetTypeOfSymbolParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    symbol: "symbol" plain,
});

// Go: proto.go:502 GetTypesOfSymbolsParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetTypesOfSymbolsParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub symbols: Vec<SymbolID>,
}

proto_json!(both GetTypesOfSymbolsParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    symbols: "symbols" plain,
});

// Go: proto.go:508 TypeResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct TypeResponse {
    pub id: TypeID,
    pub flags: u32,
    pub object_flags: u32,
    // ts#64080
    pub is_tuple_type: bool,

    // Value is literal type data. BigInt literals are encoded as signed decimal
    // strings because JSON cannot represent bigint; absent values are null.
    pub value: LspAny,

    // ObjectType / TypeReference / StringMappingType / IndexType target
    pub target: TypeID,

    // InterfaceType type parameters
    pub type_parameters: Vec<TypeID>,
    pub outer_type_parameters: Vec<TypeID>,
    pub local_type_parameters: Vec<TypeID>,

    // TupleType data
    pub element_flags: Vec<ElementFlags>,
    pub fixed_length: Option<i32>,
    pub tuple_readonly: Option<bool>,
    // ts#64109
    pub labeled_element_declarations: Vec<NodeHandle>,

    // IndexedAccessType data
    pub object_type: TypeID,
    pub index_type: TypeID,

    // ConditionalType data
    pub check_type: TypeID,
    pub extends_type: TypeID,

    // SubstitutionType data
    pub base_type: TypeID,
    pub subst_constraint: TypeID,

    // TemplateLiteralType text segments
    pub texts: Vec<String>,

    // FreshableType data (LiteralType and computed enum types)
    pub fresh_type: TypeID,
    pub regular_type: TypeID,

    // TypeParameter data
    pub is_this_type: bool,

    // InterfaceType data (ts#64264)
    pub this_type: TypeID,

    // IntrinsicType data
    pub intrinsic_name: String,

    // TypeAlias data
    pub alias_type_arguments: Vec<TypeID>,
    pub alias_symbol: SymbolID,

    // Symbol associated with structured types
    pub symbol: SymbolID,
}

impl MarshalerTo for TypeResponse {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        // PORT: `checker.ElementFlags` is a Go uint32 type; it writes as a number.
        let element_flags: Vec<u32> = self.element_flags.iter().map(|f| f.0).collect();
        write_object_start(enc);
        let mut first = true;
        marshal_field(enc, &mut first, "id", &self.id)?;
        marshal_field(enc, &mut first, "flags", &self.flags)?;
        marshal_field_omitempty(enc, &mut first, "objectFlags", &self.object_flags)?;
        marshal_field_omitempty(enc, &mut first, "isTupleType", &self.is_tuple_type)?;
        marshal_field(enc, &mut first, "value", &self.value)?;
        marshal_field_omitzero(enc, &mut first, "target", &self.target)?;
        marshal_field_omitempty(enc, &mut first, "typeParameters", &self.type_parameters)?;
        marshal_field_omitempty(
            enc,
            &mut first,
            "outerTypeParameters",
            &self.outer_type_parameters,
        )?;
        marshal_field_omitempty(
            enc,
            &mut first,
            "localTypeParameters",
            &self.local_type_parameters,
        )?;
        marshal_field_omitempty(enc, &mut first, "elementFlags", &element_flags)?;
        marshal_field_omitempty(enc, &mut first, "fixedLength", &self.fixed_length)?;
        marshal_field_omitempty(enc, &mut first, "readonly", &self.tuple_readonly)?;
        marshal_field_omitempty(
            enc,
            &mut first,
            "labeledElementDeclarations",
            &self.labeled_element_declarations,
        )?;
        marshal_field_omitzero(enc, &mut first, "objectType", &self.object_type)?;
        marshal_field_omitzero(enc, &mut first, "indexType", &self.index_type)?;
        marshal_field_omitzero(enc, &mut first, "checkType", &self.check_type)?;
        marshal_field_omitzero(enc, &mut first, "extendsType", &self.extends_type)?;
        marshal_field_omitzero(enc, &mut first, "baseType", &self.base_type)?;
        marshal_field_omitzero(enc, &mut first, "substConstraint", &self.subst_constraint)?;
        marshal_field_omitempty(enc, &mut first, "texts", &self.texts)?;
        marshal_field_omitzero(enc, &mut first, "freshType", &self.fresh_type)?;
        marshal_field_omitzero(enc, &mut first, "regularType", &self.regular_type)?;
        marshal_field_omitempty(enc, &mut first, "isThisType", &self.is_this_type)?;
        marshal_field_omitzero(enc, &mut first, "thisType", &self.this_type)?;
        marshal_field_omitempty(enc, &mut first, "intrinsicName", &self.intrinsic_name)?;
        marshal_field_omitempty(
            enc,
            &mut first,
            "aliasTypeArguments",
            &self.alias_type_arguments,
        )?;
        marshal_field_omitzero(enc, &mut first, "aliasSymbol", &self.alias_symbol)?;
        marshal_field_omitzero(enc, &mut first, "symbol", &self.symbol)?;
        write_object_end(enc);
        Ok(())
    }
}

// Go: proto.go:562 newTypeResponse
// PORT: Go reads the type through its pointer; the port reads it from the
// checker arena that owns `t`.
pub fn new_type_response(c: &Checker, t: TypeId, id: TypeID) -> TypeResponse {
    let ty = c.ty(t);
    let mut resp = TypeResponse {
        id,
        flags: ty.flags().0,
        ..TypeResponse::default()
    };

    if ty.symbol().is_some() {
        resp.symbol = symbol_handle(&c.symbols, ty.symbol());
    }

    if let Some(alias) = ty.alias() {
        resp.alias_type_arguments = type_handles(alias.type_arguments());
        if alias.symbol().is_some() {
            resp.alias_symbol = symbol_handle(&c.symbols, alias.symbol());
        }
    }

    let flags = ty.flags();
    if flags.intersects(TypeFlags::FRESHABLE) {
        let lit = ty.as_literal_type();
        if flags.intersects(TypeFlags::LITERAL) {
            resp.value = literal_value_to_json(lit.value());
        }
        if lit.fresh_type().is_some() {
            resp.fresh_type = type_handle(lit.fresh_type());
        }
        if lit.regular_type().is_some() {
            resp.regular_type = type_handle(lit.regular_type());
        }
    } else if flags.intersects(TypeFlags::OBJECT) {
        resp.object_flags = ty.object_flags().0;
        // ts#64080
        resp.is_tuple_type = c.is_tuple_type_exported(t);
        let object_flags = ty.object_flags();
        if object_flags.intersects(ObjectFlags::REFERENCE) {
            // PORT: Go takes `ref := t.AsTypeReference()` and calls the
            // promoted `Type.Target()` of the same type.
            let _ = ty.as_type_reference();
            if c.is_tuple_type_target(t) {
                let tuple = ty.as_tuple_type();
                resp.element_flags = tuple.element_flags();
                let fixed_len = tuple.fixed_length();
                resp.fixed_length = Some(fixed_len);
                let is_readonly = tuple.is_readonly();
                resp.tuple_readonly = Some(is_readonly);
            }
            if ty.target().is_some() {
                resp.target = type_handle(ty.target());
            }
        }
        if object_flags.intersects(ObjectFlags::CLASS_OR_INTERFACE) {
            let iface = ty.as_interface_type();
            resp.type_parameters = type_handles(iface.type_parameters());
            resp.outer_type_parameters = type_handles(iface.outer_type_parameters());
            resp.local_type_parameters = type_handles(iface.local_type_parameters());
            // ts#64264
            // PORT: Go `iface.ThisType()` returns this field.
            if iface.this_type.is_some() {
                resp.this_type = type_handle(iface.this_type);
            }
        }
    } else if flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
        // types omitted; fetched via separate request
    } else if flags.intersects(TypeFlags::INDEX) {
        resp.target = type_handle(ty.as_index_type().target());
    } else if flags.intersects(TypeFlags::INDEXED_ACCESS) {
        let data = ty.as_indexed_access_type();
        resp.object_type = type_handle(data.object_type());
        resp.index_type = type_handle(data.index_type());
    } else if flags.intersects(TypeFlags::CONDITIONAL) {
        let data = ty.as_conditional_type();
        resp.check_type = type_handle(data.check_type());
        resp.extends_type = type_handle(data.extends_type());
    } else if flags.intersects(TypeFlags::SUBSTITUTION) {
        let data = ty.as_substitution_type();
        resp.base_type = type_handle(data.base_type());
        resp.subst_constraint = type_handle(data.subst_constraint());
    } else if flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
        let tl = ty.as_template_literal_type();
        resp.texts = tl.texts().to_vec();
        // types omitted; fetched via separate request
    } else if flags.intersects(TypeFlags::STRING_MAPPING) {
        resp.target = type_handle(ty.as_string_mapping_type().target());
    } else if flags.intersects(TypeFlags::TYPE_PARAMETER) {
        resp.is_this_type = ty.as_type_parameter().is_this_type();
    } else if flags.intersects(TypeFlags::INTRINSIC) {
        resp.intrinsic_name = ty.as_intrinsic_type().intrinsic_name().to_string();
    }

    resp
}

// Go: proto.go:648 typeHandles
pub fn type_handles(types: &[TypeId]) -> Vec<TypeID> {
    if types.is_empty() {
        return Vec::new();
    }
    let mut handles = Vec::with_capacity(types.len());
    for &t in types {
        handles.push(type_handle(t));
    }
    handles
}

// Go: proto.go:659 literalValueToJSON
// PORT: the Go `any` value is `Option<&LiteralValue>` (nil is `None`); the
// result holds the same JSON primitive as `LspAny`.
pub fn literal_value_to_json(value: Option<&LiteralValue>) -> LspAny {
    match value {
        Some(LiteralValue::String(v)) => LspAny::String(v.clone()),
        Some(LiteralValue::Number(v)) => {
            // ts#64241
            if v.is_infinite() {
                if v.0 > 0.0 {
                    return LspAny::String("+Infinity".to_string());
                }
                return LspAny::String("-Infinity".to_string());
            }
            if v.is_nan() {
                return LspAny::String("NaN".to_string());
            }
            LspAny::Number(v.0)
        }
        Some(LiteralValue::Bool(v)) => LspAny::Bool(*v),
        // Encode bigint literals as a signed decimal string (e.g. "-123"); the
        // API client decodes this back into a real bigint. JSON has no bigint.
        Some(LiteralValue::PseudoBigInt(v)) => LspAny::String(v.to_string()),
        None => LspAny::Null,
    }
}

// Go: proto.go ConstantValueResponse (ts#64241)
// PORT: Go `Value any` holds a JSON primitive (`literalValueToJSON`).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ConstantValueResponse {
    pub is_number: bool,
    pub value: LspAny,
}

proto_json!(marshal ConstantValueResponse {
    is_number: "isNumber" plain,
    value: "value" plain,
});

// Go: proto.go:674 SignatureResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct SignatureResponse {
    pub id: SignatureID,
    pub flags: u32,
    pub declaration: NodeHandle,
    pub type_parameters: Vec<TypeID>,
    pub parameters: Vec<SymbolID>,
    pub this_parameter: SymbolID,
    pub target: SignatureID,
}

proto_json!(marshal SignatureResponse {
    id: "id" plain,
    flags: "flags" plain,
    declaration: "declaration" omitempty,
    type_parameters: "typeParameters" omitempty,
    parameters: "parameters" omitempty,
    this_parameter: "thisParameter" omitzero,
    target: "target" omitzero,
});

// Go: proto.go:684 GetSourceFileParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetSourceFileParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub file: DocumentIdentifier,
}

proto_json!(both GetSourceFileParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    file: "file" plain,
});

// Go: proto.go:770 GetSourceFileNamesParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetSourceFileNamesParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
}

proto_json!(both GetSourceFileNamesParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
});

// PORT: Go `core.ModuleKind` (and its alias `core.ResolutionMode`) is a Go
// int32 type with no JSON methods, so JSON uses the v2 int arshaler. The
// params of ts#64247 and ts#64292 decode it. Errors name `core.ModuleKind`.
impl MarshalerTo for ModuleKind {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        self.0.marshal_json_to(enc)
    }
}

impl UnmarshalerFrom for ModuleKind {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        self.0
            .unmarshal_json_from(dec)
            .map_err(|err| match SemanticError::of(&err) {
                Some(mut s) => {
                    s.go_type = "core.ModuleKind".to_string();
                    s.into_json_error()
                }
                None => err,
            })
    }
}

impl IsZero for ModuleKind {
    fn is_zero(&self) -> bool {
        self.0 == 0
    }
}

// Go: proto.go GetResolvedModuleParams (ts#64247)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetResolvedModuleParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub file: DocumentIdentifier,
    pub module_name: String,
    pub mode: ResolutionMode,
}

proto_json!(both GetResolvedModuleParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    file: "file" plain,
    module_name: "moduleName" plain,
    mode: "mode" plain,
});

// Go: proto.go GetResolvedModuleFromModuleSpecifierParams (ts#64247)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetResolvedModuleFromModuleSpecifierParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub module_specifier: NodeHandle,
    pub source_file: Option<DocumentIdentifier>,
}

proto_json!(both GetResolvedModuleFromModuleSpecifierParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    module_specifier: "moduleSpecifier" plain,
    source_file: "sourceFile" omitempty,
});

// Go: proto.go GetResolvedTypeReferenceDirectiveParams (ts#64247)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetResolvedTypeReferenceDirectiveParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub file: DocumentIdentifier,
    pub type_directive_name: String,
    pub mode: ResolutionMode,
}

proto_json!(both GetResolvedTypeReferenceDirectiveParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    file: "file" plain,
    type_directive_name: "typeDirectiveName" plain,
    mode: "mode" plain,
});

// Go: proto.go GetResolvedTypeReferenceDirectiveFromReferenceParams (ts#64247)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetResolvedTypeReferenceDirectiveFromReferenceParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub source_file: DocumentIdentifier,
    pub type_directive_name: String,
    pub resolution_mode: ResolutionMode,
}

proto_json!(both GetResolvedTypeReferenceDirectiveFromReferenceParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    source_file: "sourceFile" plain,
    type_directive_name: "typeDirectiveName" plain,
    resolution_mode: "resolutionMode" plain,
});

// Go: proto.go PackageId (ts#64247)
// PORT: `crate::program::PackageId` is Go `module.PackageId`; code outside
// this file names the api one `proto::PackageId`.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct PackageId {
    pub name: String,
    pub sub_module_name: String,
    pub version: String,
    pub peer_dependencies: String,
}

proto_json!(marshal PackageId {
    name: "name" plain,
    sub_module_name: "subModuleName" plain,
    version: "version" plain,
    peer_dependencies: "peerDependencies" plain,
});

// Go: proto.go NewPackageId (ts#64247)
pub fn new_package_id(package_id: &crate::program::PackageId) -> Option<PackageId> {
    if package_id.name.is_empty() {
        return None;
    }
    Some(PackageId {
        name: package_id.name.clone(),
        sub_module_name: package_id.sub_module_name.clone(),
        version: package_id.version.clone(),
        peer_dependencies: package_id.peer_dependencies.clone(),
    })
}

// Go: proto.go ResolvedModule (ts#64247)
// PORT: `crate::program::ResolvedModule` is Go `module.ResolvedModule`; code
// outside this file names the api one `proto::ResolvedModule`.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ResolvedModule {
    pub resolved_file_name: String,
    pub original_path: String,
    pub extension: String,
    pub resolved_using_ts_extension: bool,
    pub resolved_using_extra_extensions: bool,
    pub package_id: Option<PackageId>,
    pub is_external_library_import: bool,
    pub alternate_result: String,
}

proto_json!(marshal ResolvedModule {
    resolved_file_name: "resolvedFileName" plain,
    original_path: "originalPath" omitempty,
    extension: "extension" plain,
    resolved_using_ts_extension: "resolvedUsingTsExtension" omitempty,
    resolved_using_extra_extensions: "resolvedUsingExtraExtensions" omitempty,
    package_id: "packageId" omitempty,
    is_external_library_import: "isExternalLibraryImport" omitempty,
    alternate_result: "alternateResult" omitempty,
});

// Go: proto.go ResolvedTypeReferenceDirective (ts#64247)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ResolvedTypeReferenceDirective {
    pub primary: bool,
    pub resolved_file_name: String,
    pub original_path: String,
    pub package_id: Option<PackageId>,
    pub is_external_library_import: bool,
}

proto_json!(marshal ResolvedTypeReferenceDirective {
    primary: "primary" plain,
    resolved_file_name: "resolvedFileName" plain,
    original_path: "originalPath" omitempty,
    package_id: "packageId" omitempty,
    is_external_library_import: "isExternalLibraryImport" omitempty,
});

// SourceFileMetadata carries program-stored metadata about a single source file.
// Go: proto.go:761 SourceFileMetadata
// PORT: Go `core.ResolutionMode` marshals as its int32 value.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct SourceFileMetadata {
    pub is_default_library: bool,
    pub is_from_external_library: bool,
    pub package_json_type: String,
    pub package_json_directory: String,
    pub implied_node_format: i32,
}

proto_json!(marshal SourceFileMetadata {
    is_default_library: "isDefaultLibrary" plain,
    is_from_external_library: "isFromExternalLibrary" plain,
    package_json_type: "packageJsonType" plain,
    package_json_directory: "packageJsonDirectory" plain,
    implied_node_format: "impliedNodeFormat" plain,
});

// Go: proto.go:690 ResolveNameParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ResolveNameParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub name: String,
    pub location: NodeHandle, // Optional: node handle for location context
    pub file: Option<DocumentIdentifier>, // Optional: file for location context (alternative to Location)
    pub position: Option<u32>, // Optional: position in file for location context (with File)
    pub meaning: u32,          // SymbolFlags for what kind of symbol to find
    pub exclude_globals: bool, // Whether to exclude global symbols
}

proto_json!(both ResolveNameParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    name: "name" plain,
    location: "location" omitempty,
    file: "file" omitempty,
    position: "position" omitempty,
    meaning: "meaning" plain,
    exclude_globals: "excludeGlobals" omitempty,
});

// GetSymbolsInScopeParams are parameters for getSymbolsInScope, which returns
// all symbols visible at a given location.
// Go: proto.go:1007 GetSymbolsInScopeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetSymbolsInScopeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub location: NodeHandle, // Optional: node handle for location context
    pub file: Option<DocumentIdentifier>, // Optional: file for location context (alternative to Location)
    pub position: Option<u32>, // Optional: position in file for location context (with File)
    pub meaning: u32,          // SymbolFlags for what kind of symbols to find
}

proto_json!(both GetSymbolsInScopeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    location: "location" omitempty,
    file: "file" omitempty,
    position: "position" omitempty,
    meaning: "meaning" plain,
});

// GetTypePropertyParams is used for all type sub-property endpoints.
// Go: proto.go:702 GetTypePropertyParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetTypePropertyParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub type_: TypeID,
}

proto_json!(both GetTypePropertyParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    type_: "objectId" plain,
});

// GetSymbolPropertyParams is used for all symbol sub-property endpoints.
// Go: proto.go:708 GetSymbolPropertyParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetSymbolPropertyParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub symbol: SymbolID,
}

proto_json!(both GetSymbolPropertyParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    symbol: "objectId" plain,
});

// GetSignaturePropertyParams is used for all signature sub-property endpoints.
// Go: proto.go:714 GetSignaturePropertyParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetSignaturePropertyParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub signature: SignatureID,
}

proto_json!(both GetSignaturePropertyParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    signature: "objectId" plain,
});

// GetContextualTypeParams returns the contextual type for a node.
// Go: proto.go:720 GetContextualTypeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetContextualTypeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub location: NodeHandle,
}

proto_json!(both GetContextualTypeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    location: "location" plain,
});

// Go: proto.go GetContextualTypeForArgumentParams (ts#64264)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetContextualTypeForArgumentParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub location: NodeHandle,
    pub index: i32,
}

proto_json!(both GetContextualTypeForArgumentParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    location: "location" plain,
    index: "index" plain,
});

// GetTypeOfSymbolAtLocationParams returns the narrowed type of a symbol at a specific location.
// Go: proto.go:727 GetTypeOfSymbolAtLocationParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetTypeOfSymbolAtLocationParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub symbol: SymbolID,
    pub location: NodeHandle,
}

proto_json!(both GetTypeOfSymbolAtLocationParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    symbol: "symbol" plain,
    location: "location" plain,
});

// GetReferencesToSymbolInFileParams are the parameters for the getReferencesToSymbolInFile method.
// Go: proto.go:735 GetReferencesToSymbolInFileParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetReferencesToSymbolInFileParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub file: DocumentIdentifier,
    pub symbol: SymbolID,
}

proto_json!(both GetReferencesToSymbolInFileParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    file: "file" plain,
    symbol: "symbol" plain,
});

// GetReferencedSymbolsForNodeParams are the parameters for the getReferencedSymbolsForNode method.
// Go: proto.go:743 GetReferencedSymbolsForNodeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetReferencedSymbolsForNodeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub node: NodeHandle,
    pub position: i32,
}

proto_json!(both GetReferencedSymbolsForNodeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    node: "node" plain,
    position: "position" plain,
});

// ReferencedSymbolEntry represents a symbol definition and its references.
// Go: proto.go:751 ReferencedSymbolEntry
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ReferencedSymbolEntry {
    pub definition: NodeHandle,
    pub symbol: Option<SymbolResponse>,
    pub references: Vec<NodeHandle>,
}

proto_json!(marshal ReferencedSymbolEntry {
    definition: "definition" plain,
    symbol: "symbol" omitempty,
    references: "references" plain,
});

// GetSignatureUsagesParams are the parameters for the getSignatureUsages method.
// Go: proto.go:758 GetSignatureUsagesParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetSignatureUsagesParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub signature_decl: NodeHandle,
}

proto_json!(both GetSignatureUsagesParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    signature_decl: "signatureDecl" plain,
});

// SignatureUsageResponse represents a single usage of a signature as a name-call pair.
// Go: proto.go:765 SignatureUsageResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct SignatureUsageResponse {
    pub name: NodeHandle,
    pub call: NodeHandle,
}

proto_json!(marshal SignatureUsageResponse {
    name: "name" plain,
    call: "call" omitempty,
});

// GetCompletionsAtPositionParams are the parameters for the getCompletionsAtPosition method.
// Go: proto.go:771 GetCompletionsAtPositionParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetCompletionsAtPositionParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub file: DocumentIdentifier,
    pub position: u32,
    pub trigger_character: Option<String>,
    pub include_symbol: bool,
}

proto_json!(both GetCompletionsAtPositionParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    file: "file" plain,
    position: "position" plain,
    trigger_character: "triggerCharacter" omitempty,
    include_symbol: "includeSymbol" omitempty,
});

// CompletionEntryLabelDetailsResponse holds additional label display text for a completion entry.
// Go: proto.go:781 CompletionEntryLabelDetailsResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct CompletionEntryLabelDetailsResponse {
    pub detail: Option<String>,
    pub description: Option<String>,
}

proto_json!(marshal CompletionEntryLabelDetailsResponse {
    detail: "detail" omitempty,
    description: "description" omitempty,
});

// CompletionEntryResponse represents a single completion item.
// Go: proto.go:787 CompletionEntryResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct CompletionEntryResponse {
    pub name: String,
    pub kind: u32,
    pub sort_text: Option<String>,
    pub insert_text: Option<String>,
    pub filter_text: Option<String>,
    pub detail: Option<String>,
    pub label_details: Option<CompletionEntryLabelDetailsResponse>,
    pub symbol: Option<SymbolResponse>,
}

proto_json!(marshal CompletionEntryResponse {
    name: "name" plain,
    kind: "kind" omitempty,
    sort_text: "sortText" omitempty,
    insert_text: "insertText" omitempty,
    filter_text: "filterText" omitempty,
    detail: "detail" omitempty,
    label_details: "labelDetails" omitempty,
    symbol: "symbol" omitempty,
});

// CompletionInfoResponse wraps a list of completion entries.
// Go: proto.go:799 CompletionInfoResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct CompletionInfoResponse {
    pub is_incomplete: bool,
    pub entries: Vec<CompletionEntryResponse>,
}

proto_json!(marshal CompletionInfoResponse {
    is_incomplete: "isIncomplete" plain,
    entries: "entries" plain,
});

// GetIntrinsicTypeParams is used for intrinsic type getters (anyType, stringType, etc.).
// Go: proto.go:805 GetIntrinsicTypeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetIntrinsicTypeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
}

proto_json!(both GetIntrinsicTypeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
});

// WellKnownSymbolsResponse carries the handle ids of the per-checker singleton
// symbols (unknown, undefined, arguments) so the client can identify them by id
// without a round-trip on every check.
// Go: proto.go:894 WellKnownSymbolsResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct WellKnownSymbolsResponse {
    pub unknown: SymbolID,
    pub undefined: SymbolID,
    pub arguments: SymbolID,
}

proto_json!(marshal WellKnownSymbolsResponse {
    unknown: "unknown" plain,
    undefined: "undefined" plain,
    arguments: "arguments" plain,
});

// WellKnownSignaturesResponse carries the handle id of the per-checker singleton
// unknown signature (the signature the checker yields when a call cannot be
// resolved) so the client can identify it by id without a round-trip on every check.
// Go: proto.go:1140 WellKnownSignaturesResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct WellKnownSignaturesResponse {
    pub unknown: SignatureID,
}

proto_json!(marshal WellKnownSignaturesResponse {
    unknown: "unknown" plain,
});

// GetBaseTypeOfLiteralTypeParams returns the base type of a literal type.
// Go: proto.go:811 GetBaseTypeOfLiteralTypeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetBaseTypeOfLiteralTypeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub type_: TypeID,
}

proto_json!(both GetBaseTypeOfLiteralTypeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    type_: "type" plain,
});

// GetNonNullableTypeParams are the parameters for the getNonNullableType method.
// Go: proto.go:818 GetNonNullableTypeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetNonNullableTypeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub type_: TypeID,
}

proto_json!(both GetNonNullableTypeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    type_: "type" plain,
});

// GetTypeFromTypeNodeParams are the parameters for the getTypeFromTypeNode method.
// Go: proto.go:825 GetTypeFromTypeNodeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetTypeFromTypeNodeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub location: NodeHandle,
}

proto_json!(both GetTypeFromTypeNodeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    location: "location" plain,
});

// GetWidenedTypeParams are the parameters for the getWidenedType method.
// Go: proto.go:832 GetWidenedTypeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetWidenedTypeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub type_: TypeID,
}

proto_json!(both GetWidenedTypeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    type_: "type" plain,
});

// GetParameterTypeParams are the parameters for the getParameterType method.
// Go: proto.go:839 GetParameterTypeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetParameterTypeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub signature: SignatureID,
    pub index: i32,
}

proto_json!(both GetParameterTypeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    signature: "signature" plain,
    index: "index" plain,
});

// IsArrayLikeTypeParams checks whether a type is array-like.
// Go: proto.go:847 IsArrayLikeTypeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct IsArrayLikeTypeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub type_: TypeID,
}

proto_json!(both IsArrayLikeTypeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    type_: "type" plain,
});

// IsTypeAssignableToParams checks assignability between two types.
// Go: proto.go:854 IsTypeAssignableToParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct IsTypeAssignableToParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub source: TypeID,
    pub target: TypeID,
}

proto_json!(both IsTypeAssignableToParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    source: "source" plain,
    target: "target" plain,
});

// Go: proto.go:861 GetSignaturesOfTypeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetSignaturesOfTypeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub type_: TypeID,
    pub kind: i32,
}

proto_json!(both GetSignaturesOfTypeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    type_: "type" plain,
    kind: "kind" plain,
});

// Go: proto.go:868 GetResolvedSignatureParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetResolvedSignatureParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub location: NodeHandle,
}

proto_json!(both GetResolvedSignatureParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    location: "location" plain,
});

// Go: proto.go:874 GetTypeAtLocationParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetTypeAtLocationParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub location: NodeHandle,
}

proto_json!(both GetTypeAtLocationParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    location: "location" plain,
});

// Go: proto.go:880 GetTypeAtLocationsParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetTypeAtLocationsParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub locations: Vec<NodeHandle>,
}

proto_json!(both GetTypeAtLocationsParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    locations: "locations" plain,
});

// Go: proto.go:886 GetTypeAtPositionParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetTypeAtPositionParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub file: DocumentIdentifier,
    pub position: u32,
}

proto_json!(both GetTypeAtPositionParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    file: "file" plain,
    position: "position" plain,
});

// Go: proto.go:893 GetTypesAtPositionsParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetTypesAtPositionsParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub file: DocumentIdentifier,
    pub positions: Vec<u32>,
}

proto_json!(both GetTypesAtPositionsParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    file: "file" plain,
    positions: "positions" plain,
});

// Go: proto.go:1234 ImportAdderActionKind (tsgo#3881)
// PORT: a Go string type, a newtype as the handles are (see `handle_json!`).
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ImportAdderActionKind(pub String);

handle_json!(string: ImportAdderActionKind);

// Go: proto.go:1237 ImportAdderActionKindImportSymbol (tsgo#3881)
pub const IMPORT_ADDER_ACTION_KIND_IMPORT_SYMBOL: &str = "importSymbol";

// Go: proto.go:1240 ImportAdderAction (tsgo#3881)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ImportAdderAction {
    pub kind: ImportAdderActionKind,
    pub symbol: SymbolID,
    pub is_valid_type_only_use_site: Option<bool>,
}

proto_json!(both ImportAdderAction {
    kind: "kind" plain,
    symbol: "symbol" omitempty,
    is_valid_type_only_use_site: "isValidTypeOnlyUseSite" omitempty,
});

// Go: proto.go:1246 GetImportAdderEditsParams (tsgo#3881)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetImportAdderEditsParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub file: DocumentIdentifier,
    pub actions: Vec<ImportAdderAction>,
}

proto_json!(both GetImportAdderEditsParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    file: "file" plain,
    actions: "actions" plain,
});

// Go: proto.go:1253 TextEdit (tsgo#3881)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct TextEdit {
    pub pos: i32,
    pub end: i32,
    pub new_text: String,
}

proto_json!(marshal TextEdit {
    pos: "pos" plain,
    end: "end" plain,
    new_text: "newText" plain,
});

// TypeToTypeNodeParams are the parameters for the typeToTypeNode method.
// Go: proto.go:901 TypeToTypeNodeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct TypeToTypeNodeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub type_: TypeID,
    pub location: NodeHandle,
    pub flags: i32,
}

proto_json!(both TypeToTypeNodeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    type_: "type" plain,
    location: "location" omitempty,
    flags: "flags" omitempty,
});

// SignatureToSignatureDeclarationParams are the parameters for the signatureToSignatureDeclaration method.
// Go: proto.go:910 SignatureToSignatureDeclarationParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct SignatureToSignatureDeclarationParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub signature: SignatureID,
    pub kind: i32,
    pub location: NodeHandle,
    pub flags: i32,
}

proto_json!(both SignatureToSignatureDeclarationParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    signature: "signature" plain,
    kind: "kind" plain,
    location: "location" omitempty,
    flags: "flags" omitempty,
});

// PrintNodeParams are the parameters for the printNode method.
// Go: proto.go:920 PrintNodeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct PrintNodeParams {
    pub data: String, // base64-encoded binary AST data
    pub preserve_source_newlines: bool,
    pub never_ascii_escape: bool,
    pub terminate_unterminated_literals: bool,
}

proto_json!(both PrintNodeParams {
    data: "data" plain,
    preserve_source_newlines: "preserveSourceNewlines" omitempty,
    never_ascii_escape: "neverAsciiEscape" omitempty,
    terminate_unterminated_literals: "terminateUnterminatedLiterals" omitempty,
});

// Go: proto.go:1286 EmitParams (tsgo#4699)
// PORT: Go `*uint32` is `Option<u32>`.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct EmitParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub emit_only: Option<u32>,
}

proto_json!(both EmitParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    emit_only: "emitOnly" omitempty,
});

// Go: proto.go:1292 SelectedFilesEmitParams (tsgo#4699)
// PORT: Go tells a nil `Files` (absent or `null`) from an empty one, so it
// is `Option<Vec>`.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct SelectedFilesEmitParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub files: Option<Vec<DocumentIdentifier>>,
}

proto_json!(both SelectedFilesEmitParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    files: "files" plain,
});

// Go: proto.go:1298 EmitResponse (tsgo#4699)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct EmitResponse {
    pub emit_skipped: bool,
    pub diagnostics: Vec<DiagnosticResponse>,
    pub emitted_files: Vec<String>,
}

proto_json!(marshal EmitResponse {
    emit_skipped: "emitSkipped" plain,
    diagnostics: "diagnostics" plain,
    emitted_files: "emittedFiles" plain,
});

// Go: proto.go:1304 EmitOutputFile (tsgo#4699)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct EmitOutputFile {
    pub file_name: String,
    pub text: String,
    pub source_file_name: Option<String>,
}

proto_json!(marshal EmitOutputFile {
    file_name: "fileName" plain,
    text: "text" plain,
    source_file_name: "sourceFileName" omitempty,
});

// Go: proto.go:1310 EmitOutputResponse (tsgo#4699)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct EmitOutputResponse {
    pub emit_skipped: bool,
    pub diagnostics: Vec<DiagnosticResponse>,
    pub output_files: Vec<EmitOutputFile>,
}

proto_json!(marshal EmitOutputResponse {
    emit_skipped: "emitSkipped" plain,
    diagnostics: "diagnostics" plain,
    output_files: "outputFiles" plain,
});

// FormatNodeForInsertionParams are the parameters for the formatNodeForInsertion method.
// Go: proto.go:1317 FormatNodeForInsertionParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct FormatNodeForInsertionParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub file: DocumentIdentifier, // target file where the node will be inserted
    pub position: u32, // UTF-16 code-unit offset of the insertion position in the target file
    pub data: String,  // base64-encoded binary AST data for the synthesized node
}

proto_json!(both FormatNodeForInsertionParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    file: "file" plain,
    position: "position" plain,
    data: "data" plain,
});

// CheckerTypeParams are parameters for checker methods that operate on a type.
// Go: proto.go:928 CheckerTypeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct CheckerTypeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub type_: TypeID,
}

proto_json!(both CheckerTypeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    type_: "type" plain,
});

// GetPropertyOfTypeParams are parameters for getPropertyOfType (a named property of a type).
// Go: proto.go:984 GetPropertyOfTypeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetPropertyOfTypeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub type_: TypeID,
    pub name: String,
}

proto_json!(both GetPropertyOfTypeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    type_: "type" plain,
    name: "name" plain,
});

// Go: proto.go GetIndexInfoOfTypeParams (ts#64264)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetIndexInfoOfTypeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub type_: TypeID,
    pub kind: i32,
}

proto_json!(both GetIndexInfoOfTypeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    type_: "type" plain,
    kind: "kind" plain,
});

// CheckerNodeParams are parameters for checker methods that operate on a node location.
// Go: proto.go:992 CheckerNodeParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct CheckerNodeParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub location: NodeHandle,
}

proto_json!(both CheckerNodeParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    location: "location" plain,
});

// GetMemberInModuleExportsParams are parameters for getMemberInModuleExports.
// Go: proto.go:1049 GetMemberInModuleExportsParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetMemberInModuleExportsParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub symbol: SymbolID,
    pub name: String,
}

proto_json!(both GetMemberInModuleExportsParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    symbol: "symbol" plain,
    name: "name" plain,
});

// CheckerSymbolParams are parameters for checker methods that operate on a symbol.
// Go: proto.go:1064 CheckerSymbolParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct CheckerSymbolParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub symbol: SymbolID,
}

proto_json!(both CheckerSymbolParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    symbol: "symbol" plain,
});

// JSDocTagInfo is a single JSDoc tag, mirroring Strada's JSDocTagInfo but with the tag text
// rendered as a plain string rather than SymbolDisplayPart[].
// Go: proto.go:1007 JSDocTagInfo
#[derive(Clone, Debug, Default, PartialEq)]
pub struct JSDocTagInfo {
    pub name: String,
    pub text: String,
}

proto_json!(marshal JSDocTagInfo {
    name: "name" plain,
    text: "text" omitempty,
});

// CheckerSignatureParams are parameters for checker methods that operate on a signature.
// Go: proto.go:935 CheckerSignatureParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct CheckerSignatureParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub signature: SignatureID,
}

proto_json!(both CheckerSignatureParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    signature: "signature" plain,
});

// TypePredicateResponse is the response for getTypePredicateOfSignature.
// Go: proto.go:942 TypePredicateResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct TypePredicateResponse {
    pub kind: i32,
    pub parameter_index: i32,
    pub parameter_name: String,
    pub type_: Option<TypeResponse>,
}

proto_json!(marshal TypePredicateResponse {
    kind: "kind" plain,
    parameter_index: "parameterIndex" plain,
    parameter_name: "parameterName" omitempty,
    type_: "type" omitempty,
});

// IndexInfoResponse represents a single index signature.
// Go: proto.go:950 IndexInfoResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct IndexInfoResponse {
    pub key_type: TypeResponse,
    pub value_type: TypeResponse,
    pub is_readonly: bool,
    pub declaration: NodeHandle,
}

proto_json!(marshal IndexInfoResponse {
    key_type: "keyType" plain,
    value_type: "valueType" plain,
    is_readonly: "isReadonly" omitempty,
    declaration: "declaration" omitempty,
});

// SourceFileResponse contains the binary-encoded AST data for a source file.
// The Data field is base64-encoded binary data in the encoder's format.
// Go: proto.go:959 SourceFileResponse
#[derive(Clone, Debug, Default, PartialEq)]
pub struct SourceFileResponse {
    // Data is the base64-encoded binary AST data in the encoder's format.
    pub data: String,
}

proto_json!(marshal SourceFileResponse {
    data: "data" plain,
});

// GetDiagnosticsParams are parameters for per-file diagnostic methods.
// Go: proto.go:964 GetDiagnosticsParams
#[derive(Clone, Debug, Default, PartialEq)]
// PORT: Go `Files []DocumentIdentifier` is `Option`: `None` is a nil slice
// (no `files`, or `null`) and `Some(vec![])` is `[]`. `getDiagnostics`
// tells them apart.
pub struct GetDiagnosticsParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
    pub files: Option<Vec<DocumentIdentifier>>,
}

proto_json!(both GetDiagnosticsParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
    files: "files" omitempty,
});

// GetProjectDiagnosticsParams are parameters for project-wide diagnostic methods.
// Go: proto.go:971 GetProjectDiagnosticsParams
#[derive(Clone, Debug, Default, PartialEq)]
pub struct GetProjectDiagnosticsParams {
    pub snapshot: SnapshotID,
    pub project: ProjectID,
}

proto_json!(both GetProjectDiagnosticsParams {
    snapshot: "snapshot" plain,
    project: "project" plain,
});

// DiagnosticResponse is the API response for a single diagnostic.
// Go: proto.go:977 DiagnosticResponse
// PORT: no `Default`; `diagnostics.Category` has none in the port.
#[derive(Clone, Debug, PartialEq)]
pub struct DiagnosticResponse {
    // FileName is the path of the file this diagnostic belongs to, if any.
    pub file_name: String,
    // Pos is the start position of the diagnostic in the source file.
    pub pos: i32,
    // End is the end position of the diagnostic in the source file.
    pub end: i32,
    // StartPosition is the zero-based line and UTF-16 character position of Pos.
    pub start_position: Option<DiagnosticPositionResponse>,
    // EndPosition is the zero-based line and UTF-16 character position of End.
    pub end_position: Option<DiagnosticPositionResponse>,
    // SourceLines contains the source lines needed to render this diagnostic with context.
    pub source_lines: Vec<DiagnosticSourceLineResponse>,
    // Code is the diagnostic error code.
    pub code: i32,
    // Category is the diagnostic category (error, warning, suggestion, message).
    pub category: crate::diagnostics::Category,
    // Source is a custom diagnostic-code prefix. An empty value uses the default "TS".
    pub source: String,
    // Text is the localized diagnostic message text.
    pub text: String,
    // ReportsUnnecessary indicates this diagnostic highlights unnecessary code.
    pub reports_unnecessary: bool,
    // ReportsDeprecated indicates this diagnostic highlights deprecated code.
    pub reports_deprecated: bool,
    // MessageChain contains chained diagnostic messages, if any.
    pub message_chain: Vec<DiagnosticResponse>,
    // RelatedInformation contains related diagnostic information, if any.
    pub related_information: Vec<DiagnosticResponse>,
}

impl MarshalerTo for DiagnosticResponse {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        let mut first = true;
        marshal_field_omitempty(enc, &mut first, "fileName", &self.file_name)?;
        marshal_field(enc, &mut first, "pos", &self.pos)?;
        marshal_field(enc, &mut first, "end", &self.end)?;
        marshal_field_omitempty(enc, &mut first, "startPosition", &self.start_position)?;
        marshal_field_omitempty(enc, &mut first, "endPosition", &self.end_position)?;
        marshal_field_omitempty(enc, &mut first, "sourceLines", &self.source_lines)?;
        marshal_field(enc, &mut first, "code", &self.code)?;
        // PORT: `diagnostics.Category` is a Go int32 type; it writes as a number.
        marshal_field(enc, &mut first, "category", &(self.category as i32))?;
        marshal_field_omitempty(enc, &mut first, "source", &self.source)?;
        marshal_field(enc, &mut first, "text", &self.text)?;
        marshal_field_omitzero(
            enc,
            &mut first,
            "reportsUnnecessary",
            &self.reports_unnecessary,
        )?;
        marshal_field_omitzero(
            enc,
            &mut first,
            "reportsDeprecated",
            &self.reports_deprecated,
        )?;
        marshal_field_omitempty(enc, &mut first, "messageChain", &self.message_chain)?;
        marshal_field_omitempty(
            enc,
            &mut first,
            "relatedInformation",
            &self.related_information,
        )?;
        write_object_end(enc);
        Ok(())
    }
}

// Go: proto.go DiagnosticPositionResponse (ts#63935)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct DiagnosticPositionResponse {
    pub line: i32,
    // PORT: Go `core.UTF16Offset`.
    pub character: i32,
}

proto_json!(marshal DiagnosticPositionResponse {
    line: "line" plain,
    character: "character" plain,
});

// Go: proto.go DiagnosticSourceLineResponse (ts#63935)
#[derive(Clone, Debug, Default, PartialEq)]
pub struct DiagnosticSourceLineResponse {
    pub line: i32,
    pub text: String,
}

proto_json!(marshal DiagnosticSourceLineResponse {
    line: "line" plain,
    text: "text" plain,
});

// Go: proto.go diagnosticSourceLines (ts#63935)
// PORT: Go returns nil for an empty line map; the field is `omitempty`, so
// an empty `Vec` writes the same JSON.
fn diagnostic_source_lines(
    file: &diagnosticwriter::FileLike,
    first_line: i32,
    last_line: i32,
) -> Vec<DiagnosticSourceLineResponse> {
    let line_map = file.ecma_line_map();
    if line_map.is_empty() {
        return Vec::new();
    }

    let mut lines: Vec<i32> = Vec::with_capacity((last_line - first_line + 1).clamp(0, 4) as usize);
    if last_line - first_line >= 4 {
        lines.extend([first_line, first_line + 1, last_line - 1, last_line]);
    } else {
        for line in first_line..=last_line {
            lines.push(line);
        }
    }

    let text = file.text();
    let mut result = Vec::with_capacity(lines.len());
    for line in lines {
        let start = line_map[line as usize] as usize;
        let mut end = text.len();
        if ((line + 1) as usize) < line_map.len() {
            end = line_map[(line + 1) as usize] as usize;
        }
        result.push(DiagnosticSourceLineResponse {
            line,
            text: text[start..end].to_string(),
        });
    }
    result
}

// Go: proto.go:1001 NewDiagnosticResponse
// NewDiagnosticResponse converts an ast.Diagnostic to a DiagnosticResponse.
pub fn new_diagnostic_response(d: &Diagnostic) -> DiagnosticResponse {
    new_diagnostic_response_wrapped(diagnosticwriter::wrap_ast_diagnostic(d))
}

// Go: proto.go newDiagnosticResponse (ts#63935)
// PORT: Go names it `newDiagnosticResponse`, which snakes to the name of the
// exported function; the wrapped form gets the `_wrapped` suffix.
fn new_diagnostic_response_wrapped(d: diagnosticwriter::AstDiagnostic<'_>) -> DiagnosticResponse {
    let file = d.file();
    let (mut pos, mut end) = (d.pos(), d.end());
    if let Some(file) = &file {
        let text_len = file.text().len() as i32;
        pos = 0.max(pos.min(text_len));
        end = pos.max(end.min(text_len));
    }
    let mut resp = DiagnosticResponse {
        file_name: String::new(),
        pos,
        end,
        start_position: None,
        end_position: None,
        source_lines: Vec::new(),
        code: d.0.code,
        category: d.0.category,
        source: d.source().to_string(),
        text: d.0.localize(&crate::locale::DEFAULT),
        reports_unnecessary: d.0.reports_unnecessary,
        reports_deprecated: d.0.reports_deprecated,
        message_chain: Vec::new(),
        related_information: Vec::new(),
    };

    if let Some(file) = &file {
        resp.file_name = file.file_name().to_string();
        if let diagnosticwriter::FileLike::Source(source_file) = file {
            let position_map = source_file_get_position_map(*source_file);
            resp.pos = position_map.utf8_to_utf16(pos);
            resp.end = position_map.utf8_to_utf16(end);
        } else {
            resp.pos = utf16_len_of_prefix(file.text(), pos);
            resp.end = utf16_len_of_prefix(file.text(), end);
        }
        let (start_line, start_character) =
            diagnosticwriter::get_ecma_line_and_utf16_character_of_file_position(file, pos);
        let (end_line, end_character) =
            diagnosticwriter::get_ecma_line_and_utf16_character_of_file_position(file, end);
        resp.start_position = Some(DiagnosticPositionResponse {
            line: start_line,
            character: start_character,
        });
        resp.end_position = Some(DiagnosticPositionResponse {
            line: end_line,
            character: end_character,
        });
        resp.source_lines = diagnostic_source_lines(file, start_line, end_line);
    }

    let chain = d.message_chain();
    if !chain.is_empty() {
        resp.message_chain = Vec::with_capacity(chain.len());
        for c in &chain {
            resp.message_chain.push(new_diagnostic_response_wrapped(
                diagnosticwriter::wrap_ast_diagnostic(c),
            ));
        }
    }

    let related: Vec<_> = d.related_information().collect();
    if !related.is_empty() {
        resp.related_information = Vec::with_capacity(related.len());
        for r in related {
            resp.related_information
                .push(new_diagnostic_response_wrapped(r));
        }
    }

    resp
}

/// Go `int(core.UTF16Len(text[:pos]))`. Go cuts the bytes at `pos`; a cut
/// char reads as one RuneError per byte, one UTF-16 unit each.
fn utf16_len_of_prefix(text: &str, pos: i32) -> i32 {
    let end = pos as usize;
    let mut boundary = end;
    while !text.is_char_boundary(boundary) {
        boundary -= 1;
    }
    utf16_len(&text[..boundary]) + (end - boundary) as i32
}

// Go: proto.go:1042 NewDiagnosticResponses
// NewDiagnosticResponses converts a slice of ast.Diagnostics to DiagnosticResponses.
pub fn new_diagnostic_responses(diags: &[Diagnostic]) -> Vec<DiagnosticResponse> {
    if diags.is_empty() {
        return Vec::new();
    }
    let mut result = Vec::with_capacity(diags.len());
    for d in diags {
        result.push(new_diagnostic_response(d));
    }
    result
}

// Go: proto.go:1053 unmarshalPayload
pub fn unmarshal_payload(
    method: &str,
    payload: impl AsRef<[u8]>,
) -> Result<Option<Box<dyn AnyValue>>, GoError> {
    let Some(unmarshaler) = UNMARSHALERS.get(&Method(Cow::Owned(method.to_string()))) else {
        return Err(errors::new(format!(
            "unknown API method {}",
            strconv::quote(method)
        )));
    };
    unmarshaler(payload.as_ref())
}

// Go: proto.go:1061 unmarshallerFor
// `unmarshal_root` is Go `json.Unmarshal` with the v2 error text.
pub fn unmarshaller_for<T: UnmarshalerFrom + Default + AnyValue>(
    data: &[u8],
) -> Result<Option<Box<dyn AnyValue>>, GoError> {
    let mut v = T::default();
    if let Err(err) = unmarshal_root(data, &mut v) {
        let err = errors::from_value(err);
        return Err(errors::errorf(
            format!(
                "failed to unmarshal *{}: {}",
                go_type_name::<T>(),
                err.error()
            ),
            vec![err],
        ));
    }
    Ok(Some(Box::new(v)))
}

// Go: proto.go:1069 noParams
pub fn no_params(data: &[u8]) -> Result<Option<Box<dyn AnyValue>>, GoError> {
    let _ = data;
    Ok(None)
}

// PORT: the JSON form of `core.CompilerOptions` (`CompilerOptionsJSON`,
// `TypeAcquisitionJSON` and the `CompilerOptions` decode) and
// `marshal_field_omitempty` live in `crate::options_json`, so the compiler
// side (content mappers) does not depend on `api`. Go keeps them in `core`
// (struct tags) and in the json package.
pub use crate::options_json::{CompilerOptionsJSON, TypeAcquisitionJSON, marshal_field_omitempty};

#[cfg(test)]
mod unmarshal_error_tests {
    use super::*;

    fn err_text<T: UnmarshalerFrom + Default + AnyValue>(data: &str) -> String {
        unmarshaller_for::<T>(data.as_bytes())
            .expect_err("want an error")
            .error()
    }

    // Expected texts come from the pinned Go API (tests2 S5-003 goldens and
    // Go JSON v2); Go writes "cannot" or "unable to".
    #[test]
    fn decode_errors_match_go() {
        assert_eq!(
            err_text::<GetSymbolAtPositionParams>(
                r#"{"snapshot":1,"project":"p","file":"a.ts","position":"x"}"#
            ),
            r#"failed to unmarshal *api.GetSymbolAtPositionParams: json: cannot unmarshal JSON string into Go uint32 within "/position""#
        );
        assert_eq!(
            err_text::<ReleaseParams>(r#"{"snapshot":"x"}"#),
            r#"failed to unmarshal *api.ReleaseParams: json: cannot unmarshal JSON string into Go api.SnapshotID within "/snapshot""#
        );
        assert_eq!(
            err_text::<GetSymbolsAtPositionsParams>(r#"{"snapshot":1,"positions":[1,"x"]}"#),
            r#"failed to unmarshal *api.GetSymbolsAtPositionsParams: json: cannot unmarshal JSON string into Go uint32 within "/positions/1""#
        );
        assert_eq!(
            err_text::<GetSourceFileParams>(r#"{"snapshot":1,"file":5}"#),
            r#"failed to unmarshal *api.GetSourceFileParams: json: cannot unmarshal into Go api.DocumentIdentifier within "/file": DocumentIdentifier: expected string or object, got number"#
        );
    }

    // tsgo#4849: the client sends back the `compilerOptions` that the API
    // wrote (`CompilerOptionsJSON`). Decoding them and writing them again
    // gives the same text. The options are those of the hono-ext traces.
    #[test]
    fn transpile_compiler_options_round_trip() {
        let options = r#"{"composite":true,"declaration":true,"forceConsistentCasingInFileNames":true,"module":6,"moduleResolution":100,"noUnusedLocals":true,"noUnusedParameters":true,"outDir":"/p/dist/types","paths":{"a/*":["b/*"],"c":["d"]},"rootDir":"/p/src","skipLibCheck":true,"strict":true,"target":9,"types":["node"],"esModuleInterop":true,"configFilePath":"/p/tsconfig.build.json"}"#;
        let data = format!(
            r#"{{"fileName":"/p/src/a.ts","options":{{"compilerOptions":{options},"reportDiagnostics":true}}}}"#
        );
        let parsed = unmarshaller_for::<TranspileFromFileParams>(data.as_bytes())
            .expect("valid params")
            .expect("params value");
        let params = parsed
            .downcast_ref::<TranspileFromFileParams>()
            .expect("TranspileFromFileParams");
        assert!(params.options.report_diagnostics);
        let compiler_options = params
            .options
            .compiler_options
            .as_ref()
            .expect("compilerOptions");
        assert_eq!(compiler_options.module, ModuleKind(6));
        assert_eq!(compiler_options.strict, Tristate::True);
        let written =
            crate::frontend::json::json_marshal(&CompilerOptionsJSON(compiler_options), &[])
                .expect("marshal");
        assert_eq!(written, options);
    }
}
