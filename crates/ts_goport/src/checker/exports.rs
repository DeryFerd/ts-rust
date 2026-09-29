use crate::diagnostics::Message;
use crate::prelude::*;

// Port of checker/exports.go (all): the exported Checker API that the
// language service calls.
//
// PORT: names. When the unexported Go twin has the same snake name, the
// exported method ends in `_exported` (PORTING.md). The names follow
// `checker-api-tools/names_exports_services.tsv` column 5.
// PORT: Go package-level functions in this file (`IsTypeUsableAsPropertyName`,
// `GetPropertyNameFromType`, `GetDeclarationModifierFlagsFromSymbol`,
// `IsTupleType`) read type or symbol data, so they are Checker methods.
// PORT: a Go `[]*T` result is a `Vec<T>`. Where the twin returns a
// `SharedList`, the wrapper copies it into a `Vec`.

impl Checker {
    // Go: checker/exports.go:9 GetStringType
    pub fn get_string_type(&self) -> TypeId {
        self.string_type
    }

    // Go: checker/exports.go:13 GetNumberType
    pub fn get_number_type(&self) -> TypeId {
        self.number_type
    }

    // Go: checker/exports.go:17 GetBooleanType
    pub fn get_boolean_type(&self) -> TypeId {
        self.boolean_type
    }

    // Go: checker/exports.go:21 GetVoidType
    pub fn get_void_type(&self) -> TypeId {
        self.void_type
    }

    // Go: checker/exports.go:25 GetUndefinedType
    pub fn get_undefined_type(&self) -> TypeId {
        self.undefined_type
    }

    // Go: checker/exports.go:29 GetNullType
    pub fn get_null_type(&self) -> TypeId {
        self.null_type
    }

    // Go: checker/exports.go:33 GetAnyType
    pub fn get_any_type(&self) -> TypeId {
        self.any_type
    }

    // Go: checker/exports.go:37 GetErrorType
    pub fn get_error_type(&self) -> TypeId {
        self.error_type
    }

    // Go: checker/exports.go:41 GetNeverType
    pub fn get_never_type(&self) -> TypeId {
        self.never_type
    }

    // Go: checker/exports.go:45 GetUnknownType
    pub fn get_unknown_type(&self) -> TypeId {
        self.unknown_type
    }

    // Go: checker/exports.go:49 GetBigIntType
    pub fn get_big_int_type(&self) -> TypeId {
        self.bigint_type
    }

    // Go: checker/exports.go:53 GetESSymbolType
    pub fn get_es_symbol_type(&self) -> TypeId {
        self.es_symbol_type
    }

    // Go: checker/exports.go:57 GetNonPrimitiveType
    pub fn get_non_primitive_type(&self) -> TypeId {
        self.non_primitive_type
    }

    // Go: checker/exports.go:57 GetBaseTypeOfLiteralType
    pub fn get_base_type_of_literal_type_exported(&mut self, t: TypeId) -> TypeId {
        self.get_base_type_of_literal_type(t)
    }

    // Go: checker/exports.go:61 GetUnknownSymbol
    pub fn get_unknown_symbol(&self) -> SymbolId {
        self.unknown_symbol
    }

    // Go: checker/exports.go:65 GetUndefinedSymbol
    pub fn get_undefined_symbol(&self) -> SymbolId {
        self.undefined_symbol
    }

    // Go: checker/exports.go:69 GetArgumentsSymbol
    pub fn get_arguments_symbol(&self) -> SymbolId {
        self.arguments_symbol
    }

    // Go: checker/exports.go:77 GetUnknownSignature
    pub fn get_unknown_signature(&self) -> SignatureId {
        self.unknown_signature
    }

    // Go: checker/exports.go:65 GetUnionType
    pub fn get_union_type_exported(&mut self, types: &[TypeId]) -> TypeId {
        self.get_union_type(types)
    }

    // Go: checker/exports.go:69 GetNameTypeOfSymbol
    pub fn get_name_type_of_symbol(&self, symbol: SymbolId) -> TypeId {
        if !self.value_symbol_links.has(symbol) {
            return TypeId::NIL;
        }
        self.value_symbol_links
            .try_get(symbol)
            .expect("value symbol links exist")
            .name_type
    }

    // Go: checker/exports.go:76 IsTypeUsableAsPropertyName
    pub fn is_type_usable_as_property_name_exported(&self, t: TypeId) -> bool {
        self.is_type_usable_as_property_name(t)
    }

    // Go: checker/exports.go:80 GetPropertyNameFromType
    pub fn get_property_name_from_type_exported(&self, t: TypeId) -> String {
        self.get_property_name_from_type(t)
    }

    // Go: checker/exports.go:84 GetGlobalSymbol
    pub fn get_global_symbol_exported(
        &mut self,
        name: &str,
        meaning: SymbolFlags,
        diagnostic: Option<&'static Message>,
    ) -> SymbolId {
        self.get_global_symbol(name, meaning, diagnostic)
    }

    // Go: checker/exports.go:88 GetMergedSymbol
    pub fn get_merged_symbol_exported(&self, symbol: SymbolId) -> SymbolId {
        self.get_merged_symbol(symbol)
    }

    // Go: checker/exports.go:92 TryFindAmbientModule
    pub fn try_find_ambient_module_exported(&mut self, module_name: &str) -> SymbolId {
        self.try_find_ambient_module(module_name, true /*withAugmentations*/)
    }

    // Go: checker/exports.go:96 GetImmediateAliasedSymbol
    pub fn get_immediate_aliased_symbol_exported(&mut self, symbol: SymbolId) -> SymbolId {
        self.get_immediate_aliased_symbol(symbol)
    }

    // Go: checker/exports.go:116 GetTargetSymbol
    pub fn get_target_symbol_exported(&mut self, symbol: SymbolId) -> SymbolId {
        self.get_target_symbol(symbol)
    }

    // Go: checker/exports.go:100 GetTypeOnlyAliasDeclaration
    pub fn get_type_only_alias_declaration_exported(&mut self, symbol: SymbolId) -> Node {
        self.get_type_only_alias_declaration(symbol)
    }

    // Go: checker/exports.go:104 ResolveExternalModuleName
    pub fn resolve_external_module_name_exported(&mut self, module_specifier: Node) -> SymbolId {
        self.resolve_external_module_name(
            module_specifier,
            module_specifier,
            true, /*ignoreErrors*/
        )
    }

    // Go: checker/exports.go:108 ResolveExternalModuleSymbol
    pub fn resolve_external_module_symbol_exported(&mut self, module_symbol: SymbolId) -> SymbolId {
        self.resolve_external_module_symbol(module_symbol, false /*dontResolveAlias*/)
    }

    // Go: checker/exports.go:112 GetTypeFromTypeNode
    pub fn get_type_from_type_node_exported(&mut self, node: Node) -> TypeId {
        self.get_type_from_type_node(node)
    }

    // Go: checker/exports.go:116 IsArrayLikeType
    pub fn is_array_like_type_exported(&mut self, t: TypeId) -> bool {
        self.is_array_like_type(t)
    }

    // Go: checker/exports.go:120 GetPropertiesOfType
    pub fn get_properties_of_type_exported(&mut self, t: TypeId) -> Vec<SymbolId> {
        self.get_properties_of_type(t).to_vec()
    }

    // Go: checker/exports.go:124 GetPropertyOfType
    pub fn get_property_of_type_exported(&mut self, t: TypeId, name: &str) -> SymbolId {
        self.get_property_of_type(t, name)
    }

    // Go: checker/exports.go:128 TypeHasCallOrConstructSignatures
    pub fn type_has_call_or_construct_signatures_exported(&mut self, t: TypeId) -> bool {
        self.type_has_call_or_construct_signatures(t)
    }

    // Go: checker/exports.go:140 IsPropertyAccessible
    // Checks if a property can be accessed in a location.
    // The location is given by the `node` parameter.
    // The node does not need to be a property access.
    // @param node location where to check property accessibility
    // @param isSuper whether to consider this a `super` property access, e.g. `super.foo`.
    // @param isWrite whether this is a write access, e.g. `++foo.x`.
    // @param containingType type where the property comes from.
    // @param property property symbol.
    pub fn is_property_accessible_exported(
        &mut self,
        node: Node,
        is_super: bool,
        is_write: bool,
        containing_type: TypeId,
        property: SymbolId,
    ) -> bool {
        self.is_property_accessible(node, is_super, is_write, containing_type, property)
    }

    // Go: checker/exports.go:144 GetTypeOfPropertyOfContextualType
    pub fn get_type_of_property_of_contextual_type_exported(
        &mut self,
        t: TypeId,
        name: &str,
    ) -> TypeId {
        self.get_type_of_property_of_contextual_type(t, name)
    }

    // Go: checker/exports.go:148 GetDeclarationModifierFlagsFromSymbol
    pub fn get_declaration_modifier_flags_from_symbol_exported(
        &self,
        s: SymbolId,
    ) -> ModifierFlags {
        self.get_declaration_modifier_flags_from_symbol(s)
    }

    // Go: checker/exports.go:152 WasCanceled
    pub fn was_canceled(&self) -> bool {
        self.was_canceled
    }

    // Go: checker/exports.go:156 GetSignaturesOfType
    pub fn get_signatures_of_type_exported(
        &mut self,
        t: TypeId,
        kind: SignatureKind,
    ) -> Vec<SignatureId> {
        self.get_signatures_of_type(t, kind).to_vec()
    }

    // Go: checker/exports.go:160 GetDeclaredTypeOfSymbol
    pub fn get_declared_type_of_symbol_exported(&mut self, symbol: SymbolId) -> TypeId {
        self.get_declared_type_of_symbol(symbol)
    }

    // Go: checker/exports.go:164 GetTypeOfSymbol
    pub fn get_type_of_symbol_exported(&mut self, symbol: SymbolId) -> TypeId {
        self.get_type_of_symbol(symbol)
    }

    // Go: checker/exports.go:168 GetConstraintOfTypeParameter
    pub fn get_constraint_of_type_parameter_exported(&mut self, type_parameter: TypeId) -> TypeId {
        self.get_constraint_of_type_parameter(type_parameter)
    }

    // Go: checker/exports.go:172 GetTrueTypeOfConditionalType
    pub fn get_true_type_of_conditional_type(&mut self, t: TypeId) -> TypeId {
        self.get_true_type_from_conditional_type(t)
    }

    // Go: checker/exports.go:176 GetFalseTypeOfConditionalType
    pub fn get_false_type_of_conditional_type(&mut self, t: TypeId) -> TypeId {
        self.get_false_type_from_conditional_type(t)
    }

    // Go: checker/exports.go:172 GetDefaultFromTypeParameter
    pub fn get_default_from_type_parameter_exported(&mut self, type_parameter: TypeId) -> TypeId {
        self.get_default_from_type_parameter(type_parameter)
    }

    // Go: checker/exports.go:176 GetResolutionModeOverride
    pub fn get_resolution_mode_override_exported(
        &mut self,
        node: Node,
        report_errors: bool,
    ) -> ResolutionMode {
        self.get_resolution_mode_override(node, report_errors)
    }

    // Go: checker/exports.go:180 GetEffectiveDeclarationFlags
    pub fn get_effective_declaration_flags_exported(
        &mut self,
        n: Node,
        flags_to_check: ModifierFlags,
    ) -> ModifierFlags {
        self.get_effective_declaration_flags(n, flags_to_check)
    }

    // Go: checker/exports.go:184 GetBaseConstraintOfType
    pub fn get_base_constraint_of_type_exported(&mut self, t: TypeId) -> TypeId {
        self.get_base_constraint_of_type(t)
    }

    // Go: checker/exports.go:188 GetTypePredicateOfSignature
    pub fn get_type_predicate_of_signature_exported(
        &mut self,
        sig: SignatureId,
    ) -> TypePredicateId {
        self.get_type_predicate_of_signature(sig)
    }

    // Go: checker/exports.go:192 IsTupleType
    pub fn is_tuple_type_exported(&self, t: TypeId) -> bool {
        self.is_tuple_type(t)
    }

    // Go: checker/exports.go:196 IsArrayType
    pub fn is_array_type_exported(&self, t: TypeId) -> bool {
        self.is_array_type(t)
    }

    // Go: checker/exports.go:228 IsReadonlySymbol
    pub fn is_readonly_symbol_exported(&mut self, symbol: SymbolId) -> bool {
        self.is_readonly_symbol(symbol)
    }

    // Go: checker/exports.go:196 GetReturnTypeOfSignature
    pub fn get_return_type_of_signature_exported(&mut self, sig: SignatureId) -> TypeId {
        self.get_return_type_of_signature(sig)
    }

    // Go: checker/exports.go:200 HasEffectiveRestParameter
    pub fn has_effective_rest_parameter_exported(&mut self, signature: SignatureId) -> bool {
        self.has_effective_rest_parameter(signature)
    }

    // Go: checker/exports.go:204 GetLocalTypeParametersOfClassOrInterfaceOrTypeAlias
    pub fn get_local_type_parameters_of_class_or_interface_or_type_alias_exported(
        &mut self,
        symbol: SymbolId,
    ) -> Vec<TypeId> {
        self.get_local_type_parameters_of_class_or_interface_or_type_alias(symbol)
    }

    // Go: checker/exports.go:208 GetContextualTypeForObjectLiteralElement
    pub fn get_contextual_type_for_object_literal_element_exported(
        &mut self,
        element: Node,
        context_flags: ContextFlags,
    ) -> TypeId {
        self.get_contextual_type_for_object_literal_element(element, context_flags)
    }

    // Go: checker/exports.go:212 TypePredicateToString
    pub fn type_predicate_to_string_exported(&mut self, t: TypePredicateId) -> String {
        self.type_predicate_to_string(t)
    }

    // Go: checker/exports.go:216 GetExpandedParameters
    pub fn get_expanded_parameters_exported(
        &mut self,
        signature: SignatureId,
        skip_union_expanding: bool,
    ) -> Vec<Vec<SymbolId>> {
        self.get_expanded_parameters(signature, skip_union_expanding)
    }

    // Go: checker/exports.go:220 GetResolvedSignature
    pub fn get_resolved_signature_exported(&mut self, node: Node) -> SignatureId {
        self.get_resolved_signature(node, None, CheckMode::NORMAL)
    }

    // Go: checker/exports.go:225 GetTypeOfPropertyOfType
    // Return the type of the given property in the given type, or nil if no such property exists
    pub fn get_type_of_property_of_type_exported(&mut self, t: TypeId, name: &str) -> TypeId {
        self.get_type_of_property_of_type(t, name)
    }

    // Go: checker/exports.go:229 GetContextualTypeForArgumentAtIndex
    pub fn get_contextual_type_for_argument_at_index_exported(
        &mut self,
        node: Node,
        arg_index: i32,
    ) -> TypeId {
        self.get_contextual_type_for_argument_at_index(node, arg_index)
    }

    // Go: checker/exports.go:233 GetIndexSignaturesAtLocation
    pub fn get_index_signatures_at_location_exported(&mut self, node: Node) -> Vec<Node> {
        self.get_index_signatures_at_location(node)
    }

    // Go: checker/exports.go:237 GetResolvedSymbol
    pub fn get_resolved_symbol_exported(&mut self, node: Node) -> SymbolId {
        self.get_resolved_symbol(node)
    }

    // Go: checker/exports.go:241 GetJsxNamespace
    pub fn get_jsx_namespace_exported(&mut self, location: Node) -> String {
        self.get_jsx_namespace(location)
    }

    // Go: checker/exports.go:245 GetJsxFragmentFactory
    pub fn get_jsx_fragment_factory(&mut self, location: Node) -> String {
        let entity = self.get_jsx_fragment_factory_entity(location);
        if entity.is_some() {
            return get_first_identifier(entity).text().to_string();
        }
        String::new()
    }

    // Go: checker/exports.go:253 ResolveName
    // PORT: the unexported twin is the Go function field `resolveName`
    // (`fnfields.rs` `resolve_name`).
    pub fn resolve_name_exported(
        &mut self,
        name: &str,
        location: Node,
        meaning: SymbolFlags,
        exclude_globals: bool,
    ) -> SymbolId {
        self.resolve_name(location, name, meaning, None, true, exclude_globals)
    }

    // Go: checker/exports.go:257 GetSymbolFlags
    pub fn get_symbol_flags_exported(&mut self, symbol: SymbolId) -> SymbolFlags {
        self.get_symbol_flags(symbol)
    }

    // Go: checker/exports.go:261 GetBaseTypes
    pub fn get_base_types_exported(&mut self, t: TypeId) -> Vec<TypeId> {
        self.get_base_types(t)
    }

    // Go: checker/exports.go:265 GetApparentType
    pub fn get_apparent_type_exported(&mut self, t: TypeId) -> TypeId {
        self.get_apparent_type(t)
    }

    // Go: checker/exports.go:297 GetReducedType
    pub fn get_reduced_type_exported(&mut self, t: TypeId) -> TypeId {
        self.get_reduced_type(t)
    }

    // Go: checker/exports.go:299 GetFullyQualifiedName
    // GetFullyQualifiedName returns the fully qualified name of a symbol, walking up
    // its parent chain (e.g. `"/path/to/module".Namespace.Name`).
    pub fn get_fully_qualified_name_exported(&mut self, symbol: SymbolId) -> String {
        self.get_fully_qualified_name(symbol, Node::NIL /*containingLocation*/)
    }

    // Go: checker/exports.go:269 GetBaseConstructorTypeOfClass
    pub fn get_base_constructor_type_of_class_exported(&mut self, t: TypeId) -> TypeId {
        self.get_base_constructor_type_of_class(t)
    }

    // Go: checker/exports.go:307 GetMemberOverrideModifierStatus
    pub fn get_member_override_modifier_status_exported(
        &mut self,
        node: Node,
        member: Node,
        member_symbol: SymbolId,
    ) -> MemberOverrideStatus {
        self.get_member_override_modifier_status(node, member, member_symbol)
    }

    // Go: checker/exports.go:273 GetRestTypeOfSignature
    pub fn get_rest_type_of_signature_exported(&mut self, sig: SignatureId) -> TypeId {
        self.get_rest_type_of_signature(sig)
    }

    // Go: checker/exports.go:277 GetTypeArguments
    pub fn get_type_arguments_exported(&mut self, t: TypeId) -> Vec<TypeId> {
        self.get_type_arguments(t).to_vec()
    }

    // Go: checker/exports.go:281 GetIndexInfoOfType
    pub fn get_index_info_of_type_exported(&mut self, t: TypeId, key_type: TypeId) -> IndexInfoId {
        self.get_index_info_of_type(t, key_type)
    }

    // Go: checker/exports.go:285 GetIndexInfosOfType
    pub fn get_index_infos_of_type_exported(&mut self, t: TypeId) -> Vec<IndexInfoId> {
        self.get_index_infos_of_type(t).to_vec()
    }

    // Go: checker/exports.go:289 IsContextSensitive
    pub fn is_context_sensitive_exported(&mut self, node: Node) -> bool {
        self.is_context_sensitive(node)
    }

    // Go: checker/exports.go:293 FillMissingTypeArguments
    pub fn fill_missing_type_arguments_exported(
        &mut self,
        type_arguments: &[TypeId],
        type_parameters: &[TypeId],
        min_type_argument_count: i32,
        is_java_script_implicit_any: bool,
    ) -> Vec<TypeId> {
        self.fill_missing_type_arguments(
            type_arguments,
            type_parameters,
            min_type_argument_count,
            is_java_script_implicit_any,
        )
    }

    // Go: checker/exports.go:297 GetMinTypeArgumentCount
    pub fn get_min_type_argument_count_exported(&mut self, type_parameters: &[TypeId]) -> i32 {
        self.get_min_type_argument_count(type_parameters)
    }

    // Go: checker/exports.go:301 GetWidenedLiteralType
    pub fn get_widened_literal_type_exported(&mut self, t: TypeId) -> TypeId {
        self.get_widened_literal_type(t)
    }

    // Go: checker/exports.go:305 IsTypeAssignableTo
    pub fn is_type_assignable_to_exported(&mut self, source: TypeId, target: TypeId) -> bool {
        self.is_type_assignable_to(source, target)
    }

    // Go: checker/exports.go:309 GetUnionTypeEx
    pub fn get_union_type_ex_exported(
        &mut self,
        types: &[TypeId],
        union_reduction: UnionReduction,
    ) -> TypeId {
        self.get_union_type_ex(types, union_reduction, None, TypeId::NIL)
    }

    // Go: checker/exports.go:313 RequiresAddingImplicitUndefined
    // PORT: Go calls the locking `EmitResolver.RequiresAddingImplicitUndefined`,
    // which takes the resolver's `checkerMu`. Here the checker is `self`,
    // already borrowed by the caller, so the unlocked body runs:
    // `requires_adding_implicit_undefined_unsafe_worker` is the same
    // `IsParseTreeNode` test and `requiresAddingImplicitUndefined` call
    // without the lock. The locking Rust method borrows the checker from
    // the compile worker pool, which the language service thread does not use.
    pub fn requires_adding_implicit_undefined_exported(&mut self, node: Node) -> bool {
        let mut enclosing_declaration = find_ancestor(node, is_declaration);
        if enclosing_declaration.is_nil() {
            enclosing_declaration = get_source_file_of_node(node);
        }
        let symbol = node.symbol();
        if symbol.is_nil() {
            return false;
        }
        let resolver = self.get_emit_resolver();
        resolver.requires_adding_implicit_undefined_unsafe_worker(
            self,
            node,
            symbol,
            enclosing_declaration,
        )
    }

    // Go: checker/exports.go:325 RemoveMissingOrUndefinedType
    pub fn remove_missing_or_undefined_type_exported(&mut self, t: TypeId) -> TypeId {
        self.remove_missing_or_undefined_type(t)
    }

    // Go: checker/exports.go:329 GetWidenedType
    pub fn get_widened_type_exported(&mut self, t: TypeId) -> TypeId {
        self.get_widened_type(t)
    }

    // Go: checker/exports.go:353 CompareSymbols
    pub fn compare_symbols_exported(&mut self, s1: SymbolId, s2: SymbolId) -> i32 {
        self.compare_symbols(s1, s2)
    }
}
