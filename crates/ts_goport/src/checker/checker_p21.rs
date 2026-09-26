//! Port of `checker/checker.go` lines 18536-19435: optionality helpers,
//! cached node/modifier flags, the type resolution stack, property, signature
//! and index info lookup, structured member resolution, base types, and
//! signature instantiation.

use crate::prelude::*;

impl Checker {
    // Go: checker/checker.go:18536 addOptionality
    pub fn add_optionality(&mut self, t: TypeId) -> TypeId {
        self.add_optionality_ex(t, false /*isProperty*/, true /*isOptional*/)
    }

    // Go: checker/checker.go:18540 addOptionalityEx
    pub fn add_optionality_ex(
        &mut self,
        t: TypeId,
        is_property: bool,
        is_optional: bool,
    ) -> TypeId {
        if self.strict_null_checks && is_optional {
            return self.get_optional_type(t, is_property);
        }
        t
    }

    // Go: checker/checker.go:18547 getOptionalType
    pub fn get_optional_type(&mut self, t: TypeId, is_property: bool) -> TypeId {
        debug_assert!(self.strict_null_checks);
        let missing_or_undefined = if is_property {
            self.undefined_or_missing_type
        } else {
            self.undefined_type
        };
        if t == missing_or_undefined
            || self.ty(t).flags.intersects(TypeFlags::UNION)
                && self.ty(t).types()[0] == missing_or_undefined
        {
            return t;
        }
        self.get_union_type(&[t, missing_or_undefined])
    }

    // Go: checker/checker.go:18557 getNullableType
    // Add undefined or null or both to a type if they are missing.
    pub fn get_nullable_type(&mut self, t: TypeId, flags: TypeFlags) -> TypeId {
        let missing = (flags & !self.ty(t).flags) & (TypeFlags::UNDEFINED | TypeFlags::NULL);
        if missing.is_empty() {
            return t;
        } else if missing == TypeFlags::UNDEFINED {
            let undefined_type = self.undefined_type;
            return self.get_union_type(&[t, undefined_type]);
        } else if missing == TypeFlags::NULL {
            let null_type = self.null_type;
            return self.get_union_type(&[t, null_type]);
        }
        let undefined_type = self.undefined_type;
        let null_type = self.null_type;
        self.get_union_type(&[t, undefined_type, null_type])
    }

    // Go: checker/checker.go:18570 GetNonNullableType
    pub fn get_non_nullable_type(&mut self, t: TypeId) -> TypeId {
        if self.strict_null_checks {
            return self.get_adjusted_type_with_facts(t, TypeFacts::NE_UNDEFINED_OR_NULL);
        }
        t
    }

    // Go: checker/checker.go:18577 IsNullableType
    pub fn is_nullable_type(&mut self, t: TypeId) -> bool {
        self.has_type_facts(t, TypeFacts::IS_UNDEFINED_OR_NULL)
    }

    // Go: checker/checker.go:18581 getNonNullableTypeIfNeeded
    pub fn get_non_nullable_type_if_needed(&mut self, t: TypeId) -> TypeId {
        if self.is_nullable_type(t) {
            return self.get_non_nullable_type(t);
        }
        t
    }

    // Go: checker/checker.go:18588 getDeclarationNodeFlagsFromSymbol
    pub fn get_declaration_node_flags_from_symbol(&mut self, s: SymbolId) -> NodeFlags {
        let value_declaration = self.sym(s).value_declaration;
        if value_declaration.is_some() {
            return self.get_combined_node_flags_cached(value_declaration);
        }
        NodeFlags::NONE
    }

    // Go: checker/checker.go:18595 getCombinedNodeFlagsCached
    pub fn get_combined_node_flags_cached(&mut self, node: Node) -> NodeFlags {
        // we hold onto the last node and result to speed up repeated lookups against the same node.
        if self.last_get_combined_node_flags_node == node {
            return self.last_get_combined_node_flags_result;
        }
        self.last_get_combined_node_flags_node = node;
        self.last_get_combined_node_flags_result = get_combined_node_flags(node);
        self.last_get_combined_node_flags_result
    }

    // Go: checker/checker.go:18605 isVarConstLike
    pub fn is_var_const_like(&mut self, node: Node) -> bool {
        let block_scope_kind = self.get_combined_node_flags_cached(node) & NodeFlags::BLOCK_SCOPED;
        block_scope_kind == NodeFlags::CONST
            || block_scope_kind == NodeFlags::USING
            || block_scope_kind == NodeFlags::AWAIT_USING
    }

    // Go: checker/checker.go:18610 getEffectivePropertyNameForPropertyNameNode
    pub fn get_effective_property_name_for_property_name_node(
        &mut self,
        node: Node,
    ) -> (String, bool) {
        let name = get_property_name_for_property_name_node(node);
        if name != INTERNAL_SYMBOL_NAME_MISSING {
            return (name, true);
        } else if is_computed_property_name(node) {
            let t = self.get_type_of_expression(node.expression());
            return self.try_get_name_from_type(t);
        }
        (String::new(), false)
    }

    // Go: checker/checker.go:18621 tryGetNameFromType
    pub fn try_get_name_from_type(&mut self, t: TypeId) -> (String, bool) {
        let flags = self.ty(t).flags;
        if flags.intersects(TypeFlags::UNIQUE_ES_SYMBOL) {
            (self.ty(t).as_unique_es_symbol_type().name.clone(), true)
        } else if flags.intersects(TypeFlags::STRING_LITERAL) {
            let s = self.get_string_literal_value(t);
            (s, true)
        } else if flags.intersects(TypeFlags::NUMBER_LITERAL) {
            let s = self.get_number_literal_value(t).to_string();
            (s, true)
        } else {
            (String::new(), false)
        }
    }

    // Go: checker/checker.go:18636 getCombinedModifierFlagsCached
    pub fn get_combined_modifier_flags_cached(&mut self, node: Node) -> ModifierFlags {
        // we hold onto the last node and result to speed up repeated lookups against the same node.
        if self.last_get_combined_modifier_flags_node == node {
            return self.last_get_combined_modifier_flags_result;
        }
        self.last_get_combined_modifier_flags_node = node;
        self.last_get_combined_modifier_flags_result = get_combined_modifier_flags(node);
        self.last_get_combined_modifier_flags_result
    }

    // Go: checker/checker.go:18657 pushTypeResolution
    /// Push an entry on the type resolution stack. If an entry with the given target and the given property name
    /// is already on the stack, and no entries in between already have a type, then a circularity has occurred.
    /// In this case, the result values of the existing entry and all entries pushed after it are changed to false,
    /// and the value false is returned. Otherwise, the new entry is just pushed onto the stack, and true is returned.
    /// In order to see if the same query has already been done before, the target object and the propertyName both
    /// must match the one passed in.
    ///
    /// target: The symbol, type, or signature whose type is being queried
    /// property_name: The property name that should be used to query the target for its type
    pub fn push_type_resolution(
        &mut self,
        target: TypeSystemEntity,
        property_name: TypeSystemPropertyName,
    ) -> bool {
        let resolution_cycle_start_index =
            self.find_resolution_cycle_start_index(target, property_name);
        if resolution_cycle_start_index >= 0 {
            // A cycle was found
            for i in resolution_cycle_start_index as usize..self.type_resolutions.len() {
                self.type_resolutions[i].result = false;
            }
            return false;
        }
        self.type_resolutions.push(TypeResolution {
            target,
            property_name,
            result: true,
        });
        true
    }

    // Go: checker/checker.go:18674 popTypeResolution
    /// Pop an entry from the type resolution stack and return its associated result value. The result value will
    /// be true if no circularities were detected, or false if a circularity was found.
    pub fn pop_type_resolution(&mut self) -> bool {
        let last = self
            .type_resolutions
            .pop()
            .expect("popTypeResolution on empty stack");
        last.result
    }

    // Go: checker/checker.go:18682 findResolutionCycleStartIndex
    pub fn find_resolution_cycle_start_index(
        &mut self,
        target: TypeSystemEntity,
        property_name: TypeSystemPropertyName,
    ) -> i32 {
        let mut i = self.type_resolutions.len() as i32 - 1;
        while i >= self.resolution_start {
            let resolution = self.type_resolutions[i as usize];
            if self.type_resolution_has_property(&resolution) {
                return -1;
            }
            if resolution.target == target && resolution.property_name == property_name {
                return i;
            }
            i -= 1;
        }
        -1
    }

    // Go: checker/checker.go:18695 typeResolutionHasProperty
    pub fn type_resolution_has_property(&mut self, r: &TypeResolution) -> bool {
        let as_symbol = |e: TypeSystemEntity| match e {
            TypeSystemEntity::Symbol(s) => s,
            _ => panic!("interface conversion: TypeSystemEntity is not *ast.Symbol"),
        };
        let as_type = |e: TypeSystemEntity| match e {
            TypeSystemEntity::Type(t) => t,
            _ => panic!("interface conversion: TypeSystemEntity is not *Type"),
        };
        match r.property_name {
            TypeSystemPropertyName::TYPE => self
                .value_symbol_links
                .get(as_symbol(r.target))
                .resolved_type
                .is_some(),
            TypeSystemPropertyName::DECLARED_TYPE => self
                .type_alias_links
                .get(as_symbol(r.target))
                .declared_type
                .is_some(),
            TypeSystemPropertyName::RESOLVED_TYPE_ARGUMENTS => {
                // PORT: Go checks `resolvedTypeArguments != nil`. The Rust field
                // is a `SharedList`, so an empty list reads as unresolved.
                !self
                    .ty(as_type(r.target))
                    .as_type_reference()
                    .resolved_type_arguments
                    .is_empty()
            }
            TypeSystemPropertyName::RESOLVED_BASE_TYPES => {
                self.ty(as_type(r.target))
                    .as_interface_type()
                    .base_types_resolved
            }
            TypeSystemPropertyName::RESOLVED_BASE_CONSTRUCTOR_TYPE => self
                .ty(as_type(r.target))
                .as_interface_type()
                .resolved_base_constructor_type
                .is_some(),
            TypeSystemPropertyName::RESOLVED_RETURN_TYPE => match r.target {
                TypeSystemEntity::Signature(s) => self.sig(s).resolved_return_type.is_some(),
                _ => panic!("interface conversion: TypeSystemEntity is not *Signature"),
            },
            TypeSystemPropertyName::RESOLVED_BASE_CONSTRAINT => self
                .ty(as_type(r.target))
                .as_constrained_type()
                .resolved_base_constraint
                .is_some(),
            TypeSystemPropertyName::INITIALIZER_IS_UNDEFINED => match r.target {
                TypeSystemEntity::Node(n) => self
                    .node_links
                    .get(n)
                    .flags
                    .intersects(NodeCheckFlags::INITIALIZER_IS_UNDEFINED_COMPUTED),
                _ => panic!("interface conversion: TypeSystemEntity is not *ast.Node"),
            },
            TypeSystemPropertyName::WRITE_TYPE => self
                .value_symbol_links
                .get(as_symbol(r.target))
                .write_type
                .is_some(),
            TypeSystemPropertyName::ALIAS_TARGET => self
                .alias_symbol_links
                .get(as_symbol(r.target))
                .alias_target
                .is_some(),
            _ => panic!("Unhandled case in typeResolutionHasProperty"),
        }
    }

    // Go: checker/checker.go:18721 reportCircularityError
    pub fn report_circularity_error(&mut self, symbol: SymbolId) -> TypeId {
        let declaration = self.sym(symbol).value_declaration;
        // Check if variable has type annotation that circularly references the variable itself
        if declaration.is_some() {
            if declaration.type_().is_some() {
                let name = self.symbol_to_string(symbol);
                self.error(
                    declaration,
                    diag::X_0_is_referenced_directly_or_indirectly_in_its_own_type_annotation,
                    args![name],
                );
                return self.error_type;
            }
            // Check if variable has initializer that circularly references the variable itself
            if self.no_implicit_any
                && (!is_parameter_declaration(declaration) || declaration.initializer().is_some())
            {
                let name = self.symbol_to_string(symbol);
                self.error(
                    declaration,
                    diag::X_0_implicitly_has_type_any_because_it_does_not_have_a_type_annotation_and_is_referenced_directly_or_indirectly_in_its_own_initializer,
                    args![name],
                );
            }
        } else if self.sym(symbol).flags.intersects(SymbolFlags::ALIAS) {
            let node = self.get_declaration_of_alias_symbol(symbol);
            if node.is_some() {
                let name = self.symbol_to_string(symbol);
                self.error(
                    node,
                    diag::Circular_definition_of_import_alias_0,
                    args![name],
                );
            }
        }
        // Circularities could also result from parameters in function expressions that end up
        // having themselves as contextual types following type argument inference. In those cases
        // we have already reported an implicit any error so we don't report anything here.
        self.any_type
    }

    // Go: checker/checker.go:18745 getPropertiesOfType
    pub fn get_properties_of_type(&mut self, t: TypeId) -> SharedList<SymbolId> {
        let t = self.get_reduced_apparent_type(t);
        if self
            .ty(t)
            .flags
            .intersects(TypeFlags::UNION_OR_INTERSECTION)
        {
            return self.get_properties_of_union_or_intersection_type(t);
        }
        self.get_properties_of_object_type(t)
    }

    /// `get_properties_of_type(t).len()` without a copy of the list.
    pub fn get_properties_of_type_count(&mut self, t: TypeId) -> usize {
        let t = self.get_reduced_apparent_type(t);
        if self
            .ty(t)
            .flags
            .intersects(TypeFlags::UNION_OR_INTERSECTION)
        {
            self.resolve_properties_of_union_or_intersection_type(t);
            return self
                .ty(t)
                .as_union_or_intersection_type()
                .resolved_properties
                .len();
        }
        if self.ty(t).flags.intersects(TypeFlags::OBJECT) {
            return self.resolve_structured_type_members(t).properties.len();
        }
        0
    }

    // Go: checker/checker.go:18753 getPropertiesOfObjectType
    pub fn get_properties_of_object_type(&mut self, t: TypeId) -> SharedList<SymbolId> {
        if self.ty(t).flags.intersects(TypeFlags::OBJECT) {
            return self.resolve_structured_type_members(t).properties.clone();
        }
        SharedList::default()
    }

    // Go: checker/checker.go:18760 getPropertiesOfUnionOrIntersectionType
    pub fn get_properties_of_union_or_intersection_type(
        &mut self,
        t: TypeId,
    ) -> SharedList<SymbolId> {
        self.resolve_properties_of_union_or_intersection_type(t);
        self.ty(t)
            .as_union_or_intersection_type()
            .resolved_properties
            .clone()
    }

    /// The body of Go `getPropertiesOfUnionOrIntersectionType`. It stores the
    /// list in `resolved_properties`.
    fn resolve_properties_of_union_or_intersection_type(&mut self, t: TypeId) {
        // PORT: Go checks `resolvedProperties == nil`. The Rust field is a
        // `SharedList`, so an empty result is recomputed; the recomputation is
        // idempotent because the property lookups are cached.
        if self
            .ty(t)
            .as_union_or_intersection_type()
            .resolved_properties
            .is_empty()
        {
            let mut checked: FxHashSet<Name> = FxHashSet::default();
            let mut props: Vec<SymbolId> = Vec::new();
            let t_flags = self.ty(t).flags;
            for i in 0..self.ty(t).types().len() {
                let current = self.type_at(t, i);
                for prop in self.get_properties_of_type(current) {
                    let prop_name = self.sym(prop).name.clone();
                    if checked.insert(prop_name.clone()) {
                        let combined_prop = self.get_property_of_union_or_intersection_type(
                            t,
                            &prop_name,
                            t_flags.intersects(TypeFlags::INTERSECTION), /*skipObjectFunctionPropertyAugment*/
                        );
                        if combined_prop.is_some() {
                            props.push(combined_prop);
                        }
                    }
                }
                // The properties of a union type are those that are present in all constituent types, so
                // we only need to check the properties of the first type without index signature
                if t_flags.intersects(TypeFlags::UNION)
                    && self.get_index_infos_of_type(current).is_empty()
                {
                    break;
                }
            }
            self.ty_mut(t)
                .as_union_or_intersection_type_mut()
                .resolved_properties = props.into();
        }
    }

    // Go: checker/checker.go:18786 getPropertyOfType
    pub fn get_property_of_type(&mut self, t: TypeId, name: &str) -> SymbolId {
        self.get_property_of_type_ex(
            t, name, false, /*skipObjectFunctionPropertyAugment*/
            false, /*includeTypeOnlyMembers*/
        )
    }

    // Go: checker/checker.go:18798 getPropertyOfTypeEx
    /// Return the symbol for the property with the given name in the given type. Creates synthetic union properties when
    /// necessary, maps primitive types and type parameters are to their apparent types, and augments with properties from
    /// Object and Function as appropriate.
    ///
    /// t: a type to look up property from
    /// name: a name of property to look up in a given type
    pub fn get_property_of_type_ex(
        &mut self,
        t: TypeId,
        name: &str,
        skip_object_function_property_augment: bool,
        include_type_only_members: bool,
    ) -> SymbolId {
        let t = self.get_reduced_apparent_type(t);
        let flags = self.ty(t).flags;
        if flags.intersects(TypeFlags::OBJECT) {
            self.resolve_structured_type_members(t);
            let members = self.ty(t).as_structured_type().members;
            let mut symbol = self.symbols.get(members, name);
            if symbol.is_some() {
                let t_symbol = self.ty(t).symbol;
                if !include_type_only_members
                    && t_symbol.is_some()
                    && self
                        .sym(t_symbol)
                        .flags
                        .intersects(SymbolFlags::VALUE_MODULE)
                    && self
                        .module_symbol_links
                        .get(t_symbol)
                        .type_only_export_star_map
                        .get(name)
                        .is_some_and(|n| n.is_some())
                {
                    // If this is the type of a module, `resolved.members.get(name)` might have effectively skipped over
                    // an `export type * from './foo'`, leaving `symbolIsValue` unable to see that the symbol is being
                    // viewed through a type-only export.
                    return SymbolId::NIL;
                }
                if self.symbol_is_value_ex(symbol, include_type_only_members) {
                    return symbol;
                }
            }
            if skip_object_function_property_augment {
                return SymbolId::NIL;
            }
            let resolved = self.ty(t).as_structured_type();
            let call_count = resolved.call_signatures().len();
            let construct_count = resolved.construct_signatures().len();
            let function_type = if t == self.any_function_type {
                self.global_function_type
            } else if call_count != 0 {
                self.global_callable_function_type
            } else if construct_count != 0 {
                self.global_newable_function_type
            } else {
                TypeId::NIL
            };
            if function_type.is_some() {
                symbol = self.get_property_of_object_type(function_type, name);
                if symbol.is_some() {
                    return symbol;
                }
            }
            let global_object_type = self.global_object_type;
            return self.get_property_of_object_type(global_object_type, name);
        } else if flags.intersects(TypeFlags::INTERSECTION) {
            let prop = self.get_property_of_union_or_intersection_type(
                t, name, true, /*skipObjectFunctionPropertyAugment*/
            );
            if prop.is_some() {
                return prop;
            }
            if !skip_object_function_property_augment {
                return self.get_property_of_union_or_intersection_type(
                    t,
                    name,
                    skip_object_function_property_augment,
                );
            }
            return SymbolId::NIL;
        } else if flags.intersects(TypeFlags::UNION) {
            return self.get_property_of_union_or_intersection_type(
                t,
                name,
                skip_object_function_property_augment,
            );
        }
        SymbolId::NIL
    }

    // Go: checker/checker.go:18850 getTypeOfPropertyOfType
    // Return the type of the given property in the given type, or nil if no such property exists
    pub fn get_type_of_property_of_type(&mut self, t: TypeId, name: &str) -> TypeId {
        let prop = self.get_property_of_type(t, name);
        if prop.is_some() {
            return self.get_type_of_symbol(prop);
        }
        TypeId::NIL
    }

    // Go: checker/checker.go:18858 getSignaturesOfType
    pub fn get_signatures_of_type(
        &mut self,
        t: TypeId,
        kind: SignatureKind,
    ) -> SharedList<SignatureId> {
        let reduced = self.get_reduced_apparent_type(t);
        self.get_signatures_of_structured_type(reduced, kind)
    }

    // Go: checker/checker.go:18862 getSignaturesOfStructuredType
    pub fn get_signatures_of_structured_type(
        &mut self,
        t: TypeId,
        kind: SignatureKind,
    ) -> SharedList<SignatureId> {
        if !self.ty(t).flags.intersects(TypeFlags::STRUCTURED_TYPE) {
            return SharedList::default();
        }
        let resolved = self.resolve_structured_type_members(t);
        let call_count = resolved.call_signature_count as usize;
        if kind == SignatureKind::CALL {
            return resolved.signatures.slice(0..call_count);
        }
        resolved
            .signatures
            .slice(call_count..resolved.signatures.len())
    }

    /// `instantiate_signatures(&get_signatures_of_type(t, kind), m)` without a
    /// copy of the source list. Resolved members never change, so the
    /// signatures are read in place, in order.
    pub fn instantiate_signatures_of_type(
        &mut self,
        t: TypeId,
        kind: SignatureKind,
        m: MapperId,
    ) -> Vec<SignatureId> {
        let t = self.get_reduced_apparent_type(t);
        if !self.ty(t).flags.intersects(TypeFlags::STRUCTURED_TYPE) {
            return Vec::new();
        }
        let resolved = self.resolve_structured_type_members(t);
        let call_count = resolved.call_signature_count as usize;
        let range = if kind == SignatureKind::CALL {
            0..call_count
        } else {
            call_count..resolved.signatures.len()
        };
        let mut result = Vec::with_capacity(range.len());
        for i in range {
            let signature = self.ty(t).as_structured_type().signatures[i];
            result.push(self.instantiate_signature(signature, m));
        }
        result
    }

    // Go: checker/checker.go:18873 getIndexInfosOfType
    pub fn get_index_infos_of_type(&mut self, t: TypeId) -> SharedList<IndexInfoId> {
        let reduced = self.get_reduced_apparent_type(t);
        self.get_index_infos_of_structured_type(reduced)
    }

    // Go: checker/checker.go:18877 getIndexInfosOfStructuredType
    pub fn get_index_infos_of_structured_type(&mut self, t: TypeId) -> SharedList<IndexInfoId> {
        if self.ty(t).flags.intersects(TypeFlags::STRUCTURED_TYPE) {
            return self.resolve_structured_type_members(t).index_infos.clone();
        }
        SharedList::default()
    }

    // Go: checker/checker.go:18886 getIndexInfoOfType
    // Return the indexing info of the given kind in the given type. Creates synthetic union index types when necessary and
    // maps primitive types and type parameters are to their apparent types.
    pub fn get_index_info_of_type(&mut self, t: TypeId, key_type: TypeId) -> IndexInfoId {
        let index_infos = self.get_index_infos_of_type(t);
        self.find_index_info(&index_infos, key_type)
    }

    // Go: checker/checker.go:18892 getIndexTypeOfType
    // Return the index type of the given kind in the given type. Creates synthetic union index types when necessary and
    // maps primitive types and type parameters are to their apparent types.
    pub fn get_index_type_of_type(&mut self, t: TypeId, key_type: TypeId) -> TypeId {
        let info = self.get_index_info_of_type(t, key_type);
        if info.is_some() {
            return self.index_info(info).value_type;
        }
        TypeId::NIL
    }

    // Go: checker/checker.go:18900 getIndexTypeOfTypeEx
    pub fn get_index_type_of_type_ex(
        &mut self,
        t: TypeId,
        key_type: TypeId,
        default_type: TypeId,
    ) -> TypeId {
        let result = self.get_index_type_of_type(t, key_type);
        if result.is_some() {
            return result;
        }
        default_type
    }

    // Go: checker/checker.go:18907 getApplicableIndexInfo
    pub fn get_applicable_index_info(&mut self, t: TypeId, key_type: TypeId) -> IndexInfoId {
        let index_infos = self.get_index_infos_of_type(t);
        self.find_applicable_index_info(&index_infos, key_type)
    }

    // Go: checker/checker.go:18911 getApplicableIndexInfoForName
    pub fn get_applicable_index_info_for_name(&mut self, t: TypeId, name: &str) -> IndexInfoId {
        if is_late_bound_name(name) {
            let es_symbol_type = self.es_symbol_type;
            return self.get_applicable_index_info(t, es_symbol_type);
        }
        let key_type = self.get_string_literal_type(name);
        self.get_applicable_index_info(t, key_type)
    }

    // Go: checker/checker.go:18918 findApplicableIndexInfo
    pub fn find_applicable_index_info(
        &mut self,
        index_infos: &[IndexInfoId],
        key_type: TypeId,
    ) -> IndexInfoId {
        // Index signatures for type 'string' are considered only when no other index signatures apply.
        let mut string_index_info = IndexInfoId::NIL;
        let mut applicable_infos: Vec<IndexInfoId> = Vec::with_capacity(8);
        for &info in index_infos {
            let info_key_type = self.index_info(info).key_type;
            if info_key_type == self.string_type {
                string_index_info = info;
            } else if self.is_applicable_index_type(key_type, info_key_type) {
                applicable_infos.push(info);
            }
        }
        // When more than one index signature is applicable we create a synthetic IndexInfo. Instead of computing
        // the intersected key type, we just use unknownType for the key type as nothing actually depends on the
        // keyType property of the returned IndexInfo.
        match applicable_infos.len() {
            0 => {
                let string_type = self.string_type;
                if string_index_info.is_some()
                    && self.is_applicable_index_type(key_type, string_type)
                {
                    return string_index_info;
                }
                IndexInfoId::NIL
            }
            1 => applicable_infos[0],
            _ => {
                let mut is_readonly = true;
                let mut types: Vec<TypeId> = Vec::with_capacity(applicable_infos.len());
                for &info in &applicable_infos {
                    types.push(self.index_info(info).value_type);
                    if !self.index_info(info).is_readonly {
                        is_readonly = false;
                    }
                }
                let unknown_type = self.unknown_type;
                let value_type = self.get_intersection_type(&types);
                self.new_index_info(unknown_type, value_type, is_readonly, Node::NIL, &[])
            }
        }
    }

    // Go: checker/checker.go:18953 isApplicableIndexType
    pub fn is_applicable_index_type(&mut self, source: TypeId, target: TypeId) -> bool {
        // A 'string' index signature applies to types assignable to 'string' or 'number', and a 'number' index
        // signature applies to types assignable to 'number', `${number}` and numeric string literal types.
        if self.is_type_assignable_to(source, target) {
            return true;
        }
        if target == self.string_type {
            let number_type = self.number_type;
            if self.is_type_assignable_to(source, number_type) {
                return true;
            }
        }
        target == self.number_type
            && (source == self.numeric_string_type
                || self.ty(source).flags.intersects(TypeFlags::STRING_LITERAL)
                    && is_numeric_literal_name(self.get_string_literal_value_ref(source)))
    }

    // Go: checker/checker.go:18961 resolveStructuredTypeMembers
    // PORT: Go returns `*StructuredType`. Rust returns a shared borrow of the
    // resolved type's `StructuredType`; callers that need to call other
    // checker methods copy what they need out of it first.
    // PORT: the resolved case is the common one, so it stays inline and the
    // dispatch below is out of line.
    #[inline]
    pub fn resolve_structured_type_members(&mut self, t: TypeId) -> &StructuredType {
        if !self
            .ty(t)
            .object_flags
            .intersects(ObjectFlags::MEMBERS_RESOLVED)
        {
            self.resolve_structured_type_members_slow(t);
        }
        self.ty(t).as_structured_type()
    }

    /// The member resolution dispatch of `resolve_structured_type_members`.
    #[inline(never)]
    fn resolve_structured_type_members_slow(&mut self, t: TypeId) {
        let flags = self.ty(t).flags;
        let object_flags = self.ty(t).object_flags;
        if flags.intersects(TypeFlags::OBJECT) {
            if object_flags.intersects(ObjectFlags::REFERENCE) {
                self.resolve_type_reference_members(t);
            } else if object_flags.intersects(ObjectFlags::CLASS_OR_INTERFACE) {
                self.resolve_class_or_interface_members(t);
            } else if object_flags.intersects(ObjectFlags::REVERSE_MAPPED) {
                self.resolve_reverse_mapped_type_members(t);
            } else if object_flags.intersects(ObjectFlags::ANONYMOUS) {
                self.resolve_anonymous_type_members(t);
            } else if object_flags.intersects(ObjectFlags::MAPPED) {
                self.resolve_mapped_type_members(t);
            } else {
                panic!("Unhandled case in resolveStructuredTypeMembers");
            }
        } else if flags.intersects(TypeFlags::UNION) {
            self.resolve_union_type_members(t);
        } else if flags.intersects(TypeFlags::INTERSECTION) {
            self.resolve_intersection_type_members(t);
        } else {
            panic!("Unhandled case in resolveStructuredTypeMembers");
        }
    }

    // Go: checker/checker.go:18990 resolveClassOrInterfaceMembers
    pub fn resolve_class_or_interface_members(&mut self, t: TypeId) {
        self.resolve_object_type_members(t, t, &[], &[]);
    }

    // Go: checker/checker.go:18994 resolveTypeReferenceMembers
    pub fn resolve_type_reference_members(&mut self, t: TypeId) {
        let source = self.ty(t).target();
        let type_parameters = self
            .ty(source)
            .as_interface_type()
            .all_type_parameters
            .clone();
        // One allocation with room for the padding `t`.
        let mut padded_type_arguments = {
            let type_arguments = self.type_arguments_of(t);
            let mut padded = Vec::with_capacity(type_arguments.len() + 1);
            padded.extend_from_slice(&type_arguments);
            padded
        };
        if padded_type_arguments.len() == type_parameters.len().wrapping_sub(1) {
            padded_type_arguments.push(t);
        }
        self.resolve_object_type_members(t, source, &type_parameters, &padded_type_arguments);
    }

    // Go: checker/checker.go:19005 resolveObjectTypeMembers
    pub fn resolve_object_type_members(
        &mut self,
        t: TypeId,
        source: TypeId,
        type_parameters: &[TypeId],
        type_arguments: &[TypeId],
    ) {
        let mut mapper = MapperId::NIL;
        let mut members: SymbolTable;
        let mut call_signatures: Vec<SignatureId>;
        let mut construct_signatures: Vec<SignatureId>;
        let mut index_infos: Vec<IndexInfoId>;
        let mut instantiated = false;
        self.resolve_declared_members(source);
        let (
            declared_members,
            declared_call_signatures,
            declared_construct_signatures,
            declared_index_infos,
        ) = {
            let resolved = self.ty(source).as_interface_type();
            (
                resolved.declared_members,
                resolved.declared_call_signatures.clone(),
                resolved.declared_construct_signatures.clone(),
                resolved.declared_index_infos.clone(),
            )
        };
        if type_parameters == type_arguments {
            members = declared_members;
            call_signatures = declared_call_signatures;
            construct_signatures = declared_construct_signatures;
            index_infos = declared_index_infos;
        } else {
            instantiated = true;
            mapper = self.new_type_mapper(type_parameters, type_arguments);
            members = self.instantiate_symbol_table(declared_members, mapper);
            call_signatures = self.instantiate_signatures(&declared_call_signatures, mapper);
            construct_signatures =
                self.instantiate_signatures(&declared_construct_signatures, mapper);
            index_infos = self.instantiate_index_infos(&declared_index_infos, mapper);
        }
        let base_types = self.get_base_types(source);
        if !base_types.is_empty() {
            if !instantiated {
                // PORT: Go `maps.Clone(members)`; a nil map clones to nil.
                members = self.symbols.clone_table(members);
            }
            self.set_structured_type_members(
                t,
                members,
                &call_signatures,
                &construct_signatures,
                &index_infos,
            );
            let this_argument = type_arguments.last().copied().unwrap_or(TypeId::NIL);
            self.ty_mut(t).object_flags |= ObjectFlags::UNRESOLVED_MEMBERS;
            for base_type in base_types {
                let mut instantiated_base_type = base_type;
                if this_argument.is_some() {
                    let instantiated_type = self.instantiate_type(base_type, mapper);
                    instantiated_base_type = self.get_type_with_this_argument(
                        instantiated_type,
                        this_argument,
                        false, /*needsApparentType*/
                    );
                }
                let base_properties = self.get_properties_of_type(instantiated_base_type);
                members = self.add_inherited_members(members, &base_properties);
                call_signatures.extend(
                    self.get_signatures_of_type(instantiated_base_type, SignatureKind::CALL),
                );
                construct_signatures.extend(
                    self.get_signatures_of_type(instantiated_base_type, SignatureKind::CONSTRUCT),
                );
                let inherited_index_infos: Vec<IndexInfoId> =
                    if instantiated_base_type != self.any_type {
                        self.get_index_infos_of_type(instantiated_base_type)
                            .to_vec()
                    } else {
                        vec![self.any_base_type_index_info]
                    };
                let filtered: Vec<IndexInfoId> = inherited_index_infos
                    .into_iter()
                    .filter(|&info| {
                        let key_type = self.index_info(info).key_type;
                        self.find_index_info(&index_infos, key_type).is_nil()
                    })
                    .collect();
                index_infos.extend(filtered);
            }
            {
                let object_flags = self
                    .ty(t)
                    .object_flags
                    .without(ObjectFlags::UNRESOLVED_MEMBERS);
                self.ty_mut(t).object_flags = object_flags;
            }
        }
        self.set_structured_type_members(
            t,
            members,
            &call_signatures,
            &construct_signatures,
            &index_infos,
        );
    }
}

// Go: checker/checker.go:19057 findIndexInfo
// PORT: package-level Go function that reads index info data, so it is a
// `Checker` method (`&self`).
impl Checker {
    pub fn find_index_info(&self, index_infos: &[IndexInfoId], key_type: TypeId) -> IndexInfoId {
        for &info in index_infos {
            if self.index_info(info).key_type == key_type {
                return info;
            }
        }
        IndexInfoId::NIL
    }

    // Go: checker/checker.go:19066 getBaseTypes
    pub fn get_base_types(&mut self, t: TypeId) -> Vec<TypeId> {
        if !self
            .ty(t)
            .object_flags
            .intersects(ObjectFlags::CLASS_OR_INTERFACE | ObjectFlags::REFERENCE)
        {
            return Vec::new();
        }
        if !self.ty(t).as_interface_type().base_types_resolved {
            if !self.push_type_resolution(
                TypeSystemEntity::Type(t),
                TypeSystemPropertyName::RESOLVED_BASE_TYPES,
            ) {
                return self.ty(t).as_interface_type().resolved_base_types.clone();
            }
            let t_symbol = self.ty(t).symbol;
            if self.ty(t).object_flags.intersects(ObjectFlags::TUPLE) {
                let base = self.get_tuple_base_type(t);
                self.ty_mut(t).as_interface_type_mut().resolved_base_types = vec![base];
            } else if self
                .sym(t_symbol)
                .flags
                .intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE)
            {
                if self.sym(t_symbol).flags.intersects(SymbolFlags::CLASS) {
                    self.resolve_base_types_of_class(t);
                }
                if self.sym(t_symbol).flags.intersects(SymbolFlags::INTERFACE) {
                    self.resolve_base_types_of_interface(t);
                }
            } else {
                panic!("Unhandled case in getBaseTypes");
            }
            // PORT: Go checks `t.symbol.Declarations != nil`; an empty list
            // has nothing to report either way.
            if !self.pop_type_resolution()
                && t_symbol.is_some()
                && !self.sym(t_symbol).declarations.is_empty()
            {
                let declarations = self.sym(t_symbol).declarations.clone();
                for &declaration in declarations.iter() {
                    if is_class_declaration(declaration) || is_interface_declaration(declaration) {
                        self.report_circular_base_type(declaration, t);
                    }
                }
            }
            // In general, base type resolution always precedes member resolution. However, it is possible
            // for resolution of type parameter defaults to cause circularity errors, possibly leaving
            // members partially resolved. Here we ensure any such partial resolution is reset.
            // See https://github.com/microsoft/TypeScript/issues/16861 for an example.
            {
                let object_flags = self
                    .ty(t)
                    .object_flags
                    .without(ObjectFlags::MEMBERS_RESOLVED);
                self.ty_mut(t).object_flags = object_flags;
            }
            self.ty_mut(t).as_interface_type_mut().base_types_resolved = true;
        }
        self.ty(t).as_interface_type().resolved_base_types.clone()
    }

    // Go: checker/checker.go:19105 getTupleBaseType
    pub fn get_tuple_base_type(&mut self, t: TypeId) -> TypeId {
        let type_parameters = self.ty(t).as_interface_type().type_parameters().to_vec();
        let element_flags: Vec<ElementFlags> = self
            .ty(t)
            .as_tuple_type()
            .element_infos
            .iter()
            .map(|info| info.flags)
            .collect();
        let mut element_types: Vec<TypeId> = Vec::with_capacity(type_parameters.len());
        for (i, &tp) in type_parameters.iter().enumerate() {
            if element_flags[i].intersects(ElementFlags::VARIADIC) {
                let number_type = self.number_type;
                element_types.push(self.get_indexed_access_type(tp, number_type));
            } else {
                element_types.push(tp);
            }
        }
        let readonly = self.ty(t).as_tuple_type().readonly;
        let element_type = self.get_union_type(&element_types);
        self.create_array_type_ex(element_type, readonly)
    }

    // Go: checker/checker.go:19119 resolveBaseTypesOfClass
    pub fn resolve_base_types_of_class(&mut self, t: TypeId) {
        let base_constructor_type_of_class = self.get_base_constructor_type_of_class(t);
        let base_constructor_type = self.get_apparent_type(base_constructor_type_of_class);
        if !self
            .ty(base_constructor_type)
            .flags
            .intersects(TypeFlags::OBJECT | TypeFlags::INTERSECTION | TypeFlags::ANY)
        {
            return;
        }
        let base_type_node = self.get_base_type_node_of_class(t);
        let base_type: TypeId;
        let mut original_base_type = TypeId::NIL;
        let base_constructor_symbol = self.ty(base_constructor_type).symbol;
        if base_constructor_symbol.is_some() {
            original_base_type = self.get_declared_type_of_symbol(base_constructor_symbol);
        }
        if base_constructor_symbol.is_some()
            && self
                .sym(base_constructor_symbol)
                .flags
                .intersects(SymbolFlags::CLASS)
            && self.are_all_outer_type_parameters_applied(original_base_type)
        {
            // When base constructor type is a class with no captured type arguments we know that the constructors all have the same type parameters as the
            // class and all return the instance type of the class. There is no need for further checks and we can apply the
            // type arguments in the same manner as a type reference to get the same error reporting experience.
            base_type = self.get_type_from_class_or_interface_reference(
                base_type_node,
                base_constructor_symbol,
            );
        } else if self
            .ty(base_constructor_type)
            .flags
            .intersects(TypeFlags::ANY)
        {
            base_type = base_constructor_type;
        } else {
            // The class derives from a "class-like" constructor function, check that we have at least one construct signature
            // with a matching number of type parameters and use the return type of the first instantiated signature. Elsewhere
            // we check that all instantiated signatures return the same type.
            let type_argument_nodes = base_type_node.type_arguments().to_vec();
            let constructors = self.get_instantiated_constructors_for_type_arguments(
                base_constructor_type,
                &type_argument_nodes,
                base_type_node,
            );
            if constructors.is_empty() {
                self.error(
                    base_type_node.expression(),
                    diag::No_base_constructor_has_the_specified_number_of_type_arguments,
                    args![],
                );
                return;
            }
            base_type = self.get_return_type_of_signature(constructors[0]);
        }
        if self.is_error_type(base_type) {
            return;
        }
        let reduced_base_type = self.get_reduced_type(base_type);
        if !self.is_valid_base_type(reduced_base_type) {
            let error_node = base_type_node.expression();
            let diagnostic = self.elaborate_never_intersection(None, error_node, base_type);
            let type_string = self.type_to_string_exported(reduced_base_type);
            let diagnostic = new_diagnostic_chain_for_node(
                diagnostic,
                error_node,
                diag::Base_constructor_return_type_0_is_not_an_object_type_or_intersection_of_object_types_with_statically_known_members,
                args![type_string],
            );
            self.add_diagnostic(diagnostic);
            return;
        }
        if t == reduced_base_type || self.has_base_type(reduced_base_type, t) {
            let value_declaration = self.sym(self.ty(t).symbol).value_declaration;
            let type_string = self.type_to_string_exported(t);
            self.error(
                value_declaration,
                diag::Type_0_recursively_references_itself_as_a_base_type,
                args![type_string],
            );
            return;
        }
        self.ty_mut(t).as_interface_type_mut().resolved_base_types = vec![reduced_base_type];
    }

    // Go: checker/checker.go:19166 getBaseTypeNodeOfClass
    // PORT: package-level Go function that reads type data, so it is a
    // `Checker` method.
    pub fn get_base_type_node_of_class(&self, t: TypeId) -> Node {
        let decl = get_class_like_declaration_of_symbol(&self.symbols, self.ty(t).symbol);
        if decl.is_some() {
            return get_extends_heritage_clause_element(decl);
        }
        Node::NIL
    }

    // Go: checker/checker.go:19174 getInstantiatedConstructorsForTypeArguments
    pub fn get_instantiated_constructors_for_type_arguments(
        &mut self,
        t: TypeId,
        type_argument_nodes: &[Node],
        location: Node,
    ) -> Vec<SignatureId> {
        let signatures = self.get_constructors_for_type_arguments(t, type_argument_nodes, location);
        let type_arguments: Vec<TypeId> = type_argument_nodes
            .iter()
            .map(|&n| self.get_type_from_type_node(n))
            .collect();
        let mut result = Vec::with_capacity(signatures.len());
        for sig in signatures {
            if !self.sig(sig).type_parameters.is_empty() {
                result.push(self.get_signature_instantiation(
                    sig,
                    &type_arguments,
                    is_in_js_file(location),
                    &[],
                    0,
                ));
            } else {
                result.push(sig);
            }
        }
        result
    }

    // Go: checker/checker.go:19185 getConstructorsForTypeArguments
    pub fn get_constructors_for_type_arguments(
        &mut self,
        t: TypeId,
        type_argument_nodes: &[Node],
        location: Node,
    ) -> Vec<SignatureId> {
        let type_arg_count = type_argument_nodes.len() as i32;
        let signatures = self.get_signatures_of_type(t, SignatureKind::CONSTRUCT);
        let mut result = Vec::new();
        for sig in signatures {
            let type_parameters = self.sig(sig).type_parameters.clone();
            if type_arg_count >= self.get_min_type_argument_count(&type_parameters)
                && type_arg_count <= type_parameters.len() as i32
            {
                result.push(sig);
            }
        }
        result
    }

    // Go: checker/checker.go:19192 getSignatureInstantiation
    pub fn get_signature_instantiation(
        &mut self,
        sig: SignatureId,
        type_arguments: &[TypeId],
        is_java_script: bool,
        inferred_type_parameters: &[TypeId],
        // PORT: slice identity of `inferred_type_parameters`
        // (`InferenceContext::inferred_type_parameters_origin`; 0 when empty).
        inferred_type_parameters_origin: u32,
    ) -> SignatureId {
        let type_parameters = self.sig(sig).type_parameters.clone();
        let min_type_argument_count = self.get_min_type_argument_count(&type_parameters);
        let filled = self.fill_missing_type_arguments(
            type_arguments,
            &type_parameters,
            min_type_argument_count,
            is_java_script,
        );
        let instantiated_signature =
            self.get_signature_instantiation_without_filling_in_type_arguments(sig, &filled);
        if !inferred_type_parameters.is_empty() {
            let return_type = self.get_return_type_of_signature(instantiated_signature);
            let return_signature = self.get_single_call_or_construct_signature(return_type);
            if return_signature.is_some() {
                let new_return_signature = self.clone_signature(return_signature);
                let r = self.sig_mut(new_return_signature);
                r.type_parameters = inferred_type_parameters.to_vec();
                r.type_parameters_origin = inferred_type_parameters_origin;
                let new_return_type = self.get_or_create_type_from_signature(new_return_signature);
                let instantiated_mapper = self.sig(instantiated_signature).mapper;
                self.ty_mut(new_return_type).as_object_type_mut().mapper = instantiated_mapper;
                let new_instantiated_signature = self.clone_signature(instantiated_signature);
                self.sig_mut(new_instantiated_signature)
                    .resolved_return_type = new_return_type;
                return new_instantiated_signature;
            }
        }
        instantiated_signature
    }

    // Go: checker/checker.go:19209 cloneSignature
    pub fn clone_signature(&mut self, sig: SignatureId) -> SignatureId {
        let s = self.sig(sig);
        let flags = s.flags & SignatureFlags::PROPAGATING_FLAGS;
        let declaration = s.declaration;
        let type_parameters = s.type_parameters.clone();
        let this_parameter = s.this_parameter;
        let parameters = s.parameters.clone();
        let min_argument_count = s.min_argument_count;
        let target = s.target;
        let mapper = s.mapper;
        let composite = s.composite.clone();
        let result = self.new_signature(
            flags,
            declaration,
            &type_parameters,
            this_parameter,
            &parameters,
            TypeId::NIL,
            TypePredicateId::NIL,
            min_argument_count,
        );
        // Go shares the type parameter slice with the clone.
        let origin = self.share_type_parameters_origin(sig);
        let r = self.sig_mut(result);
        r.target = target;
        r.mapper = mapper;
        r.composite = composite;
        r.type_parameters_origin = origin;
        result
    }

    // Go: checker/checker.go:19217 getSignatureInstantiationWithoutFillingInTypeArguments
    pub fn get_signature_instantiation_without_filling_in_type_arguments(
        &mut self,
        sig: SignatureId,
        type_arguments: &[TypeId],
    ) -> SignatureId {
        let key = CachedSignatureKey {
            sig,
            key: get_type_list_key(type_arguments),
        };
        let mut instantiation = self
            .cached_signatures
            .get(&key)
            .copied()
            .unwrap_or_default();
        if instantiation.is_nil() {
            instantiation = self.create_signature_instantiation(sig, type_arguments);
            self.cached_signatures.insert(key, instantiation);
        }
        instantiation
    }

    // Go: checker/checker.go:19227 createSignatureInstantiation
    pub fn create_signature_instantiation(
        &mut self,
        sig: SignatureId,
        type_arguments: &[TypeId],
    ) -> SignatureId {
        let mapper = self.create_signature_type_mapper(sig, type_arguments);
        self.instantiate_signature_ex(sig, mapper, true /*eraseTypeParameters*/)
    }

    // Go: checker/checker.go:19231 createSignatureTypeMapper
    pub fn create_signature_type_mapper(
        &mut self,
        sig: SignatureId,
        type_arguments: &[TypeId],
    ) -> MapperId {
        let type_parameters = self.get_type_parameters_for_mapper(sig);
        self.new_type_mapper(&type_parameters, type_arguments)
    }

    // Go: checker/checker.go:19235 getTypeParametersForMapper
    pub fn get_type_parameters_for_mapper(&mut self, sig: SignatureId) -> Vec<TypeId> {
        let type_parameters = self.sig(sig).type_parameters.clone();
        let mut result = Vec::with_capacity(type_parameters.len());
        for tp in type_parameters {
            let mapper = self.ty(tp).mapper();
            result.push(self.instantiate_type(tp, mapper));
        }
        result
    }

    // Go: checker/checker.go:19240 getSingleCallSignature
    // If type has a single call signature and no other members, return that signature. Otherwise, return nil.
    pub fn get_single_call_signature(&mut self, t: TypeId) -> SignatureId {
        self.get_single_signature(t, SignatureKind::CALL, false /*allowMembers*/)
    }

    // Go: checker/checker.go:19244 getSingleCallOrConstructSignature
    pub fn get_single_call_or_construct_signature(&mut self, t: TypeId) -> SignatureId {
        let call_sig =
            self.get_single_signature(t, SignatureKind::CALL, false /*allowMembers*/);
        if call_sig.is_some() {
            return call_sig;
        }
        self.get_single_signature(t, SignatureKind::CONSTRUCT, false /*allowMembers*/)
    }

    // Go: checker/checker.go:19252 getSingleSignature
    pub fn get_single_signature(
        &mut self,
        t: TypeId,
        kind: SignatureKind,
        allow_members: bool,
    ) -> SignatureId {
        if self.ty(t).flags.intersects(TypeFlags::OBJECT) {
            let resolved = self.resolve_structured_type_members(t);
            if allow_members || resolved.properties.is_empty() && resolved.index_infos.is_empty() {
                if kind == SignatureKind::CALL
                    && resolved.call_signatures().len() == 1
                    && resolved.construct_signatures().is_empty()
                {
                    return resolved.call_signatures()[0];
                }
                if kind == SignatureKind::CONSTRUCT
                    && resolved.construct_signatures().len() == 1
                    && resolved.call_signatures().is_empty()
                {
                    return resolved.construct_signatures()[0];
                }
            }
        }
        SignatureId::NIL
    }

    // Go: checker/checker.go:19267 getOrCreateTypeFromSignature
    pub fn get_or_create_type_from_signature(&mut self, sig: SignatureId) -> TypeId {
        // There are two ways to declare a construct signature, one is by declaring a class constructor
        // using the constructor keyword, and the other is declaring a bare construct signature in an
        // object type literal or interface (using the new keyword). Each way of declaring a constructor
        // will result in a different declaration kind.
        if self.sig(sig).isolated_signature_type.is_nil() {
            let declaration = self.sig(sig).declaration;
            let kind = if declaration.is_some() {
                declaration.kind()
            } else {
                SyntaxKind::Unknown
            };
            // If declaration is undefined, it is likely to be the signature of the default constructor.
            let is_constructor = kind == SyntaxKind::Unknown
                || kind == SyntaxKind::Constructor
                || kind == SyntaxKind::ConstructSignature
                || kind == SyntaxKind::ConstructorType;

            let symbol = if declaration.is_some() {
                declaration.symbol()
            } else {
                SymbolId::NIL
            };
            let t = self.new_object_type(
                ObjectFlags::ANONYMOUS | ObjectFlags::SINGLE_SIGNATURE_TYPE,
                symbol,
            );
            if is_constructor {
                self.set_structured_type_members(t, SymbolTable::NIL, &[], &[sig], &[]);
            } else {
                self.set_structured_type_members(t, SymbolTable::NIL, &[sig], &[], &[]);
            }
            self.sig_mut(sig).isolated_signature_type = t;
        }
        self.sig(sig).isolated_signature_type
    }

    // Go: checker/checker.go:19295 getErasedSignature
    pub fn get_erased_signature(&mut self, signature: SignatureId) -> SignatureId {
        if self.sig(signature).type_parameters.is_empty() {
            return signature;
        }
        let key = CachedSignatureKey {
            sig: signature,
            key: *SIGNATURE_KEY_ERASED,
        };
        let mut erased = self
            .cached_signatures
            .get(&key)
            .copied()
            .unwrap_or_default();
        if erased.is_nil() {
            let type_parameters = self.sig(signature).type_parameters.clone();
            let any_type = self.any_type;
            let mapper = self.new_array_to_single_type_mapper(&type_parameters, any_type);
            erased =
                self.instantiate_signature_ex(signature, mapper, true /*eraseTypeParameters*/);
            self.cached_signatures.insert(key, erased);
        }
        erased
    }

    // Go: checker/checker.go:19308 getCanonicalSignature
    pub fn get_canonical_signature(&mut self, signature: SignatureId) -> SignatureId {
        if self.sig(signature).type_parameters.is_empty() {
            return signature;
        }
        let key = CachedSignatureKey {
            sig: signature,
            key: *SIGNATURE_KEY_CANONICAL,
        };
        let mut canonical = self
            .cached_signatures
            .get(&key)
            .copied()
            .unwrap_or_default();
        if canonical.is_nil() {
            canonical = self.create_canonical_signature(signature);
            self.cached_signatures.insert(key, canonical);
        }
        canonical
    }

    // Go: checker/checker.go:19321 createCanonicalSignature
    pub fn create_canonical_signature(&mut self, signature: SignatureId) -> SignatureId {
        // Create an instantiation of the signature where each unconstrained type parameter is replaced with
        // its original. When a generic class or interface is instantiated, each generic method in the class or
        // interface is instantiated with a fresh set of cloned type parameters (which we need to handle scenarios
        // where different generations of the same type parameter are in scope). This leads to a lot of new type
        // identities, and potentially a lot of work comparing those identities, so here we create an instantiation
        // that uses the original type identities for all unconstrained type parameters.
        let type_parameters = self.sig(signature).type_parameters.clone();
        let mut type_arguments = Vec::with_capacity(type_parameters.len());
        for tp in type_parameters {
            let target = self.ty(tp).target();
            if target.is_some() && self.get_constraint_of_type_parameter(target).is_nil() {
                type_arguments.push(target);
            } else {
                type_arguments.push(tp);
            }
        }
        let declaration = self.sig(signature).declaration;
        self.get_signature_instantiation(
            signature,
            &type_arguments,
            is_in_js_file(declaration),
            &[], /*inferredTypeParameters*/
            0,
        )
    }

    // Go: checker/checker.go:19337 getBaseSignature
    pub fn get_base_signature(&mut self, signature: SignatureId) -> SignatureId {
        let type_parameters = self.sig(signature).type_parameters.clone();
        if type_parameters.is_empty() {
            return signature;
        }
        let key = CachedSignatureKey {
            sig: signature,
            key: *SIGNATURE_KEY_BASE,
        };
        if let Some(&cached) = self.cached_signatures.get(&key) {
            if cached.is_some() {
                return cached;
            }
        }
        let mut constraints = Vec::with_capacity(type_parameters.len());
        for &tp in &type_parameters {
            let constraint = self.get_constraint_of_type_parameter(tp);
            constraints.push(if constraint.is_some() {
                constraint
            } else {
                self.unknown_type
            });
        }
        let base_constraint_mapper = self.new_type_mapper(&type_parameters, &constraints);
        let mut base_constraints = Vec::with_capacity(type_parameters.len());
        for &tp in &type_parameters {
            base_constraints.push(self.instantiate_type(tp, base_constraint_mapper));
        }
        // Run the immediate constraint mapper N-1 times so non-circular interdependent type parameters
        // resolve to their external dependencies without adding an extra expansion step for self-recursive constraints.
        for _ in 0..type_parameters.len() - 1 {
            base_constraints = self.instantiate_types(&base_constraints, base_constraint_mapper);
        }
        // and then apply a type eraser to remove any remaining circularly dependent type parameters
        let any_type = self.any_type;
        let eraser = self.new_array_to_single_type_mapper(&type_parameters, any_type);
        base_constraints = self.instantiate_types(&base_constraints, eraser);
        let mapper = self.new_type_mapper(&type_parameters, &base_constraints);
        let result =
            self.instantiate_signature_ex(signature, mapper, true /*eraseTypeParameters*/);
        self.cached_signatures.insert(key, result);
        result
    }

    // Go: checker/checker.go:19365 instantiateSignatureInContextOf
    // Instantiate a generic signature in the context of a non-generic signature (section 3.8.5 in TypeScript spec)
    pub fn instantiate_signature_in_context_of(
        &mut self,
        signature: SignatureId,
        contextual_signature: SignatureId,
        inference_context: InferenceContextId,
        compare_types: Option<TypeComparer>,
    ) -> SignatureId {
        let type_parameters = self.get_type_parameters_for_mapper(signature);
        let context = self.new_inference_context(
            &type_parameters,
            signature,
            InferenceFlags::NONE,
            compare_types,
        );
        // We clone the inferenceContext to avoid fixing. For example, when the source signature is <T>(x: T) => T[] and
        // the contextual signature is (...args: A) => B, we want to infer the element type of A's constraint (say 'any')
        // for T but leave it possible to later infer '[any]' back to A.
        let rest_type = self.get_effective_rest_type(contextual_signature);
        let mut mapper = MapperId::NIL;
        if inference_context.is_some() {
            if rest_type.is_some()
                && self
                    .ty(rest_type)
                    .flags
                    .intersects(TypeFlags::TYPE_PARAMETER)
            {
                mapper = self.inference_context(inference_context).non_fixing_mapper;
            } else {
                mapper = self.inference_context(inference_context).mapper;
            }
        }
        let source_signature = if mapper.is_some() {
            self.instantiate_signature(contextual_signature, mapper)
        } else {
            contextual_signature
        };
        self.apply_to_parameter_types(
            source_signature,
            signature,
            &mut |c: &mut Checker, source: TypeId, target: TypeId| {
                // Type parameters from outer context referenced by source type are fixed by instantiation of the source type
                c.infer_types(context, source, target, InferencePriority::NONE, false);
            },
        );
        if inference_context.is_nil() {
            self.apply_to_return_types(
                contextual_signature,
                signature,
                &mut |c: &mut Checker, source: TypeId, target: TypeId| {
                    c.infer_types(
                        context,
                        source,
                        target,
                        InferencePriority::RETURN_TYPE,
                        false,
                    );
                },
            );
        }
        let inferred_types = self.get_inferred_types(context);
        let declaration = self.sig(contextual_signature).declaration;
        self.get_signature_instantiation(
            signature,
            &inferred_types,
            is_in_js_file(declaration),
            &[], /*inferredTypeParameters*/
            0,
        )
    }

    // Go: checker/checker.go:19397 resolveBaseTypesOfInterface
    pub fn resolve_base_types_of_interface(&mut self, t: TypeId) {
        let declarations = self.sym(self.ty(t).symbol).declarations.clone();
        for &declaration in declarations.iter() {
            if is_interface_declaration(declaration) {
                for node in get_extends_heritage_clause_elements(declaration) {
                    let type_from_node = self.get_type_from_type_node(node);
                    let base_type = self.get_reduced_type(type_from_node);
                    if !self.is_error_type(base_type) {
                        if self.is_valid_base_type(base_type) {
                            if t != base_type && !self.has_base_type(base_type, t) {
                                self.ty_mut(t)
                                    .as_interface_type_mut()
                                    .resolved_base_types
                                    .push(base_type);
                            } else {
                                self.report_circular_base_type(declaration, t);
                            }
                        } else {
                            self.error(
                                node,
                                diag::An_interface_can_only_extend_an_object_type_or_intersection_of_object_types_with_statically_known_members,
                                args![],
                            );
                        }
                    }
                }
            }
        }
    }

    // Go: checker/checker.go:19419 areAllOuterTypeParametersApplied
    pub fn are_all_outer_type_parameters_applied(&mut self, t: TypeId) -> bool {
        // An unapplied type parameter has its symbol still the same as the matching argument symbol.
        // Since parameters are applied outer-to-inner, only the last outer parameter needs to be checked.
        let outer_type_parameters = self
            .ty(t)
            .as_interface_type()
            .outer_type_parameters()
            .to_vec();
        if !outer_type_parameters.is_empty() {
            let last = outer_type_parameters.len() - 1;
            let last_type_argument = self.type_arguments_of(t)[last];
            return self.ty(outer_type_parameters[last]).symbol
                != self.ty(last_type_argument).symbol;
        }
        true
    }

    // Go: checker/checker.go:19431 reportCircularBaseType
    pub fn report_circular_base_type(&mut self, node: Node, t: TypeId) {
        let type_string = self.type_to_string_ex(
            t,
            Node::NIL,
            TypeFormatFlags::WRITE_ARRAY_AS_GENERIC_TYPE,
            None,
        );
        self.error(
            node,
            diag::Type_0_recursively_references_itself_as_a_base_type,
            args![type_string],
        );
    }
}
