//! Port of `checker/mapper.go`.
//!
//! Go `*TypeMapper` is a `MapperId` into `Checker::mappers`. The Go
//! `TypeMapperData` interface implementations become variants of the
//! `TypeMapper` enum. Go `m.Map(t)` is `self.mapper_map(m, t)`.

use crate::prelude::*;

// TypeMapperKind

// Go: checker/mapper.go:11 TypeMapperKind
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(i32)]
pub enum TypeMapperKind {
    #[default]
    Unknown = 0,
    Simple = 1,
    Array = 2,
    Merged = 3,
}

// TypeMapper

/// Go `func() *Type` stored in a `DeferredTypeMapper`.
pub type DeferredTypeFn = Rc<dyn Fn(&mut Checker) -> TypeId>;

/// Go `func(*Type) *Type` stored in a `FunctionTypeMapper`.
pub type TypeMapperFn = Rc<dyn Fn(&mut Checker, TypeId) -> TypeId>;

/// Go `TypeMapper` with its `TypeMapperData`. One variant per Go mapper
/// struct. `Base` is Go `TypeMapperBase` (also the arena dummy entry).
#[derive(Clone)]
pub enum TypeMapper {
    Base(TypeMapperBase),
    Simple(SimpleTypeMapper),
    Array(ArrayTypeMapper),
    ArrayToSingle(ArrayToSingleTypeMapper),
    Deferred(DeferredTypeMapper),
    Function(FunctionTypeMapper),
    Merged(MergedTypeMapper),
    Composite(CompositeTypeMapper),
    Inference(InferenceTypeMapper),
}

impl Default for TypeMapper {
    fn default() -> Self {
        TypeMapper::Base(TypeMapperBase)
    }
}

impl std::fmt::Debug for TypeMapper {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeMapper::Base(_) => f.write_str("TypeMapperBase"),
            TypeMapper::Simple(m) => f
                .debug_struct("SimpleTypeMapper")
                .field("source", &m.source)
                .field("target", &m.target)
                .finish(),
            TypeMapper::Array(m) => f
                .debug_struct("ArrayTypeMapper")
                .field("sources", &m.sources)
                .field("targets", &m.targets)
                .finish(),
            TypeMapper::ArrayToSingle(m) => f
                .debug_struct("ArrayToSingleTypeMapper")
                .field("sources", &m.sources)
                .field("target", &m.target)
                .finish(),
            TypeMapper::Deferred(m) => f
                .debug_struct("DeferredTypeMapper")
                .field("sources", &m.sources)
                .finish(),
            TypeMapper::Function(_) => f.write_str("FunctionTypeMapper"),
            TypeMapper::Merged(m) => f
                .debug_struct("MergedTypeMapper")
                .field("m1", &m.m1)
                .field("m2", &m.m2)
                .finish(),
            TypeMapper::Composite(m) => f
                .debug_struct("CompositeTypeMapper")
                .field("m1", &m.m1)
                .field("m2", &m.m2)
                .finish(),
            TypeMapper::Inference(m) => f
                .debug_struct("InferenceTypeMapper")
                .field("n", &m.n)
                .field("fixing", &m.fixing)
                .finish(),
        }
    }
}

impl TypeMapper {
    // Go: checker/mapper.go:28 (*TypeMapper).Kind
    #[must_use]
    pub fn kind(&self) -> TypeMapperKind {
        match self {
            TypeMapper::Simple(_) => TypeMapperKind::Simple,
            TypeMapper::Array(_) => TypeMapperKind::Array,
            TypeMapper::Merged(_) => TypeMapperKind::Merged,
            // Go: TypeMapperBase.Kind for every other mapper.
            TypeMapper::Base(_)
            | TypeMapper::ArrayToSingle(_)
            | TypeMapper::Deferred(_)
            | TypeMapper::Function(_)
            | TypeMapper::Composite(_)
            | TypeMapper::Inference(_) => TypeMapperKind::Unknown,
        }
    }

    // Go: checker/mapper.go:29 (*TypeMapper).MapsThisOnly
    // PORT: Go calls isThisTypeParameter(source) here. That reads the type
    // arena, which a `TypeMapper` cannot reach, so the constructors compute
    // it once and store it. A type's isThisType is set right after the type
    // is created, before any mapper can reference it, so the value matches.
    #[must_use]
    pub fn maps_this_only(&self) -> bool {
        match self {
            TypeMapper::Simple(m) => m.maps_this_only,
            TypeMapper::Array(m) => m.maps_this_only,
            TypeMapper::ArrayToSingle(m) => m.maps_this_only,
            TypeMapper::Deferred(m) => m.maps_this_only,
            // Go: TypeMapperBase.MapsThisOnly for every other mapper.
            TypeMapper::Base(_)
            | TypeMapper::Function(_)
            | TypeMapper::Merged(_)
            | TypeMapper::Composite(_)
            | TypeMapper::Inference(_) => false,
        }
    }

    /// Go `m.data.(*SimpleTypeMapper)`. Panics on other kinds, like Go.
    #[must_use]
    pub fn as_simple_type_mapper(&self) -> &SimpleTypeMapper {
        match self {
            TypeMapper::Simple(m) => m,
            _ => panic!("interface conversion: not a *SimpleTypeMapper"),
        }
    }

    /// Go `m.data.(*ArrayTypeMapper)`. Panics on other kinds, like Go.
    #[must_use]
    pub fn as_array_type_mapper(&self) -> &ArrayTypeMapper {
        match self {
            TypeMapper::Array(m) => m,
            _ => panic!("interface conversion: not a *ArrayTypeMapper"),
        }
    }

    /// Go `m.data.(*MergedTypeMapper)`. Panics on other kinds, like Go.
    #[must_use]
    pub fn as_merged_type_mapper(&self) -> &MergedTypeMapper {
        match self {
            TypeMapper::Merged(m) => m,
            _ => panic!("interface conversion: not a *MergedTypeMapper"),
        }
    }
}

// TypeMapperBase

// Go: checker/mapper.go:102 TypeMapperBase
#[derive(Clone, Copy, Debug, Default)]
pub struct TypeMapperBase;

// SimpleTypeMapper

// Go: checker/mapper.go:112 SimpleTypeMapper
#[derive(Clone, Debug, Default)]
pub struct SimpleTypeMapper {
    pub source: TypeId,
    pub target: TypeId,
    /// Cached Go `isThisTypeParameter(m.source)`.
    pub maps_this_only: bool,
}

// ArrayTypeMapper

// Go: checker/mapper.go:143 ArrayTypeMapper
#[derive(Clone, Debug, Default)]
pub struct ArrayTypeMapper {
    pub sources: SharedList<TypeId>,
    pub targets: SharedList<TypeId>,
    /// Cached Go `len(m.sources) == 1 && isThisTypeParameter(m.sources[0])`.
    pub maps_this_only: bool,
}

// ArrayToSingleTypeMapper

// Go: checker/mapper.go:176 ArrayToSingleTypeMapper
#[derive(Clone, Debug, Default)]
pub struct ArrayToSingleTypeMapper {
    pub sources: Vec<TypeId>,
    pub target: TypeId,
    /// Cached Go `len(m.sources) == 1 && isThisTypeParameter(m.sources[0])`.
    pub maps_this_only: bool,
}

// DeferredTypeMapper

// Go: checker/mapper.go:203 DeferredTypeMapper
#[derive(Clone)]
pub struct DeferredTypeMapper {
    pub sources: Vec<TypeId>,
    pub targets: Vec<DeferredTypeFn>,
    /// Cached Go `len(m.sources) == 1 && isThisTypeParameter(m.sources[0])`.
    pub maps_this_only: bool,
}

// FunctionTypeMapper

// Go: checker/mapper.go:232 FunctionTypeMapper
#[derive(Clone)]
pub struct FunctionTypeMapper {
    pub fn_: TypeMapperFn,
}

// MergedTypeMapper

// Go: checker/mapper.go:250 MergedTypeMapper
#[derive(Clone, Copy, Debug, Default)]
pub struct MergedTypeMapper {
    pub m1: MapperId,
    pub m2: MapperId,
}

// CompositeTypeMapper

// Go: checker/mapper.go:274 CompositeTypeMapper
// PORT: the Go `c *Checker` field is dropped; `mapper_map` gets the checker.
#[derive(Clone, Copy, Debug, Default)]
pub struct CompositeTypeMapper {
    pub m1: MapperId,
    pub m2: MapperId,
}

// InferenceTypeMapper

// Go: checker/mapper.go:300 InferenceTypeMapper
// PORT: the Go `c *Checker` field is dropped; `mapper_map` gets the checker.
#[derive(Clone, Copy, Debug, Default)]
pub struct InferenceTypeMapper {
    pub n: InferenceContextId,
    pub fixing: bool,
}

impl Checker {
    /// Pushes a mapper into the arena. Go allocates with `&XxxTypeMapper{}`.
    ///
    /// PERF: this and the small `new_*_type_mapper` constructors that call it
    /// are `inline(always)`, with the arena push, so the `TypeMapper` is built
    /// once in its arena slot. Out of line (a plain `#[inline]` hint was not
    /// taken), the 64-byte `TypeMapper` went through the stack, and most of
    /// this function's time was the reload of that copy.
    #[inline(always)]
    pub fn alloc_type_mapper(&mut self, data: TypeMapper) -> MapperId {
        let id = MapperId(u32::try_from(self.mappers.len()).expect("mapper overflow"));
        self.mappers.push(data);
        id
    }

    // Go: checker/mapper.go:40 getMappedType
    pub fn get_mapped_type(&mut self, t: TypeId, mapper: MapperId) -> TypeId {
        let t = self.get_non_distributed_type_parameter(t);
        self.mapper_map(mapper, t)
    }

    // Go: checker/mapper.go:27 (*TypeMapper).Map
    // Dispatches to the Go `Map` method of each mapper kind.
    pub fn mapper_map(&mut self, m: MapperId, t: TypeId) -> TypeId {
        match self.mapper(m) {
            // Go: checker/mapper.go:88 (*TypeMapperBase).Map
            TypeMapper::Base(_) => t,
            // Go: checker/mapper.go:108 (*SimpleTypeMapper).Map
            TypeMapper::Simple(d) => {
                if t == d.source {
                    return d.target;
                }
                t
            }
            // Go: checker/mapper.go:136 (*ArrayTypeMapper).Map
            TypeMapper::Array(d) => {
                for (i, s) in d.sources.iter().enumerate() {
                    if t == *s {
                        return d.targets[i];
                    }
                }
                t
            }
            // Go: checker/mapper.go:168 (*ArrayToSingleTypeMapper).Map
            TypeMapper::ArrayToSingle(d) => {
                if d.sources.contains(&t) {
                    return d.target;
                }
                t
            }
            // Go: checker/mapper.go:193 (*DeferredTypeMapper).Map
            TypeMapper::Deferred(d) => {
                let mut target: Option<DeferredTypeFn> = None;
                for (i, s) in d.sources.iter().enumerate() {
                    if t == *s {
                        target = Some(d.targets[i].clone());
                        break;
                    }
                }
                if let Some(f) = target {
                    return f(self);
                }
                t
            }
            // Go: checker/mapper.go:219 (*FunctionTypeMapper).Map
            TypeMapper::Function(d) => {
                let f = d.fn_.clone();
                f(self, t)
            }
            // Go: checker/mapper.go:239 (*MergedTypeMapper).Map
            TypeMapper::Merged(d) => {
                let (m1, m2) = (d.m1, d.m2);
                let t1 = self.mapper_map(m1, t);
                self.mapper_map(m2, t1)
            }
            // Go: checker/mapper.go:265 (*CompositeTypeMapper).Map
            TypeMapper::Composite(d) => {
                let (m1, m2) = (d.m1, d.m2);
                let t1 = self.mapper_map(m1, t);
                if t1 != t {
                    return self.instantiate_type(t1, m2);
                }
                self.mapper_map(m2, t)
            }
            // Go: checker/mapper.go:293 (*InferenceTypeMapper).Map
            TypeMapper::Inference(d) => {
                let (n, fixing) = (d.n, d.fixing);
                self.inference_type_mapper_map(n, fixing, t)
            }
        }
    }

    // Go: checker/mapper.go:28 (*TypeMapper).Kind
    #[must_use]
    pub fn mapper_kind(&self, m: MapperId) -> TypeMapperKind {
        self.mapper(m).kind()
    }

    // Go: checker/mapper.go:29 (*TypeMapper).MapsThisOnly
    #[must_use]
    pub fn mapper_maps_this_only(&self, m: MapperId) -> bool {
        self.mapper(m).maps_this_only()
    }

    // Factory functions

    // Go: checker/mapper.go:44 newTypeMapper
    pub fn new_type_mapper(&mut self, sources: &[TypeId], targets: &[TypeId]) -> MapperId {
        if sources.len() == 1 {
            return self.new_simple_type_mapper(sources[0], targets[0]);
        }
        self.new_array_type_mapper(sources, targets)
    }

    /// `new_type_mapper` over shared lists. See `new_array_type_mapper_shared`.
    pub fn new_type_mapper_shared(
        &mut self,
        sources: SharedList<TypeId>,
        targets: SharedList<TypeId>,
    ) -> MapperId {
        if sources.len() == 1 {
            return self.new_simple_type_mapper(sources[0], targets[0]);
        }
        self.new_array_type_mapper_shared(sources, targets)
    }

    // Go: checker/mapper.go:51 combineTypeMappers
    pub fn combine_type_mappers(&mut self, m1: MapperId, m2: MapperId) -> MapperId {
        if m1.is_some() {
            return self.new_composite_type_mapper(m1, m2);
        }
        m2
    }

    // Go: checker/mapper.go:58 mapTypeWithCompositeMapper
    pub fn map_type_with_composite_mapper(
        &mut self,
        t: TypeId,
        m1: MapperId,
        m2: MapperId,
    ) -> TypeId {
        if m1.is_nil() {
            return self.get_mapped_type(t, m2);
        }
        let t1 = self.get_mapped_type(t, m1);
        if t1 != t {
            return self.instantiate_type(t1, m2);
        }
        self.get_mapped_type(t, m2)
    }

    // Go: checker/mapper.go:69 mergeTypeMappers
    pub fn merge_type_mappers(&mut self, m1: MapperId, m2: MapperId) -> MapperId {
        if m1.is_some() {
            return self.new_merged_type_mapper(m1, m2);
        }
        m2
    }

    // Go: checker/mapper.go:76 prependTypeMapping
    pub fn prepend_type_mapping(
        &mut self,
        source: TypeId,
        target: TypeId,
        mapper: MapperId,
    ) -> MapperId {
        if mapper.is_nil() {
            let source = self.get_non_distributed_type_parameter(source);
            return self.new_simple_type_mapper(source, target);
        }
        let source = self.get_non_distributed_type_parameter(source);
        let simple = self.new_simple_type_mapper(source, target);
        self.new_merged_type_mapper(simple, mapper)
    }

    // Go: checker/mapper.go:83 appendTypeMapping
    pub fn append_type_mapping(
        &mut self,
        mapper: MapperId,
        source: TypeId,
        target: TypeId,
    ) -> MapperId {
        if mapper.is_nil() {
            let source = self.get_non_distributed_type_parameter(source);
            return self.new_simple_type_mapper(source, target);
        }
        let source = self.get_non_distributed_type_parameter(source);
        let simple = self.new_simple_type_mapper(source, target);
        self.new_merged_type_mapper(mapper, simple)
    }

    // Maps forward-references to later types parameters to the empty object type.
    // This is used during inference when instantiating type parameter defaults.
    // Go: checker/mapper.go:92 newBackreferenceMapper
    pub fn new_backreference_mapper(
        &mut self,
        context: InferenceContextId,
        index: i32,
    ) -> MapperId {
        let type_parameters: Vec<TypeId> = self.inference_context(context).inferences
            [index as usize..]
            .iter()
            .map(|i| i.type_parameter)
            .collect();
        let unknown_type = self.unknown_type;
        self.new_array_to_single_type_mapper(&type_parameters, unknown_type)
    }

    // Go: checker/mapper.go:118 newSimpleTypeMapper
    #[inline(always)]
    pub fn new_simple_type_mapper(&mut self, source: TypeId, target: TypeId) -> MapperId {
        // Go: checker/mapper.go:119 (*SimpleTypeMapper).MapsThisOnly
        let maps_this_only = self.is_this_type_parameter(source);
        self.alloc_type_mapper(TypeMapper::Simple(SimpleTypeMapper {
            source,
            target,
            maps_this_only,
        }))
    }

    // Go: checker/mapper.go:149 newArrayTypeMapper
    // PORT: Go keeps the caller's slices; we copy them. Go callers do not
    // mutate these slices after building the mapper.
    pub fn new_array_type_mapper(&mut self, sources: &[TypeId], targets: &[TypeId]) -> MapperId {
        self.new_array_type_mapper_shared(sources.into(), targets.into())
    }

    /// `new_array_type_mapper` over lists that are already shared, so the
    /// mapper keeps them without a copy, like Go keeps the slices.
    #[inline(always)]
    pub fn new_array_type_mapper_shared(
        &mut self,
        sources: SharedList<TypeId>,
        targets: SharedList<TypeId>,
    ) -> MapperId {
        // Go: checker/mapper.go:149 (*ArrayTypeMapper).MapsThisOnly
        let maps_this_only = sources.len() == 1 && self.is_this_type_parameter(sources[0]);
        self.alloc_type_mapper(TypeMapper::Array(ArrayTypeMapper {
            sources,
            targets,
            maps_this_only,
        }))
    }

    // Go: checker/mapper.go:182 newArrayToSingleTypeMapper
    #[inline(always)]
    pub fn new_array_to_single_type_mapper(
        &mut self,
        sources: &[TypeId],
        target: TypeId,
    ) -> MapperId {
        // Go: checker/mapper.go:175 (*ArrayToSingleTypeMapper).MapsThisOnly
        let maps_this_only = sources.len() == 1 && self.is_this_type_parameter(sources[0]);
        self.alloc_type_mapper(TypeMapper::ArrayToSingle(ArrayToSingleTypeMapper {
            sources: sources.to_vec(),
            target,
            maps_this_only,
        }))
    }

    // Go: checker/mapper.go:209 newDeferredTypeMapper
    pub fn new_deferred_type_mapper(
        &mut self,
        sources: &[TypeId],
        targets: Vec<DeferredTypeFn>,
    ) -> MapperId {
        // Go: checker/mapper.go:202 (*DeferredTypeMapper).MapsThisOnly
        let maps_this_only = sources.len() == 1 && self.is_this_type_parameter(sources[0]);
        self.alloc_type_mapper(TypeMapper::Deferred(DeferredTypeMapper {
            sources: sources.to_vec(),
            targets,
            maps_this_only,
        }))
    }

    // Go: checker/mapper.go:237 newFunctionTypeMapper
    pub fn new_function_type_mapper(&mut self, fn_: TypeMapperFn) -> MapperId {
        self.alloc_type_mapper(TypeMapper::Function(FunctionTypeMapper { fn_ }))
    }

    // Go: checker/mapper.go:256 newMergedTypeMapper
    pub fn new_merged_type_mapper(&mut self, m1: MapperId, m2: MapperId) -> MapperId {
        self.alloc_type_mapper(TypeMapper::Merged(MergedTypeMapper { m1, m2 }))
    }

    // Go: checker/mapper.go:281 newCompositeTypeMapper
    pub fn new_composite_type_mapper(&mut self, m1: MapperId, m2: MapperId) -> MapperId {
        self.alloc_type_mapper(TypeMapper::Composite(CompositeTypeMapper { m1, m2 }))
    }

    // Go: checker/mapper.go:307 newInferenceTypeMapper
    pub fn new_inference_type_mapper(&mut self, n: InferenceContextId, fixing: bool) -> MapperId {
        self.alloc_type_mapper(TypeMapper::Inference(InferenceTypeMapper { n, fixing }))
    }

    // Go: checker/mapper.go:293 (*InferenceTypeMapper).Map
    fn inference_type_mapper_map(
        &mut self,
        n: InferenceContextId,
        fixing: bool,
        t: TypeId,
    ) -> TypeId {
        let count = self.inference_context(n).inferences.len();
        for i in 0..count {
            let inference = &self.inference_context(n).inferences[i];
            if t == inference.type_parameter {
                if fixing && !inference.is_fixed {
                    // Before we commit to a particular inference (and thus lock out any further inferences),
                    // we infer from any intra-expression inference sites we have collected.
                    self.infer_from_intra_expression_sites(n);
                    // PORT: Go clearCachedInferences(m.n.inferences), inlined
                    // over the context's inference list.
                    for info in &mut self.inference_context_mut(n).inferences {
                        if !info.is_fixed {
                            info.inferred_type = TypeId::NIL;
                        }
                    }
                    self.inference_context_mut(n).inferences[i].is_fixed = true;
                }
                return self.get_inferred_type(n, i as i32);
            }
        }
        t
    }
}
