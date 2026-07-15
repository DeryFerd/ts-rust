//! Canonical lexical name resolution.
//!
//! This is the immutable-AST counterpart of the pinned
//! `internal/binder/nameresolver.go`. Declaration lookup and alias/merge
//! behavior remain host callbacks: silently replacing them with direct table
//! reads would change TypeScript semantics. JavaScript, `JSDoc`, and `CommonJS`
//! paths are deliberately outside this dependency closure.

use std::ops::ControlFlow;

use ts_ast::{FileId, ModifierList, NodeArena, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_diagnostics::{Diagnostic, Message, message_by_code};
use ts_options::{CompilerOptions, ScriptTarget};

use crate::{
    BindingPhase, BoundFile, EscapedNameRef, InternalSymbolName, SemanticSymbolId, SymbolFlags,
    SymbolStore, SymbolTableId,
};

const NODE_FLAG_SYNTHESIZED: u32 = 1 << 4;
const NODE_FLAG_JSDOC: u32 = 1 << 22;

/// Exact compiler-option facts consumed by the pinned resolver.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CanonicalNameResolverOptions {
    pub isolated_modules: bool,
    pub verbatim_module_syntax: bool,
    pub emit_target: ScriptTarget,
    pub use_define_for_class_fields: Option<bool>,
}

impl Default for CanonicalNameResolverOptions {
    fn default() -> Self {
        Self::from(&CompilerOptions::default())
    }
}

impl From<&CompilerOptions> for CanonicalNameResolverOptions {
    fn from(options: &CompilerOptions) -> Self {
        Self {
            isolated_modules: options.isolated_modules,
            verbatim_module_syntax: options.verbatim_module_syntax,
            emit_target: options.target,
            use_define_for_class_fields: options.use_define_for_class_fields,
        }
    }
}

impl CanonicalNameResolverOptions {
    fn isolated_modules_like(self) -> bool {
        self.isolated_modules || self.verbatim_module_syntax
    }

    /// Pinned `CompilerOptions.GetEmitStandardClassFields`.
    fn emit_standard_class_fields(self) -> bool {
        self.use_define_for_class_fields != Some(false) && self.emit_target >= ScriptTarget::Es2022
    }
}

/// Three-state cache domain used by `useOuterVariableScopeInParameter`.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CanonicalScopeChangeState {
    #[default]
    Unknown,
    False,
    True,
}

/// Successful resolution facts passed to the pinned success callback.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CanonicalResolvedName {
    pub location: NodeRef,
    pub symbol: SemanticSymbolId,
    pub meaning: SymbolFlags,
    pub last_location: Option<NodeRef>,
    pub associated_declaration_for_containing_initializer_or_binding_name: Option<NodeRef>,
    pub within_deferred_context: bool,
}

/// Structural or capability failure. An ordinary missing name is `Ok(None)`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CanonicalNameResolutionError {
    WrongArena { file: FileId },
    DeclarationsIncomplete(FileId),
    MissingSourceFileFacts(FileId),
    JavaScriptDeferred(FileId),
    CommonJsDeferred(FileId),
    InvalidSymbolStore(FileId),
    UnboundLocation(NodeRef),
    JsDocDeferred(NodeRef),
    InvalidHostSymbol(SemanticSymbolId),
    InvalidHostTable(SymbolTableId),
    MissingDeclarationSymbol(NodeRef),
    MissingArgumentsSymbol,
    ForeignDeclarationAstUnavailable(NodeRef),
}

impl std::fmt::Display for CanonicalNameResolutionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongArena { file } => write!(
                formatter,
                "name-resolution arena does not match Program file slot {}",
                file.index()
            ),
            Self::DeclarationsIncomplete(file) => write!(
                formatter,
                "declaration binding is incomplete for Program file slot {}",
                file.index()
            ),
            Self::MissingSourceFileFacts(file) => write!(
                formatter,
                "source-file facts are missing for Program file slot {}",
                file.index()
            ),
            Self::JavaScriptDeferred(file) => write!(
                formatter,
                "JavaScript name resolution is deferred for Program file slot {}",
                file.index()
            ),
            Self::CommonJsDeferred(file) => write!(
                formatter,
                "CommonJS name resolution is deferred for Program file slot {}",
                file.index()
            ),
            Self::InvalidSymbolStore(file) => write!(
                formatter,
                "symbol store does not own Program file slot {}",
                file.index()
            ),
            Self::UnboundLocation(node) => write!(
                formatter,
                "AST node {:?} is not part of the bound source file",
                node.node
            ),
            Self::JsDocDeferred(node) => write!(
                formatter,
                "JSDoc name resolution is deferred at AST node {:?}",
                node.node
            ),
            Self::InvalidHostSymbol(_) => {
                formatter.write_str("name-resolution host returned a foreign symbol")
            }
            Self::InvalidHostTable(_) => {
                formatter.write_str("name-resolution host returned a foreign symbol table")
            }
            Self::MissingDeclarationSymbol(node) => write!(
                formatter,
                "name-resolution host omitted the symbol for declaration {:?}",
                node.node
            ),
            Self::MissingArgumentsSymbol => {
                formatter.write_str("name-resolution host omitted the arguments symbol")
            }
            Self::ForeignDeclarationAstUnavailable(node) => write!(
                formatter,
                "name-resolution host cannot inspect foreign declaration {:?}",
                node.node
            ),
        }
    }
}

impl std::error::Error for CanonicalNameResolutionError {}

/// Callback surface retained from the pinned Go resolver.
///
/// The two required semantic callbacks must implement merged-symbol and alias
/// behavior. The resolver validates every returned handle before observing it.
pub trait CanonicalNameResolverHost {
    fn compiler_options(&self) -> CanonicalNameResolverOptions;

    fn get_symbol_of_declaration(&mut self, declaration: NodeRef) -> Option<SemanticSymbolId>;

    fn get_local_symbol_of_declaration(&mut self, declaration: NodeRef)
    -> Option<SemanticSymbolId>;

    fn lookup(
        &mut self,
        store: &SymbolStore,
        symbols: SymbolTableId,
        name: EscapedNameRef<'_>,
        meaning: SymbolFlags,
    ) -> Option<SemanticSymbolId>;

    fn globals(&self) -> Option<SymbolTableId>;

    fn arguments_symbol(&mut self, store: &SymbolStore) -> Option<SemanticSymbolId>;

    /// Retained for the later JavaScript closure. It is not called by this
    /// TypeScript-only resolver.
    fn require_symbol(&mut self, _store: &SymbolStore) -> Option<SemanticSymbolId> {
        None
    }

    /// AST facts for declarations in another file/arena. Returning `None`
    /// fails closed when the pinned algorithm actually needs the fact.
    fn foreign_declaration_kind(&mut self, _declaration: NodeRef) -> Option<SyntaxKind> {
        None
    }

    fn foreign_declaration_parent(&mut self, _declaration: NodeRef) -> Option<NodeRef> {
        None
    }

    fn foreign_declaration_has_syntactic_modifier(
        &mut self,
        _declaration: NodeRef,
        _modifier: SyntaxKind,
    ) -> Option<bool> {
        None
    }

    fn error(&mut self, _location: NodeRef, _diagnostic: Diagnostic) {}

    fn symbol_referenced(&mut self, _symbol: SemanticSymbolId, _meaning: SymbolFlags) {}

    fn set_requires_scope_change_cache(
        &mut self,
        _declaration: NodeRef,
        _value: CanonicalScopeChangeState,
    ) {
    }

    fn get_requires_scope_change_cache(
        &mut self,
        _declaration: NodeRef,
    ) -> CanonicalScopeChangeState {
        CanonicalScopeChangeState::Unknown
    }

    fn on_property_with_invalid_initializer(
        &mut self,
        _location: NodeRef,
        _name: &str,
        _declaration: NodeRef,
        _result: Option<SemanticSymbolId>,
    ) -> bool {
        false
    }

    fn on_failed_to_resolve_symbol(
        &mut self,
        _location: NodeRef,
        _name: &str,
        _meaning: SymbolFlags,
        _name_not_found_message: &'static Message,
    ) {
    }

    fn on_successfully_resolved_symbol(&mut self, _resolved: CanonicalResolvedName) {}
}

/// Exact non-JavaScript lexical/module name resolver over one bound file.
pub struct CanonicalNameResolver<'a, H> {
    arena: &'a NodeArena,
    bound: &'a BoundFile,
    symbols: &'a SymbolStore,
    options: CanonicalNameResolverOptions,
    host: &'a mut H,
}

impl<'a, H: CanonicalNameResolverHost> CanonicalNameResolver<'a, H> {
    /// Creates a resolver only after the full source/store provenance preflight.
    ///
    /// # Errors
    ///
    /// Returns a typed source-kind, binding-phase, arena, or store-provenance
    /// error when the supplied components cannot form one canonical resolver.
    pub fn new(
        arena: &'a NodeArena,
        bound: &'a BoundFile,
        symbols: &'a SymbolStore,
        host: &'a mut H,
    ) -> Result<Self, CanonicalNameResolutionError> {
        let file = bound.file_id();
        if bound.node_arena_id() != arena.id() {
            return Err(CanonicalNameResolutionError::WrongArena { file });
        }
        let Some(facts) = bound.source_facts() else {
            return Err(CanonicalNameResolutionError::MissingSourceFileFacts(file));
        };
        if facts.is_javascript_file() {
            return Err(CanonicalNameResolutionError::JavaScriptDeferred(file));
        }
        if facts.is_common_js_module() {
            return Err(CanonicalNameResolutionError::CommonJsDeferred(file));
        }
        if bound.phase() != BindingPhase::Declarations {
            return Err(CanonicalNameResolutionError::DeclarationsIncomplete(file));
        }
        if !symbols.contains_node_ref(bound.source_file()) {
            return Err(CanonicalNameResolutionError::InvalidSymbolStore(file));
        }
        let options = host.compiler_options();
        Ok(Self {
            arena,
            bound,
            symbols,
            options,
            host,
        })
    }

    /// Resolves `name` from `location` with pinned TypeScript lexical rules.
    ///
    /// `name_not_found_message` is only a callback/error-reporting sentinel,
    /// matching the Go implementation. `Ok(None)` is an ordinary miss.
    ///
    /// # Errors
    ///
    /// Returns a typed provenance or unavailable-capability error. A name that
    /// is absent from every applicable scope returns `Ok(None)` instead.
    ///
    /// # Panics
    ///
    /// Panics only if the already-bound immutable AST violates the parent,
    /// kind/payload, or declaration invariants validated by canonical binding.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    pub fn resolve(
        &mut self,
        original_location: NodeRef,
        name: &str,
        meaning: SymbolFlags,
        name_not_found_message: Option<&'static Message>,
        is_use: bool,
        exclude_globals: bool,
    ) -> Result<Option<SemanticSymbolId>, CanonicalNameResolutionError> {
        self.validate_location(original_location)?;
        let mut location = Some(original_location.node);
        let mut result = None;
        let mut last_location = None;
        let mut last_self_reference_location = None;
        let mut property_with_invalid_initializer = None;
        let mut associated_declaration = None;
        let mut within_deferred_context = false;
        let name_is_const = name == "const";

        while let Some(mut current) = location {
            self.reject_jsdoc(current)?;
            if name_is_const && is_const_assertion(self.arena, current) {
                return Ok(None);
            }

            if is_module_or_enum_declaration(self.arena, current)
                && last_location.is_some()
                && declaration_name(self.arena, current) == last_location
            {
                last_location = Some(current);
                current = self
                    .arena
                    .get(current)
                    .and_then(|node| node.parent)
                    .expect("bound non-root declaration has a parent");
            }

            if let Some(locals) = self.bound.locals(self.node_ref(current))
                && !self.is_global_source_file(current)
            {
                let candidate = self.lookup(locals, name, meaning)?;
                if let Some(candidate) = candidate {
                    let mut use_result = true;
                    let record = self
                        .symbols
                        .symbol(candidate)
                        .expect("lookup result was validated");
                    if is_function_like(self.kind(current))
                        && let Some(last) = last_location
                        && Some(last) != function_body(self.arena, current)
                    {
                        if meaning.intersects(record.flags() & SymbolFlags::TYPE)
                            && self.kind(last) != SyntaxKind::JsDoc
                        {
                            use_result = record.flags().contains(SymbolFlags::TYPE_PARAMETER)
                                && (self.is_synthesized(last)
                                    || Some(last) == function_type(self.arena, current)
                                    || matches!(
                                        self.kind(last),
                                        SyntaxKind::Parameter
                                            | SyntaxKind::JsDocParameterTag
                                            | SyntaxKind::JsDocReturnTag
                                            | SyntaxKind::TypeParameter
                                    ));
                        }
                        if meaning.intersects(record.flags() & SymbolFlags::VARIABLE) {
                            if self.use_outer_variable_scope_in_parameter(candidate, current, last)
                            {
                                use_result = false;
                            } else if record
                                .flags()
                                .contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
                            {
                                use_result = self.kind(last) == SyntaxKind::Parameter
                                    || self.is_synthesized(last)
                                    || Some(last) == function_type(self.arena, current)
                                        && record.value_declaration().is_some_and(|declaration| {
                                            self.find_ancestor_kind(
                                                declaration,
                                                SyntaxKind::Parameter,
                                            )
                                        });
                            }
                        }
                    } else if self.kind(current) == SyntaxKind::ConditionalType {
                        let NodeData::ConditionalTypeNode(conditional) = &self.node(current).data
                        else {
                            unreachable!("bound kind/data agreement was preflighted");
                        };
                        use_result = last_location == Some(conditional.true_type);
                    }
                    if use_result {
                        result = Some(candidate);
                        break;
                    }
                }
            }

            within_deferred_context |= self.get_is_deferred_context(current, last_location);

            match self.kind(current) {
                SyntaxKind::SourceFile => {
                    if self.bound.source_facts().is_some_and(
                        crate::CanonicalSourceFileFacts::is_external_or_common_js_module,
                    ) {
                        result = self.lookup_module_or_namespace(current, name, meaning)?;
                        if result.is_some() {
                            break;
                        }
                    }
                }
                SyntaxKind::ModuleDeclaration => {
                    result = self.lookup_module_or_namespace(current, name, meaning)?;
                    if result.is_some() {
                        break;
                    }
                }
                SyntaxKind::EnumDeclaration => {
                    let declaration = self.node_ref(current);
                    if let Some(enum_symbol) = self.declaration_symbol(declaration)? {
                        let exports = self
                            .symbols
                            .symbol(enum_symbol)
                            .expect("declaration symbol was validated")
                            .exports();
                        if let Some(exports) = exports {
                            result =
                                self.lookup(exports, name, meaning & SymbolFlags::ENUM_MEMBER)?;
                        }
                        if let Some(member) = result {
                            self.report_cross_file_enum_reference(
                                original_location,
                                current,
                                enum_symbol,
                                member,
                                name,
                                name_not_found_message.is_some(),
                            );
                            break;
                        }
                    }
                }
                SyntaxKind::PropertyDeclaration => {
                    if !is_static(self.arena, current)
                        && let Some(class) = self.node(current).parent
                        && let Some(constructor) = find_constructor(self.arena, class)
                        && let Some(locals) = self.bound.locals(self.node_ref(constructor))
                        && self
                            .lookup(locals, name, meaning & SymbolFlags::VALUE)?
                            .is_some()
                    {
                        property_with_invalid_initializer = Some(current);
                    }
                }
                SyntaxKind::ClassDeclaration
                | SyntaxKind::ClassExpression
                | SyntaxKind::InterfaceDeclaration => {
                    let declaration = self.node_ref(current);
                    let container = self.declaration_symbol(declaration)?.ok_or(
                        CanonicalNameResolutionError::MissingDeclarationSymbol(declaration),
                    )?;
                    let members = self
                        .symbols
                        .symbol(container)
                        .expect("declaration symbol was validated")
                        .members();
                    if let Some(members) = members {
                        result = self.lookup(members, name, meaning & SymbolFlags::TYPE)?;
                    }
                    if let Some(type_parameter) = result {
                        if !self.type_parameter_declared_in_container(type_parameter, current)? {
                            result = None;
                        } else if last_location.is_some_and(|last| is_static(self.arena, last)) {
                            if name_not_found_message.is_some() {
                                self.error(original_location, 2302, std::iter::empty::<String>());
                            }
                            return Ok(None);
                        } else {
                            break;
                        }
                    }
                    if self.kind(current) == SyntaxKind::ClassExpression
                        && meaning.intersects(SymbolFlags::CLASS)
                        && declaration_name(self.arena, current)
                            .and_then(|node| identifier_text(self.arena, node))
                            == Some(name)
                    {
                        result = self.bound.symbol(declaration);
                        self.validate_optional_symbol(result)?;
                        break;
                    }
                }
                SyntaxKind::ExpressionWithTypeArguments => {
                    let NodeData::ExpressionWithTypeArguments(expression) =
                        &self.node(current).data
                    else {
                        unreachable!("bound kind/data agreement was preflighted");
                    };
                    if last_location == Some(expression.expression)
                        && self.node(current).parent.is_some_and(|heritage| {
                            matches!(
                                &self.node(heritage).data,
                                NodeData::HeritageClause(clause)
                                    if clause.token == SyntaxKind::ExtendsKeyword
                            )
                        })
                    {
                        let heritage = self.node(current).parent.expect("checked above");
                        let container = self.node(heritage).parent.expect("heritage has a parent");
                        if is_class_like(self.kind(container)) {
                            let declaration = self.node_ref(container);
                            let symbol = self.declaration_symbol(declaration)?.ok_or(
                                CanonicalNameResolutionError::MissingDeclarationSymbol(declaration),
                            )?;
                            if let Some(members) = self
                                .symbols
                                .symbol(symbol)
                                .expect("declaration symbol was validated")
                                .members()
                            {
                                result = self.lookup(members, name, meaning & SymbolFlags::TYPE)?;
                            }
                            if result.is_some() {
                                if name_not_found_message.is_some() {
                                    self.error(
                                        original_location,
                                        2562,
                                        std::iter::empty::<String>(),
                                    );
                                }
                                return Ok(None);
                            }
                        }
                    }
                }
                SyntaxKind::ComputedPropertyName => {
                    let parent = self
                        .node(current)
                        .parent
                        .expect("computed name has a parent");
                    let grandparent = self.node(parent).parent.expect("member has a parent");
                    if is_class_like(self.kind(grandparent))
                        || self.kind(grandparent) == SyntaxKind::InterfaceDeclaration
                    {
                        let declaration = self.node_ref(grandparent);
                        let symbol = self.declaration_symbol(declaration)?.ok_or(
                            CanonicalNameResolutionError::MissingDeclarationSymbol(declaration),
                        )?;
                        if let Some(members) = self
                            .symbols
                            .symbol(symbol)
                            .expect("declaration symbol was validated")
                            .members()
                        {
                            result = self.lookup(members, name, meaning & SymbolFlags::TYPE)?;
                        }
                        if result.is_some() {
                            if name_not_found_message.is_some() {
                                self.error(original_location, 2467, std::iter::empty::<String>());
                            }
                            return Ok(None);
                        }
                    }
                }
                SyntaxKind::MethodDeclaration
                | SyntaxKind::Constructor
                | SyntaxKind::GetAccessor
                | SyntaxKind::SetAccessor
                | SyntaxKind::FunctionDeclaration => {
                    if meaning.intersects(SymbolFlags::VARIABLE) && name == "arguments" {
                        result = Some(self.arguments_symbol()?);
                        break;
                    }
                }
                SyntaxKind::FunctionExpression => {
                    if meaning.intersects(SymbolFlags::VARIABLE) && name == "arguments" {
                        result = Some(self.arguments_symbol()?);
                        break;
                    }
                    if meaning.intersects(SymbolFlags::FUNCTION)
                        && declaration_name(self.arena, current)
                            .and_then(|node| identifier_text(self.arena, node))
                            == Some(name)
                    {
                        result = self.bound.symbol(self.node_ref(current));
                        self.validate_optional_symbol(result)?;
                        break;
                    }
                }
                SyntaxKind::Decorator => {
                    if self
                        .node(current)
                        .parent
                        .is_some_and(|parent| self.kind(parent) == SyntaxKind::Parameter)
                    {
                        current = self.node(current).parent.expect("checked above");
                    }
                    if self.node(current).parent.is_some_and(|parent| {
                        is_class_element(self.kind(parent))
                            || self.kind(parent) == SyntaxKind::ClassDeclaration
                    }) {
                        current = self.node(current).parent.expect("checked above");
                    }
                }
                SyntaxKind::Parameter => {
                    let NodeData::ParameterDeclaration(parameter) = &self.node(current).data else {
                        unreachable!("bound kind/data agreement was preflighted");
                    };
                    if last_location.is_some_and(|last| {
                        Some(last) == parameter.initializer
                            || last == parameter.name && is_binding_pattern(self.kind(last))
                    }) && associated_declaration.is_none()
                    {
                        associated_declaration = Some(current);
                    }
                }
                SyntaxKind::BindingElement => {
                    let NodeData::BindingElement(element) = &self.node(current).data else {
                        unreachable!("bound kind/data agreement was preflighted");
                    };
                    if last_location.is_some_and(|last| {
                        Some(last) == element.initializer
                            || Some(last) == element.name && is_binding_pattern(self.kind(last))
                    }) && self.is_part_of_parameter_declaration(current)
                        && associated_declaration.is_none()
                    {
                        associated_declaration = Some(current);
                    }
                }
                SyntaxKind::InferType => {
                    if meaning.intersects(SymbolFlags::TYPE_PARAMETER) {
                        let NodeData::InferTypeNode(infer) = &self.node(current).data else {
                            unreachable!("bound kind/data agreement was preflighted");
                        };
                        let type_parameter = self.node(infer.type_parameter);
                        let NodeData::TypeParameterDeclaration(parameter) = &type_parameter.data
                        else {
                            unreachable!("bound kind/data agreement was preflighted");
                        };
                        if identifier_text(self.arena, parameter.name) == Some(name) {
                            result = self.bound.symbol(self.node_ref(infer.type_parameter));
                            self.validate_optional_symbol(result)?;
                            break;
                        }
                    }
                }
                SyntaxKind::ExportSpecifier => {
                    let NodeData::ExportSpecifier(specifier) = &self.node(current).data else {
                        unreachable!("bound kind/data agreement was preflighted");
                    };
                    if last_location == specifier.property_name {
                        let named_exports =
                            self.node(current).parent.expect("specifier has parent");
                        let export_declaration = self
                            .node(named_exports)
                            .parent
                            .expect("named exports has parent");
                        if matches!(
                            &self.node(export_declaration).data,
                            NodeData::ExportDeclaration(export) if export.module_specifier.is_some()
                        ) {
                            current = self
                                .node(export_declaration)
                                .parent
                                .expect("export declaration has parent");
                        }
                    }
                }
                _ => {}
            }

            if is_self_reference_location(self.arena, current, last_location) {
                last_self_reference_location = Some(current);
            }
            last_location = Some(current);
            location = self.node(current).parent;
        }

        if is_use
            && let Some(resolved) = result
            && last_self_reference_location.is_none_or(|self_reference| {
                self.bound.symbol(self.node_ref(self_reference)) != Some(resolved)
            })
        {
            self.host.symbol_referenced(resolved, meaning);
        }

        if result.is_none()
            && !exclude_globals
            && let Some(globals) = self.host.globals()
        {
            self.validate_table(globals)?;
            result = self.lookup(globals, name, meaning | SymbolFlags::GLOBAL_LOOKUP)?;
        }

        if let Some(message) = name_not_found_message {
            if let Some(property) = property_with_invalid_initializer
                && self.host.on_property_with_invalid_initializer(
                    original_location,
                    name,
                    self.node_ref(property),
                    result,
                )
            {
                return Ok(None);
            }
            match result {
                None => {
                    self.host.on_failed_to_resolve_symbol(
                        original_location,
                        name,
                        meaning,
                        message,
                    );
                }
                Some(symbol) => {
                    self.host
                        .on_successfully_resolved_symbol(CanonicalResolvedName {
                            location: original_location,
                            symbol,
                            meaning,
                            last_location: last_location.map(|node| self.node_ref(node)),
                            associated_declaration_for_containing_initializer_or_binding_name:
                                associated_declaration.map(|node| self.node_ref(node)),
                            within_deferred_context,
                        });
                }
            }
        }
        Ok(result)
    }

    fn lookup_module_or_namespace(
        &mut self,
        location: NodeId,
        name: &str,
        meaning: SymbolFlags,
    ) -> Result<Option<SemanticSymbolId>, CanonicalNameResolutionError> {
        let declaration = self.node_ref(location);
        let Some(module_symbol) = self.declaration_symbol(declaration)? else {
            return Ok(None);
        };
        let Some(exports) = self
            .symbols
            .symbol(module_symbol)
            .expect("declaration symbol was validated")
            .exports()
        else {
            return Ok(None);
        };
        self.validate_table(exports)?;

        if self.kind(location) == SyntaxKind::SourceFile
            || self.kind(location) == SyntaxKind::ModuleDeclaration
                && self.is_ambient_node(location)
                && !is_global_scope_augmentation(self.arena, location)
        {
            if let Some(default_export) = self
                .symbols
                .symbol_table(exports)
                .expect("exports table was validated")
                .get(InternalSymbolName::Default.as_ref())
            {
                let local = self.local_symbol_for_export_default(default_export)?;
                let export = self
                    .symbols
                    .symbol(default_export)
                    .expect("table symbols are store-owned");
                if let Some(local) = local
                    && export.flags().intersects(meaning)
                    && self
                        .symbols
                        .symbol(local)
                        .expect("local symbol was validated")
                        .name()
                        == EscapedNameRef::source(name)
                {
                    return Ok(Some(default_export));
                }
            }

            if let Some(module_export) = self
                .symbols
                .symbol_table(exports)
                .expect("exports table was validated")
                .get_source(name)
            {
                let export = self
                    .symbols
                    .symbol(module_export)
                    .expect("table symbols are store-owned");
                if export.flags() == SymbolFlags::ALIAS
                    && self.symbol_has_declaration_kind(
                        module_export,
                        [SyntaxKind::ExportSpecifier, SyntaxKind::NamespaceExport],
                    )?
                {
                    return Ok(None);
                }
            }
        }

        if name == "default" {
            Ok(None)
        } else {
            self.lookup(exports, name, meaning & SymbolFlags::MODULE_MEMBER)
        }
    }

    fn local_symbol_for_export_default(
        &mut self,
        symbol: SemanticSymbolId,
    ) -> Result<Option<SemanticSymbolId>, CanonicalNameResolutionError> {
        let record = self
            .symbols
            .symbol(symbol)
            .ok_or(CanonicalNameResolutionError::InvalidHostSymbol(symbol))?;
        let Some(declarations) = record.declarations() else {
            return Ok(None);
        };
        let Some(first) = declarations.first().copied() else {
            return Ok(None);
        };
        if !self.declaration_has_modifier(first, SyntaxKind::DefaultKeyword)? {
            return Ok(None);
        }
        for declaration in declarations {
            if let Some(local) = self.host.get_local_symbol_of_declaration(*declaration) {
                self.validate_symbol(local)?;
                return Ok(Some(local));
            }
        }
        Ok(None)
    }

    fn symbol_has_declaration_kind<const N: usize>(
        &mut self,
        symbol: SemanticSymbolId,
        kinds: [SyntaxKind; N],
    ) -> Result<bool, CanonicalNameResolutionError> {
        let declarations = self
            .symbols
            .symbol(symbol)
            .ok_or(CanonicalNameResolutionError::InvalidHostSymbol(symbol))?
            .declarations()
            .map(<[_]>::to_vec)
            .unwrap_or_default();
        for declaration in declarations {
            let kind = self.declaration_kind(declaration)?;
            if kinds.contains(&kind) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn type_parameter_declared_in_container(
        &mut self,
        symbol: SemanticSymbolId,
        container: NodeId,
    ) -> Result<bool, CanonicalNameResolutionError> {
        let declarations = self
            .symbols
            .symbol(symbol)
            .ok_or(CanonicalNameResolutionError::InvalidHostSymbol(symbol))?
            .declarations()
            .map(<[_]>::to_vec)
            .unwrap_or_default();
        let container = self.node_ref(container);
        for declaration in declarations {
            if self.declaration_kind(declaration)? == SyntaxKind::TypeParameter
                && self.declaration_parent(declaration)? == container
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn report_cross_file_enum_reference(
        &mut self,
        original_location: NodeRef,
        enum_declaration: NodeId,
        enum_symbol: SemanticSymbolId,
        member: SemanticSymbolId,
        name: &str,
        report: bool,
    ) {
        if !report
            || !self.options.isolated_modules_like()
            || self.is_ambient_node(enum_declaration)
        {
            return;
        }
        let Some(value_declaration) = self
            .symbols
            .symbol(member)
            .and_then(crate::semantic::Symbol::value_declaration)
        else {
            return;
        };
        if value_declaration.file == self.bound.file_id() {
            return;
        }
        let flag_name = if self.options.verbatim_module_syntax {
            "verbatimModuleSyntax"
        } else {
            "isolatedModules"
        };
        let enum_name = self
            .symbols
            .symbol(enum_symbol)
            .and_then(|symbol| symbol.name().as_utf8())
            .unwrap_or_default();
        self.error(
            original_location,
            1281,
            [
                name.to_owned(),
                flag_name.to_owned(),
                format!("{enum_name}.{name}"),
            ],
        );
    }

    fn use_outer_variable_scope_in_parameter(
        &mut self,
        result: SemanticSymbolId,
        function: NodeId,
        last_location: NodeId,
    ) -> bool {
        if self.kind(last_location) != SyntaxKind::Parameter {
            return false;
        }
        let Some(body) = function_body(self.arena, function) else {
            return false;
        };
        let Some(value_declaration) = self
            .symbols
            .symbol(result)
            .expect("lookup result was validated")
            .value_declaration()
        else {
            return false;
        };
        if !value_declaration.is_for(self.arena.id(), self.bound.file_id()) {
            return false;
        }
        let declaration_range = self.node(value_declaration.node).range;
        let body_range = self.node(body).range;
        if declaration_range.start < body_range.start || declaration_range.end > body_range.end {
            return false;
        }

        let function_ref = self.node_ref(function);
        let mut state = self.host.get_requires_scope_change_cache(function_ref);
        if state == CanonicalScopeChangeState::Unknown {
            let requires = function_parameters(self.arena, function).is_some_and(|parameters| {
                parameters
                    .iter()
                    .copied()
                    .any(|parameter| self.requires_scope_change(parameter))
            });
            state = if requires {
                CanonicalScopeChangeState::True
            } else {
                CanonicalScopeChangeState::False
            };
            self.host
                .set_requires_scope_change_cache(function_ref, state);
        }
        state != CanonicalScopeChangeState::True
    }

    fn requires_scope_change(&self, parameter: NodeId) -> bool {
        let NodeData::ParameterDeclaration(parameter) = &self.node(parameter).data else {
            return false;
        };
        self.requires_scope_change_worker(parameter.name)
            || parameter
                .initializer
                .is_some_and(|initializer| self.requires_scope_change_worker(initializer))
    }

    fn requires_scope_change_worker(&self, node: NodeId) -> bool {
        match self.kind(node) {
            SyntaxKind::ArrowFunction
            | SyntaxKind::FunctionExpression
            | SyntaxKind::FunctionDeclaration
            | SyntaxKind::Constructor => false,
            SyntaxKind::MethodDeclaration
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::PropertyAssignment => declaration_name(self.arena, node)
                .is_some_and(|name| self.requires_scope_change_worker(name)),
            SyntaxKind::PropertyDeclaration => {
                if has_syntactic_modifier(self.arena, node, SyntaxKind::StaticKeyword) {
                    !self.options.emit_standard_class_fields()
                } else {
                    declaration_name(self.arena, node)
                        .is_some_and(|name| self.requires_scope_change_worker(name))
                }
            }
            kind => {
                if is_nullish_coalesce(self.arena, node) || is_optional_chain(self.arena, node) {
                    return self.options.emit_target < ScriptTarget::Es2020;
                }
                if kind == SyntaxKind::BindingElement
                    && matches!(
                        &self.node(node).data,
                        NodeData::BindingElement(element)
                            if element.dot_dot_dot_token.is_some()
                                && self.node(node).parent.is_some_and(|parent| {
                                    self.kind(parent) == SyntaxKind::ObjectBindingPattern
                                })
                    )
                {
                    return self.options.emit_target < ScriptTarget::Es2017;
                }
                if is_type_node_kind(kind) {
                    return false;
                }
                matches!(
                    self.node(node).try_for_each_child(|child| {
                        if self.requires_scope_change_worker(child) {
                            ControlFlow::Break(())
                        } else {
                            ControlFlow::Continue(())
                        }
                    }),
                    ControlFlow::Break(())
                )
            }
        }
    }

    fn get_is_deferred_context(&self, location: NodeId, last_location: Option<NodeId>) -> bool {
        let kind = self.kind(location);
        if !matches!(
            kind,
            SyntaxKind::ArrowFunction | SyntaxKind::FunctionExpression
        ) {
            return kind == SyntaxKind::TypeQuery
                || (is_function_like_declaration(kind)
                    || kind == SyntaxKind::PropertyDeclaration
                        && !is_static(self.arena, location))
                    && (last_location.is_none()
                        || last_location != declaration_name(self.arena, location));
        }
        if last_location.is_some() && last_location == declaration_name(self.arena, location) {
            return false;
        }
        if function_asterisk_token(self.arena, location).is_some()
            || has_syntactic_modifier(self.arena, location, SyntaxKind::AsyncKeyword)
        {
            return true;
        }
        immediately_invoked_function(self.arena, location).is_none()
    }

    fn is_ambient_node(&self, mut node: NodeId) -> bool {
        if self
            .bound
            .source_facts()
            .is_some_and(crate::CanonicalSourceFileFacts::is_declaration_file)
        {
            return true;
        }
        loop {
            if has_syntactic_modifier(self.arena, node, SyntaxKind::DeclareKeyword)
                || is_ambient_module(self.arena, node)
            {
                return true;
            }
            let Some(parent) = self.node(node).parent else {
                return false;
            };
            node = parent;
        }
    }

    fn is_global_source_file(&self, node: NodeId) -> bool {
        self.kind(node) == SyntaxKind::SourceFile
            && self
                .bound
                .source_facts()
                .is_some_and(|facts| !facts.is_external_or_common_js_module())
    }

    fn is_part_of_parameter_declaration(&self, mut node: NodeId) -> bool {
        while matches!(
            self.kind(node),
            SyntaxKind::BindingElement
                | SyntaxKind::ObjectBindingPattern
                | SyntaxKind::ArrayBindingPattern
        ) {
            node = match self.node(node).parent {
                Some(parent) => parent,
                None => return false,
            };
        }
        self.kind(node) == SyntaxKind::Parameter
    }

    fn find_ancestor_kind(&self, node: NodeRef, kind: SyntaxKind) -> bool {
        if !node.is_for(self.arena.id(), self.bound.file_id()) {
            return false;
        }
        let mut current = Some(node.node);
        while let Some(node) = current {
            if self.kind(node) == kind {
                return true;
            }
            current = self.node(node).parent;
        }
        false
    }

    fn declaration_symbol(
        &mut self,
        declaration: NodeRef,
    ) -> Result<Option<SemanticSymbolId>, CanonicalNameResolutionError> {
        let symbol = self.host.get_symbol_of_declaration(declaration);
        self.validate_optional_symbol(symbol)?;
        Ok(symbol)
    }

    fn arguments_symbol(&mut self) -> Result<SemanticSymbolId, CanonicalNameResolutionError> {
        let symbol = self
            .host
            .arguments_symbol(self.symbols)
            .ok_or(CanonicalNameResolutionError::MissingArgumentsSymbol)?;
        self.validate_symbol(symbol)?;
        Ok(symbol)
    }

    fn lookup(
        &mut self,
        table: SymbolTableId,
        name: &str,
        meaning: SymbolFlags,
    ) -> Result<Option<SemanticSymbolId>, CanonicalNameResolutionError> {
        self.validate_table(table)?;
        let symbol = self
            .host
            .lookup(self.symbols, table, EscapedNameRef::source(name), meaning);
        self.validate_optional_symbol(symbol)?;
        Ok(symbol)
    }

    fn declaration_kind(
        &mut self,
        declaration: NodeRef,
    ) -> Result<SyntaxKind, CanonicalNameResolutionError> {
        if !self.symbols.contains_node_ref(declaration) {
            return Err(CanonicalNameResolutionError::UnboundLocation(declaration));
        }
        if declaration.is_for(self.arena.id(), self.bound.file_id()) {
            return Ok(self.kind(declaration.node));
        }
        self.host
            .foreign_declaration_kind(declaration)
            .ok_or(CanonicalNameResolutionError::ForeignDeclarationAstUnavailable(declaration))
    }

    fn declaration_parent(
        &mut self,
        declaration: NodeRef,
    ) -> Result<NodeRef, CanonicalNameResolutionError> {
        if !self.symbols.contains_node_ref(declaration) {
            return Err(CanonicalNameResolutionError::UnboundLocation(declaration));
        }
        if declaration.is_for(self.arena.id(), self.bound.file_id()) {
            let parent = self.node(declaration.node).parent.ok_or(
                CanonicalNameResolutionError::ForeignDeclarationAstUnavailable(declaration),
            )?;
            return Ok(self.node_ref(parent));
        }
        let parent = self
            .host
            .foreign_declaration_parent(declaration)
            .ok_or(CanonicalNameResolutionError::ForeignDeclarationAstUnavailable(declaration))?;
        if !parent.is_for(declaration.arena, declaration.file)
            || !self.symbols.contains_node_ref(parent)
        {
            return Err(CanonicalNameResolutionError::UnboundLocation(parent));
        }
        Ok(parent)
    }

    fn declaration_has_modifier(
        &mut self,
        declaration: NodeRef,
        modifier: SyntaxKind,
    ) -> Result<bool, CanonicalNameResolutionError> {
        if !self.symbols.contains_node_ref(declaration) {
            return Err(CanonicalNameResolutionError::UnboundLocation(declaration));
        }
        if declaration.is_for(self.arena.id(), self.bound.file_id()) {
            return Ok(has_syntactic_modifier(
                self.arena,
                declaration.node,
                modifier,
            ));
        }
        self.host
            .foreign_declaration_has_syntactic_modifier(declaration, modifier)
            .ok_or(CanonicalNameResolutionError::ForeignDeclarationAstUnavailable(declaration))
    }

    fn validate_location(&self, location: NodeRef) -> Result<(), CanonicalNameResolutionError> {
        if !self.bound.contains(location) || !self.symbols.contains_node_ref(location) {
            return Err(CanonicalNameResolutionError::UnboundLocation(location));
        }
        Ok(())
    }

    fn validate_symbol(
        &self,
        symbol: SemanticSymbolId,
    ) -> Result<(), CanonicalNameResolutionError> {
        if !self.symbols.contains_symbol(symbol) {
            return Err(CanonicalNameResolutionError::InvalidHostSymbol(symbol));
        }
        Ok(())
    }

    fn validate_optional_symbol(
        &self,
        symbol: Option<SemanticSymbolId>,
    ) -> Result<(), CanonicalNameResolutionError> {
        if let Some(symbol) = symbol {
            self.validate_symbol(symbol)?;
        }
        Ok(())
    }

    fn validate_table(&self, table: SymbolTableId) -> Result<(), CanonicalNameResolutionError> {
        if !self.symbols.contains_symbol_table(table) {
            return Err(CanonicalNameResolutionError::InvalidHostTable(table));
        }
        Ok(())
    }

    fn reject_jsdoc(&self, node: NodeId) -> Result<(), CanonicalNameResolutionError> {
        let record = self.node(node);
        if is_jsdoc_kind(record.kind) || record.flags.0 & NODE_FLAG_JSDOC != 0 {
            return Err(CanonicalNameResolutionError::JsDocDeferred(
                self.node_ref(node),
            ));
        }
        Ok(())
    }

    fn error(&mut self, location: NodeRef, code: u32, arguments: impl IntoIterator<Item = String>) {
        let message = message_by_code(code).expect("pinned name-resolver diagnostic exists");
        self.host
            .error(location, Diagnostic::with_arguments(message, arguments));
    }

    fn node_ref(&self, node: NodeId) -> NodeRef {
        NodeRef::new(self.arena.id(), self.bound.file_id(), node)
    }

    fn node(&self, node: NodeId) -> &ts_ast::Node {
        self.arena
            .get(node)
            .expect("bound AST node is present in its arena")
    }

    fn kind(&self, node: NodeId) -> SyntaxKind {
        self.node(node).kind
    }

    fn is_synthesized(&self, node: NodeId) -> bool {
        self.node(node).flags.0 & NODE_FLAG_SYNTHESIZED != 0
    }
}

fn is_module_or_enum_declaration(arena: &NodeArena, node: NodeId) -> bool {
    arena.get(node).is_some_and(|node| {
        matches!(
            node.kind,
            SyntaxKind::ModuleDeclaration | SyntaxKind::EnumDeclaration
        )
    })
}

fn declaration_name(arena: &NodeArena, node: NodeId) -> Option<NodeId> {
    match &arena.get(node)?.data {
        NodeData::BindingElement(data) => data.name,
        NodeData::ClassDeclaration(data) => data.name,
        NodeData::ClassExpression(data) => data.name,
        NodeData::EnumDeclaration(data) => Some(data.name),
        NodeData::FunctionDeclaration(data) => data.name,
        NodeData::FunctionExpression(data) => data.name,
        NodeData::GetAccessorDeclaration(data) => Some(data.name),
        NodeData::InterfaceDeclaration(data) => Some(data.name),
        NodeData::MethodDeclaration(data) => Some(data.name),
        NodeData::ModuleDeclaration(data) => Some(data.name),
        NodeData::ParameterDeclaration(data) => Some(data.name),
        NodeData::PropertyAssignment(data) => Some(data.name),
        NodeData::PropertyDeclaration(data) => Some(data.name),
        NodeData::SetAccessorDeclaration(data) => Some(data.name),
        NodeData::TypeAliasDeclaration(data) => Some(data.name),
        NodeData::TypeParameterDeclaration(data) => Some(data.name),
        _ => None,
    }
}

fn identifier_text(arena: &NodeArena, node: NodeId) -> Option<&str> {
    match &arena.get(node)?.data {
        NodeData::Identifier(identifier) => Some(&identifier.text),
        _ => None,
    }
}

fn modifier_list(data: &NodeData) -> Option<&ModifierList> {
    match data {
        NodeData::ArrowFunction(data) => data.modifiers.as_ref(),
        NodeData::BinaryExpression(data) => data.modifiers.as_ref(),
        NodeData::ClassDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ClassExpression(data) => data.modifiers.as_ref(),
        NodeData::ClassStaticBlockDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ConstructorDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ConstructorTypeNode(data) => data.modifiers.as_ref(),
        NodeData::EnumDeclaration(data) => data.modifiers.as_ref(),
        NodeData::EnumMember(data) => data.modifiers.as_ref(),
        NodeData::ExportAssignment(data) => data.modifiers.as_ref(),
        NodeData::ExportDeclaration(data) => data.modifiers.as_ref(),
        NodeData::FunctionDeclaration(data) => data.modifiers.as_ref(),
        NodeData::FunctionExpression(data) => data.modifiers.as_ref(),
        NodeData::FunctionTypeNode(data) => data.modifiers.as_ref(),
        NodeData::GetAccessorDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ImportDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ImportEqualsDeclaration(data) => data.modifiers.as_ref(),
        NodeData::IndexSignatureDeclaration(data) => data.modifiers.as_ref(),
        NodeData::InterfaceDeclaration(data) => data.modifiers.as_ref(),
        NodeData::MethodDeclaration(data) => data.modifiers.as_ref(),
        NodeData::MethodSignatureDeclaration(data) => data.modifiers.as_ref(),
        NodeData::MissingDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ModuleDeclaration(data) => data.modifiers.as_ref(),
        NodeData::NamespaceExportDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ParameterDeclaration(data) => data.modifiers.as_ref(),
        NodeData::PropertyAssignment(data) => data.modifiers.as_ref(),
        NodeData::PropertyDeclaration(data) => data.modifiers.as_ref(),
        NodeData::PropertySignatureDeclaration(data) => data.modifiers.as_ref(),
        NodeData::SetAccessorDeclaration(data) => data.modifiers.as_ref(),
        NodeData::ShorthandPropertyAssignment(data) => data.modifiers.as_ref(),
        NodeData::TypeAliasDeclaration(data) => data.modifiers.as_ref(),
        NodeData::TypeParameterDeclaration(data) => data.modifiers.as_ref(),
        NodeData::VariableStatement(data) => data.modifiers.as_ref(),
        _ => None,
    }
}

fn has_syntactic_modifier(arena: &NodeArena, node: NodeId, modifier: SyntaxKind) -> bool {
    arena
        .get(node)
        .and_then(|node| modifier_list(&node.data))
        .is_some_and(|modifiers| {
            modifiers
                .list
                .nodes
                .iter()
                .any(|node| arena.get(*node).is_some_and(|node| node.kind == modifier))
        })
}

fn is_function_like(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::FunctionDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::Constructor
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::FunctionExpression
            | SyntaxKind::ArrowFunction
            | SyntaxKind::MethodSignature
            | SyntaxKind::CallSignature
            | SyntaxKind::ConstructSignature
            | SyntaxKind::IndexSignature
            | SyntaxKind::FunctionType
            | SyntaxKind::ConstructorType
    )
}

fn is_function_like_declaration(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::FunctionDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::Constructor
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::FunctionExpression
            | SyntaxKind::ArrowFunction
    )
}

fn function_body(arena: &NodeArena, node: NodeId) -> Option<NodeId> {
    match &arena.get(node)?.data {
        NodeData::ArrowFunction(data) => Some(data.body),
        NodeData::ConstructorDeclaration(data) => data.body,
        NodeData::FunctionDeclaration(data) => data.body,
        NodeData::FunctionExpression(data) => Some(data.body),
        NodeData::GetAccessorDeclaration(data) => data.body,
        NodeData::MethodDeclaration(data) => data.body,
        NodeData::SetAccessorDeclaration(data) => data.body,
        _ => None,
    }
}

fn function_type(arena: &NodeArena, node: NodeId) -> Option<NodeId> {
    match &arena.get(node)?.data {
        NodeData::ArrowFunction(data) => data.type_,
        NodeData::CallSignatureDeclaration(data) => data.type_,
        NodeData::ConstructSignatureDeclaration(data) => data.type_,
        NodeData::ConstructorDeclaration(data) => data.type_,
        NodeData::ConstructorTypeNode(data) => data.type_,
        NodeData::FunctionDeclaration(data) => data.type_,
        NodeData::FunctionExpression(data) => data.type_,
        NodeData::FunctionTypeNode(data) => data.type_,
        NodeData::GetAccessorDeclaration(data) => data.type_,
        NodeData::IndexSignatureDeclaration(data) => Some(data.type_),
        NodeData::MethodDeclaration(data) => data.type_,
        NodeData::MethodSignatureDeclaration(data) => data.type_,
        NodeData::SetAccessorDeclaration(data) => data.type_,
        _ => None,
    }
}

fn function_parameters(arena: &NodeArena, node: NodeId) -> Option<&[NodeId]> {
    let parameters = match &arena.get(node)?.data {
        NodeData::ArrowFunction(data) => &data.parameters,
        NodeData::CallSignatureDeclaration(data) => &data.parameters,
        NodeData::ConstructSignatureDeclaration(data) => &data.parameters,
        NodeData::ConstructorDeclaration(data) => &data.parameters,
        NodeData::ConstructorTypeNode(data) => &data.parameters,
        NodeData::FunctionDeclaration(data) => &data.parameters,
        NodeData::FunctionExpression(data) => &data.parameters,
        NodeData::FunctionTypeNode(data) => &data.parameters,
        NodeData::GetAccessorDeclaration(data) => &data.parameters,
        NodeData::IndexSignatureDeclaration(data) => &data.parameters,
        NodeData::MethodDeclaration(data) => &data.parameters,
        NodeData::MethodSignatureDeclaration(data) => &data.parameters,
        NodeData::SetAccessorDeclaration(data) => &data.parameters,
        _ => return None,
    };
    Some(&parameters.nodes)
}

fn function_asterisk_token(arena: &NodeArena, node: NodeId) -> Option<NodeId> {
    match &arena.get(node)?.data {
        NodeData::ArrowFunction(data) => data.asterisk_token,
        NodeData::ConstructorDeclaration(data) => data.asterisk_token,
        NodeData::FunctionDeclaration(data) => data.asterisk_token,
        NodeData::FunctionExpression(data) => data.asterisk_token,
        NodeData::GetAccessorDeclaration(data) => data.asterisk_token,
        NodeData::MethodDeclaration(data) => data.asterisk_token,
        NodeData::SetAccessorDeclaration(data) => data.asterisk_token,
        _ => None,
    }
}

fn is_class_like(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::ClassDeclaration | SyntaxKind::ClassExpression
    )
}

fn is_class_element(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Constructor
            | SyntaxKind::PropertyDeclaration
            | SyntaxKind::MethodDeclaration
            | SyntaxKind::GetAccessor
            | SyntaxKind::SetAccessor
            | SyntaxKind::IndexSignature
            | SyntaxKind::ClassStaticBlockDeclaration
            | SyntaxKind::SemicolonClassElement
    )
}

fn is_static(arena: &NodeArena, node: NodeId) -> bool {
    arena
        .get(node)
        .is_some_and(|node| node.kind == SyntaxKind::ClassStaticBlockDeclaration)
        || arena
            .get(node)
            .is_some_and(|node| is_class_element(node.kind))
            && has_syntactic_modifier(arena, node, SyntaxKind::StaticKeyword)
}

fn is_binding_pattern(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::ObjectBindingPattern | SyntaxKind::ArrayBindingPattern
    )
}

fn is_ambient_module(arena: &NodeArena, node: NodeId) -> bool {
    let Some(NodeData::ModuleDeclaration(module)) = arena.get(node).map(|node| &node.data) else {
        return false;
    };
    module.keyword == SyntaxKind::GlobalKeyword
        || arena
            .get(module.name)
            .is_some_and(|name| name.kind == SyntaxKind::StringLiteral)
}

fn is_global_scope_augmentation(arena: &NodeArena, node: NodeId) -> bool {
    matches!(
        arena.get(node).map(|node| &node.data),
        Some(NodeData::ModuleDeclaration(module)) if module.keyword == SyntaxKind::GlobalKeyword
    )
}

fn find_constructor(arena: &NodeArena, class: NodeId) -> Option<NodeId> {
    let members = match &arena.get(class)?.data {
        NodeData::ClassDeclaration(class) => &class.members.nodes,
        NodeData::ClassExpression(class) => &class.members.nodes,
        _ => return None,
    };
    members.iter().copied().find(|member| {
        arena
            .get(*member)
            .is_some_and(|member| member.kind == SyntaxKind::Constructor)
    })
}

fn is_const_assertion(arena: &NodeArena, node: NodeId) -> bool {
    let type_node = match &arena.get(node).map(|node| &node.data) {
        Some(NodeData::AsExpression(assertion)) => assertion.type_,
        Some(NodeData::TypeAssertion(assertion)) => assertion.type_,
        _ => return false,
    };
    let Some(NodeData::TypeReferenceNode(reference)) = arena.get(type_node).map(|node| &node.data)
    else {
        return false;
    };
    reference
        .type_arguments
        .as_ref()
        .is_none_or(|types| types.nodes.is_empty())
        && identifier_text(arena, reference.type_name) == Some("const")
}

fn is_nullish_coalesce(arena: &NodeArena, node: NodeId) -> bool {
    let Some(NodeData::BinaryExpression(binary)) = arena.get(node).map(|node| &node.data) else {
        return false;
    };
    arena
        .get(binary.operator_token)
        .is_some_and(|operator| operator.kind == SyntaxKind::QuestionQuestionToken)
}

/// Reconstructs the pinned parser's `NodeFlagsOptionalChain` from the exact
/// receiver/qdot shape. The Rust parser does not yet persist that derived bit.
fn is_optional_chain(arena: &NodeArena, node: NodeId) -> bool {
    match arena.get(node).map(|node| &node.data) {
        Some(NodeData::PropertyAccessExpression(access)) => {
            access.question_dot_token.is_some() || is_optional_chain(arena, access.expression)
        }
        Some(NodeData::ElementAccessExpression(access)) => {
            access.question_dot_token.is_some() || is_optional_chain(arena, access.expression)
        }
        Some(NodeData::CallExpression(call)) => {
            call.question_dot_token.is_some() || is_optional_chain(arena, call.expression)
        }
        Some(NodeData::NonNullExpression(expression)) => {
            is_optional_chain(arena, expression.expression)
        }
        _ => false,
    }
}

fn is_type_node_kind(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::AnyKeyword
            | SyntaxKind::UnknownKeyword
            | SyntaxKind::NumberKeyword
            | SyntaxKind::BigIntKeyword
            | SyntaxKind::ObjectKeyword
            | SyntaxKind::BooleanKeyword
            | SyntaxKind::StringKeyword
            | SyntaxKind::SymbolKeyword
            | SyntaxKind::VoidKeyword
            | SyntaxKind::UndefinedKeyword
            | SyntaxKind::NeverKeyword
            | SyntaxKind::IntrinsicKeyword
            | SyntaxKind::ExpressionWithTypeArguments
    ) || (SyntaxKind::TypePredicate as u16..=SyntaxKind::ImportType as u16).contains(&(kind as u16))
}

fn immediately_invoked_function(arena: &NodeArena, function: NodeId) -> Option<NodeId> {
    if !matches!(
        arena.get(function).map(|node| node.kind),
        Some(SyntaxKind::FunctionExpression | SyntaxKind::ArrowFunction)
    ) {
        return None;
    }
    let mut previous = function;
    let mut parent = arena.get(function)?.parent?;
    while arena
        .get(parent)
        .is_some_and(|parent| parent.kind == SyntaxKind::ParenthesizedExpression)
    {
        previous = parent;
        parent = arena.get(parent)?.parent?;
    }
    matches!(
        arena.get(parent).map(|parent| &parent.data),
        Some(NodeData::CallExpression(call)) if call.expression == previous
    )
    .then_some(parent)
}

fn is_self_reference_location(
    arena: &NodeArena,
    node: NodeId,
    last_location: Option<NodeId>,
) -> bool {
    match arena.get(node).map(|node| node.kind) {
        Some(SyntaxKind::Parameter) => {
            last_location.is_some() && declaration_name(arena, node) == last_location
        }
        Some(
            SyntaxKind::FunctionDeclaration
            | SyntaxKind::ClassDeclaration
            | SyntaxKind::InterfaceDeclaration
            | SyntaxKind::EnumDeclaration
            | SyntaxKind::TypeAliasDeclaration
            | SyntaxKind::ModuleDeclaration,
        ) => true,
        _ => false,
    }
}

fn is_jsdoc_kind(kind: SyntaxKind) -> bool {
    (SyntaxKind::JsDocTypeExpression as u16..=SyntaxKind::JsDocImportTag as u16)
        .contains(&(kind as u16))
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
    use ts_diagnostics::{Diagnostic, Message, message_by_code};
    use ts_options::ScriptTarget;
    use ts_parser::{ParseResult, parse_javascript_source_file, parse_source_file};

    use super::{
        CanonicalNameResolutionError, CanonicalNameResolver, CanonicalNameResolverHost,
        CanonicalNameResolverOptions, CanonicalResolvedName, CanonicalScopeChangeState,
    };
    use crate::{
        BindingPhase, CanonicalBinder, CanonicalModuleState, CanonicalProgramBindings,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName, EscapedNameRef,
        SemanticSymbolId, SymbolData, SymbolFlags, SymbolStore, SymbolTableId,
    };

    const FILE: FileId = FileId::new(401);

    struct BoundSource {
        parsed: ParseResult,
        bindings: CanonicalProgramBindings,
    }

    fn bind(source: &str, module_state: CanonicalModuleState) -> BoundSource {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                FILE,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/name-resolver.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    module_state,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, FILE)
            .unwrap();
        BoundSource {
            parsed,
            bindings: binder.finish(),
        }
    }

    fn node_ref(source: &BoundSource, node: NodeId) -> NodeRef {
        NodeRef::new(source.parsed.arena.id(), FILE, node)
    }

    fn bound(source: &BoundSource) -> &crate::BoundFile {
        source.bindings.file(FILE).unwrap()
    }

    fn identifier_in(source: &BoundSource, fragment: &str, name: &str) -> NodeId {
        let text = source.parsed.arena.source_text().unwrap();
        let fragment_start = text.find(fragment).expect("test fragment is present");
        let name_start = fragment
            .rfind(name)
            .map(|offset| fragment_start + offset)
            .expect("name occurs in test fragment");
        source
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(
                    &record.data,
                    NodeData::Identifier(identifier)
                        if identifier.text == name
                            && record.range.start.get() as usize == name_start
                )
                .then_some(node)
            })
            .expect("identifier starts at the selected fragment offset")
    }

    fn first_kind(source: &BoundSource, kind: SyntaxKind) -> NodeId {
        source
            .parsed
            .arena
            .iter()
            .find_map(|(node, record)| (record.kind == kind).then_some(node))
            .expect("test node kind is present")
    }

    fn declaration_symbol(source: &BoundSource, node: NodeId) -> SemanticSymbolId {
        bound(source).symbol(node_ref(source, node)).unwrap()
    }

    fn table_symbol(source: &BoundSource, table: SymbolTableId, name: &str) -> SemanticSymbolId {
        source
            .bindings
            .symbol_store()
            .symbol_table(table)
            .unwrap()
            .get_source(name)
            .unwrap()
    }

    fn not_found_message() -> &'static Message {
        message_by_code(2304).unwrap()
    }

    #[derive(Default)]
    struct TestHost {
        options: CanonicalNameResolverOptions,
        declaration_symbols: HashMap<NodeRef, SemanticSymbolId>,
        local_symbols: HashMap<NodeRef, SemanticSymbolId>,
        globals: Option<SymbolTableId>,
        arguments: Option<SemanticSymbolId>,
        lookup_override: Option<SemanticSymbolId>,
        foreign_kinds: HashMap<NodeRef, SyntaxKind>,
        foreign_parents: HashMap<NodeRef, NodeRef>,
        foreign_modifiers: HashMap<(NodeRef, SyntaxKind), bool>,
        diagnostics: Vec<(NodeRef, Diagnostic)>,
        referenced: Vec<(SemanticSymbolId, SymbolFlags)>,
        cache: HashMap<NodeRef, CanonicalScopeChangeState>,
        failed: Vec<(NodeRef, String, SymbolFlags, u32)>,
        succeeded: Vec<CanonicalResolvedName>,
        invalid_property_result: bool,
    }

    impl TestHost {
        fn for_source(source: &BoundSource) -> Self {
            let file = bound(source);
            let mut host = Self {
                globals: file.locals(file.source_file()),
                ..Self::default()
            };
            for node in file.traversal_order() {
                if let Some(symbol) = file.symbol(node) {
                    host.declaration_symbols.insert(node, symbol);
                    host.arguments.get_or_insert(symbol);
                }
                if let Some(symbol) = file.local_symbol(node) {
                    host.local_symbols.insert(node, symbol);
                }
            }
            host
        }
    }

    impl CanonicalNameResolverHost for TestHost {
        fn compiler_options(&self) -> CanonicalNameResolverOptions {
            self.options
        }

        fn get_symbol_of_declaration(&mut self, declaration: NodeRef) -> Option<SemanticSymbolId> {
            self.declaration_symbols.get(&declaration).copied()
        }

        fn get_local_symbol_of_declaration(
            &mut self,
            declaration: NodeRef,
        ) -> Option<SemanticSymbolId> {
            self.local_symbols.get(&declaration).copied()
        }

        fn lookup(
            &mut self,
            store: &SymbolStore,
            symbols: SymbolTableId,
            name: EscapedNameRef<'_>,
            meaning: SymbolFlags,
        ) -> Option<SemanticSymbolId> {
            if let Some(symbol) = self.lookup_override {
                return Some(symbol);
            }
            if meaning == SymbolFlags::NONE {
                return None;
            }
            let symbol = store.symbol_table(symbols)?.get(name)?;
            store
                .symbol(symbol)?
                .flags()
                .intersects(meaning)
                .then_some(symbol)
        }

        fn globals(&self) -> Option<SymbolTableId> {
            self.globals
        }

        fn arguments_symbol(&mut self, _store: &SymbolStore) -> Option<SemanticSymbolId> {
            self.arguments
        }

        fn foreign_declaration_kind(&mut self, declaration: NodeRef) -> Option<SyntaxKind> {
            self.foreign_kinds.get(&declaration).copied()
        }

        fn foreign_declaration_parent(&mut self, declaration: NodeRef) -> Option<NodeRef> {
            self.foreign_parents.get(&declaration).copied()
        }

        fn foreign_declaration_has_syntactic_modifier(
            &mut self,
            declaration: NodeRef,
            modifier: SyntaxKind,
        ) -> Option<bool> {
            self.foreign_modifiers
                .get(&(declaration, modifier))
                .copied()
        }

        fn error(&mut self, location: NodeRef, diagnostic: Diagnostic) {
            self.diagnostics.push((location, diagnostic));
        }

        fn symbol_referenced(&mut self, symbol: SemanticSymbolId, meaning: SymbolFlags) {
            self.referenced.push((symbol, meaning));
        }

        fn set_requires_scope_change_cache(
            &mut self,
            declaration: NodeRef,
            value: CanonicalScopeChangeState,
        ) {
            self.cache.insert(declaration, value);
        }

        fn get_requires_scope_change_cache(
            &mut self,
            declaration: NodeRef,
        ) -> CanonicalScopeChangeState {
            self.cache.get(&declaration).copied().unwrap_or_default()
        }

        fn on_property_with_invalid_initializer(
            &mut self,
            _location: NodeRef,
            _name: &str,
            _declaration: NodeRef,
            _result: Option<SemanticSymbolId>,
        ) -> bool {
            self.invalid_property_result
        }

        fn on_failed_to_resolve_symbol(
            &mut self,
            location: NodeRef,
            name: &str,
            meaning: SymbolFlags,
            name_not_found_message: &'static Message,
        ) {
            self.failed.push((
                location,
                name.to_owned(),
                meaning,
                name_not_found_message.code(),
            ));
        }

        fn on_successfully_resolved_symbol(&mut self, resolved: CanonicalResolvedName) {
            self.succeeded.push(resolved);
        }
    }

    fn resolve(
        source: &BoundSource,
        host: &mut TestHost,
        location: NodeId,
        name: &str,
        meaning: SymbolFlags,
    ) -> Result<Option<SemanticSymbolId>, CanonicalNameResolutionError> {
        CanonicalNameResolver::new(
            &source.parsed.arena,
            bound(source),
            source.bindings.symbol_store(),
            host,
        )?
        .resolve(
            node_ref(source, location),
            name,
            meaning,
            Some(not_found_message()),
            true,
            false,
        )
    }

    #[test]
    fn function_scope_restrictions_preserve_type_parameters_and_outer_parameter_values() {
        let source = bind(
            r"
type GlobalOnly = string;
const shadow = 0;
function plain<T>(parameter: T = shadow): T {
    var shadow = 1;
    type BodyOnly = T;
    return parameter;
}
",
            CanonicalModuleState::Script,
        );
        let function = first_kind(&source, SyntaxKind::FunctionDeclaration);
        let function_locals = bound(&source).locals(node_ref(&source, function)).unwrap();
        let type_parameter = table_symbol(&source, function_locals, "T");
        let body_shadow = table_symbol(&source, function_locals, "shadow");
        let global_table = bound(&source).locals(bound(&source).source_file()).unwrap();
        let global_shadow = table_symbol(&source, global_table, "shadow");
        let parameter_type = identifier_in(&source, "parameter: T", "T");
        let parameter_initializer = identifier_in(&source, "T = shadow", "shadow");
        let mut host = TestHost::for_source(&source);

        assert_eq!(
            resolve(&source, &mut host, parameter_type, "T", SymbolFlags::TYPE,),
            Ok(Some(type_parameter))
        );
        assert_eq!(
            resolve(
                &source,
                &mut host,
                parameter_type,
                "BodyOnly",
                SymbolFlags::TYPE,
            ),
            Ok(None)
        );
        assert_eq!(
            resolve(
                &source,
                &mut host,
                parameter_initializer,
                "shadow",
                SymbolFlags::VALUE,
            ),
            Ok(Some(global_shadow))
        );
        assert_ne!(body_shadow, global_shadow);
        assert_eq!(
            host.cache.get(&node_ref(&source, function)),
            Some(&CanonicalScopeChangeState::False)
        );
    }

    #[test]
    fn parameter_scope_change_uses_exact_es2020_optional_chain_threshold() {
        let source = bind(
            r"
const shadow = 0;
declare const input: { value: number } | undefined;
function lowered(first = input?.value, second = shadow) {
    var shadow = 1;
}
",
            CanonicalModuleState::Script,
        );
        let function = first_kind(&source, SyntaxKind::FunctionDeclaration);
        let local = table_symbol(
            &source,
            bound(&source).locals(node_ref(&source, function)).unwrap(),
            "shadow",
        );
        let global = table_symbol(
            &source,
            bound(&source).locals(bound(&source).source_file()).unwrap(),
            "shadow",
        );
        let use_site = identifier_in(&source, "second = shadow", "shadow");

        let mut es2019 = TestHost::for_source(&source);
        es2019.options.emit_target = ScriptTarget::Es2019;
        assert_eq!(
            resolve(&source, &mut es2019, use_site, "shadow", SymbolFlags::VALUE,),
            Ok(Some(local))
        );
        assert_eq!(
            es2019.cache.get(&node_ref(&source, function)),
            Some(&CanonicalScopeChangeState::True)
        );

        let mut es2020 = TestHost::for_source(&source);
        es2020.options.emit_target = ScriptTarget::Es2020;
        assert_eq!(
            resolve(&source, &mut es2020, use_site, "shadow", SymbolFlags::VALUE,),
            Ok(Some(global))
        );
        assert_eq!(
            es2020.cache.get(&node_ref(&source, function)),
            Some(&CanonicalScopeChangeState::False)
        );
    }

    #[test]
    fn parameter_scope_change_uses_exact_es2017_object_rest_threshold() {
        let source = bind(
            r"
const shadow = 0;
declare const input: { value: number };
function lowered({ ...rest } = input, second = shadow) {
    var shadow = 1;
}
",
            CanonicalModuleState::Script,
        );
        let function = first_kind(&source, SyntaxKind::FunctionDeclaration);
        let local = table_symbol(
            &source,
            bound(&source).locals(node_ref(&source, function)).unwrap(),
            "shadow",
        );
        let global = table_symbol(
            &source,
            bound(&source).locals(bound(&source).source_file()).unwrap(),
            "shadow",
        );
        let use_site = identifier_in(&source, "second = shadow", "shadow");

        let mut es2016 = TestHost::for_source(&source);
        es2016.options.emit_target = ScriptTarget::Es2016;
        assert_eq!(
            resolve(&source, &mut es2016, use_site, "shadow", SymbolFlags::VALUE,),
            Ok(Some(local))
        );

        let mut es2017 = TestHost::for_source(&source);
        es2017.options.emit_target = ScriptTarget::Es2017;
        assert_eq!(
            resolve(&source, &mut es2017, use_site, "shadow", SymbolFlags::VALUE,),
            Ok(Some(global))
        );
    }

    #[test]
    fn parameter_scope_change_uses_exact_standard_class_fields_rule() {
        let source = bind(
            r"
const shadow = 0;
function lowered(first = class { static field = shadow }, second = shadow) {
    var shadow = 1;
}
",
            CanonicalModuleState::Script,
        );
        let function = first_kind(&source, SyntaxKind::FunctionDeclaration);
        let local = table_symbol(
            &source,
            bound(&source).locals(node_ref(&source, function)).unwrap(),
            "shadow",
        );
        let global = table_symbol(
            &source,
            bound(&source).locals(bound(&source).source_file()).unwrap(),
            "shadow",
        );
        let use_site = identifier_in(&source, "second = shadow", "shadow");

        let mut es2021 = TestHost::for_source(&source);
        es2021.options.emit_target = ScriptTarget::Es2021;
        assert_eq!(
            resolve(&source, &mut es2021, use_site, "shadow", SymbolFlags::VALUE,),
            Ok(Some(local))
        );

        let mut es2022 = TestHost::for_source(&source);
        es2022.options.emit_target = ScriptTarget::Es2022;
        assert_eq!(
            resolve(&source, &mut es2022, use_site, "shadow", SymbolFlags::VALUE,),
            Ok(Some(global))
        );

        let mut legacy_fields = TestHost::for_source(&source);
        legacy_fields.options.emit_target = ScriptTarget::Es2022;
        legacy_fields.options.use_define_for_class_fields = Some(false);
        assert_eq!(
            resolve(
                &source,
                &mut legacy_fields,
                use_site,
                "shadow",
                SymbolFlags::VALUE,
            ),
            Ok(Some(local))
        );
    }

    #[test]
    fn conditional_infer_parameter_is_visible_only_in_true_branch() {
        let source = bind(
            "type Result<T> = T extends infer U ? U : U;",
            CanonicalModuleState::Script,
        );
        let infer = first_kind(&source, SyntaxKind::InferType);
        let infer_parameter = match &source.parsed.arena.get(infer).unwrap().data {
            NodeData::InferTypeNode(infer) => infer.type_parameter,
            _ => unreachable!(),
        };
        let expected = declaration_symbol(&source, infer_parameter);
        let true_use = identifier_in(&source, "? U", "U");
        let false_use = identifier_in(&source, ": U", "U");
        let mut host = TestHost::for_source(&source);

        assert_eq!(
            resolve(&source, &mut host, true_use, "U", SymbolFlags::TYPE,),
            Ok(Some(expected))
        );
        assert_eq!(
            resolve(&source, &mut host, false_use, "U", SymbolFlags::TYPE,),
            Ok(None)
        );
    }

    #[test]
    fn merged_namespace_exports_are_visible_but_pure_reexports_are_not() {
        let source = bind(
            r"
namespace N {
    export const first = 1;
    export { first as alias };
}
namespace N {
    export function good() { return first; }
    export function bad() { return alias; }
}
",
            CanonicalModuleState::Script,
        );
        let namespace = first_kind(&source, SyntaxKind::ModuleDeclaration);
        let namespace_symbol = declaration_symbol(&source, namespace);
        let exports = source
            .bindings
            .symbol_store()
            .symbol(namespace_symbol)
            .unwrap()
            .exports()
            .unwrap();
        let first = table_symbol(&source, exports, "first");
        let first_use = identifier_in(&source, "return first", "first");
        let alias_use = identifier_in(&source, "return alias", "alias");
        let mut host = TestHost::for_source(&source);

        assert_eq!(
            resolve(&source, &mut host, first_use, "first", SymbolFlags::VALUE,),
            Ok(Some(first))
        );
        assert_eq!(
            resolve(&source, &mut host, alias_use, "alias", SymbolFlags::VALUE,),
            Ok(None)
        );
    }

    #[test]
    fn external_reexport_property_name_jumps_over_source_locals() {
        let source = bind(
            r#"
const remote = 1;
export { remote as forwarded } from "pkg";
"#,
            CanonicalModuleState::External,
        );
        let property = identifier_in(&source, "{ remote as", "remote");
        let source_locals = bound(&source).locals(bound(&source).source_file()).unwrap();
        assert!(
            source
                .bindings
                .symbol_store()
                .symbol_table(source_locals)
                .unwrap()
                .get_source("remote")
                .is_some()
        );
        let mut host = TestHost::for_source(&source);
        host.globals = None;
        assert_eq!(
            resolve(&source, &mut host, property, "remote", SymbolFlags::VALUE,),
            Ok(None)
        );
    }

    #[test]
    fn class_type_parameter_restrictions_report_exact_diagnostics() {
        let source = bind(
            r"
type T = string;
declare function make(value: unknown): any;
declare function key<V>(): string;
class Box<T> {
    value!: T;
    static bad!: T;
    [key<T>()]!: number;
}
class Derived<T> extends make(T) {}
",
            CanonicalModuleState::Script,
        );
        let classes = source
            .parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::ClassDeclaration).then_some(node)
            })
            .collect::<Vec<_>>();
        let box_symbol = declaration_symbol(&source, classes[0]);
        let box_type_parameter = table_symbol(
            &source,
            source
                .bindings
                .symbol_store()
                .symbol(box_symbol)
                .unwrap()
                .members()
                .unwrap(),
            "T",
        );
        let instance = identifier_in(&source, "value!: T", "T");
        let static_use = identifier_in(&source, "static bad!: T", "T");
        let computed = identifier_in(&source, "key<T>()", "T");
        let heritage = identifier_in(&source, "extends make(T)", "T");
        let mut host = TestHost::for_source(&source);

        assert_eq!(
            resolve(&source, &mut host, instance, "T", SymbolFlags::TYPE,),
            Ok(Some(box_type_parameter))
        );
        assert_eq!(
            resolve(&source, &mut host, static_use, "T", SymbolFlags::TYPE,),
            Ok(None)
        );
        assert_eq!(host.diagnostics.last().unwrap().1.message.code(), 2302);
        assert_eq!(
            resolve(&source, &mut host, computed, "T", SymbolFlags::TYPE,),
            Ok(None)
        );
        assert_eq!(host.diagnostics.last().unwrap().1.message.code(), 2467);
        assert_eq!(
            resolve(&source, &mut host, heritage, "T", SymbolFlags::TYPE,),
            Ok(None)
        );
        assert_eq!(host.diagnostics.last().unwrap().1.message.code(), 2562);
    }

    #[test]
    fn arguments_decorators_and_named_expressions_follow_pinned_scopes() {
        let source = bind(
            r"
const decorate = () => {};
class C {
    method(@decorate value: number, decorate: string) {
        return arguments;
    }
}
const namedClass = class Inner { value: Inner };
const namedFunction = function inner() { return inner; };
",
            CanonicalModuleState::Script,
        );
        let globals = bound(&source).locals(bound(&source).source_file()).unwrap();
        let decorate = table_symbol(&source, globals, "decorate");
        let decorator_use = identifier_in(&source, "@decorate", "decorate");
        let arguments_use = identifier_in(&source, "return arguments", "arguments");
        let class_use = identifier_in(&source, "value: Inner", "Inner");
        let function_use = identifier_in(&source, "return inner", "inner");
        let class_expression = first_kind(&source, SyntaxKind::ClassExpression);
        let function_expression = first_kind(&source, SyntaxKind::FunctionExpression);
        let class_symbol = declaration_symbol(&source, class_expression);
        let function_symbol = declaration_symbol(&source, function_expression);
        let mut host = TestHost::for_source(&source);
        host.arguments = Some(decorate);

        assert_eq!(
            resolve(
                &source,
                &mut host,
                decorator_use,
                "decorate",
                SymbolFlags::VALUE,
            ),
            Ok(Some(decorate))
        );
        assert_eq!(
            resolve(
                &source,
                &mut host,
                arguments_use,
                "arguments",
                SymbolFlags::VALUE,
            ),
            Ok(Some(decorate))
        );
        assert_eq!(
            resolve(&source, &mut host, class_use, "Inner", SymbolFlags::CLASS,),
            Ok(Some(class_symbol))
        );
        assert_eq!(
            resolve(
                &source,
                &mut host,
                function_use,
                "inner",
                SymbolFlags::FUNCTION,
            ),
            Ok(Some(function_symbol))
        );
    }

    #[test]
    fn success_callback_tracks_binding_initializer_and_deferred_context() {
        let source = bind(
            r"
const outer = 1;
function associated({ value = outer } = {}) {}
const deferred = function () { return outer; };
const immediate = (function () { return outer; })();
",
            CanonicalModuleState::Script,
        );
        let binding_use = identifier_in(&source, "value = outer", "outer");
        let deferred_use = identifier_in(&source, "deferred = function () { return outer", "outer");
        let immediate_use =
            identifier_in(&source, "immediate = (function () { return outer", "outer");
        let binding = source
            .parsed
            .arena
            .get(binding_use)
            .unwrap()
            .parent
            .expect("initializer belongs to a binding element");
        assert_eq!(
            source.parsed.arena.get(binding).unwrap().kind,
            SyntaxKind::BindingElement
        );
        let mut host = TestHost::for_source(&source);

        resolve(&source, &mut host, binding_use, "outer", SymbolFlags::VALUE).unwrap();
        assert_eq!(
            host.succeeded
                .last()
                .unwrap()
                .associated_declaration_for_containing_initializer_or_binding_name,
            Some(node_ref(&source, binding))
        );
        resolve(
            &source,
            &mut host,
            deferred_use,
            "outer",
            SymbolFlags::VALUE,
        )
        .unwrap();
        assert!(host.succeeded.last().unwrap().within_deferred_context);
        resolve(
            &source,
            &mut host,
            immediate_use,
            "outer",
            SymbolFlags::VALUE,
        )
        .unwrap();
        assert!(!host.succeeded.last().unwrap().within_deferred_context);
    }

    #[test]
    fn provenance_and_host_failures_are_rejected_before_notifications() {
        let source = bind(
            "const value = 1; function read() { return value; }",
            CanonicalModuleState::Script,
        );
        let use_site = identifier_in(&source, "return value", "value");
        let mut foreign_store = SymbolStore::new();
        let foreign_symbol = foreign_store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
                EscapedName::source("foreign"),
            ))
            .unwrap();
        let foreign_table = foreign_store.alloc_symbol_table();

        let mut host = TestHost::for_source(&source);
        host.lookup_override = Some(foreign_symbol);
        assert_eq!(
            resolve(&source, &mut host, use_site, "value", SymbolFlags::VALUE,),
            Err(CanonicalNameResolutionError::InvalidHostSymbol(
                foreign_symbol
            ))
        );
        assert!(host.referenced.is_empty());
        assert!(host.succeeded.is_empty());
        assert!(host.failed.is_empty());

        let mut host = TestHost::for_source(&source);
        host.globals = Some(foreign_table);
        assert_eq!(
            resolve(&source, &mut host, use_site, "missing", SymbolFlags::VALUE,),
            Err(CanonicalNameResolutionError::InvalidHostTable(
                foreign_table
            ))
        );
        assert!(host.failed.is_empty());

        let mut host = TestHost::for_source(&source);
        let foreign_location = NodeRef::new(source.parsed.arena.id(), FileId::new(404), use_site);
        let mut resolver = CanonicalNameResolver::new(
            &source.parsed.arena,
            bound(&source),
            source.bindings.symbol_store(),
            &mut host,
        )
        .unwrap();
        assert_eq!(
            resolver.resolve(
                foreign_location,
                "value",
                SymbolFlags::VALUE,
                None,
                false,
                false,
            ),
            Err(CanonicalNameResolutionError::UnboundLocation(
                foreign_location
            ))
        );
    }

    #[test]
    fn constructor_preflight_rejects_wrong_store_and_deferred_source_kinds() {
        let source = bind("const value = 1;", CanonicalModuleState::Script);
        let mut host = TestHost::for_source(&source);
        let foreign_store = SymbolStore::new();
        assert!(matches!(
            CanonicalNameResolver::new(
                &source.parsed.arena,
                bound(&source),
                &foreign_store,
                &mut host,
            ),
            Err(CanonicalNameResolutionError::InvalidSymbolStore(FILE))
        ));

        let javascript = parse_javascript_source_file("const value = 1;");
        let js_file = FileId::new(402);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &javascript.arena,
                javascript.source_file,
                js_file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/input.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        let bindings = binder.finish();
        let bound = bindings.file(js_file).unwrap();
        assert_eq!(bound.phase(), BindingPhase::Traversal);
        let mut host = TestHost::default();
        assert!(matches!(
            CanonicalNameResolver::new(
                &javascript.arena,
                bound,
                bindings.symbol_store(),
                &mut host,
            ),
            Err(CanonicalNameResolutionError::JavaScriptDeferred(file)) if file == js_file
        ));

        let common_js = parse_source_file("const value = 1;");
        let common_js_file = FileId::new(403);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &common_js.arena,
                common_js.source_file,
                common_js_file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/input.cts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::CommonJs,
                ),
            )
            .unwrap();
        let bindings = binder.finish();
        let mut host = TestHost::default();
        assert!(matches!(
            CanonicalNameResolver::new(
                &common_js.arena,
                bindings.file(common_js_file).unwrap(),
                bindings.symbol_store(),
                &mut host,
            ),
            Err(CanonicalNameResolutionError::CommonJsDeferred(file)) if file == common_js_file
        ));
    }

    #[test]
    fn foreign_declaration_ast_queries_are_explicitly_capability_gated() {
        let parsed = parse_source_file("const value = 1;");
        let foreign_parsed = parse_source_file("interface Foreign {}");
        let foreign_file = FileId::new(410);
        let mut binder = CanonicalBinder::new();
        for (arena, source_file, file, name) in [
            (&parsed.arena, parsed.source_file, FILE, "current.ts"),
            (
                &foreign_parsed.arena,
                foreign_parsed.source_file,
                foreign_file,
                "foreign.ts",
            ),
        ] {
            binder
                .bind_source_file_with_facts(
                    arena,
                    source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"/project/{name}\"")),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(arena, file)
                .unwrap();
        }
        let source = BoundSource {
            parsed,
            bindings: binder.finish(),
        };
        let foreign_declaration = foreign_parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::InterfaceDeclaration).then_some(node)
            })
            .unwrap();
        let foreign = NodeRef::new(foreign_parsed.arena.id(), foreign_file, foreign_declaration);
        let foreign_parent = NodeRef::new(
            foreign_parsed.arena.id(),
            foreign_file,
            foreign_parsed.source_file,
        );
        let mut host = TestHost::for_source(&source);
        {
            let mut resolver = CanonicalNameResolver::new(
                &source.parsed.arena,
                bound(&source),
                source.bindings.symbol_store(),
                &mut host,
            )
            .unwrap();
            assert_eq!(
                resolver.declaration_kind(foreign),
                Err(CanonicalNameResolutionError::ForeignDeclarationAstUnavailable(foreign))
            );
        }

        host.foreign_kinds
            .insert(foreign, SyntaxKind::InterfaceDeclaration);
        host.foreign_parents.insert(foreign, foreign_parent);
        host.foreign_modifiers
            .insert((foreign, SyntaxKind::DefaultKeyword), false);
        let mut resolver = CanonicalNameResolver::new(
            &source.parsed.arena,
            bound(&source),
            source.bindings.symbol_store(),
            &mut host,
        )
        .unwrap();
        assert_eq!(
            resolver.declaration_kind(foreign),
            Ok(SyntaxKind::InterfaceDeclaration)
        );
        assert_eq!(resolver.declaration_parent(foreign), Ok(foreign_parent));
        assert_eq!(
            resolver.declaration_has_modifier(foreign, SyntaxKind::DefaultKeyword),
            Ok(false)
        );

        let unregistered = NodeRef::new(
            foreign_parsed.arena.id(),
            FileId::new(411),
            foreign_declaration,
        );
        assert_eq!(
            resolver.declaration_kind(unregistered),
            Err(CanonicalNameResolutionError::UnboundLocation(unregistered))
        );
    }
}
