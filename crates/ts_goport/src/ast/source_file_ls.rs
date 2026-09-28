//! Port of Go `ast/ast.go` parts that the language service needs:
//! lines 2405-2450 (`SourceFileDataKey`, `NewSourceFileDataKey`,
//! `GetOrComputeSourceFileData`, `getSourceFileDataCell`), 2462-2465
//! (`TokenCacheKey`) and 2776-2838 (`(*SourceFile).GetOrCreateToken`,
//! `createToken`).
//!
//! PORT: Go keeps `data`, `tokenCache` and `tokenFactory` on each
//! `SourceFile` behind mutexes. Parsed files are immutable here, so these are
//! thread-local maps keyed by the source file `Node`, like
//! `source_file_get_declaration_map` in `ast/node.rs`. Created tokens are
//! synthetic nodes, which are thread-local too. All language-service state
//! runs on the LSP dispatch thread (PORTING "Language service", Threads).

use crate::prelude::*;
use std::any::Any;
use std::cell::OnceCell;
use std::marker::PhantomData;
use std::sync::atomic::{AtomicU64, Ordering};

thread_local! {
    /// Go `SourceFile.data`, keyed by (file, data key).
    static SOURCE_FILE_DATA: RefCell<FxHashMap<(Node, u64), Rc<dyn Any>>> =
        RefCell::new(FxHashMap::default());
    /// Go `SourceFile.tokenCache`, keyed by (file, token cache key).
    static TOKEN_CACHES: RefCell<FxHashMap<(Node, TokenCacheKey), Node>> =
        RefCell::new(FxHashMap::default());
    /// Go `SourceFile.tokenFactory`, one per file.
    static TOKEN_FACTORIES: RefCell<FxHashMap<Node, Rc<NodeFactory>>> =
        RefCell::new(FxHashMap::default());
}

// Go: ast/ast.go:2407 SourceFileDataKey
/// SourceFileDataKey identifies lazily-computed data attached to a SourceFile by
/// another package. Prefer regular SourceFile fields for ast-owned data.
// PORT: Go `key sourceFileDataKey` is `u64` (Go `type sourceFileDataKey
// uint64`; its Rust type name would be the same as this struct's). Go
// `_ [0]T` is `PhantomData<fn() -> T>`, so a key can live in a `static` for
// any `T`. Go returns a pointer from `NewSourceFileDataKey`; here the key is
// a `Copy` value, and its `key` number is its identity.
pub struct SourceFileDataKey<T> {
    key: u64,
    _t: PhantomData<fn() -> T>,
}

impl<T> Clone for SourceFileDataKey<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for SourceFileDataKey<T> {}

impl<T> std::fmt::Debug for SourceFileDataKey<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SourceFileDataKey")
            .field("key", &self.key)
            .finish()
    }
}

// Go: ast/ast.go:2414 sourceFileDataKeyCounter
static SOURCE_FILE_DATA_KEY_COUNTER: AtomicU64 = AtomicU64::new(0);

// Go: ast/ast.go:2416 sourceFileDataCell
// PORT: Go `once sync.Once` and `value T` are one `OnceCell<T>`.
pub struct SourceFileDataCell<T> {
    value: OnceCell<T>,
}

// Go: ast/ast.go:2421 NewSourceFileDataKey
pub fn new_source_file_data_key<T>() -> SourceFileDataKey<T> {
    SourceFileDataKey {
        // Go `atomic.Uint64.Add(1)` returns the new value.
        key: SOURCE_FILE_DATA_KEY_COUNTER.fetch_add(1, Ordering::SeqCst) + 1,
        _t: PhantomData,
    }
}

// Go: ast/ast.go:2425 GetOrComputeSourceFileData
// PORT: Go `compute func(*SourceFile) T` is `FnOnce(Node) -> T`; the value
// is returned by clone (Go copies `T`; callers use `Rc` or `Copy` values).
// `compute` runs without any thread-local borrow held, so it can read other
// data keys of the same file.
pub fn get_or_compute_source_file_data<T: Clone + 'static>(
    file: Node,
    key: &SourceFileDataKey<T>,
    compute: impl FnOnce(Node) -> T,
) -> T {
    let cell = get_source_file_data_cell(file, key);
    cell.value.get_or_init(|| compute(file)).clone()
}

// Go: ast/ast.go:2433 getSourceFileDataCell
// PORT: a Rust reference cannot be nil, so only `key.key == 0` is checked.
fn get_source_file_data_cell<T: 'static>(
    file: Node,
    key: &SourceFileDataKey<T>,
) -> Rc<SourceFileDataCell<T>> {
    if key.key == 0 {
        panic!("invalid SourceFileDataKey; use NewSourceFileDataKey");
    }

    SOURCE_FILE_DATA.with(|data| {
        let mut data = data.borrow_mut();
        if let Some(cell) = data.get(&(file, key.key)) {
            // PORT: Go type assertion `cell.(*sourceFileDataCell[T])`.
            return Rc::clone(cell)
                .downcast::<SourceFileDataCell<T>>()
                .unwrap_or_else(|_| {
                    panic!("interface conversion: source file data cell has another type")
                });
        }
        let cell = Rc::new(SourceFileDataCell {
            value: OnceCell::new(),
        });
        let any_cell: Rc<dyn Any> = cell.clone();
        data.insert((file, key.key), any_cell);
        cell
    })
}

// Go: ast/ast.go:2462 TokenCacheKey
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TokenCacheKey {
    parent: Node,
    loc: TextRange,
}

// Go: ast/ast.go:2776 (*SourceFile).GetOrCreateToken
/// Gets a token from the file's token cache, or creates it if it does not already exist.
/// This function should NOT be used for creating synthetic tokens that are not in the file in the first place.
// PORT: Go `%v` of `Kind` prints the Go kind name ("KindIdentifier"); this
// prints the Rust `Debug` name ("Identifier"). Panic text only.
pub fn source_file_get_or_create_token(
    file: Node,
    kind: SyntaxKind,
    pos: i32,
    end: i32,
    parent: Node,
    flags: TokenFlags,
) -> Node {
    let loc = TextRange::new(pos, end);
    let key = TokenCacheKey { parent, loc };
    if let Some(token) = TOKEN_CACHES.with(|c| c.borrow().get(&(file, key)).copied()) {
        if token.kind() != kind {
            panic!("Token cache mismatch: {:?} != {:?}", token.kind(), kind);
        }
        return token;
    }
    if parent.flags().intersects(NodeFlags::REPARSED) {
        panic!(
            "Cannot create token from reparsed node of kind {:?}",
            parent.kind()
        );
    }
    // PORT: Go `if node.tokenCache == nil { make(...) }`: the thread-local map
    // always exists. The cache outlives program versions, so the token
    // belongs to the thread (`enter_base_synthetic_owner`).
    let _base = enter_base_synthetic_owner();
    let token = create_token(kind, file, pos, end, flags);
    set_node_loc(token, loc);
    set_node_parent(token, parent);
    TOKEN_CACHES.with(|c| c.borrow_mut().insert((file, key), token));
    token
}

// Go: ast/ast.go:2807 createToken
/// `kind` should be a token kind.
fn create_token(kind: SyntaxKind, file: Node, pos: i32, end: i32, flags: TokenFlags) -> Node {
    // Go: if file.tokenFactory == nil { file.tokenFactory = NewNodeFactory(NodeFactoryHooks{}) }
    let token_factory =
        TOKEN_FACTORIES.with(|f| {
            Rc::clone(f.borrow_mut().entry(file).or_insert_with(|| {
                Rc::new(NodeFactory::new_with_hooks(NodeFactoryHooks::default()))
            }))
        });
    // PORT: scanner token boundaries are rune boundaries, so this byte slice
    // is a valid `&str` slice.
    let text = &source_file_text(file)[pos as usize..end as usize];
    match kind {
        SyntaxKind::NumericLiteral => token_factory.new_numeric_literal(text, flags),
        SyntaxKind::BigIntLiteral => token_factory.new_big_int_literal(text, flags),
        SyntaxKind::StringLiteral => token_factory.new_string_literal(text, flags),
        SyntaxKind::JsxText | SyntaxKind::JsxTextAllWhiteSpaces => {
            token_factory.new_jsx_text(text, kind == SyntaxKind::JsxTextAllWhiteSpaces)
        }
        SyntaxKind::RegularExpressionLiteral => {
            token_factory.new_regular_expression_literal(text, flags)
        }
        SyntaxKind::NoSubstitutionTemplateLiteral => {
            token_factory.new_no_substitution_template_literal(text, flags)
        }
        SyntaxKind::TemplateHead => {
            token_factory.new_template_head(text, "" /*rawText*/, flags)
        }
        SyntaxKind::TemplateMiddle => {
            token_factory.new_template_middle(text, "" /*rawText*/, flags)
        }
        SyntaxKind::TemplateTail => {
            token_factory.new_template_tail(text, "" /*rawText*/, flags)
        }
        SyntaxKind::Identifier => token_factory.new_identifier(text),
        SyntaxKind::PrivateIdentifier => token_factory.new_private_identifier(text),
        // Punctuation and keywords
        _ => token_factory.new_token(kind),
    }
}
