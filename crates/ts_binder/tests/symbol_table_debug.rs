use ts_binder::{EscapedName, SymbolData, SymbolFlags, SymbolStore, semantic::PreparedSymbolTable};

#[test]
fn symbol_table_debug_sorts_names_without_changing_entries() {
    let mut store = SymbolStore::new();
    let symbols = ["zeta", "alpha", "middle"].map(|name| {
        let name = EscapedName::source(name);
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::BLOCK_SCOPED_VARIABLE,
                name.clone(),
            ))
            .unwrap();
        (name, symbol)
    });
    let first = store.alloc_symbol_table();
    let second = store.alloc_prepared_symbol_table(PreparedSymbolTable::new(64).unwrap());
    for (name, symbol) in &symbols {
        assert_eq!(
            store.insert_symbol(first, name.clone(), *symbol),
            Some(None)
        );
    }
    for (name, symbol) in symbols.iter().rev() {
        assert_eq!(
            store.insert_symbol(second, name.clone(), *symbol),
            Some(None)
        );
    }

    let before = store.symbol_table(first).unwrap().clone();
    let debug = format!("{before:?}");
    assert_eq!(debug, format!("{:?}", store.symbol_table(second).unwrap()));
    let positions = ["alpha", "middle", "zeta"].map(|name| {
        debug
            .find(&format!("{:?}", EscapedName::source(name)))
            .unwrap()
    });
    assert!(positions.windows(2).all(|pair| pair[0] < pair[1]));
    assert_eq!(store.symbol_table(first), Some(&before));
    assert_eq!(store.symbol_table(second), Some(&before));
}
