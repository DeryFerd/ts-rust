use super::Parser;

#[test]
fn type_entry_restores_only_the_type_excluded_contexts() {
    for (source, errors) in [
        ("<await, yield>() => void;", false),
        ("value is <await, yield>() => void;", false),
        (
            "T extends unknown ? (<await, yield>() => void) : never;",
            false,
        ),
        ("<await", true),
    ] {
        let mut parser = Parser::new(source);
        parser.await_context = true;
        parser.yield_context = true;
        parser.await_identifier_context = true;
        parser.disallow_in = true;
        parser.parse_type();
        assert_eq!(
            !parser.diagnostics.is_empty(),
            errors,
            "{source}: {:?}",
            parser.diagnostics
        );
        assert!(parser.await_context, "{source}");
        assert!(parser.yield_context, "{source}");
        assert!(parser.await_identifier_context, "{source}");
        assert!(parser.disallow_in, "{source}");
    }
}

#[test]
fn generic_arrow_type_lookahead_keeps_live_parser_state() {
    for (source, expected) in [
        ("<T,>(value: T): <await, yield>() => void => value;", true),
        ("<T,>(value: T): <await, yield>() => void;", false),
        ("<const await,>(value: unknown) => value;", false),
    ] {
        let mut parser = Parser::new(source);
        parser.await_context = true;
        parser.yield_context = true;
        parser.await_identifier_context = true;
        parser.disallow_in = true;
        let current = parser.current.clone();
        let node_count = parser.arena.len();
        let checkpoint = parser.scanner.mark();
        let next = parser.scanner.scan();
        parser.scanner.rewind(checkpoint);

        assert_eq!(parser.is_generic_arrow_function(), expected, "{source}");

        assert_eq!(parser.current, current, "{source}");
        assert_eq!(parser.scanner.scan(), next, "{source}");
        assert_eq!(parser.arena.len(), node_count, "{source}");
        assert!(
            parser.diagnostics.is_empty(),
            "{source}: {:?}",
            parser.diagnostics
        );
        assert!(parser.await_context, "{source}");
        assert!(parser.yield_context, "{source}");
        assert!(parser.await_identifier_context, "{source}");
        assert!(parser.disallow_in, "{source}");
    }
}
