//! Port of Effect-TS/tsgo `internal/codegen` (the `Codegen` type) and
//! `internal/codegens` (the registry), effect-tsgo 0.51.1 (`47cb1ed7`).
//! In 0.51.1 only the `@effect-codegens` comment completion
//! (`effect::ls::completions::effect_codegens_comment`) reads them: there is
//! no codegen diagnostic or fix.

// Go: codegen/codegen.go:5 Codegen
/// Codegen defines a code generation directive with its metadata.
pub struct Codegen {
    /// Name is the unique identifier used in @effect-codegens directives.
    pub name: &'static str,

    /// Description explains what the codegen does.
    pub description: &'static str,
}

// Go: codegens/codegens.go:9 All
/// All is the list of all codegens.
pub static ALL: &[Codegen] = &[
    Codegen {
        name: "accessors",
        description: "Generate accessors for the service",
    },
    Codegen {
        name: "annotate",
        description: "Annotate with type",
    },
    Codegen {
        name: "typeToSchema",
        description: "Generate Schemas from types",
    },
];
