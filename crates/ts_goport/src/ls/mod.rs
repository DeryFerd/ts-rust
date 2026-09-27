//! Go package tree `internal/ls`.

pub mod api;
pub mod autoimport;
pub mod autoinsert;
pub mod callhierarchy;
pub mod change;
pub mod codeactions;
pub mod codeactions_fixclassincorrectlyimplementsinterface;
pub mod codeactions_fixmissingtypeannotation;
pub mod codeactions_importfixes;
pub mod codeactions_missingmemberfixer;
pub mod codelens;
pub mod completions_p1;
pub mod completions_p2;
pub mod completions_p3;
pub mod completions_p4;
pub mod constants;
pub mod crossproject;
pub mod definition;
pub mod diagnostics;
pub mod displaypartswriter;
pub mod documenthighlights;
pub mod file_rename;
pub mod findallreferences_p1;
pub mod findallreferences_p2;
pub mod folding;
pub mod format;
pub mod host;
pub mod hover;
pub mod import_tracker;
pub mod inlay_hints;
pub mod jsdoc;
pub mod jsdoc_snippet;
pub mod languageservice;
pub mod linkedediting;
pub mod lsconv;
pub mod lsutil;
pub mod organizeimports;
pub mod rename;
pub mod selectionranges;
pub mod semantictokens;
pub mod signaturehelp;
pub mod source_map;
pub mod sourcedefinition;
pub mod string_completions;
pub mod symbols;
pub mod utilities;

pub use api::*;
pub use autoinsert::*;
pub use callhierarchy::*;
pub use codeactions::*;
pub use codeactions_fixclassincorrectlyimplementsinterface::*;
pub use codeactions_fixmissingtypeannotation::*;
pub use codeactions_importfixes::*;
pub use codeactions_missingmemberfixer::*;
pub use codelens::*;
pub use completions_p1::*;
pub use completions_p2::*;
pub use completions_p3::*;
pub use completions_p4::*;
pub use constants::*;
pub use crossproject::*;
pub use definition::*;
pub use diagnostics::*;
pub use displaypartswriter::*;
pub use documenthighlights::*;
pub use file_rename::*;
pub use findallreferences_p1::*;
pub use findallreferences_p2::*;
pub use folding::*;
pub use format::*;
pub use host::*;
pub use hover::*;
pub use import_tracker::*;
pub use inlay_hints::*;
pub use jsdoc::*;
pub use jsdoc_snippet::*;
pub use languageservice::*;
pub use linkedediting::*;
pub use organizeimports::*;
pub use rename::*;
pub use selectionranges::*;
pub use semantictokens::*;
pub use signaturehelp::*;
pub use source_map::*;
pub use sourcedefinition::*;
pub use string_completions::*;
pub use symbols::*;
pub use utilities::*;

/// Glob import for ls files: `use crate::ls::prelude::*;`.
pub mod prelude {
    pub use super::{
        api::*, autoinsert::*, callhierarchy::*, codeactions::*,
        codeactions_fixclassincorrectlyimplementsinterface::*,
        codeactions_fixmissingtypeannotation::*, codeactions_importfixes::*,
        codeactions_missingmemberfixer::*, codelens::*, completions_p1::*, completions_p2::*,
        completions_p3::*, completions_p4::*, constants::*, crossproject::*, definition::*,
        diagnostics::*, displaypartswriter::*, documenthighlights::*, file_rename::*,
        findallreferences_p1::*, findallreferences_p2::*, folding::*, format::*, host::*, hover::*,
        import_tracker::*, inlay_hints::*, jsdoc::*, jsdoc_snippet::*, languageservice::*,
        linkedediting::*, organizeimports::*, rename::*, selectionranges::*, semantictokens::*,
        signaturehelp::*, source_map::*, sourcedefinition::*, string_completions::*, symbols::*,
        utilities::*,
    };
    pub use crate::astnav;
    pub use crate::format;
    pub use crate::frontend::json_ext::{self, LspAny};
    pub use crate::frontend::scanner::scanner_ls;
    pub use crate::frontend::{compiler, module, packagejson, tsoptions, tspath, vfs};
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::locale;
    pub use crate::ls::{autoimport, change, lsconv, lsutil};
    pub use crate::lsp::lsproto;
    pub use crate::modulespecifiers;
    pub use crate::prelude::*;
    pub use crate::program::ls_program;
    pub use crate::sourcemap;

    // Names that the crate prelude also exports. The package item wins.
    pub use super::callhierarchy::is_variable_like;
    pub use super::findallreferences_p2::{
        get_possible_symbol_reference_nodes, get_possible_symbol_reference_positions,
        is_method_or_accessor,
    };
    pub use super::utilities::{
        get_meaning_from_declaration, is_export_specifier_alias, is_jump_statement_target,
        is_label_of_labeled_statement, is_no_substitution_template_literal,
        is_readonly_type_operator, is_right_side_of_property_access, is_tagged_template_expression,
        is_template_head, is_template_tail,
    };
}
