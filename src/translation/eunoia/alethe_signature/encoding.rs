//! The two encodings the Alethe-in-Eunoia signature declares. `AletheTheory`
//! carries the encoding, so whoever emits Eunoia gets it from the signature.

use crate::{ast::Operator, translation::eunoia::ast::*};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Encoding {
    /// `eo::List` sequences and the `_native` declarations, built on list
    /// builtins.
    Native,
    /// Rare-lists, whose nil carries the element sort, and the declarations
    /// checked by library programs.
    RareList,
}

use Encoding::*;

fn id(name: impl Into<String>) -> EunoiaTerm {
    EunoiaTerm::Id(name.into())
}

fn app(name: impl Into<String>, args: Vec<EunoiaTerm>) -> EunoiaTerm {
    EunoiaTerm::App(name.into(), args)
}

impl Encoding {
    pub fn new(native: bool) -> Self {
        if native { Native } else { RareList }
    }

    /// The symbol of `op`, when the encodings name it differently.
    pub fn symbol(self, op: Operator) -> Option<&'static str> {
        match (op, self) {
            (Operator::Distinct, Native) => Some("distinct_native"),
            (Operator::Distinct, RareList) => Some("distinct"),
            _ => None,
        }
    }

    /// The Eunoia rule checking the Alethe rule `rule`.
    pub fn rule(self, rule: &str) -> &str {
        match (rule, self) {
            // distinct
            ("distinct_elim", Native) => "distinct_elim_native",
            // and, or
            ("aci_simp", Native) => "aci_simp_native",
            _ => rule,
        }
    }

    /// A sequence of `elements`. Only the empty rare-list needs `sort`, their
    /// sort; without it, the nil is left untyped for the caller to complete.
    pub fn sequence(self, elements: Vec<EunoiaTerm>, sort: Option<EunoiaTerm>) -> EunoiaTerm {
        match (self, elements.is_empty(), sort) {
            (Native, true, _) => id("eo::List::nil"),
            (Native, false, _) => app("eo::List::cons", elements),
            (RareList, true, Some(sort)) => app("@rare-list-nil", vec![sort]),
            (RareList, true, None) => id("@rare-list-nil"),
            (RareList, false, _) => app("@rare-list-cons", elements),
        }
    }

    /// The spine of the operator `symbol`, whose nil is `nil`, over
    /// `elements` of sort `sort`: list fragments are spliced, and ordinary
    /// nested formulas remain elements.
    pub fn spine(
        self,
        symbol: &str,
        nil: EunoiaTerm,
        sort: EunoiaTerm,
        elements: Vec<EunoiaTerm>,
    ) -> EunoiaTerm {
        let sequence = self.sequence(elements, Some(sort.clone()));
        match self {
            Native => app(
                "$normalize_eo_list_native",
                vec![sort.clone(), sort, id(symbol), sequence],
            ),
            RareList => app(
                "$normalize_rare_list",
                vec![sort, id(symbol), nil, sequence],
            ),
        }
    }

    /// `spine`, or its only element when it has one.
    pub fn singleton_elim(self, symbol: &str, nil: EunoiaTerm, spine: EunoiaTerm) -> EunoiaTerm {
        match self {
            Native => app("eo::list_singleton_elim", vec![id(symbol), spine]),
            RareList => app("$f_list_singleton_elim", vec![id(symbol), nil, spine]),
        }
    }

    /// The type of a list parameter whose elements have type `element`.
    pub fn list_type(self, element: EunoiaType) -> EunoiaType {
        match self {
            Native => EunoiaType::Name("eo::List".into()),
            RareList => element,
        }
    }

    /// The requirement that the list parameter `name` has elements of `sort`.
    pub fn list_requirement(self, sort: EunoiaTerm, name: &str) -> (EunoiaTerm, EunoiaTerm) {
        match self {
            // Normalizing into eo::List checks every element and preserves
            // the carrier.
            Native => (
                app(
                    "$normalize_eo_list_native",
                    vec![
                        sort,
                        EunoiaTerm::Type(EunoiaType::Name("eo::List".into())),
                        id("eo::List::cons"),
                        id(name),
                    ],
                ),
                id(name),
            ),
            // The nil terminator carries the element sort.
            RareList => (
                app("$rare_list_of_sort", vec![sort, id(name)]),
                EunoiaTerm::True,
            ),
        }
    }
}
