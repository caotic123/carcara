//! Encoded terms, rewrite patterns, and their Alethe decoding.
use std::{cmp::Ordering, collections::BTreeMap};
use rug::{Integer, Rational};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Term {
    pub op: String,
    pub children: Vec<Term>,
}

impl Term {
    pub fn new(op: &str, children: Vec<Self>) -> Self {
        Self { op: op.to_owned(), children }
    }

    pub fn leaf(op: &str) -> Self {
        Self::new(op, Vec::new())
    }

    pub fn size(&self) -> usize {
        1 + self.children.iter().map(Self::size).sum::<usize>()
    }

    pub fn to_egglog(&self) -> String {
        if self.children.is_empty() {
            if self.op == "Empty" {
                "(Empty)".to_owned()
            } else {
                self.op.clone()
            }
        } else {
            format!(
                "({} {})",
                self.op,
                self.children
                    .iter()
                    .map(Self::to_egglog)
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Var(&'static str),
    App(&'static str, Vec<Pattern>),
}

#[derive(Clone, Debug)]
pub struct Rewrite {
    pub name: &'static str,
    pub lhs: Pattern,
    pub rhs: Pattern,
}

pub type Substitution = BTreeMap<String, Term>;
pub type ClassSubstitution = BTreeMap<&'static str, u32>;

pub fn match_pattern(pattern: &Pattern, term: &Term, substitution: &mut Substitution) -> bool {
    match pattern {
        Pattern::Var(variable) => match substitution.get(*variable) {
            Some(previous) => previous == term,
            None => {
                substitution.insert((*variable).to_owned(), term.clone());
                true
            }
        },
        Pattern::App(op, children) => {
            op == &term.op
                && children.len() == term.children.len()
                && children
                    .iter()
                    .zip(&term.children)
                    .all(|(pattern, term)| match_pattern(pattern, term, substitution))
        }
    }
}

pub fn has_unbound_variables(pattern: &Pattern, substitution: &ClassSubstitution) -> bool {
    match pattern {
        Pattern::Var(variable) => !substitution.contains_key(variable),
        Pattern::App(_, children) => children
            .iter()
            .any(|child| has_unbound_variables(child, substitution)),
    }
}

pub fn instantiate(pattern: &Pattern, substitution: &Substitution) -> Option<Term> {
    match pattern {
        Pattern::Var(variable) => substitution.get(*variable).cloned(),
        Pattern::App(op, children) => Some(Term::new(
            op,
            children
                .iter()
                .map(|child| instantiate(child, substitution))
                .collect::<Option<Vec<_>>>()?,
        )),
    }
}

pub fn encoded_args(elements: Vec<Term>) -> Term {
    elements
        .into_iter()
        .rev()
        .fold(Term::leaf("Empty"), |tail, element| {
            Term::new("Args", vec![element, tail])
        })
}

pub fn encoded_app(operator: &str, elements: Vec<Term>) -> Term {
    Term::new("Mk", vec![Term::new(operator, vec![encoded_args(elements)])])
}

pub fn encoded_bool(value: bool) -> Term {
    let literal = if value { "true" } else { "false" };
    Term::new("Mk", vec![Term::new("Bool", vec![Term::leaf(literal)])])
}

/// Elements of an encoded argument list `(Args e1 (Args e2 ... (Empty)))`.
pub fn list_elements(list: &Term) -> Option<Vec<Term>> {
    let mut elements = Vec::new();
    let mut current = list;
    loop {
        match (current.op.as_str(), current.children.as_slice()) {
            ("Empty", []) => return Some(elements),
            ("Args", [element, tail]) => {
                elements.push(element.clone());
                current = tail;
            }
            _ => return None,
        }
    }
}

/// Decompose an encoded application `Mk(op(list))` into its operator and
/// argument elements.
pub fn encoded_application(term: &Term) -> Option<(&str, Vec<Term>)> {
    let ("Mk", [application]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    let [arguments] = application.children.as_slice() else {
        return None;
    };
    Some((application.op.as_str(), list_elements(arguments)?))
}

pub fn bool_value(term: &Term) -> Option<bool> {
    let ("Mk", [inner]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    let ("Bool", [literal]) = (inner.op.as_str(), inner.children.as_slice()) else {
        return None;
    };
    match literal.op.as_str() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

pub fn rational_from_leaves(numer: &Term, denom: &Term) -> Option<Rational> {
    let numer: Integer = numer.op.parse().ok()?;
    let denom: Integer = denom.op.parse().ok()?;
    (denom != 0).then(|| Rational::from((numer, denom)))
}

/// A serialized `BigRat` literal, `(bigrat (bigint "n") (bigint "d"))`.
pub fn bigrat_literal(literal: &str) -> Option<Rational> {
    let parts: Vec<&str> = literal.split('"').collect();
    let numer: Integer = parts.get(1)?.parse().ok()?;
    let denom: Integer = parts.get(3)?.parse().ok()?;
    (denom != 0).then(|| Rational::from((numer, denom)))
}

pub fn integer_of(term: &Term) -> Option<i64> {
    let ("Mk", [inner]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    match (inner.op.as_str(), inner.children.as_slice()) {
        ("Num", [value]) => value.op.parse().ok(),
        _ => None,
    }
}

/// A rational literal in either encoding: the parser's `Real` or the
/// solver's `RatConst`.
pub fn rational_of(term: &Term) -> Option<Rational> {
    let ("Mk", [inner]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    match (inner.op.as_str(), inner.children.as_slice()) {
        ("Real", [numer, denom]) => rational_from_leaves(numer, denom),
        ("RatConst", [literal]) => bigrat_literal(&literal.op),
        _ => None,
    }
}

pub fn encoded_num(value: i64) -> Term {
    Term::new("Mk", vec![Term::new("Num", vec![Term::leaf(&value.to_string())])])
}

/// The solver's rational constant, with the `BigRat` literal spelled the
/// way egglog serializes it.
pub fn encoded_rational(value: &Rational) -> Term {
    let literal = format!(
        "(bigrat (from-string \"{}\") (from-string \"{}\"))",
        value.numer(),
        value.denom()
    );
    Term::new("Mk", vec![Term::new("RatConst", vec![Term::leaf(&literal)])])
}

/// Decode an encoded term back to SMT-LIB/Alethe syntax: `Mk`-wrapped
/// constants, booleans, variables, `@`-operator applications over `Args`
/// lists, and curried `App` chains for uninterpreted functions.  Hashed
/// variable identifiers resolve through `names` (built by walking the
/// original conclusion against the encoded goals); solver-internal shapes
/// decode to `None`.
pub fn decode_term(term: &Term, names: &HashMap<String, String>) -> Option<String> {
    let ("Mk", [inner]) = (term.op.as_str(), term.children.as_slice()) else {
        return None;
    };
    decode_inner(inner, names)
}

pub fn decode_any(term: &Term, names: &HashMap<String, String>) -> Option<String> {
    if term.op == "Mk" {
        decode_term(term, names)
    } else {
        decode_inner(term, names)
    }
}

pub fn decode_inner(inner: &Term, names: &HashMap<String, String>) -> Option<String> {
    match (inner.op.as_str(), inner.children.as_slice()) {
        ("Const", [name]) => Some(name.op.trim_matches('"').to_owned()),
        ("Bool", [literal]) => Some(literal.op.clone()),
        ("Op", [name]) => Some(name.op.trim_matches('"').to_owned()),
        // Numerals print the way Carcara prints them, so they parse back.
        ("Num", [value]) => Some(value.op.clone()),
        ("Real", [numer, denom]) => Some(if denom.op == "1" && !numer.op.starts_with('-') {
            format!("{}.0", numer.op)
        } else {
            format!("{}/{}", numer.op, denom.op)
        }),
        ("RatConst", [literal]) => bigrat_literal(&literal.op).map(|value| {
            if value.is_integer() && value.cmp0() != Ordering::Less {
                format!("{}.0", value.numer())
            } else {
                format!("{}/{}", value.numer(), value.denom())
            }
        }),
        ("Var", [id, _sort]) => Some(
            names
                .get(&id.op)
                .cloned()
                .unwrap_or_else(|| format!("v{}", id.op.trim_start_matches('-'))),
        ),
        ("App", [_, _]) => {
            let mut arguments = Vec::new();
            let mut current = inner;
            while let ("App", [next, argument]) = (current.op.as_str(), current.children.as_slice())
            {
                arguments.push(argument);
                current = next;
            }
            arguments.reverse();
            let head = decode_any(current, names)?;
            let arguments = arguments
                .iter()
                .map(|argument| decode_any(argument, names))
                .collect::<Option<Vec<_>>>()?;
            Some(format!("({} {})", head, arguments.join(" ")))
        }
        (operator, [arguments]) if operator.starts_with('@') => {
            let elements = list_elements(arguments)?
                .iter()
                .map(|element| decode_any(element, names))
                .collect::<Option<Vec<_>>>()?;
            Some(format!("({} {})", &operator[1..], elements.join(" ")))
        }
        _ => None,
    }
}

pub fn leak(string: String) -> &'static str {
    Box::leak(string.into_boxed_str())
}
