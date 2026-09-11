//! Equality certificates and their independent verification.
use std::collections::BTreeMap;
use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Certificate {
    Refl {
        term: Term,
    },
    Rule {
        name: String,
        lhs: Term,
        rhs: Term,
        substitution: Substitution,
    },
    Computational {
        kind: Computation,
        lhs: Term,
        rhs: Term,
    },
    Symm {
        lhs: Term,
        rhs: Term,
        proof: Box<Certificate>,
    },
    Congruence {
        lhs: Term,
        rhs: Term,
        child_index: usize,
        child: Box<Certificate>,
    },
    Trans {
        lhs: Term,
        middle: Term,
        rhs: Term,
        first: Box<Certificate>,
        second: Box<Certificate>,
    },
}

impl Certificate {
    pub fn lhs(&self) -> &Term {
        match self {
            Self::Refl { term } => term,
            Self::Rule { lhs, .. }
            | Self::Computational { lhs, .. }
            | Self::Symm { lhs, .. }
            | Self::Congruence { lhs, .. }
            | Self::Trans { lhs, .. } => lhs,
        }
    }

    pub fn rhs(&self) -> &Term {
        match self {
            Self::Refl { term } => term,
            Self::Rule { rhs, .. }
            | Self::Computational { rhs, .. }
            | Self::Symm { rhs, .. }
            | Self::Congruence { rhs, .. }
            | Self::Trans { rhs, .. } => rhs,
        }
    }

    pub fn rule_names(&self, names: &mut Vec<String>) {
        match self {
            Self::Refl { .. } | Self::Computational { .. } => {}
            Self::Rule { name, .. } => names.push(name.clone()),
            Self::Symm { proof, .. } => proof.rule_names(names),
            Self::Congruence { child, .. } => child.rule_names(names),
            Self::Trans { first, second, .. } => {
                first.rule_names(names);
                second.rule_names(names);
            }
        }
    }

    pub fn contains_congruence(&self) -> bool {
        match self {
            Self::Congruence { .. } => true,
            Self::Symm { proof, .. } => proof.contains_congruence(),
            Self::Trans { first, second, .. } => {
                first.contains_congruence() || second.contains_congruence()
            }
            Self::Refl { .. } | Self::Rule { .. } | Self::Computational { .. } => false,
        }
    }

    pub fn contains_computation(&self, kind: Computation) -> bool {
        match self {
            Self::Computational { kind: used, .. } => *used == kind,
            Self::Symm { proof, .. } => proof.contains_computation(kind),
            Self::Congruence { child, .. } => child.contains_computation(kind),
            Self::Trans { first, second, .. } => {
                first.contains_computation(kind) || second.contains_computation(kind)
            }
            Self::Refl { .. } | Self::Rule { .. } => false,
        }
    }

    pub fn verify(&self, rules: &[Rewrite]) -> bool {
        self.verify_in(rules, &ArithSorts::default())
    }

    /// Verification with the arithmetic sort facts the relation checker
    /// needs; `rules` and `sorts` are both trusted problem input.
    pub fn verify_in(&self, rules: &[Rewrite], sorts: &ArithSorts) -> bool {
        match self {
            Self::Refl { .. } => true,
            Self::Rule { name, lhs, rhs, substitution } => {
                let Some(rule) = rules.iter().find(|rule| rule.name == name) else {
                    return false;
                };
                let mut matched = BTreeMap::new();
                match_pattern(&rule.lhs, lhs, &mut matched)
                    && &matched == substitution
                    && instantiate(&rule.rhs, substitution).as_ref() == Some(rhs)
            }
            // Verified by independent recomputation; the e-graph's own
            // solver state is never consulted.  ACI steps are judged by
            // flatten-and-compare, which subsumes the collapse edges the
            // proposer generates.
            Self::Computational { kind: Computation::AciNorm, lhs, rhs } => aci_equal(lhs, rhs),
            Self::Computational { kind: Computation::ArithPolyNorm, lhs, rhs } => {
                poly_equal(lhs, rhs)
            }
            Self::Computational { kind: Computation::ArithPolyNormRel, lhs, rhs } => {
                rel_equal(lhs, rhs, sorts)
            }
            Self::Computational { kind, lhs, rhs } => kind.apply(lhs).as_ref() == Some(rhs),
            Self::Symm { lhs, rhs, proof } => {
                proof.verify_in(rules, sorts) && proof.lhs() == rhs && proof.rhs() == lhs
            }
            Self::Congruence { lhs, rhs, child_index, child } => {
                child.verify_in(rules, sorts)
                    && lhs.op == rhs.op
                    && lhs.children.len() == rhs.children.len()
                    && lhs.children.get(*child_index) == Some(child.lhs())
                    && rhs.children.get(*child_index) == Some(child.rhs())
                    && lhs
                        .children
                        .iter()
                        .zip(&rhs.children)
                        .enumerate()
                        .all(|(index, (lhs, rhs))| index == *child_index || lhs == rhs)
            }
            Self::Trans { lhs, middle, rhs, first, second } => {
                first.verify_in(rules, sorts)
                    && second.verify_in(rules, sorts)
                    && first.lhs() == lhs
                    && first.rhs() == middle
                    && second.lhs() == middle
                    && second.rhs() == rhs
            }
        }
    }
}

pub fn chain(source: Term, steps: Vec<Certificate>) -> Certificate {
    if steps.is_empty() {
        return Certificate::Refl { term: source };
    }

    let mut steps = steps.into_iter();
    let mut certificate = steps.next().unwrap();
    for next in steps {
        certificate = Certificate::Trans {
            lhs: certificate.lhs().clone(),
            middle: certificate.rhs().clone(),
            rhs: next.rhs().clone(),
            first: Box::new(certificate),
            second: Box::new(next),
        };
    }
    certificate
}

pub fn reverse(certificate: Certificate) -> Certificate {
    Certificate::Symm {
        lhs: certificate.rhs().clone(),
        rhs: certificate.lhs().clone(),
        proof: Box::new(certificate),
    }
}
