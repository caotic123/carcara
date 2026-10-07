//! Compile supplied RARE definitions, preserving sequence parameters until
//! each operator occurrence interprets them. Every rule in the supplied database
//! is compiled; proof references are validated separately.
//!
//! - `steps`: the `rare_rewrite` steps of a proof, which reference the rules.
//! - `rule`: the compiler of one definition into an Eunoia rule.
//! - `compose`: lists of properties, each given the rest as its continuation,
//!   and the properties of operators applied in rule templates.
//! - `parameter`: the properties of the parameters of a generated rule.

mod compose;
mod parameter;
mod rule;
mod steps;

pub use steps::{empty_list_sort, validate_proof};

use super::{alethe_signature::theory::AletheTheory, ast::*};
use crate::ast::rare_rules::Rules;
use indexmap::IndexMap;
use rule::RuleCompiler;

#[derive(Debug, thiserror::Error)]
#[error("cannot translate RARE rule '{rule}': {reason}")]
pub struct RareTranslationError {
    pub rule: String,
    pub reason: String,
}

pub struct CompiledRules {
    pub declarations: EunoiaProof,
    pub names: IndexMap<String, String>,
}

fn id(name: impl Into<String>) -> EunoiaTerm {
    EunoiaTerm::Id(name.into())
}

fn app(name: impl Into<String>, args: Vec<EunoiaTerm>) -> EunoiaTerm {
    EunoiaTerm::App(name.into(), args)
}

/// Compile the complete rule database in its declaration order, in the
/// signature's encoding.
pub fn compile(
    rules: &Rules,
    theory: &AletheTheory,
) -> Result<CompiledRules, RareTranslationError> {
    let mut names = IndexMap::new();
    let mut declarations = Vec::new();
    for (i, (name, rule)) in rules.rules.iter().enumerate() {
        // Keep supplied rule names in their own namespace, even if a RARE
        // definition has the same name as an Alethe rule such as `refl`.
        let generated = format!("@rare.rule.{i}");
        declarations.push(RuleCompiler { rule, theory }.compile(&generated)?);
        names.insert(name.clone(), generated);
    }
    Ok(CompiledRules { declarations, names })
}
