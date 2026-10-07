//! The parameters of a generated rule. Each one is declared by the list of
//! its properties, and each premise of the rule is bound to one of its own.

use super::{
    RareTranslationError, app,
    compose::{Composable, Next, compose},
    id,
    rule::RuleCompiler,
};
use crate::{
    ast::{
        Sort, Term,
        rare_rules::{AttributeParameters, TypeParameter},
    },
    translation::eunoia::ast::{EunoiaConsAttr, EunoiaTerm, EunoiaType},
};

/// A parameter of the generated rule, as its properties declare it.
pub(super) struct Parameter {
    pub(super) name: String,
    sort: Sort,
    /// Its type in the declaration: its sort, unless a property changes it.
    pub(super) eunoia_type: EunoiaType,
    pub(super) attrs: Vec<EunoiaConsAttr>,
    /// What the rule requires of its value.
    pub(super) requirements: Vec<(EunoiaTerm, EunoiaTerm)>,
    /// The premise of the rule it binds.
    pub(super) premise: Option<EunoiaTerm>,
}

pub(super) type Declared = Result<Parameter, RareTranslationError>;

impl RuleCompiler<'_> {
    fn parameter(&self, name: String, sort: Sort) -> Declared {
        Ok(Parameter {
            eunoia_type: self.sort(&sort)?,
            name,
            sort,
            attrs: Vec::new(),
            requirements: Vec::new(),
            premise: None,
        })
    }

    /// Declares a parameter of the rule by its properties.
    pub(super) fn compile_parameter(&self, name: &str, parameter: &TypeParameter) -> Declared {
        let cx = self.parameter(name.to_owned(), parameter.sort.as_ref().clone())?;
        match (&cx.sort, &parameter.attribute) {
            (Sort::Type, _) => compose(self, cx, &[&anchored]),
            (_, AttributeParameters::List) => compose(self, cx, &[&supplied, &list]),
            _ => compose(self, cx, &[&supplied]),
        }
    }

    /// Binds the `i`-th premise of the rule to a fresh Boolean parameter.
    pub(super) fn compile_premise(&self, i: usize, formula: &Term) -> Declared {
        let mut name = format!("@rare.premise.{i}");
        while self.rule.parameters.contains_key(&name) {
            name.push('_');
        }
        let cx = self.parameter(name, Sort::Bool)?;
        compose(self, cx, &[&premise(self.term(formula, false)?)])
    }
}

impl Composable for Parameter {
    type Output = Declared;

    fn end(self, _: &RuleCompiler) -> Declared {
        Ok(self)
    }
}

/// Its value is supplied in `:args`.
fn supplied(rc: &RuleCompiler, cx: Parameter, k: Next<Parameter>) -> Declared {
    if !rc.rule.arguments.contains(&cx.name) {
        return Err(rc.error(format!(
            "parameter '{}' is not supplied in :args; inference from computed premises is not supported",
            cx.name
        )));
    }
    k(rc, cx)
}

/// A type parameter is supplied in `:args`, or recovered from a scalar
/// argument of that type (see `RuleCompiler::sort_term`).
fn anchored(rc: &RuleCompiler, cx: Parameter, k: Next<Parameter>) -> Declared {
    let rule = rc.rule;
    let anchored = rule.arguments.contains(&cx.name)
        || rule.arguments.iter().any(|arg| {
            rule.parameters.get(arg).is_some_and(|p| {
                p.attribute != AttributeParameters::List && p.sort.to_string() == cx.name
            })
        });
    if !anchored {
        return Err(rc.error(format!(
            "type parameter '{}' cannot be inferred from an ordinary argument",
            cx.name
        )));
    }
    k(rc, cx)
}

/// A sequence of elements of its sort, in the signature's encoding.
fn list(rc: &RuleCompiler, cx: Parameter, k: Next<Parameter>) -> Declared {
    let encoding = rc.theory.encoding;
    let mut requirements = cx.requirements;
    requirements.push(encoding.list_requirement(rc.sort_term(&cx.sort)?, &cx.name));
    k(
        rc,
        Parameter {
            eunoia_type: encoding.list_type(cx.eunoia_type),
            attrs: vec![EunoiaConsAttr::List],
            requirements,
            ..cx
        },
    )
}

/// Binds a premise of the rule: the formula it proves is this parameter,
/// required to be the instantiated `template`. Computed applications cannot
/// occur in premise patterns.
fn premise(template: EunoiaTerm) -> impl Fn(&RuleCompiler, Parameter, Next<Parameter>) -> Declared {
    move |rc, cx, k| {
        let mut requirements = cx.requirements;
        requirements.push((id(&cx.name), template.clone()));
        k(
            rc,
            Parameter {
                premise: Some(app("@cl", vec![id(&cx.name)])),
                requirements,
                ..cx
            },
        )
    }
}
