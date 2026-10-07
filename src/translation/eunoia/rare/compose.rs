//! Lists of properties, and the properties of operators applied in rule
//! templates. A property compiles a context, given the rest of the list as its
//! continuation `k`, so an operator application, or a parameter of a generated
//! rule (see `parameter`), is compiled by the list of properties it has.

use super::{RareTranslationError, app, rule::RuleCompiler};
use crate::{
    ast::{Operator, Rc, Sort, Term},
    translation::eunoia::{alethe_signature::encoding::Encoding, ast::EunoiaTerm},
};

/// What properties compose over: an operator application or a parameter of
/// the generated rule. `end` finishes a composition.
pub(super) trait Composable: Sized {
    type Output;
    fn end(self, rc: &RuleCompiler) -> Self::Output;
}

/// The rest of a composition of properties over `C`.
pub(super) type Next<'n, C> = &'n dyn Fn(&RuleCompiler, C) -> <C as Composable>::Output;

/// A property: it compiles `C`, given the rest of the composition as its
/// continuation `k`.
pub(super) type Property<'p, C> =
    &'p dyn Fn(&RuleCompiler, C, Next<C>) -> <C as Composable>::Output;

/// Runs `properties` in order, each with the rest as its continuation, and
/// then ends the composition.
pub(super) fn compose<C: Composable>(
    rc: &RuleCompiler,
    cx: C,
    properties: &[Property<C>],
) -> C::Output {
    match properties {
        [] => cx.end(rc),
        [property, rest @ ..] => property(rc, cx, &|rc, cx| compose(rc, cx, rest)),
    }
}

/// An operator application in a rule template, as its properties refine it.
struct Application {
    op: Operator,
    /// The operator's symbol in the signature.
    symbol: String,
    operands: Vec<Rc<Term>>,
    /// The sort the operands share, once a property determines it.
    sort: Option<Sort>,
    /// Whether list parameters splice into the operands.
    splices: bool,
    /// The nil of an associative operator.
    nil: Option<EunoiaTerm>,
}

type Compiled = Result<EunoiaTerm, RareTranslationError>;

impl RuleCompiler<'_> {
    /// Compiles the application of `op`, named `symbol` in the signature, to
    /// `operands` by the operator's properties. An operator without any is a
    /// plain application, in which a list parameter cannot be an operand.
    pub(super) fn compile_application(
        &self,
        op: Operator,
        symbol: String,
        operands: &[Rc<Term>],
    ) -> Compiled {
        let cx = Application {
            op,
            symbol,
            operands: operands.to_vec(),
            sort: None,
            splices: false,
            nil: None,
        };
        match op {
            Operator::Distinct => compose(self, cx, &[&shared_sort, &arg_list]),
            Operator::And => compose(
                self,
                cx,
                &[
                    &of_sort(Sort::Bool),
                    &associative(EunoiaTerm::True),
                    &singleton,
                ],
            ),
            Operator::Or => compose(
                self,
                cx,
                &[
                    &of_sort(Sort::Bool),
                    &associative(EunoiaTerm::False),
                    &singleton,
                ],
            ),
            Operator::Add => compose(
                self,
                cx,
                &[
                    &shared_sort,
                    &associative(EunoiaTerm::Numeral(0.into())),
                    &singleton,
                ],
            ),
            Operator::Mult => compose(
                self,
                cx,
                &[
                    &shared_sort,
                    &associative(EunoiaTerm::Numeral(1.into())),
                    &singleton,
                ],
            ),
            _ => compose(self, cx, &[]),
        }
    }
}

impl Composable for Application {
    type Output = Compiled;

    /// The spine of an associative operator, and a plain application
    /// otherwise.
    fn end(self, rc: &RuleCompiler) -> Compiled {
        if self.nil.is_some() {
            spine(rc, self)
        } else {
            plain(rc, self)
        }
    }
}

/// All operands have sort `sort`.
fn of_sort(sort: Sort) -> impl Fn(&RuleCompiler, Application, Next<Application>) -> Compiled {
    move |rc, cx, k| {
        if cx.operands.iter().any(|x| x.raw_sort() != sort) {
            return Err(rc.error(format!(
                "mixed operand sorts in '{}' are not supported",
                cx.op
            )));
        }
        k(rc, Application { sort: Some(sort.clone()), ..cx })
    }
}

/// All operands share the sort of the first one.
fn shared_sort(rc: &RuleCompiler, cx: Application, k: Next<Application>) -> Compiled {
    let first = cx
        .operands
        .first()
        .ok_or_else(|| {
            rc.error(format!(
                "cannot infer the operand sort of empty '{}'",
                cx.op
            ))
        })?
        .raw_sort();
    of_sort(first)(rc, cx, k)
}

/// The signature's `:arg-list` attribute splices list parameters into the
/// operands.
fn arg_list(rc: &RuleCompiler, cx: Application, k: Next<Application>) -> Compiled {
    k(rc, Application { splices: true, ..cx })
}

/// Right-associative with `nil`: the operands and list fragments form one
/// spine, which ends the composition. Without list fragments, the rare-list
/// encoding keeps the surface application, which already is that spine, and
/// skips `k`.
fn associative(
    nil: EunoiaTerm,
) -> impl Fn(&RuleCompiler, Application, Next<Application>) -> Compiled {
    move |rc, cx, k| {
        let spliced = cx.operands.iter().any(|x| rc.is_list_term(x));
        if rc.theory.encoding == Encoding::RareList && !spliced && cx.operands.len() > 1 {
            return plain(rc, cx);
        }
        k(
            rc,
            Application {
                splices: true,
                nil: Some(nil.clone()),
                ..cx
            },
        )
    }
}

/// A spine with one element is that element.
fn singleton(rc: &RuleCompiler, cx: Application, k: Next<Application>) -> Compiled {
    let symbol = cx.symbol.clone();
    let nil = cx
        .nil
        .clone()
        .ok_or_else(|| rc.error(format!("singleton '{}' needs associative before it", cx.op)))?;
    let spine = k(rc, cx)?;
    Ok(rc.theory.encoding.singleton_elim(&symbol, nil, spine))
}

/// The operator applied to its operands.
fn plain(rc: &RuleCompiler, cx: Application) -> Compiled {
    Ok(app(cx.symbol, rc.operands(&cx.operands, cx.splices)?))
}

/// The spine of an associative operator.
fn spine(rc: &RuleCompiler, cx: Application) -> Compiled {
    let (Some(nil), Some(sort)) = (cx.nil, cx.sort) else {
        return Err(rc.error(format!("'{}' has no sorted associative spine", cx.op)));
    };
    let elements = rc.operands(&cx.operands, cx.splices)?;
    Ok(rc
        .theory
        .encoding
        .spine(&cx.symbol, nil, rc.sort_term(&sort)?, elements))
}
