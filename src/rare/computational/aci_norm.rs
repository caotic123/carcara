use crate::ast::Operator;
use crate::egg_expr;
use crate::rare::language::{EggExpr, EggStatement};
use indexmap::IndexSet;

/// Centralized definition of ACI (Associative-Commutative-Idempotent) operators.
/// Returns: (Operator enum, string name, @-prefixed name, identity element,
/// absorbing element)
pub fn aci_operators()
-> impl Iterator<Item = (Operator, &'static str, &'static str, EggExpr, EggExpr)> {
    [
        (Operator::And, "and", "@and", egg_expr!((mk true)), egg_expr!((mk false))),
        (Operator::Or, "or", "@or", egg_expr!((mk false)), egg_expr!((mk true))),
    ]
    .into_iter()
}

pub fn singleton_operators(op: Operator) -> Option<EggExpr> {
    aci_operators()
        .find(|(o, _, _, _, _)| *o == op)
        .map(|(_, _, _, identity, _)| identity)
}

/// Generate all ACI normalization rules for an operator:
/// - Conversion from args-based to Assoc-based representation
/// - Identity elimination (e.g., `(and x true)` → `x`)
/// - Singleton elimination (e.g., `(and x)` → `x`)
pub fn aci_rules(
    op_with_at: &str,
    identity: EggExpr,
    absorbing: EggExpr,
    assoc_calls: Option<&IndexSet<EggExpr>>,
) -> Vec<EggStatement> {
    let mut decls = aci_call_rules(op_with_at, assoc_calls);

    // 2. Identity elimination: (op x identity) → x
    // The head must be a genuine element (Mk x): an unguarded variable can bind
    // the (Args a b) pair that Args-associativity puts in the same class as the
    // flat list, which would union the formula with a raw argument list.
    let args = egg_expr!((args (mk "x") (args {identity.clone()} ())));
    let call = EggExpr::Call(op_with_at.into(), vec![args]);
    let lhs = egg_expr!((mk { call }));
    let rhs = egg_expr!((mk "x"));
    decls.push(EggStatement::Rewrite(Box::new(lhs), Box::new(rhs), vec![]));

    // 3. Singleton elimination: (Mk (op (Args (Mk x) ()))) → (Mk x)
    // Match on Args representation directly to avoid set-insert/set-empty cycle
    let args = egg_expr!((args (mk "x") ()));
    let call = EggExpr::Call(op_with_at.into(), vec![args]);
    let lhs = egg_expr!((mk { call }));
    let rhs = egg_expr!((mk "x"));
    decls.push(EggStatement::Rewrite(Box::new(lhs), Box::new(rhs), vec![]));

    // 4. Idempotency: (Mk (op (Args (Mk x) (Args (Mk x) ())))) → (Mk x)
    // Matches (op x x) directly on Args representation
    let args = egg_expr!((args (mk "x") (args (mk "x") ())));
    let call = EggExpr::Call(op_with_at.into(), vec![args]);
    let lhs = egg_expr!((mk { call }));
    let rhs = egg_expr!((mk "x"));
    decls.push(EggStatement::Rewrite(Box::new(lhs), Box::new(rhs), vec![]));

    // 5. General singleton elimination for Assoc: (op (Assoc {x})) → x
    // Run in list-ruleset to avoid cycle issues
    let assoc_set = egg_expr!((Assoc (set_insert (set_empty) (mk "x"))));
    let op_call = EggExpr::Call(op_with_at.into(), vec![assoc_set]);
    decls.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_owned()),
        body: vec![egg_expr!((= {op_call} "result"))],
        head: vec![egg_expr!((union "result" (mk "x")))],
    });

    // 6. Identity elimination in the set form: an identity element in the
    // set is dropped, so `(and true true true x)`, which the conversion
    // turns into the set {true, x}, reaches x.  Sets only shrink, so this
    // saturates.  The set form is the bare `(op (Assoc s))` node the
    // conversion unions into the formula's class, without `Mk`.
    let set_call = EggExpr::Call(op_with_at.into(), vec![egg_expr!((Assoc "s"))]);
    let without = EggExpr::Call(
        op_with_at.into(),
        vec![egg_expr!((Assoc ("set-remove" "s" {identity.clone()})))],
    );
    decls.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_owned()),
        body: vec![
            egg_expr!((= {set_call.clone()} "result")),
            egg_expr!(("set-contains" "s" {identity.clone()})),
        ],
        head: vec![egg_expr!((union "result" {without}))],
    });

    // 7. The empty set is the identity: `(and)` is true, `(or)` is false.
    let empty_call = EggExpr::Call(op_with_at.into(), vec![egg_expr!((Assoc (set_empty)))]);
    decls.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_owned()),
        body: vec![egg_expr!((= {empty_call} "result"))],
        head: vec![egg_expr!((union "result" {identity}))],
    });

    // 8. Absorbing element: a set holding it makes the whole formula the
    // absorbing element, `(or x true)` is true and `(and x false)` is false.
    decls.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_owned()),
        body: vec![
            egg_expr!((= {set_call} "result")),
            egg_expr!(("set-contains" "s" {absorbing.clone()})),
        ],
        head: vec![egg_expr!((union "result" {absorbing}))],
    });

    decls
}

/// Generate only the conversions tied to concrete calls seen in a proof step.
///
/// Each call is a ground term of the step, so its conversion is a `union`
/// rather than a rewrite: a rewrite with a ground left-hand side is the same
/// equation, but egglog 3.0 runs it as a join over every constructor table the
/// pattern mentions, on every iteration, and a deep `and`/`or` chain over a
/// six-figure e-graph took 20 s per iteration where the union is a lookup.
pub fn aci_call_rules(
    op_with_at: &str,
    assoc_calls: Option<&IndexSet<EggExpr>>,
) -> Vec<EggStatement> {
    let Some(calls) = assoc_calls else {
        return Vec::new();
    };
    calls
        .iter()
        .map(|args_expr| {
            let call = EggExpr::Call(op_with_at.into(), vec![args_expr.clone()]);
            let lhs = egg_expr!((mk { call }));
            let rhs = to_assoc_call(op_with_at, args_expr_to_vec(op_with_at, args_expr));
            if is_ground(args_expr) {
                EggStatement::Union(Box::new(lhs), Box::new(rhs))
            } else {
                EggStatement::Rewrite(Box::new(lhs), Box::new(rhs), vec![])
            }
        })
        .collect()
}

/// A call from the step itself, as opposed to one from a rule: no pattern
/// variable anywhere in it.  Rule variables are `Literal`s; the step's own
/// variables are hashed `Var`s, and no `Literal` (the engine's globals,
/// `goal_lhs`/`goal_rhs`) occurs inside a step's call.
fn is_ground(expr: &EggExpr) -> bool {
    use EggExpr::*;
    match expr {
        Literal(_) => false,
        Var(..) | NativeBool(_) | Bool(_) | Num(_) | String(_) | RawString(_) | Real(_)
        | BitVec(..) | Op(_) | Const(_) | Empty() => true,
        Ground(e) | Mk(e) => is_ground(e),
        App(a, b) | Args(a, b) | Equal(a, b) | Distinct(a, b) | Union(a, b) | Set(a, b) => {
            is_ground(a) && is_ground(b)
        }
        Call(_, args) => args.iter().all(is_ground),
    }
}

pub fn to_assoc_call(op_with_at: &str, args: Vec<EggExpr>) -> EggExpr {
    let assoc = build_assoc(args);
    EggExpr::Call(op_with_at.into(), vec![assoc])
}

fn build_assoc(args: Vec<EggExpr>) -> EggExpr {
    let mut set_expr = egg_expr!((set_empty));
    for arg in args {
        set_expr = egg_expr!((set_insert {set_expr} {arg}));
    }
    egg_expr!((Assoc { set_expr }))
}

pub fn args_expr_to_vec(op_with_at: &str, expr: &EggExpr) -> Vec<EggExpr> {
    fn collect(op_with_at: &str, expr: &EggExpr, out: &mut Vec<EggExpr>) {
        match expr {
            EggExpr::Args(head, tail) => {
                collect(op_with_at, head, out);
                collect(op_with_at, tail, out);
            }
            EggExpr::Empty() => {}
            EggExpr::Call(name, args) if name == op_with_at => {
                for arg in args {
                    collect(op_with_at, arg, out);
                }
            }
            EggExpr::Mk(inner) => {
                if let EggExpr::Call(name, args) = inner.as_ref()
                    && name == op_with_at
                {
                    for arg in args {
                        collect(op_with_at, arg, out);
                    }
                    return;
                }
                out.push(EggExpr::Mk(inner.clone()));
            }
            other => out.push(other.clone()),
        }
    }

    let mut result = Vec::new();
    collect(op_with_at, expr, &mut result);
    result
}
