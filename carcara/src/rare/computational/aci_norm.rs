use crate::ast::Operator;
use crate::egg_expr;
use crate::rare::language::{EggExpr, EggStatement};
use indexmap::IndexSet;

/// Centralized definition of ACI (Associative-Commutative-Idempotent) operators.
/// Returns: (Operator enum, string name, @-prefixed name, identity element)
pub fn aci_operators() -> impl Iterator<Item = (Operator, &'static str, &'static str, EggExpr)> {
    [
        (Operator::And, "and", "@and", egg_expr!((mk true))),
        (Operator::Or, "or", "@or", egg_expr!((mk false))),
    ]
    .into_iter()
}

pub fn singleton_operators(op: Operator) -> Option<EggExpr> {
    aci_operators()
        .find(|(o, _, _, _)| *o == op)
        .map(|(_, _, _, identity)| identity)
}

/// Generate all ACI normalization rules for an operator:
/// - Conversion from args-based to Assoc-based representation
/// - Identity elimination (e.g., `(and x true)` → `x`)
/// - Singleton elimination (e.g., `(and x)` → `x`)
pub fn aci_rules(
    op_with_at: &str,
    identity: EggExpr,
    assoc_calls: Option<&IndexSet<EggExpr>>,
) -> Vec<EggStatement> {
    let mut decls = Vec::new();

    // 1. Convert args-based calls to Assoc-based calls
    if let Some(calls) = assoc_calls {
        for args_expr in calls {
            let call = EggExpr::Call(op_with_at.into(), vec![args_expr.clone()]);
            let lhs = egg_expr!((mk {call}));
            let rhs = to_assoc_call(op_with_at, args_expr_to_vec(op_with_at, args_expr));
            decls.push(EggStatement::Rewrite(Box::new(lhs), Box::new(rhs), vec![]));
        }
    }

    // 2. Identity elimination: (op x identity) → x
    let args = egg_expr!((args "x" (args {identity.clone()} ())));
    let call = EggExpr::Call(op_with_at.into(), vec![args]);
    let lhs = egg_expr!((mk {call}));
    let rhs = egg_expr!("x");
    decls.push(EggStatement::Rewrite(Box::new(lhs), Box::new(rhs), vec![]));

    // 3. Singleton elimination: (Mk (op (Args x ()))) → x
    // Match on Args representation directly to avoid set-insert/set-empty cycle
    let args = egg_expr!((args "x" ()));
    let call = EggExpr::Call(op_with_at.into(), vec![args]);
    let lhs = egg_expr!((mk {call}));
    let rhs = egg_expr!("x");
    decls.push(EggStatement::Rewrite(Box::new(lhs), Box::new(rhs), vec![]));

    // 4. Idempotency: (Mk (op (Args x (Args x ())))) → x
    // Matches (op x x) directly on Args representation
    let args = egg_expr!((args "x" (args "x" ())));
    let call = EggExpr::Call(op_with_at.into(), vec![args]);
    let lhs = egg_expr!((mk {call}));
    let rhs = egg_expr!("x");
    decls.push(EggStatement::Rewrite(Box::new(lhs), Box::new(rhs), vec![]));

    // 5. General singleton elimination for Assoc: (op (Assoc {x})) → x
    // Run in list-ruleset to avoid cycle issues
    let assoc_set = egg_expr!((Assoc (set_insert (set_empty) (mk "x"))));
    let op_call = EggExpr::Call(op_with_at.into(), vec![assoc_set]);
    decls.push(EggStatement::Rule {
        ruleset: Some("list-ruleset".to_string()),
        body: vec![egg_expr!((= {op_call} "result"))],
        head: vec![egg_expr!((union "result" (mk "x")))],
    });

    decls
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
    egg_expr!((Assoc {set_expr}))
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
                if let EggExpr::Call(name, args) = inner.as_ref() {
                    if name == op_with_at {
                        for arg in args {
                            collect(op_with_at, arg, out);
                        }
                        return;
                    }
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
