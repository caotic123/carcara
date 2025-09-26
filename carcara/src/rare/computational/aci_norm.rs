use crate::rare::language::{EggExpr, EggStatement};
use crate::{assoc_expr, available_expr, call_expr, mk_expr, push_rewrite};

pub fn to_assoc_call(op_with_at: &str, args: Vec<EggExpr>) -> EggExpr {
    let assoc = build_assoc(args);
    call_expr!(op_with_at; assoc)
}

fn build_assoc(args: Vec<EggExpr>) -> EggExpr {
    let mut set_expr = call_expr!("set-empty");
    for arg in args {
        set_expr = call_expr!("set-insert"; set_expr, arg);
    }
    assoc_expr!(set_expr)
}

pub fn emit_assoc_rewrite_rules(
    decls: &mut Vec<EggStatement>,
    op_with_at: &str,
    args_expr: &EggExpr,
) {
    let lhs = mk_expr!(call_expr!(op_with_at.to_string(); args_expr.clone()));
    let flattened_args = args_expr_to_vec(op_with_at, args_expr);
    let rhs = to_assoc_call(op_with_at, flattened_args);
    let availability = available_expr!(lhs.clone());
    push_rewrite!(decls, lhs, rhs; when availability);
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
