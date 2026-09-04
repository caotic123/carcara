use crate::rare::language::{EggExpr, EggStatement};

pub fn arith_poly_norm_rel_rules() -> Vec<EggStatement> {
    let egglog_content = include_str!("arith_poly_norm_rel.egglog");
    vec![EggStatement::Raw(egglog_content.to_owned())]
}

pub fn relation_bool_goal_check_terms(
    lhs: EggExpr,
    rhs: EggExpr,
) -> (Vec<EggStatement>, EggExpr, EggExpr) {
    let setup = vec![
        EggStatement::Call(Box::new(EggExpr::Call(
            "arithRelBoolKeyOf-demand".to_owned(),
            vec![lhs.clone()],
        ))),
        EggStatement::Call(Box::new(EggExpr::Call(
            "arithRelBoolKeyOf-demand".to_owned(),
            vec![rhs.clone()],
        ))),
        EggStatement::Saturate {
            ruleset: Some("arith_poly".to_owned()),
        },
    ];

    let lhs_cmp = EggExpr::Call("arithRelBoolKeyOf".to_owned(), vec![lhs]);
    let rhs_cmp = EggExpr::Call("arithRelBoolKeyOf".to_owned(), vec![rhs]);

    (setup, lhs_cmp, rhs_cmp)
}

pub fn relation_bool_goal_guard_term(lhs: EggExpr) -> EggExpr {
    EggExpr::Call("arithRelBoolCanMatch".to_owned(), vec![lhs])
}
