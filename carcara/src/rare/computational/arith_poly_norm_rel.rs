use crate::rare::language::EggStatement;

pub fn arith_poly_norm_rel_rules() -> Vec<EggStatement> {
    let egglog_content = include_str!("arith_poly_norm_rel.egglog");
    vec![EggStatement::Raw(egglog_content.to_string())]
}
