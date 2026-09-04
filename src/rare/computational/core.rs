use crate::rare::{
    computational::{aci_norm, arith_poly_norm, arith_poly_norm_rel, distinct_elim, evaluation},
    engine::EggFunctions,
    language::EggStatement,
};

fn declare_aci_rules(decls: &mut Vec<EggStatement>, functions: &EggFunctions) {
    for (_, name, op_with_at, identity) in aci_norm::aci_operators() {
        if functions.names.contains_key(name) {
            decls.extend(aci_norm::aci_rules(
                op_with_at,
                identity,
                functions.assoc_calls.get(op_with_at),
            ));
        }
    }
}

/// Add rules that are independent of a particular proof step to the reusable database baseline.
pub fn declare_database_eliminations(decls: &mut Vec<EggStatement>, functions: &EggFunctions) {
    declare_aci_rules(decls, functions);
    decls.extend(evaluation::evaluation_rules());
    if functions.names.contains_key("distinct") {
        decls.extend(distinct_elim::distinct_solver_statements());
    }
}

/// Add only rules whose shape depends on calls in the current premises or goal.
pub fn declare_goal_eliminations(
    decls: &mut Vec<EggStatement>,
    functions: &EggFunctions,
    enable_arith_poly: bool,
    database_has_distinct: bool,
) {
    for (_, name, op_with_at, _) in aci_norm::aci_operators() {
        if functions.names.contains_key(name) {
            decls.extend(aci_norm::aci_call_rules(
                op_with_at,
                functions.assoc_calls.get(op_with_at),
            ));
        }
    }

    if enable_arith_poly {
        decls.extend(arith_poly_norm::arith_poly_norm_rules());
        decls.extend(arith_poly_norm_rel::arith_poly_norm_rel_rules());
    }
    if !database_has_distinct && functions.names.contains_key("distinct") {
        decls.extend(distinct_elim::distinct_solver_statements());
    }
}
