use std::fmt::format;

use indexmap::IndexMap;

use crate::{
    ast::{
        rare_rules::{AttributeParameters, Program, RuleDefinition, TypeParameter},
        Operator, PrimitivePool, Rc, Term, TermPool,
    },
    rare::util::collect_vars,
};

fn create_matching_clauses<'a>(
    pool: &mut PrimitivePool,
    clause: &Rc<Term>,
    fixed_params: &'a mut Vec<(Rc<Term>, bool)>,
    parameters: &IndexMap<String, TypeParameter>,
) -> (Vec<Rc<Term>>, &'a mut Vec<(Rc<Term>, bool)>) {
    let mut matching_parameters = vec![];
    let Term::App(_, args) = clause.as_ref() else {
        panic!("Expected an application term, found: {:?}", clause);
    };

    for (index, arg) in args.iter().enumerate() {
        let term = pool.add(Term::Var(
            format! {"_{}", index},
            fixed_params[index].0.clone(),
        ));
        let equality = pool.add(Term::Op(Operator::Equals, vec![term, arg.clone()]));
        for var in collect_vars(arg) {
            
            fixed_params[index].1 = (parameters[&var.0].attribute == AttributeParameters::List)
                || fixed_params[index].1;
        }

        matching_parameters.push(equality);
    }

    (matching_parameters, fixed_params)
}

pub fn compile_program(pool: &mut PrimitivePool, program: &Program) -> Vec<RuleDefinition> {
    let mut rules = vec![];
    let mut keys: Vec<String> = vec![];
    let mut symbol_table = vec![];
    let mut rejected_clauses = vec![];

    for (level, sort) in program
        .signature
        .iter()
        .take(program.signature.len() - 1)
        .enumerate()
    {
        let level_name = format!("_{}", level);
        keys.push(level_name.clone());
        symbol_table.push((sort.clone(), false));
    }

    for pattern in program.patterns.iter() {
        let mut vars = collect_vars(&pattern.0);
        vars.append(&mut collect_vars(&pattern.1));
        let (matching_clause, attrs) =
            create_matching_clauses(pool, &pattern.0, &mut symbol_table, &program.parameters);


        rules.push((
            vars.into_iter()
                .map(|v| v.0)
                .chain((0..program.signature.len() - 1).map(|x| format!("_{}", x))) 
                .filter(|x| x != &program.name)
                .collect(),
            rejected_clauses
                .iter()
                .chain(matching_clause.iter())
                .cloned()
                .collect(),
            pool.add(Term::Op(
                Operator::Equals,
                vec![pattern.0.clone(), pattern.1.clone()],
            )),
        ));

        let negation = build_term!(pool, false);
        let rejected_clause = pool.add(Term::Op(Operator::Or, matching_clause));

        let rejected_clause = pool.add(Term::Op(Operator::Equals, vec![rejected_clause, negation]));

        if !rejected_clauses.contains(&rejected_clause) {
            rejected_clauses.push(rejected_clause);
        }
    }

    let mut compiled_rules = vec![];
    let mut symbol_table  = symbol_table
        .into_iter()
        .enumerate()
        .map(|(index, (sort, is_list))| {
            (
                format!("_{}", index),
                TypeParameter {
                    term: sort,
                    attribute: if is_list {
                        AttributeParameters::List
                    } else {
                        AttributeParameters::None
                    },
                },
            )
        })
        .collect::<IndexMap<_, _>>();

    symbol_table.extend(program.parameters.clone());

    for (index, rule) in rules.into_iter().enumerate() {
        let (vars, premises, conclusion) = rule;
        compiled_rules.push(RuleDefinition {
            name: format!("{}_{}", program.name.clone(), index),
            parameters: symbol_table.clone(),
            arguments: vars,
            premises,
            conclusion,
        });
    }

    compiled_rules
}
