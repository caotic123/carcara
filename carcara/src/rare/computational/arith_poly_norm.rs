use std::sync::Arc;

use crate::{
    ast::{Constant, Operator, Rc, Sort, Term, TermPool},
    egg_expr,
    rare::{
        engine::EggFunctions,
        language::{EggExpr, EggStatement},
        util::str_to_u64,
    },
};
use egglog::{
    ast::{Span, Symbol},
    constraint::{SimpleTypeConstraint, TypeConstraint},
    sort::{EqSort, I64Sort},
    ArcSort, EGraph, PrimitiveLike, Value,
};

pub fn arith_poly_norm_rules() -> Vec<EggStatement> {
    // Include the egglog file content at compile time
    let egglog_content = include_str!("arith_poly_norm.egglog");
    vec![EggStatement::Raw(egglog_content.to_string())]
}

fn is_numeric_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Int | Sort::Real)
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ArithPolyCheckKind {
    ArithPolyNfOf,
}

impl ArithPolyCheckKind {
    fn demand_relation(self) -> &'static str {
        match self {
            ArithPolyCheckKind::ArithPolyNfOf => "arithPolyNfOf-demand",
        }
    }

    fn function_name(self) -> &'static str {
        match self {
            ArithPolyCheckKind::ArithPolyNfOf => "arithPolyNfOf",
        }
    }
}

pub fn declare_opaque_arith_poly_rules(functions: &EggFunctions) -> Vec<EggStatement> {
    let mut numeric_funcs: Vec<_> = functions
        .names
        .iter()
        .filter_map(|(name, (is_op, _arity, result_sort))| {
            (!*is_op)
                .then_some(result_sort.as_ref())
                .flatten()
                .filter(|sort| is_numeric_sort(sort))
                .map(|sort| (name.clone(), sort.clone()))
        })
        .collect();
    numeric_funcs.sort_by(|lhs, rhs| lhs.0.cmp(&rhs.0));

    if numeric_funcs.is_empty() {
        return Vec::new();
    }

    let mut decls = Vec::new();

    for (func, result_sort) in &numeric_funcs {
        let is_int_result = matches!(result_sort, Sort::Int);
        let wrapped_app = EggExpr::Mk(Box::new(EggExpr::Call(
            format!("@{}", func),
            vec![EggExpr::Literal("args".to_string())],
        )));
        decls.push(EggStatement::Rule {
            ruleset: Some("arith_poly".to_string()),
            body: vec![egg_expr!(("arithPolyNfOf-demand" {wrapped_app.clone()}))],
            head: vec![egg_expr!(("atomPolyN-demand" {wrapped_app.clone()}))],
        });
        decls.push(EggStatement::Rule {
            ruleset: Some("arith_poly".to_string()),
            body: vec![
                egg_expr!((= ("atomPolyN" {wrapped_app.clone()}) "p")),
                egg_expr!(("arithPolyNfOf-demand" {wrapped_app.clone()})),
            ],
            head: vec![egg_expr!((set ("arithPolyNfOf" {wrapped_app.clone()}) "p"))],
        });
        decls.push(EggStatement::Rule {
            ruleset: Some("arith_poly".to_string()),
            body: vec![egg_expr!(("atomMonN-demand" {wrapped_app.clone()}))],
            head: vec![EggExpr::Set(
                Box::new(EggExpr::Call(
                    "atomHashIsInt".to_string(),
                    vec![EggExpr::Call(
                        "arith_poly_atom_hash".to_string(),
                        vec![wrapped_app],
                    )],
                )),
                Box::new(EggExpr::NativeBool(is_int_result)),
            )],
        });
    }

    decls
}

fn supports_arith_poly_term(pool: &dyn TermPool, term: &Rc<Term>) -> bool {
    match term.as_ref() {
        Term::Const(Constant::Integer(_) | Constant::Real(_)) => true,
        Term::Var(_, sort) => sort.as_sort().is_some_and(is_numeric_sort),
        Term::App(_, _) => pool.sort(term).as_sort().is_some_and(is_numeric_sort),
        Term::Op(Operator::Add, args) => {
            !args.is_empty() && args.iter().all(|arg| supports_arith_poly_term(pool, arg))
        }
        Term::Op(Operator::Sub, args) if args.len() == 1 => {
            supports_arith_poly_term(pool, &args[0])
        }
        Term::Op(Operator::Sub, args) if args.len() == 2 => {
            supports_arith_poly_term(pool, &args[0]) && supports_arith_poly_term(pool, &args[1])
        }
        Term::Op(Operator::Mult, args) if args.len() == 2 => {
            supports_arith_poly_term(pool, &args[0]) && supports_arith_poly_term(pool, &args[1])
        }
        Term::Op(Operator::RealDiv, args) if args.len() == 2 => {
            supports_arith_poly_term(pool, &args[0]) && supports_arith_poly_term(pool, &args[1])
        }
        Term::Op(Operator::ToReal, args) if args.len() == 1 => {
            supports_arith_poly_term(pool, &args[0])
        }
        _ => false,
    }
}

pub fn arith_poly_check_kind(pool: &dyn TermPool, term: &Rc<Term>) -> Option<ArithPolyCheckKind> {
    if supports_arith_poly_term(pool, term) {
        Some(ArithPolyCheckKind::ArithPolyNfOf)
    } else {
        None
    }
}

pub fn poly_eq_terms(kind: ArithPolyCheckKind) -> (Vec<EggStatement>, EggExpr, EggExpr) {
    let lhs = EggExpr::Literal("goal_lhs".to_string());
    let rhs = EggExpr::Literal("goal_rhs".to_string());

    let setup = vec![
        EggStatement::Call(Box::new(EggExpr::Call(
            kind.demand_relation().to_string(),
            vec![lhs.clone()],
        ))),
        EggStatement::Call(Box::new(EggExpr::Call(
            kind.demand_relation().to_string(),
            vec![rhs.clone()],
        ))),
        EggStatement::Saturate {
            ruleset: Some("arith_poly".to_string()),
        },
    ];

    let lhs_cmp = EggExpr::Call(kind.function_name().to_string(), vec![lhs]);
    let rhs_cmp = EggExpr::Call(kind.function_name().to_string(), vec![rhs]);

    (setup, lhs_cmp, rhs_cmp)
}

struct ArithPolyAtomHash;

impl PrimitiveLike for ArithPolyAtomHash {
    fn name(&self) -> Symbol {
        Symbol::from("arith_poly_atom_hash")
    }

    fn get_type_constraints(&self, span: &Span) -> Box<dyn TypeConstraint> {
        SimpleTypeConstraint::new(
            self.name(),
            vec![
                Arc::new(EqSort { name: Symbol::from("Term") }),
                Arc::new(I64Sort),
            ],
            span.clone(),
        )
        .into_box()
    }

    fn apply(
        &self,
        values: &[Value],
        _sorts: (&[ArcSort], &ArcSort),
        _egraph: Option<&mut EGraph>,
    ) -> Option<Value> {
        Some(Value::from(
            str_to_u64(&format!("atoms:{}", values[0].bits)) as i64,
        ))
    }
}

pub fn register_arith_poly_primitives(egraph: &mut EGraph) {
    egraph.add_primitive(ArithPolyAtomHash);
}

/// Test module for arith_poly_norm debugging using the engine
#[cfg(test)]
pub mod tests {
    use crate::ast::pool::PrimitivePool;
    use crate::ast::rare_rules::RareStatements;
    use crate::ast::{ProofNode, Rc, StepNode};
    use crate::parser::{parse_instance_with_pool, Config, Parser};
    use crate::rare::engine::{run_egglog, run_egglog_with_options, RunEgglogOptions};
    use egglog::EGraph;
    use indexmap::IndexMap;
    use std::io::Cursor;

    /// Returns true if debug-egglog feature is enabled
    /// Run with: cargo test --features debug-egglog <test_name> -- --nocapture
    fn debug_egglog() -> bool {
        cfg!(feature = "debug-egglog")
    }

    const DEFINITIONS: &str = r#"
        (declare-fun arg0 () Int)
        (declare-fun fmt0 () Int)
        (declare-fun fmt1 () Int)
        (declare-fun x () Int)
        (declare-fun x1 () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (declare-fun f3 () Int)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-fun fr (Int) Real)
        (declare-fun s_count (Int) Int)
        (declare-fun x_count (Int) Int)
    "#;

    const COUNTED_OFFSET_REORDER_EQ: &str = r#"
        (= (+ (+ arg0 (* 4 (s_count (- (- fmt1 2) fmt0))))
              (* 4 (x_count (- (- fmt1 2) fmt0))))
           (+ (* 4 (x_count (- (- fmt1 2) fmt0)))
              (* 4 (s_count (- (- fmt1 2) fmt0)))
              arg0))
    "#;

    const COUNTED_OFFSET_REORDER_EQ_BINARY_CONTROL: &str = r#"
        (= (+ (+ arg0 (* 4 (s_count (- (- fmt1 2) fmt0))))
              (* 4 (x_count (- (- fmt1 2) fmt0))))
           (+ (+ (* 4 (x_count (- (- fmt1 2) fmt0)))
                 (* 4 (s_count (- (- fmt1 2) fmt0))))
              arg0))
    "#;

    // Minimal arithmetic subset copied from rules.rare for the integer-bound
    // TRUST_THEORY_REWRITE regression.
    const INTEGER_BOUND_TEST_RARE: &str = r#"
        (declare-rare-rule arith-elim-lt ((@T0 Type) (@T1 Type) (t1 @T0) (s1 @T1))
          :args (t1 s1)
          :conclusion (= (< t1 s1) (not (>= t1 s1)))
        )

        (declare-rare-rule arith-elim-leq ((@T0 Type) (@T1 Type) (t1 @T0) (s1 @T1))
          :args (t1 s1)
          :conclusion (= (<= t1 s1) (>= s1 t1))
        )

        (declare-rare-rule arith-geq-tighten ((t1 Int) (s1 Int))
          :args (t1 s1)
          :conclusion (= (not (>= t1 s1)) (>= s1 (+ t1 1)))
        )

        (declare-rare-rule arith-geq-norm1-int ((t1 Int) (s1 Int))
          :args (t1 s1)
          :conclusion (= (>= t1 s1) (>= (- t1 s1) 0))
        )

        (declare-rare-rule arith-geq-norm1-real ((t1 Real) (s1 Real))
          :args (t1 s1)
          :conclusion (= (>= t1 s1) (>= (- t1 s1) 0/1))
        )

        (declare-rare-rule arith-int-geq-tighten ((t1 Int) (c1 Real) (cc1 Int))
          :premises ((= (= (to_real (to_int c1)) c1) false) (= cc1 (+ (to_int c1) 1)))
          :args (t1 c1 cc1)
          :conclusion (= (>= (to_real t1) c1) (>= t1 cc1))
        )
    "#;

    const RAW_TERM_BASE: &str = r#"
        (datatype Term
          (App Term Term)
          (Const String)
          (Var i64 Term)
          (Bool bool)
          (Num i64)
          (Real i64 i64)
          (Op String)
          (@String String)
          (Forall Term)
          (Exists Term)
          (Lambda Term)
          (Choice Term)
          (Sort Term)
          (Empty)
          (Args Term Term)
          (Mk Term))
    "#;

    /// Parse a term from a string with arithmetic definitions
    fn parse_term(pool: &mut PrimitivePool, term_str: &str) -> Rc<crate::ast::Term> {
        let config = Config {
            apply_function_defs: true,
            expand_lets: false,
            allow_int_real_subtyping: false,
            strict: false,
            parse_hole_args: false,
        };
        let mut parser = Parser::new(pool, config, DEFINITIONS.as_bytes()).expect("parser error");
        parser.parse_problem().expect("parse problem error");
        parser.reset(term_str.as_bytes()).expect("reset error");
        parser.parse_term().expect("parse term error")
    }

    /// Create an empty Rules database (arith_poly_norm rules are hardcoded in egglog)
    fn empty_rules() -> RareStatements {
        RareStatements {
            rules: IndexMap::new(),
            programs: IndexMap::new(),
            consts: IndexMap::new(),
        }
    }

    fn parse_rare_rules(pool: &mut PrimitivePool, source: &str) -> RareStatements {
        let config = Config {
            apply_function_defs: true,
            expand_lets: false,
            allow_int_real_subtyping: false,
            strict: false,
            parse_hole_args: false,
        };
        let (_, _, rules) = parse_instance_with_pool(
            Cursor::new(b"".as_slice()),
            Cursor::new(b"".as_slice()),
            Some(Cursor::new(source.as_bytes())),
            config,
            pool,
        )
        .expect("rare rules parse error");
        rules
    }

    /// Create a minimal proof node with no premises
    fn dummy_proof_node(
        pool: &mut PrimitivePool,
        conclusion: Rc<crate::ast::Term>,
    ) -> Rc<ProofNode> {
        let step = StepNode {
            id: "test".to_string(),
            depth: 0,
            clause: vec![conclusion],
            rule: "hole".to_string(),
            premises: vec![],
            args: vec![],
            discharge: vec![],
            previous_step: None,
        };
        Rc::new(ProofNode::Step(step))
    }

    /// Try to elaborate a conclusion term using run_egglog
    /// Set DEBUG_EGGLOG=1 env var to print generated egglog code
    fn try_elaborate(conclusion_str: &str) -> Result<(), String> {
        try_elaborate_with_debug(conclusion_str, debug_egglog())
    }

    /// Try to elaborate with explicit debug flag
    fn try_elaborate_with_debug(conclusion_str: &str, debug: bool) -> Result<(), String> {
        let mut pool = PrimitivePool::new();
        let conclusion = parse_term(&mut pool, conclusion_str);
        let rules = empty_rules();
        let root = dummy_proof_node(&mut pool, conclusion.clone());
        let (result, code) = run_egglog(&mut pool, conclusion, &root, &rules);
        if debug {
            println!(
                "\n=== Generated egglog code ===\n{}\n=== End egglog code ===\n",
                code
            );
        }
        result.map(|_| ())
    }

    fn elaborate_with_options(
        conclusion_str: &str,
        options: RunEgglogOptions,
    ) -> (Result<(), String>, String) {
        let mut pool = PrimitivePool::new();
        let conclusion = parse_term(&mut pool, conclusion_str);
        let rules = empty_rules();
        let root = dummy_proof_node(&mut pool, conclusion.clone());
        let (result, code) = run_egglog_with_options(&mut pool, conclusion, &root, &rules, options);
        (result.map(|_| ()), code)
    }

    fn goal_schedule_round_count(code: &str) -> usize {
        code.lines()
            .filter(|line| line.contains("(run list-ruleset)))"))
            .count()
    }

    fn check_count(code: &str) -> usize {
        code.lines()
            .filter(|line| line.starts_with("(check "))
            .count()
    }

    fn assert_single_round_raw_then_poly_pipeline(code: &str) {
        let goal_schedule = code
            .find("(run-schedule (repeat 1 (run list-ruleset)))")
            .expect("missing goal schedule round");
        let raw_check = code
            .find("(check (= goal_lhs goal_rhs))")
            .expect("missing raw goal check");
        let poly_setup = code
            .find("(arithPolyNfOf-demand goal_lhs)")
            .expect("missing poly demand setup");
        let poly_saturation = code
            .find("(run-schedule (saturate (run arith_poly)))")
            .expect("missing poly saturation");
        let poly_check = code
            .find("(check (= (arithPolyNfOf goal_lhs) (arithPolyNfOf goal_rhs)))")
            .expect("missing poly goal check");

        assert_eq!(
            goal_schedule_round_count(code),
            1,
            "expected exactly one goal schedule round, got:\n{}",
            code
        );
        assert_eq!(
            check_count(code),
            2,
            "expected one raw check and one poly check, got:\n{}",
            code
        );
        assert!(
            goal_schedule < raw_check
                && raw_check < poly_setup
                && poly_setup < poly_saturation
                && poly_saturation < poly_check,
            "expected raw check before the poly retry pipeline, got:\n{}",
            code
        );
    }

    fn try_elaborate_with_rules(
        conclusion_str: &str,
        rare_source: &str,
        debug: bool,
    ) -> Result<(), String> {
        let mut pool = PrimitivePool::new();
        let rules = parse_rare_rules(&mut pool, rare_source);
        let conclusion = parse_term(&mut pool, conclusion_str);
        let root = dummy_proof_node(&mut pool, conclusion.clone());
        let (result, code) = run_egglog(&mut pool, conclusion, &root, &rules);
        if debug {
            println!(
                "\n=== Generated egglog code ===\n{}\n=== End egglog code ===\n",
                code
            );
        }
        result.map(|_| ())
    }

    /// Just print the generated egglog code without running it
    #[allow(dead_code)]
    fn print_egglog_code(conclusion_str: &str) {
        let mut pool = PrimitivePool::new();
        let conclusion = parse_term(&mut pool, conclusion_str);
        let rules = empty_rules();
        let root = dummy_proof_node(&mut pool, conclusion.clone());
        let (_, code) = run_egglog(&mut pool, conclusion, &root, &rules);
        println!(
            "\n=== Generated egglog code for: {} ===\n{}\n=== End ===\n",
            conclusion_str, code
        );
    }

    fn run_raw_egglog(script: &str) -> Result<(), String> {
        let mut egraph = EGraph::default();
        super::register_arith_poly_primitives(&mut egraph);
        let program = format!(
            "{}\n{}\n{}\n{}",
            RAW_TERM_BASE,
            include_str!("arith_poly_norm.egglog"),
            include_str!("arith_poly_norm_rel.egglog"),
            script,
        );
        egraph
            .parse_and_run_program(Some("arith_poly_norm_raw_tests.egg".to_string()), &program)
            .map(|_| ())
            .map_err(|e| e.to_string())
    }

    // ============ Linear arithmetic sanity checks ============

    /// Step 1: Test that (- 0 1) works (should be -1)
    #[test]
    fn test_dos_step1_negation_constant() {
        let result = try_elaborate("(= (- 0 1) (- 0 1))");
        assert!(result.is_ok(), "Step 1 failed: {:?}", result.err());
    }

    /// Step 3: Test negation times variable: (-1)*a = (-1)*a
    #[test]
    fn test_dos_step3_neg_times_var() {
        let result = try_elaborate("(= (* (- 0 1) a) (* (- 0 1) a))");
        assert!(result.is_ok(), "Step 3 failed: {:?}", result.err());
    }

    /// Step 4: Test simple addition: a + b = a + b
    #[test]
    fn test_dos_step4_simple_add() {
        let result = try_elaborate("(= (+ a b) (+ a b))");
        assert!(result.is_ok(), "Step 4 failed: {:?}", result.err());
    }

    /// Debug: just print the egglog code for step 4
    #[test]
    fn test_dos_step4_print_code() {
        print_egglog_code("(= (+ a b) (+ a b))");
    }

    /// Step 5: Test addition with negation: a + (-1)*b = a + (-1)*b
    #[test]
    fn test_dos_step5_add_with_neg() {
        let result = try_elaborate("(= (+ a (* (- 0 1) b)) (+ a (* (- 0 1) b)))");
        assert!(result.is_ok(), "Step 5 failed: {:?}", result.err());
    }

    /// From prob_01608_091584__24625092-t335.t25.t87.alethe
    /// Tests: (a + (-1)*b) = 0 iff a = b
    /// Structure: (= (+ a (* -1 b)) 0) = (= a b)
    #[test]
    fn test_hanna_sum_zero_equality() {
        let result = try_elaborate("(= (= (+ a (* (- 0 1) b)) 0) (= a b))");
        assert!(
            result.is_ok(),
            "Hanna sum zero equality failed: {:?}",
            result.err()
        );
    }

    /// From prob_00139_004785__15024976-t17.t6.alethe
    /// Tests: (>= (+ a (* -1 b)) 0) = (>= a b)
    /// Subtraction in comparison context
    #[test]
    fn test_hanna_geq_subtraction() {
        // Need to add >= to definitions for this test
        let result = try_elaborate("(= (+ a (* (- 0 1) b)) (- a b))");
        assert!(
            result.is_ok(),
            "Hanna geq subtraction failed: {:?}",
            result.err()
        );
    }

    /// From prob_00331_012189__22756550-t2.t14.alethe
    /// Tests equality flip with coefficient normalization
    /// Structure: (= (= a b) (= b a)) with coefficient 1 and -1
    #[test]
    fn test_hanna_equality_flip_coefficients() {
        // (= (* 1 (- a b)) (* -1 (- b a))) should imply (= (= a b) (= b a))
        let result = try_elaborate("(= (* 1 (- a b)) (* (- 0 1) (- b a)))");
        assert!(
            result.is_ok(),
            "Hanna equality flip coefficients failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_prefix_t1_arith_elim_leq() {
        let result = try_elaborate_with_rules(
            "(= (<= 1 f3) (>= f3 1))",
            INTEGER_BOUND_TEST_RARE,
            debug_egglog(),
        );
        assert!(
            result.is_ok(),
            "t1 prefix rewrite failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_prefix_t4_arith_elim_lt() {
        let result = try_elaborate_with_rules(
            "(= (< 2 (+ 1 (* 4 f3))) (not (>= 2 (+ 1 (* 4 f3)))))",
            INTEGER_BOUND_TEST_RARE,
            debug_egglog(),
        );
        assert!(
            result.is_ok(),
            "t4 prefix rewrite failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_prefix_t6_arith_poly_norm() {
        let result = try_elaborate("(= (+ (* 4 f3) 1) (+ 1 (* 4 f3)))");
        assert!(
            result.is_ok(),
            "t6 prefix rewrite failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_prefix_t8_arith_poly_norm() {
        let result = try_elaborate(
            "(= (* 1/4 (to_real (- 2 (+ 1 (* 4 f3)))))
                (* 1/1 (- (to_real (* (- 0 1) f3)) (- 1/4))))",
        );
        assert!(
            result.is_ok(),
            "t8 prefix rewrite failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_prefix_t9_arith_poly_norm_rel() {
        let result = run_raw_egglog(
            r#"
            (let f3 (Mk (Var 1 int_sort)))
            (let num_1 (Mk (Num 1)))
            (let num_2 (Mk (Num 2)))
            (let num_4 (Mk (Num 4)))
            (let num_neg_1 (Mk (Num -1)))
            (let real_11 (Mk (Real 1 1)))
            (let real_14 (Mk (Real 1 4)))
            (let real_neg_14 (Mk (Real -1 4)))

            (let p1 (Mk (@* (Args num_4 (Args f3 (Empty))))))
            (let p12 (Mk (@+ (Args num_1 (Args p1 (Empty))))))
            (let p14 (Mk (@* (Args num_neg_1 (Args f3 (Empty))))))
            (let p19 (Mk (@to_real (Args p14 (Empty)))))

            (let lhs_diff (Mk (@to_real (Args (Mk (@- (Args num_2 (Args p12 (Empty))))) (Empty)))))
            (let lhs_scaled (Mk (@* (Args real_14 (Args lhs_diff (Empty))))))

            (let rhs_diff (Mk (@- (Args p19 (Args real_neg_14 (Empty))))))
            (let rhs_scaled (Mk (@* (Args real_11 (Args rhs_diff (Empty))))))

            (let p13 (Mk (@>= (Args num_2 (Args p12 (Empty))))))
            (let p20 (Mk (@>= (Args p19 (Args real_neg_14 (Empty))))))

            (union lhs_scaled rhs_scaled)

            (run-schedule (saturate (run arith_poly)))

            (check (= p13 p20))
            "#,
        );
        assert!(
            result.is_ok(),
            "t9 relation lift failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_prefix_t9_direct_relation_normalization() {
        let result = run_raw_egglog(
            r#"
            (let f3 (Mk (Var 1 int_sort)))
            (let num_1 (Mk (Num 1)))
            (let num_2 (Mk (Num 2)))
            (let num_4 (Mk (Num 4)))
            (let num_neg_1 (Mk (Num -1)))
            (let real_neg_14 (Mk (Real -1 4)))

            (let p1 (Mk (@* (Args num_4 (Args f3 (Empty))))))
            (let p12 (Mk (@+ (Args num_1 (Args p1 (Empty))))))
            (let p14 (Mk (@* (Args num_neg_1 (Args f3 (Empty))))))
            (let p19 (Mk (@to_real (Args p14 (Empty)))))

            (let p13 (Mk (@>= (Args num_2 (Args p12 (Empty))))))
            (let p20 (Mk (@>= (Args p19 (Args real_neg_14 (Empty))))))

            (run-schedule (saturate (run arith_poly)))

            (check (= p13 p20))
            "#,
        );
        assert!(
            result.is_ok(),
            "t9 direct relation normalization failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_prefix_t13_arith_int_geq_tighten() {
        let result = try_elaborate_with_rules(
            "(= (>= (to_real (* (- 0 1) f3)) (- 1/4))
                (>= (* (- 0 1) f3) 0))",
            INTEGER_BOUND_TEST_RARE,
            debug_egglog(),
        );
        assert!(
            result.is_ok(),
            "t13 integer tighten failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_prefix_t13_premise_non_integer_bound() {
        let result = try_elaborate_with_rules(
            "(= (= (to_real (to_int (- 1/4))) (- 1/4)) false)",
            INTEGER_BOUND_TEST_RARE,
            debug_egglog(),
        );
        assert!(
            result.is_ok(),
            "t13 non-integer bound premise failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_prefix_t13_premise_floor_plus_one() {
        let result = try_elaborate_with_rules(
            "(= (+ (to_int (- 1/4)) 1) 0)",
            INTEGER_BOUND_TEST_RARE,
            debug_egglog(),
        );
        assert!(
            result.is_ok(),
            "t13 floor-plus-one premise failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_prefix_t14_arith_geq_tighten() {
        let result = try_elaborate_with_rules(
            "(= (not (>= f3 1))
                (>= 1 (+ f3 1)))",
            INTEGER_BOUND_TEST_RARE,
            debug_egglog(),
        );
        assert!(result.is_ok(), "t14 geq tighten failed: {:?}", result.err());
    }

    #[test]
    fn test_hanna_integer_bound_prefix_t15_arith_poly_norm() {
        let result = try_elaborate(
            "(= (* (- 0 1) (- 1 (+ f3 1)))
                (* (- 0 1) (- (* (- 0 1) f3) 0)))",
        );
        assert!(
            result.is_ok(),
            "t15 prefix rewrite failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_prefix_t16_arith_poly_norm_rel() {
        let result = run_raw_egglog(
            r#"
            (let f3 (Mk (Var 1 int_sort)))
            (let num_0 (Mk (Num 0)))
            (let num_1 (Mk (Num 1)))
            (let num_neg_1 (Mk (Num -1)))

            (let p16 (Mk (@+ (Args f3 (Args num_1 (Empty))))))
            (let p14 (Mk (@* (Args num_neg_1 (Args f3 (Empty))))))

            (let lhs_diff (Mk (@- (Args num_1 (Args p16 (Empty))))))
            (let lhs_scaled (Mk (@* (Args num_neg_1 (Args lhs_diff (Empty))))))

            (let rhs_diff (Mk (@- (Args p14 (Args num_0 (Empty))))))
            (let rhs_scaled (Mk (@* (Args num_neg_1 (Args rhs_diff (Empty))))))

            (let p17 (Mk (@>= (Args num_1 (Args p16 (Empty))))))
            (let p15 (Mk (@>= (Args p14 (Args num_0 (Empty))))))

            (union lhs_scaled rhs_scaled)

            (run-schedule (saturate (run arith_poly)))

            (check (= p17 p15))
            "#,
        );
        assert!(
            result.is_ok(),
            "t16 relation lift failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_prefix_t16_direct_relation_normalization() {
        let result = run_raw_egglog(
            r#"
            (let f3 (Mk (Var 1 int_sort)))
            (let num_0 (Mk (Num 0)))
            (let num_1 (Mk (Num 1)))
            (let num_neg_1 (Mk (Num -1)))

            (let p16 (Mk (@+ (Args f3 (Args num_1 (Empty))))))
            (let p14 (Mk (@* (Args num_neg_1 (Args f3 (Empty))))))

            (let p17 (Mk (@>= (Args num_1 (Args p16 (Empty))))))
            (let p15 (Mk (@>= (Args p14 (Args num_0 (Empty))))))

            (run-schedule (saturate (run arith_poly)))

            (check (= p17 p15))
            "#,
        );
        assert!(
            result.is_ok(),
            "t16 direct relation normalization failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_left_branch_affine_isolate_step() {
        let result = try_elaborate_with_rules(
            "(= (>= 2 (+ 1 (* 4 f3)))
                (>= (to_real (* (- 0 1) f3))
                    (/ (- (to_real 1) (to_real 2)) (to_real 4))))",
            INTEGER_BOUND_TEST_RARE,
            debug_egglog(),
        );
        assert!(
            result.is_ok(),
            "left branch affine isolate failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_left_branch_to_zero() {
        let result = try_elaborate_with_rules(
            "(= (>= 2 (+ 1 (* 4 f3)))
                (>= (* (- 0 1) f3) 0))",
            INTEGER_BOUND_TEST_RARE,
            debug_egglog(),
        );
        assert!(
            result.is_ok(),
            "left branch direct to zero failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_left_branch_generated_bound_to_zero() {
        let result = try_elaborate_with_rules(
            "(= (>= (to_real (* (- 0 1) f3))
                    (/ (- (to_real 1) (to_real 2)) (to_real 4)))
                (>= (* (- 0 1) f3) 0))",
            INTEGER_BOUND_TEST_RARE,
            debug_egglog(),
        );
        assert!(
            result.is_ok(),
            "left branch generated bound to zero failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_right_branch_after_t14() {
        let result = try_elaborate_with_rules(
            "(= (>= 1 (+ f3 1))
                (>= (* (- 0 1) f3) 0))",
            INTEGER_BOUND_TEST_RARE,
            debug_egglog(),
        );
        assert!(
            result.is_ok(),
            "right branch after t14 failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_integer_bound_right_branch_to_zero() {
        let result = try_elaborate_with_rules(
            "(= (not (>= f3 1))
                (>= (* (- 0 1) f3) 0))",
            INTEGER_BOUND_TEST_RARE,
            debug_egglog(),
        );
        assert!(
            result.is_ok(),
            "right branch to zero failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_hanna_geq_vs_not_geq_integer_bound() {
        let result = try_elaborate_with_rules(
            "(= (>= 2 (+ 1 (* 4 f3))) (not (>= f3 1)))",
            INTEGER_BOUND_TEST_RARE,
            debug_egglog(),
        );
        assert!(
            result.is_ok(),
            "integer bound complement rewrite failed: {:?}",
            result.err()
        );
    }

    /// Tests equality rearrangement with addition
    /// (= x (+ 1 y)) should be equivalent to (= y (+ -1 x))
    /// Both normalize to: x - y = 1
    #[test]
    fn test_equality_rearrangement_add() {
        let result = try_elaborate("(= (= x (+ 1 y)) (= y (+ -1 x)))");
        assert!(
            result.is_ok(),
            "Equality rearrangement failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_goal_schedule_round_runs_raw_and_poly_on_same_attempt() {
        let (result, code) = elaborate_with_options(
            "(= (+ a (* (- 0 1) b)) (- a b))",
            RunEgglogOptions { max_goal_schedule_rounds: 1 },
        );
        assert!(
            result.is_ok(),
            "single-round raw/poly attempt failed: {:?}",
            result.err()
        );
        assert_single_round_raw_then_poly_pipeline(&code);
    }

    #[test]
    #[ignore = "n-ary addition regression for counted-offset reordering"]
    fn test_counted_offset_sum_reordering_nary_regression() {
        let result = try_elaborate(COUNTED_OFFSET_REORDER_EQ);
        assert!(
            result.is_ok(),
            "counted offset sum reordering failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_counted_offset_sum_reordering_binary_control() {
        let result = try_elaborate(COUNTED_OFFSET_REORDER_EQ_BINARY_CONTROL);
        assert!(
            result.is_ok(),
            "counted offset sum reordering binary control failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_counted_offset_sum_reordering_binary_control_single_round_pipeline() {
        let (result, code) = elaborate_with_options(
            COUNTED_OFFSET_REORDER_EQ_BINARY_CONTROL,
            RunEgglogOptions { max_goal_schedule_rounds: 1 },
        );
        assert!(
            result.is_ok(),
            "single-round counted offset sum reordering binary control failed: {:?}",
            result.err()
        );
        assert_single_round_raw_then_poly_pipeline(&code);
    }

    #[test]
    fn test_uninterpreted_function_duplicate_sum() {
        let result = try_elaborate("(= (+ (f x1) (f x1)) (* 2 (f x1)))");
        assert!(
            result.is_ok(),
            "uninterpreted function duplicate sum failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_uninterpreted_function_ordering() {
        let result = try_elaborate("(= (+ (f x1) (g x1)) (+ (g x1) (f x1)))");
        assert!(
            result.is_ok(),
            "uninterpreted function ordering failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_real_uninterpreted_function_duplicate_sum() {
        let result = try_elaborate("(= (+ (fr x1) (fr x1)) (* (to_real 2) (fr x1)))");
        assert!(
            result.is_ok(),
            "real uninterpreted function duplicate sum failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_symbolic_product_cancellation() {
        let result = try_elaborate("(= (+ (* x y) (- (* x y))) 0)");
        assert!(
            result.is_ok(),
            "symbolic product cancellation failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_raw_mixed_sort_same_id_regression() {
        let result = run_raw_egglog(
            r#"
            (let int_v (Mk (Var 7 int_sort)))
            (let real_v (Mk (Var 7 real_sort)))

            (arithPolyNfOf-demand int_v)
            (arithPolyNfOf-demand real_v)

            (run-schedule (saturate (run arith_poly)))

            (check (!= (arithPolyNfOf int_v) (arithPolyNfOf real_v)))
            "#,
        );
        assert!(
            result.is_ok(),
            "mixed-sort same-id regression failed: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_raw_arith_poly_norm_rel_regressions() {
        let result = run_raw_egglog(
            r#"
            (let x1 (Mk (Var 1 int_sort)))
            (let x2 (Mk (Var 2 int_sort)))
            (let y1 (Mk (Var 3 int_sort)))
            (let y2 (Mk (Var 4 int_sort)))
            (let z1 (Mk (Var 5 int_sort)))
            (let z2 (Mk (Var 6 int_sort)))
            (let w1 (Mk (Var 7 int_sort)))
            (let w2 (Mk (Var 8 int_sort)))

            (let num_2 (Mk (Num 2)))
            (let num_3 (Mk (Num 3)))
            (let num_neg_2 (Mk (Num -2)))
            (let num_neg_3 (Mk (Num -3)))

            (let diff_x (Mk (@- (Args x1 (Args x2 (Empty))))))
            (let diff_y (Mk (@- (Args y1 (Args y2 (Empty))))))
            (let diff_y_real (Mk (@to_real (Args diff_y (Empty)))))
            (let diff_z (Mk (@- (Args z1 (Args z2 (Empty))))))
            (let diff_w (Mk (@- (Args w1 (Args w2 (Empty))))))

            (let prem_eq_lhs (Mk (@* (Args num_2 (Args diff_x (Empty))))))
            (let prem_eq_rhs (Mk (@* (Args num_3 (Args diff_y_real (Empty))))))
            (union prem_eq_lhs prem_eq_rhs)

            (let eq_lhs (Mk (@= (Args x1 (Args x2 (Empty))))))
            (let eq_rhs (Mk (@= (Args y1 (Args y2 (Empty))))))

            (let ge_lhs (Mk (@>= (Args x1 (Args x2 (Empty))))))
            (let ge_rhs (Mk (@>= (Args y1 (Args y2 (Empty))))))

            (let prem_neg_lhs (Mk (@* (Args num_neg_2 (Args diff_x (Empty))))))
            (let prem_neg_rhs (Mk (@* (Args num_neg_3 (Args diff_y (Empty))))))
            (union prem_neg_lhs prem_neg_rhs)

            (let prem_bad_lhs (Mk (@* (Args num_2 (Args diff_x (Empty))))))
            (let prem_bad_rhs (Mk (@* (Args num_neg_3 (Args diff_y (Empty))))))
            (union prem_bad_lhs prem_bad_rhs)
            (let prem_mismatch_lhs (Mk (@* (Args num_2 (Args diff_z (Empty))))))
            (let prem_mismatch_rhs (Mk (@* (Args num_neg_3 (Args diff_w (Empty))))))
            (union prem_mismatch_lhs prem_mismatch_rhs)

            (let lt_lhs (Mk (@< (Args x1 (Args x2 (Empty))))))
            (let lt_rhs (Mk (@< (Args y1 (Args y2 (Empty))))))
            (let bad_ge_lhs (Mk (@>= (Args z1 (Args z2 (Empty))))))
            (let bad_ge_rhs (Mk (@>= (Args w1 (Args w2 (Empty))))))

            (run-schedule (saturate (run arith_poly)))

            (check (= eq_lhs eq_rhs))
            (check (= ge_lhs ge_rhs))
            (check (= lt_lhs lt_rhs))
            (check (!= bad_ge_lhs bad_ge_rhs))
            "#,
        );
        assert!(
            result.is_ok(),
            "raw arith_poly_norm_rel regressions failed: {:?}",
            result.err()
        );
    }
}
