use crate::rare::language::EggStatement;


pub fn arith_poly_norm_rules() -> Vec<EggStatement> {
    // Include the egglog file content at compile time
    let egglog_content = include_str!("arith_poly_norm.egglog");
    vec![EggStatement::Raw(egglog_content.to_string())]
}

/// Test module for arith_poly_norm debugging using the engine
#[cfg(test)]
pub mod tests {
    use crate::ast::pool::PrimitivePool;
    use crate::ast::rare_rules::RareStatements;
    use crate::ast::{ProofNode, Rc, StepNode};
    use crate::parser::{Config, Parser};
    use crate::rare::engine::run_egglog;
    use indexmap::IndexMap;

    /// Returns true if debug-egglog feature is enabled
    /// Run with: cargo test --features debug-egglog <test_name> -- --nocapture
    fn debug_egglog() -> bool {
        cfg!(feature = "debug-egglog")
    }

    const DEFINITIONS: &str = r#"
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (declare-fun a () Int)
        (declare-fun b () Int)
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
        let mut parser =
            Parser::new(pool, config, DEFINITIONS.as_bytes()).expect("parser error");
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

    /// Create a minimal proof node with no premises
    fn dummy_proof_node(pool: &mut PrimitivePool, conclusion: Rc<crate::ast::Term>) -> Rc<ProofNode> {
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
            println!("\n=== Generated egglog code ===\n{}\n=== End egglog code ===\n", code);
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
        println!("\n=== Generated egglog code for: {} ===\n{}\n=== End ===\n", conclusion_str, code);
    }

    /// Test case from Alethe proof step t2: (= (* (* 2 x) y) (* 2 (* x y)))
    /// This tests coefficient reordering: (2 * x) * y should equal 2 * (x * y)
    #[test]
    fn test_t2_coeff_reorder_left() {
        let result = try_elaborate("(= (* (* 2 x) y) (* 2 (* x y)))");
        assert!(result.is_ok(), "t2 elaboration failed: {:?}", result.err());
    }

    /// Test case from Alethe proof step t3: (= (* x (* 2 y)) (* 2 (* x y)))
    /// This tests coefficient reordering: x * (2 * y) should equal 2 * (x * y)
    #[test]
    fn test_t3_coeff_reorder_right() {
        let result = try_elaborate("(= (* x (* 2 y)) (* 2 (* x y)))");
        assert!(result.is_ok(), "t3 elaboration failed: {:?}", result.err());
    }

    // ============ Step-by-step tests for difference of squares ============

    /// Step 1: Test that (- 0 1) works (should be -1)
    #[test]
    fn test_dos_step1_negation_constant() {
        let result = try_elaborate("(= (- 0 1) (- 0 1))");
        assert!(result.is_ok(), "Step 1 failed: {:?}", result.err());
    }

    /// Step 2: Test simple variable squaring: a*a = a*a
    #[test]
    fn test_dos_step2_var_squared() {
        let result = try_elaborate("(= (* a a) (* a a))");
        assert!(result.is_ok(), "Step 2 failed: {:?}", result.err());
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

    /// Step 6: Test (a+b)*(a+b) multiplication
    #[test]
    fn test_dos_step6_sum_times_sum() {
        let result = try_elaborate("(= (* (+ a b) (+ a b)) (* (+ a b) (+ a b)))");
        assert!(result.is_ok(), "Step 6 failed: {:?}", result.err());
    }

    /// Step 7: Test LHS only: a² + (-1)*b² = a² + (-1)*b²
    #[test]
    fn test_dos_step7_lhs_only() {
        let result = try_elaborate("(= (+ (* a a) (* (- 0 1) (* b b))) (+ (* a a) (* (- 0 1) (* b b))))");
        assert!(result.is_ok(), "Step 7 (LHS) failed: {:?}", result.err());
    }

    /// Step 8: Test RHS only: (a+b)*(a+(-1)*b) = (a+b)*(a+(-1)*b)
    #[test]
    fn test_dos_step8_rhs_only() {
        let result = try_elaborate("(= (* (+ a b) (+ a (* (- 0 1) b))) (* (+ a b) (+ a (* (- 0 1) b))))");
        assert!(result.is_ok(), "Step 8 (RHS) failed: {:?}", result.err());
    }

    /// From prob_00076_002539__14169734-t86.t149.t10.alethe
    /// Tests difference of squares: a² - b² = (a + b)(a - b)
    /// Structure: (+ (* a a) (* -1 (* b b))) = (* (+ a b) (+ a (* -1 b)))
    #[test]
    fn test_hanna_difference_of_squares() {
        // a² - b² = (a+b)(a-b) using (* -1 x) for negation
        let result = try_elaborate(
            "(= (+ (* a a) (* (- 0 1) (* b b))) (* (+ a b) (+ a (* (- 0 1) b))))"
        );
        assert!(result.is_ok(), "Hanna difference of squares failed: {:?}", result.err());
    }

    /// From prob_01608_091584__24625092-t335.t25.t87.alethe
    /// Tests: (a + (-1)*b) = 0 iff a = b
    /// Structure: (= (+ a (* -1 b)) 0) = (= a b)
    #[test]
    fn test_hanna_sum_zero_equality() {
        let result = try_elaborate(
            "(= (= (+ a (* (- 0 1) b)) 0) (= a b))"
        );
        assert!(result.is_ok(), "Hanna sum zero equality failed: {:?}", result.err());
    }

    /// From prob_00139_004785__15024976-t17.t6.alethe
    /// Tests: (>= (+ a (* -1 b)) 0) = (>= a b)
    /// Subtraction in comparison context
    #[test]
    fn test_hanna_geq_subtraction() {
        // Need to add >= to definitions for this test
        let result = try_elaborate(
            "(= (+ a (* (- 0 1) b)) (- a b))"
        );
        assert!(result.is_ok(), "Hanna geq subtraction failed: {:?}", result.err());
    }

    /// From prob_00097_003589__6963528-t92.alethe
    /// Tests complex sum normalization: (+ (f a) (* -1 (* m (+ 1 n)))) = (- (f a) (* m (+ 1 n)))
    /// Pattern: adding negative of product equals subtraction
    #[test]
    fn test_hanna_complex_sum_subtraction() {
        // Simplified: (+ x (* -1 (* y z))) = (- x (* y z))
        let result = try_elaborate(
            "(= (+ x (* (- 0 1) (* y z))) (- x (* y z)))"
        );
        assert!(result.is_ok(), "Hanna complex sum subtraction failed: {:?}", result.err());
    }

    /// From prob_00331_012189__22756550-t2.t14.alethe
    /// Tests equality flip with coefficient normalization
    /// Structure: (= (= a b) (= b a)) with coefficient 1 and -1
    #[test]
    fn test_hanna_equality_flip_coefficients() {
        // (= (* 1 (- a b)) (* -1 (- b a))) should imply (= (= a b) (= b a))
        let result = try_elaborate(
            "(= (* 1 (- a b)) (* (- 0 1) (- b a)))"
        );
        assert!(result.is_ok(), "Hanna equality flip coefficients failed: {:?}", result.err());
    }

    /// From prob_00076_002539__14169734-t16.t23.alethe
    /// Tests common term cancellation in sums
    /// Structure: (+ a b c d) = (+ a b c e) when d normalizes to e
    #[test]
    fn test_hanna_common_term_cancellation() {
        // Simplified: (+ a (* b x)) = (+ a (* -1 (* -1 (* b x))))
        // Tests that (* -1 (* -1 t)) = t (double negation)
        let result = try_elaborate(
            "(= (+ a (* b x)) (+ a (* (- 0 1) (* (- 0 1) (* b x)))))"
        );
        assert!(result.is_ok(), "Hanna common term cancellation failed: {:?}", result.err());
    }

    /// Tests equality rearrangement with addition
    /// (= x (+ 1 y)) should be equivalent to (= y (+ -1 x))
    /// Both normalize to: x - y = 1
    #[test]
    fn test_equality_rearrangement_add() {
        let result = try_elaborate(
            "(= (= x (+ 1 y)) (= y (+ -1 x)))"
        );
        assert!(result.is_ok(), "Equality rearrangement failed: {:?}", result.err());
    }

    /// Tests canonical form: (= a b) should be equivalent to (= (- a b) 0)
    /// This is the basic building block for equality normalization
    #[test]
    fn test_equality_canonical_form() {
        let result = try_elaborate(
            "(= (= x y) (= (- x y) 0))"
        );
        assert!(result.is_ok(), "Equality canonical form failed: {:?}", result.err());
    }

}
