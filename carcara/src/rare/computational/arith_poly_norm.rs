use crate::rare::engine::EggFunctions;
use crate::rare::language::{ConstType, EggStatement};

/// Arithmetic operators for polynomial normalization.
/// Returns: (string name, @-prefixed name)
pub fn arith_operators() -> impl Iterator<Item = (&'static str, &'static str)> {
    [
        ("-", "@-"),
        ("+", "@+"),
        ("*", "@*"),
        ("/", "@/"),
        ("/_total", "@/_total"),
        ("to_real", "@to_real"),
        // Note: "=" is NOT included here - it's a general operator declared by declare_functions
    ]
    .into_iter()
}

/// Helper predicates used by polynomial normalization rules
fn helper_predicates() -> impl Iterator<Item = &'static str> {
    ["@$less_or_equal_var", "@$is_not_num"].into_iter()
}

/// Check if any arithmetic operator is present in the function cache.
pub fn has_arith_operator(functions: &EggFunctions) -> bool {
    arith_operators().any(|(name, _)| functions.names.contains_key(name))
}

/// Generate constructor declarations for all arithmetic operators and helper predicates.
/// declare_functions() skips arith operators, so we declare them all here.
pub fn arith_constructors(_functions: &EggFunctions) -> Vec<EggStatement> {
    let term = ConstType::ConstrType("Term".to_string());
    let mut decls = Vec::new();

    // Declare all arithmetic operators
    for (_, op_with_at) in arith_operators() {
        decls.push(EggStatement::Constructor(
            op_with_at.to_string(),
            vec![term.clone()],
            term.clone(),
        ));
    }

    // Declare helper predicates used by polynomial normalization rules
    for pred in helper_predicates() {
        decls.push(EggStatement::Constructor(
            pred.to_string(),
            vec![term.clone()],
            term.clone(),
        ));
    }

    decls
}

/// Generate all polynomial normalization rules by including the egglog file.
/// The egglog file must include the datatype and constructor declarations for parsing.
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

    const DEFINITIONS: &str = r#"
        (declare-sort Int 0)
        (declare-sort Real 0)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (declare-fun * (Int Int) Int)
        (declare-fun + (Int Int) Int)
        (declare-fun - (Int Int) Int)
        (declare-fun / (Int Int) Int)
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
    fn try_elaborate(conclusion_str: &str) -> Result<(), String> {
        let mut pool = PrimitivePool::new();
        let conclusion = parse_term(&mut pool, conclusion_str);
        let rules = empty_rules();
        let root = dummy_proof_node(&mut pool, conclusion.clone());
        run_egglog(&mut pool, conclusion, &root, &rules)
            .map(|_| ())
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

    /// From prob_00310_013548__18557966-t7.alethe
    /// Tests product equality symmetry: (= (* a b) (* c d)) = (= (* c d) (* a b))
    #[test]
    fn test_hanna_product_equality_symmetry() {
        let result = try_elaborate(
            "(= (= (* a b) (* x y)) (= (* x y) (* a b)))"
        );
        assert!(result.is_ok(), "Hanna product equality symmetry failed: {:?}", result.err());
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
}
