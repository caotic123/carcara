(set-logic QF_UF)
(declare-const x Bool)
(assert (not (= (= false x) (not x))))
(check-sat)
