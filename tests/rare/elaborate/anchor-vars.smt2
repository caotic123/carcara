(set-logic LIA)
(assert (forall ((x Int)) (< x 0)))
(assert (not (forall ((x Int)) (not (>= x 0)))))
(check-sat)
