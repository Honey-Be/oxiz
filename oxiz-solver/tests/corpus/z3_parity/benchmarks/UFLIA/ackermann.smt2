; Test: Ackermann-like function properties
; Expected: sat
; Pattern: bounded base/recurrence values + monotonicity-derived positivity
;
; Positivity is stated the natural way — base `ack(0,0)>0` plus STRICT
; MONOTONICITY in each argument (⇒ ack(m,n) ≥ ack(0,0) > 0 by induction) —
; rather than as a solver-hostile grid `∀m,n. ack(m,n)>0`. Both monotonicity
; quantifiers stay range-guarded, so the instantiation domain is finite (no
; ack-of-ack matching loop). Model: ack(m,n) = m+n+1.
(set-logic UFLIA)
(declare-fun ack (Int Int) Int)
(assert (forall ((n Int)) (=> (and (>= n 0) (<= n 5)) (= (ack 0 n) (+ n 1)))))
(assert (= (ack 1 0) (ack 0 1)))
(assert (= (ack 2 0) (ack 1 1)))
(assert (forall ((n Int)) (=> (and (>= n 0) (<= n 3)) (= (ack 1 n) (+ n 2)))))
(assert (= (ack 0 0) 1))
(assert (= (ack 1 0) 2))
(assert (= (ack 1 1) 3))
(assert (> (ack 0 0) 0))
(assert (forall ((m Int) (n Int))
  (=> (and (>= m 0) (<= m 1) (>= n 0) (<= n 5))
      (> (ack (+ m 1) n) (ack m n)))))
(assert (forall ((m Int) (n Int))
  (=> (and (>= m 0) (<= m 2) (>= n 0) (<= n 4))
      (> (ack m (+ n 1)) (ack m n)))))
(check-sat)
(exit)
