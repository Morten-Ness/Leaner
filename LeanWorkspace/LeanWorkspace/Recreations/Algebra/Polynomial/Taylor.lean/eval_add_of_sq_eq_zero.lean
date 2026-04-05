import Mathlib

variable {R : Type*} [CommSemiring R] (r : R) (f : R[X])

theorem eval_add_of_sq_eq_zero (p : R[X]) (x y : R) (hy : y ^ 2 = 0) :
    p.eval (x + y) = p.eval x + p.derivative.eval x * y := by
  rw [add_comm, ← Polynomial.taylor_eval,
    Polynomial.eval_eq_sum_range' ((Nat.lt_succ_self _).trans (Nat.lt_succ_self _)),
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp [pow_succ, mul_assoc, ← pow_two, hy, add_comm (eval x p)]

