import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem natDegree_taylor (p : R[X]) (r : R) : natDegree (Polynomial.taylor r p) = natDegree p := by
  refine map_natDegree_eq_natDegree _ ?_
  nontriviality R
  intro n c c0
  simp [Polynomial.taylor_monomial, natDegree_C_mul_of_mul_ne_zero, natDegree_pow_X_add_C, c0]

