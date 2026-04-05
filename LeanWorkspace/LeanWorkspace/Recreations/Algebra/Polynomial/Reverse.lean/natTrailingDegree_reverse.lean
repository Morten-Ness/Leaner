import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem natTrailingDegree_reverse (f : R[X]) : f.reverse.natTrailingDegree = 0 := by
  rw [natTrailingDegree_eq_zero, Polynomial.reverse_eq_zero, Polynomial.coeff_zero_reverse, leadingCoeff_ne_zero]
  exact eq_or_ne _ _

