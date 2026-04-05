import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reverse_trailingCoeff (f : R[X]) : f.reverse.trailingCoeff = f.leadingCoeff := by
  rw [trailingCoeff, Polynomial.natTrailingDegree_reverse, Polynomial.coeff_zero_reverse]

