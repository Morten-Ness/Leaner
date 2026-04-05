import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reverse_leadingCoeff (f : R[X]) : f.reverse.leadingCoeff = f.trailingCoeff := by
  rw [leadingCoeff, Polynomial.reverse_natDegree, ← Polynomial.revAt_le f.natTrailingDegree_le_natDegree,
    Polynomial.coeff_reverse, Polynomial.revAt_invol, trailingCoeff]

