import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingCoeff_eq_coeff_zero (h : coeff p 0 ≠ 0) : Polynomial.trailingCoeff p = coeff p 0 := by
  rw [Polynomial.trailingCoeff, (natTrailingDegree_eq_zero.mpr <| .inr h)]

