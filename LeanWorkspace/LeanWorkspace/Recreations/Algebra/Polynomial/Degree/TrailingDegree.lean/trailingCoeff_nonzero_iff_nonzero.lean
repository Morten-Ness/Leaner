import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem trailingCoeff_nonzero_iff_nonzero : Polynomial.trailingCoeff p ≠ 0 ↔ p ≠ 0 := not_congr Polynomial.trailingCoeff_eq_zero

