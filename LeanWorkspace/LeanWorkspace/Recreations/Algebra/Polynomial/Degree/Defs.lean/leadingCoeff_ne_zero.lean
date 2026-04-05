import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem leadingCoeff_ne_zero : Polynomial.leadingCoeff p ≠ 0 ↔ p ≠ 0 := by rw [Ne, Polynomial.leadingCoeff_eq_zero]

