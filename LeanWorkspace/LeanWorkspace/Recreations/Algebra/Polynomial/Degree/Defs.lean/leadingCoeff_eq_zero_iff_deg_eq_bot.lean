import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem leadingCoeff_eq_zero_iff_deg_eq_bot : Polynomial.leadingCoeff p = 0 ↔ Polynomial.degree p = ⊥ := by
  rw [Polynomial.leadingCoeff_eq_zero, Polynomial.degree_eq_bot]

