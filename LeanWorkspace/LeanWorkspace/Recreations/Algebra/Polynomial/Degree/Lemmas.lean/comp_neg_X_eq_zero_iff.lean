import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

theorem comp_neg_X_eq_zero_iff [Ring R] {p : R[X]} : p.comp (-Polynomial.X) = 0 ↔ p = 0 := by
  simp [← leadingCoeff_eq_zero]

