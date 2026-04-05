import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem modByMonic_X (p : R[X]) : p %ₘ Polynomial.X = Polynomial.C (p.eval 0) := by
  rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval, C_0, sub_zero]

