import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable {K : Type*} [DivisionRing K]

theorem degree_leadingCoeff_inv {p : K[X]} (hp0 : p ≠ 0) :
    degree (Polynomial.C (leadingCoeff p)⁻¹) = 0 := by
  simp [hp0]

