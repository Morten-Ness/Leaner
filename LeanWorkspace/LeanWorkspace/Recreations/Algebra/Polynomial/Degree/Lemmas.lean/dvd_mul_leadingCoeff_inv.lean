import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable {K : Type*} [DivisionRing K]

theorem dvd_mul_leadingCoeff_inv {p q : K[X]} (hp0 : p ≠ 0) :
    q ∣ p * Polynomial.C (leadingCoeff p)⁻¹ ↔ q ∣ p := by
  simp [hp0]

