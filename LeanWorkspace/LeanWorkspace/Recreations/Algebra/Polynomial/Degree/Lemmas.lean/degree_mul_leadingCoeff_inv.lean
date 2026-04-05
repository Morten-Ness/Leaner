import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable {K : Type*} [DivisionRing K]

theorem degree_mul_leadingCoeff_inv (p : K[X]) {q : K[X]} (h : q ≠ 0) :
    degree (p * Polynomial.C (leadingCoeff q)⁻¹) = degree p := by
  have h₁ : (leadingCoeff q)⁻¹ ≠ 0 := inv_ne_zero (mt leadingCoeff_eq_zero.1 h)
  rw [Polynomial.degree_mul_C h₁]

