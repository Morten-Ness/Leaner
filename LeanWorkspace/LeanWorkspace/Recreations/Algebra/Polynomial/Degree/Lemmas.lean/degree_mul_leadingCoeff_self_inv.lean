import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable {K : Type*} [DivisionRing K]

theorem degree_mul_leadingCoeff_self_inv (p : K[X]) :
    degree (p * Polynomial.C (leadingCoeff p)⁻¹) = degree p := by
  by_cases hp : p = 0
  · simp [hp]
  exact Polynomial.degree_mul_leadingCoeff_inv _ hp

